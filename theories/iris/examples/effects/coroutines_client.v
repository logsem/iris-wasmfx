
From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.program_logic Require Import adequacy.
From iris.bi Require Export weakestpre.
From iris.algebra Require Import excl agree csum.
From Wasm Require Import type_checker_reflects_typing.
From Wasm.iris.rules Require Export iris_rules iris_example_helper.
From Wasm.iris.host Require Export iris_host.
From Wasm.iris.examples.effects Require Import coroutines_module coroutines_implementation_code.


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*
Class natG Σ := NAtG {
                    nat_genG :: ghost_mapG Σ unit nat
                  } .
Notation "γ ○↪ v" := (ghost_map_elem γ tt (DfracOwn 1) v%V) (at level 20).
Notation "γ ●↪ v" := (ghost_map_auth γ 1 (<[ tt := (v : nat) ]> ∅)) (at level 20).
 *)
Definition one_shotR := csumR (exclR unitO) (agreeR unitO).
Definition Pending : one_shotR := Cinl (Excl ()).
Definition Shot : one_shotR := Cinr (to_agree ()).

Class one_shotG Σ := { #[local] one_shot_inG :: inG Σ one_shotR }.

Definition one_shotΣ : gFunctors := #[GFunctor one_shotR].
Global Instance subG_one_shotΣ {Σ} : subG one_shotΣ Σ → one_shotG Σ.
Proof. solve_inG. Qed.



Section coroutines_client_functions.

  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ, !one_shotG Σ}.

   Definition f1 :=
     [ BI_const (xx 42);
       BI_set_global 0;
       BI_call 0;
       BI_const (xx 1);
       BI_set_global 1
     ].

   Definition f2 :=
     [ BI_get_global 1;
       BI_set_global 2;
       BI_call 0;
       BI_get_global 0;
       BI_set_global 3
     ].

   Definition main :=
     [ 
       BI_ref_func 2;
       BI_ref_func 3;
       BI_call 1;
       BI_get_global 2;
       BI_get_global 3
     ].


   Definition wgpt a b :=
     N.of_nat a ↦[wg] {| g_mut := MUT_mut ; g_val := xx b |}.
   
   Definition P1 : iProp Σ := True.

   Definition Q1 γx γy : iProp Σ := own γx Shot ∗ own γy Shot.

   Definition P2 addra addrb: iProp Σ :=
     ∃ a b, wgpt addra a ∗ wgpt addrb b. 

   Definition Q2 addra addrb: iProp Σ :=
     ∃ a b, wgpt addra a ∗ wgpt addrb b ∗ ⌜ a = 1 -> b = 42 ⌝ .

   Definition I addrx addry γx γy : iProp Σ :=
     (wgpt addrx 0 ∗ wgpt addry 0 ∗ own γx Pending ∗ own γy Pending) ∨
       (wgpt addrx 42 ∗ wgpt addry 0 ∗ own γx Shot ∗ own γy Pending) ∨
       (wgpt addrx 42 ∗ wgpt addry 1 ∗ own γx Shot ∗ own γy Shot).

   Definition spec_f1 f Ψ γx γy addr_f1 cl_f1 addrx addry addr_yield cl_yield: iProp Σ :=
     □ (N.of_nat addr_f1 ↦[wf] cl_f1 -∗
        N.of_nat addr_yield ↦[wf] cl_yield -∗
         P1 -∗
         I addrx addry γx γy -∗
              EWP [AI_invoke addr_f1] UNDER f <| Ψ |> {{ v; f' ,
                  ⌜ v = immV [] ⌝ ∗
                  ⌜ f' = f ⌝ ∗
                  N.of_nat addr_f1 ↦[wf] cl_f1 ∗
                  N.of_nat addr_yield ↦[wf] cl_yield ∗
                  Q1 γx γy ∗
                  I addrx addry γx γy
       }})%I.
   
   Definition spec_f2 f Ψ γx γy addr_f2 cl_f2 addrx addry addra addrb addr_yield cl_yield: iProp Σ :=
     □ (N.of_nat addr_f2 ↦[wf] cl_f2 -∗
          N.of_nat addr_yield ↦[wf] cl_yield -∗
          P2 addra addrb -∗
          I addrx addry γx γy -∗
             EWP [AI_invoke addr_f2] UNDER f <| Ψ |> {{ v; f' ,
                ⌜ v = immV [] ⌝ ∗
                ⌜ f' = f ⌝ ∗
                N.of_nat addr_f2 ↦[wf] cl_f2 ∗
                N.of_nat addr_yield ↦[wf] cl_yield ∗
                Q2 addra addrb ∗
                I addrx addry γx γy }})%I.

   Definition spec_main f Ψ addr_main cl_main addrx addry addra addrb addr_yield cl_yield addr_par cl_par addr_f1 cl_f1 addr_f2 cl_f2: iProp Σ :=
     □ (N.of_nat addr_main ↦[wf] cl_main -∗
             N.of_nat addr_f1 ↦[wf] cl_f1 -∗
             N.of_nat addr_f2 ↦[wf] cl_f2 -∗
             N.of_nat addr_yield ↦[wf] cl_yield -∗
             N.of_nat addr_par ↦[wf] cl_par -∗
             (∃ x y a b, wgpt addrx x ∗ wgpt addry y ∗ wgpt addra a ∗ wgpt addrb b) -∗
                EWP [AI_invoke addr_main] UNDER f <| Ψ |> {{ v; f' ,
                     ⌜ v = immV [] ⌝ ∗
                     ⌜ f' = f ⌝ ∗
                     N.of_nat addr_main ↦[wf] cl_main ∗
                     N.of_nat addr_f1 ↦[wf] cl_f1 ∗
                     N.of_nat addr_f2 ↦[wf] cl_f2 ∗
                     N.of_nat addr_yield ↦[wf] cl_yield ∗
                     N.of_nat addr_par ↦[wf] cl_par ∗
                     Q2 addra addrb }})%I.

   Definition main_type := Tf [] [T_num T_i32; T_num T_i32].
   
  Definition client_inst addr_yield addr_par addr_f1 addr_f2 addr_main addrx addry addra addrb :=
    {| inst_types := [ emptyt; par_type; main_type ];
      inst_funcs := [ addr_yield; addr_par; addr_f1; addr_f2; addr_main ] ;
      inst_tab := [];
      inst_memory := [];
      inst_globs := [addrx; addry; addra; addrb];
      inst_tags := [] |}.
   
   Lemma spec_f1_proof f Ψ γx γy addr_f1 cl_f1 addrx addry addr_yield cl_yield addr_par addr_f2 addr_main addra addrb :
     cl_f1 = FC_func_native (client_inst addr_yield addr_par addr_f1 addr_f2 addr_main addrx addry addra addrb) emptyt [] f1 ->
     yield_spec addr_yield cl_yield Ψ (I addrx addry γx γy)
       ⊢ spec_f1 f Ψ γx γy addr_f1 cl_f1 addrx addry addr_yield cl_yield.
   Proof.
     iIntros (->) "#Hyield !> Hwf1 Hwfyield HP1 HI".
     rewrite - (app_nil_l [AI_invoke addr_f1]).
     iApply (ewp_invoke_native with "Hwf1").
     done. done. done.
     iIntros "!> Hwf1".
     iApply ewp_frame_bind.
     done. done.
     iSplitR; last first.
     iSplitR "Hwf1".
     rewrite -(app_nil_l [AI_basic _]).
     iApply ewp_block.
     done. done. done. done.
     iApply (ewp_label_bind with "[-]").
     2:{ iPureIntro.
         instantiate (5 := []).
         rewrite /lfilled /lfill /= app_nil_r //. }
     rewrite separate2.
     iAssert (∃ x, wgpt addrx x ∗ (own γx Pending ∨ own γx Shot) ∗ ∃ y, wgpt addry y ∗ (⌜ y = 0 ⌝ ∗ own γy Pending ∨ ⌜ y = 1 ⌝ ∗ own γy Shot))%I with "[HI]" as "(%x & Hx & Htokx & %y & Hy & Htoky)".
     { iDestruct "HI" as "[(Hx & Hy & Htokx & Htoky) | [(Hx & Hy & Htokx & Htoky) | (Hx & Hy & Htokx & Htoky)]]".
       all: iFrame.
       1-2: by iLeft; iFrame.
       by iRight; iFrame.
     } 
     iApply ewp_seq.
     done.
     iSplitR; last first.
     iSplitL "Hx".
     iApply (ewp_set_global with "[] Hx"); first done.
     auto_instantiate.
     2: by iIntros (?) "[[% _] _]".
     iIntros (??) "[[-> ->] Hx]".
     iSimpl.
     iApply fupd_ewp.
     iAssert (|={⊤}=> own γx Shot)%I with "[Htokx]" as "Htokx".
     { iDestruct "Htokx" as "[Htokx | Htokx]"; last done.
       iMod (own_update with "Htokx") as "Htokx"; last done.
       apply cmra_update_exclusive. done. }
     iMod "Htokx" as "#Htokx". 
     iModIntro.
     rewrite (separate1 (AI_basic _)).
     iApply ewp_seq; first done.
     iSplitR; last first.
     simpl.
     iSplitL.
     iApply ewp_call; first done.
     iApply ("Hyield" with "[Hx Hy Htoky] Hwfyield").
     iRight.
     iDestruct "Htoky" as "[[-> Htoky] | [-> Htoky]]"; iFrame.
     by iLeft; iFrame. by iRight; iFrame.
     2: by iIntros (?) "[% _]".
     iIntros (??) "(-> & -> & HI & Hwfyield)".
     iSimpl.
     iAssert (wgpt addrx 42 ∗ ∃ i, wgpt addry i ∗ (own γy Pending ∨ own γy Shot))%I with "[HI]" as "(Hx & %i & Hy & Htoky)".

     { iDestruct "HI" as "[(Hx & Hy & Htokx2 & Htoky) | [(Hx & Hy & _ & Htoky) | (Hx & Hy & _ & Htoky)]]".
       iDestruct (own_valid_2 with "Htokx Htokx2") as "%Habs".
       done.
       all: iFrame. } 
     iApply (ewp_wand with "[Hy]").
     iApply (ewp_set_global with "[] Hy").
     done.
     auto_instantiate.
     iIntros (??) "[[-> ->] Hy]".
     simpl.
     iIntros (LI HLI).
     move/lfilledP in HLI; inversion HLI; subst.
     inversion H8; subst.
     iSimpl.
     iApply fupd_ewp.
     iAssert (|={⊤}=> own γy Shot)%I with "[Htoky]" as "Htoky".
     { iDestruct "Htoky" as "[Htoky | Htoky]"; last done.
       iMod (own_update with "Htoky") as "Htoky"; last done.
       apply cmra_update_exclusive. done. }
     iMod "Htoky" as "#Htoky".
     iModIntro.
     iApply ewp_label_value.
     done.
     instantiate (1 := λ v f,  (⌜ v = immV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝ ∗ _)%I).
     iSplitR; first done.
     iSplitR; first done.
     iCombine "Hwfyield Hx Hy Htokx Htoky" as "H".
     iExact "H".
     iIntros (??) "(-> & -> & Hwfyield & Hx & Hy & #Htokx & #Htoky)".
     iApply ewp_frame_value.
     done. done.
     iSplit; first done.
     iSplit; first done.
     iFrame.
     iFrame "Htokx Htoky".
     iRight; iRight.
     iFrame.
     iIntros (?) "[% _]" => //.
   Qed. 
     
   Lemma spec_f2_proof f Ψ addr_f2 cl_f2 addrx addry γx γy addr_yield cl_yield addr_par addr_f1 addr_main addra addrb :
     cl_f2 = FC_func_native (client_inst addr_yield addr_par addr_f1 addr_f2 addr_main addrx addry addra addrb) emptyt [] f2 ->
     yield_spec addr_yield cl_yield Ψ (I addrx addry γx γy)
       ⊢ spec_f2 f Ψ γx γy addr_f2 cl_f2 addrx addry addra addrb addr_yield cl_yield.
   Proof.
     iIntros (->) "#Hyield !> Hwf2 Hwfyield HP2 HI".
     iDestruct "HP2" as (a b) "[Ha Hb]".
     iAssert (∃ y, wgpt addry y ∗ (⌜ y = 1 ⌝ ∗ own γy Shot ∗ wgpt addrx 42 ∗ own γx Shot ∨ ⌜ y = 0 ⌝ ∗ own γy Pending ∗ ∃ x, wgpt addrx x ∗ (⌜ x = 0 ⌝ ∗ own γx Pending ∨ ⌜ x = 42 ⌝ ∗ own γx Shot)))%I with "[HI]" as "(%y & Hy & Htoky)".
     { iDestruct "HI" as "[(Hx & Hy & Htokx & Htoky) | [(Hx & Hy & Htokx & Htoky) | (Hx & Hy & Htokx & Htoky)]]".
       all: iFrame.
       - iRight. iFrame. iSplit; first done.
         by iLeft; iFrame.
       - iRight; iFrame. iSplit; first done.
         by iRight; iFrame.
       - by iLeft; iFrame. } 
     rewrite - (app_nil_l [AI_invoke addr_f2]).
     iApply (ewp_invoke_native with "Hwf2").
     done. done. done.
     iIntros "!> Hwf2".
     iApply ewp_frame_bind.
     done. done.
     iSplitR; last first.
     iSplitR "Hwf2".
     rewrite -(app_nil_l [AI_basic _]).
     iApply ewp_block.
     done. done. done. done.
     iApply (ewp_label_bind with "[-]").
     2:{ iPureIntro.
         instantiate (5 := []).
         rewrite /lfilled /lfill /= app_nil_r //. }
     rewrite (separate1 (AI_basic _)).
     iApply ewp_seq.
     done.
     iSplitR; last first.
     iSplitL "Hy".
     iApply (ewp_get_global with "[] Hy").
     done. done.
     iSimpl.
     auto_instantiate.
     2: by iIntros (?) "[[% _] _]".
     iIntros (??) "[[->->] Hy]".
     iSimpl.
     rewrite separate2.
     iApply ewp_seq.
     done.
     iSplitR; last first.
     iSplitL "Ha".
     iApply (ewp_set_global with "[] Ha").
     done.
     auto_instantiate.
     2: by iIntros (?) "[[% _] _]".
     iIntros (??) "[[-> ->] Ha]".
     iSimpl.
     rewrite (separate1 (AI_basic _)).
     iApply ewp_seq.
     done.
     iAssert (I addrx addry γx γy ∗ (⌜ y = 1 ⌝ ∗ own γy Shot ∗ own γx Shot ∨ ⌜ y = 0 ⌝))%I with "[Hy Htoky]" as "[HI #Htoky]".
     { iDestruct "Htoky" as "[(-> & #Htoky & Hx & #Htokx) | (-> & Htoky & %x & Hx & [[-> Htokx] | [-> Htokx]])]".
       iSplitL; last by iLeft; iFrame "Htokx Htoky".
       by iRight; iRight; iFrame "Htokx Htoky Hx Hy".
       all: iSplitL; last by iRight.
       iLeft; by iFrame.
       iRight; iLeft; by iFrame. } 
     iSplitR; last first.
     iSplitL "HI Hwfyield".
     iApply ewp_call.
     done.
     iApply ("Hyield" with "HI Hwfyield").
     2: by iIntros (?) "[% _]".
     iIntros (??) "(-> & -> & HI & Hwfyield)".
     iAssert (∃ x, wgpt addrx x ∗ (⌜ x = 0 ⌝ ∗ ⌜ y = 0 ⌝ ∗ own γx Pending ∗ wgpt addry 0 ∗ own γy Pending ∨ ⌜ x = 42 ⌝ ∗ own γx Shot ∗ ∃ y, wgpt addry y ∗ (⌜ y = 0 ⌝ ∗ own γy Pending ∨ ⌜ y = 1 ⌝ ∗ own γy Shot)))%I with "[HI]" as "(%x & Hx & Htokx)".
     { iDestruct "HI" as "[(Hx & Hy & Htokx & Htoky') | [(Hx & Hy & Htokx & Htoky') | (Hx & Hy & Htokx & Htoky')]]".
       all: iFrame.
       - iLeft.
         iDestruct "Htoky" as "[(-> & Htoky & Htokx') | ->]".
         iDestruct (own_valid_2 with "Htokx Htokx'") as "%Habs".
         done.
         iFrame. done.
       - iRight. iFrame. iSplit; first done. by iLeft; iFrame.
       - iRight. iFrame. iSplit; first done. by iRight; iFrame. } 
     iSimpl.
     rewrite (separate1 (AI_basic _)).
     iApply ewp_seq.
     done.
     iSplitR; last first.
     iSplitL "Hx".
     iApply (ewp_get_global with "[] Hx").
     done. done.
     by auto_instantiate.
     2: by iIntros (?) "[[% _] _]".
     iIntros (??) "[[-> ->] Hx]".
     iSimpl.
     iApply (ewp_wand with "[Hb]").
     iApply (ewp_set_global with "[] Hb").
     done.
     auto_instantiate.
     iIntros (??) "[[-> ->] Hb]".
     iIntros (LI HLI).
     move/lfilledP in HLI; inversion HLI; subst.
     inversion H8; subst.
     iApply ewp_label_value.
     done.
     instantiate (1 := λ v f, (⌜ v = immV [] ⌝ ∗ ⌜ f = Build_frame [] _ ⌝ ∗ ∃ x, N.of_nat addra↦[wg] {| g_mut := MUT_mut; g_val := xx y |} ∗
        N.of_nat addrb↦[wg] {| g_mut := MUT_mut; g_val := xx x |} ∗
        N.of_nat addrx↦[wg] {| g_mut := MUT_mut; g_val := xx x |} ∗
        (⌜x = 0⌝ ∗ ⌜y = 0⌝ ∗ own γx Pending ∗ wgpt addry 0 ∗ 
         own γy Pending ∨ ⌜x = 42⌝ ∗ own γx Shot ∗
         ∃ y0 : Z, wgpt addry y0 ∗
           (⌜y0 = 0⌝ ∗ own γy Pending ∨ ⌜y0 = 1⌝ ∗ own γy Shot)) ∗
        N.of_nat addr_yield↦[wf]cl_yield)%I).
     iSplit; first done.
     iSplit; first done.
     iCombine "Ha Hb Hx Htokx Hwfyield" as "H".
     simpl. iNext. iExists x. done.
     2: by iIntros (?) "[% _]".
     iIntros (??) "(-> & -> & %x & Ha & Hb & Hx & Htokx & Hwfyield)".
     iApply ewp_frame_value.
     done. done.
     iSplit; first done.
     iSplit; first done.
     iFrame.
     iNext.
     iSplit.
     { (* the implication *)
       iDestruct "Htokx" as "[(-> & -> & _) | [-> _]]".
       all: done. }
     (* reconstructing the invariant *)
     iDestruct "Htokx" as "[(-> & -> & Htokx & Hy & Htoky) | (-> & Htokx & %y' & Hy & [[-> Htoky] | [-> Htoky]])]".
     - iLeft. iFrame.
     - iRight. iLeft. iFrame.
     - iRight. iRight. iFrame. 
   Qed. 
       
       

     


End coroutines_client_functions.

Section coroutines_client_module.

  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ, !one_shotG Σ}.

  Definition client_module :=
    {|
      mod_types := [ emptyt; par_type; main_type ];
      mod_funcs :=
      [ {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [] ;
          modfunc_body := f1
        |};
        {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [] ;
          modfunc_body := f2
        |};
        {|
          modfunc_type := Mk_typeidx 2;
          modfunc_locals := [];
          modfunc_body := main
        |} 
      ] ;
      mod_tables := [];
      mod_mems := [] ;
      mod_globals := [
        {| modglob_type := {| tg_mut := MUT_mut ; tg_t := T_i32 |} ;
          modglob_init := [BI_const (xx 0)] |};
        {| modglob_type := {| tg_mut := MUT_mut ; tg_t := T_i32 |} ;
          modglob_init := [BI_const (xx 0)] |} ;
        {| modglob_type := {| tg_mut := MUT_mut ; tg_t := T_i32 |} ;
          modglob_init := [BI_const (xx 0)] |};
        {| modglob_type := {| tg_mut := MUT_mut ; tg_t := T_i32 |} ;
          modglob_init := [BI_const (xx 0)] |}
      ];
      mod_elem := [] ;
      mod_data := [] ;
      mod_start := None; (* Some {| modstart_func := Mk_funcidx 4 |} ;  *)
      mod_imports := [
        {| imp_module := String.list_byte_of_string "coroutines module";
          imp_name := String.list_byte_of_string "yield function";
          imp_desc := ID_func 0
        |};
        {| imp_module := String.list_byte_of_string "coroutines module";
          imp_name := String.list_byte_of_string "par function";
          imp_desc := ID_func 1
        |}(* ;
        {| imp_module := String.list_byte_of_string "host";
          imp_name := String.list_byte_of_string "a";
          imp_desc := ID_global {| tg_mut := MUT_mut ; tg_t := T_i32 |}
        |};
        {| imp_module := String.list_byte_of_string "host";
          imp_name := String.list_byte_of_string "b";
          imp_desc := ID_global {| tg_mut := MUT_mut ; tg_t := T_i32 |}
        |} *)

      ];
      mod_exports := [
        {| modexp_name := String.list_byte_of_string "main";
          modexp_desc := MED_func (Mk_funcidx 4) |}
(*        {| modexp_name := String.list_byte_of_string "a";
          modexp_desc := MED_global (Mk_globalidx 0)
        |} ;
        {| modexp_name := String.list_byte_of_string "b";
          modexp_desc := MED_global (Mk_globalidx 1)
        |} *)
      ];
      mod_tags := []
    |}.

  Definition impts := [ET_func emptyt ; ET_func par_type (* ;
                       ET_glob {| tg_mut := MUT_mut ; tg_t := T_i32 |};
                       ET_glob {| tg_mut := MUT_mut ; tg_t := T_i32 |} *)
    ].

  Definition expts : list extern_t := [ET_func (Tf [] [T_num T_i32; T_num T_i32])] (* ET_glob {| tg_mut := MUT_mut ; tg_t := T_i32 |};
                       ET_glob {| tg_mut := MUT_mut ; tg_t := T_i32 |}] *) .

  Lemma client_module_typing :
    module_typing client_module impts expts.
  Proof.
    unfold module_typing.
    exists [emptyt; emptyt; main_type], (repeat {| tg_mut := MUT_mut ; tg_t := T_i32 |} 4).
    simpl.
    repeat split; eauto.
    - constructor; last constructor; last constructor; last constructor.
      all: cbn; repeat split => //.
      + apply/b_e_type_checker_reflects_typing.
        simpl. done.
      + apply/b_e_type_checker_reflects_typing.
        simpl. done.
      + apply/b_e_type_checker_reflects_typing.
        simpl. done.
    - constructor; last constructor; last constructor; last constructor; last constructor.
      all: cbn; repeat split => //.
      all: constructor.
    - constructor; last constructor; last constructor; last constructor; last constructor.
      all: cbn; try by apply/andP; split => //.
      all: by apply/eqglobal_typeP.
    - repeat constructor => //=.
(*      unfold module_export_typing.
      simpl. by apply/eqP.
      unfold module_export_typing.
      simpl. by apply/eqP. *)
  Qed.


  Definition client_module_instantiate yield_exp_addr par_exp_addr main_exp_addr (* a_exp_addr b_exp_addr *) mod_addr mod_addr' (* ga gb *) :=
    [ ID_instantiate [ yield_exp_addr ; par_exp_addr ] mod_addr [] ;
      ID_instantiate [ main_exp_addr (* a_exp_addr ; b_exp_addr *) ] mod_addr' [ yield_exp_addr ; par_exp_addr (* ; a_exp_addr; b_exp_addr *) ];
      H_invoke main_exp_addr []
(*      H_get_global ga;
      H_get_global gb *)
    ].

  Notation "{{{{ P }}}} es {{{{ v , Q }}}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).

  Lemma instantiate_client yield_exp_addr par_exp_addr main_exp_addr (* a_exp_addr b_exp_addr *) mod_addr mod_addr' (* ga gb vala valb *): 
(*    typeof_num vala = T_i32 ->
    typeof_num valb = T_i32 -> *) 
    ⊢ {{{{ 
              mod_addr ↪[mods] coroutines_module ∗
                mod_addr' ↪[mods] client_module ∗
                (∃ exp1, yield_exp_addr ↪[vis] exp1) ∗
                (∃ exp2, par_exp_addr ↪[vis] exp2) ∗
                (∃ exp3, main_exp_addr ↪[vis] exp3) 
        (*        (∃ namea, a_exp_addr ↪[vis]  {| modexp_name := namea;
                                               modexp_desc := MED_global (Mk_globalidx ga) |}) ∗
                (∃ nameb, b_exp_addr ↪[vis]  {| modexp_name := nameb;
                                               modexp_desc := MED_global (Mk_globalidx gb) |}) ∗
                (N.of_nat ga ↦[wg] {| g_mut := MUT_mut ; g_val := vala |}) ∗
                (N.of_nat gb ↦[wg] {| g_mut := MUT_mut ; g_val := valb |})  *)
       
      }}}}
      ((client_module_instantiate yield_exp_addr par_exp_addr main_exp_addr (* a_exp_addr b_exp_addr *) mod_addr mod_addr' (* ga gb *),
         [], empty_frame) : host_expr)
      {{{{ x, ⌜ exists a b, x = (immHV [VAL_num (xx a); VAL_num (xx b)], empty_frame) /\ (a = 1 -> b = 42) ⌝ }}}}.
      (* old postcond: *)
(*        {{{{  x,  ⌜x = (immHV [], empty_frame)⌝ ∗
                         mod_addr ↪[mods] coroutines_module ∗
                         mod_addr' ↪[mods] client_module ∗
                         ∃ addra addrb vala valb namea nameb,
                           a_exp_addr ↪[vis] {| modexp_name := namea;
                                               modexp_desc := MED_global (Mk_globalidx addra) |} ∗
                             b_exp_addr ↪[vis] {| modexp_name := nameb;
                                                 modexp_desc := MED_global (Mk_globalidx addrb) |} ∗

                           wgpt addra vala ∗
                             wgpt addrb valb ∗
                             ⌜ vala = 1 -> valb = 1 ⌝
        }}}} . *)
  Proof.
(*    intros Hvala Hvalb. *)
    iIntros "!>" (Φ) "(Hmod1 & Hmod2 & Hexp1 & Hexp2 & Hexp3) HΦ".

    (* instantiate coroutines module *) 
    iApply (wp_seq_host_nostart with "[] Hmod1 [Hexp1 Hexp2]").
    done. done.
    2:{
      iIntros "Hmod1".
      iApply (instantiate_coroutines with "[$Hmod1 $Hexp1 $Hexp2]").
      iIntros (x) "(-> & Hmod & H)".
      iFrame.
      instantiate (1 := λ v, (⌜ v = (immHV [], empty_frame) ⌝ ∗ _)%I).
      iSplit; first done.
      iExact "H".
    }
    by iIntros (?) "[% _]".
    iIntros (w f) "(%Heq & %addr_yield & %addr_par & %name_yield & %name_par & %cl_yield & %cl_par & Hexp1 & Hexp2 & %Htypeyield & %Htypepar & Hwfyield & Hwfpar & #Hspecs) Hmod1".
    iDestruct (pointsto_ne with "Hwfyield Hwfpar") as %Hne.
(*    iDestruct (pointsto_ne with "Hga Hgb") as %Hne'. *)
    inversion Heq; subst. clear Heq.

    (* instantiate client module *)
(*    iApply (weakestpre.wp_wand _ _ (_ : host_expr) with "[- HΦ]"). *)
    iApply (wp_seq_host_nostart with "[] Hmod2 [Hexp1 Hexp2 Hexp3 Hwfyield Hwfpar]").
    done. done.
    2:{
      iIntros "Hmod2".
      iApply (weakestpre.wp_wand _ _ (_ : host_expr) with "[-]").
      iApply (instantiation_spec_operational_no_start with "[-]").
      4: iFrame "Hmod2".
      done.
      apply client_module_typing.
      repeat constructor.
      by eexists [_;_;_;_].
      1,2: by eexists [].
      iSplitL "Hexp1 Hexp2".
      { unfold import_resources_host.
        instantiate (1 := [_;_]).
        iFrame. done. }
    iSplitR "Hexp3"; last first.
    { iSplitL; last done.
      unfold export_ownership_host.
      iFrame. done. } 
    unfold instantiation_resources_pre_wasm.
    iSimpl.
    iSplitL; last first.
    iSplitL. by unfold module_elem_bound_check_gmap.
    by unfold module_data_bound_check_gmap.
    unfold import_resources_wasm_typecheck.
    iSplitL; last first.
(*    iSplitR "Hga Hgb"; last first. *)
    iSplitR.
    instantiate (1 := ∅).
    unfold import_tab_wasm_check.
    iSplitL.
    by unfold import_tab_resources.
    unfold tab_typecheck, tab_domcheck.
    iPureIntro. split; last done. by repeat constructor.
    iSplitR.
    instantiate (1 := ∅).
    unfold import_mem_wasm_check.
    iSplitL. 
    by unfold import_mem_resources.
    iPureIntro.
    split; last done.
    by repeat constructor.
    iSplitL.
    instantiate (1 := (* <[ _ := _ ]> (<[ _ := _ ]>  *) ∅ (* ) *) ).
    unfold import_glob_wasm_check.
    iSplitL; first unfold import_glob_resources.
    done.
(*    iApply big_sepM_insert; last first.
    iFrame "Hga".
    iApply big_sepM_insert.
    done.
    iFrame "Hgb". done. 
    rewrite lookup_insert_ne => //.  *)

    iPureIntro.
    unfold glob_typecheck, glob_domcheck.
    simpl.
    split; last by set_solver.
    repeat constructor => //=.
(*    rewrite lookup_insert.
    repeat eexists => //=.
    unfold global_agree.
    rewrite Hvala. done.
    rewrite lookup_insert_ne; last done.
    rewrite lookup_insert.
    repeat eexists => //=.
    rewrite /global_agree /= Hvalb //. *)
    unfold import_tag_wasm_check.
    iSplitL; first by unfold import_tag_resources.
    iPureIntro. split; last done.
    by repeat constructor.
    unfold import_func_wasm_check.
    unfold import_func_resources.

    instantiate (1 := (<[ _ := _ ]> (<[ _ := _]> ∅))).
    iSplitL.

    iApply big_sepM_insert.
    2:{ iFrame "Hwfyield".
        iApply big_sepM_insert.
        done.
        iFrame "Hwfpar".
        done. }
    rewrite lookup_insert_ne.
    done.
    done.
    iPureIntro.
    split.
    repeat constructor => //=.
    eexists.
    rewrite lookup_insert.
    split => //. 
    by rewrite Htypeyield.
    eexists.
    rewrite lookup_insert_ne; last done.
    rewrite lookup_insert.
    split => //.
    by rewrite Htypepar.
    unfold func_domcheck.
    simpl.
    set_solver.
    iIntros (idnstart) "H".
    unfold instantiation_resources_post.
    iDestruct "H" as "(-> & Hmod2 & Himps & %inst & Hresources & Hexports)".
    unfold module_export_resources_host.
(*    iClear "Hexports". *)
    iDestruct "Hexports" as "([%namemain Hexpmain] & _)".
    simpl.
    iFrame.
    iCombine "Himps Hresources Hexpmain" as "H".
    instantiate (1 := λ v, (∃ namemain inst, ⌜ v = (immHV [], empty_frame) ⌝ ∗ _)%I).
    iExists namemain, inst. iSplit; first done. iExact "H". }
    by iIntros (?) "(%namemain & %inst & % & _)".
    iIntros (w fr) "(%namemain & %inst & %Heq & Himps & Hresources & Hexpmain) Hmod2".
    inversion Heq; subst; clear Heq.
    
     unfold import_resources_host.
    iDestruct "Himps" as "(Hexp1 & Hexp2 & _)".
    unfold instantiation_resources_post_wasm.
    iDestruct "Hresources" as (g_inits tab_allocs mem_allocs glob_allocs tag_allocs wts' wms') "(Himptype & %Hprefs & -> & -> & %Helembound & -> & -> & %Hdatabound & %Hinitval & -> & -> & Hresources)".
    unfold module_glob_init_values in Hinitval.
    unfold module_glob_init_value in Hinitval.
    destruct Hinitval as [Hinittypes Hthose].
    simpl in Hthose.
    unfold those in Hthose.
    simpl in Hthose.
    inversion Hthose; subst.
    unfold module_inst_resources_wasm.
    iDestruct "Hresources" as "(Hfuncs & Htabs & Hmems & Hglobs & Htags)".
    unfold module_inst_resources_func.
    unfold module_inst_resources_tab.
    unfold module_inst_resources_mem.
    unfold module_inst_resources_glob.
    unfold module_inst_resources_tag.
(*    assert (exists a b c d, module_inst_global_init (module_inst_build_globals (mod_globals client_module)) g_inits = map (fun x => {| g_mut := MUT_mut ; g_val := VAL_int32 x |}) [a;b;c;d]) as (? & ? & ? & ? & ->).
    { simpl.
      do 4 (destruct g_inits; first by repeat eexists).
      by repeat eexists. } *)
(*    rewrite Heq0. *)
    
    destruct inst; simpl in *.
    rewrite /get_import_func_count /get_import_table_count /get_import_mem_count
      /get_import_global_count /get_import_tag_count /=.
    repeat rewrite drop_0.
    destruct inst_tags; last done.
    destruct inst_memory; last done.
    destruct inst_tab; last done.
    iClear "Htags Hmems Htabs".

    
    destruct Hprefs as (-> & Hfuncpref & _ & _ & Hglobpref & _ & Hstart).
    destruct inst_funcs; first done.
    destruct inst_funcs; first done.
    inversion Hfuncpref.
    inversion H; subst.
    clear H Hfuncpref.
    destruct x; first done.
    iDestruct "Hfuncs" as "[Hf1 Hfuncs]".
    destruct x; first done.
    iDestruct "Hfuncs" as "[Hf2 Hfuncs]".
    destruct x; first done.
    iDestruct "Hfuncs" as "[Hfmain Hfuncs]".
    destruct x; last done.

    destruct inst_globs; first done.
    iDestruct "Hglobs" as "[Hg1 Hglobs]".
    destruct inst_globs; first done.
    iDestruct "Hglobs" as "[Hg2 Hglobs]".
    destruct inst_globs; first done.
    iDestruct "Hglobs" as "[Hg3 Hglobs]".
    destruct inst_globs; first done.
    iDestruct "Hglobs" as "[Hg4 Hglobs]".
    destruct inst_globs; last done.

    
    iClear "Hfuncs Hglobs".
    simpl.
(*    unfold check_start in Hstart.
    move/eqP in Hstart; simpl in Hstart.
    inversion Hstart; subst idnstart. *)
    unfold import_resources_wasm_typecheck, impts.
    iDestruct "Himptype" as "(Himpfunc & _)". (* " & _ & Himpglob & _)". *)
    unfold import_func_wasm_check.
    iDestruct "Himpfunc" as "[Himpfunc %Himpfunc]".
    unfold import_func_resources.
    iDestruct (big_sepM_insert with "Himpfunc") as "[Hfyield Himpfunc]".
    rewrite lookup_insert_ne; last done.
    done.
    iDestruct (big_sepM_insert with "Himpfunc") as "[Hfpar _]".
    done.
    unfold import_func_wasm_check.
(*    iDestruct "Himpglob" as "[Himpglob %Himpglob]".
    unfold import_glob_resources.
    iDestruct (big_sepM_insert with "Himpglob") as "[Hga Himpglob]".
    rewrite lookup_insert_ne; last done.
    done.
    iDestruct (big_sepM_insert with "Himpglob") as "[Hgb Himpglob]".
    done. *)
    replace [] with (v_to_e_list []); last done.
    iApply (wp_invoke_host with "[$] [$Hfmain]").
    done.
    done.
    iIntros "!> Hexpmain Hfmain".

    iApply wp_lift_wasm.

    (* Prove the specification of main *)
    (*    rewrite - (app_nil_l [AI_invoke _]). *)
    iApply (ewp_invoke_native with "Hfmain").
    done. done. done.
    iIntros "!> Hfmain".
    iApply ewp_frame_bind.
    done. done.
    iSplitR; last first.
    iSplitL "Hg1 Hg2 Hg3 Hg4 Hf1 Hf2 Hfyield Hfpar".
    rewrite -(app_nil_l [AI_basic _]).
    iApply ewp_block.
    done. done. done. done.
    iApply (ewp_label_bind with "[-]").
    2:{ iPureIntro.
        instantiate (5 := []).
        rewrite /lfilled /lfill /= app_nil_r //. }
    rewrite (separate1 (AI_basic _)).
    iApply ewp_seq.
    done.
    iSplitR; last first.
    iSplitR.
    iApply ewp_ref_func.
    done.
    auto_instantiate.
    2: by iIntros (?) "[% _]".
    iIntros (??) "[->->]".
    iSimpl.
    rewrite (separate2 (AI_ref _)).
    iApply ewp_seq.
    done.
    iSplitR; last first.
    rewrite (separate1 (AI_ref _)).
    iSplitR.
    iApply ewp_val_app.
    done.
    iSplitR; last first.
    instantiate (1 := λ v f, (⌜ v = immV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝)%I).
    iApply ewp_wand.
    iApply ewp_ref_func.
    done.
    auto_instantiate.
    iIntros (??) "[->->]".
    iSimpl.
    done.
    by iIntros "!>" (?) "[% _]".
    2: by iIntros (?) "[% _]".
    iIntros (??) "[->->]".
    iSimpl.
    rewrite (separate2 (AI_ref _)).
    (*    rewrite - (app_nil_r [AI_basic _]). *)
    rewrite (separate1 (AI_basic (BI_call 1))).
    iApply ewp_wasm_empty_ctx.
    iApply ewp_base_push.
    done.
    iApply ewp_call_ctx.
    done.
    iApply ewp_base_pull.
    iApply ewp_wasm_empty_ctx.
    iSimpl.
    rewrite (separate3 (AI_ref _)).
    iApply ewp_seq.
    done.
    iSplitR; last first.
    iSplitL.
    unfold yield_par_spec.
    iNext. iApply fupd_ewp.
    iMod (own_alloc Pending) as (γx) "Hγx"; first done.
    iMod (own_alloc Pending) as (γy) "Hγy"; first done.
    iDestruct ("Hspecs" $! P1 (P2 g1 g2) (Q1 γx γy) (Q2 g1 g2) (I g g0 γx γy))%I as (Ψ) "[Hspecyield Hspecpar]".

    iApply (ewp_wand with "[-]").  
    iApply ("Hspecpar" with "[$] [$Hg3 $Hg4] [Hγx Hγy Hg1 Hg2] Hf1 Hf2 Hfyield").
    iLeft. iFrame. 
    iIntros "!>" (f) "HP1 HI Hf1 Hfyield".
    iApply (ewp_call_reference with "Hf1").
    done. done.
    iIntros "!> Hf1".
    iApply (ewp_wand with "[-]").
    iApply (spec_f1_proof with "[] Hf1 Hfyield HP1 HI").
    done. iExact "Hspecyield".
    iIntros (??) "(-> & -> & Hf1 & Hfyield & HQ1 & HI)".
    iFrame. done.
    iIntros "!>" (f) "HP2 HI Hf2 Hfyield".
    iApply (ewp_call_reference with "Hf2").
    done. done.
    iIntros "!> Hf2".
    iApply (ewp_wand with "[-]").
    iApply (spec_f2_proof with "[] Hf2 Hfyield HP2 HI").
    done. iExact "Hspecyield".
    iIntros (??) "(-> & -> & Hf2 & Hfyield & HQ2 & HI)".
    iFrame. done.
    iFrame.
(*    2: by iIntros "!>" (?) "[% _]". *)
    iIntros "!>" (??) "(-> & -> & H)".
    instantiate (1 := λ v f, (∃ _ _, ⌜ v = immV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝ ∗ _)%I).
    iExists γx, γy.
    iSplit; first done.
    iSplit; first done.
    iExact "H".
    iIntros "!>" (??) "(%γx & %γy & -> & -> & HQ1 & HQ2 & HI & Hf1 & Hf2 & Hfyield & Hfpar)".
    2: by iIntros "!>" (?) "(% & % & % & _)".

    iSimpl.
    iDestruct "HQ2" as "(%a & %b & Ha & Hb & %Hab)".
    iApply (ewp_wand with "[Ha Hb]").
    instantiate (1 := λ v f, (⌜ v = immV [_; _] ⌝ ∗ ⌜ f = Build_frame _ _ ⌝ ∗ wgpt g1 a ∗ wgpt g2 b)%I).
                                      
    rewrite (separate1 (AI_basic _)).
    iApply ewp_seq.
    done.
    iSplitR; last first.
    iSplitL "Ha".
    iApply (ewp_get_global with "[] Ha").
    done.
    done.
    auto_instantiate.
    2: by iIntros (?) "([% _] & _)".
    iIntros (??) "[[-> ->] Ha]".
    iSimpl.
    rewrite (separate1 (AI_basic _)).
    iApply ewp_val_app.
    done.
    iSplitR; last first.
    iApply (ewp_wand with "[Hb]").
    iApply (ewp_get_global with "[] Hb").
    done.
    done.
    auto_instantiate.
    2: by iIntros "!>" (?) "[% _]".
    iIntros (??) "[[-> ->] Hb]".
    iFrame. done.
    iSimpl. 
    iIntros (??) "(-> & -> & Ha & Hb)".

    
    iIntros (LI HLI).
    move/lfilledP in HLI; inversion HLI; subst.
    inversion H8; subst.
    iSimpl.
    iApply ewp_label_value.
    done.
    iCombine "HQ1 Ha Hb HI Hf1 Hf2 Hfyield Hfpar" as "H".
    instantiate (1 := λ v f, (∃ γx γy a b, ⌜ v = immV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝ ∗ ⌜ a = 1%Z -> b = 42%Z ⌝ ∗ _)%I).
    iExists γx, γy, a, b. iSplit; first done. iSplit; first done. iSplit; first done.
    iExact "H".
    2: by iIntros (?) "(% & % & % & % & % & _)".
    iIntros (??) "(%γx & %γy & %a & %b & -> & -> & %Hab & HQ1 & Ha & Hb & HI & Hf1 & Hf2 & Hfyield & Hfpar)".
    iSimpl.
    iApply ewp_frame_value.
    done. done.
    iSimpl.
(*    iDestruct "HQ2" as (a b) "(Hga & Hgb & %Hab)".
    iApply (wp_get_global_host with "Hga").
    iIntros "!> !> Hga".
    iApply (wp_get_global_host with "Hgb").
    iIntros "!> Hgb". *)

    
    iApply wp_value. done.
    iApply "HΦ".
    iPureIntro.
    exists a, b. split => //. 
  Qed. 
    
      

End coroutines_client_module.


Section coroutines_client_adequacy.

  Context (Σ: gFunctors).
  Context {inv_preg: invGpreS Σ}.
  Context {na_invg: na_invG Σ}.
  Context {func_preg: gen_heapGpreS N function_closure Σ}.
  Context {tab_preg: gen_heapGpreS (N*N) funcelem Σ}.
  Context {tabsize_preg: gen_heapGpreS N nat Σ}.
  Context {tablimits_preg: gen_heapGpreS N (option N) Σ}.
  Context {mem_preg: gen_heapGpreS (N*N) byte Σ}.
  Context {memsize_preg: gen_heapGpreS N N Σ}.
  Context {memlimit_preg: gen_heapGpreS N (option N) Σ}.
  Context {glob_preg: gen_heapGpreS N global Σ}.
(*  Context {locs_preg: gen_heapGpreS unit frame Σ}. *)
  Context {vis_preg: gen_heapGpreS N module_export Σ}.
  Context {ms_preg: gen_heapGpreS N module Σ}.
  Context {has_preg: gen_heapGpreS N host_action Σ}.
  Context {tag_preg: gen_heapGpreS N function_type Σ}.
  Context {cont_preg: gen_heapGpreS N continuation_resource Σ}.
  Context {one_shotg: one_shotG Σ}.

  Definition near_empty_store : store_record := Build_store_record [] [] [] [] [ (* {| g_mut := MUT_mut; g_val := xx 0 |};  {| g_mut := MUT_mut; g_val := xx 0 |};  {| g_mut := MUT_mut; g_val := xx 0 |};  {| g_mut := MUT_mut; g_val := xx 0 |}*) ] [] [].

  (* The following addresses could be generalised, as long as there are
     no duplicates *)
  Definition yield_exp_addr := 0%N.
  Definition par_exp_addr := 1%N.
(*  Definition a_exp_addr := 2%N.
  Definition b_exp_addr := 3%N. *)
  Definition main_exp_addr := 4%N.

  Definition mod_addr := 0%N.
  Definition mod_addr' := 1%N.

(*  Definition ga := 0.
  Definition gb := 1. *)
  
  Definition exports: vi_store :=
(*     (<[ a_exp_addr := {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx ga) |} ]> ( *)
     (<[ main_exp_addr := {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx (N.to_nat 0)) |} ]> (
    (<[ yield_exp_addr := {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx (N.to_nat 0)) |} ]> (
      <[ par_exp_addr := {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx (N.to_nat 0)) |} ]> ∅)))) (* )) *).
  
  Lemma coroutines_client_adequacy he' S' V' M' HA':
    rtc erased_step (([ (client_module_instantiate yield_exp_addr par_exp_addr (* a_exp_addr b_exp_addr *) main_exp_addr mod_addr mod_addr' (* ga gb *), [], empty_frame) ],
                       (near_empty_store, exports, [coroutines_module; client_module], [] )) : cfg wasm_host_lang)
      ([he'] , (S', V', M', HA')) ->
    (forall v, iris_host.to_val he' = Some v ->
          exists a b, v = (immHV [VAL_num (xx a); VAL_num (xx b)], empty_frame) /\ (a = 1 -> b = 42)).
  Proof.
    intros Hstep.
    pose proof (wp_adequacy Σ wasm_host_lang NotStuck
                  (client_module_instantiate yield_exp_addr par_exp_addr main_exp_addr (* a_exp_addr b_exp_addr *) mod_addr mod_addr' (* ga gb *), [], empty_frame)
                  (near_empty_store, exports, [coroutines_module; client_module], [] )
                  (λ v,  exists a b, v = (immHV [VAL_num (xx a); VAL_num (xx b)], empty_frame) /\ (a = 1 -> b = 42)) 
      ).
    simpl in H.
    
    eassert _.
    { apply H.
      iIntros (Hinv κs).
      iMod (gen_heap_init (∅:gmap N function_closure)) as (func_heapg) "[Hfunc_ctx _]".
      iMod (gen_heap_init (∅:gmap (N*N) funcelem)) as (tab_heapg) "[Htab_ctx _]".
      iMod (gen_heap_init (∅:gmap N nat)) as (tabsize_heapg) "[Htabsize_ctx _]".
      iMod (@gen_heap_init _ _ _ _ _ tablimits_preg (∅:gmap N (option N))) as (tablimit_heapg) "[Htablimit_ctx _]".
      iMod (gen_heap_init (∅:gmap (N*N) byte)) as (mem_heapg) "[Hmem_ctx _]".
      iMod (gen_heap_init (∅:gmap N N)) as (memsize_heapg) "[Hmemsize_ctx _]".
      iMod (@gen_heap_init _ _ _ _ _ memlimit_preg (∅:gmap N (option N))) as (memlimit_heapg) "[Hmemlimit_ctx _]".
      iMod (gen_heap_init (∅:gmap N global)) as (global_heapg) "[Hglobal_ctx _]".
      iMod (gen_heap_init (∅: gmap N function_type)) as (tag_heapg) "[Htag_ctx _]".
      iMod (gen_heap_init (∅: gmap N continuation_resource)) as (cont_heapg) "[Hcont_ctx _]".
      
(*      apply (@gen_heapGpreS_heap) in locs_preg as frame_heapg.
      iMod (ghost_map_alloc (∅:gmap unit frame)) as (γframe) "[Hframe_ctx _]". *)
      apply (@gen_heapGpreS_heap) in vis_preg as vis_heapg.
      iMod (ghost_map_alloc (∅:gmap N module_export)) as (γvis) "[Hvis_ctx _]".
      apply (@gen_heapGpreS_heap) in ms_preg as ms_heapg.
      iMod (ghost_map_alloc (∅:gmap N module)) as (γms) "[Hms_ctx _]".
      apply (@gen_heapGpreS_heap) in has_preg as has_heapg.
      iMod (ghost_map_alloc (∅:gmap N host_action)) as (γhas) "[Hhas_ctx _]".

      iMod (@na_alloc Σ na_invg) as (logrel_nais) "Hna".
      pose wasmg := WasmG Σ Hinv func_heapg cont_heapg tag_heapg tab_heapg tabsize_heapg
                          tablimit_heapg mem_heapg memsize_heapg memlimit_heapg
                          global_heapg.
      pose visgg := HVisG Σ vis_heapg γvis.
      pose msgg := HMsG Σ ms_heapg γms.
      pose hasgg := HAsG Σ has_heapg γhas.
      pose logrel_na_invs := Build_logrel_na_invs _ na_invg logrel_nais.
(*      pose proof (instantiate_client yield_exp_addr par_exp_addr a_exp_addr b_exp_addr mod_addr mod_addr'). *)

      iMod (ghost_map_insert par_exp_addr {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx (N.to_nat 0)) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv1]";[auto|].
      iMod (ghost_map_insert yield_exp_addr {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx (N.to_nat 0)) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv2]";[auto|].
      iMod (ghost_map_insert main_exp_addr {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx (N.to_nat 0)) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv3]";[auto|].
(*      iMod (ghost_map_insert b_exp_addr {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx gb) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv3]";[auto|].
      iMod (ghost_map_insert a_exp_addr {| modexp_name := [Byte.x00]; modexp_desc := MED_global (Mk_globalidx ga) |}
             with "Hvis_ctx") as "[Hvis_ctx Hv4]";[auto|]. *)
      iMod (ghost_map_insert mod_addr coroutines_module with "Hms_ctx") as "[Hms_ctx Hm0]";[auto|].
      iMod (ghost_map_insert mod_addr' client_module with "Hms_ctx") as "[Hms_ctx Hm1]";[auto|].
      
(*      iMod (gen_heap_alloc _ (N.of_nat ga) {| g_mut := MUT_mut; g_val := xx 0 |} with "Hglobal_ctx") as "[Hglobal_ctx [Hg _]]";[auto|].
      iMod (gen_heap_alloc _ (N.of_nat gb) {| g_mut := MUT_mut; g_val := xx 0 |} with "Hglobal_ctx") as "[Hglobal_ctx [Hg' _]]";[auto|]. *)

      iDestruct (instantiate_client $! (λ v, ⌜ exists a b, v = (immHV [VAL_num (xx a); VAL_num (xx b)], empty_frame) /\ (a = 1 -> b = 42) ⌝%I) 
                  with "[$Hm1 $Hm0 Hv1 Hv2 Hv3]") as "HH".
      
(*      iFrame.
      3:{ iSplitL "Hv2"; first by iFrame.
          iSplitL "Hv1"; first by iFrame.
          iSplitL "Hv4"; first by iFrame.
          iSplitL "Hv3"; first by iFrame.
          iFrame.
      }
      done. done. *)

      2: iDestruct ("HH" with "[]") as "HH";[auto|].
      2: iModIntro.
      2: iExists _,_.
      2: iFrame "HH".
      iFrame.
      simpl. iFrame.
    }
    intros v Hval.
    destruct X. eapply adequate_result with (t2 := []).
    apply iris_host.of_to_val in Hval as <-. eauto.
  Qed.

End coroutines_client_adequacy.

Theorem coroutines_example he' S' V' M' HA':
    rtc erased_step (([ (client_module_instantiate yield_exp_addr par_exp_addr main_exp_addr (* a_exp_addr b_exp_addr *) mod_addr mod_addr' (* ga gb *), [], empty_frame) ],
                       (near_empty_store, exports, [coroutines_module; client_module], [] )) : cfg wasm_host_lang)
      ([he'] , (S', V', M', HA')) ->
    (forall v, iris_host.to_val he' = Some v ->
          exists a b, v = (immHV [VAL_num (xx a); VAL_num (xx b)], empty_frame) /\ (a = 1 -> b = 42)).
Proof.
   set (Σ := #[invΣ;
              na_invΣ;
              gen_heapΣ N function_closure;
              gen_heapΣ (N*N) funcelem;
              gen_heapΣ N nat;
              gen_heapΣ N (option N);
              gen_heapΣ (N*N) byte;
              gen_heapΣ N N;
              gen_heapΣ N (option N);
              gen_heapΣ N global;
              gen_heapΣ N module_export;
              gen_heapΣ N module;
               gen_heapΣ N host_action;
               gen_heapΣ N function_type;
               gen_heapΣ N continuation_resource;
               one_shotΣ
      ]).
  eapply (@coroutines_client_adequacy Σ); typeclasses eauto.
Qed.

