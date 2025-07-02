
From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From iris.algebra Require Import auth excl.
From Wasm Require Import type_checker_reflects_typing.
From Wasm.iris.rules Require Export iris_rules iris_example_helper.
From Wasm.iris.host Require Export iris_host.
From Wasm.iris.examples.effects Require Import coroutines_module coroutines_implementation_code.


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section coroutines_client_functions.

  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}.
  Context `{!inG Σ (one_shotR unitO)}.

   Definition f1 :=
     [ BI_const (xx 1);
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
       BI_call 1
     ].


   Definition wgpt a b :=
     N.of_nat a ↦[wg] {| g_mut := MUT_mut ; g_val := xx b |}.
   Definition wgpt_half a b :=
     N.of_nat a ↦[wg]{ DfracOwn (1/2)%Qp } {| g_mut := MUT_mut ; g_val := xx b |}.
   
   Definition P1 addrx : iProp Σ :=
     wgpt_half addrx 0.

   Definition Q1 addrx : iProp Σ :=
     wgpt_half addrx 1.

   Definition P2 addra addrb : iProp Σ :=
     ∃ a b, wgpt addra a ∗ wgpt addrb b. 

   Definition Q2 addra addrb : iProp Σ :=
     ∃ a b, wgpt addra a ∗ wgpt addrb b ∗ ⌜ a = 1 -> b = 1 ⌝ .

   Definition I addrx addry : iProp Σ :=
     (wgpt_half addrx 0 ∗ wgpt addry 0) ∨
       (wgpt_half addrx 1 ∗ wgpt addry 0) ∨
       (wgpt_half addrx 1 ∗ wgpt addry 1).

   Definition spec_f1 f Ψ addr_f1 cl_f1 addrx addry addr_yield cl_yield: iProp Σ :=
     □ (N.of_nat addr_f1 ↦[wf] cl_f1 -∗
        N.of_nat addr_yield ↦[wf] cl_yield -∗
         P1 addrx -∗
         I addrx addry -∗
              EWP [AI_invoke addr_f1] UNDER f <| Ψ |> {{ v; f' ,
                  ⌜ v = immV [] ⌝ ∗
                  ⌜ f' = f ⌝ ∗
                  N.of_nat addr_f1 ↦[wf] cl_f1 ∗
                  N.of_nat addr_yield ↦[wf] cl_yield ∗
                  Q1 addrx ∗
                  I addrx addry
       }})%I.
   
   Definition spec_f2 f Ψ addr_f2 cl_f2 addrx addry addra addrb addr_yield cl_yield: iProp Σ :=
     □ (N.of_nat addr_f2 ↦[wf] cl_f2 -∗
          N.of_nat addr_yield ↦[wf] cl_yield -∗
          P2 addra addrb -∗
          I addrx addry -∗
             EWP [AI_invoke addr_f2] UNDER f <| Ψ |> {{ v; f' ,
                ⌜ v = immV [] ⌝ ∗
                ⌜ f' = f ⌝ ∗
                N.of_nat addr_f2 ↦[wf] cl_f2 ∗
                N.of_nat addr_yield ↦[wf] cl_yield ∗
                Q2 addra addrb ∗
                I addrx addry }})%I.

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


  Definition client_inst addr_yield addr_par addr_f1 addr_f2 addr_main addrx addry addra addrb :=
    {| inst_types := [ emptyt; par_type ];
      inst_funcs := [ addr_yield; addr_par; addr_f1; addr_f2; addr_main ] ;
      inst_tab := [];
      inst_memory := [];
      inst_globs := [addrx; addry; addra; addrb];
      inst_tags := [] |}.
   
   Lemma spec_f1_proof f Ψ addr_f1 cl_f1 addrx addry addr_yield cl_yield addr_par addr_f2 addr_main addra addrb :
     cl_f1 = FC_func_native (client_inst addr_yield addr_par addr_f1 addr_f2 addr_main addrx addry addra addrb) emptyt [] f1 ->
     yield_spec addr_yield cl_yield Ψ (I addrx addry)
       ⊢ spec_f1 f Ψ addr_f1 cl_f1 addrx addry addr_yield cl_yield.
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
     iApply ewp_seq.
     done.
     iSplitR; last first.
     iAssert (wgpt addrx 0 ∗ wgpt addry 0)%I with "[HI HP1]" as "[Hx Hy]".
     { iDestruct "HI" as "[[Hx Hy] | [[Hx Hy] | [Hx Hy]]]".
       iFrame.
       all: iDestruct (pointsto_agree with "Hx HP1") as "%Habs" => //. } 
     iSplitL "Hx".
     iApply (ewp_set_global with "[] Hx").
     done.
     auto_instantiate.
     2: by iIntros (?) "[[% _] _]".
     iIntros (??) "[[-> ->] Hx]".
     iSimpl.
     rewrite (separate1 (AI_basic _)).
     iApply ewp_seq.
     done.
     iSplitR; last first.
     simpl.
     iDestruct "Hx" as "[Hx1 Hx2]".
     iSplitR "Hx2".
     iApply ewp_call.
     done.
     iApply ("Hyield" with "[Hx1 Hy] Hwfyield").
     simpl.
     iRight. iLeft. iFrame.
     iIntros (??) "(-> & -> & HI & Hwfyield)".
     iSimpl.
     iAssert (wgpt addrx 1 ∗ ∃ i, wgpt addry i)%I with "[HI Hx2]" as "(Hx & %i & Hy)".

     { iDestruct "HI" as "[[Hx Hy] | [[Hx Hy] | [Hx Hy]]]".
       iDestruct (pointsto_agree with "Hx Hx2") as %Habs => //.
       all: iFrame. }
     iApply (ewp_wand with "[Hy]").
     iApply (ewp_set_global with "[] Hy").
     done.
     auto_instantiate.
     2: by iIntros (?) "[% _]".
     iIntros (??) "[[-> ->] Hy]".
     simpl.
     iIntros (LI HLI).
     move/lfilledP in HLI; inversion HLI; subst.
     inversion H8; subst.
     iSimpl.
     iApply ewp_label_value.
     done.
     instantiate (1 := λ v f,  (⌜ v = immV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝ ∗ _)%I).
     iSplitR; first done.
     iSplitR; first done.
     iCombine "Hwfyield Hx Hy" as "H".
     iExact "H".
     iIntros (??) "(-> & -> & Hwfyield & Hx & Hy)".
     iApply ewp_frame_value.
     done. done.
     iSplit; first done.
     iSplit; first done.
     iFrame.
     iDestruct "Hx" as "[Hx1 Hx2]".
     iFrame.
     iRight. iRight.
     iFrame.
     iIntros (?) "[% _]" => //.
   Qed. 
     
   Lemma spec_f2_proof f Ψ addr_f2 cl_f2 addrx addry addr_yield cl_yield addr_par addr_f1 addr_main addra addrb :
     cl_f2 = FC_func_native (client_inst addr_yield addr_par addr_f1 addr_f2 addr_main addrx addry addra addrb) emptyt [] f2 ->
     yield_spec addr_yield cl_yield Ψ (I addrx addry)
       ⊢ spec_f2 f Ψ addr_f2 cl_f2 addrx addry addra addrb addr_yield cl_yield.
   Proof.
     iIntros (->) "#Hyield !> Hwf2 Hwfyield HP2 HI".
     iDestruct "HP2" as (a b) "[Ha Hb]".
     iDestruct "HI" as "[[Hx Hy] | [[Hx Hy] | [Hx Hy]]]".
     - (* Case 1 *) 
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
       iAssert (I addrx addry)%I with "[Hx Hy]" as "HI".
       by iLeft; iFrame.
       iSplitR; last first.
       iSplitL "HI Hwfyield".
       iApply ewp_call.
       done.
       iApply ("Hyield" with "HI Hwfyield").
       2: by iIntros (?) "[% _]".
       iIntros (??) "(-> & -> & HI & Hwfyield)".
       iDestruct "HI" as "[[Hx Hy] | [[ Hx Hy ] | [Hx Hy]]]".

       iSimpl.
        rewrite (separate1 (AI_basic _)).
        iApply ewp_seq.
        try done.
        iSplitR; last first.
        try iSplitL "Hx".
        try iApply (ewp_get_global with "[] Hx").
        try done.
        try by auto_instantiate.
        try by iIntros (?) "[[% _] _]".
        iIntros (??) "[[-> ->] Hx]".
        iSimpl.
        iApply (ewp_wand with "[Hb]").
        try iApply (ewp_set_global with "[] Hb").
        try done.
        try auto_instantiate.
        iIntros (??) "[[-> ->] Hb]".
        iIntros (LI HLI).
        move/lfilledP in HLI; inversion HLI; subst.
        inversion H8; subst.
        iApply ewp_label_value.
        try done.
       instantiate (1 := λ v f, (⌜ v = immV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝ ∗ _ ∗ (_ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _ ∨ _))%I).
        iSplit; first done.
        iSplit; first done.
        iSplitL "Hwfyield"; first iExact "Hwfyield".
        iCombine "Ha Hb Hx Hy" as "H".
       iLeft; iExact "H".
        iRight.
       iLeft; iExact "H".
        iRight.
       iLeft; iExact "H".
        iRight.
       iLeft; iExact "H".
        iRight.
       iLeft; iExact "H".
        iRight.
       iLeft; iExact "H".
        iRight.
       iLeft; iExact "H".
        iRight.
       iLeft; iExact "H".
       iRight.
       iExact "H".
     }
     2: by iIntros (?) "[% _]".
     iIntros (??) "(-> & -> & Hwfyield & H)".
     iApply ewp_frame_value.
     done. done.
     iSplit; first done.
     iSplit; first done.
     iFrame.
     iDestruct "H" as "[ (Ha & Hb & Hx & Hy) | [ (Ha & Hb & Hx & Hy) | [ (Ha & Hb & Hx & Hy) | [ (Ha & Hb & Hx & Hy) | [ (Ha & Hb & Hx & Hy) | [ (Ha & Hb & Hx & Hy) | [ (Ha & Hb & Hx & Hy) | [ (Ha & Hb & Hx & Hy) | (Ha & Hb & Hx & Hy) ]]]]]]]]".
     all: iFrame.
     all: iSplit; first try done.
       
       

     


End coroutines_client_functions.

Section coroutines_client_module.

  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}.

  Definition client_module :=
    {|
      mod_types := [ emptyt; par_type ];
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
          modfunc_type := Mk_typeidx 0;
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
          modglob_init := [BI_const (xx 0)] |};
        {| modglob_type := {| tg_mut := MUT_mut ; tg_t := T_i32 |} ;
          modglob_init := [BI_const (xx 0)] |};
        {| modglob_type := {| tg_mut := MUT_mut ; tg_t := T_i32 |} ;
          modglob_init := [BI_const (xx 0)] |}
      ];
      mod_elem := [] ;
      mod_data := [] ;
      mod_start := Some {| modstart_func := Mk_funcidx 4 |} ; 
      mod_imports := [
        {| imp_module := String.list_byte_of_string "coroutines module";
          imp_name := String.list_byte_of_string "yield function";
          imp_desc := ID_func 0
        |};
        {| imp_module := String.list_byte_of_string "coroutines module";
          imp_name := String.list_byte_of_string "par function";
          imp_desc := ID_func 1
        |}
      ];
      mod_exports := [];
      mod_tags := []
    |}.

  Definition impts := [ET_func emptyt ; ET_func par_type].

  Lemma client_module_typing :
    module_typing client_module impts [].
  Proof.
    unfold module_typing.
    exists [emptyt; emptyt; emptyt], (repeat {| tg_mut := MUT_mut ; tg_t := T_i32 |} 4).
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
    - constructor; last constructor; last constructor.
      all: cbn; apply/andP; split => //.
  Qed.


  Definition client_module_instantiate yield_exp_addr par_exp_addr mod_addr mod_addr' :=
    [ ID_instantiate [ yield_exp_addr ; par_exp_addr ] mod_addr [] ;
      ID_instantiate [] mod_addr' [ yield_exp_addr ; par_exp_addr ]
    ].

  Notation "{{{{ P }}}} es {{{{ v , Q }}}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).

  Lemma instantiate_client yield_exp_addr par_exp_addr mod_addr mod_addr' : 
    
    ⊢ {{{{ 
              mod_addr ↪[mods] coroutines_module ∗
                mod_addr' ↪[mods] client_module ∗
                (∃ exp1, yield_exp_addr ↪[vis] exp1) ∗
                (∃ exp2, par_exp_addr ↪[vis] exp2)
      }}}}
      ((client_module_instantiate yield_exp_addr par_exp_addr mod_addr mod_addr',
         [], empty_frame) : host_expr) 
        {{{{  x,  ⌜x = (immHV [], empty_frame)⌝ ∗
                         mod_addr ↪[mods] coroutines_module ∗
                         mod_addr' ↪[mods] client_module ∗
                         ∃ inst addra addrb addrx addry vala valb valx valy addr_f1 cl_f1 addr_f2 cl_f2 addr_main cl_main,
                           wgpt addra valb ∗
                             wgpt addrb valb ∗
                             wgpt addrx valx ∗
                             wgpt addry valy ∗
                             ⌜ vala = 1 -> valb = 1 ⌝ ∗
                            N.of_nat addr_f1 ↦[wf] cl_f1 ∗
                            N.of_nat addr_f2 ↦[wf] cl_f2 ∗
                            N.of_nat addr_main ↦[wf] cl_main ∗
                            
                         
        }}}} .
  Proof.
      

   
     
