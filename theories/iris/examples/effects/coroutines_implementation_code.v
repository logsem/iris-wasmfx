From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.rules Require Export iris_rules iris_example_helper.
From Wasm Require Import type_checker_reflects_typing.

Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section yield_par.
  

  Definition yield := [ BI_suspend (Mk_tagident 0) ].

  Definition par : seq.seq basic_instruction := [
      BI_const (xx 0);
      BI_set_local 4;
      BI_get_local 0;
      BI_contnew (Type_lookup 0);
      BI_set_local 2;
      BI_get_local 1;
      BI_contnew (Type_lookup 0);
      BI_set_local 3;
      BI_loop (Tf [] []) [
          BI_block (Tf [] [T_ref (T_contref (Tf [] []))]) [
              BI_get_local 2;
              BI_resume (Type_lookup 0) [ HC_catch (Mk_tagident 0) 0 ];
              BI_get_local 4;
              BI_br_if 2;
              BI_const (xx 1);
              BI_set_local 4;
              BI_get_local 3;
              BI_set_local 2;
              BI_br 1
            ];
          BI_set_local 2;
          BI_get_local 4;
          BI_br_if 0;
          BI_get_local 2;
          BI_get_local 3;
          BI_set_local 2;
          BI_set_local 3;
          BI_br 0
        ]
    ].

  Definition emptyt := Tf [] [].
  Definition par_type := Tf [T_ref (T_funcref emptyt); T_ref (T_funcref emptyt)] [].
  Definition par_locs := [
       T_ref (T_contref emptyt);
       T_ref (T_contref emptyt);
       T_num T_i32
    ].

  Definition t_ctxt :=
      {| tc_types_t := [emptyt; par_type];
      tc_func_t := [emptyt; par_type];
      tc_global := [];
      tc_table := [];
      tc_memory := [];
      tc_local := [];
      tc_label := [[]];
      tc_return := Some [];
      tc_refs := [];
        tc_tags_t := [emptyt] |}.

  Lemma yield_typing : be_typing t_ctxt yield emptyt.
  Proof.
    apply/b_e_type_checker_reflects_typing.
    done.
  Qed.

  Definition t_ctxt_par :=
      {| tc_types_t := [emptyt; par_type];
      tc_func_t := [emptyt; par_type];
      tc_global := [];
      tc_table := [];
      tc_memory := [];
        tc_local :=
          [T_ref (T_funcref emptyt);
           T_ref (T_funcref emptyt) ] ++ par_locs ;
      tc_label := [[]];
      tc_return := Some [];
      tc_refs := [];
        tc_tags_t := [emptyt] |}.

  Lemma par_typing : be_typing t_ctxt_par par emptyt.
  Proof.
    rewrite /par separate2.
    eapply bet_composition'.
    - apply/b_e_type_checker_reflects_typing.
      simpl.
      done.
    - rewrite separate3.
      eapply bet_composition'.
      + apply/b_e_type_checker_reflects_typing.
        simpl.
        done.
      + rewrite separate3.
        eapply bet_composition'.
        * apply/b_e_type_checker_reflects_typing.
          simpl.
          done.
        * constructor.
          rewrite (separate1 (BI_block _ _)).
          eapply bet_composition'.
          -- constructor.
             rewrite (separate4 (BI_get_local _)).
             eapply bet_composition'.
             ++ apply/b_e_type_checker_reflects_typing.
                simpl.
                done.
             ++ apply/b_e_type_checker_reflects_typing.
                simpl.
                done.
          -- rewrite separate4.
             eapply bet_composition'.
             ++ apply/b_e_type_checker_reflects_typing.
                simpl.
                done.
             ++ apply/b_e_type_checker_reflects_typing.
                simpl.
                done.
  Qed.


  Definition coroutine_inst yield_addr par_addr tag_addr :=
    {| inst_types := [ emptyt; par_type ];
      inst_funcs := [ yield_addr; par_addr ] ;
      inst_tab := [];
      inst_memory := [];
      inst_globs := [];
      inst_tags := [ tag_addr ] |}.
  
  Definition closure_yield yield_addr par_addr tag_addr :=
    FC_func_native (coroutine_inst yield_addr par_addr tag_addr) emptyt [] yield.

  Definition closure_par yield_addr par_addr tag_addr :=
    FC_func_native (coroutine_inst yield_addr par_addr tag_addr) par_type par_locs par.

  Opaque upcl. 

  Definition yield_par_spec `{!wasmG Σ} addr_yield addr_par cl_yield cl_par : iProp Σ :=
      (∀ P1 P2 Q1 Q2 I, ∃ Ψ,

                                              (□ (∀ f, I -∗ N.of_nat addr_yield ↦[wf] cl_yield  -∗ EWP [AI_invoke addr_yield] UNDER f <| Ψ |> {{ v ; f , ⌜ v = immV [] ⌝ ∗ I ∗ N.of_nat addr_yield ↦[wf] cl_yield }})) ∗
                                              (∀ f1 f2, □ (∀ f,  P1 -∗ P2 -∗ I -∗ (□ (P1 -∗ I -∗ EWP [AI_ref f1; AI_basic (BI_call_reference (Type_explicit emptyt))] UNDER empty_frame <| Ψ |> {{ v ; f , ⌜ v = immV [] ⌝ ∗ Q1 ∗ I }})) -∗ (□ (P2 -∗ I -∗ EWP [AI_ref f2; AI_basic (BI_call_reference (Type_explicit emptyt))] UNDER empty_frame <| Ψ |> {{ v ; f , ⌜ v = immV [] ⌝ ∗ Q2 ∗ I }})) -∗ N.of_nat addr_par ↦[wf] cl_par -∗ EWP [AI_ref f1; AI_ref f2; AI_invoke addr_par] UNDER f {{ v ; f , ⌜ v = immV [] ⌝ ∗ Q1 ∗ Q2 ∗ I ∗  N.of_nat addr_par ↦[wf] cl_par  }}))
      )%I.
  
  Lemma yield_par_spec_proof  addr_yield addr_par cl_yield cl_par `{!wasmG Σ}:
    forall addr_tag,
    cl_yield = closure_yield addr_yield addr_par addr_tag ->
    cl_par = closure_par addr_yield addr_par addr_tag ->
    N.of_nat addr_tag ↦□[tag] Tf [] []
    ⊢ yield_par_spec addr_yield addr_par cl_yield cl_par.
  Proof.
    iIntros (addr_tag -> ->) "#Htag".
    iIntros (P1 P2 Q1 Q2 I).
    iExists (λ eid, match eid with
                    | SuspendE (Mk_tagidx n) => if (Nat.eqb n addr_tag) then (! immV [] {{ I }} ; ? immV [] {{ I }})%iprot else iProt_bottom
                    | _ => iProt_bottom
                    end).
    iSplit.
    - (* yield *)
      iIntros "!>" (f) "HI Hcl".
      rewrite - (app_nil_l [AI_invoke _]).
      iApply (ewp_invoke_native with "Hcl").
      done. done. done.
      iIntros "!> Hcl".
      iApply ewp_frame_bind.
      done. done.
      iSplitR; last first.
      rewrite - (app_nil_l [AI_basic _]).
      iSplitL "HI".
      iApply ewp_block.
      done. done. done. done.
      iNext.
      iApply (ewp_label_bind with "[HI]").
      2:{ iPureIntro. unfold lfilled, lfill => /=.
          instantiate (5 := []) => /=.
          rewrite app_nil_r. done. }
      rewrite - (app_nil_l [AI_basic _]).
      iApply ewp_suspend_desugar.
      done. done.
      2: by instantiate (1 := []).
      by instantiate (1 := []).
      iFrame "Htag".
      iApply ewp_suspend.

      rewrite Nat.eqb_refl.
      rewrite (upcl_tele' [tele] [tele]).
      iSimpl.
      iFrame.
      iSplit; first done.
      iIntros "!> HI".
      iIntros (LI HLI).
      move/lfilledP in HLI.
      inversion HLI; subst.
      inversion H8; subst.
      iSimpl.
      iApply (ewp_label_value with "[HI]").
      done.
(*      auto_instantiate. *)
      by instantiate (1 := λ v f, (⌜ v = immV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝ ∗ I)%I); iFrame. 

      2: by iIntros (?) "[% _]".
      iIntros (??) "(-> & -> & HI)".
      iApply (ewp_frame_value with "[-]").
      done.
      done.
      iFrame. done. 
    - (* par *)
      iIntros (f1 f2).
      iIntros "!>" (f) "HP1 HP2 HI #Hspec1 #Hspec2 Hcl".
      rewrite (separate2 (AI_ref _) (AI_ref _)).
      iApply (ewp_invoke_native with "Hcl").
      done. done. done.
      iIntros "!> Hcl".
      iApply ewp_frame_bind.
      done. done.

      instantiate (1 := λ v f, (⌜ v = immV [] ⌝ ∗ Q1 ∗ Q2 ∗ I)%I).
      iSplitR; first by iIntros (?) "[% _]".
      
      iSplitR "Hcl" ; last first.
      { iIntros (??) "(-> & HQ1 & HQ2 & HI)".
        iApply ewp_frame_value.
        rewrite to_of_val //.
        done.
        iFrame. done. }
      
      rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
      iApply ewp_block.
      done. done. done. done.
      iNext.
      iApply (ewp_label_bind with "[-]").
      2:{ iPureIntro. instantiate (5 := []).
          rewrite /lfilled /lfill /= app_nil_r //. }

      rewrite (separate2 (AI_basic _)).
      iApply ewp_seq.
      done.
      iSplitR; last first.
      iSplitR.
      fold (AI_const (VAL_num (xx 0))).
      iApply ewp_set_local.
      simpl.
      lia.
      iSimpl.
      auto_instantiate.
      2: by iIntros (?) "[% _]".
      iIntros (??) "[-> ->]".
      iSimpl.
      rewrite (separate1 (AI_basic (BI_get_local _))).
      iApply ewp_seq.
      done.
      iSplitR; last first.
      iSplitR.
      iApply ewp_get_local.
      done.
      auto_instantiate.
      2: by iIntros (?) "[% _]".
      iIntros (??) "[-> ->]".
      iSimpl.
      rewrite (separate2 _ (AI_basic (BI_contnew _))).
      iApply ewp_seq.
      done.
      iSplitR; last first.
      iSplitR.
      iApply ewp_contnew.
      done.
      2: by iIntros (?) "(%kaddr & % & _)".
      iIntros (??) "(%kaddr1 & -> & -> & Hcont1)".
      iSimpl.
      rewrite (separate2 (AI_ref_cont _)).
      iApply ewp_seq.
      done.
      iSplitR; last first.
      iSplitR.
      fold (AI_const (VAL_ref (VAL_ref_cont kaddr1))).
      iApply ewp_set_local.
      simpl. lia.
      iSimpl.
      auto_instantiate.
      2: by iIntros (?) "[% _]".
      iIntros (??) "[-> ->]".
      iSimpl.
      rewrite (separate1 (AI_basic (BI_get_local _))).
      iApply ewp_seq.
      done.
      iSplitR; last first.
      iSplitR.
      iApply ewp_get_local.
      done.
      auto_instantiate.
      2: by iIntros (?) "[% _]".
      iIntros (??) "[-> ->]".
      iSimpl.
      rewrite (separate2 _ (AI_basic (BI_contnew _))).
      iApply ewp_seq.
      done.
      iSplitR; last first.
      iSplitR.
      iApply ewp_contnew.
      done.
      2: by iIntros (?) "(%kaddr & % & _)".
      iIntros (??) "(%kaddr2 & -> & -> & Hcont2)".
      iSimpl.
      rewrite (separate2 (AI_ref_cont _)).
      iApply ewp_seq.
      done.
      iSplitR; last first.
      iSplitR.
      fold (AI_const (VAL_ref (VAL_ref_cont kaddr2))).
      iApply ewp_set_local.
      simpl. lia.
      iSimpl.
      auto_instantiate.
      2: by iIntros (?) "[% _]".
      iIntros (??) "[-> ->]".
      iSimpl.
      rewrite - (app_nil_l [AI_basic (BI_loop _ _)]).

      (*      instantiate (3 := λ f, (∃ locs, ⌜ f = Build_frame locs (coroutine_inst addr_yield addr_par addr_tag) ⌝)%I). 

      instantiate (3 := Φf'). *)
      remember ( λ eid : effect_identifier,
                   match eid with
                   | SuspendE (Mk_tagidx n) =>
                       if n =? addr_tag
                       then (!immV []{{ I }};? immV [] {{ I }} )%iprot
                       else iProt_bottom
                   | _ => iProt_bottom
                   end
               ) as Ψ.
      (*      instantiate (3 := λ f, True%I).
      instantiate (2 := λ f, True%I).
      instantiate (1 := λ v, (⌜ v = immV [] ⌝ ∗ Q1 v ∗ Q2 v ∗ I)%I). *)
      
      iAssert ( ∀ kaddra kaddrb b conta,
                  (I ∗ N.of_nat kaddra ↦[wcont] Cont_hh emptyt conta  ∗
                     (I -∗ ∃ LI, ⌜ hfilled No_var conta [] LI ⌝ ∗ ▷ EWP LI UNDER empty_frame <| Ψ |> {{ v ; f , ⌜ v = immV [] ⌝ ∗ Q1 ∗ I }})  ∗
                     ((⌜ b = 0 ⌝ ∗ ∃ contb, N.of_nat kaddrb ↦[wcont] Cont_hh emptyt contb ∗ (I -∗ ∃ LI, ⌜ hfilled No_var contb [] LI ⌝ ∗ ▷ EWP LI UNDER empty_frame <| Ψ |> {{ v ; f , ⌜ v = immV [] ⌝ ∗ Q2 ∗ I }})) ∨ (⌜ b = 1 ⌝ ∗ Q2))) ∨
                    (I ∗ N.of_nat kaddra ↦[wcont] Cont_hh emptyt conta  ∗
                       (I -∗ ∃ LI, ⌜ hfilled No_var conta [] LI ⌝ ∗ ▷ EWP LI UNDER empty_frame <| Ψ |> {{ v ; f , ⌜ v = immV [] ⌝ ∗ Q2 ∗ I }})  ∗
                       ((⌜ b = 0 ⌝ ∗ ∃ contb, N.of_nat kaddrb ↦[wcont] Cont_hh emptyt contb ∗ (I -∗ ∃ LI, ⌜ hfilled No_var contb [] LI ⌝ ∗ ▷ EWP LI UNDER empty_frame <| Ψ |> {{ v ; f , ⌜ v = immV [] ⌝ ∗ Q1 ∗ I }})) ∨ (⌜ b = 1 ⌝ ∗ Q1)))  -∗
                                                                                                                                                                                                                                              EWP [] ++
                                                                                                                                                                                                                                              [AI_basic
                                                                                                                                                                                                                                                 (BI_loop (Tf [] [])
                                                                                                                                                                                                                                                    [BI_block (Tf [] [T_ref (T_contref (Tf [] []))])
                                                                                                                                                                                                                                                       [BI_get_local 2; BI_resume (Type_lookup 0) [HC_catch (Mk_tagident 0) 0];
                                                                                                                                                                                                                                                        BI_get_local 4; BI_br_if 2; BI_const (xx 1); 
                                                                                                                                                                                                                                                        BI_set_local 4; BI_get_local 3; BI_set_local 2; 
                                                                                                                                                                                                                                                        BI_br 1]; BI_set_local 2; BI_get_local 4; BI_br_if 0; 
                                                                                                                                                                                                                                                     BI_get_local 2; BI_get_local 3; BI_set_local 2; 
                                                                                                                                                                                                                                                     BI_set_local 3; BI_br 0])]
                                                                                                                                                                                                                                              UNDER {|
                                                                                                                                                                                                                                                f_locs :=
                                                                                                                                                                                                                                                  [VAL_ref (VAL_ref_func f1); VAL_ref (VAL_ref_func f2);
                                                                                                                                                                                                                                                   VAL_ref (VAL_ref_cont kaddra); VAL_ref (VAL_ref_cont kaddrb);
                                                                                                                                                                                                                                                   VAL_num (xx b)];
                                                                                                                                                                                                                                                f_inst := coroutine_inst addr_yield addr_par addr_tag
                                                                                                                                                                                                                                              |} {{w;f0,ewp_wasm_ctx ⊤ (of_val w) f0 (λ _ : effect_identifier, iProt_bottom)
                                                                                                                                                                                                                                                          (λ (w0 : iris_resources.val) (_ : frame), ⌜
                                                                                                                                                                                                                                                                                                      w0 = immV []⌝ ∗ Q1 ∗ Q2 ∗ I) 1
                                                                                                                                                                                                                                                          (LH_rec [] 0 [] (LH_base [] []) [])  }}
              )%I as "H".
      2:{ iApply ("H" $! kaddr1 kaddr2 0).
          iLeft.
          iFrame "Hcont1 HI".
          iSplitL "HP1".
          iIntros "HI".
          iExists _; iSplit; first iPureIntro.
          rewrite /hfilled /hfill //=.
          iApply ("Hspec1" with "HP1 HI").
          iLeft.
          iSplit; first done.
          iFrame "Hcont2".
          iIntros "HI".
          iExists _; iSplit; first iPureIntro.
          rewrite /hfilled /hfill //=.
          iApply ("Hspec2" with "HP2 HI"). }
      iLöb as "IH".
      iIntros (kaddra kaddrb b conta) "H".
      iDestruct "H" as "[H | H]".
      + (* Case where $current is the $f1 function *)

        iApply ewp_loop.
        done. done. done. done.
        iNext.
        iApply (ewp_label_bind with "[-]").
        2:{ iPureIntro. instantiate (5 := []).
            rewrite /lfilled /lfill /= app_nil_r //. }
        rewrite (separate1 (AI_basic (BI_block _ _))).
        iApply ewp_seq.
        done.
        iSplitR; last first.
        rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
        iSplitL.
        iApply ewp_block.
        done. done. done. done.
        iNext.
        iApply (ewp_label_bind with "[-]").
        2:{ iPureIntro. instantiate (5 := []).
            rewrite /lfilled /lfill /= app_nil_r //. }
        rewrite (separate1 (AI_basic (BI_get_local _))).
        iApply ewp_seq.
        done.
        iSplitR; last first.
        iSplitR.
        iApply ewp_get_local.
        done.
        auto_instantiate.
        2: by iIntros (?) "[% _]".
        iIntros (??) "[-> ->]".
        iSimpl.
        rewrite (separate2 (AI_ref_cont _)).
        iApply ewp_seq.
        done.
        iSplitR; last first.
        iDestruct "H" as "(HI & Hconta & Hruna & Hb)".
        iDestruct ("Hruna" with "HI") as (LI) "[%HLI Hruna]".
        iSplitR "Hb".
        rewrite -(app_nil_l [AI_ref_cont _;_]).
        
        iApply (ewp_resume with "[$Hconta $Hruna]").
        done. done. done.
        simpl. instantiate (1 := [_]) => //.
        unfold agree_on_uncaptured => /=.
        repeat split => //.
        intros i.
        destruct (i == Mk_tagidx addr_tag) eqn:Hi => //.
        move/eqP in Hi.
        intros _.
        subst Ψ; simpl.
        destruct i => //.
        destruct (n =? addr_tag) eqn:Hn => //.
        apply Nat.eqb_eq in Hn as ->.
        exfalso; by apply Hi.
        by subst Ψ.
        by subst Ψ.
        by destruct (hfilled No_var conta [] LI).
        iSplitR.
        by iIntros (?) "[% ?]".
        iSplitR; last first.
        iFrame "Htag".
        iSplitR.
        iIntros "!>" (w) "(-> & HQ & HI)".
        iApply (ewp_prompt_value with "[-]").
        rewrite to_of_val => //.
        instantiate (1 := λ v, ((⌜ v = immV [] ⌝ ∗ I ∗ Q1) ∨ _)%I).
        iLeft. iFrame. done. 
        iSimpl.
        iSplitL; last done.
        iIntros "!>" (vs kaddr h) "Hcont HΨ".
        iApply ewp_value.
        unfold IntoVal.
        apply of_to_val.
        unfold to_val.
        rewrite map_app merge_app.
        specialize (@const_list_to_val (v_to_e_list vs)) as (vs' & Htv & Hinj).
        apply v_to_e_is_const_list.
        apply v_to_e_inj in Hinj as ->.
        unfold to_val in Htv.
        destruct (merge_values _); try by exfalso.
        inversion Htv; subst.
        simpl.
        done.

        iRight.
        instantiate (1 := (∃ kaddr vs h, ⌜ v = brV _ ⌝ ∗ _)%I). 
        iExists kaddr, vs, h. iSplit; first done.
        iCombine "Hcont HΨ" as "H".
        iExact "H".
        iIntros "[[% _] | (% & % & % & % & _)]" => //.
        
        iIntros (??) "[H ->]".
        iDestruct "H" as "[(-> & HI & HQ) | (%kaddr & %vs & %h & -> & Hcont & HΨ)]".
        * (* Case 1: the continuation terminated execution *)
          iSimpl.
          rewrite (separate1 (AI_basic (BI_get_local _))).
          iApply ewp_seq.
          done.
          iSplitR; last first.
          iSplitR.
          iApply ewp_get_local.
          done.
          auto_instantiate.
          2: by iIntros (?) "[% _]".
          iIntros (??) "[-> ->]".
          iSimpl.
          iDestruct "Hb" as "[(-> & %contb & Hcont & Hrunb) | (-> & HQ2)]". (* Changed %Hb to -> twice *)
          -- (* Case 1a: the other continuation is not done *)
            rewrite (separate2 (AI_basic (BI_const _))).
            iApply ewp_seq.
            done.
            iSplitR; last first.
            iSplitR.
            iApply ewp_br_if_false.
            by subst.
            auto_instantiate.
            2: by iIntros (?) "[% _]".
            iIntros (??) "[-> ->]".
            iSimpl.
            rewrite (separate2 (AI_basic (BI_const _))).
            iApply ewp_seq.
            done.
            iSplitR; last first.
            iSplitR.
            fold (AI_const (VAL_num (xx 1))).
            iApply ewp_set_local.
            simpl; lia.
            iSimpl.
            auto_instantiate.
            2: by iIntros (?) "[% _]".
            iIntros (??) "[-> ->]".
            iSimpl.
            rewrite (separate1 (AI_basic (BI_get_local _))).
            iApply ewp_seq.
            done.
            iSplitR; last first.
            iSplitR.
            iApply ewp_get_local.
            done.
            auto_instantiate.
            2: by iIntros (?) "[% _]".
            iIntros (??) "[-> ->]".
            iSimpl.
            rewrite (separate2 (AI_ref_cont _)).
            iApply ewp_seq.
            done.
            iSplitR; last first.
            iSplitR.
            fold (AI_const (VAL_ref (VAL_ref_cont kaddrb))).
            iApply ewp_set_local.
            simpl; lia.
            iSimpl.
            auto_instantiate.
            2: by iIntros (?) "[% _]".
            iIntros (??) "[-> ->]".
            iSimpl.
            iApply ewp_value.
            apply of_to_val. done.
            (*            iSplitL; last first.
            instantiate (1 := λ f, (⌜ b = 0 ⌝ ∗ ⌜ f = Build_frame _ _ ⌝ ∨ ⌜ b = 1 ⌝ ∗ ⌜ f = Build_frame _ _ ⌝ ∨ ⌜ f = Build_frame _ _ ⌝ )%I).  
            by iLeft. 
            iIntros (?) "[[_ ->] | [[% _] | %Hf]]"; try by subst b. *)
            iIntros (LI' HLI').
            move/lfilledP in HLI'; inversion HLI'; subst.
            inversion H8; subst.
            iSimpl.
            iApply ewp_value.
            apply of_to_val.
            done.
            iSimpl.
            instantiate (1 := λ v f, ((∃ contb, ⌜ v = brV (VH_rec [] 1 [] (VH_base 0 [] []) []) ⌝ ∗ ⌜ f = Build_frame _ _ ⌝ ∗ _) ∨ (⌜ v = brV (VH_rec [] 1 []
                                                                                                                                                 (VH_base 1 []
                                                                                                                                                    [AI_basic (BI_const (xx 1)); AI_basic (BI_set_local 4);
                                                                                                                                                     AI_basic (BI_get_local 3); AI_basic (BI_set_local 2); 
                                                                                                                                                     AI_basic (BI_br 1)]) []) ⌝ ∗ ⌜ f = Build_frame _ _ ⌝ ∗ _) ∨ (∃ kaddr h, ⌜ v = immV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝%I ∗ _))%I). 
            iLeft. iExists contb.
            iSimpl.
            iSplit; first done. 
            iSplit; first done.            
            iCombine "Hcont Hrunb HI HQ" as "H".
            iExact "H".
          -- (* Case 1b: the other continuation is also done *)
            rewrite (separate2 (AI_basic (BI_const _))).
            iApply ewp_seq.
            done.
            iSplitR; last first.
            iSplitR.
            iApply ewp_br_if_true.
            by subst.
            iApply ewp_value.
            apply of_to_val.
            done.
            iNext.
            by instantiate (1 := λ v f, (⌜ v = brV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝)%I).
            2: by iIntros (?) "[% _]".
            iIntros (??) "[-> ->]".
            iSimpl.
            iApply ewp_value.
            apply of_to_val.
            done.
            (*            iSplitL; last first.
            by iRight.
            iIntros (?) "[[% _] | [_ ->]]"; first by subst. *)
            iIntros (LI' HLI').
            move/lfilledP in HLI'; inversion HLI'; subst.
            inversion H8; subst.
            iSimpl.
            iApply ewp_value.
            apply of_to_val.
            done. simpl in *.
            iRight. iLeft. iSimpl.
            iSplit; first done.
            iSplit; first done.
            iCombine "HQ HQ2 HI" as "H".
            iExact "H".
        * (* Case 2: the continuation yielded *)
          iSimpl.
          replace (Ψ (SuspendE (Mk_tagidx addr_tag))) with (!immV []{{ I }};? immV [] {{ I }} )%iprot.
          2:{ subst Ψ. rewrite Nat.eqb_refl. done. }
          rewrite (upcl_tele' [tele] [tele]).
          simpl.
          iDestruct "HΨ" as "(%Heq & HI & Hrunb)".
          inversion Heq; subst.
          iSimpl.
          iApply ewp_value.
          apply of_to_val.
          done.
          iIntros (LI' HLI').
          move/lfilledP in HLI'; inversion HLI'; subst.
          inversion H8; subst.
          iSimpl.
          iApply ewp_br.
          3:{ instantiate (1 := 0).
              instantiate (1 := [AI_ref_cont kaddr]).
              instantiate (1 := LH_base [] _).
              rewrite /lfilled /lfill //=. } 
          done.
          done.
          iApply ewp_value.
          apply of_to_val.
          done.
          iRight. iRight.
          iExists kaddr, h.
          iSplit; first done.
          iSplit; first done.
          iCombine "Hb Hcont HI Hrunb" as "H".
          iExact "H".
        * iIntros (?) "[[[% _] | (% & % & % & % & _)] _]" => //.
        * iIntros (??) "H".
          iDestruct "H" as "[(%contb & -> & -> & Hcontb & Hrunb & HI & HQ1) | [(-> & -> & HQ1 & HQ2 & HI) | (%kaddr & %h & -> & -> & Hb & Hcont & HI & Hrunb)]]".
          -- (* Case 1a *)
            iApply ewp_value.
            apply of_to_val.
            done.
            iIntros (LI HLI).
            move/lfilledP in HLI; inversion HLI; subst.
            inversion H8; subst.
            iSimpl.
            iApply ewp_br.
            3:{
              instantiate (1 := 1).
              instantiate (1 := []).
              instantiate (1 := LH_rec [] _ _ (LH_base [] _) _).
              rewrite /lfilled /lfill //=. }
            done.
            done.
(*            iNext. *)
            iApply ("IH" $! kaddrb kaddrb 1).
            iRight.
            iFrame "Hrunb".
            iFrame.
            by iRight.
          -- (* Case 1b *)
            iApply ewp_value.
            apply of_to_val.
            done.
            iIntros (LI HLI).
            move/lfilledP in HLI; inversion HLI; subst.
            inversion H8; subst.
            iSimpl.
            iApply ewp_value.
            apply of_to_val.
            done.
            iIntros (LI' HLI').
            move/lfilledP in HLI'; inversion HLI'; subst.
            inversion H11; subst.
            iSimpl.
            iApply ewp_br.
            3:{
              instantiate (1 := 2).
              instantiate (1 := []).
              instantiate (1 := LH_rec [] _ _ (LH_rec [] _ _ (LH_base [] _) _) _).
              rewrite /lfilled /lfill //=. }
            done.
            done.
(*            iNext. *)
            iApply ewp_value.
            apply of_to_val.
            done.
            iFrame.
            done.
          -- (* Case 2 *)
            iSimpl.
            rewrite (separate2 (AI_ref_cont _)).
            iApply ewp_seq.
            done.
            iSplitR; last first.
            iSplitR.
            fold (AI_const (VAL_ref (VAL_ref_cont kaddr))).
            iApply ewp_set_local.
            simpl; lia.
            iSimpl.
            auto_instantiate.
            2: by iIntros (?) "[% _]".
            iIntros (??) "[-> ->]".
            iSimpl.
            rewrite (separate1 (AI_basic (BI_get_local _))).
            iApply ewp_seq.
            done.
            iSplitR; last first.
            iSplitR.
            iApply ewp_get_local.
            done.
            auto_instantiate.
            2: by iIntros (?) "[% _]".
            iIntros (??) "[-> ->]".
            iSimpl.
            iDestruct "Hb" as "[(-> & %contb & Hconta & Hruna) | (-> & HQ2)]". 
            ++ (* Case 2a: the other continuation is not done *)
              rewrite (separate2 (AI_basic (BI_const _))).
              iApply ewp_seq.
              done.
              iSplitR; last first.
              iSplitR.
              iApply ewp_br_if_false.
              by subst.
              auto_instantiate.
              2: by iIntros (?) "[% _]".
              iIntros (??) "[-> ->]".
              iSimpl.
              rewrite (separate1 (AI_basic (BI_get_local _))).
              iApply ewp_seq.
              done.
              iSplitR; last first.
              iSplitR.
              iApply ewp_get_local.
              done.
              auto_instantiate.
              2: by iIntros (?) "[% _]".
              iIntros (??) "[-> ->]".
              iSimpl.
              rewrite (separate3 (AI_ref_cont _)).
              iApply ewp_seq.
              done.
              iSplitR; last first.
              iSplitR.
              rewrite (separate1 (AI_ref_cont _)).
              iApply ewp_val_app.
              done.
              iSplitR; last first.
              rewrite (separate1 (AI_basic (BI_get_local 3))).
              iApply ewp_wand_r. iSplitR.
              iApply ewp_seq.
              done.
              iSplitR; last first.
              iSplitR.
              iApply ewp_get_local.
              done.
              auto_instantiate.
              2: by iIntros (?) "[% _]".
              iIntros (??) "[-> ->]".
              iSimpl.
              fold (AI_const (VAL_ref (VAL_ref_cont kaddrb))).
              iApply ewp_set_local.
              simpl; lia.
              iSimpl.
              auto_instantiate.
              iIntros (??) "[-> ->]".
              unfold val_combine. iSimpl.
              auto_instantiate.
              by iIntros "!>" (?) "[% _]".
              2: by iIntros (?) "[% _]".
              iIntros (??) "[->->]".
              iSimpl.
              rewrite (separate2 (AI_ref_cont _)).
              iApply ewp_seq.
              done.
              iSplitR; last first.
              iSplitR.
              fold (AI_const (VAL_ref (VAL_ref_cont kaddr))).
              iApply ewp_set_local.
              simpl; lia.
              iSimpl.
              auto_instantiate.
              2: by iIntros (?) "[% _]".
              iIntros (??) "[-> ->]".
              iSimpl.
              iApply ewp_value.
              apply of_to_val.
              done.
              iIntros (LI HLI).
              move/lfilledP in HLI; inversion HLI; subst.
              inversion H8; subst.
              iSimpl.
              iApply ewp_br.
              3:{ instantiate (1 := 0).
                  instantiate (1 := []).
                  instantiate (1 := LH_base [] _).
                  rewrite /lfilled /lfill //=. }
              done. done.
(*              iNext. *)
              iApply "IH".
              iRight.
              iFrame "Hconta Hruna HI".
              iLeft.
              iSplit; first done.
              iExists h.
              iFrame "Hcont".
              iNext.
(*              iExact "Hrunb". *)
              iIntros "HI".
              iDestruct ("Hrunb" with "HI") as "(%LI' & %HLI' & Hewp)".
              iExists LI'.
              iSplit; first by iPureIntro; destruct (hfilled No_var h [] LI').
              iExact "Hewp".
            ++ (* Case 2b: the other continuation is also done *)
              rewrite (separate2 (AI_basic (BI_const _))).
              iApply ewp_seq.
              done.
              iSplitR; last first.
              iSplitR.
              iApply ewp_br_if_true.
              by subst.
              iApply ewp_value.
              apply of_to_val.
              done.
              iNext.
              by instantiate (1 := λ v f, (⌜ v = brV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝)%I).
              2: by iIntros (?) "[% _]".
              iIntros (??) "[-> ->]".
              iSimpl.
              iApply ewp_value.
              apply of_to_val.
              done.
              iSimpl.
              iIntros (LI HLI).
              move/lfilledP in HLI; inversion HLI; subst.
              inversion H8; subst.
              iSimpl.
              iApply ewp_br.
              3:{ instantiate (1 := 0).
                  instantiate (1 := []).
                  instantiate (1 := LH_base [] _).
                  rewrite /lfilled /lfill //=. }
              done. done.
              iApply "IH".
              iLeft.
              iSplitL "HI"; first iExact "HI".
              instantiate (1 := h).
              iFrame "Hcont".
              iSplitL "Hrunb".
              iIntros "!> HI".
              iDestruct ("Hrunb" with "HI") as "(%LI' & %HLI' & Hewp)".
              iExists LI'.
              iSplit; first by iPureIntro; destruct (hfilled No_var h [] LI').
              iExact "Hewp".
              iRight.
              iFrame. done.
        * iIntros (?) "H".
          iDestruct "H" as "[H | H]".
          iDestruct "H" as (?) "[% _]" => //.
          iDestruct "H" as "[H | H]".
          iDestruct "H" as "[% _]" => //.
          iDestruct "H" as (???) "[% _]" => //.
      + (* Case where $current is the $f2 function *)

        iApply ewp_loop.
        done. done. done. done.
        iNext.
        iApply (ewp_label_bind with "[-]").
        2:{ iPureIntro. instantiate (5 := []).
            rewrite /lfilled /lfill /= app_nil_r //. }
        rewrite (separate1 (AI_basic (BI_block _ _))).
        iApply ewp_seq.
        done.
        iSplitR; last first.
        rewrite - (app_nil_l [AI_basic (BI_block _ _)]).
        iSplitL.
        iApply ewp_block.
        done. done. done. done.
        iNext.
        iApply (ewp_label_bind with "[-]").
        2:{ iPureIntro. instantiate (5 := []).
            rewrite /lfilled /lfill /= app_nil_r //. }
        rewrite (separate1 (AI_basic (BI_get_local _))).
        iApply ewp_seq.
        done.
        iSplitR; last first.
        iSplitR.
        iApply ewp_get_local.
        done.
        auto_instantiate.
        2: by iIntros (?) "[% _]".
        iIntros (??) "[-> ->]".
        iSimpl.
        rewrite (separate2 (AI_ref_cont _)).
        iApply ewp_seq.
        done.
        iSplitR; last first.
        iDestruct "H" as "(HI & Hconta & Hruna & Hb)".
        iDestruct ("Hruna" with "HI") as (LI) "[%HLI Hruna]".
        iSplitR "Hb".
        rewrite -(app_nil_l [AI_ref_cont _;_]).
        
        iApply (ewp_resume with "[$Hconta $Hruna]").
        done. done. done.
        simpl. instantiate (1 := [_]) => //.
        unfold agree_on_uncaptured => /=.
        repeat split => //.
        intros i.
        destruct (i == Mk_tagidx addr_tag) eqn:Hi => //.
        move/eqP in Hi.
        intros _.
        subst Ψ; simpl.
        destruct i => //.
        destruct (n =? addr_tag) eqn:Hn => //.
        apply Nat.eqb_eq in Hn as ->.
        exfalso; by apply Hi.
        by subst Ψ.
        by subst Ψ.
        by destruct (hfilled No_var conta [] LI).
        iSplitR.
        by iIntros (?) "[% ?]".
        iSplitR; last first.
        iFrame "Htag".
        iSplitR.
        iIntros "!>" (w) "(-> & HQ & HI)".
        iApply (ewp_prompt_value with "[-]").
        rewrite to_of_val => //.
        instantiate (1 := λ v, ((⌜ v = immV [] ⌝ ∗ I ∗ Q2) ∨ _)%I).
        iLeft. iFrame. done. 
        iSimpl.
        iSplitL; last done.
        iIntros "!>" (vs kaddr h) "Hcont HΨ".
        iApply ewp_value.
        unfold IntoVal.
        apply of_to_val.
        unfold to_val.
        rewrite map_app merge_app.
        specialize (@const_list_to_val (v_to_e_list vs)) as (vs' & Htv & Hinj).
        apply v_to_e_is_const_list.
        apply v_to_e_inj in Hinj as ->.
        unfold to_val in Htv.
        destruct (merge_values _); try by exfalso.
        inversion Htv; subst.
        simpl.
        done.

        iRight.
        instantiate (1 := (∃ kaddr vs h, ⌜ v = brV _ ⌝ ∗ _)%I). 
        iExists kaddr, vs, h. iSplit; first done.
        iCombine "Hcont HΨ" as "H".
        iExact "H".
        iIntros "[[% _] | (% & % & % & % & _)]" => //.
        
        iIntros (??) "[H ->]".
        iDestruct "H" as "[(-> & HI & HQ) | (%kaddr & %vs & %h & -> & Hcont & HΨ)]".
        * (* Case 1: the continuation terminated execution *)
          iSimpl.
          rewrite (separate1 (AI_basic (BI_get_local _))).
          iApply ewp_seq.
          done.
          iSplitR; last first.
          iSplitR.
          iApply ewp_get_local.
          done.
          auto_instantiate.
          2: by iIntros (?) "[% _]".
          iIntros (??) "[-> ->]".
          iSimpl.
          iDestruct "Hb" as "[(-> & %contb & Hcont & Hrunb) | (-> & HQ2)]". (* Changed %Hb to -> twice *)
          -- (* Case 1a: the other continuation is not done *)
            rewrite (separate2 (AI_basic (BI_const _))).
            iApply ewp_seq.
            done.
            iSplitR; last first.
            iSplitR.
            iApply ewp_br_if_false.
            by subst.
            auto_instantiate.
            2: by iIntros (?) "[% _]".
            iIntros (??) "[-> ->]".
            iSimpl.
            rewrite (separate2 (AI_basic (BI_const _))).
            iApply ewp_seq.
            done.
            iSplitR; last first.
            iSplitR.
            fold (AI_const (VAL_num (xx 1))).
            iApply ewp_set_local.
            simpl; lia.
            iSimpl.
            auto_instantiate.
            2: by iIntros (?) "[% _]".
            iIntros (??) "[-> ->]".
            iSimpl.
            rewrite (separate1 (AI_basic (BI_get_local _))).
            iApply ewp_seq.
            done.
            iSplitR; last first.
            iSplitR.
            iApply ewp_get_local.
            done.
            auto_instantiate.
            2: by iIntros (?) "[% _]".
            iIntros (??) "[-> ->]".
            iSimpl.
            rewrite (separate2 (AI_ref_cont _)).
            iApply ewp_seq.
            done.
            iSplitR; last first.
            iSplitR.
            fold (AI_const (VAL_ref (VAL_ref_cont kaddrb))).
            iApply ewp_set_local.
            simpl; lia.
            iSimpl.
            auto_instantiate.
            2: by iIntros (?) "[% _]".
            iIntros (??) "[-> ->]".
            iSimpl.
            iApply ewp_value.
            apply of_to_val. done.
            (*            iSplitL; last first.
            instantiate (1 := λ f, (⌜ b = 0 ⌝ ∗ ⌜ f = Build_frame _ _ ⌝ ∨ ⌜ b = 1 ⌝ ∗ ⌜ f = Build_frame _ _ ⌝ ∨ ⌜ f = Build_frame _ _ ⌝ )%I).  
            by iLeft. 
            iIntros (?) "[[_ ->] | [[% _] | %Hf]]"; try by subst b. *)
            iIntros (LI' HLI').
            move/lfilledP in HLI'; inversion HLI'; subst.
            inversion H8; subst.
            iSimpl.
            iApply ewp_value.
            apply of_to_val.
            done.
            iSimpl.
            instantiate (1 := λ v f, ((∃ contb, ⌜ v = brV (VH_rec [] 1 [] (VH_base 0 [] []) []) ⌝ ∗ ⌜ f = Build_frame _ _ ⌝ ∗ _) ∨ (⌜ v = brV (VH_rec [] 1 []
                                                                                                                                                 (VH_base 1 []
                                                                                                                                                    [AI_basic (BI_const (xx 1)); AI_basic (BI_set_local 4);
                                                                                                                                                     AI_basic (BI_get_local 3); AI_basic (BI_set_local 2); 
                                                                                                                                                     AI_basic (BI_br 1)]) []) ⌝ ∗ ⌜ f = Build_frame _ _ ⌝ ∗ _) ∨ (∃ kaddr h, ⌜ v = immV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝%I ∗ _))%I). 
            iLeft. iExists contb.
            iSimpl.
            iSplit; first done. 
            iSplit; first done.            
            iCombine "Hcont Hrunb HI HQ" as "H".
            iExact "H".
          -- (* Case 1b: the other continuation is also done *)
            rewrite (separate2 (AI_basic (BI_const _))).
            iApply ewp_seq.
            done.
            iSplitR; last first.
            iSplitR.
            iApply ewp_br_if_true.
            by subst.
            iApply ewp_value.
            apply of_to_val.
            done.
            iNext.
            by instantiate (1 := λ v f, (⌜ v = brV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝)%I).
            2: by iIntros (?) "[% _]".
            iIntros (??) "[-> ->]".
            iSimpl.
            iApply ewp_value.
            apply of_to_val.
            done.
            (*            iSplitL; last first.
            by iRight.
            iIntros (?) "[[% _] | [_ ->]]"; first by subst. *)
            iIntros (LI' HLI').
            move/lfilledP in HLI'; inversion HLI'; subst.
            inversion H8; subst.
            iSimpl.
            iApply ewp_value.
            apply of_to_val.
            done. simpl in *.
            iRight. iLeft. iSimpl.
            iSplit; first done.
            iSplit; first done.
            iCombine "HQ HQ2 HI" as "H".
            iExact "H".
        * (* Case 2: the continuation yielded *)
          iSimpl.
          replace (Ψ (SuspendE (Mk_tagidx addr_tag))) with (!immV []{{ I }};? immV [] {{ I }} )%iprot.
          2:{ subst Ψ. rewrite Nat.eqb_refl. done. }
          rewrite (upcl_tele' [tele] [tele]).
          simpl.
          iDestruct "HΨ" as "(%Heq & HI & Hrunb)".
          inversion Heq; subst.
          iSimpl.
          iApply ewp_value.
          apply of_to_val.
          done.
          iIntros (LI' HLI').
          move/lfilledP in HLI'; inversion HLI'; subst.
          inversion H8; subst.
          iSimpl.
          iApply ewp_br.
          3:{ instantiate (1 := 0).
              instantiate (1 := [AI_ref_cont kaddr]).
              instantiate (1 := LH_base [] _).
              rewrite /lfilled /lfill //=. } 
          done.
          done.
          iApply ewp_value.
          apply of_to_val.
          done.
          iRight. iRight.
          iExists kaddr, h.
          iSplit; first done.
          iSplit; first done.
          iCombine "Hb Hcont HI Hrunb" as "H".
          iExact "H".
        * iIntros (?) "[[[% _] | (% & % & % & % & _)] _]" => //.
        * iIntros (??) "H".
          iDestruct "H" as "[(%contb & -> & -> & Hcontb & Hrunb & HI & HQ1) | [(-> & -> & HQ1 & HQ2 & HI) | (%kaddr & %h & -> & -> & Hb & Hcont & HI & Hrunb)]]".
          -- (* Case 1a *)
            iApply ewp_value.
            apply of_to_val.
            done.
            iIntros (LI HLI).
            move/lfilledP in HLI; inversion HLI; subst.
            inversion H8; subst.
            iSimpl.
            iApply ewp_br.
            3:{
              instantiate (1 := 1).
              instantiate (1 := []).
              instantiate (1 := LH_rec [] _ _ (LH_base [] _) _).
              rewrite /lfilled /lfill //=. }
            done.
            done.
(*            iNext. *)
            iApply ("IH" $! kaddrb kaddrb 1).
            iLeft.
            iFrame "Hrunb".
            iFrame.
            by iRight.
          -- (* Case 1b *)
            iApply ewp_value.
            apply of_to_val.
            done.
            iIntros (LI HLI).
            move/lfilledP in HLI; inversion HLI; subst.
            inversion H8; subst.
            iSimpl.
            iApply ewp_value.
            apply of_to_val.
            done.
            iIntros (LI' HLI').
            move/lfilledP in HLI'; inversion HLI'; subst.
            inversion H11; subst.
            iSimpl.
            iApply ewp_br.
            3:{
              instantiate (1 := 2).
              instantiate (1 := []).
              instantiate (1 := LH_rec [] _ _ (LH_rec [] _ _ (LH_base [] _) _) _).
              rewrite /lfilled /lfill //=. }
            done.
            done.
(*            iNext. *)
            iApply ewp_value.
            apply of_to_val.
            done.
            iFrame.
            done.
          -- (* Case 2 *)
            iSimpl.
            rewrite (separate2 (AI_ref_cont _)).
            iApply ewp_seq.
            done.
            iSplitR; last first.
            iSplitR.
            fold (AI_const (VAL_ref (VAL_ref_cont kaddr))).
            iApply ewp_set_local.
            simpl; lia.
            iSimpl.
            auto_instantiate.
            2: by iIntros (?) "[% _]".
            iIntros (??) "[-> ->]".
            iSimpl.
            rewrite (separate1 (AI_basic (BI_get_local _))).
            iApply ewp_seq.
            done.
            iSplitR; last first.
            iSplitR.
            iApply ewp_get_local.
            done.
            auto_instantiate.
            2: by iIntros (?) "[% _]".
            iIntros (??) "[-> ->]".
            iSimpl.
            iDestruct "Hb" as "[(-> & %contb & Hconta & Hruna) | (-> & HQ2)]". 
            ++ (* Case 2a: the other continuation is not done *)
              rewrite (separate2 (AI_basic (BI_const _))).
              iApply ewp_seq.
              done.
              iSplitR; last first.
              iSplitR.
              iApply ewp_br_if_false.
              by subst.
              auto_instantiate.
              2: by iIntros (?) "[% _]".
              iIntros (??) "[-> ->]".
              iSimpl.
              rewrite (separate1 (AI_basic (BI_get_local _))).
              iApply ewp_seq.
              done.
              iSplitR; last first.
              iSplitR.
              iApply ewp_get_local.
              done.
              auto_instantiate.
              2: by iIntros (?) "[% _]".
              iIntros (??) "[-> ->]".
              iSimpl.
              rewrite (separate3 (AI_ref_cont _)).
              iApply ewp_seq.
              done.
              iSplitR; last first.
              iSplitR.
              rewrite (separate1 (AI_ref_cont _)).
              iApply ewp_val_app.
              done.
              iSplitR; last first.
              rewrite (separate1 (AI_basic (BI_get_local 3))).
              iApply ewp_wand_r. iSplitR.
              iApply ewp_seq.
              done.
              iSplitR; last first.
              iSplitR.
              iApply ewp_get_local.
              done.
              auto_instantiate.
              2: by iIntros (?) "[% _]".
              iIntros (??) "[-> ->]".
              iSimpl.
              fold (AI_const (VAL_ref (VAL_ref_cont kaddrb))).
              iApply ewp_set_local.
              simpl; lia.
              iSimpl.
              auto_instantiate.
              iIntros (??) "[-> ->]".
              unfold val_combine. iSimpl.
              auto_instantiate.
              by iIntros "!>" (?) "[% _]".
              2: by iIntros (?) "[% _]".
              iIntros (??) "[->->]".
              iSimpl.
              rewrite (separate2 (AI_ref_cont _)).
              iApply ewp_seq.
              done.
              iSplitR; last first.
              iSplitR.
              fold (AI_const (VAL_ref (VAL_ref_cont kaddr))).
              iApply ewp_set_local.
              simpl; lia.
              iSimpl.
              auto_instantiate.
              2: by iIntros (?) "[% _]".
              iIntros (??) "[-> ->]".
              iSimpl.
              iApply ewp_value.
              apply of_to_val.
              done.
              iIntros (LI HLI).
              move/lfilledP in HLI; inversion HLI; subst.
              inversion H8; subst.
              iSimpl.
              iApply ewp_br.
              3:{ instantiate (1 := 0).
                  instantiate (1 := []).
                  instantiate (1 := LH_base [] _).
                  rewrite /lfilled /lfill //=. }
              done. done.
              iApply "IH".
              iLeft.
              iFrame "Hconta Hruna HI".
              iLeft.
              iSplit; first done.
              iFrame "Hcont".
              iNext.
              iIntros "HI".
              iDestruct ("Hrunb" with "HI") as "(%LI' & %HLI' & Hewp)".
              iExists LI'.
              iSplit; first by iPureIntro; destruct (hfilled No_var h [] LI').
              iExact "Hewp".
            ++ (* Case 2b: the other continuation is also done *)
              rewrite (separate2 (AI_basic (BI_const _))).
              iApply ewp_seq.
              done.
              iSplitR; last first.
              iSplitR.
              iApply ewp_br_if_true.
              by subst.
              iApply ewp_value.
              apply of_to_val.
              done.
              iNext.
              by instantiate (1 := λ v f, (⌜ v = brV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝)%I).
              2: by iIntros (?) "[% _]".
              iIntros (??) "[-> ->]".
              iSimpl.
              iApply ewp_value.
              apply of_to_val.
              done.
              iSimpl.
              iIntros (LI HLI).
              move/lfilledP in HLI; inversion HLI; subst.
              inversion H8; subst.
              iSimpl.
              iApply ewp_br.
              3:{ instantiate (1 := 0).
                  instantiate (1 := []).
                  instantiate (1 := LH_base [] _).
                  rewrite /lfilled /lfill //=. }
              done. done.
              iApply "IH".
              iRight.
              iSplitL "HI"; first iExact "HI".
              iFrame "Hcont".
              iSplitL "Hrunb".
              iIntros "!> HI".
              iDestruct ("Hrunb" with "HI") as "(%LI' & %HLI' & Hewp)".
              iExists LI'.
              iSplit; first by iPureIntro; destruct (hfilled No_var h [] LI').
              iExact "Hewp".
              iRight.
              iFrame. done.
        * iIntros (?) "H".
          iDestruct "H" as "[H | H]".
          iDestruct "H" as (?) "[% _]" => //.
          iDestruct "H" as "[H | H]".
          iDestruct "H" as "[% _]" => //.
          iDestruct "H" as (???) "[% _]" => //.
  Qed. 
              
              
              
              
          
            
            
End yield_par.
        
        
        
        
        
        
        

      
      
      
