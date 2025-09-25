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

(* Example Programs *)
Section Example2.
  Context `{!wasmG Σ}.

  Definition aux_type := Tf [] [T_num T_i32].
  Definition cont_type := T_contref aux_type.
  Definition main_type := Tf [] [T_num T_i32].

  Definition t_tag : tag_identifier := Mk_tagident 0.

  Definition aux_body :=
    [ BI_const (xx 42); BI_return ].

  Definition main_body :=
    [
      BI_block (* $b *) (Tf [] [T_num T_i32]) [
        BI_block (* $on-t *) (Tf [] [T_ref cont_type]) [
          (* create ref to aux function *)
          BI_ref_func 0;
          (* create continuation from aux ref with type aux_type *)
          BI_contnew (Type_lookup 0);
          (* resume continuation *)
          BI_resume (Type_lookup 0) [HC_catch t_tag 0 (* break out of $on-t *)];
          (* Continuation finished. 42 is now on stack. *)
          BI_const (xx 7); (* put 7 on stack*)
          BI_binop T_i32 (Binop_i BOI_add); (* 49 (42 + 7) is now on stack *)
          BI_br 1 (* break out of $b *)
        ];
        (* Continuation suspended. *)
        BI_drop; (* drop the continuation *)
        BI_const (xx 0) (* put 0 on stack *)
      ];
      (* Finally, increment whatever is on the stack by 1 *)
      BI_const (xx 1);
      BI_binop T_i32 (Binop_i BOI_add)
    ].

  Definition typing_context : t_context :=
  {|
    tc_types_t := [aux_type; main_type];
    tc_func_t := [aux_type; main_type];
    tc_global := [];
    tc_table := [];
    tc_memory := [];
    tc_local := [];
    tc_label := [];
    tc_return := Some [];
    tc_refs := [];
    tc_tags_t := [Tf [] []]
  |}.

  Lemma aux_body_type : be_typing typing_context aux_body aux_type.
  Proof.
    apply /b_e_type_checker_reflects_typing; done.
  Qed.

  Lemma main_body_type : be_typing typing_context main_body main_type.
  Proof.
    rewrite /main_body separate1.
    apply bet_composition' with (t2s := [T_num T_i32]).
    2: {
      apply /b_e_type_checker_reflects_typing; done.
    }
    constructor.
    rewrite (separate1 (BI_block _ _)).
    apply bet_composition' with (t2s := [T_ref cont_type]).
    2: {
      apply /b_e_type_checker_reflects_typing; done.
    }
    constructor.
    simpl.
    rewrite (separate1 (BI_ref_func 0)).
    apply bet_composition' with (t2s := [T_ref $ T_funcref aux_type]); first by constructor.
    rewrite (separate1 (BI_contnew _)).
    apply bet_composition' with (t2s := [T_ref cont_type]); first by constructor.
    rewrite (separate1 (BI_resume _ _)).
    apply bet_composition' with (t2s := [T_num T_i32]).
    2: {
      apply /b_e_type_checker_reflects_typing; done.
    }
    unfold typing_context, upd_label, cont_type; simpl.
    rewrite <- (app_nil_l [T_ref _]).
    constructor; first done.
    simpl.
    constructor; last done.
    by eapply cct_clause.
  Qed.

  Definition inst addraux addrmain :=
    {|
      inst_types  := [aux_type; main_type];
      inst_funcs  := [addraux; addrmain];
      inst_tab    := [];
      inst_memory := [];
      inst_globs  := [];
      inst_tags   := [0];
    |}.

  Lemma aux_spec : ∀(addraux addrmain: nat) f,
    (N.of_nat addraux) ↦[wf] FC_func_native (inst addraux addrmain) aux_type [] aux_body -∗
    EWP [AI_invoke addraux] UNDER f {{ v; f', ⌜v = (immV [VAL_num $ xx 42]) ∧ f = f'⌝ }}.
  Proof.
    iIntros (???) "Hwf_addraux".

    (* Reason about invocation of aux function *)
    rewrite <- (app_nil_l [AI_invoke _]).
    iApply (ewp_invoke_native with "Hwf_addraux"); try done.

    (* Reason about aux_body in a frame *)
    iIntros "!> Hwf_addraux"; simpl.
    iApply ewp_frame_bind => //.
    repeat iSplitR.

    (* The body of the frame will symbolically evaluate to a retV value, representing a context of depth 1, with the ret instruction being preceeded by the value 42. *)
    instantiate (1 := λ v f', ⌜v = retV (SH_rec [] 1 [] (SH_base [VAL_num (xx 42)] []) [])⌝%I).
    all: simpl.
    (* We first prove that that is indeed the case *)
    2: {
      rewrite <- (app_nil_l _).
      iApply ewp_block; try done.
      iModIntro; simpl.
      
      (* aux_body is simply a retV value. *)
      iApply ewp_value; done.
    }

    (* The retV value is not a TrapV value. *)
    { by iIntros (? Hcontra). }

    (* Now, we must reason about the retV value inside the frame. *) 
    iIntros (?? ->).
    simpl.
    (* The return is no longer a value, as it now sits under a frame.
       So we reason about returning from the frame. *)
    iApply ewp_return.
    3: {
      (* First, we specify what is returned. *)
      instantiate (1 := [AI_basic (BI_const (xx 42))]).
      (* Then we specify the context in which the instructions are plugged. *)
      instantiate (1 := LH_rec [] 1 [] (LH_base [] []) []).
      (* Finally, the depth of the context. *)
      instantiate (1 := 1).
      unfold lfilled, lfill => //=.
    }
    (* Now the rest is trivial. *)
    1,2: done.
    by iApply ewp_value.
  Qed.

  Lemma main_spec : ∀(addrmain addraux: nat) f,
  (N.of_nat addraux) ↦[wf] FC_func_native (inst addraux addrmain) aux_type [] aux_body -∗
  (N.of_nat addrmain) ↦[wf] FC_func_native (inst addraux addrmain) main_type [] main_body -∗
  0%N ↦□[tag] Tf [] [] -∗
  EWP [AI_invoke addrmain] UNDER f {{ v; f', ⌜v = (immV [VAL_num $ xx 50]) ∧ f = f'⌝}}.
  Proof.
    iIntros (addrmain addraux f) "Hwf_aux Hwf_main #Htag".

    (* Reason about invocation of main function *)
    rewrite <- (app_nil_l [AI_invoke _]).
    iApply (ewp_invoke_native with "Hwf_main"); try done.
    iIntros "!> Hwf_main"; simpl.

    (* Reason about frame *)
    iApply ewp_frame_bind; try done.
    iSplitR; last iSplitL "Hwf_aux".

    (* The result of main_body will be the value 50 with an unchanged frame. *)
    instantiate (1 := λ v f, ⌜v = immV [VAL_num (xx 50)] ∧ f = {| f_locs := []; f_inst := inst addraux addrmain |}⌝%I); simpl.

    (* We first prove that this is the case. *)
    2: {
      rewrite <- (app_nil_l [AI_basic _]).
      iApply ewp_block; try done.
      simpl.
      
      iApply (ewp_label_bind with "[-]").
      2: {
        iPureIntro.
        unfold lfilled. simpl.
        instantiate (5 := []).
        simpl.
        rewrite app_nil_r.
        done.
      }
      unfold ewp_wasm_ctx.
      (* Reason about main_body *)
      rewrite (separate1 (AI_basic (BI_block _ _))).
      iApply ewp_seq; first done.
      iSplitR; last iSplitL.

      (* Outer block *)
      instantiate (1 := λ v f, ⌜v = immV [VAL_num (xx 49)] ∧ f = {| f_locs := []; f_inst := inst addraux addrmain |}⌝%I); simpl.
      { by iIntros (? [Hcontra _]). }
      {
        rewrite <- (app_nil_l [AI_basic _]).
        iApply ewp_block; try done.
        simpl.
        iApply (ewp_label_bind with "[-]").
        2: {
          iPureIntro.
          unfold lfilled. simpl.
          instantiate (5 := []).
          simpl.
          rewrite app_nil_r.
          done.
        }
        rewrite (separate1 (AI_basic (BI_block _ _))).
        iApply ewp_seq; first done.
        iSplitR; last iSplitL.

        (* Inner block *)
        2: {
          rewrite <- (app_nil_l [AI_basic _]).
          iApply ewp_block; try done.
          simpl.
          iApply (ewp_label_bind with "[-]").
          2: {
            iPureIntro.
            unfold lfilled. simpl.
            instantiate (5 := []).
            simpl.
            rewrite app_nil_r.
            done.
          }
          rewrite (separate1 (AI_basic (BI_ref_func _))).
          iApply ewp_seq; first done.
          repeat iSplitR.
          2: {
            iApply ewp_ref_func.
            done.
            instantiate (1 :=  λ v f', ⌜v = immV [VAL_ref (VAL_ref_func addraux)] ∧ f' = {| f_locs := []; f_inst := (inst addraux addrmain) |}⌝%I).
            done.
          }
          { by iIntros (f0 [Hcontra _]). }
          iIntros (w f' [-> ->]).
          simpl.
          rewrite separate2.
          iApply ewp_seq; first done.
          repeat iSplitR.
          2: {
            iApply ewp_contnew.
            done.
          }
          { simpl. by iIntros (f0) "(%kaddr & % & _)". }
          simpl.
          iIntros (w f') "(%kaddr & -> & -> & Hkaddr)".
          simpl.
          (* reason about resumption *)
          rewrite separate2.
          iApply ewp_seq; first done.
          iSplitR; last iSplitL "Hkaddr Hwf_aux".
          2: {
            rewrite <- (app_nil_l [AI_ref_cont _; _]).
            iApply ewp_resume; try done.
            simpl.
            instantiate (1 := [_]). done.
            instantiate (1 := λ x, iProt_bottom). done.
            2: iFrame "Hkaddr".
            unfold hfilled, hfill => //=.
            iSplitR; last iSplitR; last iSplitL; last iSplitR.
            3: {
              iModIntro.
              iApply (ewp_call_reference with "[Hwf_aux]"); try done.
              simpl. done.
              iApply aux_spec.
            }
            { iIntros (? [Hcontr _]). done. }
            2: {
              simpl.
              iIntros (w) "!> [-> _]". simpl.
              iApply (ewp_prompt_value with "[-]").
              done.
              simpl.
              instantiate (1 := λ v,⌜v = immV [VAL_num (xx 42)]⌝%I).
              done.
            }
            done.
            simpl.
            iModIntro.
            iSplitR; last done.
            iExists [], [].
            iFrame "#".
            iIntros (vs kaddr' h) "Hkaddr HΦ".
            iDestruct "HΦ" as "(%Φ & H & _)".
            done.
          }
          {
            simpl.
            iIntros (?) "[%Hcontra _]".
            done.
          }
          simpl.
          iIntros (w f') "[-> ->]". 
          simpl.
          rewrite separate3.
          iApply ewp_seq; first done.
          instantiate (2 := λ v f, ⌜v = immV [VAL_num (xx 49)] ∧ f = {| f_locs := []; f_inst := inst addraux addrmain |}⌝%I).
          iSplitR.
          { by iIntros (? [Hcontra _]). }
          iSplitR; first by iApply ewp_binop.
          iIntros (w f' [-> ->]).
          simpl.
          iApply ewp_value; first done.
          simpl.
          unfold ewp_wasm_ctx.
          iIntros (LI Hfilled).
          move/lfilledP in Hfilled; inversion Hfilled; subst; simpl.
          inversion H8; subst; simpl.
          iApply ewp_value; first done.
          instantiate (1 := λ v f, ⌜v = brV _ ∧ f = {| f_locs := []; f_inst := inst addraux addrmain |}⌝%I). done.
        }
        { by iIntros (? [Hcontra _]). }
        simpl.
        iIntros (w f' [-> ->]).
        simpl.
        iApply ewp_value; first done.
        simpl.
        iIntros (LI HLI).
        move /lfilledP in HLI. inversion HLI; subst.
        inversion H8; subst.
        simpl.
        iApply ewp_br.
        3: { 
          instantiate (2 := [_] ).
          instantiate (3 := LH_rec [] 1 [] (LH_base [] []) _).
          instantiate (1 := 1).
          unfold lfilled, lfill. simpl. done.
        }
        1,2: done.
        by iApply ewp_value.
      }
      iIntros (w f' [-> ->]).
      simpl.
      iApply ewp_binop.
      instantiate (1 := (xx 50)). done.
      simpl.
      iIntros (LI HLI).
      move /lfilledP in HLI.
      inversion HLI; subst.
      inversion H8; subst.
      simpl.
      iApply ewp_label_value; first done.
      simpl.
      done.
    }
    (* We have now shown that the main body reduces to 50... which isn't a trap value *)
    { by iIntros (? [Hcontra _]). }
    simpl.
    iIntros (w f' [-> ->]). simpl.
    by iApply ewp_frame_value.
    Qed.

End Example2.
