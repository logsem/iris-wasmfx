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

  Definition inst addraux addrmain tag :=
    {|
      inst_types  := [aux_type; main_type];
      inst_funcs  := [addraux; addrmain];
      inst_tab    := [];
      inst_memory := [];
      inst_globs  := [];
      inst_tags   := [tag];
    |}.

  Lemma aux_spec : ∀(addraux addrmain tag: nat) f,
    (N.of_nat addraux) ↦[wf] FC_func_native (inst addraux addrmain tag) aux_type [] aux_body -∗
    EWP [AI_invoke addraux] UNDER f {{ v; f', ⌜v = (immV [VAL_num $ xx 42]) ∧ f = f'⌝ }}.
  Proof.
    iIntros (????) "Hwf_addraux".

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

  Lemma main_spec : ∀(addrmain addraux tag: nat) f,
  (N.of_nat addraux) ↦[wf] FC_func_native (inst addraux addrmain tag) aux_type [] aux_body -∗
  (N.of_nat addrmain) ↦[wf] FC_func_native (inst addraux addrmain tag) main_type [] main_body -∗
  (N.of_nat tag) ↦□[tag] Tf [] [] -∗
  EWP [AI_invoke addrmain] UNDER f {{ v; f', ⌜v = (immV [VAL_num $ xx 50]) ∧ f = f'⌝}}.
  Proof.
    iIntros (addrmain addraux tag f) "Hwf_aux Hwf_main #Htag".

    (* Reason about invocation of main function *)
    rewrite <- (app_nil_l [AI_invoke _]).
    iApply (ewp_invoke_native with "Hwf_main"); try done.
    iIntros "!> Hwf_main"; simpl.

    (* Reason about frame *)
    iApply ewp_frame_bind; try done.
    iSplitR; last iSplitL "Hwf_aux".

    (* The result of main_body will be the value 50 with an unchanged frame. *)
    instantiate (1 := λ v f, ⌜v = immV [VAL_num (xx 50)] ∧ f = {| f_locs := []; f_inst := inst addraux addrmain tag |}⌝%I); simpl.

    (* We first prove that this is the case. *)
    2: {
      (* We first reduce the block containing main_body to a label. *)
      rewrite <- (app_nil_l [AI_basic _]).
      iApply ewp_block; try done.
      simpl.

      (* We now bind into the label to reason about main_body. *)
      iApply (ewp_label_bind with "[-]").
      2: {
        iPureIntro.
        instantiate (5 := []).
        unfold lfilled; simpl.
        by rewrite app_nil_r.
      }
      
      (* We now reason about main_body *)
      (* The main body consist of a sequence of instructions: an outer block followed by the constant 1 and the add operation. *)
      (* We split this up to reason about the outer block in isolation. *)
      rewrite (separate1 (AI_basic (BI_block _ _))).
      iApply ewp_seq; first done.
      iSplitR; last iSplitL.

      (* Outer block *)
      (* Running the outer block will leave us with the constant 49 on the stack, and an unchanged frame. *)
      instantiate (1 := λ v f, ⌜v = immV [VAL_num (xx 49)] ∧ f = {| f_locs := []; f_inst := inst addraux addrmain tag |}⌝%I); simpl.
      (* We first prove that this is the case. *)
      2: {
        (* The outer block reduces to a label which we bind into. *)
        rewrite <- (app_nil_l [AI_basic _]).
        iApply ewp_block; try done.
        simpl.
        iApply (ewp_label_bind with "[-]").
        2: {
          iPureIntro.
          instantiate (5 := []).
          unfold lfilled; simpl.
          by rewrite app_nil_r.
        }
        
        (* The outer block consists of an inner block followed by instructions drop and const 0. *)
        (* We consider first the inner block. *)
        rewrite (separate1 (AI_basic (BI_block _ _))).
        iApply ewp_seq; first done.
        iSplitR; last iSplitL.

        (* Inner block *)
        (* The inner block will reduce to a stuck branch, i.e. a brV. *)
        instantiate (1 := λ v f, ⌜v = brV _ ∧ f = {| f_locs := []; f_inst := inst addraux addrmain tag |}⌝%I).
        (* We first prove this. *)
        2: {
          (* We reduce the block and bind into the label *)
          rewrite <- (app_nil_l [AI_basic _]).
          iApply ewp_block; try done.
          simpl.
          iApply (ewp_label_bind with "[-]").
          2: {
            iPureIntro.
            unfold lfilled. simpl.
            instantiate (5 := []); simpl.
            by rewrite app_nil_r.
          }
          (* In the inner block, we first create the function reference to aux. *)
          rewrite (separate1 (AI_basic (BI_ref_func _))).
          iApply ewp_seq; first done.
          repeat iSplitR.
          2: {
            iApply ewp_ref_func; first done.
            instantiate (1 :=  λ v f', ⌜v = immV _ ∧ f' = {| f_locs := []; f_inst := inst addraux addrmain tag |}⌝%I).
            done.
          }
          { by iIntros (? [Hcontra _]). }
          iIntros (?? [-> ->]).
          simpl.
          (* Now we have a reference to aux on the stack. We can now create a continuation for it. *)
          rewrite separate2.
          iApply ewp_seq; first done.
          repeat iSplitR.
          2: { by iApply ewp_contnew. }
          { by iIntros (?) "(%kaddr & %Hcontra & _)". }
          simpl.
          iIntros (??) "(%kaddr & -> & -> & Hkaddr)".
          simpl.
          (* With the continuation on the stack, we reason about the resumption of it. *)
          rewrite separate2.
          iApply ewp_seq; first done.
          iSplitR; last iSplitL "Hkaddr Hwf_aux".
          2: {
            rewrite <- (app_nil_l [AI_ref_cont _; _]).
            iApply ewp_resume; try done.
            by instantiate (1 := [_]).
            (* We use the bottom protocol as aux never suspends. *)
            by instantiate (1 := λ x, iProt_bottom).
            2: iFrame "Hkaddr".
            unfold hfilled, hfill => //=.
            iSplitR; last iSplitR; last iSplitL; last iSplitR.
            (* Resumption of the continuation consists of invoking aux. *)
            (* We use our spec for aux, to reason about it. *)
            3: {
              iModIntro.
              iApply (ewp_call_reference with "[Hwf_aux]"); try done.
              simpl. done.
              iApply aux_spec.
            }
            (* aux doesn't trap. *)
            { by iIntros (? [Hcontr _]). }
            (* If aux doesn't suspend, it returns 42. *)
            2: {
              simpl.
              iIntros (w) "!> [-> _]". simpl.
              iApply (ewp_prompt_value with "[-]").
              done.
              simpl.
              by instantiate (1 := λ v,⌜v = immV [VAL_num (xx 42)]⌝%I).
            }
            (* The returned 42 isn't a trap *)
            { done. }
            (* Finally, we consider what happens if aux triggers an effect. *)
            (* Since our protocol is bottom, we can derive falsehood. *)
            {
              simpl.
              iModIntro.
              iSplitR; last done.
              iExists [], [].
              iFrame "#".
              iIntros (vs kaddr' h) "Hkaddr HΦ".
              iDestruct "HΦ" as "(%Φ & Hcontra & _)".
              done.
            }
          }
          (* We have now concluded that the continuation ends with a 42 on the stack. *)
          (* ... which isn't a trap. *)
          { by iIntros (?) "[%Hcontra _]". }
          (* We continue with the rest of the inner block. *)
          simpl.
          iIntros (?? [-> ->]). 
          simpl.
          (* We perform the add operation *)
          rewrite separate3.
          iApply ewp_seq; first done.
          instantiate (3 := λ v f, ⌜v = immV [VAL_num (xx 49)] ∧ f = {| f_locs := []; f_inst := inst addraux addrmain tag |}⌝%I).
          iSplitR.
          { by iIntros (? [Hcontra _]). }
          iSplitR; first by iApply ewp_binop.
          iIntros (?? [-> ->]).
          simpl.
          (* Finaly, we are left with a stuck branch instruction. *)
          iApply ewp_value; first done.
          simpl.
          (* We put the branch value back into the inner label. *)
          unfold ewp_wasm_ctx.
          iIntros (LI HLI).
          move /lfilledP in HLI; 
          inversion HLI; subst; simpl.
          inversion H8; subst; simpl.
          (* However, the branch is still a value as it targets the next label out, i.e. the outer label. *)
          iApply ewp_value; first done.
          done.
        }
        (* We have now concluded that the inner block leaves a branch value on the stack *)
        (* ... which is not a trap *)
        { by iIntros (? [Hcontra _]). }
        (* We continue reasoning about the rest of the outer block. *)
        simpl.
        iIntros (?? [-> ->]).
        simpl.
        (* The sequence of instructions is actually a value, as the branch is only under one label. *)
        iApply ewp_value; first done.
        simpl.
        (* We put the instructions back into the outer label. *)
        iIntros (LI HLI).
        move /lfilledP in HLI. 
        inversion HLI; subst.
        inversion H8; subst.
        simpl.
        (* Now the branch instruction is in a deep enough context for us to perform the branch. *)
        iApply ewp_br.
        3: { 
          instantiate (2 := [_] ).
          instantiate (3 := LH_rec [] 1 [] (LH_base [] []) _).
          instantiate (1 := 1).
          unfold lfilled, lfill => //=.
        }
        1,2: done.
        by iApply ewp_value.
      }
      (* We have now shown that the outer block results in a 49 on the stack *)
      (* ... which isn't a trap. *)
      { by iIntros (? [Hcontra _]). }
      (* We are now left with 49 on the stack followed by the const 1 and add operations, which we can show results in 50. *)
      iIntros (w f' [-> ->]).
      simpl.
      iApply ewp_binop.
      by instantiate (1 := (xx 50)).
      (* We are finally back to the label we bound into in the start of the proof. *)
      simpl.
      iIntros (LI HLI).
      move /lfilledP in HLI.
      inversion HLI; subst.
      inversion H8; subst.
      simpl.
      (* The label simply contains the value 50, which it leaves on the stack. *) 
      by iApply ewp_label_value.
    }
    (* We have now shown that the block containing the main body results in the value 50 on the stack *)
    (* ... which is not a trap. *)
    { by iIntros (? [Hcontra _]). }
    (* Finally, the function simply returns the value left on the stack: 50. *)
    simpl.
    iIntros (w f' [-> ->]).
    by iApply ewp_frame_value.
    Qed.

End Example2.
