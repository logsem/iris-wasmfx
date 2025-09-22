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
    (* apply /b_e_type_checker_reflects_typing; done. *) (* todo: Why doesn't that work??? well-typing can be proved manually... *)
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

  Definition inst :=
    {|
      inst_types  := [];
      inst_funcs  := [];
      inst_tab    := [];
      inst_memory := [];
      inst_globs  := [];
      inst_tags   := [];
    |}.

  Lemma aux_spec : ∀(addraux: nat) f,
    (N.of_nat addraux) ↦[wf] FC_func_native inst aux_type [] aux_body -∗
    EWP [AI_invoke addraux] UNDER f {{ v; f', ⌜v = (immV [VAL_num $ xx 42]) ∧ f = f'⌝ }}.
  Proof.
    iIntros (addraux f) "Hwf_addraux".

    (* Reason about invocation of aux function *)
    rewrite <- (app_nil_l [AI_invoke _]).
    iApply (ewp_invoke_native with "Hwf_addraux"); try done.

    (* Reason about aux_body in a frame *)
    iIntros "!> Hwf_addraux"; simpl.
    iApply ewp_frame_bind => //.
    repeat iSplitR.

    (* The body of the frame will symbolically evaluate to a retV value. *)
    instantiate (1 := λ v f', ⌜v = retV (SH_rec [] 1 [] (SH_base [VAL_num (xx 42)] []) [])⌝%I).
    2: {
      rewrite <- (app_nil_l _).
      iApply ewp_block; try done.
      iModIntro; simpl.
      
      (* Reason about aux_body. *)
      iApply ewp_value.
      done.
      iPureIntro.
      simpl.
      done.
    }

    (* The retV value is not a TrapV value. *)
    {
     iIntros (? Hcontra); inversion Hcontra. 
    }

    (* ... and putting the retV value in the frame gives us the immediate result 42. *)
    {
      iIntros (w f1 ->).
      simpl.
      iApply ewp_return.
      3: {
        instantiate (1 := [AI_basic (BI_const (xx 42))]).
        instantiate (1 := LH_rec [] 1 [] (LH_base [] []) []).
        instantiate (1 := 1).
        unfold lfilled, lfill.
        simpl.
        done.
      }
      all: try done.
      iModIntro.
      by iApply ewp_value.
    }
  Qed.

  Lemma main_spec : ∀(addrmain addraux: nat) f,
  (N.of_nat addraux) ↦[wf] FC_func_native inst aux_type [] aux_body -∗
  (N.of_nat addrmain) ↦[wf] FC_func_native inst main_type [] main_body -∗
  EWP [AI_invoke addrmain] UNDER f {{ v; f', ⌜v = (immV [VAL_num $ xx 50]) ∧ f = f'⌝}}.

End Example2.
