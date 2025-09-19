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

  Definition aux_type := Tf [] [].
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
    tc_types_t := [];
    tc_func_t := [];
    tc_global := [];
    tc_table := [];
    tc_memory := [];
    tc_local := [];
    tc_label := [];
    tc_return := Some [];
    tc_refs := [];
    tc_tags_t := []
  |}.

  Lemma aux_body_type : be_typing typing_context aux_body aux_type.
  Proof.
    apply/b_e_type_checker_reflects_typing.
    done.
  Qed.

  Lemma main_body_type : be_typing typing_context main_body main_type.
  Proof.
    apply/b_e_type_checker_reflects_typing.
    (* todo: fix typing_context *)
    admit.

  Definition inst :=
    {|
      inst_types  := [];
      inst_funcs  := [];
      inst_tab    := [];
      inst_memory := [];
      inst_globs  := [];
      inst_tags   := [];
    |}.

  Lemma aux_body_spec : ∀(addraux: nat) f,
    (N.of_nat addraux) ↦[wf] FC_func_native inst aux_type [] aux_body -∗
    EWP [AI_invoke addraux] UNDER f {{ v; f', ⌜v = (immV [VAL_num $ xx 42]) ∧ f = f'⌝ }}.
  

  Lemma main_body_spec : ∀(addrmain addraux: nat) f,
  (N.of_nat addraux) ↦[wf] FC_func_native inst aux_type [] aux_body -∗
  (N.of_nat addrmain) ↦[wf] FC_func_native inst main_type [] main_body -∗
  EWP [AI_invoke addrmain] UNDER f {{ v; f', ⌜v = (immV [VAL_num $ xx 50]) ∧ f = f'⌝}}.

End Example2.
