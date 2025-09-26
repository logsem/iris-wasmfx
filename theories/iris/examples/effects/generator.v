
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

Definition gen_tag := Mk_tagident 0.

Definition naturals :=
  [
    BI_loop (Tf [] []) [
      BI_get_local 0;
      BI_suspend gen_tag; (* suspend with generated number *)
      BI_get_local 0; (* generate next number *)
      BI_const (xx 1);
      BI_binop T_i32 (Binop_i BOI_add);
      BI_set_local 0;
      BI_br 0 (* loop *)
    ]
  ]
  .

Definition t_ctxt := 
  {| 
    tc_types_t := [];
    tc_func_t := [Tf [] []];
    tc_global := [];
    tc_table := [];
    tc_memory := [];
    tc_local := [];
    tc_label := [[]];
    tc_return := None;
    tc_refs := [];
    tc_tags_t := [Tf [T_num T_i32] []]
  |}.

Lemma naturals_typing : be_typing t_ctxt naturals (Tf [] []).
Proof.
  constructor.
  simpl.
  rewrite (separate1 (BI_get_local _)).
  apply bet_composition' with (t2s := [T_num T_i32]).
  {
    apply /b_e_type_checker_reflects_typing.
    si

  apply /b_e_type_checker_reflects_typing.
  done.
Qed.



