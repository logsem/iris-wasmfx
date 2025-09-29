
From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.program_logic Require Import adequacy.
From iris.bi Require Export weakestpre.
From iris.algebra Require Import list excl agree csum.
From Wasm Require Import type_checker_reflects_typing.
From Wasm.iris.rules Require Export iris_rules iris_example_helper.
From Wasm.iris.host Require Export iris_host.
From Wasm.iris.examples.effects Require Import coroutines_module coroutines_implementation_code.


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition naturals_type := Tf [] [].
Definition cont_type := T_contref naturals_type.
Definition sum_until_type := Tf [] [T_num T_i32].

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

Definition t_ctxt_naturals :=
  {| 
    tc_types_t := [];
    tc_func_t := [];
    tc_global := [];
    tc_table := [];
    tc_memory := [];
    tc_local := [T_num T_i32];
    tc_label := [[]];
    tc_return := None;
    tc_refs := [];
    tc_tags_t := [Tf [T_num T_i32] []]
  |}.

Lemma naturals_typing : be_typing t_ctxt_naturals naturals naturals_type.
Proof.
  apply /b_e_type_checker_reflects_typing.
  done.
Qed.


Definition sum_until := [
    (* param $upto = 0 *)
    (* local $v = 1 *)
    (* local $sum = 2 *)
    (* local $k = 3 *)
    BI_ref_func 0;
    BI_contnew (Type_lookup 0);
    BI_set_local 3; (* $k *)
    BI_loop (* $l *) (Tf [] []) [
      BI_block (* $on_gen *) (Tf [] [T_num T_i32; T_ref (cont_type)]) [
        BI_get_local 3; (* $k *)
        BI_resume (Type_lookup 0) [ HC_catch gen_tag 0 (* $on_gen *) ];
        BI_unreachable
      ];
      BI_set_local 3; (* $k *)
      BI_set_local 1; (* $v *)

      BI_get_local 2; (* $sum *)
      BI_get_local 1; (* $v *)
      BI_binop T_i32 (Binop_i BOI_add);
      BI_set_local 2; (* $sum *)

      BI_get_local 1; (* $v *)
      BI_get_local 0; (* $upto *)
      BI_relop T_i32 (Relop_i (ROI_lt SX_U));
      BI_br_if 0 (* $l *)
    ];
    BI_get_local 2 (* $sum *)
  ].

Definition t_ctxt_sum_until :=
  {| 
    tc_types_t := [naturals_type];
    tc_func_t := [naturals_type];
    tc_global := [];
    tc_table := [];
    tc_memory := [];
    tc_local := [T_num T_i32; T_num T_i32; T_num T_i32; T_ref cont_type];
    tc_label := [[]];
    tc_return := None;
    tc_refs := [];
    tc_tags_t := [Tf [T_num T_i32] []]
  |}.

Lemma sum_until_typing : be_typing t_ctxt_sum_until sum_until sum_until_type.
Proof.
  rewrite /sum_until separate3.
  eapply bet_composition'.
  {
    apply /b_e_type_checker_reflects_typing.
    simpl.
    done.
  }
  rewrite separate1.
  eapply bet_composition'.
  {
    constructor; simpl.
    rewrite (separate1 (BI_block _ _)).
    eapply bet_composition'.
    {
      apply /b_e_type_checker_reflects_typing.
      simpl.
      done.
    }
    rewrite (separate2 (BI_set_local _)).
    eapply bet_composition'.
    {
      apply /b_e_type_checker_reflects_typing.
      simpl.
      done.
    }
    by apply /b_e_type_checker_reflects_typing.
  }
  by apply /b_e_type_checker_reflects_typing.
Qed.


Section generator_spec.

  Context `{!wasmG Σ}.
  Context `{!inG Σ (authR (List0 nat))}.

  Definition permitted (xs: list nat) := True.

  Definition SEQ (I : list nat -> iProp Σ) : iProt Σ :=
    ( ! ( []) {{ True%I }} ; ? ( []) {{ False }})%iprot.

  Definition Ψgen I x :=
    match x with
    | SuspendE (Mk_tagidx 0) => SEQ I
    | _ => iProt_bottom
    end.

  Definition naturals_spec addr_naturals cl_naturals f (I : list nat -> iProp Σ) :
    I [] -∗
    N.of_nat addr_naturals ↦[wf] cl_naturals -∗
    EWP [AI_invoke addr_naturals] UNDER f <| Ψgen I |> {{ v ; f, False }}.



End generator_spec.
