From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Set Bullet Behavior "Strict Subproofs".

Lemma return_det vs n i lh s f f0 es s' f' es' :
  const_list vs ->
  length vs = n ->
  lfilled i lh (vs ++ [AI_basic BI_return]) es ->
  reduce s f [AI_local n f0 es] s' f' es' ->
  reduce_det_goal s f vs s' f' es' [AI_local n f0 es].
Proof.
  move => H H0 H1 Hred.
  (* this is the rs_return case. It combines the difficulties of rs_br with
         the fact that, as for the previous few cases, [ only_one ] cannot be applied
         and thus all the work must be performed by hand *)
  left ; remember [AI_local n f0 es] as es0.
  rewrite <- app_nil_l in Heqes0.
  induction Hred.
  inversion H2.
  all: remember Heqes0 as Heqes; clear HeqHeqes Heqes0; subst.
  all: try done.
  all: try by do 2 destruct vs0 => //.
  all: try by do 2 destruct vcs => //. 
  - inversion Heqes; subst.
    apply lfilled_const in H1 as [??] => //.
    apply const_list_split in H1 as [??] => //.
  - inversion Heqes; subst.
    apply filled_singleton in H1 as (? & ? & ?) => //.
    all: do 2 destruct vs => //.
  - inversion Heqes; subst.
    edestruct lfilled_first_values as (_ & _ & Hsol).
    exact H5. exact H1. all: try done.
    apply Hsol in H4 as [-> ->] => //.
  - move/lfilledP in H4; inversion H4; subst.
    do 2 destruct vs0 => //.
    all: do 2 destruct bef => //.
  - move/lfilledP in H2; inversion H2; subst.
    all: move/lfilledP in H3; inversion H3; subst.
    all: try by do 2 destruct vs0 => //.
    all: try by do 2 destruct bef => //.
    destruct vs0; last by destruct vs0, es0 => //; empty_list_no_reduce.
    destruct es0; first empty_list_no_reduce.
    inversion H0; subst.
    destruct es0, es'0 => //.
    rewrite /= cats0.
    by apply IHHred.
  - inversion Heqes; subst.
    exfalso; eapply lfilled_return_and_reduce.
    exact Hred.
    2: exact H1.
    done.
    instantiate (1 := LH_base [] []).
    instantiate (1 := 0).
    unfold lfilled, lfill => //=.
    rewrite app_nil_r => //.
Qed.
