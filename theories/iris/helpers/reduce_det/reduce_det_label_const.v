From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Set Bullet Behavior "Strict Subproofs".

Lemma label_const_det n es vs s f s' f' es':
  const_list vs ->
  reduce s f [AI_label n es vs] s' f' es' ->
  reduce_det_strong_goal s f vs s' f' es'.
Proof.
  intros Hvs Hred.
  lazymatch goal with
  | _ : reduce _ _ ?es _ _ _ |- _ => remember es as ves
  end.
  induction Hred.
  inversion H.
  all: remember Heqves as Heqves'; clear HeqHeqves' Heqves.
  all: subst.
  all: try by inversion Heqves'.
  all: try by do 4 destruct vs0 => //.
  all: try by do 4 destruct vcs => //.
  - inversion Heqves'; subst.
    apply lfilled_const in H2 as [??] => //.
    apply const_list_split in H2 as [??] => //.
  - move/lfilledP in H1; inversion H1; subst.
    all: try by do 4 destruct bef => //.
    rewrite - (app_nil_l [_]) in H2.
    apply first_values in H2 as (_ & ? & _) => //.
  - move/lfilledP in H; inversion H; subst.
    all: try by do 4 destruct bef => //.
    + destruct vs0.
      * destruct es0; first empty_list_no_reduce.
        inversion H1; subst.
        destruct es0, es'0 => //.
        move/lfilledP in H0; inversion H0; subst.
        simpl in *.
        rewrite cats0.
        apply IHHred => //.
      * inversion H1; subst => //.
    + destruct vs0 ; last by destruct vs0.
      inversion H1; subst.
      exfalso; apply values_no_reduce in Hred => //.
      move/lfilledP in H6.
      apply lfilled_const in H6 as [??] => //.
Qed.

Lemma label_trap_det n es s f s' f' es':
  reduce s f [AI_label n es [AI_trap]] s' f' es' ->
  reduce_det_strong_goal s f [AI_trap] s' f' es'.
Proof.
  intros Hred.
  lazymatch goal with
  | _ : reduce _ _ ?es _ _ _ |- _ => remember es as ves
  end.
  induction Hred.
  inversion H.
  all: remember Heqves as Heqves'; clear HeqHeqves' Heqves.
  all: subst.
  all: try by inversion Heqves'.
  all: try by do 4 destruct vs => //.
  all: try by do 4 destruct vcs => //.
  - inversion Heqves'; subst.
    eapply filled_singleton in H2 as (_ & _ & ?) => //.
    all: do 2 destruct vs => //.
  - move/lfilledP in H1; inversion H1; subst.
    all: try by do 4 destruct bef => //.
    rewrite - (app_nil_l [_]) in H2.
    apply first_values in H2 as (_ & ? & _) => //.
  - move/lfilledP in H; inversion H; subst.
    all: try by do 4 destruct bef => //.
    + destruct vs.
      * destruct es0; first empty_list_no_reduce.
        inversion H1; subst.
        destruct es0, es'0 => //.
        move/lfilledP in H0; inversion H0; subst.
        simpl in *.
        rewrite cats0.
        apply IHHred => //.
      * inversion H1; subst => //.
    + destruct vs ; last by destruct vs.
      inversion H1; subst.
      move/lfilledP in H6.
      apply filled_singleton in H6 as (? & ? & ?) => //.
      subst; exfalso; eapply AI_trap_irreducible => //.
      intros ->; empty_list_no_reduce.
Qed. 


