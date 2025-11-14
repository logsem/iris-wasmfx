From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Set Bullet Behavior "Strict Subproofs".

Lemma throw_det x a ts ves vcs s2 s f s' f' es' :
  nth_error (inst_tags (f_inst f)) x = Some a ->
  nth_error (s_tags s) a = Some (Tf ts []) ->
  length ves = length ts ->
  ves = v_to_e_list vcs ->
  s2 = add_exn s {| e_tag := Mk_tagidx a; e_fields := vcs |} ->
  reduce s f (ves ++ [AI_basic (BI_throw x)]) s' f' es' ->
  reduce_det_strong_goal s2 f [AI_ref_exn (length (s_exns s)) (Mk_tagidx a); AI_basic BI_throw_ref] s' f' es' .
Proof.
  move => H H0 H1 Hves H2 Hred.
  subst ves.

  lazymatch goal with
  | _ : reduce _ _ ?es _ _ _ |- _ => remember es as es0 end.
  induction Hred.
  destruct H3.
  all: try by (try destruct ref); (try destruct v; try destruct v); rewrite separate1 in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try rewrite /= H3; try apply v_to_e_is_const_list.
  all: try by rewrite separate2 in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try apply v_to_e_is_const_list.
  all: try by rewrite - (app_nil_l [_]) in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try apply v_to_e_is_const_list.
  
  all: try by destruct v1, v2; try destruct v; try destruct v0; rewrite separate3 in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try apply v_to_e_is_const_list.
  all: try by apply first_values in Heqes0 as (? & ? & ?); subst; try apply v_to_e_is_const_list.
  all: try by rewrite separate1 -cat_app catA in Heqes0;
      apply first_values in Heqes0 as (? & ? & ?);
    try apply const_list_concat; subst; try apply v_to_e_is_const_list.
  - move/lfilledP in H4; inversion H4; subst.
    by apply first_values in H9 as (? & ? & ?); try apply v_to_e_is_const_list.
    by apply first_values in H10 as (? & ? & ?); try apply v_to_e_is_const_list.
    by apply first_values in H10 as (? & ? & ?); try apply v_to_e_is_const_list.
  - apply concat_cancel_last in Heqes0 as [-> Heq].
    inversion Heq; subst.
    rewrite H3 in H; inversion H; subst.
    apply v_to_e_inj in H5 as ->.
    repeat split => //. 
    
  - move/lfilledP in H3; inversion H3; subst.
    all: try by apply first_values in H10 as (? & ? & ?); try apply v_to_e_is_const_list.
    move/lfilledP in H4; inversion H4; subst.
    separate_last es'0.
    + rewrite -cat_app in H9. repeat rewrite catA in H9.
      apply concat_cancel_last in H9 as [Hvcs ->].
      exfalso; eapply values_no_reduce.
      exact Hred.
      assert (const_list (v_to_e_list vcs)); first by apply v_to_e_is_const_list.
      rewrite -Hvcs in H2.
      apply const_list_split in H2 as [??].
      apply const_list_split in H2 as [??] => //. 
    + destruct vs.
      * do 1 rewrite /= cats0.
        rewrite /= cats0 in H9.
        apply IHHred => //.
      * separate_last es; last by empty_list_no_reduce.
        rewrite cats0 in H9.
        repeat rewrite -cat_app in H9.
        repeat rewrite catA in H9.
        apply concat_cancel_last in H9 as [Hvcs ->].
        exfalso.
        eapply throw_not_enough_arguments_no_reduce.
        exact H. exact H0.
        exact Hred.
        assert (const_list (v_to_e_list vcs)); first by apply v_to_e_is_const_list.
        rewrite -Hvcs in H2.
        apply const_list_split in H2 as [??] => //.
        rewrite -Hvcs cat_app length_app /= in H1.
        lia.
Qed.

