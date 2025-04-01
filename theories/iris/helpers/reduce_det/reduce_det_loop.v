From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Lemma loop_det vs n m t1s t2s s f es s' f' es' :
  const_list vs ->
  length vs = n ->
  length t1s = n ->
  length t2s = m ->
  reduce s f (vs ++ [AI_basic (BI_loop (Tf t1s t2s) es)]) s' f' es' ->
  reduce_det_goal s f [AI_label n [AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)] s' f' es' (vs ++ [AI_basic (BI_loop (Tf t1s t2s) es)]).
Proof.
  move => H H0 H1 H2 Hred.
  (* Here, in the block case, the left-hand-side of Hred2 is
         [ vs ++ [AI_basic (BI_block (Tf t1s t2s) es)] ] which is not an explicit
         list, thus we cannot use [ only_one ]. We perform the case analysis on Hred2
         by hand. Likewise for the following case (loop) *)
  remember (vs ++ [AI_basic (BI_loop (Tf t1s t2s) es)])%SEQ as es0.
  (* apply Logic.eq_sym in Heqes0. *)
  induction Hred.
  destruct H3.
  all: try by (try destruct ref); (try destruct v; try destruct v); rewrite separate1 in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try rewrite /= H3.
  all: try by rewrite separate2 in Heqes0; apply first_values in Heqes0 as (? & ? & ?) => //.
  all: try by rewrite - (app_nil_l [_]) in Heqes0; apply first_values in Heqes0 as (? & ? & ?).
  
  all: try by destruct v1, v2; try destruct v; try destruct v0; rewrite separate3 in Heqes0; apply first_values in Heqes0 as (? & ? & ?) => //.
  all: try by apply first_values in Heqes0 as (? & ? & ?); subst; try apply v_to_e_is_const_list.
  all: try by rewrite separate1 -cat_app catA in Heqes0;
      apply first_values in Heqes0 as (? & ? & ?);
    try apply const_list_concat; subst; try apply v_to_e_is_const_list.
  - apply concat_cancel_last in Heqes0 as [-> Heq].
    inversion Heq; subst. left. done.
  - move/lfilledP in H4; inversion H4; subst.
    by apply first_values in H9 as (? & ? & ?).
    by apply first_values in H10 as (? & ? & ?).
    by apply first_values in H10 as (? & ? & ?).
  - move/lfilledP in H3; inversion H3; subst.
    all: try by apply first_values in H10 as (? & ? & ?).
    move/lfilledP in H4; inversion H4; subst.
    separate_last es'0.
    + rewrite -cat_app in H9. repeat rewrite catA in H9.
      apply concat_cancel_last in H9 as [<- ->].
      exfalso; eapply values_no_reduce.
      exact Hred.
      apply const_list_split in H as [??].
      apply const_list_split in H as [??] => //. 
    + destruct vs0.
      * do 2 rewrite /= cats0.
        rewrite /= cats0 in H9.
        apply IHHred => //.
      * separate_last es0; last by empty_list_no_reduce.
        rewrite cats0 in H9.
        repeat rewrite -cat_app in H9.
        repeat rewrite catA in H9.
        apply concat_cancel_last in H9 as [<- ->].
        exfalso.
        eapply loop_not_enough_arguments_no_reduce.
        exact Hred. apply const_list_split in H as [??] => //.
        rewrite cat_app length_app /= in H1.
        lia.
Qed.

