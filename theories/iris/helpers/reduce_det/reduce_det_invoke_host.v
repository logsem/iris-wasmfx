From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_properties iris_reduce_det_prelude.

Set Bullet Behavior "Strict Subproofs".

Lemma invoke_host_det h ws2 f2 es2 s a f t1s t2s vcs:
  nth_error (s_funcs s) a = Some (FC_func_host (Tf t1s t2s) h) ->
  length t1s = length vcs ->
  reduce s f (v_to_e_list vcs ++ [AI_invoke a]) ws2 f2 es2 ->
  (s, f, [AI_call_host (Tf t1s t2s) h vcs]) = (ws2, f2, es2).
Proof.
  move => H H0 Hred.
  lazymatch goal with
  | _ : reduce _ _ ?es _ _ _ |- _ => remember es as es0 end.
  induction Hred.
  destruct H1.
  all: try by (try destruct ref); (try destruct v; try destruct v); rewrite separate1 in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try rewrite /= H1; try apply v_to_e_is_const_list.
  all: try by rewrite separate2 in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try apply v_to_e_is_const_list.
  all: try by rewrite - (app_nil_l [_]) in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try apply v_to_e_is_const_list.
  
  all: try by destruct v1, v2; try destruct v; try destruct v0; rewrite separate3 in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try apply v_to_e_is_const_list.
  all: try by apply first_values in Heqes0 as (? & ? & ?); subst; try apply v_to_e_is_const_list.
  all: try by rewrite separate1 -cat_app catA in Heqes0;
      apply first_values in Heqes0 as (? & ? & ?);
    try apply const_list_concat; subst; try apply v_to_e_is_const_list.
  - move/lfilledP in H2; inversion H2; subst.
    by apply first_values in H7 as (? & ? & ?); try apply v_to_e_is_const_list.
    by apply first_values in H8 as (? & ? & ?); try apply v_to_e_is_const_list.
    by apply first_values in H8 as (? & ? & ?); try apply v_to_e_is_const_list.
  - apply concat_cancel_last in Heqes0 as [-> Heq].
    inversion Heq; subst.
    rewrite H in H1; inversion H1; subst.
  - apply concat_cancel_last in Heqes0 as [-> Heq].
    inversion Heq; subst.
    apply v_to_e_inj in H3 as ->.
    rewrite H in H1; inversion H1; subst.
    done.
  - move/lfilledP in H1; inversion H1; subst.
    all: try by apply first_values in H8 as (? & ? & ?); try apply v_to_e_is_const_list.
    move/lfilledP in H2; inversion H2; subst.
    separate_last es'0.
    + rewrite -cat_app in H7. repeat rewrite catA in H7.
      apply concat_cancel_last in H7 as [Hvcs ->].
      exfalso; eapply values_no_reduce.
      exact Hred.
      assert (const_list ((vs ++ es) ++ l)%SEQ) ; first by rewrite Hvcs; apply v_to_e_is_const_list.
      apply const_list_split in H4 as [??].
      apply const_list_split in H4 as [??] => //. 
    + destruct vs.
      * rewrite /= cats0.
        rewrite /= cats0 in H7.
        apply IHHred => //.
      * separate_last es; last by empty_list_no_reduce.
        rewrite cats0 in H7.
        repeat rewrite -cat_app in H7.
        repeat rewrite catA in H7.
        apply concat_cancel_last in H7 as [Hvcs ->].
        exfalso.
        eapply invoke_not_enough_arguments_no_reduce_host.
        exact H.
        exact Hred.
        assert (const_list ((a0 :: vs) ++ l)%SEQ); first by rewrite Hvcs; apply v_to_e_is_const_list.
        apply const_list_split in H4 as [??] => //.
        apply (f_equal length) in Hvcs.
        rewrite v_to_e_length in Hvcs.
        rewrite -Hvcs in H0.
        rewrite cat_app length_app /= in H0.
        lia.
Qed.

  
