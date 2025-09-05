From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_properties iris_reduce_det_prelude.

Set Bullet Behavior "Strict Subproofs".

Lemma invoke_native_det ws2 f2 es2 s a f f' t1s t2s ts es vcs:
  nth_error (s_funcs s) a = Some (FC_func_native (f_inst f') (Tf t1s t2s) ts es) ->
  length t1s = length vcs ->
  f_locs f' = (vcs ++ default_vals ts) ->
  reduce s f (v_to_e_list vcs ++ [AI_invoke a]) ws2 f2 es2 ->
  (s, f, [AI_frame (length t2s) f' [AI_basic (BI_block (Tf [] t2s) es)]]) = (ws2, f2, es2).
Proof.
  move => H H0 H1 Hred.
  lazymatch goal with
  | _ : reduce _ _ ?es _ _ _ |- _ => remember es as es0 end.
  induction Hred.
  destruct H2.
  all: try by (try destruct ref); (try destruct v; try destruct v); rewrite separate1 in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try rewrite /= H2; try apply v_to_e_is_const_list.
  all: try by rewrite separate2 in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try apply v_to_e_is_const_list.
  all: try by rewrite - (app_nil_l [_]) in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try apply v_to_e_is_const_list.
  
  all: try by destruct v1, v2; try destruct v; try destruct v0; rewrite separate3 in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try apply v_to_e_is_const_list.
  all: try by apply first_values in Heqes0 as (? & ? & ?); subst; try apply v_to_e_is_const_list.
  all: try by rewrite separate1 -cat_app catA in Heqes0;
      apply first_values in Heqes0 as (? & ? & ?);
    try apply const_list_concat; subst; try apply v_to_e_is_const_list.
  - move/lfilledP in H3; inversion H3; subst.
    by apply first_values in H8 as (? & ? & ?); try apply v_to_e_is_const_list.
    by apply first_values in H9 as (? & ? & ?); try apply v_to_e_is_const_list.
    by apply first_values in H9 as (? & ? & ?); try apply v_to_e_is_const_list.
  - apply concat_cancel_last in Heqes0 as [-> Heq].
    inversion Heq; subst.
    apply v_to_e_inj in H4 as ->.
    rewrite H in H2; inversion H2; subst.
    destruct f', f'0.
    simpl in H4. simpl in H1. simpl in H11. subst. done.
  - apply concat_cancel_last in Heqes0 as [-> Heq].
    inversion Heq; subst.
    rewrite H in H2 => //. 
  - move/lfilledP in H2; inversion H2; subst.
    all: try by apply first_values in H9 as (? & ? & ?); try apply v_to_e_is_const_list.
    move/lfilledP in H3; inversion H3; subst.
    separate_last es'0.
    + rewrite -cat_app in H8. repeat rewrite catA in H8.
      apply concat_cancel_last in H8 as [Hvcs ->].
      exfalso; eapply values_no_reduce.
      exact Hred.
      assert (const_list ((vs ++ es0) ++ l)%SEQ) ; first by rewrite Hvcs; apply v_to_e_is_const_list.
      apply const_list_split in H5 as [??].
      apply const_list_split in H5 as [??] => //. 
    + destruct vs.
      * rewrite /= cats0.
        rewrite /= cats0 in H8.
        apply IHHred => //.
      * separate_last es0; last by empty_list_no_reduce.
        rewrite cats0 in H8.
        repeat rewrite -cat_app in H8.
        repeat rewrite catA in H8.
        apply concat_cancel_last in H8 as [Hvcs ->].
        exfalso.
        eapply invoke_not_enough_arguments_no_reduce_native.
        exact H.
        exact Hred.
        assert (const_list ((a0 :: vs) ++ l)%SEQ); first by rewrite Hvcs; apply v_to_e_is_const_list.
        apply const_list_split in H5 as [??] => //.
        apply (f_equal length) in Hvcs.
        rewrite v_to_e_length in Hvcs.
        rewrite -Hvcs in H0.
        rewrite cat_app length_app /= in H0.
        lia.
Qed.

  
