From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Set Bullet Behavior "Strict Subproofs".

Lemma suspend_desugar_det x a t1s t2s vs s f s' f' es' :
  nth_error (inst_tags (f_inst f)) x = Some a ->
  nth_error (s_tags s) a = Some (Tf t1s t2s) ->
  length vs = length t1s ->
  reduce s f (v_to_e_list vs ++ [AI_basic (BI_suspend (Mk_tagident x))]) s' f' es' ->
  reduce_det_goal s f [AI_suspend_desugared vs (Mk_tagidx a)] s' f' es' (v_to_e_list vs ++ [AI_basic (BI_suspend (Mk_tagident x))]). 
Proof.
  move => H H0 H1 Hred.
  assert (0 = 0) as H2; first done.
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
  - apply concat_cancel_last in Heqes0 as [Hvs Heq].
    inversion Heq; subst.
    rewrite H3 in H; inversion H; subst.
    apply v_to_e_inj in Hvs as ->.
    repeat split => //. by left.
    
  - move/lfilledP in H3; inversion H3; subst.
    all: try by apply first_values in H10 as (? & ? & ?); try apply v_to_e_is_const_list.
    move/lfilledP in H4; inversion H4; subst.
    separate_last es'0.
    + rewrite -cat_app in H9. repeat rewrite catA in H9.
      apply concat_cancel_last in H9 as [Hvcs ->].
      exfalso; eapply values_no_reduce.
      exact Hred.
      assert (const_list (v_to_e_list vs)); first by apply v_to_e_is_const_list.
      rewrite -Hvcs in H6.
      apply const_list_split in H6 as [??].
      apply const_list_split in H6 as [??] => //. 
    + destruct vs0.
      * do 2 rewrite /= cats0.
        rewrite /= cats0 in H9.
        apply IHHred => //.
      * separate_last es; last by empty_list_no_reduce.
        rewrite cats0 in H9.
        repeat rewrite -cat_app in H9.
        repeat rewrite catA in H9.
        apply concat_cancel_last in H9 as [Hvcs ->].
        exfalso.
        eapply suspend_not_enough_arguments_no_reduce.
        exact H. exact H0.
        exact Hred.
        assert (const_list (v_to_e_list vs)); first by apply v_to_e_is_const_list.
        rewrite -Hvcs in H6.
        apply const_list_split in H6 as [??] => //.
        assert (length (v_to_e_list vs) = length t1s) as H1'; first by rewrite length_map.
        rewrite -Hvcs cat_app length_app /= in H1'.
        lia.
Qed.


Lemma suspend_det a t1s t2s hs x l hh vs LI ts s f s' f' es':
  x = Mk_tagidx a ->
  List.nth_error (s_tags s) a = Some (Tf t1s t2s) ->
  firstx_continuation_suspend hs x = Some l ->
  hfilled (Var_prompt_suspend x) hh [AI_suspend_desugared vs x] LI ->
  reduce s f [AI_prompt ts hs LI] s' f' es' ->
  reduce_det_goal (new_cont s (Cont_hh (Tf t2s ts) hh)) f (v_to_e_list vs ++ [AI_ref_cont (length (s_conts s)); AI_basic (BI_br l)]) s' f' es' [AI_prompt ts hs LI]. 
Proof.
  intros -> Htag Hfirst Hfill Hred.
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
    apply hfilled_const in Hfill => //.
  - inversion Heqves'; subst.
    apply hfilled_singleton in Hfill as ( _ & ?) => //.
  - move/lfilledP in H1; inversion H1; subst.
    all: try by do 2 destruct vs0 => //.
    all: try by do 2 destruct bef => //.
    destruct bef; last by destruct bef.
    inversion H2; subst.
    move/lfilledP in H7.
    apply hfilled_to_llfill in Hfill as [llh Hllh].
    edestruct lfilled_llfill_first_values as (? & ?).
    instantiate (3 := []). exact H7. instantiate (2 := []). exact Hllh.
    all: try done.
  - inversion Heqves'; subst.
    edestruct hfilled_first_values as (? & ?).
    instantiate (3 := []).
    exact H2.
    instantiate (2 := []).
    exact Hfill.
    all: try done.
    destruct H3 as [_ ->] => //.
    inversion H; subst.
    rewrite H1 in Hfirst; inversion Hfirst; subst.
    rewrite H0 in Htag; inversion Htag; subst.
    repeat split => //. by left.
  - inversion Heqves'; subst.
    edestruct hfilled_first_values as (? & ?).
    instantiate (3 := []).
    exact H2.
    instantiate (2 := []).
    exact Hfill.
    all: try done.
  - move/lfilledP in H; inversion H; subst.
    all: try by do 2 destruct vs0 => //. 
    all: try by do 2 destruct bef => //. 
    all: move/lfilledP in H0; inversion H0; subst.
    + destruct vs0; last by destruct vs0, es => //; empty_list_no_reduce.
      destruct es; first empty_list_no_reduce.
      inversion H1; destruct es, es'0 => //.
      simpl in *. subst. rewrite cats0.
      apply IHHred => //.
    + destruct bef; last by destruct bef.
      inversion H1; subst.
      exfalso; eapply hfilled_suspend_and_reduce.
      exact Hred.
      exact Hfill.
      apply/lfilledP => //.
Qed. 
