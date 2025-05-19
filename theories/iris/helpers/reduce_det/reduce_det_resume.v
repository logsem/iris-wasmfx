From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Set Bullet Behavior "Strict Subproofs".

Lemma resume_null_det tf i i' s f s' f' es:
  reduce s f [AI_basic (BI_ref_null tf); AI_basic $ BI_resume i' i] s' f' es ->
  reduce_det_goal s f [AI_trap] s' f' es [AI_basic (BI_ref_null tf); AI_basic $ BI_resume i' i]. 
Proof.
  move => Hred.
   only_one.
  inversion H3; subst.
    destruct vs; inversion H4; subst => //.
    destruct esnewest; first empty_list_no_reduce.
    inversion H1; subst.
    destruct esnewest => //. 
    clear -Hred.
    lazymatch goal with
    | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
    end.
    exfalso. 
    induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
        first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
        try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by do 4 destruct vs => //);
          do 4 destruct bef => //
        | move/lfilledP in H02; inversion H02; subst;
          try (by do 4 destruct vs => //);
          try (by do 4 destruct bef => //);
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
              inversion H3; subst;
              destruct es => //; apply IHHred => //
              )
        ].
  inversion H3; subst => //.
Qed.

Lemma resume_det i t1s t2s vs k hh LI hs hsd s f s' f' es' :
  const_list vs ->
  stypes (f_inst f) i = Some (Tf t1s t2s) ->
  length vs = length t1s ->
  nth_error (s_conts s) k = Some (Cont_hh (Tf t1s t2s) hh) ->
  hfilled No_var hh vs LI ->
  [seq desugar_continuation_clause (f_inst f) i | i <- hs] = [seq Some i | i <- hsd] ->
  reduce s f (vs ++ [AI_ref_cont k; AI_basic (BI_resume i hs)]) s' f' es' ->
  reduce_det_goal (upd_s_cont s k (Cont_dagger (Tf t1s t2s))) f [AI_prompt t2s hsd LI] s' f' es' (vs ++ [AI_ref_cont k; AI_basic (BI_resume i hs)]).
Proof.
  move => Hvs H H0 H1 Hves H2 Hred.
  lazymatch goal with
  | _ : reduce _ _ ?es _ _ _ |- _ => remember es as es0 end.
  rewrite separate1 -cat_app catA in Heqes0.
  induction Hred.
  destruct H3.
  all: try by (try destruct ref); (try destruct v; try destruct v); rewrite separate1 in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try rewrite /= H3; try apply const_list_concat; try apply v_to_e_is_const_list.
  all: try by rewrite separate2 in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try apply const_list_concat; try apply v_to_e_is_const_list.
  all: try by rewrite - (app_nil_l [_]) in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try apply const_list_concat; try apply v_to_e_is_const_list.
  
  all: try by destruct v1, v2; try destruct v; try destruct v0; rewrite separate3 in Heqes0; apply first_values in Heqes0 as (? & ? & ?); try apply const_list_concat; try apply v_to_e_is_const_list.
  all: try by apply first_values in Heqes0 as (? & ? & ?); subst; try apply const_list_concat; try apply v_to_e_is_const_list.
  all: try by rewrite separate1 -cat_app catA in Heqes0;
      apply first_values in Heqes0 as (? & ? & ?); 
    try apply const_list_concat; subst; try apply v_to_e_is_const_list.
  - do 3 destruct vs => //. 
  - move/lfilledP in H4; inversion H4; subst.
    by apply first_values in H9 as (? & ? & ?); try apply const_list_concat; try apply v_to_e_is_const_list.
    by apply first_values in H10 as (? & ? & ?); try apply const_list_concat; try apply v_to_e_is_const_list.
    by apply first_values in H10 as (? & ? & ?); try apply const_list_concat; try apply v_to_e_is_const_list.
  - rewrite -catA /= in Heqes0.
    apply app_inj_2 in Heqes0 as [-> Heq] => //.
    inversion Heq; subst.
    rewrite H4 in H; inversion H; subst.
    rewrite H6 in H1; inversion H1; subst.
    eapply hfilled_inj in Hves.
    2: exact H7.
    subst.
    rewrite H2 in H8.
    apply map_Some_inj in H8 as ->.
    by left.
  - repeat destruct vs => //.
    inversion Heqes0; subst.
    rewrite H3 in H1 => //. 
    
  - move/lfilledP in H3; inversion H3; subst.
    all: try by apply first_values in H10 as (? & ? & ?); try apply const_list_concat; try apply v_to_e_is_const_list.
    move/lfilledP in H4; inversion H4; subst.
    separate_last es'0.
    + rewrite -cat_app in H9. repeat rewrite catA in H9.
      apply concat_cancel_last in H9 as [Hvcs ->].
      exfalso; eapply values_no_reduce.
      exact Hred.
      assert (const_list (vs ++ [AI_ref_cont k])); first by apply const_list_concat.
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
        destruct vs.
        -- inversion Hvcs; subst. destruct vs0, l => //.
           clear - Hred.
           lazymatch goal with
    | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
    end.

    induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
        first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
        try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by do 4 destruct vs => //);
          do 4 destruct bef => //
        | move/lfilledP in H02; inversion H02; subst;
          try (by do 4 destruct vs => //);
          try (by do 4 destruct bef => //);
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
              inversion H3; subst;
              destruct es => //; apply IHHred => //
              )
        ].
  inversion H3; subst => //.
        -- inversion Hvcs; subst.
           simpl in H8. remove_bools_options.
           eapply resume_not_enough_arguments_no_reduce.
           exact H. exact H1.
           instantiate (5 := vs).
           rewrite separate1 -cat_app catA -H9.
           rewrite -catA.
           eapply r_label.
           exact Hred.
           instantiate (2 := LH_base vs0 []).
           instantiate (2 := 0).
           rewrite /lfilled /lfill /= H7.
           rewrite app_nil_r //.
           rewrite /lfilled /lfill /= H7.
           done. simpl in Hvs; remove_bools_options. done.
           simpl in H0. lia.
Qed.

Lemma resume_dagger_det k tf i i' s f s' f' es:
  nth_error (s_conts s) k = Some (Cont_dagger tf) ->
  reduce s f [AI_ref_cont k; AI_basic $ BI_resume i' i] s' f' es ->
  reduce_det_goal s f [AI_trap] s' f' es [AI_ref_cont k; AI_basic $ BI_resume i' i]. 
Proof.
  move => Hk Hred.
  only_one.
  repeat destruct vs => //.
  inversion Heqesnew; subst.
  rewrite H2 in Hk => //. 
  inversion H3; subst.
  destruct vs; inversion H4; subst => //.
    destruct esnewest; first empty_list_no_reduce.
    inversion H1; subst.
    destruct esnewest => //. 
    clear -Hred.
    lazymatch goal with
    | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
    end.
    exfalso. 
    induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
        first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
        try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by do 4 destruct vs => //);
          do 4 destruct bef => //
        | move/lfilledP in H02; inversion H02; subst;
          try (by do 4 destruct vs => //);
          try (by do 4 destruct bef => //);
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
              inversion H3; subst;
              destruct es => //; apply IHHred => //
              )
        ].
  inversion H3; subst => //.
Qed.
