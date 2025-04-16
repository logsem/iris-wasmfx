From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Set Bullet Behavior "Strict Subproofs".

Lemma switch_null_det tf i i' s f s' f' es:
  reduce s f [AI_basic (BI_ref_null tf); AI_basic $ BI_switch i' i] s' f' es ->
  reduce_det_goal s f [AI_trap] s' f' es [AI_basic (BI_ref_null tf); AI_basic $ BI_switch i' i]. 
Proof.
  move => Hred.
  (* example of a usage of [ only_one ] : in this subgoal, we know that Hred2 is
         the hypothesis [ [AI_basic (BI_const v) ; AI_basic (BI_unop t op) ] -> es2 ].
         [ only_one ] selects the left disjunct in the conclusion, meaning we wish
         to show that in this case, there was indeed determinism. Then it performs a 
         case analysis on Hred2. Most cases have a left-hand-side very different from
         [AI_basic (BI_const v) ; AI_basic (BI_unop t op)] and can thus be exfalsoed.
         Some cases, like the r_label case, require a little more effort, but the tactic
         can handle most difficulties. See the next comment for an example of when 
         [ only_one ] cannot exfalso all irrelevant cases *)
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

Lemma switch_desugar_det x a k cont t1s t2s vs i tf s f s' f' es' :
  stypes s (f_inst f) i = Some tf ->
  nth_error (inst_tags (f_inst f)) x = Some a ->
  nth_error (s_conts s) k = Some cont ->
  typeof_cont cont = Tf t1s t2s ->
  S (length vs) = length t1s ->
  reduce s f (v_to_e_list vs ++ [AI_ref_cont k; AI_basic (BI_switch i (Mk_tagident x))]) s' f' es' ->
  reduce_det_goal s f [AI_switch_desugared vs k tf (Mk_tagidx a)] s' f' es' (v_to_e_list vs ++ [AI_ref_cont k; AI_basic (BI_switch i (Mk_tagident x))]). 
Proof.
  move => H H0 H1 H2 Hlen Hred.
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
    apply app_inj_2 in Heqes0 as [Hvs Heq] => //.
    inversion Heq; subst.
    rewrite H3 in H; inversion H; subst.
    rewrite H4 in H0; inversion H0; subst.
    rewrite H6 in H1; inversion H1; subst.
    apply v_to_e_inj in Hvs as ->.
    by left.
  - move/lfilledP in H3; inversion H3; subst.
    all: try by apply first_values in H10 as (? & ? & ?); try apply const_list_concat; try apply v_to_e_is_const_list.
    move/lfilledP in H4; inversion H4; subst.
    separate_last es'0.
    + rewrite -cat_app in H9. repeat rewrite catA in H9.
      apply concat_cancel_last in H9 as [Hvcs ->].
      exfalso; eapply values_no_reduce.
      exact Hred.
      assert (const_list (v_to_e_list vs ++ [AI_ref_cont k])); first by apply const_list_concat; try apply v_to_e_is_const_list.
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
           eapply switch_not_enough_arguments_no_reduce.
           done. done. 
           instantiate (6 := v_to_e_list vs).
           rewrite separate1 -cat_app catA -H9.
           rewrite -catA.
           eapply r_label.
           exact Hred.
           instantiate (3:= LH_base vs0 []).
           instantiate (3 := 0).
           rewrite /lfilled /lfill /= H7.
           rewrite app_nil_r //.
           rewrite /lfilled /lfill /= H7.
           done.
           apply v_to_e_is_const_list.
           simpl in Hlen. rewrite length_map. lia.
Qed.


Lemma switch_det tf t1s ts tf' t2s t1s' t2s' hh' hs hh vs k x LI LI' s f s' f' es':
  tf = Tf (t1s ++ [T_ref (T_contref tf')]) t2s ->
  nth_error (s_conts s) k = Some (Cont_hh (Tf t1s' t2s') hh') ->
  firstx_continuation_switch hs x = true ->
  hfilled (Var_prompt_switch x) hh [AI_switch_desugared vs k tf x] LI ->
  hfilled No_var hh' (v_to_e_list vs ++ [AI_ref_cont (length (s_conts s))]) LI' ->
  reduce s f [AI_prompt ts hs LI] s' f' es' ->
  reduce_det_goal (new_cont (upd_s_cont s k (Cont_dagger (Tf t1s' t2s'))) (Cont_hh tf' hh)) f [AI_prompt t2s' hs LI'] s' f' es' [AI_prompt ts hs LI]. 
Proof.
  intros -> Hcont Hfirst Hfill Hfill' Hred.
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
  - inversion Heqves'; subst.
    edestruct hfilled_first_values as (? & ?).
    instantiate (3 := []).
    exact H2.
    instantiate (2 := []).
    exact Hfill.
    all: try done.
    destruct H4 as [_ ->] => //.
    inversion H0; subst.
    rewrite H1 in Hcont; inversion Hcont; subst.
    apply concat_cancel_last in H7 as [-> Heq].
    inversion Heq; subst.
    eapply hfilled_inj in Hfill'.
    2: exact H3.
    subst.
    by left.

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
      edestruct hfilled_switch_and_reduce as (tf'' & sh & hh'' & Hfill'' & Hcont' & Heq & Heq' & Htrap).
      exact Hred.
      exact Hfill.
      apply/lfilledP => //.
      rewrite Hcont' in Hcont. done.
Qed. 



