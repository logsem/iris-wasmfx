From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm Require Export stdpp_aux.
Require Export lfilled_reduce iris_split_reduce.

Set Bullet Behavior "Strict Subproofs".

Ltac solve_prim_step_split_reduce_r H objs Heqf0 :=
  left ; subst ;
  apply Logic.eq_sym, app_eq_nil in H as [? ?] ;
  exists objs ; subst ; rewrite app_nil_r ;
  repeat split => //= ; rewrite Heqf0.

Section prim_step_split_properties.
  
  Let reducible := @iris.program_logic.language.reducible wasm_lang.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.
  
  Lemma lfilled_prim_step_split_reduce_r i lh es1 es2 σ LI e2 σ2 f1 f2 obs2 efs2 :
    lfilled i lh (es1 ++ es2)%list LI ->
    reducible (es1, f1) σ ->
    prim_step (LI, f1) σ obs2 (e2, f2) σ2 efs2 ->
    (∃ e', prim_step (es1, f1) σ obs2 (e', f2) σ2 efs2 ∧ lfilled i lh (e' ++ es2) e2)
    \/ (exists lh, lfilled 0 lh [AI_trap] es1) /\ σ = σ2 /\ f1 = f2.
  Proof.
    intros Hfill Hred Hstep.
    edestruct lfilled_reduce as [(es' & Hstep' & Hfill') | (lh0 & Htrap & Hσ) ] => //=.
    - destruct Hred as (obs & [e1 f1'] & s1 & efs & (Hes1 & -> & ->)).
      exists [], (e1 ++ es2, f1'), s1, [].
      repeat split => //=.
      eapply (r_label (k:=0) (lh := LH_base [] es2)) ; try done ;
        unfold lfilled, lfill => //=.
    - eapply prim_step_split_reduce_r in Hstep' as
          [ (es'' & Hes' & Hes1) | (n & m & lh0 & Htrap' & Htrap & -> & ->)].
      + left. eexists ; split => //=.
        replace (cat es'' es2) with (app es'' es2) ; last done.
        rewrite - Hes'.
        done.
      + right. split => //=.
        by eexists.
      + destruct (iris.to_val0 es1) eqn:Htv => //=.
        destruct Hred as (? & [??] & ? & ? & (? & ? & ?)).
        apply val_head_stuck_reduce in H. congruence.
    - right. split => //=.
      move/lfilledP in Htrap; inversion Htrap; subst.
      + destruct Hred as (?&[??]&?&?&(?&?&?)).
        edestruct first_non_value_reduce as (vs' & e' & afte & Hvs & He & Hes1) => //=.
        rewrite Hes1 in H.
        rewrite - app_assoc in H.
        rewrite - app_comm_cons in H.
        apply first_values in H as (<- & <- & ->) => //=.
        2: by destruct He as [He | ->] => //; destruct e' => //; destruct b.
        exists (LH_base vs afte).
        rewrite Hes1; apply/lfilledP; constructor => //.
      + destruct Hred as (?&[??]&?&?&(?&?&?)).
        edestruct first_non_value_reduce as (vs' & e' & afte & Hvs & He & Hes1) => //=.
        rewrite Hes1 in H.
        rewrite - app_assoc in H.
        rewrite - app_comm_cons in H.
        apply first_values in H as (<- & <- & ->) => //=.
        2: by destruct He as [He | ->] => //; destruct e' => //; destruct b.
        exists (LH_handler bef hs lh' afte).
        rewrite Hes1; apply/lfilledP; constructor => //.
      + destruct Hred as (?&[??]&?&?&(?&?&?)).
        edestruct first_non_value_reduce as (vs' & e' & afte & Hvs & He & Hes1) => //=.
        rewrite Hes1 in H.
        rewrite - app_assoc in H.
        rewrite - app_comm_cons in H.
        apply first_values in H as (<- & <- & ->) => //=.
        2: by destruct He as [He | ->] => //; destruct e' => //; destruct b.
        exists (LH_prompt bef ts hs lh' afte).
        rewrite Hes1; apply/lfilledP; constructor => //.
  Qed.


  Lemma local_frame_lfilled_prim_step_split_reduce_r es1 es2 s f n f' e2 s2 f2 efs2 obs2 j lh LI :
    lfilled j lh (es1 ++ es2)%list LI ->
    reducible (es1, f) s ->
    prim_step ([AI_frame n f LI], f') s obs2 (e2, f2) s2 efs2 ->
    (∃ e' f'' LI', prim_step (es1, f) s obs2 (e', f'') s2 efs2 ∧ f' = f2 ∧ e2 = [AI_frame n f'' LI'] ∧ lfilled j lh (e' ++ es2) LI') \/
      ∃ lh0, lfilled 0 lh0 [AI_trap] es1 /\ s = s2 /\ f' = f2 .
  Proof.
    intros Hfill (obs & [e1 f1] & s1 & efs & (Hes1 & -> & ->)) (Hstep & -> & ->).
    remember [AI_frame n f LI] as es.
    induction Hstep ; try (by inversion Heqes) ;
      try (by rewrite <- (app_nil_l [AI_frame _ _ _]) in Heqes ;
           apply app_inj_tail in Heqes as [_ Habs] ;
           inversion Habs).
    { destruct H ; try (by inversion Heqes) ;
        try (by rewrite <- (app_nil_l [AI_frame _ _ _]) in Heqes ;
             apply app_inj_tail in Heqes as [_ Habs] ;
             inversion Habs).
      - inversion Heqes ; subst ; clear Heqes.
        destruct (lfilled_const j lh (es1 ++ es2) LI) as [-> Hconst] => //=.
        unfold const_list in Hconst.
        rewrite forallb_app in Hconst.
        apply andb_true_iff in Hconst as [? _].
        exfalso ; values_no_reduce.
      - inversion Heqes ; subst ; clear Heqes.
        assert (es1 ++ es2 <> []).
        intro.
        apply app_eq_nil in H as [-> _ ] ; empty_list_no_reduce.
        eapply (filled_singleton j lh (es1 ++ es2)) in H as (-> & -> & Hes) => //=.
        apply app_eq_unit in Hes as [[ -> ->]|[-> ->]].
        empty_list_no_reduce.
        by exfalso ; eapply AI_trap_irreducible.
      - inversion Heqes ; subst ; clear Heqes.
        exfalso.
        eapply (lfilled_return_and_reduce (s := s) (es := es1 ++ es2) (LI:=LI)).
        eapply r_label.
        exact Hes1.
        instantiate (1 := LH_base [] es2).
        instantiate (1 := 0).
        unfold lfilled, lfill => //=.
        unfold lfilled, lfill => //=.
        exact H.
        exact H1.
        exact Hfill.
      - subst.
        move/lfilledP in H0; inversion H0; subst.
        repeat destruct vs => //.
        repeat destruct bef => //.
        repeat destruct bef => //. }
    - repeat destruct vs => //.
    - repeat destruct vs => //.
    - repeat destruct vs => //.
    - repeat destruct ves => //.
    - subst les.
      assert (es <> []) ; first by intro ; subst ;  empty_list_no_reduce.
      eapply (filled_singleton k lh0 es) in H1 as (-> & -> & Hes) => //=.
      unfold lfilled, lfill in H0 ; simpl in H0 ; rewrite app_nil_r in H0.
      move/eqP in H0; rewrite H0.
      apply IHHstep => //=.
    - inversion Heqes ; subst n0 f0 es ; clear Heqes.
      assert (reducible (es1, f) s).
      { eexists _, (_,_) , _, _. repeat split => //=. } 
      assert (prim_step (LI, f) s [] (es', f') s' []).
      { repeat split => //=. }
      edestruct lfilled_prim_step_split_reduce_r
        as [(e' & Hes1' & Hfill') | [[lh0 Htrap] Hσ]].
      exact Hfill.
      exact H.
      exact H0.
      left.
      eexists _,_,_. repeat split => //=.
      right.
      eexists.
      split => //=.
      inversion Hσ ; subst.
      done.
  Qed.    


  Lemma local_frame_prim_step_split_reduce_r es1 es2 s f n f' e2 s2 f2 efs2 obs2 :
    reducible (es1, f) s ->
    prim_step ([AI_frame n f (es1 ++ es2)], f') s obs2 (e2, f2) s2 efs2 ->
    (∃ e' f'', prim_step (es1, f) s obs2 (e', f'') s2 efs2 ∧ f' = f2 ∧ e2 = [AI_frame n f'' (e' ++ es2)]) \/
      (∃ lh0, lfilled 0 lh0 [AI_trap] es1 /\ s = s2 /\ f' = f2).
  Proof.
    intros Hred Hprim.
    apply local_frame_lfilled_prim_step_split_reduce_r with (es1 := es1) (es2:=es2) (j:=0) (lh:= LH_base [] []) in Hprim;auto.
    destruct Hprim as [[e' [f'' [LI' Hprim]]]|[lh' [Hlh' HH]]].
    destruct Hprim as [Hprim [-> [-> Hfill]]].
    { left. eexists _,_. split.  apply Hprim. repeat split;eauto.
      apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;subst.
      erewrite app_nil_l; erewrite app_nil_r. auto. }
    { right. simplify_eq. eexists. eauto. }
    cbn. rewrite app_nil_r. rewrite eqseqE. apply eq_refl.
  Qed.
  
End prim_step_split_properties.
