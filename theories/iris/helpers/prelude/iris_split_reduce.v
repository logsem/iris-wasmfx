From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm Require Export stdpp_aux.
Require Export iris_reduce_properties.

Set Bullet Behavior "Strict Subproofs".

Ltac solve_prim_step_split_reduce_r (* Heqf0 *) :=
  lazymatch goal with
    | H : [] = _ ++ _ |- _ =>
  lazymatch goal with
  | _ : length ?objs < _ |- _ =>
      left ; subst ;
      apply Logic.eq_sym, app_eq_nil in H as [? ?] ;
      exists objs ; subst ; rewrite app_nil_r ;
      repeat split => //= ; (* rewrite Heqf0; *)
                     (try by econstructor);
                     try by econstructor; econstructor
  end
  end.


Section split_reduce_properties.
  
  Let reducible := @iris.program_logic.language.reducible wasm_lang.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.

  
  Lemma prim_step_split_reduce_r (es1 es2 es' : list administrative_instruction) σ σ' obs efs :
    iris.to_val es1 = None -> 
    prim_step (es1 ++ es2) σ obs es' σ' efs ->
    (exists es'', es' = es'' ++ es2 /\ prim_step es1 σ obs es'' σ' efs) \/
      (exists n m lh, lfilled 0 (LH_base (take n es1)
                                    (drop m (es1 ++ es2)))
                         [AI_trap] es' /\ lfilled 0 lh [AI_trap] es1 ∧ σ' = σ). 
  Proof.
    intros Hes1 Hstep. 
    cut (forall n, length es' < n ->
              (exists es'', es' = es'' ++ es2 /\ prim_step es1 σ obs es'' σ' efs) \/
                (exists n m lh, n <= length es1 /\ m <= length (es1 ++ es2) /\
                             lfilled 0 (LH_base (take n es1)
                                                (drop m (es1 ++ es2)))
                                     [AI_trap] es' /\ lfilled 0 lh [AI_trap] es1 ∧ σ'=σ)). 
    { intro Hn ; assert (length es' < S (length es')) as Hlen ; first lia.
      destruct (Hn (S (length es')) Hlen) as [ Hl | (n0 & m & lh & _ & _ & ? & ? & ?) ].
      by left. right ; exists n0, m, lh. 
      repeat split => //=. } 
    intros len Hlen.
    generalize dependent es' ; generalize dependent es1 ; generalize dependent es2.
    induction len ; intros es2 es1 Hes1 es' Hstep Hlen ; first lia.
    unfold prim_step, iris.prim_step in Hstep.
    destruct σ as [[[??]?]?] ;
      destruct σ' as [[[??]?]?] ;
      destruct Hstep as (Hstep & -> & ->).
    remember (es1 ++ es2) as es.
    remember {| f_locs := l ; f_inst := i |} as f.
    remember {| f_locs := l0 ; f_inst := i0 |} as f0.
    induction Hstep.
    destruct H.
    all: repeat (destruct es1 ; first (by inversion Heqes ; subst ; try destruct v; try destruct v1,v2; try destruct v; try destruct v0; inversion Hes1)) ;
      inversion Heqes.
    all: try (rewrite Heqf in Heqf0; inversion Heqf0; subst).
    all: try solve_prim_step_split_reduce_r.
    all: try (left; destruct (first_non_value _ Hes1) as (vs1 & e1 & es'1 & Hvs1 & He1 & Hes'1);
      rewrite Hes'1 in Heqes; rewrite <- app_assoc in Heqes;
              rewrite <- app_comm_cons in Heqes;
              try (repeat rewrite cat_app in Heqes; rewrite (separate1 (AI_ref_cont _)) app_assoc in Heqes);
      apply first_values in Heqes as (<- & <- & Hnil) => //=;
      try (by destruct He1; destruct e1 => //=; destruct b);  subst; try apply const_list_concat; try apply v_to_e_is_const_list;
      destruct es'1, es2 => //;
      eexists _; repeat split => //=; [by rewrite app_nil_r |
      rewrite Hes'1; try rewrite -app_assoc; try (by econstructor); try by apply r_simple; econstructor]).
    - destruct ref.
      all: destruct es1; first (by inversion Heqes ; subst ; inversion Hes1).
      all: inversion H2.
      all: solve_prim_step_split_reduce_r.
      all: constructor.
      exfalso; by eapply H.
      fold (AI_const (VAL_ref (VAL_ref_func f))).
      2: fold (AI_const (VAL_ref $ VAL_ref_cont f)).
      3: fold (AI_const (VAL_ref (VAL_ref_exn e t))).
      all: by apply rs_ref_is_null_false.
    - destruct es1. subst. destruct a ; try by inversion H.
      destruct b ; try by inversion H. inversion H2. subst.
      solve_prim_step_split_reduce_r.
    - right. exists 0, (length (a :: es1 ++ es2)). rewrite take_0. rewrite drop_all.
      destruct (first_non_value _ Hes1) as (vs1 & e1 & es'1 & Hvs1 & He1 & Hes'1).
      unfold lfilled, lfill in H0.
      destruct lh => //; fold lfill in H0.
      all: destruct (const_list l) eqn:Hl1 => //.
      2-3: destruct (lfill _ _ _) eqn:Hfill => //.
      all: move/eqP in H0.
      all: rewrite Hes'1 in H0.
      all: rewrite (separate1 e1) in H0. 
      all: repeat rewrite -app_assoc in H0.
      all: apply first_values in H0 as (-> & -> & <-) => //=. 
      all: try by destruct He1; destruct e1 => //=; destruct b => //=.
      + exists (LH_base l es'1). repeat split => //=. lia.
        unfold lfilled, lfill; subst; rewrite Hl1 Hes'1. done.
      + exists (LH_handler l l1 lh es'1). repeat split => //=. lia.
        unfold lfilled, lfill; fold lfill; subst; rewrite Hl1 Hfill Hes'1 //.
      + exists (LH_prompt l l1 l2 lh es'1). repeat split => //=. lia.
        unfold lfilled, lfill; fold lfill; subst; rewrite Hl1 Hfill Hes'1 //.
    - unfold lfilled, lfill in H.
      destruct lh; fold lfill in H.
      1-2: destruct k => //.
      all: destruct (const_list l1) eqn:Hl1 => //.
      2-4: destruct (lfill _ _ _) eqn:Hfill => //.
      all: move/eqP in H; subst les.
      + unfold lfilled, lfill in H0.
        rewrite Hl1 in H0. move/eqP in H0; subst les'.
        destruct l1.
        * destruct (separate_last l2) as [[??]|] eqn:Hlast; last first.
          -- apply separate_last_None in Hlast as ->.
             rewrite app_nil_l app_nil_r in H.
             rewrite app_nil_l app_nil_r.
             rewrite app_nil_l app_nil_r in Hlen.
             by apply IHHstep. 
          -- apply separate_last_spec in Hlast as ->.
             destruct (separate_last es2) as [[??]|] eqn:Hlast; last first.
             ++ apply separate_last_None in Hlast as ->.
                left. exists (es' ++ l1 ++ [a0]).
                repeat split => //=.
                by rewrite app_nil_r. rewrite app_nil_r in H.
                rewrite H.
                apply (r_label (es:=es) (es':=es') (k:=0)
                         (lh:=LH_base [] (l1 ++ [a0]))).
                by subst. unfold lfilled, lfill => //=.
                unfold lfilled, lfill => //=. 
             ++ apply separate_last_spec in Hlast as ->.
                simpl in H. rewrite separate1 in H.
                repeat rewrite app_assoc in H.
                apply app_inj_tail in H as [Heqes ->].
                assert (prim_step ((a :: es1) ++ l2) (s,l,i) [] (es' ++ l1)
                          (s',l0,i0) []) as Hstep'.
                { repeat split => //=.
                  simpl in Heqes. rewrite Heqes.
                  apply (r_label (es:=es) (es':=es') (k:=0) (lh:=LH_base [] l1)) ;
                    try by unfold lfilled, lfill ; simpl.
                  by subst. } 
                assert (length (es' ++ l1) < len) as Hlen'.
                { simpl in Hlen. repeat rewrite length_app /= in Hlen.
                  rewrite length_app. lia. }
                destruct (IHlen l2 _ Hes1 (es' ++ l1) Hstep' Hlen')
                  as [(es'' & Heq & Hred) | (n & m & lh & Hn & Hm & Hfill & Hcontext)].
                ** left. 
                   exists es''. repeat split => //=.
                   rewrite app_assoc ; rewrite Heq.
                   by rewrite app_assoc. 
                ** right. exists n, m.
                   unfold lfilled, lfill; fold lfill.
                   unfold lfilled, lfill in Hfill.
                   destruct (const_list (take n (a :: es1))) => //=. 
                   move/eqP in Hfill ; rewrite app_assoc Hfill.
                   rewrite <- app_assoc. rewrite <- (app_assoc [AI_trap]).
                   exists lh.
                   repeat split => //=. do 2 rewrite length_app. simpl in Hm.
                   rewrite length_app in Hm. lia.
                   cut (forall es0, m <= length es0 -> drop m es0 ++ [a0] =
                                                  drop m (es0 ++ [a0])).
                   intro Hdrop. rewrite (Hdrop ((a :: es1) ++ l2) Hm).
                   rewrite <- app_assoc. rewrite app_comm_cons. done.
                   clear Hm Hfill.
                   induction m ; intros es0 Hm => //=.
                   destruct es0 ; first by inversion Hm.
                   simpl. apply IHm. simpl in Hm ; lia. 
        * inversion H; subst.
          simpl in Hl1; remove_bools_options.
(*          edestruct IHlen as [(es'' & Hes' & Hstep') | (n & m & lh & Hn & Hm & Htrap & Htrap' & Hstate)].
          3:{ instantiate (1 := l1 ++ es' ++ l2).
              simpl in Hlen. lia. }
          2:{ repeat split => //.
              eapply r_label. exact Hstep.
              instantiate (3 := LH_base l1 l2).
              instantiate (3 := 0).
              all: unfold lfilled, lfill.
              rewrite app_assoc.
              all: rewrite H2 => //. }
          apply to_val_cat_None2 => //. *)
          apply to_val_cons_None_inv in Hes1 as [?| -> ] => //.
          2:{ destruct l1; last by inversion H3; subst.
              destruct es; first by empty_list_no_reduce.
              inversion H3; subst.
              destruct es; first by exfalso; eapply AI_trap_irreducible.
              clear IHHstep.
              edestruct trap_reduce_length as (n1 & n2 & (Hlen1 & Hn1 & Hn2) & Hes' & Hσ).
              2: exact Hstep.
              instantiate (1 := a :: es).
              instantiate (1 := []).
              apply/lfilledP; constructor => //.
              inversion Hσ; subst.
              right.
              destruct n1; last by simpl in Hn1; lia.
              move/lfilledP in Hes'. inversion Hes'; subst.
              simpl in Hlen1.
              destruct n2; first lia.
              simpl. simpl in Hn2.
              exists 1, (S $ S $ S n2), (LH_base [a0] []).
              repeat split => //=; last first.
              apply/lfilledP; constructor => //.
              simpl. by rewrite H0.
              unfold lfilled, lfill => //=.
              rewrite H0 => /=.
              rewrite drop_app_le.
              done. lia. rewrite length_app. lia. lia.

              } 
(*
          
          -- destruct a0 => //.
             destruct b => //. 
             all: unfold iris.to_val in Hes1.
             all: simpl in Hes1.
             all: rewrite merge_prepend in Hes1.
             all: unfold iris.to_val in Heqtv.
             all: destruct (merge_values _) eqn:Hmerge => //.
             all: symmetry in Heqtv; inversion Heqtv ; subst.
             all: simpl in Hes1.
             all: destruct v ; first by inversion Hes1.
             all: assert (to_val es1 = Some trapV) as Htrap;
               first by unfold to_val, iris.to_val ; rewrite Hmerge.
             all: apply to_val_trap_is_singleton in Htrap as ->.
             all: destruct l1 ; last by inversion H3; subst.
             all: destruct es ; first by empty_list_no_reduce.
             all: inversion H3; subst. 
             all: right.
             all: remember (AI_trap :: es) as es0.
             all: clear IHHstep IHlen.
             all: eexists 1.
             all: simpl.
             all: cut (forall n, (length es0 < n ->
                        exists m, 1 <= 2
                             /\ m <= S (S (length (es ++ l2)%list))
                             /\ lfilled 0
                                 (LH_base [AI_basic (BI_const v0)]
                                    (drop m ([AI_basic (BI_const v0) ; AI_trap]
                                               ++ (es ++ l2))))
                                 [AI_trap] (AI_basic (BI_const v0) :: (es' ++ l2)%list)
                             /\ (s', l0, i0) = (s, l, i)
                             /\ opsem.reduce s
                                            {| f_locs := l ; f_inst := i |}
                                            [AI_basic (BI_const v0); AI_trap] s
                                            {| f_locs := l ; f_inst := i |} [AI_trap] /\
                               ([] : seq.seq administrative_instruction) = [] /\
                               ([] : seq.seq administrative_instruction) = [])).
          { intro Hn. assert (length es0 < S (length es0)) ; first lia.
            destruct (Hn _ H0) as (m & Hs1 & Hs2 & Hs3 & Hs4 & Hs5 & Hs6 & Hs7).
            exists m. repeat split => //=. exists (LH_base [AI_basic (BI_const v0)] []).
            unfold lfilled, lfill => //=. }
          intros len' Hlen'. clear H4 Hes1 Hbef Ha Heqtv Heqes H Hmerge.
          generalize dependent es0. generalize dependent es.
          generalize dependent es'. generalize dependent aft.
          induction len' ; intros aft es' Hlen es es0 Heqes0 Hstep Hlen' ; first lia.
          induction Hstep ; try by inversion Heqes0.
          { destruct H ; try by inversion Heqes0.
            destruct vs ; inversion Heqes0.
            rewrite H4 in H. simpl in H ; false_assumption.
            destruct vs ; inversion Heqes0.
            rewrite H4 in H ; simpl in H ; false_assumption.
            inversion Heqes0. rewrite H1 in H ; simpl in H ; false_assumption.
            exists (2 + length es).
            repeat split => //=. lia. rewrite length_app. lia.
            unfold lfilled, lfill. simpl.
            rewrite drop_app. rewrite Nat.sub_diag.
            rewrite drop_all. done.
            rewrite Heqf in Heqf0 ; by inversion Heqf0.
            apply r_simple. apply (rs_trap (lh := LH_base [AI_basic (BI_const v0)] [])).
            intro Habs ; inversion Habs. unfold lfilled, lfill => //=. }
          destruct ves ; inversion Heqes0.
          rewrite H10 in H1. cut (const_list (AI_trap :: ves) = true).
          intro Habs ; simpl in Habs ; false_assumption.
          rewrite H1 ; by apply v_to_e_is_const_list.
          destruct ves ; inversion Heqes0.
          rewrite H6 in H1. cut (const_list (AI_trap :: ves) = true).
          intro Habs ; simpl in Habs ; false_assumption.
          rewrite H1 ; by apply v_to_e_is_const_list.
          unfold lfilled, lfill in H.
          destruct k.
          { destruct lh as [bef0 aft0 |] ; last by false_assumption.
            remember (const_list bef0) as b eqn:Hbef0 ; destruct b ; last by false_assumption.
            move/eqP in H. rewrite Heqes0 in H.
            unfold lfilled, lfill in H0. rewrite <- Hbef0 in H0.
            move/eqP in H0. rewrite H0.
            destruct bef0. {
              destruct aft0. {
                rewrite app_nil_l app_nil_r in H. subst.
                rewrite app_nil_l app_nil_r.
                apply IHHstep => //=. simpl in Hlen.
                repeat rewrite length_app in Hlen.
                rewrite length_app. lia. }
              clear IHHstep. destruct es.
              { destruct es0 ; first by empty_list_no_reduce.
                inversion H. apply Logic.eq_sym, app_eq_nil in H3 as [_ Habs].
                inversion Habs. }
              rewrite H in Heqes0.
              get_tail a0 es ys y Hy. rewrite Hy in H.
              get_tail a aft0 zs z Hz ; rewrite Hz in H.
              rewrite app_comm_cons in H. do 2 rewrite app_assoc in H.
              apply app_inj_tail in H as [Heq Hyz]. simpl in Heq.
              assert (reduce s f (es0 ++ zs) s' f' (es' ++ zs)).
              apply (r_label (es:=es0) (es':=es') (k:=0) (lh:=LH_base [] zs)) ;
                try done ;
                by unfold lfilled, lfill => //=.
              assert (length (es0 ++ zs) < len').
              rewrite Heqes0 in Hlen'. rewrite Hz in Hlen'. simpl in Hlen'.
              rewrite app_assoc in Hlen'. rewrite length_app in Hlen'. simpl in Hlen'.
              rewrite Nat.add_1_r in Hlen'. by apply Nat.succ_lt_mono.
              assert (length ([AI_basic (BI_const v0)] ++ (es' ++ zs)%SEQ ++ (z :: aft)%SEQ)%list < S len).
              subst les'. rewrite Hz in Hlen.
              repeat rewrite length_app in Hlen.
              repeat rewrite length_app.
              simpl in Hlen.
              simpl.
              lia.
              destruct (IHlen' (z :: aft) _ H2 ys (es0 ++ zs) (Logic.eq_sym Heq) H H1) as
                (m & Hn & Hm & Hfill & Hσ & Hred & _ & _).
              unfold lfilled, lfill in Hfill. simpl in Hfill.
              move/eqP in Hfill. simpl. rewrite (app_comm_cons es) Hy Hz Hyz.
              exists m. repeat split => //=.
              { replace (ys ++ (z :: aft)) with ((ys ++ [z]) ++ aft) in Hm ;
                  last by rewrite <- app_assoc.
                rewrite <- Hyz in Hm. rewrite <- Hy in Hm. simpl in Hm. lia. }
              unfold lfilled, lfill => //=. do 2 rewrite <- app_assoc => //=.
              rewrite app_assoc. rewrite Hfill. rewrite <- app_assoc => //=. }
            inversion H.
            rewrite <- H2 in Hbef0 ; simpl in Hbef0 ; inversion Hbef0. }
          { fold lfill in H. destruct lh ; first by false_assumption.
            remember (const_list l1) as b eqn:Hl1 ; destruct b ; last by false_assumption.
            remember (lfill k lh es0) as lfilledk ;
              destruct lfilledk ; last by false_assumption.
            move/eqP in H.
            rewrite Heqes0 in H. destruct l1 ; inversion H.
            rewrite <- H2 in Hl1 ; simpl in Hl1 ; inversion Hl1. }
          { simplify_eq. }
          { simplify_eq. }
          { simplify_eq. } } *)
        clear IHHstep.
        assert (prim_step (es1 ++ es2) (s, l, i) [] (l1 ++ es' ++ l2)
                          (s', l0, i0) []).
        { repeat split => //=.
          apply (r_label (es:=es) (es':=es') (k:=0) (lh:=LH_base l1 l2)) ;
            try by unfold lfilled, lfill ; rewrite H2 ; try rewrite H3.
          by subst. }
        assert (length (l1 ++ es' ++ l2) < len).
        { simpl in Hlen. by apply Nat.succ_lt_mono. }
        edestruct IHlen (* (IHlen es2 es1 H4 (l1 ++ es' ++ l2) H2 H5) *)
          as [(es'' & Heq & Hred) | (n & m & lh & Hn & Hm & Hfill & Hcontext & Hσ)].
        exact H4. exact H5. exact H6.
          -- left. exists (a0 :: es''). repeat split => //=. by rewrite Heq.
             apply (r_label (es:= es1) (es':=es'') (k:=0) (lh:=LH_base [a0] [])).
             by destruct Hred as (? & _ & _).
             unfold lfilled, lfill. simpl. subst. rewrite H0 => //=.
             by rewrite app_nil_r.
             unfold lfilled, lfill. simpl ; subst ; rewrite H0 => //=.
             by rewrite app_nil_r. 
          -- right. exists (S n), (S m). 
             unfold lfilled, lfill; fold lfill.
             unfold lfilled, lfill in Hfill.
             subst. 
             simpl. rewrite H0.
             destruct (const_list (take n es1)) => //.
             simpl. move/eqP in Hfill.
             move/lfilledP in Hcontext.
             inversion Hcontext; subst.
             exists (LH_base (a0 :: vs) es'0).
             2: eexists (LH_handler (a0 :: bef) hs lh' aft).
             3: eexists (LH_prompt (a0 :: bef) ts hs lh' aft).
             all: repeat split => //=.
             all: try by simpl in Hn; lia.
             all: try by simpl in Hm; lia.
             all: try by rewrite Hfill.
             all: try by rewrite H0 H7 /= //.
             all: rewrite H0 H7 /=.
             all: move/lfilledP in H8.
             all: unfold lfilled in H8.
             all: destruct (lfill _ _ _) => //.
             all: move/eqP in H8; by subst.
      + clear IHHstep. 
        destruct (first_non_value _ Hes1) as (vs & e & ult & Hvs & He & Hult).
        rewrite Hult in H. rewrite <- app_assoc in H.
        rewrite <- app_comm_cons in H.
        apply first_values in H as (Hvsl1 & Hlab & Hlast) => //= ; try by left.
        2: by destruct He; destruct e => //; destruct b.
        unfold lfilled, lfill in H0 ; fold lfill in H0.
        rewrite Hl1 in H0.
        destruct (lfill k lh es') eqn:Hfill' => //.  
        move/eqP in H0; subst les'.
        left ; exists (l1 ++ AI_label n l2 l5 :: ult).
        repeat split => //=.
        rewrite <- app_assoc. rewrite <- app_comm_cons. by rewrite Hlast.
        rewrite Hult. rewrite Hlab. rewrite Hvsl1.
        apply (r_label (es:=es) (es':=es') (k:=S k) (lh:=LH_rec l1 n l2 lh ult)) ;
          first (by subst) ;
          unfold lfilled, lfill ; fold lfill ; rewrite Hl1.
        by rewrite Hfill.
        by rewrite Hfill'.
      + clear IHHstep. 
        destruct (first_non_value _ Hes1) as (vs & e & ult & Hvs & He & Hult).
        rewrite Hult in H. rewrite <- app_assoc in H.
        rewrite <- app_comm_cons in H.
        apply first_values in H as (Hvsl1 & Hlab & Hlast) => //= ; try by left.
        2: by destruct He; destruct e => //; destruct b.
        unfold lfilled, lfill in H0 ; fold lfill in H0.
        rewrite Hl1 in H0.
        destruct (lfill k lh es') eqn:Hfill' => //.  
        move/eqP in H0; subst les'.
        left ; exists (l1 ++ AI_handler l2 l5 :: ult).
        repeat split => //=.
        rewrite <- app_assoc. rewrite <- app_comm_cons. by rewrite Hlast.
        rewrite Hult. rewrite Hlab. rewrite Hvsl1.
        apply (r_label (es:=es) (es':=es') (k:=k) (lh:=LH_handler l1 l2 lh ult)) ;
          first (by subst) ;
          unfold lfilled, lfill ; fold lfill ; rewrite Hl1.
        by rewrite Hfill.
        by rewrite Hfill'.
      + clear IHHstep. 
        destruct (first_non_value _ Hes1) as (vs & e & ult & Hvs & He & Hult).
        rewrite Hult in H. rewrite <- app_assoc in H.
        rewrite <- app_comm_cons in H.
        apply first_values in H as (Hvsl1 & Hlab & Hlast) => //= ; try by left.
        2: by destruct He; destruct e => //; destruct b.
        unfold lfilled, lfill in H0 ; fold lfill in H0.
        rewrite Hl1 in H0.
        destruct (lfill k lh es') eqn:Hfill' => //.  
        move/eqP in H0; subst les'.
        left ; exists (l1 ++ AI_prompt l2 l3 l6 :: ult).
        repeat split => //=.
        rewrite <- app_assoc. rewrite <- app_comm_cons. by rewrite Hlast.
        rewrite Hult. rewrite Hlab. rewrite Hvsl1.
        apply (r_label (es:=es) (es':=es') (k:=k) (lh:=LH_prompt l1 l2 l3 lh ult)) ;
          first (by subst) ;
          unfold lfilled, lfill ; fold lfill ; rewrite Hl1.
        by rewrite Hfill.
        by rewrite Hfill'.
  Qed.

  
  Lemma reduce_ves: forall v es es' σ σ' efs obs,
      reducible es σ ->
      prim_step ([AI_const v] ++ es) σ obs es' σ' efs ->
      (es' = [AI_const v] ++ drop 1 es' /\ prim_step es σ obs (drop 1 es') σ' efs)
      \/ (exists lh lh', lfilled 0 lh [AI_trap] es' /\ lfilled 0 lh' [AI_trap] es /\ σ = σ'). 
  Proof.
    cut (forall n v es es' σ σ' efs obs,
            length es < n ->
            reducible es σ ->
            prim_step ([AI_const v] ++ es) σ obs es' σ' efs ->
            (es' = [AI_const v] ++ drop 1 es' /\
               prim_step es σ obs (drop 1 es') σ' efs)
            \/ (exists lh lh', lfilled 0 lh [AI_trap] es' /\
                           lfilled 0 lh' [AI_trap] es /\ σ = σ')).
    { intros H v es es' σ σ' efs obs. apply (H (S (length es)) v es). lia. } 
    intro len. induction len.
    { intros v es es' σ σ' efs obs Habs ; inversion Habs. }
    intros v es es' σ σ' efs obs Hlen Hes Hves.
    destruct Hes as (obs0 & es0 & σ0 & efs0 & H).
    unfold prim_step, iris.prim_step in Hves.
    destruct σ as [[??]?].
    destruct σ' as [[??]?]. 
    destruct Hves as (Hred & Hobs & Hefs).
    remember ([AI_const v] ++ es)%list as ves.
    remember {| f_locs := l ; f_inst := i |} as f.
    remember {| f_locs := l0 ; f_inst := i0 |} as f0.
    unfold language.prim_step, wasm_lang, iris.prim_step in H.
    destruct σ0 as [[[??]?]?] ; destruct H as (Hred0 & Hobs0 & Hefs0).
    induction Hred.
    destruct H.
    43:{ right. exists (LH_base [] []).
         move/lfilledP in H0.
         inversion H0; subst.
         all: (destruct vs + destruct bef); first by destruct v; try destruct v.
         all: simpl in H1; remove_bools_options.
         inversion H5; subst.
         2,3: inversion H6; subst.
         exists (LH_base vs es').
         2: eexists (LH_handler bef hs lh' aft).
         3: eexists (LH_prompt bef ts hs lh' aft).
         all: inversion Heqf0; subst.
         all: repeat split => //.
         all: apply/lfilledP.
         all: constructor => //.  } 
    83:{ move/lfilledP in H.
         move/lfilledP in H0.
         inversion H; subst; inversion H0; subst.
         - destruct vs.
           + destruct es1 ; first by empty_list_no_reduce.
             inversion H5; subst.
             destruct es'0.
             * rewrite cats0. rewrite cats0 in IHHred.
                repeat rewrite cats0 /=.
                rewrite cats0 in Hred0.
                apply IHHred => //.
             * clear IHHred. destruct (to_val es1) eqn:Htv.
               -- destruct v0.
                  ++ exfalso ; values_no_reduce.
                     rewrite const_const => //=.
                     apply to_val_const_list in Htv => //.
                  ++ apply to_val_trap_is_singleton in Htv as ->.
                     lazymatch goal with
                     | _ : reduce s ?f ?es s' ?f' es' |- _ => remember f as ff; remember es as estrap ; remember f' as ff'
                     end .
                     right.
                     exists (LH_base [] (a :: es'0)), (LH_base [] (a :: es'0)).
                     induction Hred.
                     destruct H2.
                     all: try by inversion Heqestrap.
                     all: try by do 3 destruct vs => //.
                     all: try by do 3 destruct ves => //. 
                     ** move/lfilledP in H3. inversion H3; subst.
                        all: try by destruct v; try destruct v; do 3 destruct bef => //.
                        destruct vs; first by destruct v; try destruct v.
                        destruct vs; last by destruct vs; inversion H10.
                        inversion H10; subst.
                        split ; unfold lfilled, lfill => //=.
                        split => //.
                        inversion Heqff'; subst. done.
                     ** move/lfilledP in H2; move/lfilledP in H3.
                        inversion H2; subst; inversion H3; subst.
                        all: try by destruct v; try destruct v; do 3 destruct vs => //.
                        all: try by destruct v; try destruct v; do 3 destruct bef => //.
                        destruct vs.
                        --- destruct es; first by empty_list_no_reduce.
                            destruct es.
                            +++ exfalso; eapply values_no_reduce.
                                exact Hred.
                                inversion H10; subst.
                                rewrite /= const_const //.
                            +++ inversion H10; subst.
                                destruct es, es'1 => //=.
                                rewrite cats0.
                                apply IHHred => //.
                                constructor => //.
                        --- inversion H10.
                            destruct vs; last by inversion H11; destruct vs, es, es'1 => //; empty_list_no_reduce.
                            destruct es; first by empty_list_no_reduce.
                            inversion H11; subst. destruct es, es'1 => //.
                            apply AI_trap_irreducible in Hred => //.
                  ++ exfalso. unfold to_val, iris.to_val in Htv.
                     apply reduce_val_false in Hred;[done|].
                     unfold iris.to_val => /=.
                     rewrite merge_prepend.
                     destruct (merge_values _) => //.
                     inversion Htv => //=. destruct v => //.
                     destruct v => //.
                  ++ exfalso. unfold to_val, iris.to_val in Htv.
                     apply reduce_val_false in Hred;[done|].
                     unfold iris.to_val => /=.
                     rewrite merge_prepend.
                     destruct (merge_values _) => //.
                     inversion Htv => //=. destruct v => //.
                     destruct v => //.
                  ++ exfalso. unfold to_val, iris.to_val in Htv.
                     apply reduce_val_false in Hred;[done|].
                     unfold iris.to_val => /=.
                     rewrite merge_prepend.
                     destruct (merge_values _) => //.
                     inversion Htv => //=. destruct v => //.
                     destruct v => //. 
               -- edestruct prim_step_split_reduce_r as
                    [ (es'' & H01 & H2) | (n & m & lh & H01 & H2 & Hσ) ].
                  exact Htv. unfold prim_step.
                  instantiate (5 := (_, _, _)).
                  instantiate (8 := (_, _, _)).
                  simpl. split; first exact Hred0. split => //.
                  ++ subst.
                     edestruct IHlen as [[Hdrop Hstep] | (lh & lh' & Hfill & Hfill' & Hσ)].
                     2:{ unfold reducible, language.reducible.
                         repeat eexists.
                         unfold language.prim_step. simpl.
                         exact H2. }
                     rewrite length_app /= in Hlen. lia.
                     unfold prim_step. instantiate (5 := (_,_,_)) => /=.
                     split; first exact Hred. split => //.
                     ** left. repeat split => //=.
                        rewrite Hdrop. rewrite <- app_assoc.
                        simpl. rewrite drop_0 //.
                        eapply r_label.
                        destruct Hstep as (Hres & _ & _); exact Hres.
                        instantiate (1 := LH_base [] (a :: es'0)).
                        instantiate (1 := 0).
                        unfold lfilled, lfill => //=.
                        unfold lfilled, lfill => //=.
                        rewrite Hdrop => //=.
                     ** right.
                        move/lfilledP in Hfill.
                        move/lfilledP in Hfill'.
                        inversion Hfill; subst.
                        exists (LH_base vs (es'1 ++ a :: es'0)).
                        2: eexists (LH_handler bef hs lh'0 (aft ++ a :: es'0)).
                        3: eexists (LH_prompt bef ts hs lh'0 (aft ++ a :: es'0)).
                        all: inversion Hfill'; subst.
                        all: eexists.
                        all: repeat split => //=.
                        all: unfold lfilled, lfill; fold lfill => //=.
                        all: try rewrite /= H3.
                        all: try rewrite /= H6.
                        all: try rewrite -cat_app -catA //.
                        all: try by move/lfilledP in H6; unfold lfilled in H6; destruct (lfill _ _ _) => //; move/eqP in H6; subst; rewrite -catA //.
                        --- instantiate (1 := LH_base vs0 (es' ++ a :: es'0)).
                            rewrite /= H6 -cat_app -catA //.
                        --- instantiate (1 := LH_handler bef hs lh'0 (aft ++ a :: es'0)).
                            rewrite /= H6.
                            move/lfilledP in H7.
                            unfold lfilled in H7.
                            destruct (lfill _ _ _) => //.
                            move/eqP in H7; subst l2.
                            rewrite -catA //.
                        --- instantiate (1 := LH_prompt bef ts hs lh'0 (aft ++ a :: es'0)).
                            rewrite /= H6.
                            move/lfilledP in H7. unfold lfilled in H7.
                            destruct (lfill _ _ _) => //.
                            move/eqP in H7; subst l2.
                            rewrite -catA //.
                        --- instantiate (1 := LH_base vs (es' ++ a :: es'0)).
                            rewrite /= H7 -cat_app -catA //.
                        --- instantiate (1 := (LH_handler bef0 hs0 lh'1 (aft0 ++ a :: es'0))).
                            rewrite /= H7. move/lfilledP in H8.
                            unfold lfilled in H8.
                            destruct (lfill _ _ _) => //.
                            move/eqP in H8; subst l2.
                            rewrite -catA //.
                        --- instantiate (1 := (LH_prompt bef0 ts hs0 lh'1 (aft0 ++ a :: es'0))).
                            rewrite /= H7.
                            move/lfilledP in H8.
                            unfold lfilled in H8.
                            destruct (lfill _ _ _) => //.
                            move/eqP in H8; subst l2.
                            rewrite -catA //.
                        --- instantiate (1 := (LH_base vs (es' ++ a :: es'0))).
                            rewrite /= H7 -cat_app -catA //.
                        --- instantiate (1 := (LH_handler bef0 hs0 lh'1 (aft0 ++ a :: es'0))).
                            rewrite /= H7.
                            move/lfilledP in H8. unfold lfilled in H8.
                            destruct (lfill _ _ _) => //.
                            move/eqP in H8; subst l2.
                            rewrite -catA //.
                        --- instantiate (1 := (LH_prompt bef0 ts0 hs0 lh'1 (aft0 ++ a :: es'0))).
                            rewrite /= H7.
                            move/lfilledP in H8. unfold lfilled in H8.
                            destruct (lfill _ _ _) => //.
                            move/eqP in H8; subst l2.
                            rewrite -catA //.
                  ++ right.
                     edestruct lfilled_prepend_append as [? Hfillres].
                     instantiate (1 := [AI_const v]).
                     rewrite /= const_const //.
                     exact H2.
                     edestruct trap_reduce as (lh' & Hfill' & Hσ').
                     exact Hfillres.
                     instantiate (4 := []).
                     rewrite cats0.
                     exact Hred.
                     inversion Hσ'; subst.
                     edestruct lfilled_prepend_append as [? Hres].
                     instantiate (1 := []) => //.
                     exact Hfill'.
                     edestruct lfilled_prepend_append as [? Hres'].
                     instantiate (1 := []) => //.
                     exact H2.
                     do 2 eexists.
                     repeat split => //.
           + clear IHHred. inversion H5; subst.
             simpl in H1; remove_bools_options.
             left. repeat split => //=.
             rewrite drop_0.
             eapply r_label.
             exact Hred.
             instantiate (1 := LH_base vs es'0).
             instantiate (1 := 0).
             apply/lfilledP. constructor => //.
             apply/lfilledP. constructor => //. 
         - destruct vs; first by destruct v; try destruct v; inversion H6.
           simpl in H1; remove_bools_options.
           inversion H6; subst.
           left. repeat split => //=.
           rewrite drop_0. eapply r_label.
           exact Hred.
           instantiate (1 := LH_rec vs n es'0 lh' es'').
           instantiate (1 := S k0).
           apply/lfilledP. constructor => //.
           apply/lfilledP. constructor => //.
         - destruct bef; first by destruct v; try destruct v; inversion H6.
           simpl in H1; remove_bools_options.
           inversion H6; subst.
           left. repeat split => //=.
           rewrite drop_0. eapply r_label.
           exact Hred.
           instantiate (1 := LH_handler bef hs lh' aft).
           instantiate (1 := k).
           apply/lfilledP. constructor => //.
           apply/lfilledP. constructor => //.
         - destruct bef; first by destruct v; try destruct v; inversion H6.
           simpl in H1; remove_bools_options.
           inversion H6; subst.
           left. repeat split => //=.
           rewrite drop_0. eapply r_label.
           exact Hred.
           instantiate (1 := LH_prompt bef ts hs lh' aft).
           instantiate (1 := k).
           apply/lfilledP. constructor => //.
           apply/lfilledP. constructor => //. 
    }                         
                     
    all: try by destruct v; try destruct v; inversion Heqves; subst.
    20, 21: destruct v1, v2; destruct v0, v1.
    all: try subst vs.
      
    all: try (exfalso; clear Hlen IHlen; induction Hred0 as [? ? ? ? H00 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H00 H01 | ];
        first destruct H00 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
        try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by do 4 destruct vs => //);
          do 4 destruct bef => //
        | move/lfilledP in H00; inversion H00; subst;
          try (by do 4 destruct vs => //);
          try (by do 4 destruct bef => //);
          destruct vs;
          first (
              repeat (destruct es; first by inversion Heqves; subst; apply values_no_reduce in Hred0);

              inversion Heqves; subst;
              destruct es => //; apply IHHred0 => //
           )]).
    all: try (clear IHHred0 H00 H01; inversion Heqves; subst => //).
    all: try (destruct vs; last by inversion Heqves; destruct vs, es => //; apply empty_no_reduce in Hred0).
    all: try (destruct vs; last (destruct vs; last by inversion Heqves; destruct vs, es => //; apply empty_no_reduce in Hred0)).
    all: try (induction Hred0 as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
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
              repeat (destruct es; first by inversion Heqves; subst; apply values_no_reduce in Hred0);

              inversion Heqves; subst;
              destruct es, es'1, es'0 => //; apply IHHred0 => // ) 
          ]).
    all: try (clear IHHred0 H02 H03; inversion Heqves; subst => //).
    all: try (destruct vs; last by inversion Heqves; destruct vs, es => //; apply empty_no_reduce in Hred0).
     all: try (induction Hred0 as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
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
              repeat (destruct es; first by inversion Heqves; subst; apply values_no_reduce in Hred0);

              inversion Heqves; subst;
              destruct es, es'1, es'0, es'2 => //; apply IHHred0 => // ) 
            ]).
     all: try (clear IHHred0 H02 H03; inversion Heqves; subst => //).
    - (* block *)
      destruct vs; first by destruct v; try destruct v; inversion Heqves.
      inversion Heqves; subst es.
      exfalso; eapply block_not_enough_arguments_no_reduce.
      exact Hred0. simpl in H; remove_bools_options => //.
      simpl in H0. lia.
    - (* loop *)
      destruct vs; first by destruct v; try destruct v; inversion Heqves.
      inversion Heqves; subst es.
      exfalso; eapply loop_not_enough_arguments_no_reduce.
      exact Hred0. simpl in H; remove_bools_options => //.
      simpl in H0. lia.
    - (* invoke *)
      destruct ves; first by destruct v; try destruct v; inversion Heqves.
      inversion Heqves; subst es.
      destruct vcs => //.
      inversion H1; subst.
      exfalso; eapply invoke_not_enough_arguments_no_reduce_native.
      all: try exact Hred0. exact H. 
      apply v_to_e_is_const_list.
      rewrite v_to_e_length. simpl in H4. lia.
    - (* invoke *)
      destruct ves; first by destruct v; try destruct v; inversion Heqves.
      inversion Heqves; subst es.
      destruct vcs => //.
      inversion H1; subst.
      exfalso; eapply invoke_not_enough_arguments_no_reduce_host.
      all: try exact Hred0. exact H. 
      apply v_to_e_is_const_list.
      rewrite v_to_e_length. simpl in H3. lia.
    - (* try_table *)
      destruct vs; first by destruct v; try destruct v; inversion Heqves.
      inversion Heqves; subst es.
      exfalso; eapply try_table_not_enough_arguments_no_reduce.
      all: try exact Hred0. subst. exact H.
      simpl in H1. remove_bools_options. done.
      simpl in H2. lia.
    - (* throw *)
      destruct ves; first by destruct v; try destruct v; inversion Heqves.
      subst.
      inversion Heqves; subst es.
      destruct vcs => //. inversion H1; subst.
      exfalso; eapply throw_not_enough_arguments_no_reduce.
      all: try exact Hred0. exact H. exact H0.
      apply v_to_e_is_const_list.
      simpl in H2. lia.
    - (* resume *)
      destruct vs.
      + inversion Heqves.
        induction Hred0 as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
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
              repeat (destruct es; first by inversion Heqves; subst; apply values_no_reduce in Hred0);

              inversion Heqves; subst;
              destruct es, es'0 => //; apply IHHred0 => // ) 
        ].
        inversion H11; subst.
        rewrite H8; done.
        inversion H11; subst => //. 
      + subst.
        inversion Heqves; subst es.
        exfalso; eapply resume_not_enough_arguments_no_reduce.
        all: try exact Hred0. exact H0. exact H2.
        simpl in H. remove_bools_options. done.
        simpl in H1. lia.
    - (* suspend *)
      destruct vs; first by destruct v; try destruct v; inversion Heqves.
      subst.
      inversion Heqves; subst es.
      exfalso; eapply suspend_not_enough_arguments_no_reduce.
      all: try exact Hred0. exact H. exact H0.
      apply v_to_e_is_const_list.
      rewrite length_map.
      simpl in H1. lia.
    - (* switch *)
       destruct vs.
      + inversion Heqves.
        induction Hred0 as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
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
              repeat (destruct es; first by inversion Heqves; subst; apply values_no_reduce in Hred0);

              inversion Heqves; subst;
              destruct es, es'0 => //; apply IHHred0 => // ) 
        ].
        inversion H11; subst.
        rewrite H8; done.
        inversion H11; subst => //. 
      + subst.
        inversion Heqves; subst es.
        exfalso; eapply switch_not_enough_arguments_no_reduce.
        all: try exact Hred0. exact H2. exact H3.
        apply v_to_e_is_const_list.
        rewrite length_map. simpl in H4. lia.
    - (* contbind *)
      destruct vs.
      + inversion Heqves.
        induction Hred0 as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
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
              repeat (destruct es; first by inversion Heqves; subst; apply values_no_reduce in Hred0);

              inversion Heqves; subst;
              destruct es, es'0 => //; apply IHHred0 => // ) 
        ].
        inversion H10; subst.
        rewrite H7; done.
        inversion H10; subst => //. 
      + subst.
        inversion Heqves; subst es.
        exfalso; eapply contbind_not_enough_arguments_no_reduce.
        all: try exact Hred0. exact H0. exact H1. exact H3.
        simpl in H. remove_bools_options. done.
        simpl in H2. lia.
    - (* resume_throw *)
      destruct ves.
      + inversion Heqves.
        induction Hred0 as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
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
              repeat (destruct es; first by inversion Heqves; subst; apply values_no_reduce in Hred0);

              inversion Heqves; subst;
              destruct es, es'0 => //; apply IHHred0 => // ) 
        ].
        inversion H15; subst.
        rewrite H4; done.
        inversion H15; subst => //. 
      + subst.
        inversion Heqves; subst es.
        destruct vcs => //. inversion H1; subst.
        exfalso; eapply resume_throw_not_enough_arguments_no_reduce.
        all: try exact Hred0. exact H. exact H0. exact H5.
        apply v_to_e_is_const_list.
        simpl in H2. lia.
Qed.

  




End split_reduce_properties.
