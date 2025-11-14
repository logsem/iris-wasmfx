From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude iris_split_reduce.

Local Definition reducible := @iris.program_logic.language.reducible wasm_lang.
Set Bullet Behavior "Strict Subproofs".

Lemma label_det s f es s' f' es' les les' k lh ws2 f2 es2 nnn:
  (∀ (f f2 f1 : frame) (es2 es1 es : seq.seq administrative_instruction),
    reduce s f es s' f1 es1
    → reduce s f es ws2 f2 es2 → length_rec es < nnn → reduce_det_goal s' f1 es1 ws2 f2 es2 es) ->
  reduce s f es s' f' es' ->
  lfilled k lh es les ->
  lfilled k lh es' les' ->
  reduce s f les ws2 f2 es2 ->
  length_rec les < S nnn ->
  ((∀ (f f2 f1 : frame) (es2 es1 es : seq.seq administrative_instruction),
      reduce s f es s' f1 es1
      → reduce s f es ws2 f2 es2 → length_rec es < nnn → reduce_det_goal s' f1 es1 ws2 f2 es2 es)
   → reduce s f es ws2 f2 es2 → length_rec es < S nnn → reduce_det_goal s' f' es' ws2 f2 es2 es) ->
  reduce_det_goal s' f' les' ws2 f2 es2 les.
Proof.
  move => IHnnn Hred1 H H0 Hred2 Hlen IHHred1.
  (* r_label case. The proof is tedious and relies on cleverly calling the induction
       hypothesis IHnnn. For this, we need to have some term es0 smaller than the original
       es (in terms of length_rec, i.e. number of instructions, including recursively under
       AI_labels and AI_locals). To find this, we first look at whether the lfilled
       statement is at level 0 or at a higher level : *)
  move/lfilledP in H; move/lfilledP in H0.
  inversion H; subst; inversion H0; subst.
  - (* in this case, Hred1 was [ les -> les1 ] with [ les = bef ++ es ++ aft ],
         [ les1 = bef ++ es1 ++ aft ] and [ es -> es1 ]. 
         Hred2 is hypothesis [ les -> es2 ] with nothing known of [ es2 ]. *)
    destruct vs.
    + separate_last es'0; last first.
      * (*  If bef and aft are both empty, induction hypothesis 
                            IHHred1 can be used. *)
        do 2 rewrite /= cats0.
        rewrite /= cats0 in Hred2 Hlen.
        apply IHHred1 => //=. 
      * (* Else, if bef is empty and aft is nonempty, then let us call y the last 
           instruction in les. We have [ les = es ++ ys ++ [y] ]. r_label gives us
           that [ es ++ ys -> es1 ++ ys ], and Hred2 is still [ les -> es2 ].
           Using lemma reduce_append (the append equivalent of reduce_ves), 
           we know es2 ends in y and [ es ++ ys -> take (all but 1) es2 ].
           We can thus apply IHnnn to [ es ++ ys ] (shorter than les since we 
           removed y) *)
        assert (reducible (es ++ l, f) s) as Hred.
        { exists [], (es' ++ l, f'), s', [].
          repeat split => //=.
          apply (r_label (k:=0) (lh:=LH_base [] l) (es:=es) (es':=es')) ;
            unfold lfilled, lfill => //=.
        } 
        assert (prim_step ((es ++ l) ++ [a], f) s
                  [] (es2, f2) ws2 []) as Hstep.
        { repeat split => //=. rewrite -app_assoc. done. } 
        destruct (reduce_append _ _ _ _ _ _ _ _ _ Hred Hstep) as [[ Hes2y Htakestep ]|
                                                               (lh & lh' & Htrap &
                                                                  Htrap' & -> & ->)].
        -- assert (reduce s f (es ++ l) s' f' (es' ++ l)).
           { apply (r_label (k:=0) (lh:=LH_base [] l) (es:=es) (es':=es')) ;
               (try done) ; by unfold lfilled, lfill => //=. }
           destruct Htakestep as (H3 & _ & _).
           destruct f ; destruct f2.
           assert (length_rec (es ++ l) < nnn).
           { do 2 rewrite length_app_rec in Hlen.
             assert (length_rec [a] > 0) ; first by apply length_cons_rec.
             rewrite length_app_rec.
             lia. }
           destruct (IHnnn _ _ _ _ _ _ H2 H3 H5) as (-> &  [[Hes ->] | [[i Hstart] |
                                                        (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & ->)
                                                        ]]).
           ++ repeat split => //. left. subst.
              rewrite /= catA Hes cat_app -Hes2y //. 
           ++ repeat split => //. right ; left.
              exists i. rewrite /= catA.
              apply first_instr_app. done.
           ++ repeat split => //. repeat right.
              exists i1, i2, i3. repeat split => //=.
              rewrite catA. apply first_instr_app => //.
              rewrite catA. apply first_instr_app => //.
              rewrite -(take_drop (length es2 - 1) es2).
              apply first_instr_app => //. 
        -- do 2 rewrite /= catA.
           assert (reduce ws2 f2 (es ++ l) s' f' (es' ++ l)) as Hles.
           { apply (r_label (k:=0) (lh:=LH_base [] l) (es:=es) (es':=es')) => //=.
             unfold lfilled, lfill => //=.
             unfold lfilled, lfill => //=. }
           destruct (trap_reduce _ _ _ _ _ _ _ Htrap' Hles) as (lh''' & Hnew & Hσ').
           inversion Hσ'; subst.
           repeat split => //.
           repeat right.
           exists 0, 0, 0.
           repeat split => //= ; try by try apply first_instr_app; eapply lfilled_implies_starts.
    + (* if bef is nonempty, then we proceed like before, but on the left side.
         Calling v the first value in bef, we know that [ les = v :: bef' ++ es ++ aft ]
         r_label gives us [ bef' ++ es ++ aft -> bef' ++ es1 ++ aft ] and we still
         have Hred2 telling [ les -> es2 ]. Using reduce_ves, we know that es2 starts
         with v and that [ bef' ++ es ++ aft -> drop 1 es2 ]. We can thus apply
         induction hypothesis on [ bef' ++ es ++ aft ], which is indeed shorter than
         les since we removed v *)
      simpl in H1; remove_bools_options.
      assert (reduce s f (vs ++ es ++ es'0) s' f' (vs ++ es' ++ es'0)) as Hles.
      { apply (r_label (k:=0) (lh:=LH_base vs es'0) (es:=es) (es':=es')) => //=.
        unfold lfilled, lfill ; by rewrite H2. 
        unfold lfilled, lfill ; by rewrite H2. }
      assert (reducible (vs ++ es ++ es'0, f) s) as Hred.
      { exists [], (vs ++ es' ++ es'0, f'), s', [].
        repeat split => //=. }
      apply const_const_inv in H1 as [v ->].
      assert (prim_step ([AI_const v] ++ vs ++ es ++ es'0, f)
                      s [] (es2, f2)
                      ws2 []) as Hstep.
    { repeat split => //=. } 
    destruct (reduce_ves _ _ _ _ _ _ _ _ _ Hred Hstep) as [[ Hves2 Hdropstep] |
                                                       ( lh & lh' & Htrap & Htrap' & -> & -> )].
      * assert (reduce s f (vs ++ es ++ es'0) s' f' (vs ++ es' ++ es'0)).
        { apply (r_label (k:=0) (lh:=LH_base vs es'0) (es:=es) (es':=es'))
        ; (try done) ; by unfold lfilled, lfill; rewrite H2. }
      destruct Hdropstep as (H3 & _ & _).
      destruct f ; simpl in H2. destruct f2 ; simpl in H2.
      assert (length_rec (vs ++ es ++ es'0) < nnn).
      { rewrite separate1 in Hlen. repeat rewrite cat_app in Hlen.
        repeat rewrite length_app_rec in Hlen.
        repeat rewrite length_app_rec.
        destruct v; try destruct v; simpl in Hlen; lia. } 
      destruct (IHnnn _ _ _ _ _ _ H1 H3 H5) as (-> & [[Hes ->] | [[i Hstart] |
                                                      (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & ->)
                                               ]]).
        -- repeat split => //. left. 
           subst.
           rewrite separate1. rewrite -cat_app.
           repeat rewrite -catA. rewrite Hes.
           by rewrite Hves2.
        -- repeat split => //. right ; left.
           exists i. rewrite separate1 -cat_app -catA.
           rewrite first_instr_const => //.
           rewrite /= const_const //.
        -- repeat split => //. repeat right.
           exists i1, i2, i3. repeat split => //=.
           rewrite separate1 -cat_app first_instr_const //.
           rewrite /= const_const //.
           rewrite separate1 -cat_app first_instr_const //.
           rewrite /= const_const //.
           rewrite - (take_drop 1 es2).
           rewrite first_instr_const //.
           rewrite Hves2 /= const_const //. 
      * destruct (trap_reduce _ _ _ _ _ _ _ Htrap' Hles) as (lh''' & ? & Hσ').
        inversion Hσ'; subst.
        repeat split => //. 
        repeat right. exists 0,0,0.

        repeat split => //= ; try by try rewrite separate1 -cat_app first_instr_const //; try eapply lfilled_implies_starts; try rewrite /= const_const //.
  - (* in this case, Hred1 was [ les -> les1 ] with 
       [ les = bef ++ AI_label n es0 l :: aft ], [ les1 = bef ++ AI_label n es0 l1 :: aft ],
       [ lfilled k lh es l ], [ lfilled k lh es1 l1 ] and [ es -> es1 ]. We still have
       Hred2 being [ les -> es2 ] with nothing known of es2. *)
    destruct vs.
    + separate_last es''; last first. 
        (* if bef and aft are empty, then Hred2 is [ [AI_label n es0 l] -> es2 ].
             We painstakingly show, by case analysis, that this means es2 is of the
             form [AI_label n es0 l'] with [ l -> l' ].
             Knowing that, and since r_label gives [ l -> l1 ], we can apply the 
             induction hypothesis IHnnn on l, which is shorter than les since there is
             one less AI_label node.
         *)
      * rewrite /= in Hred2.
        lazymatch goal with
        | _ : reduce _ _ ?es _ _ _ |- _ => remember es as ves end.
        induction Hred2.
        inversion H3.
        all: remember Heqves as Heq; clear HeqHeq Heqves; subst.
        all: try by inversion Heq.
        all: try by do 4 destruct vs => //.
        all: try by do 4 destruct vcs => //.
        -- inversion Heq; subst.
           move/lfilledP in H2.
           apply lfilled_const in H2 as [-> Hes] => //.
           exfalso; apply values_no_reduce in Hred1 => //.
        -- inversion Heq; subst.
           inversion H2.
           all: try by do 2 destruct vs => //.
           all: try by do 2 destruct bef => //.
           destruct vs; last by destruct vs, es, es'1 => //; empty_list_no_reduce.
           destruct es; first empty_list_no_reduce.
           inversion H4; destruct es, es'1; subst => //.
           apply AI_trap_irreducible in Hred1 => //.
        -- inversion Heq; subst.
           move/lfilledP in H2. exfalso.
           eapply lfilled_br_and_reduce; try exact H2; try exact H6; try done.
        -- move/lfilledP in H5; inversion H5; subst.
           all: try by do 2 destruct bef => //.
           do 2 destruct vs => //.
        -- move/lfilledP in H3; inversion H3; subst.
           all: try by do 2 destruct bef => //.
           all: move/lfilledP in H4; inversion H4; subst.
           ++ destruct vs.
              ** destruct es0; first empty_list_no_reduce.
                 inversion H5; destruct es0, es'2; subst => //.
                 rewrite /= cats0. rewrite /= cats0 in IHHred1.
                 apply IHHred2 => //.
              ** inversion H5; destruct vs, es0, es'2; subst => //.
           ++ destruct vs; last by destruct vs.
              inversion H5; subst. simpl.
              assert (reduce s f LI s' f' LI0).
              { eapply r_label. exact Hred1. apply/lfilledP. exact H2.
                apply/lfilledP. done. }
              assert (reduce s f LI s'0 f'0 LI2).
              { eapply r_label. exact Hred2. apply/lfilledP. exact H10.
                apply/lfilledP. done. }
              assert (length_rec LI < nnn).
              { rewrite /= /length_rec /= in Hlen.
                unfold length_rec. lia. }
              assert (lfilled 1 (LH_rec [] n es'0 (LH_base [] []) []) LI [AI_label n es'0 LI]).
              { unfold lfilled, lfill => //=. by rewrite app_nil_r. }
              destruct (IHnnn _ _ _ _ _ _ H7 H8 H9)
                as (-> &  [ [Hes ->] | [ [i Hstart] | (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & ->) ]]).
              ** repeat split => //. left. by subst.
              ** repeat split => //. right ; left. exists (i + 1).
                 eapply starts_with_lfilled => //=.
              ** repeat split => //. repeat right.
                 exists (S i1),(S i2),(S i3). repeat split => //=.
                 unfold first_instr => //=.
                 unfold first_instr in Hstart1 ; rewrite Hstart1 => //=.
                 unfold first_instr => //=.
                 unfold first_instr in Hstart2 ; rewrite Hstart2 => //=.
                 unfold first_instr => //=.
                 unfold first_instr in Hstart3 ; rewrite Hstart3 => //=. 
      * (* in the cases where aft is nonempty or bef is nonempty, we proceed exactly
           like in the corresponding cases when k was 0 *)
        assert (reducible (AI_label n es'0 LI :: l, f) s) as Hred.
        { exists [], (AI_label n es'0 LI0 :: l, f'), s', [].
          repeat split => //=.
          apply (r_label (k:=S k0) (lh:=LH_rec [] n es'0 lh' l) (es:=es) (es':=es')) ;
            try by apply/lfilledP; rewrite -(app_nil_l (_ :: _)); constructor.
          destruct f ; destruct f' => //=.
        }
        assert (prim_step ((AI_label n es'0 LI :: l) ++ [a], f) s
                        [] (es2, f2) ws2 []) as Hstep.
        { repeat split => //=. }
        destruct (reduce_append _ _ _ _ _ _ _ _ _ Hred Hstep) as [[ Hes2y Htakestep ]|
                                                            (lh0 & lh'' & Htrap &
                                                             Htrap' & -> & -> )].
        -- assert (reduce s f (AI_label n es'0 LI :: l) s' f'
                       (AI_label n es'0 LI0 :: l)).
           { apply (r_label (k:=S k0) (lh:=LH_rec [] n es'0 lh' l) (es:=es) (es':=es')) ;
               (try done) ; apply/lfilledP; rewrite - (app_nil_l (_ :: _)); constructor => //. } 

           destruct Htakestep as (H2' & _ & _).
           destruct f ; destruct f2.
           assert (length_rec (AI_label n es'0 LI :: l) < nnn).
           { rewrite cat0s cat_app length_app_rec length_app_rec in Hlen.
             assert (length_rec [a] > 0) ; first by apply length_cons_rec.
             rewrite separate1 length_app_rec. lia. }
           destruct (IHnnn _ _ _ _ _ _ H3 H2' H4) as (-> &  [[Hes ->] | [ [i Hstart] |
                                                         (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & ->)
                                                 ]]).
           ++ repeat split => //. left. subst.
              rewrite /= -cat_app separate1 -cat_app catA.
              rewrite separate1 -cat_app in Hes. rewrite Hes.
              rewrite -cat_app in Hes2y.
              rewrite - Hes2y. done.
           ++ repeat split => //. right ; left.
              exists i. simpl.
              rewrite separate1 app_assoc.
              apply first_instr_app => //.
           ++ repeat split => //. repeat right.
              exists i1, i2, i3. repeat split => //=.
              rewrite separate1 app_assoc.
              apply first_instr_app => //.
              rewrite separate1 app_assoc.
              apply first_instr_app => //.
              rewrite - (take_drop (length es2 - 1) es2).
              apply first_instr_app => //. 
        -- assert (reduce ws2 f2 (AI_label n es'0 LI :: l) s' f'
                     (AI_label n es'0 LI0 :: l)) as Hles.
           { apply (r_label (k:=S k0) (lh:=LH_rec [] n es'0 lh' l) (es:=es) (es':=es')) => //=.
             rewrite -(app_nil_l (_ :: _)). apply/lfilledP. constructor => //.
             rewrite -(app_nil_l (_ :: _)). apply/lfilledP. constructor => //. } 
           destruct (trap_reduce _ _ _ _ _ _ _ Htrap' Hles) as (lh''' & ? & Hσ').
           inversion Hσ'; subst.
           repeat split => //. 
           repeat right. 
           exists 0, 0, 0.
           repeat split; try by try rewrite cat0s -cat_app catA; try apply first_instr_app; eapply lfilled_implies_starts.
    + simpl in H1; remove_bools_options.
      assert (reduce s f (vs ++ AI_label n es'0 LI :: es'') s' f'
                (vs ++ AI_label n es'0 LI0 :: es'')) as Hles.
      { apply (r_label (k:=S k0) (lh:=LH_rec vs n es'0 lh' es'') (es:=es) (es':=es')) => //=.
        all: apply/lfilledP; constructor => //. } 
      assert (reducible (vs ++ AI_label n es'0 LI :: es'', f)
                      s) as Hred.
    { exists [], (vs ++ AI_label n es'0 LI0 :: es'', f'), s', [].
      repeat split => //=. }
    apply const_const_inv in H1 as [v ->].
    assert (prim_step ([AI_const v] ++ vs ++ AI_label n es'0 LI :: es'', f)
                      s [] (es2, f2)
                      ws2 []) as Hstep.
    { repeat split => //=.  } 
    destruct (reduce_ves _ _ _ _ _ _ _ _ _ Hred Hstep) as [[ Hves2 Hdropstep] |
                                                       ( lh0 & lh'' & Htrap & Htrap' &
                                                         -> & -> )].
    * destruct Hdropstep as (H2' & _ & _).
      destruct f ; simpl in H2'. destruct f2 ; simpl in H2'.
      assert (length_rec (vs ++ AI_label n es'0 LI :: es'') < nnn).
      { repeat rewrite cat_app in Hlen. rewrite separate1 in Hlen.
        repeat rewrite length_app_rec in Hlen.
        rewrite separate1. repeat rewrite length_app_rec.
        simpl in Hlen. simpl. destruct v; try destruct v; simpl in Hlen; lia. }
      destruct (IHnnn _ _ _ _ _ _ Hles H2' H1) as (-> & [[Hes ->] | [ [i Hstart] |
                                                         (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & ->)
                                                 ]]).
      -- repeat split => //. left.
         subst.
         rewrite separate1 -cat_app -catA Hes Hves2 //.  
      -- repeat split => //. right ; left.
         exists i. rewrite separate1 -cat_app -catA first_instr_const //.
         rewrite /= const_const //.
      -- repeat split => //. repeat right.
         exists i1, i2, i3. repeat split => //=.
         rewrite separate1 -cat_app first_instr_const //.
         rewrite /= const_const //.
         rewrite separate1 -cat_app first_instr_const //.
         rewrite /= const_const //.
         rewrite - (take_drop 1 es2) first_instr_const //.
         rewrite Hves2 /= const_const //.
    * destruct (trap_reduce _ _ _ _ _ _ _ Htrap' Hles) as (lh''' & ? & Hσ').
      inversion Hσ'; subst.
      repeat split => //. 
      repeat right.
      exists 0, 0, 0.
      repeat split => //= ; try by try rewrite separate1 -cat_app first_instr_const; try rewrite /= const_const //; eapply lfilled_implies_starts.
  - (* Handler *)
    destruct bef.
    + separate_last aft; last first. 
        (* if bef and aft are empty, then Hred2 is [ [AI_label n es0 l] -> es2 ].
             We painstakingly show, by case analysis, that this means es2 is of the
             form [AI_label n es0 l'] with [ l -> l' ].
             Knowing that, and since r_label gives [ l -> l1 ], we can apply the 
             induction hypothesis IHnnn on l, which is shorter than les since there is
             one less AI_label node.
         *)
      * rewrite /= in Hred2.
        lazymatch goal with
        | _ : reduce _ _ ?es _ _ _ |- _ => remember es as ves end.
        induction Hred2.
        inversion H3.
        all: remember Heqves as Heq; clear HeqHeq Heqves; subst.
        all: try by inversion Heq.
        all: try by do 4 destruct vs => //.
        all: try by do 4 destruct vcs => //.
        -- inversion Heq; subst.
           move/lfilledP in H2.
           apply lfilled_const in H2 as [-> Hes] => //.
           exfalso; apply values_no_reduce in Hred1 => //.
        -- inversion Heq; subst.
           inversion H2.
           all: try by do 2 destruct vs => //.
           all: try by do 2 destruct bef => //.
           destruct vs; last by destruct vs, es, es'0 => //; empty_list_no_reduce.
           destruct es; first empty_list_no_reduce.
           inversion H4; destruct es, es'0; subst => //.
           apply AI_trap_irreducible in Hred1 => //.
        -- move/lfilledP in H5; inversion H5; subst.
           all: try by do 2 destruct bef => //.
           all: try by do 2 destruct vs => //.
           destruct bef; last by destruct bef.
           inversion H6; subst.
           edestruct trap_reduce as (lh''' & ? & Hσ').
           apply/lfilledP. exact H13.
           eapply r_label.
           exact Hred1.
           apply/lfilledP. exact H2.
           apply/lfilledP. exact H11.
           inversion Hσ'; subst.
           repeat split => //. right. right.
                      
           exists 0, 0, 0.

           repeat split => //=.
           eapply lfilled_implies_starts => //.
           instantiate (1 := LH_handler [] hs lh'0 []).
           apply/lfilledP. rewrite - (app_nil_l [AI_handler _ _]) - (app_nil_r [AI_handler _ _]). constructor => //.
           eapply lfilled_implies_starts => //.
           instantiate (1 := LH_handler [] hs lh''' []).
           apply/lfilledP. rewrite - (app_nil_l [AI_handler _ _]) - (app_nil_r [AI_handler _ _]). constructor => //.
           apply/lfilledP. done.
        -- inversion Heq; subst.
           exfalso. move/lfilledP in H2.
           eapply hfilled_throw_ref_and_reduce.
           3: exact H2. exact Hred1. done.
        -- inversion Heq; subst.
           exfalso. move/lfilledP in H2.
           eapply hfilled_throw_ref_and_reduce.
           3: exact H2. exact Hred1. done.
        -- move/lfilledP in H3; inversion H3; subst.
           all: try by do 2 destruct bef => //.
           all: try by do 2 destruct vs => //. 
           all: move/lfilledP in H4; inversion H4; subst.
           ++ destruct vs.
              ** destruct es0; first empty_list_no_reduce.
                 inversion H5; destruct es0, es'1; subst => //.
                 rewrite /= cats0. rewrite /= cats0 in IHHred1.
                 apply IHHred2 => //.
              ** inversion H5; destruct vs, es0, es'1; subst => //.
           ++ destruct bef; last by destruct bef.
              inversion H5; subst. simpl.
              assert (reduce s f LI s' f' LI0).
              { eapply r_label. exact Hred1. apply/lfilledP. exact H2.
                apply/lfilledP. done. }
              assert (reduce s f LI s'0 f'0 LI2).
              { eapply r_label. exact Hred2. apply/lfilledP. exact H12.
                apply/lfilledP. done. }
              assert (length_rec LI < nnn).
              { rewrite /= /length_rec /= in Hlen.
                unfold length_rec. lia. }
              assert (lfilled 0 (LH_handler [] hs (LH_base [] []) []) LI [AI_handler hs LI]).
              { unfold lfilled, lfill => //=. by rewrite app_nil_r. }
              destruct (IHnnn _ _ _ _ _ _ H7 H8 H9)
                as (-> & [ [Hes ->] | [ [i Hstart] | (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3& ->) ]]).
              ** repeat split => //. left. by subst.
              ** repeat split => //. right ; left. exists (i + 0).
                 eapply starts_with_lfilled => //=.
              ** repeat split => //. repeat right.
                 exists i1,i2,i3. repeat split => //=.
                 unfold first_instr => //=.
                 unfold first_instr in Hstart1 ; rewrite Hstart1 => //=.
                 unfold first_instr => //=.
                 unfold first_instr in Hstart2 ; rewrite Hstart2 => //=.
                 unfold first_instr => //=.
                 unfold first_instr in Hstart3 ; rewrite Hstart3 => //=. 
      * (* in the cases where aft is nonempty or bef is nonempty, we proceed exactly
           like in the corresponding cases when k was 0 *)
        assert (reducible (AI_handler hs LI :: l, f) s) as Hred.
        { exists [], (AI_handler hs LI0 :: l, f'), s', [].
          repeat split => //=.
          apply (r_label (k:=k) (lh:=LH_handler [] hs lh' l) (es:=es) (es':=es')) ;
            try by apply/lfilledP; rewrite -(app_nil_l (_ :: _)); constructor.
          destruct f ; destruct f' => //=.
        }
        assert (prim_step ((AI_handler hs LI :: l) ++ [a], f) s
                        [] (es2, f2) ws2 []) as Hstep.
        { repeat split => //=. } 
        destruct (reduce_append _ _ _ _ _ _ _ _ _ Hred Hstep) as [[ Hes2y Htakestep ]|
                                                            (lh0 & lh'' & Htrap &
                                                             Htrap' & -> & ->)].
        -- assert (reduce s f (AI_handler hs LI :: l) s' f'
                       (AI_handler hs LI0 :: l)).
           { apply (r_label (k:=k) (lh:=LH_handler [] hs lh' l) (es:=es) (es':=es')) ;
               (try done) ; apply/lfilledP; rewrite - (app_nil_l (_ :: _)); constructor => //. } 

           destruct Htakestep as (H2' & _ & _).
           destruct f ; destruct f2.
           assert (length_rec (AI_handler hs LI :: l) < nnn).
           { rewrite cat0s cat_app length_app_rec length_app_rec in Hlen.
             assert (length_rec [a] > 0) ; first by apply length_cons_rec.
             rewrite separate1 length_app_rec. lia. }
           destruct (IHnnn _ _ _ _ _ _ H3 H2' H4) as (-> & [[Hes ->] | [ [i Hstart] |
                                                         (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & ->)
                                                 ]]).
           ++ repeat split => //. left. subst.
              rewrite /= -cat_app separate1 -cat_app catA.
              rewrite separate1 -cat_app in Hes. rewrite Hes.
              rewrite -cat_app in Hes2y.
              rewrite - Hes2y. done.
           ++ repeat split => //. right ; left.
              exists i. simpl.
              rewrite separate1 app_assoc.
              apply first_instr_app => //.
           ++ repeat split => //. repeat right.
              exists i1, i2, i3. repeat split => //=.
              rewrite separate1 app_assoc.
              apply first_instr_app => //.
              rewrite separate1 app_assoc.
              apply first_instr_app => //.
              rewrite - (take_drop (length es2 - 1) es2).
              apply first_instr_app => //. 
        -- assert (reduce ws2 f2 (AI_handler hs LI :: l) s' f'
                     (AI_handler hs LI0 :: l)) as Hles.
           { apply (r_label (k:=k) (lh:=LH_handler [] hs lh' l) (es:=es) (es':=es')) => //=.
             rewrite -(app_nil_l (_ :: _)). apply/lfilledP. constructor => //.
             rewrite -(app_nil_l (_ :: _)). apply/lfilledP. constructor => //. } 
           destruct (trap_reduce _ _ _ _ _ _ _ Htrap' Hles) as (lh''' & ? & Hσ').
           inversion Hσ'; subst.
           repeat split => //. 
           repeat right. exists 0, 0, 0.
           repeat split; try by try rewrite cat0s -cat_app catA; try apply first_instr_app; eapply lfilled_implies_starts.
    + simpl in H1; remove_bools_options.
      assert (reduce s f (bef ++ AI_handler hs LI :: aft) s' f'
                (bef ++ AI_handler hs LI0 :: aft)) as Hles.
      { apply (r_label (k:=k) (lh:=LH_handler bef hs lh' aft) (es:=es) (es':=es')) => //=.
        all: apply/lfilledP; constructor => //. } 
      assert (reducible (bef ++ AI_handler hs LI :: aft, f)
                      s) as Hred.
    { exists [], (bef ++ AI_handler hs LI0 :: aft, f'), s', [].
      repeat split => //=. } 
    apply const_const_inv in H1 as [v ->].
    assert (prim_step ([AI_const v] ++ bef ++ AI_handler hs LI :: aft, f)
                      s [] (es2, f2)
                      ws2 []) as Hstep.
    { repeat split => //=. } 

    destruct (reduce_ves _ _ _ _ _ _ _ _ _ Hred Hstep) as [[ Hves2 Hdropstep] |
                                                       ( lh0 & lh'' & Htrap & Htrap' &
                                                         -> & -> )].
    * destruct Hdropstep as (H2' & _ & _).
      destruct f ; simpl in H2'. destruct f2 ; simpl in H2'.
      assert (length_rec (bef ++ AI_handler hs LI :: aft) < nnn).
      { repeat rewrite cat_app in Hlen. rewrite separate1 in Hlen.
        repeat rewrite length_app_rec in Hlen.
        rewrite separate1. repeat rewrite length_app_rec.
        simpl in Hlen. simpl. destruct v; try destruct v; simpl in Hlen; lia. }
      destruct (IHnnn _ _ _ _ _ _ Hles H2' H1) as (-> & [[Hes ->] | [ [i Hstart] |
                                                         (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & ->)
                                                 ]]).
      -- repeat split => //. left.
         subst.
         rewrite separate1 -cat_app -catA Hes Hves2 //.  
      -- repeat split => //. right ; left.
         exists i. rewrite separate1 -cat_app -catA first_instr_const //.
         rewrite /= const_const //.
      -- repeat split => //. repeat right.
         exists i1, i2, i3. repeat split => //=.
         rewrite separate1 -cat_app first_instr_const //.
         rewrite /= const_const //.
         rewrite separate1 -cat_app first_instr_const //.
         rewrite /= const_const //.
         rewrite - (take_drop 1 es2) first_instr_const //.
         rewrite Hves2 /= const_const //.
    * destruct (trap_reduce _ _ _ _ _ _ _ Htrap' Hles) as (lh''' & ? & Hσ').
      
      inversion Hσ'; subst.
      repeat split => //=.
      repeat right.
      exists 0,0,0.
      repeat split => //= ; try by try rewrite separate1 -cat_app first_instr_const; try rewrite /= const_const //; eapply lfilled_implies_starts.
      
  - (* Prompt *)
    destruct bef.
    + separate_last aft; last first. 
        (* if bef and aft are empty, then Hred2 is [ [AI_label n es0 l] -> es2 ].
             We painstakingly show, by case analysis, that this means es2 is of the
             form [AI_label n es0 l'] with [ l -> l' ].
             Knowing that, and since r_label gives [ l -> l1 ], we can apply the 
             induction hypothesis IHnnn on l, which is shorter than les since there is
             one less AI_label node.
         *)
      * rewrite /= in Hred2.
        lazymatch goal with
        | _ : reduce _ _ ?es _ _ _ |- _ => remember es as ves end.
        induction Hred2.
        inversion H3.
        all: remember Heqves as Heq; clear HeqHeq Heqves; subst.
        all: try by inversion Heq.
        all: try by do 4 destruct vs => //.
        all: try by do 4 destruct vcs => //.
        -- inversion Heq; subst.
           move/lfilledP in H2.
           apply lfilled_const in H2 as [-> Hes] => //.
           exfalso; apply values_no_reduce in Hred1 => //.
        -- inversion Heq; subst.
           inversion H2.
           all: try by do 2 destruct vs => //.
           all: try by do 2 destruct bef => //.
           destruct vs; last by destruct vs, es, es'0 => //; empty_list_no_reduce.
           destruct es; first empty_list_no_reduce.
           inversion H4; destruct es, es'0; subst => //.
           apply AI_trap_irreducible in Hred1 => //.
        -- move/lfilledP in H5; inversion H5; subst.
           all: try by do 2 destruct bef => //.
           all: try by do 2 destruct vs => //.
           destruct bef; last by destruct bef.
           inversion H6; subst.
           
           edestruct trap_reduce as (lh''' & ? & Hσ').
           apply/lfilledP. exact H13.
           eapply r_label.
           exact Hred1.
           apply/lfilledP. exact H2.
           apply/lfilledP. exact H12.
           inversion Hσ'; subst.
           repeat split => //. right. right.
           exists 0, 0, 0.
           repeat split => //=.
           eapply lfilled_implies_starts => //.
           instantiate (1 := LH_prompt [] ts hs lh'0 []).
           apply/lfilledP. rewrite - (app_nil_l [AI_prompt _ _ _]) - (app_nil_r [AI_prompt _ _ _]). constructor => //.
           eapply lfilled_implies_starts => //.
           instantiate (1 := LH_prompt [] ts hs lh''' []).
           apply/lfilledP. rewrite - (app_nil_l [AI_prompt _ _ _]) - (app_nil_r [AI_prompt _ _ _]). constructor => //.
           apply/lfilledP. done.
        -- inversion Heq; subst.
           exfalso. move/lfilledP in H2.
           eapply hfilled_suspend_and_reduce.
           3: exact H2. exact Hred1. done.
        -- inversion Heq; subst.
           exfalso. move/lfilledP in H2.
            eapply hfilled_switch_and_reduce in Hred1 as (tfn & sh & hhn & Hsw & Hdag & -> & -> & Htrap) => //.
           rewrite H5 in Hdag => //. 
        -- move/lfilledP in H3; inversion H3; subst.
           all: try by do 2 destruct bef => //.
           all: try by do 2 destruct vs => //. 
           all: move/lfilledP in H4; inversion H4; subst.
           ++ destruct vs.
              ** destruct es0; first empty_list_no_reduce.
                 inversion H5; destruct es0, es'1; subst => //.
                 rewrite /= cats0. rewrite /= cats0 in IHHred1.
                 apply IHHred2 => //.
              ** inversion H5; destruct vs, es0, es'1; subst => //.
           ++ destruct bef; last by destruct bef.
              inversion H5; subst. simpl.
              assert (reduce s f LI s' f' LI0).
              { eapply r_label. exact Hred1. apply/lfilledP. exact H2.
                apply/lfilledP. done. }
              assert (reduce s f LI s'0 f'0 LI2).
              { eapply r_label. exact Hred2. apply/lfilledP. exact H10.
                apply/lfilledP. done. }
              assert (length_rec LI < nnn).
              { rewrite /= /length_rec /= in Hlen.
                unfold length_rec. lia. }
              assert (lfilled 0 (LH_prompt [] ts hs (LH_base [] []) []) LI [AI_prompt ts hs LI]).
              { unfold lfilled, lfill => //=. by rewrite app_nil_r. }
              destruct (IHnnn _ _ _ _ _ _ H7 H8 H9)
                as (-> & [ [Hes ->] | [ [i Hstart] | (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & ->) ]]).
              ** repeat split => //. left. by subst.
              ** repeat split => //. right ; left. exists (i + 0).
                 eapply starts_with_lfilled => //=.
              ** repeat split => //. repeat right.
                 exists i1,i2,i3. repeat split => //=.
                 unfold first_instr => //=.
                 unfold first_instr in Hstart1 ; rewrite Hstart1 => //=.
                 unfold first_instr => //=.
                 unfold first_instr in Hstart2 ; rewrite Hstart2 => //=.
                 unfold first_instr => //=.
                 unfold first_instr in Hstart3 ; rewrite Hstart3 => //=. 
      * (* in the cases where aft is nonempty or bef is nonempty, we proceed exactly
           like in the corresponding cases when k was 0 *)
        assert (reducible (AI_prompt ts hs LI :: l, f) s) as Hred.
        { exists [], (AI_prompt ts hs LI0 :: l, f'), s', [].
          repeat split => //=.
          apply (r_label (k:=k) (lh:=LH_prompt [] ts hs lh' l) (es:=es) (es':=es')) ;
            try by apply/lfilledP; rewrite -(app_nil_l (_ :: _)); constructor.
          destruct f ; destruct f' => //=.
        }
        assert (prim_step ((AI_prompt ts hs LI :: l) ++ [a], f) s
                        [] (es2, f2) ws2 []) as Hstep.
        { repeat split => //=. } 
        destruct (reduce_append _ _ _ _ _ _ _ _ _ Hred Hstep) as [[ Hes2y Htakestep ]|
                                                            (lh0 & lh'' & Htrap &
                                                             Htrap' & -> & -> )].
        -- assert (reduce s f (AI_prompt ts hs LI :: l) s' f'
                       (AI_prompt ts hs LI0 :: l)).
           { apply (r_label (k:=k) (lh:=LH_prompt [] ts hs lh' l) (es:=es) (es':=es')) ;
               (try done) ; apply/lfilledP; rewrite - (app_nil_l (_ :: _)); constructor => //. } 

           destruct Htakestep as (H2' & _ & _).
           destruct f ; destruct f2.
           assert (length_rec (AI_prompt ts hs LI :: l) < nnn).
           { rewrite cat0s cat_app length_app_rec length_app_rec in Hlen.
             assert (length_rec [a] > 0) ; first by apply length_cons_rec.
             rewrite separate1 length_app_rec. lia. }
           destruct (IHnnn _ _ _ _ _ _ H3 H2' H4) as (-> & [[Hes ->] | [ [i Hstart] |
                                                         (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & ->)
                                                 ]]).
           ++ repeat split => //. left. subst.
              rewrite /= -cat_app separate1 -cat_app catA.
              rewrite separate1 -cat_app in Hes. rewrite Hes.
              rewrite -cat_app in Hes2y.
              rewrite - Hes2y. done.
           ++ repeat split => //. right ; left.
              exists i. simpl.
              rewrite separate1 app_assoc.
              apply first_instr_app => //.
           ++ repeat split => //. repeat right.
              exists i1, i2, i3. repeat split => //=.
              rewrite separate1 app_assoc.
              apply first_instr_app => //.
              rewrite separate1 app_assoc.
              apply first_instr_app => //.
              rewrite - (take_drop (length es2 - 1) es2).
              apply first_instr_app => //. 
        -- assert (reduce ws2 f2 (AI_prompt ts hs LI :: l) s' f'
                     (AI_prompt ts hs LI0 :: l)) as Hles.
           { apply (r_label (k:=k) (lh:=LH_prompt [] ts hs lh' l) (es:=es) (es':=es')) => //=.
             rewrite -(app_nil_l (_ :: _)). apply/lfilledP. constructor => //.
             rewrite -(app_nil_l (_ :: _)). apply/lfilledP. constructor => //. } 
           destruct (trap_reduce _ _ _ _ _ _ _ Htrap' Hles) as (lh''' & ? & Hσ').
           inversion Hσ'; subst.
           repeat split => //. 
           repeat right.
           exists 0, 0, 0.
           repeat split; try by try rewrite cat0s -cat_app catA; try apply first_instr_app; eapply lfilled_implies_starts.
    + simpl in H1; remove_bools_options.
      assert (reduce s f (bef ++ AI_prompt ts hs LI :: aft) s' f'
                (bef ++ AI_prompt ts hs LI0 :: aft)) as Hles.
      { apply (r_label (k:=k) (lh:=LH_prompt bef ts hs lh' aft) (es:=es) (es':=es')) => //=.
        all: apply/lfilledP; constructor => //. } 
      assert (reducible (bef ++ AI_prompt ts hs LI :: aft, f)
                      s) as Hred.
    { exists [], (bef ++ AI_prompt ts hs LI0 :: aft, f'), s', [].
      repeat split => //=. } 
    apply const_const_inv in H1 as [v ->].
    assert (prim_step ([AI_const v] ++ bef ++ AI_prompt ts hs LI :: aft, f)
                      s [] (es2, f2)
                      ws2 []) as Hstep.
    { repeat split => //=.  } 
    destruct (reduce_ves _ _ _ _ _ _ _ _ _ Hred Hstep) as [[ Hves2 Hdropstep] |
                                                       ( lh0 & lh'' & Htrap & Htrap' &
                                                         <- & <- )].
    * destruct Hdropstep as (H2' & _ & _).
      destruct f ; simpl in H2'. destruct f2 ; simpl in H2'.
      assert (length_rec (bef ++ AI_prompt ts hs LI :: aft) < nnn).
      { repeat rewrite cat_app in Hlen. rewrite separate1 in Hlen.
        repeat rewrite length_app_rec in Hlen.
        rewrite separate1. repeat rewrite length_app_rec.
        simpl in Hlen. simpl. destruct v; try destruct v; simpl in Hlen; lia. }
      destruct (IHnnn _ _ _ _ _ _ Hles H2' H1) as (-> & [[Hes ->] | [ [i Hstart] |
                                                         (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & ->)
                                                 ]]).
      -- repeat split => //. left.
         subst.
         rewrite separate1 -cat_app -catA Hes Hves2 //.  
      -- repeat split => //; right ; left.
         exists i. rewrite separate1 -cat_app -catA first_instr_const //.
         rewrite /= const_const //.
      -- repeat split => //. repeat right.
         exists i1, i2, i3. repeat split => //=.
         rewrite separate1 -cat_app first_instr_const //.
         rewrite /= const_const //.
         rewrite separate1 -cat_app first_instr_const //.
         rewrite /= const_const //.
         rewrite - (take_drop 1 es2) first_instr_const //.
         rewrite Hves2 /= const_const //.
    * destruct (trap_reduce _ _ _ _ _ _ _ Htrap' Hles) as (lh''' & ? & Hσ').
      inversion Hσ' ; subst.
      repeat split => //.

      repeat right.
      exists 0, 0, 0. 

      repeat split => //= ; try by try rewrite separate1 -cat_app first_instr_const; try rewrite /= const_const //; eapply lfilled_implies_starts.

Qed.
