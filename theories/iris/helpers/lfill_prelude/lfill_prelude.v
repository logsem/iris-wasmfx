From mathcomp Require Import ssreflect ssrbool eqtype seq.
From Coq Require Import Eqdep_dec.
From stdpp Require Import base list.
From Wasm Require Export common operations opsem properties list_extra stdpp_aux.
Require Export lfill_extension.
Require Import Coq.Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Lemma length_cons_rec a es :
  length_rec (a :: es) > length_rec es.
Proof.
  unfold length_rec => //=. destruct a => //= ; lia.
Qed. 

Lemma length_app_rec l1 l2 :
  length_rec (app l1 l2) = length_rec l1 + length_rec l2.
Proof.
  unfold length_rec. rewrite map_app. rewrite list_sum_app. done.  
Qed. 

Lemma length_lfilled_rec k lh es les :
  lfilled k lh es les -> length_rec es <= length_rec les.
Proof.
  move => Hlf; move/lfilledP in Hlf.
  induction Hlf; repeat rewrite length_app_rec => /=; first lia.
  all: unfold length_rec in * => /=; by lias.
Qed.

Lemma length_lfilled_rec' k lh es les :
  lfilled k lh es les -> length_rec es < length_rec les \/ es = les /\ k = 0 /\ lh = LH_base [::] [::].
Proof.
  move => Hlf; move/lfilledP in Hlf.
  induction Hlf; repeat rewrite length_app_rec => /=.
  - destruct vs => //=.
    + destruct es' => //=.
       * right. by rewrite cats0.
       * left. specialize (length_cons_rec a es') as H'.
         lias.
    + left. specialize (length_cons_rec a vs) as H'. lias.
  - left. unfold length_rec in * => /=.
    destruct IHHlf as [? | (-> & -> & ->)]; lias.
  - left. unfold length_rec in * => /=.
    destruct IHHlf as [? | (-> & -> & ->)]; lias.
  - left. unfold length_rec in * => /=.
    destruct IHHlf as [? | (-> & -> & ->)]; lias.

Qed.

Lemma length_llfill_rec' lh es les :
  llfill lh es = les -> length_rec es < length_rec les \/ es = les /\ lh = LL_base [::] [::].
Proof.
  move => <-.
  induction lh => /=; repeat rewrite length_app_rec => /=.
  - destruct l => //=.
    + destruct l0 => //=.
      * right. by rewrite List.app_nil_r.
      * left. specialize (length_cons_rec a l0) as H'.
        lias.
    + left. specialize (length_cons_rec (AI_const v) (v_to_e_list l)) as H'. lias.
  - left. unfold length_rec in * => /=.
    destruct IHlh as [? | (-> & ->)] => //=; try lias.
    repeat rewrite List.app_nil_r. lias.
  - left. unfold length_rec in * => /=.
    destruct IHlh as [? | (-> & ->)] => //=; try lias.
    repeat rewrite List.app_nil_r. lias.
  - left. unfold length_rec in * => /=.
    destruct IHlh as [? | (-> & ->)] => //=; try lias.
    repeat rewrite List.app_nil_r. lias.
  - left. unfold length_rec in * => /=.
    destruct IHlh as [? | (-> & ->)] => //=; try lias.
    repeat rewrite List.app_nil_r. lias.
Qed.

Lemma lfill_cons_not_Some_nil : forall i lh es es' e es0,
  lfill i lh es = es' -> es = e :: es0 -> es' <> Some [::].
Proof.
  move => i lh es es' e es0 Hlf Hes Hcontra.
  destruct es' => //; inversion Hcontra; subst; clear Hcontra.
  assert (lfilled i lh (e :: es0) []) as Hlf'; first by unfold lfilled; rewrite Hlf.
  move/lfilledP in Hlf'.
  inversion Hlf'; subst.
  all: try by destruct vs => //.
  all: try by destruct bef => //. 
Qed.

Lemma lfilled_not_nil : forall i lh es es', lfilled i lh es es' -> es <> [::] -> es' <> [::].
Proof.
  move => i lh es es' H Hes Hes'.
  move/lfilledP in H.
  inversion H; subst; clear H; try by destruct vs, es => //.
  all: by destruct bef, aft => //. 
Qed.

Lemma lfilled_first_values i lh vs e i' lh' vs' e' LI :
  lfilled i lh (vs ++ [::e]) LI ->
  lfilled i' lh' (vs' ++ [::e']) LI ->
  const_list vs -> const_list vs' ->
  (is_const e = false) -> (is_const e' = false) ->
  (forall n es LI, e <> AI_label n es LI) -> (forall n es LI, e' <> AI_label n es LI) ->
  (forall hs LI, e <> AI_handler hs LI) -> (forall ts hs LI, e <> AI_prompt ts hs LI) ->
  (forall hs LI, e' <> AI_handler hs LI) -> (forall ts hs LI, e' <> AI_prompt ts hs LI) ->
  e = e' /\ i = i' /\ (length vs = length vs' -> (vs = vs' /\ lh = lh')).
Proof.
  generalize dependent LI. generalize dependent lh'.
  generalize dependent i'.
  generalize dependent i. 
  induction lh as [bef aft| bef n0 es lh IH aft |bef hs lh IH aft |bef ts hs lh IH aft ] => //.
  all: intros i i' lh' LI Hfill Hfill' Hvs Hvs' He He' Hlabe Hlabe' Hhandlere Hprompte Hhandlere' Hprompte'.
  all: unfold lfilled, lfill in Hfill; fold lfill in Hfill.
  all: try unfold lfilled in IH.
  1,2 : destruct i => //.
  all: try (specialize (IH i)).
  all: remember (const_list bef) as b eqn:Hbef ; destruct b => //.
  all: try (destruct (lfill i _ _) as [fill0|]; last done).
  all: move/eqP in Hfill.
  all: destruct lh' as [bef' aft'|bef' n' es' lh' aft' | bef' hs' lh' aft' | bef' ts' hs' lh' aft' ] => //.
  all: unfold lfilled, lfill in Hfill' ; fold lfill in Hfill'.
  all: try (destruct i'; first done).
  all: try (destruct i'; last done).
  all: remember (const_list bef') as b0 eqn:Hbef' ; destruct b0 => //.
  all: try (specialize (IH i' lh')).
  all: try (destruct (lfill _ _ _) as [fill0'|]; last done).
  all: move/eqP in Hfill'.
  all: rewrite Hfill in Hfill'.
  all: repeat rewrite - app_assoc in Hfill'.
  all: try rewrite (app_assoc bef) in Hfill'.
  all: try rewrite (app_assoc bef') in Hfill'.
  all: try (apply first_values in Hfill' as (Hvvs & Hee & ?);
            (try done); (try by left); try by unfold const_list ; rewrite forallb_app; apply andb_true_iff).
  all: try by exfalso; eapply Hlabe.
  all: try by exfalso; eapply Hhandlere.
  all: try by exfalso; eapply Hprompte.
  all: try by exfalso; eapply Hlabe'.
  all: try by exfalso; eapply Hhandlere'.
  all: try by exfalso; eapply Hprompte'.
  { repeat split => //=. apply (app_inj_2 _ _ _ _ H0 Hvvs).
    apply app_inj_2 in Hvvs as [-> _] => //. by subst. } 
  all: inversion Hee; subst.
  all: destruct (IH fill0') as (-> & -> & Hlen) => //.
  all: split => //.
  all: split => //.
  all: intros Hlenvs.
  all: apply Hlen in Hlenvs as [-> ->].
  all: done.
Qed.

Lemma hfilled_first_values i lh vs e i' lh' vs' e' LI :
  hfilled i lh (vs ++ [::e]) LI ->
  hfilled i' lh' (vs' ++ [::e']) LI ->
  const_list vs -> const_list vs' ->
  (is_const e = false) -> (is_const e' = false) ->
  (forall n es LI, e <> AI_label n es LI) -> (forall n es LI, e' <> AI_label n es LI) ->
  (forall n es LI, e <> AI_local n es LI) -> (forall n es LI, e' <> AI_local n es LI) ->
  (forall hs LI, e <> AI_handler hs LI) -> (forall ts hs LI, e <> AI_prompt ts hs LI) ->
  (forall hs LI, e' <> AI_handler hs LI) -> (forall ts hs LI, e' <> AI_prompt ts hs LI) ->
  e = e' /\ (length vs = length vs' -> (vs = vs' /\ lh = lh')).
Proof.
  generalize dependent LI. generalize dependent lh'.
  generalize dependent i'.
  generalize dependent i. 
  induction lh as [bef aft| bef n0 es lh IH aft | bef n0 es lh IH aft |bef hs lh IH aft |bef ts hs lh IH aft ] => //.
  all: intros i i' lh' LI Hfill Hfill' Hvs Hvs' He He' Hlabe Hlabe' Hloce Hloce' Hhandlere Hprompte Hhandlere' Hprompte'.
  all: move/hfilledP in Hfill; inversion Hfill; subst.
  all: destruct lh' as [bef' aft'|bef' n' es' lh' aft' | bef' n' es' lh' aft' | bef' hs' lh' aft' | bef' ts' hs' lh' aft' ] => //.
  all: move/hfilledP in Hfill'; inversion Hfill'; subst.
  all: lazymatch goal with
       | H : (_ ++ _)%SEQ = (_ ++ _)%SEQ |- _ => remember H as Hnew; clear HeqHnew H
       end.
  all: repeat rewrite cat_app in Hnew.
  all: repeat rewrite - app_assoc in Hnew.
  all: try rewrite (app_assoc bef) in Hnew.
  all: try rewrite (app_assoc bef') in Hnew.
  all: try (apply first_values in Hnew as (Hvvs & Hee & ?);
            (try done); (try by left); try by unfold const_list ; rewrite forallb_app; apply andb_true_iff).
  all: try by exfalso; eapply Hlabe.
  all: try by exfalso; eapply Hhandlere.
  all: try by exfalso; eapply Hprompte.
  all: try by exfalso; eapply Hlabe'.
  all: try by exfalso; eapply Hloce.
  all: try by exfalso; eapply Hloce'.
  all: try by exfalso; eapply Hhandlere'.
  all: try by exfalso; eapply Hprompte'.
  { repeat split => //=. eapply app_inj_2. exact H0. symmetry. exact Hvvs. 
    apply app_inj_2 in Hvvs as [-> _] => //. by subst. } 
  all: inversion Hee; subst.
  all: edestruct IH as (Hres & Hlen) => //.
  all: try by apply/hfilledP.
  all: split => //.
  all: intros Hlenvs.
  all: apply Hlen in Hlenvs as [-> ->].
  all: done.
Qed.

Lemma lfilled_trans : forall k lh es1 es2 k' lh' es3,
    lfilled k lh es1 es2 -> lfilled k' lh' es2 es3 -> exists lh'', lfilled (k+k') lh'' es1 es3.
Proof.
  intros k lh es1 es2 k' lh' ; generalize dependent es1 ;
    generalize dependent es2 ; 
(*    generalize dependent lh ; generalize dependent k ; *)

    generalize dependent k';
    induction lh' as [bef' aft' | bef' nn' es' lh' IHlh' aft' | bef' hs' lh' IHlh' aft' | bef' ts' hs' lh' IHlh' aft'];
    intros k' (* k lh *) es2 es1 es3 Hfill2 Hfill3.
  all: unfold lfilled, lfill in Hfill3; fold lfill in Hfill3.
  1, 2: destruct k' => //.
(*  all: try (specialize (IHlh' k' (* es2 *))). *)
(*  all: try unfold lfilled in IHlh'. *)
  all: destruct (const_list bef') eqn:Hbef' ; last done.
  all: try (destruct (lfill k' _ _) as [fill' |] eqn:Hfill'; last done).
  all: move/eqP in Hfill3.
 
  all: destruct lh as [bef aft |bef nn es lh aft | bef hs lh aft | bef ts hs lh aft] => //.
  all: unfold lfilled, lfill in Hfill2; fold lfill in Hfill2.
  all: try (destruct k; first done).
  all: try (destruct k; last done).
  all: destruct (const_list bef) eqn:Hbef; last done.
(*  all: try (specialize (IHlh' k lh)). *)
(*  all: try (specialize (IHlh' 0 (LH_base bef aft))). *)
  (* ;
            unfold lfill in IHlh'; fold lfill in IHlh';
            rewrite Hbef in IHlh'). *)
  all: try (destruct (lfill k _ _) as [fill |] eqn:Hfill; last done).
  all: move/eqP in Hfill2 ; subst.
  all: try rewrite Nat.add_0_r.
  all: simpl.
  exists (LH_base (bef' ++ bef) (aft ++ aft')).
  2: eexists (LH_rec (bef' ++ bef) nn es lh (aft ++ aft')).
  3: eexists (LH_handler (bef' ++ bef) hs lh (aft ++ aft')).
  4: eexists (LH_prompt (bef' ++ bef) ts hs lh (aft ++ aft')).

  1-4: unfold lfilled, lfill; fold lfill.
  1-4: rewrite const_list_concat => //.
  2-4: rewrite Hfill.
  2-4: rewrite separate1.
  1-4: repeat rewrite app_assoc.
  1-4: repeat rewrite - List.app_assoc => //.
  all: edestruct IHlh' as [lh'' Hlh''];
    [ |
      unfold lfilled; erewrite Hfill'; done | ].
  all: try instantiate (1 := es1).
  all: unfold lfilled, lfill; fold lfill.
  all: try rewrite Hbef.
  all: try rewrite Hfill.
  all: try done.
  1-4: eexists (LH_rec bef' nn' es' lh'' aft').
  5-8: eexists (LH_handler bef' hs' lh'' aft').
  9-12: eexists (LH_prompt bef' ts' hs' lh'' aft').
  all: unfold lfill; fold lfill.
  all: rewrite Hbef'.
  all: simpl in Hlh''.
  all: unfold lfilled in Hlh''.
  all: destruct (lfill _ lh'' _) eqn:Hfill'' => //.
  all: move/eqP in Hlh''; subst l.
  all: try done.
  all: replace (k + S k') with (S k + k'); last lias.
  all: simpl.
  all: rewrite Hfill''.
  all: done.
Qed.

Lemma lfilled_hfilled_trans hh k lh es1 es2 es3:
  hfilled No_var hh es1 es2 -> lfilled k lh es2 es3 ->
  exists hh', hfilled No_var hh' es1 es3.
Proof.
  intros Hh Hl.
  move/lfilledP in Hl.
  induction Hl.
  { move/hfilledP in Hh.
    inversion Hh; subst.
    { exists (HH_base (vs ++ vs0) (es'0 ++ es')).
      unfold hfilled, hfill => //=.
      rewrite const_list_concat => //.
      repeat rewrite catA => //. } 
    exists (HH_label (vs ++ vs0) n es'0 hh' (es'' ++ es')).
    2: eexists (HH_local (vs ++ vs0) n f hh' (es'' ++ es')).
    3: eexists (HH_prompt (vs ++ bef) ts hs hh' (aft ++ es')).
    4: eexists (HH_handler (vs ++ bef) hs hh' (aft ++ es')).
    all: unfold hfilled, hfill; fold hfill.
    all: rewrite const_list_concat => //.
    1-2: move/hfilledP in H1.
    3-4: move/hfilledP in H2.
    1-2: unfold hfilled in H1.
    3-4: unfold hfilled in H2.
    all: destruct (hfill _ _ _) => //.
    1-2: move/eqP in H1; subst.
    3-4: move/eqP in H2; subst.
    all: repeat rewrite catA => //. }
  all: apply IHHl in Hh as [hh' Hres].
  all: unfold hfilled in Hres.
  exists (HH_label vs n es' hh' es'').
  2: eexists (HH_handler bef hs hh' aft).
  3: eexists (HH_prompt bef ts hs hh' aft).
  all: unfold hfilled, hfill; fold hfill.
  all: rewrite H.
  all: destruct (hfill _ _ _) => //.
  all: move/eqP in Hres; subst => //.
Qed. 
    

Lemma vfill_is_nil n (vh : valid_holed n) es :
  vfill vh es = [] -> es = [] /\ vh = VH_base n [] [].
Proof.
  destruct vh => //= ; intros.
  { repeat apply app_eq_nil in H as [? H].
    apply map_eq_nil in H0.
    by subst. } 
  all: apply app_eq_nil in H as [_ H] ; inversion H.
Qed.

Lemma susfill_is_nil x (sh : susholed) es :
  susfill x sh es = [] -> es = [] /\ sh = SuBase [] [].
Proof.
  destruct sh => //=; intros.
  { repeat apply app_eq_nil in H as [? H].
    apply map_eq_nil in H0.
    by subst. }
  all: apply app_eq_nil in H as [_ H]; inversion H.
Qed.

Lemma swfill_is_nil x (sh : swholed) es :
  swfill x sh es = [] -> es = [] /\ sh = SwBase [] [].
Proof.
  destruct sh => //=; intros.
  { repeat apply app_eq_nil in H as [? H].
    apply map_eq_nil in H0.
    by subst. }
  all: apply app_eq_nil in H as [_ H]; inversion H.
Qed.

Lemma exnfill_is_nil x (sh : exnholed) es :
  exnfill x sh es = [] -> es = [] /\ sh = ExBase [] [].
Proof.
  destruct sh => //=; intros.
  { repeat apply app_eq_nil in H as [? H].
    apply map_eq_nil in H0.
    by subst. }
  all: apply app_eq_nil in H as [_ H]; inversion H.
Qed. 

Lemma sfill_is_nil sh es :
  sfill sh es = [] -> es = [] /\ sh = SH_base [] [].
Proof.
  destruct sh => //= ; intros.
  { repeat apply app_eq_nil in H as [? H].
    apply map_eq_nil in H0.
    by subst. } 
  all: apply app_eq_nil in H as [_ H] ; inversion H.
Qed.

Lemma llfill_is_nil lh es :
  llfill lh es = [] -> es = [] /\ lh = LL_base [] [].
Proof.
  destruct lh => //= ; intros.
  { repeat apply app_eq_nil in H as [? H].
    apply map_eq_nil in H0.
    by subst. } 
  all : apply app_eq_nil in H as [_ H] ; inversion H.
Qed.
  
Lemma vh_push_const_inj n (vh : valid_holed n) vh' vs :
  vh_push_const vh vs = vh_push_const vh' vs -> vh = vh'.
Proof.
  destruct vh => //=.
  - destruct vh' => //=.
    intro H ; inversion H.
    apply app_inv_head in H1.
    by subst.
  - set (m := S n) in vh'.
    pose (Logic.eq_refl : m = S n) as Hm.
    change vh' with match Hm in _ = w return valid_holed w with
                    | Logic.eq_refl => vh' end.
    clearbody m Hm.
    replace (vh_push_const match Hm in _ = w return valid_holed w with
               | Logic.eq_refl => vh' end vs)
      with match Hm in _ = w return valid_holed w with
           | Logic.eq_refl => vh_push_const vh' vs end ;
      last by destruct Hm.
    destruct vh' => //=.
    + replace match Hm in (_ = w) return (valid_holed w) with
              | Logic.eq_refl => VH_base n1 (vs ++ l2) l3
              end with (VH_base (S n) (vs ++ l2) l3) ;
        last by destruct Hm.
      done.
    + pose proof (eq_add_S _ _ Hm) as Hn.
      assert (Hm = f_equal S Hn) as Hproof.
      apply Eqdep.EqdepTheory.UIP.
      replace match Hm in (_ = w) return (valid_holed w) with
              | Logic.eq_refl => VH_rec (vs ++ l2) n2 l3 vh' l4
              end with (VH_rec (vs ++ l2) n2 l3 match Hn in _ = w return valid_holed w
                          with Logic.eq_refl => vh' end l4) ;
        last by rewrite Hproof ; destruct Hn.
      intro H ; inversion H.
      apply app_inv_head in H1.
      apply Eqdep.EqdepTheory.inj_pair2 in H4.
      rewrite H1 H4.
      by rewrite Hproof ; destruct Hn.
    + destruct n1 => //.
      pose proof (eq_add_S _ _ Hm) as Hn.
      assert (Hm = f_equal S Hn) as Hproof.
      apply Eqdep.EqdepTheory.UIP.
      replace match Hm in (_ = w) return (valid_holed w) with
              | Logic.eq_refl => VH_prompt (vs ++ l2) l3 l4 vh' l5
              end with
        (VH_prompt (vs ++ l2) l3 l4 match Hm in _ = w return valid_holed w with Logic.eq_refl => vh' end l5) => //.
      rewrite Hproof. destruct Hn. done.
    + destruct n1 => //.
      pose proof (eq_add_S _ _ Hm) as Hn.
      assert (Hm = f_equal S Hn) as Hproof.
      apply Eqdep.EqdepTheory.UIP.
      replace match Hm in (_ = w) return (valid_holed w) with
              | Logic.eq_refl => VH_handler (vs ++ l2) l3 vh' l4
              end with
        (VH_handler (vs ++ l2) l3 match Hm in _ = w return valid_holed w with Logic.eq_refl => vh' end l4) => //.
      rewrite Hproof. destruct Hn. done.
  - destruct vh' => //=.
    intros H; inversion H; subst.
    apply app_app in H1 => //.
    inversion H1; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H4 as ->.
    done.
  - destruct vh' => //=.
        intros H; inversion H; subst.
    apply app_app in H1 => //.
    inversion H1; subst.
    apply Eqdep.EqdepTheory.inj_pair2 in H3 as ->.
    done.
Qed.
  
Lemma vfill_decrease n (vh1:valid_holed (S n)) vh2 es :
  vh_decrease vh1 = Some vh2 -> vfill vh1 es = vfill vh2 es.
Proof.
  set (m := S n) in vh1.
  pose (Logic.eq_refl : m = S n) as Hm.
  change vh1 with match Hm in _ = w return valid_holed w with
                  | Logic.eq_refl => vh1 end.
  clearbody m Hm.
  generalize dependent n.
  induction vh1 ; intros m vh2 Hm.
  - destruct n => //.
    pose proof (eq_add_S _ _ Hm) as Hn.
    assert (Hm = f_equal S Hn) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease match Hm in _ = w return valid_holed w with
                         | Logic.eq_refl => VH_base (S n) l l0 end) with
      match Hn in _ = w return option (valid_holed w) with
      | Logic.eq_refl => vh_decrease (VH_base (S n) l l0) end ;
      last by rewrite Hproof ; destruct Hn.
    simpl.
    rewrite Hproof.
    destruct Hn. simpl.
    intro H ; inversion H ; subst => //=.
  - pose proof (eq_add_S _ _ Hm) as Hn.
    assert (Hm = f_equal S Hn) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease match Hm in _ = w return valid_holed w with
                         | Logic.eq_refl => VH_rec l n0 l0 vh1 l1 end) with
      match Hn in _ = w return option (valid_holed w) with
      | Logic.eq_refl => vh_decrease (VH_rec l n0 l0 vh1 l1) end ;
      last by rewrite Hproof ; destruct Hn.
    simpl.
    destruct n ; first by destruct Hn.
    destruct m => //.
    pose proof (eq_add_S _ _ Hn) as Hp.
    assert (Hn = f_equal S Hp) as Hproof'.
    apply Eqdep.EqdepTheory.UIP.
    replace  match Hn in (_ = w) return (option (valid_holed w)) with
             | Logic.eq_refl =>
                 match vh_decrease vh1 with
                 | Some vh' => Some (VH_rec l n0 l0 vh' l1)
                 | None => None
                 end
             end with match vh_decrease match Hn in (_ = w) return valid_holed w with
                                        | Logic.eq_refl => vh1 end with
                      | Some vh' => Some (VH_rec l n0 l0 vh' l1)
                      | None => None end ;
      last by rewrite Hproof' ; destruct Hp.
    destruct (vh_decrease _) eqn:Hdecr1 => //.
    apply IHvh1 in Hdecr1.
    intro H ; inversion H ; subst  => /=.
    simpl in Hdecr1.
    by rewrite Hdecr1.
  - destruct n => //.
    pose proof (eq_add_S _ _ Hm) as Hn.
    assert (Hm = f_equal S Hn) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease match Hm in _ = w return valid_holed w with
                         | Logic.eq_refl => VH_prompt l l0 l1 vh1 l2 end) with
      match Hn in _ = w return option (valid_holed w) with
      | Logic.eq_refl => vh_decrease (VH_prompt l l0 l1 vh1 l2) end ;
      last by rewrite Hproof ; destruct Hn.
    simpl.
    replace  match Hn in (_ = w) return (option (valid_holed w)) with
             | Logic.eq_refl =>
                 match vh_decrease vh1 with
                 | Some vh' => Some (VH_prompt l l0 l1 vh' l2)
                 | None => None
                 end
             end with match vh_decrease match Hm in (_ = w) return valid_holed w with
                                        | Logic.eq_refl => vh1 end with
                      | Some vh' => Some (VH_prompt l l0 l1 vh' l2)
                      | None => None end ;
      last by rewrite Hproof ; destruct Hn.
    destruct (vh_decrease _) eqn:Hdecr1 => //.
    apply IHvh1 in Hdecr1.
    intro H ; inversion H ; subst  => /=.
    simpl in Hdecr1.
    by rewrite Hdecr1.
     - destruct n => //.
    pose proof (eq_add_S _ _ Hm) as Hn.
    assert (Hm = f_equal S Hn) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease match Hm in _ = w return valid_holed w with
                         | Logic.eq_refl => VH_handler l l0 vh1 l1 end) with
      match Hn in _ = w return option (valid_holed w) with
      | Logic.eq_refl => vh_decrease (VH_handler l l0 vh1 l1) end ;
      last by rewrite Hproof ; destruct Hn.
    simpl.
    replace  match Hn in (_ = w) return (option (valid_holed w)) with
             | Logic.eq_refl =>
                 match vh_decrease vh1 with
                 | Some vh' => Some (VH_handler l l0 vh' l1)
                 | None => None
                 end
             end with match vh_decrease match Hm in (_ = w) return valid_holed w with
                                        | Logic.eq_refl => vh1 end with
                      | Some vh' => Some (VH_handler l l0 vh' l1)
                      | None => None end ;
      last by rewrite Hproof ; destruct Hn.
    destruct (vh_decrease _) eqn:Hdecr1 => //.
    apply IHvh1 in Hdecr1.
    intro H ; inversion H ; subst  => /=.
    simpl in Hdecr1.
    by rewrite Hdecr1.
Qed.    

Lemma vh_decrease_push_const m (vh : valid_holed (S m)) vs vh' :
  vh_decrease vh = Some vh' ->
  vh_decrease (vh_push_const vh vs) = Some (vh_push_const vh' vs).
Proof.
  set (n := S m) in vh.
  pose (Logic.eq_refl : n = S m) as Hn.
  change vh with (match Hn in _ = w return valid_holed w with
                  | Logic.eq_refl => vh end).
  clearbody n Hn.
  destruct vh.
  - destruct n => //.
    pose proof (eq_add_S _ _ Hn) as Hm.
    assert (Hn = f_equal S Hm) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease (match Hn in _ = w return (valid_holed w) with
                          | Logic.eq_refl => VH_base (S n) l l0 end)) with
      (match Hm in _ = w return (option (valid_holed w)) with
       | Logic.eq_refl => vh_decrease (VH_base (S n) l l0) end) ;
      last by rewrite Hproof ; destruct Hm.
    replace (vh_decrease (vh_push_const (match Hn in (_ = w) return (valid_holed w) with
                                         | Logic.eq_refl => VH_base (S n) l l0 end) vs))
      with (match Hm in _ = w return option (valid_holed w) with
            | Logic.eq_refl => vh_decrease (VH_base (S n) (vs ++ l) l0) end) ;
      last by rewrite Hproof ; destruct Hm.
    destruct Hm => //=.
    intro H ; inversion H => //=.
  - pose proof (eq_add_S _ _ Hn) as Hm.
    assert (Hn = f_equal S Hm) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease (match Hn in _ = w return (valid_holed w) with
                          | Logic.eq_refl => VH_rec l n0 l0 vh l1 end)) with
      (match Hm in _ = w return (option (valid_holed w)) with
       | Logic.eq_refl => vh_decrease (VH_rec l n0 l0 vh l1) end) ;
      last by rewrite Hproof ; destruct Hm.
    replace (vh_decrease (vh_push_const (match Hn in (_ = w) return (valid_holed w) with
                                         | Logic.eq_refl => VH_rec l n0 l0 vh l1 end) vs))
      with (match Hm in _ = w return option (valid_holed w) with
            | Logic.eq_refl => vh_decrease (VH_rec (vs ++ l) n0 l0 vh l1) end) ;
      last by rewrite Hproof ; destruct Hm.
    destruct Hm => //=.
    destruct n => //=.
    destruct (vh_decrease vh) => //=.
    intro H ; inversion H => //=.
  - destruct n => //. pose proof (eq_add_S _ _ Hn) as Hm.
    assert (Hn = f_equal S Hm) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease (match Hn in _ = w return (valid_holed w) with
                          | Logic.eq_refl => VH_prompt l l0 l1 vh l2 end)) with
      (match Hm in _ = w return (option (valid_holed w)) with
       | Logic.eq_refl => vh_decrease (VH_prompt l l0 l1 vh l2) end) ;
      last by rewrite Hproof ; destruct Hm.
    replace (vh_decrease (vh_push_const (match Hn in (_ = w) return (valid_holed w) with
                                         | Logic.eq_refl => VH_prompt l l0 l1 vh l2 end) vs))
      with (match Hm in _ = w return option (valid_holed w) with
            | Logic.eq_refl => vh_decrease (VH_prompt (vs ++ l) l0 l1 vh l2) end) ;
      last by rewrite Hproof ; destruct Hm.
    destruct Hm => //=.
    destruct (vh_decrease vh) => //=.
    intro H ; inversion H => //=.
     - destruct n => //. pose proof (eq_add_S _ _ Hn) as Hm.
    assert (Hn = f_equal S Hm) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease (match Hn in _ = w return (valid_holed w) with
                          | Logic.eq_refl => VH_handler l l0 vh l1 end)) with
      (match Hm in _ = w return (option (valid_holed w)) with
       | Logic.eq_refl => vh_decrease (VH_handler l l0 vh l1) end) ;
      last by rewrite Hproof ; destruct Hm.
    replace (vh_decrease (vh_push_const (match Hn in (_ = w) return (valid_holed w) with
                                         | Logic.eq_refl => VH_handler l l0 vh l1 end) vs))
      with (match Hm in _ = w return option (valid_holed w) with
            | Logic.eq_refl => vh_decrease (VH_handler (vs ++ l) l0 vh l1) end) ;
      last by rewrite Hproof ; destruct Hm.
    destruct Hm => //=.
    destruct (vh_decrease vh) => //=.
    intro H ; inversion H => //=.
Qed.

Lemma vh_decrease_push_const_inv m (vh : valid_holed (S m)) vs vh' :
  vh_decrease (vh_push_const vh vs) = Some vh' ->
  exists vh'', vh_decrease vh = Some vh'' /\ vh_push_const vh'' vs = vh'.
Proof.
  set (n := S m) in vh.
  pose (Logic.eq_refl : n = S m) as Hn.
  change vh with (match Hn in _ = w return valid_holed w with
                  | Logic.eq_refl => vh end) in *.
  clearbody n Hn.
  generalize dependent m.
  induction vh ; intros m vh' Hn.
  - destruct n => //.
    pose proof (eq_add_S _ _ Hn) as Hm.
    assert (Hn = f_equal S Hm) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease (match Hn in _ = w return (valid_holed w) with
                          | Logic.eq_refl => VH_base (S n) l l0 end)) with
      (match Hm in _ = w return (option (valid_holed w)) with
       | Logic.eq_refl => vh_decrease (VH_base (S n) l l0) end) ;
      last by rewrite Hproof ; destruct Hm.
    replace (vh_decrease (vh_push_const (match Hn in (_ = w) return (valid_holed w) with
                                         | Logic.eq_refl => VH_base (S n) l l0 end) vs))
      with (match Hm in _ = w return option (valid_holed w) with
            | Logic.eq_refl => vh_decrease (VH_base (S n) (vs ++ l) l0) end) ;
      last by rewrite Hproof ; destruct Hm.
    exists (VH_base m l l0).
    split.
    destruct Hm => //=.
    simpl in H. destruct Hm => //=.
    by inversion H.
  - pose proof (eq_add_S _ _ Hn) as Hm.
    assert (Hn = f_equal S Hm) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease (vh_push_const (match Hn in (_ = w) return (valid_holed w) with
                                         | Logic.eq_refl => VH_rec l n0 l0 vh l1 end) vs))
      with 
      (vh_decrease (vh_push_const (VH_rec l n0 l0 (match Hm in _ = w return valid_holed w
                                                   with Logic.eq_refl => vh end) l1) vs)) ;
      last by rewrite Hproof ; destruct Hm.
    simpl. destruct m => //.
    destruct (vh_decrease _) eqn:Hdecr => //.
    intro Hvh'.

    destruct n => //.
    pose proof (eq_add_S _ _ Hm) as Hp.
    assert (Hm = f_equal S Hp) as Hproof'.
    apply Eqdep.EqdepTheory.UIP.
    destruct (IHvh m (vh_push_const v vs) Hm) as (vh'' & Hdecr' & Hpush).    
    erewrite vh_decrease_push_const => //.
    exists (VH_rec l n0 l0 vh'' l1).
    split.
    replace ( vh_decrease
                match Hn in (_ = w) return (valid_holed w) with
                | Logic.eq_refl => VH_rec l n0 l0 vh l1
                end )
      with  ( match Hm in _ = w return option (valid_holed w) with
              | Logic.eq_refl => vh_decrease (VH_rec l n0 l0 vh l1) end) ;
      last by rewrite Hproof Hproof' ; destruct Hp.
    simpl.
    replace (  match Hm in (_ = w) return (option (valid_holed w)) with
               | Logic.eq_refl =>
                   match vh_decrease vh with
                   | Some vh'0 => Some (VH_rec l n0 l0 vh'0 l1)
                   | None => None
                   end
               end) with
      (match vh_decrease (match Hm in (_ = w) return (valid_holed w) with
                          | Logic.eq_refl => vh end) with
       | Some vh'0 => Some (VH_rec l n0 l0 vh'0 l1)
       | None => None end) ;
      last by rewrite Hproof' ; destruct Hp.
    by rewrite Hdecr'.
    simpl.
    inversion Hvh'.
    apply vh_push_const_inj in Hpush.
    by rewrite Hpush.
  - destruct n => //. pose proof (eq_add_S _ _ Hn) as Hm.
    assert (Hn = f_equal S Hm) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease (vh_push_const (match Hn in (_ = w) return (valid_holed w) with
                                         | Logic.eq_refl => VH_prompt l l0 l1 vh l2 end) vs))
      with 
      (vh_decrease (vh_push_const (VH_prompt l l0 l1 (match Hn in _ = w return valid_holed w
                                                   with Logic.eq_refl => vh end) l2) vs)) ;
      last by rewrite Hproof ; destruct Hm.
    simpl. 
    destruct (vh_decrease _) eqn:Hdecr => //.
    intro Hvh'.

    destruct (IHvh m (vh_push_const v vs) Hn) as (vh'' & Hdecr' & Hpush).    
    erewrite vh_decrease_push_const => //.
    exists (VH_prompt l l0 l1 vh'' l2).
    split.
    replace ( vh_decrease
                match Hn in (_ = w) return (valid_holed w) with
                | Logic.eq_refl => VH_prompt l l0 l1 vh l2
                end )
      with  ( match Hm in _ = w return option (valid_holed w) with
              | Logic.eq_refl => vh_decrease (VH_prompt l l0 l1 vh l2) end) ;
      last by rewrite Hproof ; destruct Hm.
    simpl.
    replace (  match Hm in (_ = w) return (option (valid_holed w)) with
               | Logic.eq_refl =>
                   match vh_decrease vh with
                   | Some vh'0 => Some (VH_prompt l l0 l1 vh'0 l2)
                   | None => None
                   end
               end) with
      (match vh_decrease (match Hn in (_ = w) return (valid_holed w) with
                          | Logic.eq_refl => vh end) with
       | Some vh'0 => Some (VH_prompt l l0 l1 vh'0 l2)
       | None => None end) ;
      last by rewrite Hproof ; destruct Hm.
    by rewrite Hdecr'.
    simpl.
    inversion Hvh'.
    apply vh_push_const_inj in Hpush.
    by rewrite Hpush.
     - destruct n => //. pose proof (eq_add_S _ _ Hn) as Hm.
    assert (Hn = f_equal S Hm) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    replace (vh_decrease (vh_push_const (match Hn in (_ = w) return (valid_holed w) with
                                         | Logic.eq_refl => VH_handler l l0 vh l1 end) vs))
      with 
      (vh_decrease (vh_push_const (VH_handler l l0 (match Hn in _ = w return valid_holed w
                                                   with Logic.eq_refl => vh end) l1) vs)) ;
      last by rewrite Hproof ; destruct Hm.
    simpl. 
    destruct (vh_decrease _) eqn:Hdecr => //.
    intro Hvh'.

    destruct (IHvh m (vh_push_const v vs) Hn) as (vh'' & Hdecr' & Hpush).    
    erewrite vh_decrease_push_const => //.
    exists (VH_handler l l0 vh'' l1).
    split.
    replace ( vh_decrease
                match Hn in (_ = w) return (valid_holed w) with
                | Logic.eq_refl => VH_handler l l0 vh l1
                end )
      with  ( match Hm in _ = w return option (valid_holed w) with
              | Logic.eq_refl => vh_decrease (VH_handler l l0 vh l1) end) ;
      last by rewrite Hproof ; destruct Hm.
    simpl.
    replace (  match Hm in (_ = w) return (option (valid_holed w)) with
               | Logic.eq_refl =>
                   match vh_decrease vh with
                   | Some vh'0 => Some (VH_handler l l0 vh'0 l1)
                   | None => None
                   end
               end) with
      (match vh_decrease (match Hn in (_ = w) return (valid_holed w) with
                          | Logic.eq_refl => vh end) with
       | Some vh'0 => Some (VH_handler l l0 vh'0 l1)
       | None => None end) ;
      last by rewrite Hproof ; destruct Hm.
    by rewrite Hdecr'.
    simpl.
    inversion Hvh'.
    apply vh_push_const_inj in Hpush.
    by rewrite Hpush.
Qed.
    
Lemma sh_push_const_app sh vs1 vs2 :
  sh_push_const sh (vs1 ++ vs2) =
    sh_push_const (sh_push_const sh vs2) vs1.
Proof.
  destruct sh => //= ; rewrite catA => //.
Qed.

Lemma vh_push_const_app n (vh : valid_holed n) vs1 vs2 :
  vh_push_const vh (vs1 ++ vs2) =
    vh_push_const (vh_push_const vh vs2) vs1.
Proof.
  destruct vh => //= ; rewrite catA => //.
Qed.

Lemma susfill_sus_push_const i sh vs es:
  susfill i (sus_push_const sh vs) es = v_to_e_list vs ++ susfill i sh es.
Proof.
  destruct sh => //=.
  all: rewrite -v_to_e_cat.
  all: repeat rewrite -cat_app.
  all: repeat rewrite catA //.
Qed.

Lemma susfill_sus_append i sh es' es:
  susfill i (sus_append sh es') es = susfill i sh es ++ es'.
Proof.
  destruct sh => //=.
  all: try (rewrite separate1; symmetry; rewrite separate1).
  all: repeat rewrite -cat_app.
  all: repeat rewrite catA //.
Qed.

Lemma swfill_sw_push_const i sh vs es:
  swfill i (sw_push_const sh vs) es = v_to_e_list vs ++ swfill i sh es.
Proof.
  destruct sh => //=.
  all: rewrite -v_to_e_cat.
  all: repeat rewrite -cat_app.
  all: repeat rewrite catA //.
Qed.

Lemma swfill_sw_append i sh es' es:
  swfill i (sw_append sh es') es = swfill i sh es ++ es'.
Proof.
  destruct sh => //=.
  all: try (rewrite separate1; symmetry; rewrite separate1).
  all: repeat rewrite -cat_app.
  all: repeat rewrite catA //.
Qed.

Lemma exnfill_exn_push_const i sh vs es:
  exnfill i (exn_push_const sh vs) es = v_to_e_list vs ++ exnfill i sh es.
Proof.
  destruct sh => //=.
  all: rewrite -v_to_e_cat.
  all: repeat rewrite -cat_app.
  all: repeat rewrite catA //.
Qed.

Lemma exnfill_exn_append i sh es' es:
  exnfill i (exn_append sh es') es = exnfill i sh es ++ es'.
Proof.
  destruct sh => //=.
  all: try (rewrite separate1; symmetry; rewrite separate1).
  all: repeat rewrite -cat_app.
  all: repeat rewrite catA //.
Qed. 

Lemma sus_push_const_app (sh : susholed) vs1 vs2 :
  sus_push_const sh (vs1 ++ vs2) =
    sus_push_const (sus_push_const sh vs2) vs1.
Proof.
  destruct sh => //=; rewrite catA => //=.
Qed.

Lemma sw_push_const_app (sh : swholed) vs1 vs2 :
  sw_push_const sh (vs1 ++ vs2) =
    sw_push_const (sw_push_const sh vs2) vs1.
Proof.
  destruct sh => //=; rewrite catA => //=.
Qed.

Lemma exn_push_const_app (sh : exnholed) vs1 vs2 :
  exn_push_const sh (vs1 ++ vs2) =
    exn_push_const (exn_push_const sh vs2) vs1.
Proof.
  destruct sh => //=; rewrite catA => //=.
Qed. 

Lemma llh_push_const_app lh vs1 vs2 :
  llh_push_const lh (vs1 ++ vs2) =
    llh_push_const (llh_push_const lh vs2) vs1.
Proof.
  destruct lh => //= ; rewrite catA => //.
Qed.

Lemma sh_push_const_nil sh :
  sh_push_const sh [] = sh.
Proof. destruct sh => //=. Qed.

Lemma vh_push_const_nil n (vh : valid_holed n) :
  vh_push_const vh [] = vh.
Proof. destruct vh => //=. Qed.

Lemma sus_push_const_nil (sh : susholed) :
  sus_push_const sh [] = sh.
Proof. destruct sh => //=. Qed.

Lemma sw_push_const_nil (sh : swholed) :
  sw_push_const sh [] = sh.
Proof. destruct sh => //=. Qed.

Lemma exn_push_const_nil (sh : exnholed) :
  exn_push_const sh [] = sh.
Proof. destruct sh => //=. Qed.

Lemma llh_push_const_nil lh :
  llh_push_const lh [] = lh.
Proof. destruct lh => //=. Qed. 

Lemma sh_append_app sh es1 es2 :
  sh_append sh (es1 ++ es2) =
    sh_append (sh_append sh es1) es2.
Proof.
  destruct sh => //= ; rewrite catA => //.
Qed.

Lemma vh_append_app n (vh : valid_holed n) es1 es2 :
  vh_append vh (es1 ++ es2) =
    vh_append (vh_append vh es1) es2.
Proof.
  destruct vh => //= ; rewrite catA => //.
Qed.

Lemma sus_append_app (sh : susholed) es1 es2 :
  sus_append sh (es1 ++ es2) =
    sus_append (sus_append sh es1) es2.
Proof.
  destruct sh; rewrite /= catA => //.
Qed.

Lemma sw_append_app (sh : swholed) es1 es2 :
  sw_append sh (es1 ++ es2) =
    sw_append (sw_append sh es1) es2.
Proof.
  destruct sh; rewrite /= catA => //.
Qed.

Lemma exn_append_app (sh : exnholed) es1 es2 :
  exn_append sh (es1 ++ es2) =
    exn_append (exn_append sh es1) es2.
Proof.
  destruct sh; rewrite /= catA => //.
Qed. 

Lemma llh_append_app lh es1 es2 :
  llh_append lh (es1 ++ es2) =
    llh_append (llh_append lh es1) es2.
Proof.
  destruct lh => //= ; rewrite catA => //. 
Qed.

Lemma sh_append_nil sh :
  sh_append sh [] = sh.
Proof. destruct sh => /= ; rewrite cats0 => //. Qed.

Lemma vh_append_nil n (vh : valid_holed n) :
  vh_append vh [] = vh.
Proof. destruct vh => /= ; rewrite cats0 => //. Qed.

Lemma sus_append_nil (sh : susholed) :
  sus_append sh [] = sh.
Proof. destruct sh; rewrite /= cats0 => //. Qed.

Lemma sw_append_nil (sh : swholed) :
  sw_append sh [] = sh.
Proof. destruct sh; rewrite /= cats0 => //. Qed.

Lemma exn_append_nil (sh : exnholed) :
  exn_append sh [] = sh.
Proof. destruct sh; rewrite /= cats0 => //. Qed.

Lemma llh_append_nil lh :
  llh_append lh [] = lh.
Proof. destruct lh => /= ; rewrite cats0 => //. Qed. 

Lemma sh_push_const_append sh vs es :
  sh_push_const (sh_append sh es) vs =
    sh_append (sh_push_const sh vs) es.
Proof.
  destruct sh => //=.
Qed.

Lemma vh_push_const_append n (vh : valid_holed n) vs es :
  vh_push_const (vh_append vh es) vs =
    vh_append (vh_push_const vh vs) es.
Proof.
  destruct vh => //=.
Qed.

Lemma sus_push_const_append (sh : susholed) vs es :
  sus_push_const (sus_append sh es) vs =
    sus_append (sus_push_const sh vs) es.
Proof.
  destruct sh => //=.
Qed.

Lemma sw_push_const_append (sh : swholed) vs es :
  sw_push_const (sw_append sh es) vs =
    sw_append (sw_push_const sh vs) es.
Proof.
  destruct sh => //=.
Qed.

Lemma exn_push_const_append (sh : exnholed) vs es :
  exn_push_const (exn_append sh es) vs =
    exn_append (exn_push_const sh vs) es.
Proof.
  destruct sh => //=.
Qed. 

Lemma llh_push_const_append lh vs es :
  llh_push_const (llh_append lh es) vs =
    llh_append (llh_push_const lh vs) es.
Proof.
  destruct lh => //=. 
Qed.

Lemma vfill_increase m (vh : valid_holed m) es :
  vfill (vh_increase vh ) es = vfill vh es.
Proof.
  induction vh => //=.
  all: by rewrite IHvh.
Qed.

Lemma vh_decrease_increase m (vh : valid_holed m) :
  vh_decrease (vh_increase vh) = Some vh.
Proof.
  induction vh => //=.
  all: by rewrite IHvh.
Qed.  

Lemma vh_increase_push_const m (vh : valid_holed m) vs :
  vh_increase (vh_push_const vh vs) = vh_push_const (vh_increase vh) vs.
Proof. destruct vh => //=. Qed.

(* Lemma vh_increase_append m (vh : valid_holed m) vs :
  vh_increase (vh_append vh vs) = vh_append (vh_increase vh) vs.
Proof. destruct vh => //=. Qed. *)

Lemma vh_increase_repeat_push_const m (vh : valid_holed m) vs j :
  vh_increase_repeat (vh_push_const vh vs) j = vh_push_const (vh_increase_repeat vh j) vs.
Proof. induction j => //=. rewrite IHj. by rewrite vh_increase_push_const. Qed.

(* Lemma vh_increase_repeat_append m (vh : valid_holed m) vs j :
  vh_increase_repeat (vh_append vh vs) j = vh_append (vh_increase_repeat vh j) vs.
Proof.
  induction j => //=. rewrite IHj.
  by rewrite vh_increase_append.
Qed. *)

Lemma S_plus m n : S (m + n) = m + S n.
Proof. induction m => //=. by rewrite IHm. Defined.

Lemma vh_increase_repeat_rec m (vh : valid_holed m) bef n es aft j :
  vh_increase_repeat (VH_rec bef n es vh aft) j =
    match S_plus j m in _ = w return valid_holed w with
    | Logic.eq_refl => VH_rec bef n es (vh_increase_repeat vh j) aft end.
Proof.
  induction j ; first done.
  unfold vh_increase_repeat ; fold vh_increase_repeat.
  unfold S_plus ; simpl.
  assert (S_plus j m = S_plus j m) ; first done.
  unfold S_plus in H at 1.
  rewrite H.
  rewrite IHj.
  unfold eq_ind_r, eq_ind.
  set (Hp := S_plus j m).
  clearbody Hp.
  destruct Hp => //=.
Qed.

Lemma vh_increase_repeat_handler m (vh : valid_holed m) bef n aft j :
  vh_increase_repeat (VH_handler bef n vh aft) j =
    VH_handler bef n (vh_increase_repeat vh j) aft .
Proof.
  induction j ; first done.
  unfold vh_increase_repeat ; fold vh_increase_repeat.
  rewrite IHj.
  done.
Qed.

Lemma vh_increase_repeat_prompt m (vh : valid_holed m) bef ts n aft j :
  vh_increase_repeat (VH_prompt bef ts n vh aft) j =
    VH_prompt bef ts n (vh_increase_repeat vh j) aft .
Proof.
  induction j ; first done.
  unfold vh_increase_repeat ; fold vh_increase_repeat.
  rewrite IHj.
  done.
Qed.


Lemma const_list_AI_const l :
  const_list (map AI_const l).
Proof.
  induction l => //=.
  rewrite const_const IHl.
  done.
Qed. 

Lemma hfilled_to_llfill x hh es LI :
  hfilled x hh es LI -> exists llh, llfill llh es = LI.
Proof.
  intros H. move/hfilledP in H.
  induction H.
  all: apply const_es_exists in H as [vs' ->].
  { by exists (LL_base vs' es'). } 
  all: destruct IHhfilledInd as [llh <-].
  - by exists (LL_label vs' n es' llh es''). 
         - by exists (LL_local vs' n f llh es'').
                - by exists (LL_prompt vs' ts hs llh aft).
                       - by exists (LL_handler vs' hs llh aft).
Qed. 

Lemma susfill_to_hfilled i sh es :
  hfilled (Var_prompt_suspend i) (hh_of_sush i sh) es (susfill i sh es).
Proof.
  apply/hfilledP.
  induction sh => //=.
  all: constructor.
  all: try apply v_to_e_is_const_list.
  all: try exact IHsh.
  done.
  clear.
  induction l1 => //=.
  rewrite IHl1.
  destruct i.
  destruct a => //=.
  destruct (n0 <? n) eqn:Hn => //=.
  all: destruct (_ == _) eqn:Habs => //.
  all: move/eqP in Habs.
  apply Nat.ltb_lt in Hn.
  2: apply Nat.ltb_ge in Hn.
  all: inversion Habs; subst.
  all: lia.
Qed.

Lemma swfill_to_hfilled i sh es :
  hfilled (Var_prompt_switch i) (hh_of_swh i sh) es (swfill i sh es).
Proof.
  apply/hfilledP.
  induction sh => //=.
  all: constructor.
  all: try apply v_to_e_is_const_list.
  all: try exact IHsh.
  done.
  clear.
  induction l1 => //=.
  rewrite IHl1.
  destruct i.
  destruct a => //=.
  destruct (n0 <? n) eqn:Hn => //=.
  all: destruct (_ == _) eqn:Habs => //.
  all: move/eqP in Habs.
  apply Nat.ltb_lt in Hn.
  2: apply Nat.ltb_ge in Hn.
  all: inversion Habs; subst.
  all: lia.
Qed.

Lemma exnfill_to_hfilled i sh es :
  hfilled (Var_handler i) (hh_of_exnh i sh) es (exnfill i sh es).
Proof.
  apply/hfilledP.
  induction sh => //=.
  all: constructor.
  all: try apply v_to_e_is_const_list.
  all: try exact IHsh.
  2: done.
  clear.
  induction l0 => //=.
  rewrite IHl0.
  destruct i.
  destruct a => //=.
  all: destruct (n0 <? n) eqn:Hn => //=.
  all: destruct (_ == _) eqn:Habs => //.
  all: move/eqP in Habs.
  1,3: try apply Nat.ltb_lt in Hn.
  3,4: try apply Nat.ltb_ge in Hn.
  all: inversion Habs; subst.
  all: lia.
Qed. 
  

Lemma vfill_to_lfilled i (vh : valid_holed i) es:
  i >= (lh_depth (lh_of_vh vh)) /\
    lfilled (lh_depth (lh_of_vh vh)) (lh_of_vh vh) es (vfill vh es).
Proof.
  induction vh => //=.
  - split ; first lia.
    unfold lfilled, lfill.
    induction l => //=.
    rewrite const_const.
    destruct (const_list _) => //=.
  - destruct IHvh as (Hk & Hfill).
    split ; first lia.
    unfold lfilled, lfill; fold lfill => /=.
    rewrite const_list_AI_const.
    unfold lfilled in Hfill.
    destruct (lfill _ _ _) => //.
    move/eqP in Hfill; subst.
    induction l => //=.
  - destruct IHvh as (Hk & Hfill).
    split ; first lia.
    unfold lfilled, lfill; fold lfill => /=.
    rewrite const_list_AI_const.
    unfold lfilled in Hfill.
    destruct (lfill _ _ _) => //.
    move/eqP in Hfill; subst.
    induction l => //=.
  - destruct IHvh as (Hk & Hfill).
    split ; first lia.
    unfold lfilled, lfill; fold lfill => /=.
    rewrite const_list_AI_const.
    unfold lfilled in Hfill.
    destruct (lfill _ _ _) => //.
    move/eqP in Hfill; subst.
    induction l => //=.
Qed.

Lemma sfill_to_lfilled sh es :
  lfilled (lh_depth (lh_of_sh sh)) (lh_of_sh sh) es (sfill sh es).
Proof.
  induction sh => //=.
  - unfold lfilled, lfill.
    rewrite const_list_AI_const.
    induction l => //=.
  - unfold lfilled, lfill ; fold lfill.
    rewrite const_list_AI_const.
    unfold lfilled in IHsh.
    destruct (lfill _ _ _) => //.
    move/eqP in IHsh; subst.
    induction l => //=.
      - unfold lfilled, lfill ; fold lfill.
    rewrite const_list_AI_const.
    unfold lfilled in IHsh.
    destruct (lfill _ _ _) => //.
    move/eqP in IHsh; subst.
    induction l => //=.
      - unfold lfilled, lfill ; fold lfill.
    rewrite const_list_AI_const.
    unfold lfilled in IHsh.
    destruct (lfill _ _ _) => //.
    move/eqP in IHsh; subst.
    induction l => //=.

Qed.
  
Lemma lfilled_to_vfill k lh es LI i :
  lfilled k lh es LI -> i >= k -> exists vh, vh_of_lh lh i = Some vh /\ vfill vh es = LI.
Proof.
  generalize dependent k ; generalize dependent LI ; generalize dependent i.
  induction lh ; intros i LI k.
  - unfold lfilled, lfill.
    destruct k => //.
    destruct (const_list l) eqn:Hl => //.
    intros HLI _ ; move/eqP in HLI; subst.
    unfold vh_of_lh.
    induction l => /=.
    + exists (VH_base i [] l0) => //=.
    + destruct a => //=.
      destruct b => //=.
      all: rewrite list_extra.cons_app.
      all: rewrite - cat_app.
      all: apply IHl in Hl as (vh & ? & ?).
      all: unfold e_to_v_list_opt in *.
      all: destruct (those _) eqn:Hthose => //.
      all: rewrite map_cat.
      all: erewrite those_app => //=.
      all: eexists ; split => //=.
      all: replace (v_to_e_list l1) with l ; first done.
      all: clear - Hthose.
      all: generalize dependent l1.
      all: induction l => //= ; intros; first by unfold those in Hthose; simpl in Hthose; inversion Hthose.
      all: destruct a => //=.
      all: try destruct b => //=.
      all: rewrite list_extra.cons_app in Hthose.
      all: rewrite - cat_app in Hthose.
      all: apply those_app_inv in Hthose as (tl1 & tl2 & Hv0 & Hthose & Htl) => //.
      all: unfold those in Hv0.
      all: inversion Hv0 ; subst.
      all: erewrite IHl => //=.
  - unfold lfilled, lfill ; fold lfill.
    destruct k => //.
    destruct (const_list l) eqn:Hl => //.
    destruct (lfill _ _ _) eqn:Hfill => //.
    intros HLI Hi ; move/eqP in HLI ; subst.
    destruct i ; first lia.
    assert (i >= k) ; first lia.
    apply (IHlh i l2 k) in H as (vh & Hvh & Hvfill) ;
      last by unfold lfilled ; rewrite Hfill.
    simpl.
    rewrite Hvh.
    induction l => //=.
    + eexists ; split => //=.
      by rewrite Hvfill.
    + destruct a => //=.
      destruct b => //=.
      all: rewrite list_extra.cons_app.
      all: rewrite - cat_app.
      all: specialize (IHl Hl) as (vh0 & Hvh0 & Hvfill0).
      all: unfold e_to_v_list_opt.
      all: rewrite map_cat.
      all: destruct (e_to_v_list_opt l) eqn:Hthose => //.
      all: erewrite those_app => //.
      all: eexists ; split => //=.
      all: inversion Hvh0 ; subst.
      all: simpl in Hvfill0.
      all: by rewrite Hvfill0.
  - unfold lfilled, lfill ; fold lfill.
    destruct (const_list l) eqn:Hl => //.
    destruct (lfill _ _ _) eqn:Hfill => //.
    intros HLI Hi ; move/eqP in HLI ; subst.
    apply (IHlh i l2 k) in Hi as (vh & Hvh & Hvfill) ;
      last by unfold lfilled ; rewrite Hfill.
    simpl.
    rewrite Hvh.
    induction l => //=.
    + eexists ; split => //=.
      by rewrite Hvfill.
    + destruct a => //=.
      destruct b => //=.
      all: rewrite list_extra.cons_app.
      all: rewrite - cat_app.
      all: specialize (IHl Hl) as (vh0 & Hvh0 & Hvfill0).
      all: destruct (e_to_v_list_opt l) eqn:Hthose => //.
      all: rewrite /e_to_v_list_opt map_cat.
      all: erewrite those_app => //.
      all: eexists ; split => //=.
      all: inversion Hvh0 ; subst.
      all: simpl in Hvfill0.
      all: by rewrite Hvfill0.
  - unfold lfilled, lfill ; fold lfill.
    destruct (const_list l) eqn:Hl => //.
    destruct (lfill _ _ _) eqn:Hfill => //.
    intros HLI Hi ; move/eqP in HLI ; subst.
    apply (IHlh i l3 k) in Hi as (vh & Hvh & Hvfill)  ;
      last by unfold lfilled ; rewrite Hfill.
    simpl.
    rewrite Hvh.
    induction l => //=.
    + eexists ; split => //=.
      by rewrite Hvfill.
    + destruct a => //=.
      destruct b => //=.
      all: rewrite list_extra.cons_app.
      all: rewrite - cat_app.
      all: specialize (IHl Hl) as (vh0 & Hvh0 & Hvfill0).
      all: destruct (e_to_v_list_opt l) eqn:Hthose => //.
      all: rewrite /e_to_v_list_opt map_cat.
      all: erewrite those_app => //.
      all: eexists ; split => //=.
      all: inversion Hvh0 ; subst.
      all: simpl in Hvfill0.
      all: by rewrite Hvfill0.
Qed.      

Lemma e_to_v_v_to_e vs :
  e_to_v_list_opt (v_to_e_list vs) = Some vs.
Proof.
  induction vs => //=.
  destruct a => //=.
  2: destruct v => //=.
  all: unfold e_to_v_list_opt => /=.
  all: unfold e_to_v_list_opt in IHvs.
  all: rewrite separate1.
  all: erewrite those_app.
  all: try rewrite separate1.
  all: done.
Qed.


Lemma v_to_e_e_to_v es vs:
  e_to_v_list_opt es = Some vs -> v_to_e_list vs = es.
Proof.
  unfold e_to_v_list_opt, those.
  assert (forall vs',
             match list_extra.those_aux (Some vs') [seq e_to_v_opt i | i <- es] with
             | Some l => Some (rev l)
             | None => None
             end = Some vs → v_to_e_list vs = v_to_e_list (rev vs') ++ es).
  2:{ specialize (H []). done. }
  induction es.
  - intros vs' H. simpl in H. inversion H; subst. by rewrite app_nil_r.
  - intros vs' H. simpl in H.
    destruct (e_to_v_opt a) eqn:Ha => //.
    apply IHes in H.
    simpl in H.
    rewrite -v_to_e_cat in H.
    rewrite -app_assoc in H.
    simpl in H.
    replace a with (AI_const v) => //.
    clear - Ha.
    destruct a => //=.
    destruct b => //=.
    all: simpl in Ha.
    all: inversion Ha; subst => //.
Qed. 
    
    


Lemma lfilled_implies_llfill k lh es LI :
  lfilled k lh es LI ->
  exists llh, llh_of_lh lh = Some llh /\ llfill llh es = LI.
Proof.
  intro Hfill.

  generalize dependent LI ; generalize dependent k ; 
    induction lh ; intros.
  all: unfold lfilled, lfill in Hfill; fold lfill in Hfill.
  1,2 : destruct k => //.
  all: destruct (const_list l) eqn:Hl => //.
  all: try specialize (IHlh k).
  all: try unfold lfilled in IHlh.
  all: try (destruct (lfill _ _ _) as [fill |]; last done).
  all: move/eqP in Hfill; subst LI.
  all: apply const_es_exists in Hl as [vs ->].
  { exists (LL_base vs l0).
    simpl. rewrite e_to_v_v_to_e.
    done. } 
  all: edestruct IHlh as (llh & Hconv & Hllh) => //.
  eexists (LL_label vs n l0 llh l1).
  2: eexists (LL_handler vs l0 llh l1).
  3: eexists (LL_prompt vs l0 l1 llh l2).
  all: simpl.
  all: rewrite e_to_v_v_to_e.
  all: rewrite Hllh.
  all: rewrite Hconv.
  all: done.
Qed.

Lemma llfill_all_values_label lh vs e lh' n0 es vs' LI :
  llfill lh (vs ++ [e]) = LI ->
  llfill lh' [AI_label n0 es vs'] = LI ->
  const_list vs -> (const_list vs' ∨ vs' = [AI_trap]) ->
  (is_const e = false ) ->
  (e <> AI_trap) ->
  (forall n es LI, e <> AI_label n es LI) ->
  (forall n f LI, e <> AI_local n f LI) ->
  (forall hs LI, e <> AI_handler hs LI) ->
  (forall ts hs LI, e <> AI_prompt ts hs LI) ->
  False.
Proof.
  move: LI lh' vs e n0 es vs'.
  induction lh as [bef aft | bef nn l lh IH aft | bef nn l lh IH aft | bef ts hs lh IH aft | bef hs lh IH aft].
  all: intros LI lh' vs e n0 es vs' Hfill Hfill' Hvs Hvs' He He' Hlabe Hloce Hhandlere Hprompte.
  all: simpl in Hfill.
  all: destruct lh' as [bef' aft' | bef' nn' l' lh' aft'  | bef' nn' l' lh' aft' | bef' ts' hs' lh' aft' | bef' hs' lh' aft']. 
  all: simpl in Hfill'.
  all: rewrite - Hfill in Hfill'.
  all: repeat rewrite <- app_assoc in Hfill' => /=.
  1-5: rewrite app_assoc in Hfill'.
  all: apply first_values in Hfill' as (Hbef & Hee & Haft);
    (try done); (try by apply v_to_e_is_const_list);
    (try by apply const_list_concat; try apply v_to_e_is_const_list).
  all: try by subst e; eapply Hlabe.
  all: try by subst e; eapply Hloce.
  all: try by subst e; eapply Hhandlere.
  all: try by subst e; eapply Hprompte.
  all: inversion Hee; subst.
  all: try by eapply IH.
  destruct Hvs'.
  - destruct lh; simpl in H.
    all: repeat apply const_list_split in H as [? H].
    all: try done.
    apply const_list_split in H1 as [? Habs].
    simpl in Habs. rewrite He in Habs. done.
  - destruct lh; simpl in H.
    { destruct l0 => //.
      - destruct vs => //.
        + inversion H; subst; done.
        + inversion H; subst; done.
      - inversion H. destruct v => //.
        destruct v => //. }
    all: destruct l0 => //.
    all: inversion H.
    all: destruct v => //.
    all: destruct v => //. 
Qed. 


Lemma lfilled_all_values_label i lh vs e i' lh' n0 es vs' LI :
  lfilled i lh (vs ++ [e]) LI ->
  lfilled i' lh' [AI_label n0 es vs'] LI ->
  const_list vs -> (const_list vs' ∨ vs' = [AI_trap]) ->
  (is_const e = false ) ->
  e <> AI_trap ->
  (forall n es LI, e <> AI_label n es LI) ->
    (forall hs LI, e <> AI_handler hs LI) ->
  (forall ts hs LI, e <> AI_prompt ts hs LI) ->
  False.
Proof.
   move: LI i i' lh' vs e n0 es vs'.
   induction lh as [bef aft | bef nn l lh IH aft | bef hs lh IH aft | bef ts hs lh IH aft].
  all: intros LI i i' lh' vs e n0 es vs' Hfill Hfill' Hvs Hvs' He He' Hlabe Hhandlere Hprompte.
  all: unfold lfilled, lfill in Hfill; fold lfill in Hfill.
  1, 2: destruct i => //.
  all: destruct (const_list bef) eqn:Hbef => //.
  all: try (destruct (lfill i _ _) eqn:Hfill0; last done).
  all: move/eqP in Hfill; subst LI.
  all: destruct lh' as [bef' aft' | bef' nn' l' lh' aft'  | bef' hs' lh' aft' | bef' ts' hs' lh' aft'].
  all: unfold lfilled, lfill in Hfill'; fold lfill in Hfill'.
  all: try (destruct i'; first done).
  all: try (destruct i'; last done).
  all: destruct (const_list bef') eqn:Hbef' => //.
  all: try (destruct (lfill i' _ _) eqn:Hfill0'; last done).
  all: move/eqP in Hfill'.
  
  all: simpl in Hfill'.
  all: repeat rewrite <- app_assoc in Hfill' => /=.
  1-4: rewrite app_assoc in Hfill'.
  all: apply first_values in Hfill' as (Hbefi & Hee & Hafti);
    (try done); (try by apply v_to_e_is_const_list);
    (try by apply const_list_concat; try apply v_to_e_is_const_list).
  all: try by subst e; eapply Hlabe.
  all: try by subst e; eapply Hhandlere.
  all: try by subst e; eapply Hprompte.
  all: inversion Hee; subst.
  all: try by eapply IH; unfold lfilled;
    (try erewrite Hfill0);
    try erewrite Hfill0'
  .

  destruct Hvs'.
   - destruct lh; simpl in Hfill0.
     1,2 : destruct i => //.
     all: destruct (const_list l) eqn:Hl => //. 
     all: try (destruct (lfill i _ _ ) eqn:Hfill1; last done).
     all: inversion Hfill0; subst vs'.
     all: repeat apply const_list_split in H as [? H].
     all: try done.
     apply const_list_split in H1 as [? Habs].
     simpl in Habs. rewrite He in Habs. done.
   - destruct lh; simpl in Hfill0.
     1,2: destruct i => //.
     all: destruct (const_list l) eqn:Hl => //.
     all: try (destruct (lfill i _ _) ; last done).
     all: inversion Hfill0; subst vs'.
     { destruct l => //.
      - destruct vs => //.
        + inversion Hfill0; subst; done.
        + inversion Hfill0; subst; done.
      - inversion Hfill0. subst a. done. 
     } 
    all: destruct l => //.
     all: inversion Hfill0.
     all: subst a => //. 
Qed. 

Lemma lfilled_all_values_handler i lh vs e i' lh' es vs' LI :
  lfilled i lh (vs ++ [e]) LI ->
  lfilled i' lh' [AI_handler es vs'] LI ->
  const_list vs -> (const_list vs' ∨ vs' = [AI_trap]) ->
  (is_const e = false ) ->
  e <> AI_trap ->
  (forall n es LI, e <> AI_label n es LI) ->
    (forall hs LI, e <> AI_handler hs LI) ->
  (forall ts hs LI, e <> AI_prompt ts hs LI) ->
  False.
Proof.
   move: LI i i' lh' vs e es vs'.
   induction lh as [bef aft | bef nn l lh IH aft | bef hs lh IH aft | bef ts hs lh IH aft].
  all: intros LI i i' lh' vs e es vs' Hfill Hfill' Hvs Hvs' He He' Hlabe Hhandlere Hprompte.
  all: unfold lfilled, lfill in Hfill; fold lfill in Hfill.
  1, 2: destruct i => //.
  all: destruct (const_list bef) eqn:Hbef => //.
  all: try (destruct (lfill i _ _) eqn:Hfill0; last done).
  all: move/eqP in Hfill; subst LI.
  all: destruct lh' as [bef' aft' | bef' nn' l' lh' aft'  | bef' hs' lh' aft' | bef' ts' hs' lh' aft'].
  all: unfold lfilled, lfill in Hfill'; fold lfill in Hfill'.
  all: try (destruct i'; first done).
  all: try (destruct i'; last done).
  all: destruct (const_list bef') eqn:Hbef' => //.
  all: try (destruct (lfill i' _ _) eqn:Hfill0'; last done).
  all: move/eqP in Hfill'.
  
  all: simpl in Hfill'.
  all: repeat rewrite <- app_assoc in Hfill' => /=.
  1-4: rewrite app_assoc in Hfill'.
  all: apply first_values in Hfill' as (Hbefi & Hee & Hafti);
    (try done); (try by apply v_to_e_is_const_list);
    (try by apply const_list_concat; try apply v_to_e_is_const_list).
  all: try by subst e; eapply Hlabe.
  all: try by subst e; eapply Hhandlere.
  all: try by subst e; eapply Hprompte.
  all: inversion Hee; subst.
  all: try by eapply IH; unfold lfilled;
    (try erewrite Hfill0);
    try erewrite Hfill0'
  .

  destruct Hvs'.
   - destruct lh; simpl in Hfill0.
     1,2 : destruct i => //.
     all: destruct (const_list l) eqn:Hl => //. 
     all: try (destruct (lfill i _ _ ) eqn:Hfill1; last done).
     all: inversion Hfill0; subst vs'.
     all: repeat apply const_list_split in H as [? H].
     all: try done.
     apply const_list_split in H1 as [? Habs].
     simpl in Habs. rewrite He in Habs. done.
   - destruct lh; simpl in Hfill0.
     1,2: destruct i => //.
     all: destruct (const_list l) eqn:Hl => //.
     all: try (destruct (lfill i _ _) ; last done).
     all: inversion Hfill0; subst vs'.
     { destruct l => //.
      - destruct vs => //.
        + inversion Hfill0; subst; done.
        + inversion Hfill0; subst; done.
      - inversion Hfill0. subst a. done. 
     } 
    all: destruct l => //.
     all: inversion Hfill0.
     all: subst a => //. 
Qed. 

Lemma lfilled_all_values_prompt i lh vs e i' lh' n0 es vs' LI :
  lfilled i lh (vs ++ [e]) LI ->
  lfilled i' lh' [AI_prompt n0 es vs'] LI ->
  const_list vs -> (const_list vs' ∨ vs' = [AI_trap]) ->
  (is_const e = false ) ->
  e <> AI_trap ->
  (forall n es LI, e <> AI_label n es LI) ->
    (forall hs LI, e <> AI_handler hs LI) ->
  (forall ts hs LI, e <> AI_prompt ts hs LI) ->
  False.
Proof.
   move: LI i i' lh' vs e n0 es vs'.
   induction lh as [bef aft | bef nn l lh IH aft | bef hs lh IH aft | bef ts hs lh IH aft].
  all: intros LI i i' lh' vs e n0 es vs' Hfill Hfill' Hvs Hvs' He He' Hlabe Hhandlere Hprompte.
  all: unfold lfilled, lfill in Hfill; fold lfill in Hfill.
  1, 2: destruct i => //.
  all: destruct (const_list bef) eqn:Hbef => //.
  all: try (destruct (lfill i _ _) eqn:Hfill0; last done).
  all: move/eqP in Hfill; subst LI.
  all: destruct lh' as [bef' aft' | bef' nn' l' lh' aft'  | bef' hs' lh' aft' | bef' ts' hs' lh' aft'].
  all: unfold lfilled, lfill in Hfill'; fold lfill in Hfill'.
  all: try (destruct i'; first done).
  all: try (destruct i'; last done).
  all: destruct (const_list bef') eqn:Hbef' => //.
  all: try (destruct (lfill i' _ _) eqn:Hfill0'; last done).
  all: move/eqP in Hfill'.
  
  all: simpl in Hfill'.
  all: repeat rewrite <- app_assoc in Hfill' => /=.
  1-4: rewrite app_assoc in Hfill'.
  all: apply first_values in Hfill' as (Hbefi & Hee & Hafti);
    (try done); (try by apply v_to_e_is_const_list);
    (try by apply const_list_concat; try apply v_to_e_is_const_list).
  all: try by subst e; eapply Hlabe.
  all: try by subst e; eapply Hhandlere.
  all: try by subst e; eapply Hprompte.
  all: inversion Hee; subst.
  all: try by eapply IH; unfold lfilled;
    (try erewrite Hfill0);
    try erewrite Hfill0'
  .

  destruct Hvs'.
   - destruct lh; simpl in Hfill0.
     1,2 : destruct i => //.
     all: destruct (const_list l) eqn:Hl => //. 
     all: try (destruct (lfill i _ _ ) eqn:Hfill1; last done).
     all: inversion Hfill0; subst vs'.
     all: repeat apply const_list_split in H as [? H].
     all: try done.
     apply const_list_split in H1 as [? Habs].
     simpl in Habs. rewrite He in Habs. done.
   - destruct lh; simpl in Hfill0.
     1,2: destruct i => //.
     all: destruct (const_list l) eqn:Hl => //.
     all: try (destruct (lfill i _ _) ; last done).
     all: inversion Hfill0; subst vs'.
     { destruct l => //.
      - destruct vs => //.
        + inversion Hfill0; subst; done.
        + inversion Hfill0; subst; done.
      - inversion Hfill0. subst a. done. 
     } 
    all: destruct l => //.
     all: inversion Hfill0.
     all: subst a => //. 
Qed. 


Lemma llfill_all_values_local lh vs e lh' n0 es vs' LI :
  llfill lh (vs ++ [e]) = LI ->
  llfill lh' [AI_local n0 es vs'] = LI ->
  const_list vs -> (const_list vs' ∨ vs' = [AI_trap]) ->
  (is_const e = false ) ->
  e <> AI_trap ->
  (forall n es LI, e <> AI_label n es LI) ->
  (forall n f LI, e <> AI_local n f LI) ->
    (forall hs LI, e <> AI_handler hs LI) ->
  (forall ts hs LI, e <> AI_prompt ts hs LI) ->
  False.
Proof.
  move: LI lh' vs e n0 es vs'.
  induction lh as [bef aft | bef nn l lh IH aft | bef nn l lh IH aft | bef ts hs lh IH aft | bef hs lh IH aft].
  all: intros LI lh' vs e n0 es vs' Hfill Hfill' Hvs Hvs' He He' Hlabe Hloce Hhandlere Hprompte.
  all: simpl in Hfill.
  all: destruct lh' as [bef' aft' | bef' nn' l' lh' aft'  | bef' nn' l' lh' aft' | bef' ts' hs' lh' aft' | bef' hs' lh' aft']. 
  all: simpl in Hfill'.
  all: rewrite - Hfill in Hfill'.
  all: repeat rewrite <- app_assoc in Hfill' => /=.
  1-5: rewrite app_assoc in Hfill'.
  all: apply first_values in Hfill' as (Hbef & Hee & Haft);
    (try done); (try by apply v_to_e_is_const_list);
    (try by apply const_list_concat; try apply v_to_e_is_const_list).
  all: try by subst e; eapply Hlabe.
  all: try by subst e; eapply Hloce.
  all: try by subst e; eapply Hhandlere.
  all: try by subst e; eapply Hprompte.
  all: inversion Hee; subst.
  all: try by eapply IH.
  destruct Hvs'.
  - destruct lh; simpl in H.
    all: repeat apply const_list_split in H as [? H].
    all: try done.
    apply const_list_split in H1 as [? Habs].
    simpl in Habs. rewrite He in Habs. done.
  - destruct lh; simpl in H.
    { destruct l0 => //.
      - destruct vs => //.
        + inversion H; subst; done.
        + inversion H; subst; done.
      - inversion H. destruct v => //.
        destruct v => //. }
    all: destruct l0 => //.
    all: inversion H.
    all: destruct v => //.
    all: destruct v => //. 
Qed.


Lemma llfill_all_values_prompt lh vs e lh' n0 es vs' LI :
  llfill lh (vs ++ [e]) = LI ->
  llfill lh' [AI_prompt n0 es vs'] = LI ->
  const_list vs -> (const_list vs' ∨ vs' = [AI_trap]) ->
  (is_const e = false ) ->
  e <> AI_trap ->
  (forall n es LI, e <> AI_label n es LI) ->
  (forall n f LI, e <> AI_local n f LI) ->
    (forall hs LI, e <> AI_handler hs LI) ->
  (forall ts hs LI, e <> AI_prompt ts hs LI) ->
  False.
Proof.
  move: LI lh' vs e n0 es vs'.
  induction lh as [bef aft | bef nn l lh IH aft | bef nn l lh IH aft | bef ts hs lh IH aft | bef hs lh IH aft].
  all: intros LI lh' vs e n0 es vs' Hfill Hfill' Hvs Hvs' He He' Hlabe Hloce Hhandlere Hprompte.
  all: simpl in Hfill.
  all: destruct lh' as [bef' aft' | bef' nn' l' lh' aft'  | bef' nn' l' lh' aft' | bef' ts' hs' lh' aft' | bef' hs' lh' aft']. 
  all: simpl in Hfill'.
  all: rewrite - Hfill in Hfill'.
  all: repeat rewrite <- app_assoc in Hfill' => /=.
  1-5: rewrite app_assoc in Hfill'.
  all: apply first_values in Hfill' as (Hbef & Hee & Haft);
    (try done); (try by apply v_to_e_is_const_list);
    (try by apply const_list_concat; try apply v_to_e_is_const_list).
  all: try by subst e; eapply Hlabe.
  all: try by subst e; eapply Hloce.
  all: try by subst e; eapply Hhandlere.
  all: try by subst e; eapply Hprompte.
  all: inversion Hee; subst.
  all: try by eapply IH.
  destruct Hvs'.
  - destruct lh; simpl in H.
    all: repeat apply const_list_split in H as [? H].
    all: try done.
    apply const_list_split in H1 as [? Habs].
    simpl in Habs. rewrite He in Habs. done.
  - destruct lh; simpl in H.
    { destruct l => //.
      - destruct vs => //.
        + inversion H; subst; done.
        + inversion H; subst; done.
      - inversion H. destruct v => //.
        destruct v => //. }
    all: destruct l => //.
    all: inversion H.
    all: destruct v => //.
    all: destruct v => //. 
Qed. 

Lemma llfill_all_values_handler lh vs e lh' es vs' LI :
  llfill lh (vs ++ [e]) = LI ->
  llfill lh' [AI_handler es vs'] = LI ->
  const_list vs -> (const_list vs' ∨ vs' = [AI_trap]) ->
  (is_const e = false ) ->
  e <> AI_trap ->
  (forall n es LI, e <> AI_label n es LI) ->
  (forall n f LI, e <> AI_local n f LI) ->
    (forall hs LI, e <> AI_handler hs LI) ->
  (forall ts hs LI, e <> AI_prompt ts hs LI) ->
  False.
Proof.
  move: LI lh' vs e es vs'.
  induction lh as [bef aft | bef nn l lh IH aft | bef nn l lh IH aft | bef ts hs lh IH aft | bef hs lh IH aft].
  all: intros LI lh' vs e es vs' Hfill Hfill' Hvs Hvs' He He' Hlabe Hloce Hhandlere Hprompte.
  all: simpl in Hfill.
  all: destruct lh' as [bef' aft' | bef' nn' l' lh' aft'  | bef' nn' l' lh' aft' | bef' ts' hs' lh' aft' | bef' hs' lh' aft']. 
  all: simpl in Hfill'.
  all: rewrite - Hfill in Hfill'.
  all: repeat rewrite <- app_assoc in Hfill' => /=.
  1-5: rewrite app_assoc in Hfill'.
  all: apply first_values in Hfill' as (Hbef & Hee & Haft);
    (try done); (try by apply v_to_e_is_const_list);
    (try by apply const_list_concat; try apply v_to_e_is_const_list).
  all: try by subst e; eapply Hlabe.
  all: try by subst e; eapply Hloce.
  all: try by subst e; eapply Hhandlere.
  all: try by subst e; eapply Hprompte.
  all: inversion Hee; subst.
  all: try by eapply IH.
  destruct Hvs'.
  - destruct lh; simpl in H.
    all: repeat apply const_list_split in H as [? H].
    all: try done.
    apply const_list_split in H1 as [? Habs].
    simpl in Habs. rewrite He in Habs. done.
  - destruct lh; simpl in H.
    { destruct l => //.
      - destruct vs => //.
        + inversion H; subst; done.
        + inversion H; subst; done.
      - inversion H. destruct v => //.
        destruct v => //. }
    all: destruct l => //.
    all: inversion H.
    all: destruct v => //.
    all: destruct v => //. 
Qed. 

Lemma hfilled_to_lfilled x hh es LI :
  hfilled x hh es LI ->
  (exists k lh, lfilled k lh es LI) \/
    (exists k lh n f LI',
        lfilled k lh [::AI_local n f LI'] LI).
Proof.
  intros H. move/hfilledP in H.
  generalize dependent LI.
  induction hh; intros LI H; inversion H; subst.
  - left. exists 0, (LH_base l l0).
    unfold lfilled, lfill.
    rewrite H5 => //.
  - apply IHhh in H9 as [(k & lh & Hlh) | (k & lh & n0 & f & LI' & Hlh)].
    left. 2: right.
    all: eexists (S k), (LH_rec l n l0 lh l1).
    2: eexists n0, f, LI'.
    all: unfold lfilled, lfill; fold lfill.
    all: rewrite H8.
    all: unfold lfilled in Hlh.
    all: destruct (lfill _ _ _) => //.
    all: move/eqP in Hlh; subst l2.
    all: done.
  - right. exists 0, (LH_base l l0), n, f, LI0.
    unfold lfilled, lfill. rewrite H8 => //.
  - apply IHhh in H9 as [(k & lh & Hlh) | (k & lh & n0 & f & LI' & Hlh)].
    left. 2: right.
    all: eexists k, (LH_handler l l0 lh l1).
    2: eexists n0, f, LI'.
    all: unfold lfilled, lfill; fold lfill.
    all: rewrite H7.
    all: unfold lfilled in Hlh.
    all: destruct (lfill _ _ _) => //.
    all: move/eqP in Hlh; subst l2.
    all: done.
  - apply IHhh in H10 as [(k & lh & Hlh) | (k & lh & n0 & f & LI' & Hlh)].
    left. 2: right.
    all: eexists k, (LH_prompt l l0 l1 lh l2).
    2: eexists n0, f, LI'.
    all: unfold lfilled, lfill; fold lfill.
    all: rewrite H8.
    all: unfold lfilled in Hlh.
    all: destruct (lfill _ _ _) => //.
    all: move/eqP in Hlh; subst l3.
    all: done.
Qed.

(*
Lemma hfilled_to_llfill x hh es LI :
  hfilled x hh es LI ->
  exists lh, llfill lh es = LI.

Proof.
  intros H. move/hfilledP in H.
  generalize dependent LI. generalize dependent x.
  induction hh; intros x LI H; inversion H; subst.
  - apply const_es_exists in H5 as [vs ->].
    exists (LL_base vs l0). simpl. done.
  - apply IHhh in H9 as [lh <-].
    apply const_es_exists in H8 as [vs ->].
    exists (LL_label vs n l0 lh l1).
    done.
  - apply IHhh in H9 as [lh <-]. 
    apply const_es_exists in H8 as [vs ->].
    exists (LL_local vs n f lh l0).
    done.
  - apply IHhh in H9 as [lh <-]. 
    apply const_es_exists in H7 as [vs ->].
    exists (LL_handler vs l0 lh l1).
    done.
  - apply IHhh in H10 as [lh <-]. 
    apply const_es_exists in H8 as [vs ->].
    exists (LL_prompt vs l0 l1 lh l2).
    done.
Qed.
*)


Lemma lfilled_br_and_reduce s f es LI s' f' es' i j lh vs k lh' :
  reduce s f es s' f' es' ->
  const_list vs ->
  i <= j ->
  lfilled i lh (vs ++ [AI_basic (BI_br j)]) LI ->
  lfilled k lh' es LI ->
  False.
Proof.
  intros Hred Hvs Hi H1 Hes.
  cut (forall n, length_rec es < n -> False).
  { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
  intro n0. 
  generalize dependent es. generalize dependent es'.  generalize dependent k.
  generalize dependent lh'.
  induction n0 ; intros lh1 k es' es1 Hred2 Hfill Hlab ; first by lia.
  induction Hred2 ; try by (rewrite_cats1_list; specialize (lfilled_first_values H1 Hfill) as [Hcontra _] => //= ;
                                                                                                            (try subst; apply v_to_e_is_const_list);                                                              repeat rewrite const_const).
  (* reduce_simple *)
  { destruct H; try by (rewrite_cats1_list; specialize (lfilled_first_values H1 Hfill) as [Hcontra _] => //=; repeat rewrite const_const). 
    - (* ref_is_null *)
      rewrite_cats1_list.
      specialize (lfilled_first_values H1 Hfill) as [Habs _] => //. simpl. destruct ref => //. 
    - (* prompt *)
      apply (lfilled_all_values_prompt H1 Hfill) => //=.
      by left.
    - (* handler *)
      apply (lfilled_all_values_handler H1 Hfill) => //=.
      by left.
    - (* handler trap *)
      apply (lfilled_all_values_handler H1 Hfill) => //.
      by right.
    - (* prompt trap *)
      apply (lfilled_all_values_prompt H1 Hfill) => //.
      by right.

    (* const *)
    - apply (lfilled_all_values_label H1 Hfill) => //=.
      by left. 
    - apply (lfilled_all_values_label H1 Hfill) => //=. by right.
    (* br itself *)
    - assert (lfilled (S i0) (LH_rec [] n es lh0 []) (vs0 ++ [AI_basic (BI_br i0)])
                [AI_label n es LI0]) as Hfill'.
      unfold lfilled, lfill ; fold lfill => //=.
      unfold lfilled in H2. destruct (lfill i0 _ _) => //. 
      move/eqP in H2 ; by subst.
      destruct (lfilled_trans Hfill' Hfill) as [lh' Hfillbr].
      specialize (lfilled_first_values H1 Hfillbr) as (? & ? & ?) => //=.
      inversion H3 ; subst. lia.
    (* tee_local *)
    - replace [v ; AI_basic (BI_tee_local i0)] with
        ([v] ++ [AI_basic (BI_tee_local i0)])%SEQ in Hfill => //=.
      assert (AI_basic (BI_br j) = AI_basic (BI_tee_local i0)) => //=.
      apply (lfilled_first_values H1 Hfill) => //=.
      by rewrite H.
    (* trap *)
    - destruct (lfilled_trans H0 Hfill) as [lh' Hfill'].
      replace [AI_trap] with ([] ++ [AI_trap])%SEQ in Hfill' => //=.
      assert (AI_basic (BI_br j) = AI_trap) => //=.
      apply (lfilled_first_values H1 Hfill') => //=.
  }
  - (* throw_ref *)
        assert (lfilled 0 (LH_handler [::] hs (LH_base [::] [::]) [::]) LI0 [::AI_handler hs LI0]) as Hfill0.
    { unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r. }
    destruct (lfilled_trans Hfill0 Hfill) as [lh0 Hfill1].
    apply hfilled_to_lfilled in H as [(k' & lh' & Hlh) | (k' & lh' & n & f' & LI' & Hlh)].
    all: destruct (lfilled_trans Hlh Hfill1) as [lh2 Hfill'].
    all: rewrite_cats1_list.
    all: specialize (lfilled_first_values H1 Hfill') as [Habs _] => //. 
  - (* throw_ref_ref *)
    assert (lfilled 0 (LH_handler [::] hs (LH_base [::] [::]) [::]) LI0 [::AI_handler hs LI0]) as Hfill0.
    { unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r. }
    destruct (lfilled_trans Hfill0 Hfill) as [lh0 Hfill1].
    apply hfilled_to_lfilled in H as [(k' & lh' & Hlh) | (k' & lh' & n & f' & LI' & Hlh)].
    all: destruct (lfilled_trans Hlh Hfill1) as [lh2 Hfill'].
    all: rewrite_cats1_list.
    all: specialize (lfilled_first_values H1 Hfill') as [Habs _] => //. 
  - (* resume *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //.
    apply const_list_concat => //. 
  - (* switch *)
    rewrite separate1 in Hfill.
    rewrite -cat_app catA in Hfill.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
    apply v_to_e_is_const_list.
  - (* suspend *)
    assert (lfilled 0 (LH_prompt [::] ts hs (LH_base [::] [::]) [::]) LI0 [::AI_prompt ts hs LI0]) as Hfill0.
    { unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r. }
    destruct (lfilled_trans Hfill0 Hfill) as [lh0 Hfill1].
    apply hfilled_to_lfilled in H3 as [(k' & lh' & Hlh) | (k' & lh' & n & f' & LI' & Hlh)].
    all: destruct (lfilled_trans Hlh Hfill1) as [lh2 Hfill'].
    all: rewrite_cats1_list. 
    all: specialize (lfilled_first_values H1 Hfill') as [Habs _] => //. 
  - (* switch *)
    assert (lfilled 0 (LH_prompt [::] ts hs (LH_base [::] [::]) [::]) LI0 [::AI_prompt ts hs LI0]) as Hfill0.
    { unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r. }
    destruct (lfilled_trans Hfill0 Hfill) as [lh0 Hfill1].
    apply hfilled_to_lfilled in H3 as [(k' & lh' & Hlh) | (k' & lh' & n & f' & LI'' & Hlh)].
    all: destruct (lfilled_trans Hlh Hfill1) as [lh2 Hfill'].
    2: rewrite_cats1_list. 
    rewrite - (cat0s [::_]) in Hfill'.
    all: specialize (lfilled_first_values H1 Hfill') as [Habs _] => //.
  - (* contbind *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //.
    apply const_list_concat => //. 
  - (* resume_throw *)
        rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
    subst; apply v_to_e_is_const_list.
  - (* set_local *)
    rewrite_cats1_list.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //=. repeat rewrite const_const. done.
(*
  - (* set_global *)
    rewrite_cats1_list.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //=. repeat rewrite const_const. done. *)
  - (* label *)
    destruct (lfilled_trans H Hfill) as [lh' Hfill'].
    apply length_lfilled_rec' in H as [H | (-> & -> & ->)].
    + apply (IHn0 _ _ _ _ Hred2 Hfill') => //. lias.
    + unfold lfilled, lfill in H0; simpl in H0.
      move/eqP in H0; subst.
      exfalso ; apply IHHred2 => //=.
Qed. 


Lemma lfilled_return_and_reduce s f es LI s' f' es' i lh vs k lh' :
  reduce s f es s' f' es' ->
  const_list vs ->
  lfilled i lh (vs ++ [AI_basic BI_return]) LI ->
  lfilled k lh' es LI ->
  False.
Proof.
  intros Hred Hvs H1 Hes.
  cut (forall n, length_rec es < n -> False).
  { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
  intro n0. 
  generalize dependent es. generalize dependent es'. generalize dependent k.
  generalize dependent lh'.
  induction n0 ; intros lh1 k es' es1 Hred2 Hfill Hlab ; first by lia.
  induction Hred2; try by (rewrite_cats1_list; specialize (lfilled_first_values H1 Hfill) as [Hcontra _] => //;  (try subst; apply v_to_e_is_const_list);                                                              repeat rewrite const_const). 
  (* r_simple *)
  { destruct H; try by (rewrite_cats1_list; specialize (lfilled_first_values H1 Hfill) as [Hcontra _] => //=; repeat rewrite const_const).
    - rewrite_cats1_list.
      specialize (lfilled_first_values H1 Hfill) as [? _] => //=.
      destruct ref => //.
    - apply (lfilled_all_values_prompt H1 Hfill) => //=;try by intros [? ?].
      by left.
    - apply (lfilled_all_values_handler H1 Hfill) => //=;try by intros [? ?].
      by left.
    - apply (lfilled_all_values_handler H1 Hfill) => //. by right.

    - (* prompt trap *)
      apply (lfilled_all_values_prompt H1 Hfill) => //=.
      by right.

    - apply (lfilled_all_values_label H1 Hfill) => //=. by left. 
    - apply (lfilled_all_values_label H1 Hfill) => //=. by right. 
    - assert (lfilled (S i0) (LH_rec [] n es lh0 []) (vs0 ++ [AI_basic (BI_br i0)])
                [AI_label n es LI0]) as Hfill'.
      unfold lfilled, lfill ; fold lfill => //=.
      unfold lfilled in H2. destruct (lfill i0 _ _) => //. 
      move/eqP in H2 ; by subst.
      destruct (lfilled_trans Hfill' Hfill) as [lh' Hfillbr].
      specialize (lfilled_first_values H1 Hfillbr) as (? & ? & ?) => //=.
    - replace [v ; AI_basic (BI_tee_local i0)] with
        ([v] ++ [AI_basic (BI_tee_local i0)])%SEQ in Hfill => //=.
      assert (AI_basic BI_return = AI_basic (BI_tee_local i0)) => //=.
      apply (lfilled_first_values H1 Hfill) => //=.
      by rewrite H.
    - destruct (lfilled_trans H0 Hfill) as [lh' Hfill'].
      replace [AI_trap] with ([] ++ [AI_trap])%SEQ in Hfill' => //=.
      assert (AI_basic BI_return = AI_trap) => //=.
      apply (lfilled_first_values H1 Hfill') => //=. }
   - (* throw_ref *)
     assert (lfilled 0 (LH_handler [::] hs (LH_base [::] [::]) [::]) LI0 [::AI_handler hs LI0]) as Hfill0.
    { unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r. }
    destruct (lfilled_trans Hfill0 Hfill) as [lh0 Hfill1].
    apply hfilled_to_lfilled in H as [(k' & lh' & Hlh) | (k' & lh' & n & f' & LI' & Hlh)].
    all: destruct (lfilled_trans Hlh Hfill1) as [lh2 Hfill'].
    all: rewrite_cats1_list.
    all: specialize (lfilled_first_values H1 Hfill') as [Habs _] => //. 
  - (* throw_ref_ref *)
            assert (lfilled 0 (LH_handler [::] hs (LH_base [::] [::]) [::]) LI0 [::AI_handler hs LI0]) as Hfill0.
    { unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r. }
    destruct (lfilled_trans Hfill0 Hfill) as [lh0 Hfill1].
    apply hfilled_to_lfilled in H as [(k' & lh' & Hlh) | (k' & lh' & n & f' & LI' & Hlh)].
    all: destruct (lfilled_trans Hlh Hfill1) as [lh2 Hfill'].
    all: rewrite_cats1_list.
    all: specialize (lfilled_first_values H1 Hfill') as [Habs _] => //. 
  - (* resume *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //.
    apply const_list_concat => //. 
  - (* switch *)
    rewrite separate1 -cat_app catA in Hfill.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
    apply v_to_e_is_const_list.
  - (* suspend *)
    assert (lfilled 0 (LH_prompt [::] ts hs (LH_base [::] [::]) [::]) LI0 [::AI_prompt ts hs LI0]) as Hfill0.
    { unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r. }
    destruct (lfilled_trans Hfill0 Hfill) as [lh0 Hfill1].
    apply hfilled_to_lfilled in H3 as [(k' & lh' & Hlh) | (k' & lh' & n & f' & LI' & Hlh)].
    all: destruct (lfilled_trans Hlh Hfill1) as [lh2 Hfill'].
    all: rewrite_cats1_list. 
    all: specialize (lfilled_first_values H1 Hfill') as [Habs _] => //.
     - (* switch *)
    assert (lfilled 0 (LH_prompt [::] ts hs (LH_base [::] [::]) [::]) LI0 [::AI_prompt ts hs LI0]) as Hfill0.
    { unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r. }
    destruct (lfilled_trans Hfill0 Hfill) as [lh0 Hfill1].
    apply hfilled_to_lfilled in H3 as [(k' & lh' & Hlh) | (k' & lh' & n & f' & LI'' & Hlh)].
    all: destruct (lfilled_trans Hlh Hfill1) as [lh2 Hfill'].
    2: rewrite_cats1_list. 
    rewrite - (cat0s [:: _]) in Hfill'.
    all: specialize (lfilled_first_values H1 Hfill') as [Habs _] => //.
     - (* contbind *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //.
    apply const_list_concat => //. 
  - (* resume_throw *)
        rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
    subst; apply v_to_e_is_const_list.
  - (* set_local *)
    rewrite_cats1_list.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //=. repeat rewrite const_const. done.

(*  - (* set_global *)
        rewrite_cats1_list.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //=. repeat rewrite const_const. done. *)
  - (* label *)
    destruct (lfilled_trans H Hfill) as [lh' Hfill'].
    apply length_lfilled_rec' in H as [H | (-> & -> & ->)].
    + apply (IHn0 _ _ _ _ Hred2 Hfill') => //. lias.
    + unfold lfilled, lfill in H0; simpl in H0.
      move/eqP in H0; subst.
      exfalso ; apply IHHred2 => //=.
Qed. 


Lemma llfill_first_values lh vs e lh' vs' e' LI :
  llfill lh (vs ++ [::e]) = LI ->
  llfill lh' (vs' ++ [::e']) = LI ->
  const_list vs -> const_list vs' ->
  (is_const e = false) -> (is_const e' = false) ->
  (forall n es LI, e <> AI_label n es LI) ->
  (forall n es LI, e' <> AI_label n es LI) ->
  (forall n f LI, e <> AI_local n f LI) ->
  (forall n f LI, e' <> AI_local n f LI) ->
  (forall hs LI, e <> AI_handler hs LI) ->
  (forall hs LI, e' <> AI_handler hs LI) ->
  (forall ts hs LI, e <> AI_prompt ts hs LI) ->
  (forall ts hs LI, e' <> AI_prompt ts hs LI) ->
  e = e' /\ (length vs = length vs' -> (vs = vs' /\ lh = lh')).
Proof.
  move: vs e lh' vs' e' LI.
  induction lh as [ bef aft | bef nn l lh IH aft | bef nn l lh IH aft | bef ts hs lh IH aft | bef hs lh IH aft ].
  all: intros vs e lh' vs' e' LI Hfill Hfill' Hvs Hvs' He He' Hlabe Hlabe' Hloce Hloce' Hhandlere Hhandlere' Hprompte Hprompte'.
  all: simpl in Hfill.
  all: destruct lh' as [bef' aft' | bef' nn' l' lh' aft' | bef' nn' l' lh' aft' | bef' ts' hs' lh' aft' | bef' hs' lh' aft' ].
  all: rewrite - Hfill in Hfill'.
  all: simpl in Hfill'.
  all: repeat rewrite app_assoc in Hfill'.
  all: try rewrite - (app_assoc (v_to_e_list bef' ++ _)) in Hfill'.
  all: try rewrite - (app_assoc (v_to_e_list bef ++ _)) in Hfill'.
  all: apply first_values in Hfill' as (Hvvs & Hee & ?);
    (try apply const_list_concat); (try done) ; try apply v_to_e_is_const_list.
  all: subst.
  all: try by exfalso; eapply Hlabe.
  all: try by exfalso; eapply Hlabe'.
  all: try by exfalso; eapply Hloce.
  all: try by exfalso; eapply Hloce'.
  all: try by exfalso; eapply Hhandlere.
  all: try by exfalso; eapply Hhandlere'.
  all: try by exfalso; eapply Hprompte.
  all: try by exfalso; eapply Hprompte'.

  { split => //. 
    intro H0.
    repeat rewrite cat_app in Hvvs.
    apply Logic.eq_sym in Hvvs.
    apply app_inj_2 in Hvvs as [Hbef ->] => //.
    apply v_to_e_inj in Hbef as ->. by subst. }
  all: inversion Hee; subst.
  all: destruct (IH vs e lh' vs' e' (llfill lh (vs ++ [e]))) as [Hres Hlen] => //.
  all: split => //.
  all: intros Hlenvs.
  all: apply Hlen in Hlenvs as [-> ->].
  all: apply v_to_e_inj in Hvvs as ->.
  all: done.
Qed.  


Lemma lfilled_llfill_first_values i lh vs e lh' vs' e' LI :
  lfilled i lh (vs ++ [::e]) LI ->
  llfill lh' (vs' ++ [::e']) = LI ->
  const_list vs -> const_list vs' ->
  (is_const e = false) -> (is_const e' = false) ->
  (forall n es LI, e <> AI_label n es LI) ->
  (forall n es LI, e' <> AI_label n es LI) ->
  (forall n f LI, e <> AI_local n f LI) ->
    (forall hs LI, e <> AI_handler hs LI) ->
  (forall hs LI, e' <> AI_handler hs LI) ->
  (forall ts hs LI, e <> AI_prompt ts hs LI) ->
  (forall ts hs LI, e' <> AI_prompt ts hs LI) ->
  e = e' /\ (length vs = length vs' -> (vs = vs')).
Proof.
  move: i vs e lh' vs' e' LI.
  induction lh as [bef aft | bef nn esc lh IH aft | bef hs lh IH aft | bef ts hs lh IH aft].
  all: intros i vs e lh' vs' e' LI Hfill Hfill' Hvs Hvs' He He' Hlabe Hlabe' Hloce Hhandlere Hhandlere' Hprompte Hprompte'.
  all: unfold lfilled, lfill in Hfill; fold lfill in Hfill.
  1,2: destruct i.
  all: destruct (const_list bef) eqn:Hbef => //.
  all: try (destruct (lfill _ _ _) eqn:Hfill0; last done).
  all: move/eqP in Hfill.
  all: destruct lh' as [bef' aft' | bef' nn' esc' lh' aft' | bef' nn' f' lh' aft' | bef' ts' hs' lh' aft' | bef' hs' lh' aft' ].
  all: rewrite Hfill in Hfill'.
  all: simpl in Hfill'.
  all: repeat rewrite app_assoc in Hfill'.
  all: try rewrite - (app_assoc (v_to_e_list bef' ++ _)) in Hfill'.
  all: try rewrite - (app_assoc (bef ++ _)) in Hfill'.
  all: apply first_values in Hfill' as (Hvvs & Hee & ?) => //=.
  all: try apply const_list_concat.
  all: try done.
  all: try apply v_to_e_is_const_list.
  all: subst.
  all: try by exfalso; eapply Hlabe.
  all: try by exfalso; eapply Hlabe'.
  all: try by exfalso; eapply Hloce.
  all: try by exfalso; eapply Hhandlere.
  all: try by exfalso; eapply Hhandlere'.
  all: try by exfalso; eapply Hprompte.
  all: try by exfalso; eapply Hprompte'.
  split => //. intro H0.
  repeat rewrite cat_app in Hvvs.
  apply Logic.eq_sym in Hvvs.
  apply (app_inj_2 _ _ _ _ H0 Hvvs).
  all: inversion Hee; subst.
  all: eapply IH => //.
  all: unfold lfilled; erewrite Hfill0.
  all: done.
Qed.


Lemma llfill_trans llh1 llh2 es0 es1 es2 :
  llfill llh1 es0 = es1 ->
  llfill llh2 es1 = es2 ->
  exists llh0, llfill llh0 es0 = es2.
Proof.
  intros ; subst.
  generalize dependent es0.
  induction llh2 => /=.
  - exists (llh_push_const (llh_append llh1 l0) l) => /=.
    destruct llh1 ; simpl ; 
      rewrite - v_to_e_cat ; repeat rewrite app_assoc ;
      by rewrite - app_assoc.
  - intro es0.
    destruct (IHllh2 es0) as [llh0 <-].
    exists (LL_label l n l0 llh0 l1) => //=.
  - intro es0.
    destruct (IHllh2 es0) as [llh0 <-].
    exists (LL_local l n f llh0 l0) => //=.
  - intro es0.
    destruct (IHllh2 es0) as [llh0 <-].
    exists (LL_prompt l l0 l1 llh0 l2) => //=.
  - intro es0.
    destruct (IHllh2 es0) as [llh0 <-].
    exists (LL_handler l l0 llh0 l1) => //=. 
Qed.

Lemma lfilled_in_llfill k lh es LI llh LI' :
  lfilled k lh es LI ->
  llfill llh LI = LI' ->
  exists llh', llfill llh' es = LI'.
Proof.
  intros H1 H2.
  apply lfilled_implies_llfill in H1 as (? & _ & H1).
  by specialize (llfill_trans H1 H2). 
Qed. 

Lemma llfill_call_host_and_reduce s f es LI s' f' es' lh lh' tf h cvs vs :
  reduce s f es s' f' es' ->
  const_list vs ->
  llfill lh (vs ++ [AI_call_host tf h cvs]) = LI ->
  llfill lh' es = LI ->
  False.
Proof.
  intros Hred Hvs H1 Hes.
  cut (forall n, length_rec es < n -> False).
  { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
  intro n0. 
  generalize dependent es. generalize dependent es'. 
  generalize dependent lh'. generalize dependent f.
  generalize dependent f'.
  induction n0 ; intros f' f lh1 es' es1 Hred2 Hfill Hlab ; first by lia.
  induction Hred2 ; try by (rewrite_cats1_list; specialize (llfill_first_values Hfill H1) as [Hcontra _] => //=; (try subst; apply v_to_e_is_const_list); repeat rewrite const_const).
  (* r_simple *) 
  { destruct H;
      try by (rewrite_cats1_list;
              specialize (llfill_first_values Hfill H1) as [Hcontra _] ; (try done) ; simpl; repeat rewrite const_const).
    - rewrite_cats1_list.
      specialize (llfill_first_values Hfill H1) as [? _] => //.
      destruct ref => //=.
    - apply (llfill_all_values_prompt H1 Hfill) => //.
      by left.
    - apply (llfill_all_values_handler H1 Hfill) => //. 
      by left.
    - apply (llfill_all_values_handler H1 Hfill) => //.
      by right.
    - apply (llfill_all_values_prompt H1 Hfill) => //.
      by right.
    - apply (llfill_all_values_label H1 Hfill) => //=. 
      by left.
    - apply (llfill_all_values_label H1 Hfill) => //=. by right. 
    - assert (lfilled (S i) (LH_rec [] n es lh0 []) (vs0 ++ [AI_basic (BI_br i)])
                [AI_label n es LI0]) as Hfill'.
      unfold lfilled, lfill ; fold lfill => //=.
      unfold lfilled in H2. destruct (lfill i _ _) => //. 
      move/eqP in H2 ; by subst.
      destruct (lfilled_in_llfill Hfill' Hfill) as [lh' Hfillbr].
      specialize (llfill_first_values Hfillbr H1) as (? & ?) => //=.
    - apply (llfill_all_values_local H1 Hfill) => //=.
      by left.
    - apply (llfill_all_values_local H1 Hfill) => //=.
      by right. 
    - apply lfilled_implies_llfill in H2 as (llh & _ & H2).
      assert (llfill (LL_local [] n f0 llh []) (vs0 ++ [AI_basic BI_return]) = [AI_local n f0 es]) => //=.
      by rewrite H2.
      destruct (llfill_trans H3 Hfill) as [llh' Hfill'].
      edestruct llfill_first_values as [? _].
      exact H1.
      exact Hfill'.
      all : try done.
    - replace [v ; AI_basic (BI_tee_local i)] with
        ([v] ++ [AI_basic (BI_tee_local i)])%SEQ in Hfill => //=.

      destruct (llfill_first_values Hfill H1) as [??] => //=.
      by rewrite H.
    - destruct (lfilled_in_llfill H0 Hfill) as [lh' Hfill'].
      replace [AI_trap] with ([] ++ [AI_trap])%SEQ in Hfill' => //=.
      destruct (llfill_first_values Hfill' H1) as [??] => //=. }
  - (* throw_ref *)
     assert (llfill (LL_handler [::] hs (LL_base [::] [::]) [::]) LI0 = [::AI_handler hs LI0]) as Hfill0.
    { simpl. 
      by rewrite List.app_nil_r. }
    destruct (llfill_trans Hfill0 Hfill) as [lh0 Hfill1].
    apply hfilled_to_llfill in H as [lh' Hlh].
    destruct (llfill_trans Hlh Hfill1) as [lh2 Hfill'].
    rewrite_cats1_list.
    specialize (llfill_first_values H1 Hfill') as [Habs _] => //. 
  - (* throw_ref_ref *)
    assert (llfill (LL_handler [::] hs (LL_base [::] [::]) [::]) LI0 = [::AI_handler hs LI0]) as Hfill0.
    { simpl.
      by rewrite List.app_nil_r. }
    destruct (llfill_trans Hfill0 Hfill) as [lh0 Hfill1].
    apply hfilled_to_llfill in H as [lh' Hlh].
    destruct (llfill_trans Hlh Hfill1) as [lh2 Hfill'].
    rewrite_cats1_list.
    specialize (llfill_first_values H1 Hfill') as [Habs _] => //. 
  - (* resume *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (llfill_first_values H1 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
  - (* switch *)
    rewrite separate1 -cat_app catA in Hfill.
    specialize (llfill_first_values H1 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
    apply v_to_e_is_const_list.

  
  - (* suspend *)
    assert (llfill (LL_prompt [::] ts hs (LL_base [::] [::]) [::]) LI0 = [::AI_prompt ts hs LI0]) as Hfill0.
    { simpl. 
      by rewrite List.app_nil_r. }
    destruct (llfill_trans Hfill0 Hfill) as [lh0 Hfill1].
    apply hfilled_to_llfill in H3 as [lh' Hlh].
    destruct (llfill_trans Hlh Hfill1) as [lh2 Hfill'].
    rewrite_cats1_list. 
    specialize (llfill_first_values H1 Hfill') as [Habs _] => //.
  - (* switch *)
    assert (llfill (LL_prompt [::] ts hs (LL_base [::] [::]) [::]) LI0 = [::AI_prompt ts hs LI0]) as Hfill0.
    { simpl. 
      by rewrite List.app_nil_r. }
    destruct (llfill_trans Hfill0 Hfill) as [lh0 Hfill1].
    apply hfilled_to_llfill in H3 as [lh' Hlh].
    destruct (llfill_trans Hlh Hfill1) as [lh2 Hfill'].
    rewrite_cats1_list.
    specialize (llfill_first_values H1 Hfill') as [Habs _] => //.
  - (* contbind *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (llfill_first_values H1 Hfill) as [Habs _] => //.
    apply const_list_concat => //. 
  - (* resume_throw *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (llfill_first_values H1 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
    subst; apply v_to_e_is_const_list.
  - (* set_local *)
    rewrite_cats1_list.
    specialize (llfill_first_values H1 Hfill) as [Habs _] => //=.
    repeat rewrite const_const. done.

(*  - (* set_global *)
    rewrite_cats1_list.
    specialize (llfill_first_values H1 Hfill) as [Habs _] => //=.
    repeat rewrite const_const. done. *)
  - (* label *)
    apply lfilled_implies_llfill in H as (lh00 & _ & H).
    destruct (llfill_trans H Hfill) as [lh' Hfill'].
    apply length_llfill_rec' in H as [H | (-> & ->)].
    + apply (IHn0 _ _ _ _ _ Hred2 Hfill') => //. lias.
    + unfold lfilled, lfill in H0; simpl in H0.
      move/eqP in H0; subst.
      exfalso ; apply IHHred2 => //=.
  -  (* local *)
    assert (llfill (LL_local [::] n f (LL_base [::] [::]) [::]) es = [::AI_local n f es]) as H => //=.
    { by rewrite List.app_nil_r. }
    destruct (llfill_trans H Hfill) as [lh' Hfill'].
    apply (IHn0 _ _ _ _ _ Hred2 Hfill') => //.
    unfold length_rec in Hlab; simpl in Hlab.
    unfold length_rec. lias.
Qed.


(* Lemma firstx_of_suselt i l :
  firstx_continuation_suspend (map (continuation_clause_of_suselt i) l) i = None.
Proof.
  induction l => //=.
  rewrite IHl.
  destruct i.
  destruct a => //=.
  destruct (n0 <? n) eqn:Hn => //.
  all: destruct (_ == _) eqn:Habs => //.
  all: move/eqP in Habs.
  all: inversion Habs; subst.
  apply Nat.ltb_lt in Hn; lia.
  apply Nat.ltb_ge in Hn; lia.
Qed.  *)



Lemma prompt_in_hfilled_suspend vs i sh LI lh ts hs es:
  hfilled (Var_prompt_suspend i) sh [AI_suspend_desugared vs i] LI ->
  llfill lh [AI_prompt ts hs es] = LI ->
  firstx_continuation_suspend hs i = None.
Proof.
  intros.
  assert (forall n, length_rec LI < n -> firstx_continuation_suspend hs i = None) as Hres.  
  2:{ apply (Hres $ S $ length_rec LI). lia. }
  intros n.
  generalize dependent sh.
  generalize dependent lh.
  generalize dependent LI.
  induction n; first by intros; lia.
  intros LI lh Hll sh Hsus Hn.
  induction sh.
  all: move/hfilledP in Hsus.
  all: inversion Hsus; subst.
  - destruct lh.
    all: simpl in H3.
    all: apply first_values in H3 as (_ & ? & _) => //.
    all: by apply v_to_e_is_const_list.
  - destruct lh.
    all: simpl in H6.
    all: apply first_values in H6 as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    subst.
    eapply IHn.
    done.
    apply/hfilledP; done.
    rewrite /= separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - destruct lh.
    all: simpl in H6.
    all: apply first_values in H6 as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    subst.
    eapply IHn.
    done.
    apply/hfilledP; done.
    rewrite /= separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - destruct lh.
    all: simpl in H5.
    all: apply first_values in H5 as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    subst.
    eapply IHn.
    done.
    apply/hfilledP; done.
    rewrite /= separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - destruct lh.
    all: simpl in H6.
    all: apply first_values in H6 as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    + inversion H0.
      subst. done.
    + inversion H0.
      subst.
      eapply IHn.
      done.
      apply/hfilledP; done.
      rewrite /= separate1 in Hn.
      do 2 rewrite length_app_rec in Hn.
      simpl in Hn. unfold length_rec. lia.
Qed.

Lemma prompt_in_hfilled_switch vs i sh LI lh ts hs es k tf:
  hfilled (Var_prompt_switch i) sh [AI_switch_desugared k tf vs i] LI ->
  llfill lh [AI_prompt ts hs es] = LI ->
  firstx_continuation_switch hs i = false.
Proof.
  intros.
  assert (forall n, length_rec LI < n -> firstx_continuation_switch hs i = false) as Hres.  
  2:{ apply (Hres $ S $ length_rec LI). lia. }
  intros n.
  generalize dependent sh.
  generalize dependent lh.
  generalize dependent LI.
  induction n; first by intros; lia.
  intros LI lh Hll sh Hsus Hn.
  induction sh.
  all: move/hfilledP in Hsus.
  all: inversion Hsus; subst.
  - destruct lh.
    all: simpl in H3.
    all: apply first_values in H3 as (_ & ? & _) => //.
    all: by apply v_to_e_is_const_list.
  - destruct lh.
    all: simpl in H6.
    all: apply first_values in H6 as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    subst.
    eapply IHn.
    done.
    apply/hfilledP; done.
    rewrite /= separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - destruct lh.
    all: simpl in H6.
    all: apply first_values in H6 as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    subst.
    eapply IHn.
    done.
    apply/hfilledP; done.
    rewrite /= separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - destruct lh.
    all: simpl in H5.
    all: apply first_values in H5 as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    subst.
    eapply IHn.
    done.
    apply/hfilledP; done.
    rewrite /= separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - destruct lh.
    all: simpl in H6.
    all: apply first_values in H6 as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    + inversion H0.
      subst. done.
    + inversion H0.
      subst.
      eapply IHn.
      done.
      apply/hfilledP; done.
      rewrite /= separate1 in Hn.
      do 2 rewrite length_app_rec in Hn.
      simpl in Hn. unfold length_rec. lia.
Qed.
(*

Lemma prompt_in_susfill vs i sh LI lh ts hs es:
  susfill i sh [AI_suspend_desugared vs i] = LI ->
  llfill lh [AI_prompt ts hs es] = LI ->
  firstx_continuation_suspend hs i = None.
Proof.
  intros.
  assert (forall n, length_rec LI < n -> firstx_continuation_suspend hs i = None) as Hres.  
  2:{ apply (Hres $ S $ length_rec LI). lia. }
  intros n.
  generalize dependent sh.
  generalize dependent lh.
  generalize dependent LI.
  induction n; first by intros; lia.
  intros LI lh Hll sh Hsus Hn.
  induction sh.
  - simpl in Hsus.
    destruct lh.
    all: simpl in Hll.
    all: rewrite -Hsus in Hll.
    all: apply first_values in Hll as (_ & ? & _) => //.
    all: by apply v_to_e_is_const_list.
  - simpl in Hsus.
    destruct lh.
    all: simpl in Hll.
    all: rewrite -Hsus in Hll.
    all: apply first_values in Hll as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    apply v_to_e_inj in H.
    subst.
    eapply IHn.
    exact H5.
    done.
    rewrite separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - simpl in Hsus.
    destruct lh.
    all: simpl in Hll.
    all: rewrite -Hsus in Hll.
    all: apply first_values in Hll as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    apply v_to_e_inj in H.
    subst.
    eapply IHn.
    exact H5.
    done.
    rewrite separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - simpl in Hsus.
    destruct lh.
    all: simpl in Hll.
    all: rewrite -Hsus in Hll.
    all: apply first_values in Hll as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    apply v_to_e_inj in H.
    subst.
    eapply IHn.
    exact H4.
    done.
    rewrite separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - simpl in Hsus.
    destruct lh.
    all: simpl in Hll.
    all: rewrite - Hsus in Hll.
    all: apply first_values in Hll as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    + inversion H0.
      apply firstx_of_suselt.
    + inversion H0.
      apply v_to_e_inj in H.
      subst.
      eapply IHn.
      exact H5.
      done.
      rewrite separate1 in Hn.
      do 2 rewrite length_app_rec in Hn.
      simpl in Hn. unfold length_rec. lia.
Qed. *)


Lemma hfilled_suspend_and_reduce s f es LI s' f' es' vs i sh k lh:
  reduce s f es s' f' es' ->
  hfilled (Var_prompt_suspend i) sh [AI_suspend_desugared vs i] LI ->
  lfilled k lh es LI ->
  False.
Proof.
  intros Hred H1 Hes.
  apply lfilled_implies_llfill in Hes as (lh' & _ & Hlh').
(*  specialize (susfill_to_hfilled i sh [AI_suspend_desugared vs i]) as Hh;
    rewrite H1 in Hh; *)
  remember H1 as Hh; clear HeqHh.
  apply hfilled_to_llfill in Hh as [lh0 Hlh0].
  cut (forall n, length_rec es < n -> False).
  { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
  intro n0. 
  generalize dependent es. generalize dependent es'. 
  generalize dependent lh'. generalize dependent f.
  generalize dependent f'.
  induction n0 ; intros f' f lh1 es' es1 Hred2 Hfill Hlab ; first by lia.
  rewrite - (cat0s [_]) in Hlh0.
  induction Hred2;
    try by (
      rewrite_cats1_list; specialize (llfill_first_values Hfill Hlh0) as [Hcontra _] => //=; (try subst; apply v_to_e_is_const_list); repeat rewrite const_const). 
  (* r_simple *) 
  { destruct H;
      try by (
        rewrite_cats1_list;
              specialize (llfill_first_values Hfill Hlh0) as [Hcontra _] ; (try done) ; simpl; repeat rewrite const_const).
    - rewrite_cats1_list.
      specialize (llfill_first_values Hfill Hlh0) as [? _] => //.
      destruct ref => //=.
    - apply (llfill_all_values_prompt Hlh0 Hfill) => //.
      by left.
    - apply (llfill_all_values_handler Hlh0 Hfill) => //. 
      by left.
    - apply (llfill_all_values_handler Hlh0 Hfill) => //.
      by right.
    - apply (llfill_all_values_prompt Hlh0 Hfill) => //.
      by right.
    - apply (llfill_all_values_label Hlh0 Hfill) => //=. 
      by left.
    - apply (llfill_all_values_label Hlh0 Hfill) => //=. by right.

    - assert (lfilled (S i0) (LH_rec [] n es lh2 []) (vs0 ++ [AI_basic (BI_br i0)])
                [AI_label n es LI0]) as Hfill'.
      unfold lfilled, lfill ; fold lfill => //=.
      unfold lfilled in H2. destruct (lfill i0 _ _) => //. 
      move/eqP in H2 ; by subst.
      destruct (lfilled_in_llfill Hfill' Hfill) as [lh' Hfillbr].
      specialize (llfill_first_values Hfillbr Hlh0) as (? & ?) => //=.
    - apply (llfill_all_values_local Hlh0 Hfill) => //=.
      by left.
    - apply (llfill_all_values_local Hlh0 Hfill) => //=.
      by right. 
    - apply lfilled_implies_llfill in H2 as (llh & _ & H2).
      assert (llfill (LL_local [] n f0 llh []) (vs0 ++ [AI_basic BI_return]) = [AI_local n f0 es]) => //=.
      by rewrite H2.
      destruct (llfill_trans H3 Hfill) as [llh' Hfill'].
      edestruct llfill_first_values as [? _].
      exact Hlh0.
      exact Hfill'.
      all : try done.
    - replace [v ; AI_basic (BI_tee_local i0)] with
        ([v] ++ [AI_basic (BI_tee_local i0)])%SEQ in Hfill => //=.

      destruct (llfill_first_values Hfill Hlh0) as [??] => //=.
      by rewrite H.
    - destruct (lfilled_in_llfill H0 Hfill) as [lh' Hfill'].
      replace [AI_trap] with ([] ++ [AI_trap])%SEQ in Hfill' => //=.
      destruct (llfill_first_values Hfill' Hlh0) as [??] => //=. }
  - (* throw_ref *)
     assert (llfill (LL_handler [::] hs (LL_base [::] [::]) [::]) LI0 = [::AI_handler hs LI0]) as Hfill0.
    { simpl. 
      by rewrite List.app_nil_r. }
    destruct (llfill_trans Hfill0 Hfill) as [lh00 Hfill1].
    apply hfilled_to_llfill in H as [lh' Hlh].
    destruct (llfill_trans Hlh Hfill1) as [lh2 Hfill'].
    rewrite_cats1_list.
    specialize (llfill_first_values Hlh0 Hfill') as [Habs _] => //. 
  - (* throw_ref_ref *)
    assert (llfill (LL_handler [::] hs (LL_base [::] [::]) [::]) LI0 = [::AI_handler hs LI0]) as Hfill0.
    { simpl.
      by rewrite List.app_nil_r. }
    destruct (llfill_trans Hfill0 Hfill) as [lh00 Hfill1].
    apply hfilled_to_llfill in H as [lh' Hlh].
    destruct (llfill_trans Hlh Hfill1) as [lh2 Hfill'].
    rewrite_cats1_list.
    specialize (llfill_first_values Hlh0 Hfill') as [Habs _] => //. 
  - (* resume *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
  - (* switch *)
    rewrite separate1 in Hfill.
    rewrite - cat_app catA in Hfill.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
    apply v_to_e_is_const_list.
  - (* suspend *)
    assert (x = i) as ->.
    { assert (llfill (LL_prompt [::] ts hs (LL_base [::] [::]) [::]) LI0 = [::AI_prompt ts hs LI0]) as Hfill0.
      { simpl. 
        by rewrite List.app_nil_r. }
      destruct (llfill_trans Hfill0 Hfill) as [lh00 Hfill1].
      apply hfilled_to_llfill in H3 as [lh' Hlh].
      destruct (llfill_trans Hlh Hfill1) as [lh2 Hfill'].
      rewrite_cats1_list. 
      specialize (llfill_first_values Hlh0 Hfill') as [Habs _] => //.
      inversion Habs; subst. done. }
    erewrite prompt_in_hfilled_suspend in H2.
    done. exact H1. exact Hfill.

  - (* switch *)
    assert (llfill (LL_prompt [::] ts hs (LL_base [::] [::]) [::]) LI0 = [::AI_prompt ts hs LI0]) as Hfill0.
    { simpl. 
      by rewrite List.app_nil_r. }
    destruct (llfill_trans Hfill0 Hfill) as [lh00 Hfill1].
    apply hfilled_to_llfill in H3 as [lh' Hlh].
    destruct (llfill_trans Hlh Hfill1) as [lh2 Hfill'].
    rewrite_cats1_list.
    specialize (llfill_first_values Hlh0 Hfill') as [Habs _] => //.
  - (* contbind *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //.
    apply const_list_concat => //. 
  - (* resume_throw *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
    subst; apply v_to_e_is_const_list.
  - (* set_local *)
    rewrite_cats1_list.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //=.
    repeat rewrite const_const. done.

(*  - (* set_global *)
    rewrite_cats1_list.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //=.
    repeat rewrite const_const. done. *)
  - (* label *)
    apply lfilled_implies_llfill in H as (lh00 & _ & H).
    destruct (llfill_trans H Hfill) as [lh' Hfill'].
    apply length_llfill_rec' in H as [H | (-> & ->)].
    + apply (IHn0 _ _ _ _ _ Hred2 Hfill') => //. lias.
    + apply IHHred2 => //=.
  -  (* local *)
    assert (llfill (LL_local [::] n f (LL_base [::] [::]) [::]) es = [::AI_local n f es]) as H => //=.
    { by rewrite List.app_nil_r. }
    destruct (llfill_trans H Hfill) as [lh' Hfill'].
    apply (IHn0 _ _ _ _ _ Hred2 Hfill') => //.
    unfold length_rec in Hlab; simpl in Hlab.
    unfold length_rec. lias.
 

Qed.

Lemma susfill_suspend_and_reduce s f es LI s' f' es' vs i sh k lh:
  reduce s f es s' f' es' ->
  susfill i sh [AI_suspend_desugared vs i] = LI ->
  lfilled k lh es LI ->
  False.
Proof.
  intros Hred H1 Hes.
  specialize (susfill_to_hfilled i sh [AI_suspend_desugared vs i]) as Hh;
    rewrite H1 in Hh.
  eapply hfilled_suspend_and_reduce => //.
Qed. 


(*
Lemma firstx_of_swelt i l :
  firstx_continuation_switch (map (continuation_clause_of_swelt i) l) i = false.
Proof.
  induction l => //=.
  rewrite IHl.
  destruct i.
  destruct a => //=.
  destruct (n0 <? n) eqn:Hn => //.
  all: destruct (_ == _) eqn:Habs => //.
  all: move/eqP in Habs.
  all: inversion Habs; subst.
  apply Nat.ltb_lt in Hn; lia.
  apply Nat.ltb_ge in Hn; lia.
Qed. *)


(*
Lemma prompt_in_swfill vs k tf i sh LI lh ts hs es:
  swfill i sh [AI_switch_desugared vs k tf i] = LI ->
  llfill lh [AI_prompt ts hs es] = LI ->
  firstx_continuation_switch hs i = false.
Proof.
  intros.
  assert (forall n, length_rec LI < n -> firstx_continuation_switch hs i = false) as Hres.  
  2:{ apply (Hres $ S $ length_rec LI). lia. }
  intros n.
  generalize dependent sh.
  generalize dependent lh.
  generalize dependent LI.
  induction n; first by intros; lia.
  intros LI lh Hll sh Hsus Hn.
  induction sh.
  - simpl in Hsus.
    destruct lh.
    all: simpl in Hll.
    all: rewrite -Hsus in Hll.
    all: apply first_values in Hll as (_ & ? & _) => //.
    all: try apply const_list_concat => //.
    all: by apply v_to_e_is_const_list.
  - simpl in Hsus.
    destruct lh.
    all: simpl in Hll.
    all: rewrite -Hsus in Hll.
    all: apply first_values in Hll as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    apply v_to_e_inj in H.
    subst.
    eapply IHn.
    exact H5.
    done.
    rewrite separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - simpl in Hsus.
    destruct lh.
    all: simpl in Hll.
    all: rewrite -Hsus in Hll.
    all: apply first_values in Hll as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    apply v_to_e_inj in H.
    subst.
    eapply IHn.
    exact H5.
    done.
    rewrite separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - simpl in Hsus.
    destruct lh.
    all: simpl in Hll.
    all: rewrite -Hsus in Hll.
    all: apply first_values in Hll as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    apply v_to_e_inj in H.
    subst.
    eapply IHn.
    exact H4.
    done.
    rewrite separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - simpl in Hsus.
    destruct lh.
    all: simpl in Hll.
    all: rewrite - Hsus in Hll.
    all: apply first_values in Hll as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    + inversion H0.
      apply firstx_of_swelt.
    + inversion H0.
      apply v_to_e_inj in H.
      subst.
      eapply IHn.
      exact H5.
      done.
      rewrite separate1 in Hn.
      do 2 rewrite length_app_rec in Hn.
      simpl in Hn. unfold length_rec. lia.
Qed.  *)

Lemma llh_of_lh_empty k lh es LI:
  lfilled k lh es LI ->
  llh_of_lh lh = Some $ LL_base [] [] ->
  es = LI.
Proof.
  destruct lh => //=.
  2-4: destruct (e_to_v_list_opt l) => //.
  2-4: destruct (llh_of_lh lh) => //.
  unfold lfilled, lfill.
  destruct k => //.
  destruct (const_list l) eqn:Hl => //.
  apply const_es_exists in Hl as [vs ->].
  rewrite e_to_v_v_to_e.
  intros H H'.
  move/eqP in H.
  inversion H'; subst.
  by rewrite app_nil_r.
Qed.

Lemma hfilled_switch_and_reduce s f es LI s' f' es' vs k0 tf i sh k lh:
  reduce s f es s' f' es' ->
  hfilled (Var_prompt_switch i) sh [AI_switch_desugared vs k0 tf i] LI ->
  lfilled k lh es LI ->
  exists tf' sh hh,
      llfill sh [AI_switch_desugared vs k0 tf i] = es /\
        List.nth_error (s_conts s) k0 = Some (Cont_dagger tf') /\
        s = s' /\ f = f' /\ hfilled No_var hh [::AI_trap] es'.
Proof.
  intros Hred H1 Hes.
  apply lfilled_implies_llfill in Hes as (lh' & _ & Hlh').
(*  specialize (swfill_to_hfilled i sh [AI_switch_desugared vs k0 tf i]) as Hh;
    rewrite H1 in Hh; *)
  remember H1 as Hh; clear HeqHh;
    apply hfilled_to_llfill in Hh as [lh0 Hlh0].
  cut (forall n, length_rec es < n ->
       ∃ (tf' : function_type) sh0 (hh : hholed),
    llfill sh0 [AI_switch_desugared vs k0 tf i] = es
    ∧ nth_error (s_conts s) k0 = Some (Cont_dagger tf') ∧ s = s' ∧ f = f' ∧ hfilled No_var hh [AI_trap] es').
  { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
  intro n0. 
  generalize dependent es. generalize dependent es'. 
  generalize dependent lh'. generalize dependent f.
  generalize dependent f'.
  induction n0 ; intros f' f lh1 es' es1 Hred2 Hfill Hlab ; first by lia.
  repeat rewrite_cats1_list.
  induction Hred2;
    try by (
      rewrite_cats1_list; specialize (llfill_first_values Hfill Hlh0) as [Hcontra _] => //=; (try subst; apply v_to_e_is_const_list); repeat rewrite const_const).
  (* r_simple *) 
  { exfalso.
    destruct H;
      try by (
        rewrite_cats1_list; try rewrite_cats1_list;
        specialize (llfill_first_values Hfill Hlh0) as [Hcontra _] ; (try done) ; simpl; repeat rewrite const_const).
    - rewrite_cats1_list.
      specialize (llfill_first_values Hfill Hlh0) as [? _] => //.
      destruct ref => //=.
    - apply (llfill_all_values_prompt Hlh0 Hfill) => //.
      by left.
    - apply (llfill_all_values_handler Hlh0 Hfill) => //. 
      by left.
    - apply (llfill_all_values_handler Hlh0 Hfill) => //.
      by right.
    - apply (llfill_all_values_prompt Hlh0 Hfill) => //.
      by right.
    - apply (llfill_all_values_label Hlh0 Hfill) => //=. 
      by left.
    - apply (llfill_all_values_label Hlh0 Hfill) => //=. by right. 
    - assert (lfilled (S i0) (LH_rec [] n es lh2 []) (vs0 ++ [AI_basic (BI_br i0)])
                [AI_label n es LI0]) as Hfill'.
      unfold lfilled, lfill ; fold lfill => //=.
      unfold lfilled in H2. destruct (lfill i0 _ _) => //. 
      move/eqP in H2 ; by subst.
      destruct (lfilled_in_llfill Hfill' Hfill) as [lh' Hfillbr].
      specialize (llfill_first_values Hfillbr Hlh0) as (? & ?) => //=.
    - apply (llfill_all_values_local Hlh0 Hfill) => //=.
      by left.
    - apply (llfill_all_values_local Hlh0 Hfill) => //=.
      by right. 
    - apply lfilled_implies_llfill in H2 as (llh & _ & H2).
      assert (llfill (LL_local [] n f0 llh []) (vs0 ++ [AI_basic BI_return]) = [AI_local n f0 es]) => //=.
      by rewrite H2.
      destruct (llfill_trans H3 Hfill) as [llh' Hfill'].
      edestruct llfill_first_values as [? _].
      exact Hlh0.
      exact Hfill'.
      all : try done.
    - replace [v ; AI_basic (BI_tee_local i0)] with
        ([v] ++ [AI_basic (BI_tee_local i0)])%SEQ in Hfill => //=.

      destruct (llfill_first_values Hfill Hlh0) as [??] => //=.
      by rewrite H.
    - destruct (lfilled_in_llfill H0 Hfill) as [lh' Hfill'].
      replace [AI_trap] with ([] ++ [AI_trap])%SEQ in Hfill' => //=.
      destruct (llfill_first_values Hfill' Hlh0) as [??] => //=. }
  - (* throw_ref *)
     assert (llfill (LL_handler [::] hs (LL_base [::] [::]) [::]) LI0 = [::AI_handler hs LI0]) as Hfill0.
    { simpl. 
      by rewrite List.app_nil_r. }
    destruct (llfill_trans Hfill0 Hfill) as [lh00 Hfill1].
    apply hfilled_to_llfill in H as [lh' Hlh].
    destruct (llfill_trans Hlh Hfill1) as [lh2 Hfill'].
    rewrite_cats1_list.
    specialize (llfill_first_values Hlh0 Hfill') as [Habs _] => //. 
  - (* throw_ref_ref *)
    assert (llfill (LL_handler [::] hs (LL_base [::] [::]) [::]) LI0 = [::AI_handler hs LI0]) as Hfill0.
    { simpl.
      by rewrite List.app_nil_r. }
    destruct (llfill_trans Hfill0 Hfill) as [lh00 Hfill1].
    apply hfilled_to_llfill in H as [lh' Hlh].
    destruct (llfill_trans Hlh Hfill1) as [lh2 Hfill'].
    rewrite_cats1_list.
    specialize (llfill_first_values Hlh0 Hfill') as [Habs _] => //. 
  - (* resume *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
  - rewrite separate1 -cat_app catA in Hfill.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
    apply v_to_e_is_const_list.
  - (* suspend *)
    assert (llfill (LL_prompt [::] ts hs (LL_base [::] [::]) [::]) LI0 = [::AI_prompt ts hs LI0]) as Hfill0.
    { simpl. 
      by rewrite List.app_nil_r. }
    destruct (llfill_trans Hfill0 Hfill) as [lh00 Hfill1].
    apply hfilled_to_llfill in H3 as [lh' Hlh].
    destruct (llfill_trans Hlh Hfill1) as [lh2 Hfill'].
    rewrite_cats1_list.
    specialize (llfill_first_values Hlh0 Hfill') as [Habs _] => //.
  - (* switch *)
    assert (x = i) as ->.
    { assert (llfill (LL_prompt [::] ts hs (LL_base [::] [::]) [::]) LI0 = [::AI_prompt ts hs LI0]) as Hfill0.
      { simpl. 
        by rewrite List.app_nil_r. }
      destruct (llfill_trans Hfill0 Hfill) as [lh00 Hfill1].
      apply hfilled_to_llfill in H3 as [lh' Hlh].
      destruct (llfill_trans Hlh Hfill1) as [lh2 Hfill'].
      rewrite -(cat0s [:: _]) in Hfill'.
      specialize (llfill_first_values Hlh0 Hfill') as [Habs _] => //.
      inversion Habs; subst. done. }
    erewrite prompt_in_hfilled_switch in H.
    done. exact H1. exact Hfill.
  - (* switch failure *)
    do 2 rewrite_cats1_list.
    specialize (llfill_first_values Hlh0 Hfill) as [Hsw Hrc] => //.
    destruct Hrc as [Heq ->] => //.
    inversion Hsw; inversion Heq. subst.
    repeat eexists.
    instantiate (1 := LL_base [] []). done.
    done. instantiate (1 := HH_base [] []).
    unfold hfilled, hfill => //. 
 
  - (* contbind *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //.
    apply const_list_concat => //. 
  - (* resume_throw *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
    subst; apply v_to_e_is_const_list.
  - (* set_local *)
    rewrite_cats1_list.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //=.
    repeat rewrite const_const. done.

(*   - (* set_global *)
    rewrite_cats1_list.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //=. 
    repeat rewrite const_const. done. *)
  - (* label *)
    apply lfilled_implies_llfill in H as (lh00 & Hlh & H).
    destruct (llfill_trans H Hfill) as [lh' Hfill'].
    remember H as H'; clear HeqH'.
    apply length_llfill_rec' in H as [H | (-> & ->)].
    + destruct (IHn0 _ _ _ _ _ Hred2 Hfill') as (tf1 & sh0 & hh0 & Hsw & Hdag & -> & -> & Htrap) => //.
      lias.
      destruct (llfill_trans Hsw H') as [lll Hlll].
      destruct (lfilled_hfilled_trans Htrap H0) as [lll' Hlll'].
      repeat eexists.
      exact Hlll. done. exact Hlll'.
    + eapply llh_of_lh_empty in Hlh.
      2: exact H0.
      subst.
      apply IHHred2 => //=. 
  -  (* local *)
    assert (llfill (LL_local [::] n f (LL_base [::] [::]) [::]) es = [::AI_local n f es]) as H => //=.
    { by rewrite List.app_nil_r. }
    destruct (llfill_trans H Hfill) as [lh' Hfill'].
    destruct (IHn0 _ _ _ _ _ Hred2 Hfill') as (tf1 & sh0 & hh0 & Hsw & Hdag & -> & -> & Htrap) => //.
    unfold length_rec in Hlab; simpl in Hlab.
    unfold length_rec. lias.
    repeat eexists.
    instantiate (1 := LL_local [] n f' sh0 []).
    simpl. simpl in Hsw. rewrite Hsw. done. done.
    instantiate (1 := HH_local [] n f' hh0 []).
    unfold hfilled, hfill; fold hfill => /=.
    unfold hfilled in Htrap.
    destruct (hfill _ _ _) => //.
    move/eqP in Htrap; subst => //. 
Qed.

Lemma swfill_switch_and_reduce s f es LI s' f' es' vs k0 tf i sh k lh:
  reduce s f es s' f' es' ->
  swfill i sh [AI_switch_desugared vs k0 tf i] = LI ->
  lfilled k lh es LI ->
  exists tf' sh hh,
      llfill sh [AI_switch_desugared vs k0 tf i] = es /\
        List.nth_error (s_conts s) k0 = Some (Cont_dagger tf') /\
        s = s' /\ f = f' /\ hfilled No_var hh [::AI_trap] es'.
Proof.
  intros Hred H1 Hes.
  specialize (swfill_to_hfilled i sh [AI_switch_desugared vs k0 tf i]) as Hh;
    rewrite H1 in Hh.
  eapply hfilled_switch_and_reduce => //. 
Qed. 

(*
Lemma firstx_of_exnelt i l :
  firstx_exception (map (exception_clause_of_exnelt i) l) i = No_label.
Proof.
  induction l => //=.
  rewrite IHl.
  destruct i.
  destruct a => //=.
  all: destruct (n0 <? n) eqn:Hn => //.
  all: destruct (_ == _) eqn:Habs => //.
  all: move/eqP in Habs.
  all: inversion Habs; subst.
  all: try by apply Nat.ltb_lt in Hn; lia.
  all: apply Nat.ltb_ge in Hn; lia.
Qed.
*)

Lemma handler_in_hfilled vs a i sh LI lh hs es:
  hfilled (Var_handler i) sh [AI_throw_ref_desugared vs a i] LI ->
  llfill lh [AI_handler hs es] = LI ->
  firstx_exception hs i = No_label.
Proof.
  intros.
  assert (forall n, length_rec LI < n -> firstx_exception hs i = No_label) as Hres.  
  2:{ apply (Hres $ S $ length_rec LI). lia. }
  intros n.
  generalize dependent sh.
  generalize dependent lh.
  generalize dependent LI.
  induction n; first by intros; lia.
  intros LI lh Hll sh Hsus Hn.
  induction sh.
  all: move/hfilledP in Hsus.
  all: inversion Hsus; subst.
  - destruct lh.
    all: simpl in H3.
    all: apply first_values in H3 as (_ & ? & _) => //.
    all: by apply v_to_e_is_const_list.
  - destruct lh.
    all: simpl in H6.
    all: apply first_values in H6 as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    subst.
    eapply IHn.
    done.
    move/hfilledP in H8. exact H8.
    rewrite /= separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - destruct lh.
    all: simpl in H6.
    all: apply first_values in H6 as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    subst.
    eapply IHn.
    done.
    apply/hfilledP; exact H8.
    rewrite /= separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - destruct lh.
    all: simpl in H5.
    all: apply first_values in H5 as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    + inversion H0. subst. done.
    + inversion H0.
      subst.
      eapply IHn.
      done.
      apply/hfilledP; exact H8.
      rewrite /= separate1 in Hn.
      do 2 rewrite length_app_rec in Hn.
      simpl in Hn. unfold length_rec. lia.
  - destruct lh.
    all: simpl in H6.
    all: apply first_values in H6 as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    subst.
    eapply IHn.
    done.
    apply/hfilledP; exact H9.
    rewrite /= separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
Qed.
(*
Lemma handler_in_exnfill vs a i sh LI lh hs es:
  exnfill i sh [AI_throw_ref_desugared vs a i] = LI ->
  llfill lh [AI_handler hs es] = LI ->
  firstx_exception hs i = No_label.
Proof.
  intros.
  assert (forall n, length_rec LI < n -> firstx_exception hs i = No_label) as Hres.  
  2:{ apply (Hres $ S $ length_rec LI). lia. }
  intros n.
  generalize dependent sh.
  generalize dependent lh.
  generalize dependent LI.
  induction n; first by intros; lia.
  intros LI lh Hll sh Hsus Hn.
  induction sh.
  - simpl in Hsus.

    destruct lh.
    all: simpl in Hll.
    all: rewrite -Hsus in Hll.
    all: apply first_values in Hll as (_ & ? & _) => //.
    all: try apply const_list_concat => //.
    all: by apply v_to_e_is_const_list.
  - simpl in Hsus.
    destruct lh.
    all: simpl in Hll.
    all: rewrite -Hsus in Hll.
    all: apply first_values in Hll as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    apply v_to_e_inj in H.
    subst.
    eapply IHn.
    exact H5.
    done.
    rewrite separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - simpl in Hsus.
    destruct lh.
    all: simpl in Hll.
    all: rewrite -Hsus in Hll.
    all: apply first_values in Hll as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    inversion H0.
    apply v_to_e_inj in H.
    subst.
    eapply IHn.
    exact H5.
    done.
    rewrite separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - simpl in Hsus.
    destruct lh.
    all: simpl in Hll.
    all: rewrite -Hsus in Hll.
    all: apply first_values in Hll as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
    + inversion H0.
      apply firstx_of_exnelt.
    + inversion H0.
    apply v_to_e_inj in H.
    subst.
    eapply IHn.
    exact H4.
    done.
    rewrite separate1 in Hn.
    do 2 rewrite length_app_rec in Hn.
    simpl in Hn. unfold length_rec. lia.
  - simpl in Hsus.
    destruct lh.
    all: simpl in Hll.
    all: rewrite - Hsus in Hll.
    all: apply first_values in Hll as (? & ? & ?) => //.
    all: try by apply v_to_e_is_const_list.
     inversion H0.
      apply v_to_e_inj in H.
      subst.
      eapply IHn.
      exact H5.
      done.
      rewrite separate1 in Hn.
      do 2 rewrite length_app_rec in Hn.
      simpl in Hn. unfold length_rec. lia.
Qed.  *)


Lemma hfilled_throw_ref_and_reduce s f es LI s' f' es' vs a i sh k lh:
  reduce s f es s' f' es' ->
  hfilled (Var_handler i) sh [AI_throw_ref_desugared vs a i] LI ->
  lfilled k lh es LI ->
  False.
Proof.
  intros Hred H1 Hes.
  apply lfilled_implies_llfill in Hes as (lh' & _ & Hlh').
(*  specialize (exnfill_to_hfilled i sh [AI_throw_ref_desugared vs a i]) as Hh;
    rewrite H1 in Hh; *)
  remember H1 as H1'; clear HeqH1'.
  apply hfilled_to_llfill in H1' as [lh0 Hlh0]. 
  cut (forall n, length_rec es < n -> False).
  { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
  intro n0. 
  generalize dependent es. generalize dependent es'. 
  generalize dependent lh'. generalize dependent f.
  generalize dependent f'.
  induction n0 ; intros f' f lh1 es' es1 Hred2 Hfill Hlab ; first by lia.
  rewrite_cats1_list.
  induction Hred2 ;
    try by (
      rewrite_cats1_list; specialize (llfill_first_values Hfill Hlh0) as [Hcontra _] => //=; (try subst; apply v_to_e_is_const_list); repeat rewrite const_const). 
  (* r_simple *) 
  { destruct H;
      try by (
        rewrite_cats1_list;
              specialize (llfill_first_values Hfill Hlh0) as [Hcontra _] ; (try done) ; simpl; repeat rewrite const_const).
    - rewrite_cats1_list.
      specialize (llfill_first_values Hfill Hlh0) as [? _] => //.
      destruct ref => //=.
    - apply (llfill_all_values_prompt Hlh0 Hfill) => //.
      by left.
    - apply (llfill_all_values_handler Hlh0 Hfill) => //. 
      by left.
    - apply (llfill_all_values_handler Hlh0 Hfill) => //.
      by right.
    - apply (llfill_all_values_prompt Hlh0 Hfill) => //.
      by right.
    - apply (llfill_all_values_label Hlh0 Hfill) => //=. 
      by left.
    - apply (llfill_all_values_label Hlh0 Hfill) => //=. by right. 
    - assert (lfilled (S i0) (LH_rec [] n es lh2 []) (vs0 ++ [AI_basic (BI_br i0)])
                [AI_label n es LI0]) as Hfill'.
      unfold lfilled, lfill ; fold lfill => //=.
      unfold lfilled in H2. destruct (lfill i0 _ _) => //. 
      move/eqP in H2 ; by subst.
      destruct (lfilled_in_llfill Hfill' Hfill) as [lh' Hfillbr].
      specialize (llfill_first_values Hfillbr Hlh0) as (? & ?) => //=.
    - apply (llfill_all_values_local Hlh0 Hfill) => //=.
      by left.
    - apply (llfill_all_values_local Hlh0 Hfill) => //=.
      by right. 
    - apply lfilled_implies_llfill in H2 as (llh & _ & H2).
      assert (llfill (LL_local [] n f0 llh []) (vs0 ++ [AI_basic BI_return]) = [AI_local n f0 es]) => //=.
      by rewrite H2.
      destruct (llfill_trans H3 Hfill) as [llh' Hfill'].
      edestruct llfill_first_values as [? _].
      exact Hlh0.
      exact Hfill'.
      all : try done.
    - replace [v ; AI_basic (BI_tee_local i0)] with
        ([v] ++ [AI_basic (BI_tee_local i0)])%SEQ in Hfill => //=.

      destruct (llfill_first_values Hfill Hlh0) as [??] => //=.
      by rewrite H.
    - destruct (lfilled_in_llfill H0 Hfill) as [lh' Hfill'].
      replace [AI_trap] with ([] ++ [AI_trap])%SEQ in Hfill' => //=.
      destruct (llfill_first_values Hfill' Hlh0) as [??] => //=. }
  - (* throw_ref *)
    assert (i = i0) as ->.
    { assert (llfill (LL_handler [::] hs (LL_base [::] [::]) [::]) LI0 = [::AI_handler hs LI0]) as Hfill0.
      { simpl. 
        by rewrite List.app_nil_r. }
      destruct (llfill_trans Hfill0 Hfill) as [lh00 Hfill1].
      apply hfilled_to_llfill in H as [lh' Hlh].
      destruct (llfill_trans Hlh Hfill1) as [lh2 Hfill'].
      rewrite_cats1_list. 
      specialize (llfill_first_values Hlh0 Hfill') as [Habs _] => //.
      inversion Habs; subst. done. }
    erewrite handler_in_hfilled in H0.
    done. exact H1. exact Hfill.
 
    - (* throw_ref_ref *)
      assert (i = i0) as ->.
    { assert (llfill (LL_handler [::] hs (LL_base [::] [::]) [::]) LI0 = [::AI_handler hs LI0]) as Hfill0.
      { simpl. 
        by rewrite List.app_nil_r. }
      destruct (llfill_trans Hfill0 Hfill) as [lh00 Hfill1].
      apply hfilled_to_llfill in H as [lh' Hlh].
      destruct (llfill_trans Hlh Hfill1) as [lh2 Hfill'].
      rewrite_cats1_list. 
      specialize (llfill_first_values Hlh0 Hfill') as [Habs _] => //.
      inversion Habs; subst. done. }
    erewrite handler_in_hfilled in H0.
    done. exact H1. exact Hfill.
  - (* resume *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
  - rewrite separate1 -cat_app catA in Hfill.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
    apply v_to_e_is_const_list.
 - (* suspend *)
     assert (llfill (LL_prompt [::] ts hs (LL_base [::] [::]) [::]) LI0 = [::AI_prompt ts hs LI0]) as Hfill0.
    { simpl. 
      by rewrite List.app_nil_r. }
    destruct (llfill_trans Hfill0 Hfill) as [lh00 Hfill1].
    apply hfilled_to_llfill in H3 as [lh' Hlh].
    destruct (llfill_trans Hlh Hfill1) as [lh2 Hfill'].
    rewrite_cats1_list.
    specialize (llfill_first_values Hlh0 Hfill') as [Habs _] => //. 

  - (* switch *)
    assert (llfill (LL_prompt [::] ts hs (LL_base [::] [::]) [::]) LI0 = [::AI_prompt ts hs LI0]) as Hfill0.
    { simpl. 
      by rewrite List.app_nil_r. }
    destruct (llfill_trans Hfill0 Hfill) as [lh00 Hfill1].
    apply hfilled_to_llfill in H3 as [lh' Hlh].
    destruct (llfill_trans Hlh Hfill1) as [lh2 Hfill'].
    rewrite_cats1_list.
    specialize (llfill_first_values Hlh0 Hfill') as [Habs _] => //.
      - (* contbind *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //.
    apply const_list_concat => //. 
  - (* resume_throw *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
    subst; apply v_to_e_is_const_list.
  - (* set_local *)
    rewrite_cats1_list.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //=.
    repeat rewrite const_const. done.

(*  - (* set_global *)
    rewrite_cats1_list.
    specialize (llfill_first_values Hlh0 Hfill) as [Habs _] => //=.
    repeat rewrite const_const. done. *)
  - (* label *)
    apply lfilled_implies_llfill in H as (lh00 & _ & H).
    destruct (llfill_trans H Hfill) as [lh' Hfill'].
    apply length_llfill_rec' in H as [H | (-> & ->)].
    + apply (IHn0 _ _ _ _ _ Hred2 Hfill') => //. lias.
    + unfold lfilled, lfill in H0; simpl in H0.
      move/eqP in H0; subst.
      exfalso ; apply IHHred2 => //=.
  -  (* local *)
    assert (llfill (LL_local [::] n f (LL_base [::] [::]) [::]) es = [::AI_local n f es]) as H => //=.
    { by rewrite List.app_nil_r. }
    destruct (llfill_trans H Hfill) as [lh' Hfill'].
    apply (IHn0 _ _ _ _ _ Hred2 Hfill') => //.
    unfold length_rec in Hlab; simpl in Hlab.
    unfold length_rec. lias.
 

Qed.


Lemma exnfill_throw_ref_and_reduce s f es LI s' f' es' vs a i sh k lh:
  reduce s f es s' f' es' ->
  exnfill i sh [AI_throw_ref_desugared vs a i] = LI ->
  lfilled k lh es LI ->
  False.
Proof.
  intros Hred H1 Hes.
  specialize (exnfill_to_hfilled i sh [AI_throw_ref_desugared vs a i]) as Hh.
  eapply hfilled_throw_ref_and_reduce.
  exact Hred. exact Hh. rewrite H1. exact Hes.
Qed. 



Lemma lfilled_call_host_and_reduce s f es LI s' f' es' i lh vs k lh' tf h cvs:
  reduce s f es s' f' es' ->
  const_list vs ->
  lfilled i lh (vs ++ [AI_call_host tf h cvs]) LI ->
  lfilled k lh' es LI ->
  False.
Proof.
  intros Hred Hvs H1 Hes.
  cut (forall n, length_rec es < n -> False).
  { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
  intro n0. 
  generalize dependent es. generalize dependent es'. generalize dependent k.
  generalize dependent lh'.
  induction n0 ; intros lh1 k es' es1 Hred2 Hfill Hlab ; first by lia.
  induction Hred2; try by (rewrite_cats1_list; specialize (lfilled_first_values H1 Hfill) as [Hcontra _] => //=; (try subst; apply v_to_e_is_const_list); repeat rewrite const_const).
  (* r_simple *)
  { destruct H; try by (rewrite_cats1_list; specialize (lfilled_first_values H1 Hfill) as [Hcontra _] => //=; repeat rewrite const_const).
    - rewrite_cats1_list.
      specialize (lfilled_first_values H1 Hfill) as [? _] => //.
      destruct ref => //.
    - apply (lfilled_all_values_prompt H1 Hfill) => //=.
      by left.
    - apply (lfilled_all_values_handler H1 Hfill) => //.
      by left.
    - apply (lfilled_all_values_handler H1 Hfill) => //.
      by right.
    - apply (lfilled_all_values_prompt H1 Hfill) => //.
      by right.
    - apply (lfilled_all_values_label H1 Hfill) => //=.
      by left.
    - apply (lfilled_all_values_label H1 Hfill) => //=.
      by right. 
    - assert (lfilled (S i0) (LH_rec [] n es lh0 []) (vs0 ++ [AI_basic (BI_br i0)])
                [AI_label n es LI0]) as Hfill'.
      unfold lfilled, lfill ; fold lfill => //=.
      unfold lfilled in H2. destruct (lfill i0 _ _) => //. 
      move/eqP in H2 ; by subst.
      destruct (lfilled_trans Hfill' Hfill) as [lh' Hfillbr].
      specialize (lfilled_first_values H1 Hfillbr) as (? & ? & ?) => //=.
    - replace [v ; AI_basic (BI_tee_local i0)] with
        ([v] ++ [AI_basic (BI_tee_local i0)])%SEQ in Hfill => //=.
      assert (AI_call_host tf h cvs = AI_basic (BI_tee_local i0)) => //=.
      apply (lfilled_first_values H1 Hfill) => //=.
      by rewrite H.
    - destruct (lfilled_trans H0 Hfill) as [lh' Hfill'].
      replace [AI_trap] with ([] ++ [AI_trap])%SEQ in Hfill' => //=.
      assert (AI_call_host tf h cvs = AI_trap) => //=.
      apply (lfilled_first_values H1 Hfill') => //=. }
  - (* throw_ref *)
     assert (lfilled 0 (LH_handler [::] hs (LH_base [::] [::]) [::]) LI0 [::AI_handler hs LI0]) as Hfill0.
    { unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r. }
    destruct (lfilled_trans Hfill0 Hfill) as [lh0 Hfill1].
    apply hfilled_to_lfilled in H as [(k' & lh' & Hlh) | (k' & lh' & n & f' & LI' & Hlh)].
    all: destruct (lfilled_trans Hlh Hfill1) as [lh2 Hfill'].
    all: rewrite_cats1_list.
    all: specialize (lfilled_first_values H1 Hfill') as [Habs _] => //. 
  - (* throw_ref_ref *)
            assert (lfilled 0 (LH_handler [::] hs (LH_base [::] [::]) [::]) LI0 [::AI_handler hs LI0]) as Hfill0.
    { unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r. }
    destruct (lfilled_trans Hfill0 Hfill) as [lh0 Hfill1].
    apply hfilled_to_lfilled in H as [(k' & lh' & Hlh) | (k' & lh' & n & f' & LI' & Hlh)].
    all: destruct (lfilled_trans Hlh Hfill1) as [lh2 Hfill'].
    all: rewrite_cats1_list.
    all: specialize (lfilled_first_values H1 Hfill') as [Habs _] => //. 
  - (* resume *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //.
    apply const_list_concat => //. 
  - (* switch *)
    rewrite separate1 -cat_app catA in Hfill.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
    apply v_to_e_is_const_list.
  - (* suspend *)
    assert (lfilled 0 (LH_prompt [::] ts hs (LH_base [::] [::]) [::]) LI0 [::AI_prompt ts hs LI0]) as Hfill0.
    { unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r. }
    destruct (lfilled_trans Hfill0 Hfill) as [lh0 Hfill1].
    apply hfilled_to_lfilled in H3 as [(k' & lh' & Hlh) | (k' & lh' & n & f' & LI' & Hlh)].
    all: destruct (lfilled_trans Hlh Hfill1) as [lh2 Hfill'].
    all: rewrite_cats1_list. 
    all: specialize (lfilled_first_values H1 Hfill') as [Habs _] => //.
  - (* switch *)
     assert (lfilled 0 (LH_prompt [::] ts hs (LH_base [::] [::]) [::]) LI0 [::AI_prompt ts hs LI0]) as Hfill0.
    { unfold lfilled, lfill => //=.
      by rewrite List.app_nil_r. }
    destruct (lfilled_trans Hfill0 Hfill) as [lh0 Hfill1].
    apply hfilled_to_lfilled in H3 as [(k' & lh' & Hlh) | (k' & lh' & n & f' & LI'' & Hlh)].
    all: destruct (lfilled_trans Hlh Hfill1) as [lh2 Hfill'].
    all: rewrite_cats1_list.
    all: specialize (lfilled_first_values H1 Hfill') as [Habs _] => //.
        
  - (* contbind *)
    rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //.
    apply const_list_concat => //. 
  - (* resume_throw *)
        rewrite separate1 in Hfill.
    rewrite - cat_app in Hfill. rewrite catA in Hfill.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //.
    apply const_list_concat => //.
    subst; apply v_to_e_is_const_list.
  - (* set_local *)
    rewrite_cats1_list.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //=. repeat rewrite const_const. done.

(*  - (* set_global *)
        rewrite_cats1_list.
    specialize (lfilled_first_values H1 Hfill) as [Habs _] => //=. repeat rewrite const_const. done. *)
  - (* label *)
    destruct (lfilled_trans H Hfill) as [lh' Hfill'].
    apply length_lfilled_rec' in H as [H | (-> & -> & ->)].
    + apply (IHn0 _ _ _ _ Hred2 Hfill') => //. lias.
    + unfold lfilled, lfill in H0; simpl in H0.
      move/eqP in H0; subst.
      exfalso ; apply IHHred2 => //=.
Qed. 


Lemma sfill_nested vh wh e :
  ∃ vh', sfill vh (sfill wh e) = sfill vh' e.
Proof.
  induction vh.
  - destruct wh.
    + exists (SH_base (l ++ l1) (l2 ++ l0)).
      cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc. auto. 
    + exists (SH_rec (l ++ l1) n l2 wh (l3 ++ l0)).
      cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc.
      rewrite app_comm_cons. rewrite (separate1 _ l3).
      repeat erewrite app_assoc. auto.
    + exists (SH_prompt (l ++ l1) l2 l3 wh (l4 ++ l0)).
      cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc.
      rewrite app_comm_cons. rewrite (separate1 _ l4).
      repeat rewrite app_assoc. done.
    + exists (SH_handler (l ++ l1) l2 wh (l3 ++ l0)).
      cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc.
      rewrite app_comm_cons. rewrite (separate1 _ l3).
      repeat rewrite app_assoc. done.
  - destruct IHvh as [vh' Heq].
    cbn. rewrite Heq.
    exists (SH_rec l n l0 vh' l1). cbn. auto.
  - destruct IHvh as [vh' Heq].
    cbn. rewrite Heq. 
    exists (SH_prompt l l0 l1 vh' l2). cbn. done.
  - destruct IHvh as [vh' Heq].
    cbn. rewrite Heq.
    exists (SH_handler l l0 vh' l1). cbn. done.
Qed.

Lemma llfill_nested vh wh e :
  ∃ vh', llfill vh (llfill wh e) = llfill vh' e.
Proof.
  induction vh.
  - destruct wh.
    + exists (LL_base (l ++ l1) (l2 ++ l0)).
      cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc. auto.
    + exists (LL_label (l ++ l1) n l2 wh (l3 ++ l0)).
      cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc.
      rewrite app_comm_cons. rewrite (separate1 _ l3).
      repeat erewrite app_assoc. auto. 
    + exists (LL_local (l ++ l1) n f wh (l2 ++ l0)).
      cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc.
      rewrite app_comm_cons.
      repeat erewrite app_assoc. auto.
    + exists (LL_prompt (l ++ l1) l2 l3 wh (l4 ++ l0)).
      cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc.
      rewrite app_comm_cons.
      repeat erewrite app_assoc. auto.
    + exists (LL_handler (l ++ l1) l2 wh (l3 ++ l0)).
      cbn. rewrite - v_to_e_cat. repeat erewrite app_assoc.
      rewrite app_comm_cons.
      repeat erewrite app_assoc. auto. 
  - destruct IHvh as [vh' Heq].
    cbn. rewrite Heq.
    exists (LL_label l n l0 vh' l1). cbn. auto. 
  - destruct IHvh as [vh' Heq].
    cbn. rewrite Heq.
    exists (LL_local l n f vh' l0). cbn. auto.
  - destruct IHvh as [vh' Heq].
    cbn. rewrite Heq.
    exists (LL_prompt l l0 l1 vh' l2). cbn. auto.
  - destruct IHvh as [vh' Heq].
    cbn. rewrite Heq.
    exists (LL_handler l l0 vh' l1). cbn. auto.
Qed.

Lemma is_pure_susholed_of_lholed k lh es LI :
  is_pure lh ->
  lfilled k lh es LI ->
  exists sh, susholed_of_lholed lh = Some sh.
Proof.
  intros Hpure.
  generalize dependent k.
  generalize dependent LI.
  induction Hpure.
  all: intros LI k Hfilled.
  all: move/lfilledP in Hfilled; inversion Hfilled; subst.
  all: simpl.
  - apply const_es_exists in H4 as [vs ->].
    rewrite e_to_v_v_to_e. by eexists.
  - move/lfilledP in H8.
    apply IHHpure in H8 as [sh ->].
    apply const_es_exists in H7 as [vs ->].
    rewrite e_to_v_v_to_e.
    by eexists.
Qed.

Lemma is_pure_swholed_of_lholed k lh es LI :
  is_pure lh ->
  lfilled k lh es LI ->
  exists sh, swholed_of_lholed lh = Some sh.
Proof.
  intros Hpure.
  generalize dependent k.
  generalize dependent LI.
  induction Hpure.
  all: intros LI k Hfilled.
  all: move/lfilledP in Hfilled; inversion Hfilled; subst.
  all: simpl.
  - apply const_es_exists in H4 as [vs ->].
    rewrite e_to_v_v_to_e. by eexists.
  - move/lfilledP in H8.
    apply IHHpure in H8 as [sh ->].
    apply const_es_exists in H7 as [vs ->].
    rewrite e_to_v_v_to_e.
    by eexists.
Qed.

Lemma is_pure_exnholed_of_lholed k lh es LI :
  is_pure lh ->
  lfilled k lh es LI ->
  exists sh, exnholed_of_lholed lh = Some sh.
Proof.
  intros Hpure.
  generalize dependent k.
  generalize dependent LI.
  induction Hpure.
  all: intros LI k Hfilled.
  all: move/lfilledP in Hfilled; inversion Hfilled; subst.
  all: simpl.
  - apply const_es_exists in H4 as [vs ->].
    rewrite e_to_v_v_to_e. by eexists.
  - move/lfilledP in H8.
    apply IHHpure in H8 as [sh ->].
    apply const_es_exists in H7 as [vs ->].
    rewrite e_to_v_v_to_e.
    by eexists.
Qed. 


Lemma susholed_of_lholed_is_pure lh sh :
  susholed_of_lholed lh = Some sh ->
  is_pure lh.
Proof.
  generalize dependent sh.
  induction lh => //=.
  - intros _ _. constructor.
  - intros sh H.
    constructor.
    destruct (susholed_of_lholed lh) => //. 
    eapply IHlh.
    done.
Qed. 


Lemma swholed_of_lholed_is_pure lh sh :
  swholed_of_lholed lh = Some sh ->
  is_pure lh.
Proof.
  generalize dependent sh.
  induction lh => //=.
  - intros _ _. constructor.
  - intros sh H.
    constructor.
    destruct (swholed_of_lholed lh) => //. 
    eapply IHlh.
    done.
Qed.



Lemma exnholed_of_lholed_is_pure lh sh :
  exnholed_of_lholed lh = Some sh ->
  is_pure lh.
Proof.
  generalize dependent sh.
  induction lh => //=.
  - intros _ _. constructor.
  - intros sh H.
    constructor.
    destruct (exnholed_of_lholed lh) => //. 
    eapply IHlh.
    done.
Qed.


Lemma susfill_trans x sh1 sh2 es :
  susfill x (sus_trans sh1 sh2) es = susfill x sh1 (susfill x sh2 es).
Proof.
  induction sh1 => //=.
  all: try rewrite IHsh1 //.
  rewrite susfill_sus_push_const.
  rewrite susfill_sus_append //.
Qed. 

Lemma swfill_trans x sh1 sh2 es :
  swfill x (sw_trans sh1 sh2) es = swfill x sh1 (swfill x sh2 es).
Proof.
  induction sh1 => //=.
  all: try rewrite IHsh1 //.
  rewrite swfill_sw_push_const.
  rewrite swfill_sw_append //.
Qed.

Lemma exnfill_trans x sh1 sh2 es :
  exnfill x (exn_trans sh1 sh2) es = exnfill x sh1 (exnfill x sh2 es).
Proof.
  induction sh1 => //=.
  all: try rewrite IHsh1 //.
  rewrite exnfill_exn_push_const.
  rewrite exnfill_exn_append //.
Qed.

Lemma susfill_to_lfilled i sh es LI lh :
  susfill i sh es = LI ->
  susholed_of_lholed lh = Some sh ->
  exists k, lfilled k lh es LI.
Proof.
  generalize dependent LI.
  generalize dependent sh.
  induction lh => //=.
  - destruct (e_to_v_list_opt l) eqn:Hl => //.
    intros sh LI Hsh Heq; inversion Heq; subst.
    exists 0. simpl.
    apply v_to_e_e_to_v in Hl as <-.
    apply/lfilledP. constructor. apply v_to_e_is_const_list.
  - destruct (susholed_of_lholed lh) eqn:Hholed => //.
    destruct (e_to_v_list_opt l) eqn:Hl => //.
    intros sh LI Hsh Heq; inversion Heq; subst.
    edestruct IHlh as [k Hfill].
    2: done.
    done.
    exists (S k).
    simpl. apply v_to_e_e_to_v in Hl as <-.
    move/lfilledP in Hfill.
    apply/lfilledP. constructor => //.
    apply v_to_e_is_const_list.
Qed. 


Lemma swfill_to_lfilled i sh es LI lh :
  swfill i sh es = LI ->
  swholed_of_lholed lh = Some sh ->
  exists k, lfilled k lh es LI.
Proof.
  generalize dependent LI.
  generalize dependent sh.
  induction lh => //=.
  - destruct (e_to_v_list_opt l) eqn:Hl => //.
    intros sh LI Hsh Heq; inversion Heq; subst.
    exists 0. simpl.
    apply v_to_e_e_to_v in Hl as <-.
    apply/lfilledP. constructor. apply v_to_e_is_const_list.
  - destruct (swholed_of_lholed lh) eqn:Hholed => //.
    destruct (e_to_v_list_opt l) eqn:Hl => //.
    intros sh LI Hsh Heq; inversion Heq; subst.
    edestruct IHlh as [k Hfill].
    2: done.
    done.
    exists (S k).
    simpl. apply v_to_e_e_to_v in Hl as <-.
    move/lfilledP in Hfill.
    apply/lfilledP. constructor => //.
    apply v_to_e_is_const_list.
Qed.

Lemma exnfill_to_lfilled i sh es LI lh :
  exnfill i sh es = LI ->
  exnholed_of_lholed lh = Some sh ->
  exists k, lfilled k lh es LI.
Proof.
  generalize dependent LI.
  generalize dependent sh.
  induction lh => //=.
  - destruct (e_to_v_list_opt l) eqn:Hl => //.
    intros sh LI Hsh Heq; inversion Heq; subst.
    exists 0. simpl.
    apply v_to_e_e_to_v in Hl as <-.
    apply/lfilledP. constructor. apply v_to_e_is_const_list.
  - destruct (exnholed_of_lholed lh) eqn:Hholed => //.
    destruct (e_to_v_list_opt l) eqn:Hl => //.
    intros sh LI Hsh Heq; inversion Heq; subst.
    edestruct IHlh as [k Hfill].
    2: done.
    done.
    exists (S k).
    simpl. apply v_to_e_e_to_v in Hl as <-.
    move/lfilledP in Hfill.
    apply/lfilledP. constructor => //.
    apply v_to_e_is_const_list.
Qed. 

Lemma sus_trans_assoc sh1 sh2 sh3 :
  sus_trans (sus_trans sh1 sh2) sh3 = sus_trans sh1 (sus_trans sh2 sh3).
Proof.
  induction sh1 => //=.
  all: try by rewrite IHsh1.
  destruct sh2 => //=.
  rewrite - sus_push_const_append.
  rewrite sus_push_const_app.
  rewrite sus_append_app //.
Qed.

Lemma sw_trans_assoc sh1 sh2 sh3 :
  sw_trans (sw_trans sh1 sh2) sh3 = sw_trans sh1 (sw_trans sh2 sh3).
Proof.
  induction sh1 => //=.
  all: try by rewrite IHsh1.
  destruct sh2 => //=.
  rewrite - sw_push_const_append.
  rewrite sw_push_const_app.
  rewrite sw_append_app //.
Qed.

Lemma exn_trans_assoc sh1 sh2 sh3 :
  exn_trans (exn_trans sh1 sh2) sh3 = exn_trans sh1 (exn_trans sh2 sh3).
Proof.
  induction sh1 => //=.
  all: try by rewrite IHsh1.
  destruct sh2 => //=.
  rewrite - exn_push_const_append.
  rewrite exn_push_const_app.
  rewrite exn_append_app //.
Qed. 
