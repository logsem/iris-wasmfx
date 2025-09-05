From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Import iris_wasm_lang_properties.
Require Import Coq.Program.Equality.

Set Bullet Behavior "Strict Subproofs".

Fixpoint find_first_some {A : Type} (l : seq.seq (option A)) :=
  match l with
  | [] => None
  | Some e :: q => Some e
  | None :: q => find_first_some q end.

Fixpoint first_instr_instr e :=
  match e with
  | AI_basic (BI_const _) => None
  | AI_basic (BI_ref_null _) => None
  | AI_ref _ => None
  | AI_ref_exn _ _ => None
  | AI_ref_cont _ => None
  | AI_label n es LI =>
    match find_first_some (List.map first_instr_instr LI)
    with Some (e',i) => Some (e',S i) | None => Some (e,0) end
  | AI_frame n es LI =>
    match find_first_some (List.map first_instr_instr LI)
    with Some (e',i) => Some (e',S i) | None => Some (e,0) end
  | AI_handler hs LI =>
      match find_first_some (List.map first_instr_instr LI)
      with Some (e', i) => Some (e', i) | None => Some (e, 0) end
  | AI_prompt tf hs LI =>
      match find_first_some (List.map first_instr_instr LI)
      with Some (e', i) => Some (e', i) | None => Some (e, 0) end
  | _ => Some (e,0) end.

Definition first_instr es :=
  find_first_some (List.map first_instr_instr es).


Lemma first_instr_const vs es :
  const_list vs -> first_instr (vs ++ es) = first_instr es.
Proof.
  intro Hvs.
  induction vs => //=.
  destruct a ; try by inversion Hvs.
  destruct b ; try by inversion Hvs.
  all: simpl in Hvs.
  all: rewrite <- (IHvs Hvs).
  all: by unfold first_instr.
Qed.

Lemma first_instr_app e :
  ∀ a es', first_instr e = Some a -> first_instr (e ++ es') = Some a.
Proof.
  induction e; intros a0 es';try done.
  cbn. destruct (first_instr_instr a) eqn:Ha;auto.
  intros Hf. eapply IHe with (es':=es') in Hf. auto.
Qed.

Lemma first_instr_app_skip e :
  ∀ es', first_instr e = None -> first_instr (e ++ es') = first_instr es'.
Proof.
  induction e; intros a0;try done.
  cbn. destruct (first_instr_instr a) eqn:Ha;auto. done.
  intros Hf. eapply IHe in Hf. eauto.
Qed.

Lemma first_instr_None_const es :
  first_instr es = None -> const_list es.
Proof.
  induction es;auto.
  cbn.
  destruct (first_instr_instr a) eqn:Ha;[done|].
  intros H. apply IHes in H.
  unfold first_instr_instr in Ha.
  destruct a => //.
  destruct b => //.
  - destruct (first_instr l0) eqn:Hl0.
    + unfold first_instr,first_instr_instr in Hl0.
      rewrite Hl0 in Ha. destruct p;done. 
    + unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha.
      done. 
  - destruct (first_instr l1) eqn:Hl0.
    + unfold first_instr,first_instr_instr in Hl0.
      rewrite Hl0 in Ha. destruct p;done. 
    + unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha.
      done.
  - destruct (first_instr l0) eqn:Hl0.
    + unfold first_instr,first_instr_instr in Hl0.
      rewrite Hl0 in Ha. destruct p;done. 
    + unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha.
      done.
  - destruct (first_instr l) eqn:Hl0.
    + unfold first_instr,first_instr_instr in Hl0.
      rewrite Hl0 in Ha. destruct p;done. 
    + unfold first_instr,first_instr_instr in Hl0. rewrite Hl0 in Ha.
      done. 
Qed.

Lemma find_first_const_label es es1 n :
  const_list es ->
  first_instr [AI_label n es1 es] = Some (AI_label n es1 es, 0).
Proof.
  intros Hconst.
  destruct es.
  all: rewrite /first_instr /= //.
  assert (first_instr_instr a = None) as ->.
  { apply andb_true_iff in Hconst as [Hconst _].
    destruct a;try done. destruct b;try done. }
  assert (find_first_some (map first_instr_instr es) = None) as ->.
  { simpl in Hconst.
    apply andb_true_iff in Hconst as [_ Hconst]. clear -Hconst.
    induction es;[done|].
    simpl. apply andb_true_iff in Hconst as [Ha Hconst].
    destruct a;try done. destruct b;try done.
    all: simpl.
    all: apply IHes.
    all: auto. }
  auto. 
Qed.

Lemma first_instr_local es e i n f :
  first_instr es = Some (e,i) ->
  first_instr [AI_frame n f es] = Some (e,S i).
Proof.
  intros Hfirst.
  induction es.
  { inversion Hfirst. }
  { rewrite /first_instr /=.
    rewrite /first_instr /= in Hfirst.
    destruct (first_instr_instr a) eqn:Ha;auto.
    destruct p;eauto. simplify_eq. auto. rewrite Hfirst //. }
Qed.

Lemma find_first_const es n f :
  const_list es ->
  first_instr [AI_frame n f es] = Some (AI_frame n f es, 0).
Proof.
  intros Hconst.
  destruct es.
  all: rewrite /first_instr /= //.
  assert (first_instr_instr a = None) as ->.
  { apply andb_true_iff in Hconst as [Hconst _].
    destruct a;try done. destruct b;try done. }
  assert (find_first_some (map first_instr_instr es) = None) as ->.
  { simpl in Hconst.
    apply andb_true_iff in Hconst as [_ Hconst]. clear -Hconst.
    induction es;[done|].
    simpl. apply andb_true_iff in Hconst as [Ha Hconst].
    destruct a;try done. destruct b;try done.
    all: simpl.
    all: apply IHes. all: auto. }
  auto. 
Qed.

Lemma starts_with_lfilled e i es k lh les :
  first_instr es = Some (e,i) ->
  lfilled k lh es les ->
  first_instr les = Some (e,i + k).
Proof.
  move => Hf Hlf; move/lfilledP in Hlf.
  move: Hf; move: e i.
  induction Hlf; move => e i Hf; rewrite first_instr_const => //; erewrite first_instr_app => //.
  { rewrite Hf; repeat f_equal; lia. }
  all: apply IHHlf in Hf.
  all: unfold first_instr in * => /=.
  all: rewrite Hf; repeat f_equal; try lia.
Qed.


Lemma starts_with_hfilled e i es k lh les :
  first_instr es = Some (e,i) ->
  hfilled k lh es les ->
  exists i', i' >= i /\ first_instr les = Some (e,i').
Proof.
  move => Hf Hlf; move/hfilledP in Hlf.
  move: Hf; move: e i.
  induction Hlf; move => e i Hf.
  all: rewrite first_instr_const => //.
  { erewrite first_instr_app => //; exists i; split => //; lia. } 
  all: apply IHHlf in Hf as (i' & Hi' & Hf).
  all: unfold first_instr in * => /=.
  all: rewrite Hf; repeat f_equal; try lia.
  all: eexists; split; last done.
  all: lia.
  
Qed.


Lemma starts_implies_not_constant e es :
  first_instr es = Some e ->
  const_list es -> False.
Proof.
  intros Hstart Hconst.
  induction es ; try by inversion Hstart.
  destruct a ; try by inversion Hconst.
  destruct b ; try by inversion Hconst.
  all: simpl in Hconst.
  all: unfold first_instr in Hstart.
  all: unfold first_instr in IHes.
  all: simpl in Hstart.
  all: by apply IHes.
Qed.

Lemma lfilled_implies_starts k lh e es :
  (forall n es' LI, e <> AI_label n es' LI) ->
  (forall n es' LI, e <> AI_frame n es' LI) ->
  (forall n es' LI, e <> AI_prompt n es' LI) ->
  (forall es' LI, e <> AI_handler es' LI) ->
  (is_const e -> False) ->
  lfilled k lh [e] es ->
  first_instr es = Some (e,k).
Proof.
  move => Hnlab Hnloc Hnprompt Hnhandler Hnconst Hlf.
  eapply (starts_with_lfilled e 0) in Hlf => //.
  destruct e => //.
  { destruct b => //; exfalso; by apply Hnconst. }
  all: try by exfalso; apply Hnconst.
  exfalso; by eapply Hnhandler.
  exfalso; by eapply Hnprompt.
  exfalso; by eapply Hnlab.
  exfalso; by eapply Hnloc.
Qed.


Inductive first_instr_Ind : list administrative_instruction -> administrative_instruction -> nat -> Prop :=
| first_instr_const_base vs es a i : const_list vs -> first_instr_Ind es a i -> first_instr_Ind (vs ++ es) a i
| first_instr_trap es : first_instr_Ind (AI_trap :: es) AI_trap 0
| first_instr_invoke es a : first_instr_Ind (AI_invoke a :: es) (AI_invoke a) 0
| first_instr_throw_ref_desugared es vs a i : first_instr_Ind (AI_throw_ref_desugared vs a i :: es) (AI_throw_ref_desugared vs a i) 0
| first_instr_suspend_desugared es vs i : first_instr_Ind (AI_suspend_desugared vs i :: es) (AI_suspend_desugared vs i) 0
| first_instr_switch_desugared es vs k tf i : first_instr_Ind (AI_switch_desugared vs k tf i :: es) (AI_switch_desugared vs k tf i) 0
| first_instr_call_host es tf h cvs : first_instr_Ind (AI_call_host tf h cvs :: es)
                                                      (AI_call_host tf h cvs) 0
| first_instr_local_ind n f es es' a i : first_instr_Ind es a i -> first_instr_Ind (AI_frame n f es :: es') a (S i)
| first_instr_label n es1 es es' a i : first_instr_Ind es a i -> first_instr_Ind (AI_label n es1 es :: es') a (S i)
| first_instr_prompt n es1 es es' a i : first_instr_Ind es a i -> first_instr_Ind (AI_prompt n es1 es :: es') a i
| first_instr_handler es1 es es' a i : first_instr_Ind es a i -> first_instr_Ind (AI_handler es1 es :: es') a i
| first_instr_local_base n f es es' : const_list es -> first_instr_Ind (AI_frame n f es :: es') (AI_frame n f es) 0
| first_instr_label_base n es1 es es' : const_list es -> first_instr_Ind (AI_label n es1 es :: es') (AI_label n es1 es) 0
| first_instr_prompt_base n es1 es es' : const_list es -> first_instr_Ind (AI_prompt n es1 es :: es') (AI_prompt n es1 es) 0
| first_instr_handler_base es1 es es' : const_list es -> first_instr_Ind (AI_handler es1 es :: es') (AI_handler es1 es) 0
| first_instr_basic bi es': (∀ b, bi ≠ BI_const b) -> (forall r, bi <> BI_ref_null r) -> first_instr_Ind (AI_basic bi :: es' ) (AI_basic bi) 0.

Lemma first_instr_Ind_not_empty es a i :
  first_instr_Ind es a i -> es ≠ [].
Proof.
  intros Hf. induction Hf;auto.
  intros Hcontr. destruct vs,es => //.
Qed.

Lemma first_instr_Ind_Equivalent es a i :
  first_instr es = Some (a,i) <-> first_instr_Ind es a i.
Proof.
  revert a i.
  remember (S (length_rec es)) as m.
  assert (length_rec es < m); first lia.
  clear Heqm.
  generalize dependent es.
  induction m;intros es Hm a i; first lia.
  split.
  - intros Hf.
    destruct es;try done.
    destruct a0;try done.
    all: try by cbn in Hf; simplify_eq; constructor. 
    * cbn in Hf.
      rewrite separate1.
      destruct b; try done; simplify_eq; try by constructor.
      all: constructor;auto.
      all: destruct es;try done. 
      all: simpl in Hf.
      all: destruct (first_instr_instr a0) eqn:Ha0; simplify_eq.
      -- unfold first_instr_instr in Ha0.
         destruct a0; try done; simplify_eq; try by constructor.
         destruct b; try done; simplify_eq; try by constructor.
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0.
               fold first_instr_instr in Hl0.
               destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               unfold length_rec in Hm; simpl in Hm.
               unfold length_rec. lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               fold first_instr_instr in Hl0.
               apply first_instr_handler_base.
               apply first_instr_None_const. auto. 
         ++ destruct (first_instr l1) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0.
               destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               rewrite /length_rec /= in Hm; rewrite /length_rec.
               lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               apply first_instr_prompt_base.
               apply first_instr_None_const. auto. 
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr, first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               unfold length_rec in Hm; simpl in Hm.
               unfold length_rec. lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               fold first_instr_instr in Hl0.
               constructor.
               apply first_instr_None_const. auto. 
         ++ destruct (first_instr l) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0.
               destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               rewrite /length_rec /= in Hm; rewrite /length_rec.
               lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               constructor.
               apply first_instr_None_const. auto. 
      -- unfold first_instr_instr in Ha0. destruct a0 => //.
         destruct b  => //.
         1-5: rewrite separate1.
         1-5: apply first_instr_const_base;auto.
         1-5: apply IHm => //.
         1-5: rewrite /length_rec /= in Hm.
         1-5: rewrite /length_rec.
         1-5: lia.
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done. 
         ++ destruct (first_instr l1) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done.
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done. 
         ++ destruct (first_instr l) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done.
      -- unfold first_instr_instr in Ha0.
         destruct a0; try done; simplify_eq; try by constructor.
         destruct b; try done; simplify_eq; try by constructor.
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0.
               fold first_instr_instr in Hl0.
               destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               unfold length_rec in Hm; simpl in Hm.
               unfold length_rec. lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               fold first_instr_instr in Hl0.
               apply first_instr_handler_base.
               apply first_instr_None_const. auto. 
         ++ destruct (first_instr l1) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0.
               destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               rewrite /length_rec /= in Hm; rewrite /length_rec.
               lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               apply first_instr_prompt_base.
               apply first_instr_None_const. auto. 
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr, first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               unfold length_rec in Hm; simpl in Hm.
               unfold length_rec. lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               fold first_instr_instr in Hl0.
               constructor.
               apply first_instr_None_const. auto. 
         ++ destruct (first_instr l) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0.
               destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               rewrite /length_rec /= in Hm; rewrite /length_rec.
               lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               constructor.
               apply first_instr_None_const. auto. 
      -- unfold first_instr_instr in Ha0. destruct a0 => //.
         destruct b  => //.
         1-5: rewrite separate1.
         1-5: apply first_instr_const_base;auto.
         1-5: apply IHm => //.
         1-5: rewrite /length_rec /= in Hm.
         1-5: rewrite /length_rec.
         1-5: lia.
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done. 
         ++ destruct (first_instr l1) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done.
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done. 
         ++ destruct (first_instr l) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done.
    * (* AI_ref *)
      rewrite separate1. constructor;auto.
      destruct es;try done. 
      unfold first_instr in Hf.
      simpl in Hf.
      destruct (first_instr_instr a0) eqn:Ha0; simplify_eq.
      -- unfold first_instr_instr in Ha0.
         destruct a0; try done; simplify_eq; try by constructor.
         destruct b; try done; simplify_eq; try by constructor.
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0.
               fold first_instr_instr in Hl0.
               destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               unfold length_rec in Hm; simpl in Hm.
               unfold length_rec. lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               fold first_instr_instr in Hl0.
               apply first_instr_handler_base.
               apply first_instr_None_const. auto. 
         ++ destruct (first_instr l1) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0.
               destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               rewrite /length_rec /= in Hm; rewrite /length_rec.
               lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               apply first_instr_prompt_base.
               apply first_instr_None_const. auto. 
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr, first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               unfold length_rec in Hm; simpl in Hm.
               unfold length_rec. lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               fold first_instr_instr in Hl0.
               constructor.
               apply first_instr_None_const. auto. 
         ++ destruct (first_instr l) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0.
               destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               rewrite /length_rec /= in Hm; rewrite /length_rec.
               lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               constructor.
               apply first_instr_None_const. auto. 
      -- unfold first_instr_instr in Ha0. destruct a0 => //.
         destruct b  => //.
         1-5: rewrite separate1.
         1-5: apply first_instr_const_base;auto.
         1-5: apply IHm => //.
         1-5: rewrite /length_rec /= in Hm.
         1-5: rewrite /length_rec.
         1-5: lia.
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done. 
         ++ destruct (first_instr l1) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done.
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done. 
         ++ destruct (first_instr l) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done.
    * (* AI_ref *)
      rewrite separate1. constructor;auto.
      destruct es;try done. 
      unfold first_instr in Hf.
      simpl in Hf.
      destruct (first_instr_instr a0) eqn:Ha0; simplify_eq.
      -- unfold first_instr_instr in Ha0.
         destruct a0; try done; simplify_eq; try by constructor.
         destruct b; try done; simplify_eq; try by constructor.
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0.
               fold first_instr_instr in Hl0.
               destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               unfold length_rec in Hm; simpl in Hm.
               unfold length_rec. lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               fold first_instr_instr in Hl0.
               apply first_instr_handler_base.
               apply first_instr_None_const. auto. 
         ++ destruct (first_instr l1) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0.
               destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               rewrite /length_rec /= in Hm; rewrite /length_rec.
               lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               apply first_instr_prompt_base.
               apply first_instr_None_const. auto. 
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr, first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               unfold length_rec in Hm; simpl in Hm.
               unfold length_rec. lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               fold first_instr_instr in Hl0.
               constructor.
               apply first_instr_None_const. auto. 
         ++ destruct (first_instr l) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0.
               destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               rewrite /length_rec /= in Hm; rewrite /length_rec.
               lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               constructor.
               apply first_instr_None_const. auto. 
      -- unfold first_instr_instr in Ha0. destruct a0 => //.
         destruct b  => //.
         1-5: rewrite separate1.
         1-5: apply first_instr_const_base;auto.
         1-5: apply IHm => //.
         1-5: rewrite /length_rec /= in Hm.
         1-5: rewrite /length_rec.
         1-5: lia.
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done. 
         ++ destruct (first_instr l1) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done.
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done. 
         ++ destruct (first_instr l) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done.
    * (* AI_ref *)
      rewrite separate1. constructor;auto.
      destruct es;try done. 
      unfold first_instr in Hf.
      simpl in Hf.
      destruct (first_instr_instr a0) eqn:Ha0; simplify_eq.
      -- unfold first_instr_instr in Ha0.
         destruct a0; try done; simplify_eq; try by constructor.
         destruct b; try done; simplify_eq; try by constructor.
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0.
               fold first_instr_instr in Hl0.
               destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               unfold length_rec in Hm; simpl in Hm.
               unfold length_rec. lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               fold first_instr_instr in Hl0.
               apply first_instr_handler_base.
               apply first_instr_None_const. auto. 
         ++ destruct (first_instr l1) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0.
               destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               rewrite /length_rec /= in Hm; rewrite /length_rec.
               lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               apply first_instr_prompt_base.
               apply first_instr_None_const. auto. 
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr, first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               unfold length_rec in Hm; simpl in Hm.
               unfold length_rec. lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               fold first_instr_instr in Hl0.
               constructor.
               apply first_instr_None_const. auto. 
         ++ destruct (first_instr l) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0.
               destruct p; inversion Ha0; subst.
               apply IHm in Hl0. constructor => //.
               rewrite /length_rec /= in Hm; rewrite /length_rec.
               lia.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. simplify_eq.
               constructor.
               apply first_instr_None_const. auto. 
      -- unfold first_instr_instr in Ha0. destruct a0 => //.
         destruct b  => //.
         1-5: rewrite separate1.
         1-5: apply first_instr_const_base;auto.
         1-5: apply IHm => //.
         1-5: rewrite /length_rec /= in Hm.
         1-5: rewrite /length_rec.
         1-5: lia.
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done. 
         ++ destruct (first_instr l1) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done.
         ++ destruct (first_instr l0) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done. 
         ++ destruct (first_instr l) eqn:Hl0.
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. destruct p;done. 
            ** unfold first_instr,first_instr_instr in Hl0.
               rewrite Hl0 in Ha0. done.
    * cbn in Hf.
      destruct (find_first_some (map first_instr_instr l0)) eqn:Hl0.
      -- destruct p. simplify_eq.
         apply IHm in Hl0. constructor => //.
         rewrite /length_rec /= in Hm. rewrite /length_rec. lia.
      -- simplify_eq. apply first_instr_handler_base.
         apply first_instr_None_const. auto.
    * cbn in Hf.
      destruct (find_first_some (map first_instr_instr l1)) eqn:Hl0.
      -- destruct p. simplify_eq.
         apply IHm in Hl0. constructor => //.
         rewrite /length_rec /= in Hm. rewrite /length_rec. lia.
      -- simplify_eq. apply first_instr_prompt_base.
         apply first_instr_None_const. auto.
    * cbn in Hf.
      destruct (find_first_some (map first_instr_instr l0)) eqn:Hl0.
      -- destruct p. simplify_eq.
         apply IHm in Hl0. constructor => //.
         rewrite /length_rec /= in Hm. rewrite /length_rec. lia.
      -- simplify_eq. constructor.
         apply first_instr_None_const. auto.
    * cbn in Hf.
      destruct (find_first_some (map first_instr_instr l)) eqn:Hl0.
      -- destruct p. simplify_eq.
         apply IHm in Hl0. constructor => //.
         rewrite /length_rec /= in Hm. rewrite /length_rec. lia.
      -- simplify_eq. constructor.
         apply first_instr_None_const. auto.
  - intros H. induction H; subst => //=.
    + rewrite first_instr_const => //.
      destruct vs.
      * apply IHfirst_instr_Ind => //.
      * apply IHm => //.
        unfold length_rec in Hm.
        rewrite cat_app in Hm.
        rewrite map_app /= in Hm.
        unfold length_rec.
        rewrite list_sum_app in Hm.
        destruct a0; try by simpl in Hm; lia.
    + apply IHm in H.
      unfold first_instr => /=.
      unfold first_instr in H. rewrite H. done.
      rewrite /length_rec /= in Hm. rewrite /length_rec. lia.
    + apply IHm in H.
      unfold first_instr => /=.
      unfold first_instr in H. rewrite H. done.
      rewrite /length_rec /= in Hm. rewrite /length_rec. lia.
    + apply IHm in H.
      unfold first_instr => /=.
      unfold first_instr in H. rewrite H. done.
      rewrite /length_rec /= in Hm. rewrite /length_rec. lia.
    + apply IHm in H.
      unfold first_instr => /=.
      unfold first_instr in H. rewrite H. done.
      rewrite /length_rec /= in Hm. rewrite /length_rec. lia.
    + unfold first_instr => /=.
      destruct (find_first_some _) eqn:Hsome => //.
      exfalso; eapply starts_implies_not_constant; eauto.
    + unfold first_instr => /=.
      destruct (find_first_some _) eqn:Hsome => //.
      exfalso; eapply starts_implies_not_constant; eauto.
    + unfold first_instr => /=.
      destruct (find_first_some _) eqn:Hsome => //.
      exfalso; eapply starts_implies_not_constant; eauto.
    + unfold first_instr => /=.
      destruct (find_first_some _) eqn:Hsome => //.
      exfalso; eapply starts_implies_not_constant; eauto.
    + destruct bi => //=.
      by exfalso; eapply H.
      by exfalso; eapply H0.
Qed. 


Lemma llfill_prepend llh vs es lles:
  llfill llh es = lles ->
  const_list vs ->
  exists llh', llfill llh' es = (vs ++ lles).
Proof.
  move => Hllf Hconst.
  apply const_es_exists in Hconst as [vs0 ->].
  destruct llh.
  - eexists (LL_base (vs0 ++ l) l0); simpl in *.
    unfold v_to_e_list; rewrite map_cat -Hllf.
    repeat rewrite cat_app.
    by rewrite - app_assoc.
  
  - eexists (LL_label (vs0 ++ l) n l0 llh l1); simpl in *.
    unfold v_to_e_list; rewrite map_cat -Hllf.
    repeat rewrite cat_app.
    by rewrite - app_assoc.
  
  - eexists (LL_frame (vs0 ++ l) n f llh l0); simpl in *.
    unfold v_to_e_list; rewrite map_cat -Hllf.
    repeat rewrite cat_app.
    by rewrite - app_assoc.
  - eexists (LL_prompt (vs0 ++ l) l0 l1 llh l2); simpl in *.
    unfold v_to_e_list; rewrite map_cat -Hllf.
    repeat rewrite cat_app.
    by rewrite - app_assoc.
  - eexists (LL_handler (vs0 ++ l) l0 llh l1); simpl in *.
    unfold v_to_e_list; rewrite map_cat -Hllf.
    repeat rewrite cat_app.
    by rewrite - app_assoc.
  
Qed.

Lemma first_instr_Ind_llfill es a i:
  first_instr_Ind es a i ->
  (exists llh, llfill llh [a] = es).
Proof.
  move => Hf.
  dependent induction Hf; (try by exists (LL_base [] es)); (try by exists (LL_base [] es')).
  all: destruct IHHf as [llh Hllf]; subst.
  - by eapply llfill_prepend. 
  - by eexists (LL_frame [] n f llh es'). 
  - by eexists (LL_label [] n es1 llh es').
  - by eexists (LL_prompt [] _ _ _ _).
  - by eexists (LL_handler [] _ _ _).
Qed.

Lemma first_instr_llfill es a i:
  first_instr es = Some (a, i) ->
  (exists llh, llfill llh [a] = es).
Proof.
  move => Hf; eapply first_instr_Ind_llfill; by apply first_instr_Ind_Equivalent.
Qed.
