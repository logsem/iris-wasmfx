(** Proof of preservation **)

From Wasm Require Export common.
From Coq Require Import Program.Equality NArith ZArith_base.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

From Wasm Require Export operations datatypes_properties typing opsem properties stdpp_aux.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".
Require Import Lia.

Ltac fold_const0 :=
  match goal with
  | |- context [ AI_basic (BI_const ?v) ] => fold (AI_const (VAL_num v))
  | |- context [ AI_basic (BI_ref_null ?t) ] => fold (AI_const (VAL_ref (VAL_ref_null t)))
  | |- context [ AI_ref ?r ] => fold (AI_const (VAL_ref (VAL_ref_func r)))
  | |- context [ AI_ref_cont ?r ] => fold (AI_const (VAL_ref (VAL_ref_cont r)))
  | |- context [ AI_ref_exn ?r ?t] => fold (AI_const (VAL_ref (VAL_ref_exn r t)))
  | _ => idtac
  end.

Ltac fold_const := repeat fold_const0.
Ltac fold_const_in v H := fold (AI_const (VAL_num v)) in H. 


Definition t_be_value bes : Prop :=
  const_list (to_e_list bes).

Ltac b_to_a_revert :=
  repeat lazymatch goal with
         | H:  to_e_list ?bes = _ |- _ =>
           apply b_e_elim in H; destruct H
         end.

Lemma b_e_elim: forall bes es,
    to_e_list bes = es ->
    bes = to_b_list es /\ es_is_basic es.
Proof.
  by apply properties.b_e_elim.
Qed.

Lemma upd_label_overwrite: forall C l1 l2,
    upd_label (upd_label C l1) l2 = upd_label C l2.
Proof.
  by [].
Qed.

Lemma strip_upd_label: forall C l,
    strip (upd_label C l) = strip C.
Proof.
  done.
Qed.

Lemma strip_upd_local_return: forall C l l0,
    strip (upd_local_return C l l0) = strip C.
Proof.
  done.
Qed.


Lemma BI_const_typing: forall C econst t1s t2s,
    be_typing C [::BI_const econst] (Tf t1s t2s) ->
    t2s = t1s ++ [::T_num (typeof_num econst)].
Proof.
  move => C econst t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.

Lemma BI_ref_null_typing: forall C t t1s t2s,
    be_typing C [::BI_ref_null t] (Tf t1s t2s) ->
    t2s = t1s ++ [::T_ref t].
Proof.
  move => C t t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.

Lemma AI_ref_typing: forall s C r t1s t2s,
    e_typing s C [::AI_ref r] (Tf t1s t2s) ->
    exists t, typeof s (VAL_ref (VAL_ref_func r)) = Some t /\ t2s = t1s ++ [::t].
Proof.
  move => s C r t1s t2s HType.
  gen_ind_subst HType => //.
  - destruct bes => //.
  - apply extract_list1 in H2; inversion H2; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (t & Hto & Ht2s) => //.
    exists t. split => //. rewrite - catA. f_equal. done.
  - eexists. simpl. rewrite H. split => //. (* f_equal. f_equal.
    inversion H0; subst => //.*)
Qed.


Lemma AI_ref_cont_typing: forall s C r t1s t2s,
    e_typing s C [::AI_ref_cont r] (Tf t1s t2s) ->
    exists t, typeof s (VAL_ref (VAL_ref_cont r)) = Some t /\ t2s = t1s ++ [::t].
Proof.
  move => s C r t1s t2s HType.
  gen_ind_subst HType => //.
  - destruct bes => //.
  - apply extract_list1 in H2; inversion H2; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (t & Ht & Hts2) => //.
    subst t2s. exists t. split => //. 
    by rewrite - catA.
  - simpl. rewrite H. eexists. repeat split => //. 
Qed.


Lemma AI_ref_exn_typing: forall s C r t t1s t2s,
    e_typing s C [::AI_ref_exn r t] (Tf t1s t2s) ->
    exists exn, List.nth_error (s_exns s) r = Some exn /\
             e_tag exn = t /\
             t2s = t1s ++ [::T_ref T_exnref].
Proof.
  move => s C r t t1s t2s HType.
  gen_ind_subst HType => //.
  - destruct bes => //.
  - apply extract_list1 in H2; inversion H2; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
(*  - erewrite (IHHType s0 (Logic.eq_refl s0) C0 (Logic.eq_refl C0) r (Logic.eq_refl _) t2s) => //. *)
  - edestruct IHHType as (t' & Ht & Hexn & Hts2) => //.
    subst t2s. exists t'. split => //.  
    by rewrite - catA.
  - simpl. rewrite H. eexists. repeat split => //.  
Qed.

Lemma AI_suspend_desugared_typing: forall s C vs x t1s t2s,
    e_typing s C [::AI_suspend_desugared vs (Mk_tagidx x)] (Tf t1s t2s) ->
    exists t1s' t2s',
      t2s = t1s ++ t2s' /\ e_typing s C (v_to_e_list vs) (Tf [::] t1s') /\ 
        List.nth_error (s_tags s) x = Some (Tf t1s' t2s').
Proof. 
  move => s C n x t1s t2s HType.
  gen_ind_subst HType => //.
  - destruct bes => //.
  - apply extract_list1 in H2; inversion H2; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (t1s' & t2s' & Ht1 & Ht2 & Htags) => //.
    subst t2s. exists t1s', t2s'.
    repeat rewrite catA.
    repeat split => //.  
  - rewrite H. exists t1s, t2s0. repeat split => //. 
Qed.

Lemma AI_const_typing: forall s C econst t1s t2s,
    e_typing s C [::AI_const econst] (Tf t1s t2s) ->
    exists t, typeof s econst = Some t /\ t2s = t1s ++ [::t] /\
      e_typing s C [::AI_const econst] (Tf [::] [::t])
.
Proof.
  move => s C econst t1s t2s HType.
  gen_ind_subst HType => //; try by destruct econst as [|v]; destruct v => //. 
  - destruct bes => //. destruct bes => //.
    inversion H3. destruct econst => //.
    + inversion H1; subst. apply BI_const_typing in H. eexists. split => //. split => //. constructor.
      constructor.
    + destruct v => //. inversion H1; subst. 
      apply BI_ref_null_typing in H. eexists. split => //. split => //. 
      constructor. constructor.
  - apply extract_list1 in H2; inversion H2; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (t & Ht & Htype & Htyping) => //. exists t.
    rewrite -catA. split => //. split => //. by subst. 
  - destruct econst as [|v] => //. destruct v => //=.
    inversion H4; subst.
    rewrite H. inversion Econs; subst; eexists; split => //=.
    split => //; eapply ety_ref; eauto.
(*    + split => //; eapply ety_ref; eauto. *)
  - destruct econst => //. destruct v => //=.
    inversion H4; subst; rewrite H => //.
    eexists. split => //. split => //. eapply ety_ref_cont; eauto.
  - destruct econst => //. destruct v => //.
    inversion H4; subst.
    eexists. split => //. simpl. rewrite H.
    rewrite eq_refl. done.
    split => //.
    eapply ety_ref_exn; eauto.
Qed. 
    

Lemma BI_const2_typing: forall C econst1 econst2 t1s t2s,
    be_typing C [::BI_const econst1; BI_const econst2] (Tf t1s t2s) ->
    t2s = t1s ++ [::T_num (typeof_num econst1); T_num (typeof_num econst2)].
Proof.
  move => C econst1 econst2 t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list2 in H1; inversion H1; subst.
    apply BI_const_typing in HType1; subst.
    apply BI_const_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.

Lemma BI_ref_null2_typing: forall C t1 t2 t1s t2s,
    be_typing C [::BI_ref_null t1; BI_ref_null t2] (Tf t1s t2s) ->
    t2s = t1s ++ [::T_ref t1; T_ref t2].
Proof.
  move => C t1 t2 t1s t2s HType.
  gen_ind_subst HType => //.
  * apply extract_list2 in H1; inversion H1; subst.
    apply BI_ref_null_typing in HType1; subst.
    apply BI_ref_null_typing in HType2; subst.
    by rewrite -catA.
  * rewrite -catA. f_equal.
    -- intros. by subst.
    -- by eapply IHHType.
Qed.

Lemma BI_const_ref_null_typing: forall C v1 t2 t1s t2s,
    be_typing C [:: BI_const v1; BI_ref_null t2] (Tf t1s t2s) ->
    t2s = t1s ++ [::T_num (typeof_num v1); T_ref t2].
Proof.
  move => C v1 t2 t1s t2s HType.
  gen_ind_subst HType.
  * apply extract_list2 in H1; inversion H1; subst.
    apply BI_const_typing in HType1; subst.
    apply BI_ref_null_typing in HType2; subst.
    by rewrite -catA.
  * rewrite -catA. f_equal.
    -- intros. by subst.
    -- by eapply IHHType.
Qed.

Lemma BI_ref_null_const_typing: forall C t1 v2 t1s t2s,
    be_typing C [:: BI_ref_null t1; BI_const v2] (Tf t1s t2s) ->
    t2s = t1s ++ [::T_ref t1; T_num (typeof_num v2)].
Proof.
  move => C v1 t2 t1s t2s HType.
  gen_ind_subst HType.
  * apply extract_list2 in H1; inversion H1; subst.
    apply BI_const_typing in HType2; subst.
    apply BI_ref_null_typing in HType1; subst.
    by rewrite -catA.
  * rewrite -catA. f_equal.
    -- intros. by subst.
    -- by eapply IHHType.
Qed.

  
Lemma AI_const2_typing: forall s C econst1 econst2 t1s t2s,
    e_typing s C [::AI_const econst1; AI_const econst2] (Tf t1s t2s) ->
    exists t1 t2, typeof s econst1 = Some t1 /\ typeof s econst2 = Some t2 /\
    t2s = t1s ++ [::t1; t2] /\
      e_typing s C [::AI_const econst1] (Tf [::] [::t1]) /\
      e_typing s C [::AI_const econst2] (Tf [::] [::t2]).
Proof.
  move => s C econst1 econst2 t1s t2s HType.
  gen_ind_subst HType => //.
  - destruct bes => //. destruct bes => //.  destruct bes => //.
    inversion H3.
    destruct econst1 as [|ref1], econst2 as [|ref2];
      try destruct ref1;
      try destruct ref2;
      inversion H1; inversion H2; subst => //.
    + apply BI_const2_typing in H => //.
      eexists _,_; (repeat split => //); by apply ety_a'; econstructor.
    + apply BI_const_ref_null_typing in H => //.
      eexists _,_; repeat split => //; by apply ety_a'; econstructor.
    + apply BI_ref_null_const_typing in H => //.
      eexists _,_; repeat split => //; by apply ety_a'; constructor.
    + apply BI_ref_null2_typing in H => //.
      eexists _,_; repeat split => //; by apply ety_a'; constructor.
  - apply extract_list2 in H2; inversion H2; subst.
    apply AI_const_typing in HType1 as (t1 & -> & -> & ?).
    apply AI_const_typing in HType2 as (t2 & -> & -> & ?).
    eexists _,_; repeat split => //. by rewrite -catA. 
  - edestruct IHHType as (t1 & t2 & Ht1 & Ht2 & Hres & Htyp1 & Htyp2) => //.
    eexists _,_; repeat split; eauto. rewrite -catA. f_equal.
    done.
Qed. 

Lemma BI_const3_typing: forall C econst1 econst2 econst3 t1s t2s,
    be_typing C [::BI_const econst1; BI_const econst2; BI_const econst3] (Tf t1s t2s) ->
    t2s = t1s ++ [::T_num (typeof_num econst1); T_num (typeof_num econst2); T_num (typeof_num econst3)].
Proof.
  move => C econst1 econst2 econst3 t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list3 in H1; inversion H1; subst.
    apply BI_const2_typing in HType1; subst.
    apply BI_const_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.

Lemma AI_const3_typing: forall s C econst1 econst2 econst3 t1s t2s,
    e_typing s C [::AI_const econst1; AI_const econst2; AI_const econst3] (Tf t1s t2s) ->
    exists t1 t2 t3, typeof s econst1 = Some t1 /\ typeof s econst2 = Some t2 /\
                  typeof s econst3 = Some t3 /\
                  t2s = t1s ++ [::t1; t2; t3] /\
                  e_typing s C [::AI_const econst1] (Tf [::] [::t1]) /\
                  e_typing s C [::AI_const econst2] (Tf [::] [::t2]) /\
                  e_typing s C [::AI_const econst3] (Tf [::] [::t3])
.
Proof.
  move => s C econst1 econst2 econst3 t1s t2s HType.
  gen_ind_subst HType => //.
  - repeat (destruct bes => //).
    destruct econst1 as [|ref1], econst2 as [|ref2], econst3 as [|ref3] => //.
    { inversion H3; subst. apply BI_const3_typing in H; eexists _,_,_; repeat split => //; by apply ety_a'; constructor. }
    all: try destruct ref1 => //.
    all: try destruct ref2 => //.
    all: try destruct ref3 => //.
    all: inversion H3; subst.
    all: gen_ind_subst H; subst => //.
    all: try by edestruct IHbe_typing as (t1 & t2 & t3 & Ht1 & Ht2 & Ht3 & Ht & Htyp1 & Htyp2 & Htyp3) => //; subst; eexists t1,t2,t3; repeat split => //; rewrite -catA. 
    all: apply extract_list3 in H4; inversion H4; subst.
    all: try (apply BI_ref_null_typing in H0; subst => //).
    all: try (apply BI_const_typing in H0; subst => //).
    all: try (apply BI_ref_null2_typing in H; subst => //).
    all: try (apply BI_const2_typing in H; subst => //).
    all: try (apply BI_const_ref_null_typing in H; subst => //).
    all: try (apply BI_ref_null_const_typing in H; subst => //).
    all: eexists _,_,_.
    all: repeat split.
    all: try by rewrite -catA.
    all: try by apply ety_a'; constructor.
  - apply extract_list3 in H2; inversion H2; subst.
    apply AI_const2_typing in HType1 as (t1 & t2 & -> & -> & -> & ? & ?).
    apply AI_const_typing in HType2 as (t & -> & -> & ?).
    eexists _,_,_. repeat split => //. by rewrite -catA.
  - edestruct IHHType as (t1 & t2 & t3 & Ht1 & Ht2 & Ht3 & Ht & Htyp1 & Htyp2 & Htyp3) => //.
    subst; eexists t1, t2, t3; repeat split => //. by rewrite -catA. 
Qed. 

(* No longer true with c_typing inside e_typing *)
(*
Lemma Const_list_typing_empty: forall s C vs ts,
    vs_to_vts s vs = map Some ts ->
    e_typing s C (v_to_e_list vs) (Tf [::] ts).
Proof.
  move => s C vs ts Hvs.
  assert (forall ts', e_typing s C (v_to_e_list vs) (Tf ts' (ts' ++ ts))) as H;
    last by apply (H [::]).
  generalize dependent ts.
  induction vs => //=.
  - destruct ts => //. intros _ ts'. rewrite <- (cats0 ts') at 1. apply ety_weakening.
    apply ety_a' => //. by apply bet_empty.
  - rewrite - cat1s.
    destruct ts => //. intros H; inversion H.
    rewrite (separate1 (AI_const a)).
    intros ts'. eapply et_composition'; eauto.
    + instantiate (1 := ts' ++ [::v]). apply et_weakening_empty_1. destruct a => //.
      * apply ety_a' => //=. constructor => //. inversion H1. constructor.
      * destruct v0 => //=.
        -- apply ety_a' => //. constructor => //. inversion H1. constructor.
        -- simpl in H1. destruct (List.nth_error _ _) eqn:Hfuncs => //.
           inversion H1. eapply ety_ref. exact Hfuncs. done.
        -- simpl in H1. destruct (List.nth_error _ _) eqn:Hconts => //.
           inversion H1. eapply ety_ref_cont => //.
    + rewrite (separate1 v ts) - cat_app catA. apply IHvs. done. 
Qed.
*)


Lemma Unop_typing: forall C t op t1s t2s,
    be_typing C [::BI_unop t op] (Tf t1s t2s) ->
    t1s = t2s /\ exists ts, t1s = ts ++ [::T_num t].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - split => //=. by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    split => //=.
    destruct H0 as [ts' H0].
    exists (ts ++ ts').
    rewrite - catA.
    by rewrite H0.
Qed.

Lemma Ref_is_null_typing: forall C t1s t2s,
    be_typing C [::BI_ref_is_null] (Tf t1s t2s) ->
    exists ts t, t1s = ts ++ [::T_ref t] /\ t2s = ts ++ [::T_num T_i32].
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //.
  - exists [::], t; split => //.
  - apply extract_list1 in Econs; inversion Econs; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (ts' & t' & Hts' & Ht') => //=; subst.
    exists (ts ++ ts'), t'. split => //; by rewrite -catA.
Qed. 
  
Lemma Ref_func_typing: forall C i t1s t2s,
    be_typing C [::BI_ref_func i] (Tf t1s t2s) ->
    exists t, List.nth_error (tc_func_t C) i = Some t /\
           t2s = t1s ++ [:: T_ref (T_funcref t)].
Proof.
  move => C i t1s t2s HType.
  gen_ind_subst HType. 
  - exists t; split => //.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (t' & Hfunc & ?) => //=; subst.
    exists t'. split => //. by rewrite -catA.
Qed. 
  
Lemma Call_reference_typing: forall C i t1s t2s,
    be_typing C [::BI_call_reference i] (Tf t1s t2s) ->
    exists ts t1s' t2s', get_type C i = Some (Tf t1s' t2s') /\
                      t1s = ts ++ t1s' ++ [:: T_ref (T_funcref (Tf t1s' t2s'))] /\
                      t2s = ts ++ t2s'.
Proof.
  move => C i t1s t2s HType.
  gen_ind_subst HType.
  - exists [::], t1s, t2s0. repeat split => //.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (ts' & t1s' & t2s' & Htypes & ? & ?) => //=; subst.
    exists (ts ++ ts'), t1s', t2s'. repeat split => //=; by rewrite -catA.
Qed.
    
Lemma Throw_typing: forall C i t1s t2s,
    be_typing C [::BI_throw i] (Tf t1s t2s) ->
    exists ts t1s', List.nth_error (tc_tags_t C) i = Some (Tf t1s' [::]) /\
                 t1s = ts ++ t1s'.
Proof.
  move => C i t1s t2s HType.
  gen_ind_subst HType.
  - exists t1s, ts. split => //.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (ts' & t1s' & Htags & ?) => //=; subst.
    exists (ts ++ ts'), t1s'. split => //. by rewrite -catA.
Qed.

Lemma Throw_ref_typing: forall C t1s t2s,
    be_typing C [::BI_throw_ref] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [:: T_ref T_exnref]. 
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //.
  - exists t1s. done.
  - apply extract_list1 in Econs as [-> ->].
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (ts' & ?) => //=; subst.
    exists (ts ++ ts'). by rewrite -catA.
Qed.
    
Lemma Contnew_typing: forall C i t1s t2s,
    be_typing C [::BI_contnew i] (Tf t1s t2s) ->
    exists ts tf, get_type C i = Some tf /\
                      t1s = ts ++ [:: T_ref (T_funcref tf)] /\
                      t2s = ts ++ [:: T_ref (T_contref tf)].
Proof.
  move => C i t1s t2s HType.
  gen_ind_subst HType.
  - exists [::], tf; repeat split => //=. 
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (ts' & tf & Htypes & ? & ?) => //=; subst.
    exists (ts ++ ts'), tf. repeat split => //=; by rewrite -catA.
Qed.

      
Lemma Resume_typing: forall C i hs t1s t2s,
    be_typing C [:: BI_resume i hs] (Tf t1s t2s) ->
    exists ts t1s' t2s', get_type C i = Some (Tf t1s' t2s') /\
                      List.Forall (fun h => continuation_clause_identifier_typing C h t2s') hs /\
                      t1s = ts ++ t1s' ++ [:: T_ref (T_contref (Tf t1s' t2s'))] /\
                      t2s = ts ++ t2s'.
Proof.
  move => C i hs t1s t2s HType.
  gen_ind_subst HType.
  - exists [::], t1s, t2s0; repeat split => //=.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (ts' & t1s' & t2s' & Htypes & Hclauses & ? & ?) => //=; subst.
    exists (ts ++ ts'), t1s', t2s'. repeat split => //=; by rewrite -catA.
Qed.


Lemma Suspend_typing: forall C i t1s t2s,
    be_typing C [:: BI_suspend i] (Tf t1s t2s) ->
    exists ts t1s' t2s', get_tag C i = Some (Tf t1s' t2s') /\
                      t1s = ts ++ t1s' /\
                      t2s = ts ++ t2s'.
Proof.
  move => C i t1s t2s HType.
  gen_ind_subst HType.
  - exists [::], t1s, t2s. repeat split => //.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (ts' & t1s' & t2s' & Htags & ? & ?) => //=; subst.
    exists (ts ++ ts'), t1s', t2s'. repeat split => //=; by rewrite -catA.
Qed.

Lemma Switch_typing: forall C x i t1s t2s,
    be_typing C [:: BI_switch x i] (Tf t1s t2s) ->
    exists ts tf t1s' t2s' tpref, get_tag C i = Some (Tf [::] ts) /\
          get_type C x = Some tf /\
          tf = Tf (t1s' ++ [::T_ref (T_contref (Tf t2s' ts))]) ts /\
          t1s = tpref ++ t1s' ++ [:: T_ref (T_contref tf)] /\
                               t2s = tpref ++ t2s'.
Proof.
  move => C x i t1s t2s HType.
  gen_ind_subst HType.
  - inversion H4; subst t2s0.
    eexists ts, _, t1s, _, [::].
    repeat split => //.
    exact H0.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (ts' & tf & t1s' & t2s' & tpref & Htags & Htypes & ? & ? & ?) => //=.
    do 5 eexists.
    split.
    exact Htags.
    split.
    exact Htypes.
    split.
    exact H.
    split.
    instantiate (1 := ts ++ tpref).
    rewrite H0.
    rewrite -catA. done.
    rewrite -catA H1. done.
Qed.

Lemma AI_switch_desugared_typing: forall s C vs k tf i t1s t2s,
    e_typing s C [:: AI_switch_desugared vs k tf (Mk_tagidx i)] (Tf t1s t2s) ->
    exists ts t1s' t2s' cont,
      List.nth_error (s_tags s) i = Some (Tf [::] ts) /\
        List.nth_error (s_conts s) k = Some cont /\
        typeof_cont cont = tf /\
        e_typing s C (v_to_e_list vs) (Tf [::] t1s') /\
        tf = Tf (t1s' ++ [::T_ref (T_contref (Tf t2s' ts))]) ts /\
        t2s = t1s ++ t2s'.
Proof.
  move => s C vs k tf i t1s t2s HType.
  gen_ind_subst HType.
  - destruct bes => //.
  - apply extract_list1 in H2; inversion H2; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (ts' & t1s' & t2s' & cont & Htags &Hcont & Htype & Hvs & ? & ?) => //=.
    repeat eexists.
    exact Htags.
    exact Hcont.
    exact Htype.
    exact Hvs.
    exact H.
    rewrite H0.
    rewrite -catA. done.
  - repeat eexists. 
    exact H. exact H1. exact H2. done.
Qed.

Lemma AI_throw_ref_desugared_typing: forall s C vs a i t1s t2s,
    e_typing s C [::AI_throw_ref_desugared vs a i] (Tf t1s t2s) ->
    exists exn, 
      List.nth_error (s_exns s) a = Some exn /\
        i = e_tag exn /\
        vs = e_fields exn
. 
Proof.
  move => s C vs a i t1s t2s HType.
  gen_ind_subst HType => //.
  - destruct bes => //=. 
  - apply extract_list1 in Econs as [-> ->].
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (exn & Hexn & ? & ?) => //=; subst.
    exists exn. done. 
  - exists exn. done.
Qed.
  
Lemma Contbind_typing: forall C i i' t1s t2s,
    be_typing C [::BI_contbind i i'] (Tf t1s t2s) ->
    exists ts t0s t1s' t2s',
      get_type C i = Some (Tf (t0s ++ t1s') t2s') /\
        get_type C i' = Some (Tf t1s' t2s') /\
        t1s = ts ++ t0s ++ [::T_ref (T_contref (Tf (t0s ++ t1s') t2s'))] /\
        t2s = ts ++ [::T_ref (T_contref (Tf t1s' t2s'))].
Proof.
  move => C i i' t1s t2s HType.
  gen_ind_subst HType.
  - exists [::], ts, t1s, t2s. repeat split => //.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (ts' & t0s & t1s' & t2s' & Htypes1 & Htypes2 & ? & ?) => //=; subst.
    exists (ts ++ ts'), t0s, t1s', t2s'. repeat split => //=; by rewrite -catA.
Qed. 

    
Lemma Resume_throw_typing: forall C i x hs t1s t2s,
    be_typing C [::BI_resume_throw i x hs] (Tf t1s t2s) ->
    exists ts t1s' t2s' t0s,
      get_type C i = Some (Tf t1s' t2s') /\
        List.nth_error (tc_tags_t C) x = Some (Tf t0s [::]) /\
        List.Forall (fun h => continuation_clause_identifier_typing C h t2s') hs /\
        t1s = ts ++ t0s ++ [::T_ref (T_contref (Tf t1s' t2s'))] /\
        t2s = ts ++ t2s'.
Proof.
  move => C i x hs t1s t2s HType.
  gen_ind_subst HType.
  - exists [::], t1s, t2s0, ts. repeat split => //. 
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (ts' & t1s' & t2s' & t0s & Htypes & Htags & Hclauses & ? & ?) => //=; subst.
    exists (ts ++ ts'), t1s', t2s', t0s. repeat split => //=; by rewrite -catA.
Qed.



Lemma Binop_typing: forall C t op t1s t2s,
    be_typing C [::BI_binop t op] (Tf t1s t2s) ->
    t1s = t2s ++ [::T_num t] /\ exists ts, t2s = ts ++ [::T_num t].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - split => //=. by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    split => //=.
    + destruct H0 as [ts' H0].
      by rewrite - catA.
    + destruct H0 as [ts' H0].
      exists (ts ++ ts').
      subst.
      by rewrite - catA.
Qed.

Lemma Testop_typing: forall C t op t1s t2s,
    be_typing C [::BI_testop t op] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::T_num t] /\ t2s = ts ++ [::T_num T_i32].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Relop_typing: forall C t op t1s t2s,
    be_typing C [::BI_relop t op] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::T_num t; T_num t] /\ t2s = ts ++ [::T_num T_i32].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Cvtop_typing: forall C t1 t2 op sx t1s t2s,
    be_typing C [::BI_cvtop t2 op t1 sx] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::T_num t1] /\ t2s = ts ++ [::T_num t2].
Proof.
  move => C t1 t2 op sx t1s t2s HType.
  gen_ind_subst HType.
  - by exists [::].
  - by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Nop_typing: forall C t1s t2s,
    be_typing C [::BI_nop] (Tf t1s t2s) ->
    t1s = t2s.
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list1 in Econs; destruct Econs; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - f_equal. by eapply IHHType.
Qed.

Lemma Drop_typing: forall C t1s t2s,
    be_typing C [::BI_drop] (Tf t1s t2s) ->
    exists t, t1s = t2s ++ [::t].
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //=.
  - by eauto.
  - apply extract_list1 in Econs; destruct Econs; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    exists x. repeat rewrite -catA. by f_equal.
Qed.

Lemma Select_typing: forall C t1s t2s,
    be_typing C [::BI_select] (Tf t1s t2s) ->
    exists ts t, t1s = ts ++ [::t; t; T_num T_i32] /\ t2s = ts ++ [::t].
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //.
  - by exists [::], t.
  - apply extract_list1 in Econs; destruct Econs; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    edestruct H as [x2 [H3 H4]]; subst.
    exists (ts ++ x), x2. by split; repeat rewrite -catA.
Qed.

Lemma If_typing: forall C t1s t2s e1s e2s ts ts',
    be_typing C [::BI_if (Tf t1s t2s) e1s e2s] (Tf ts ts') ->
    exists ts0, ts = ts0 ++ t1s ++ [::T_num T_i32] /\ ts' = ts0 ++ t2s /\
                be_typing (upd_label C ([:: t2s] ++ tc_label C)) e1s (Tf t1s t2s) /\
                be_typing (upd_label C ([:: t2s] ++ tc_label C)) e2s (Tf t1s t2s).
Proof.
  move => C t1s t2s e1s e2s ts ts' HType.
  gen_ind_subst HType.
  - by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_btyping in HType1. subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    destruct H as [H1 [H2 [H3 H4]]]. subst.
    exists (ts ++ x).
    repeat rewrite -catA.
    repeat split => //=.
Qed.

Lemma Br_if_typing: forall C ts1 ts2 i,
    be_typing C [::BI_br_if i] (Tf ts1 ts2) ->
    exists ts ts', ts2 = ts ++ ts' /\ ts1 = ts2 ++ [::T_num T_i32] /\ i < length (tc_label C) /\ plop2 C i ts'.
Proof.
  move => C ts1 ts2 i HType.
  gen_ind_subst HType.
  - unfold plop2 in H0.
    by exists [::], ts2.
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - rewrite -catA. f_equal => //=.
    edestruct IHHType => //=.
    destruct H as [ts' [H1 [H2 [H3 H4]]]].
    exists (ts ++ x), ts'. subst.
    split.
    + repeat rewrite -catA. by f_equal.
    + split => //=.
Qed.

Lemma Br_table_typing: forall C ts1 ts2 ids i0,
    be_typing C [::BI_br_table ids i0] (Tf ts1 ts2) ->
    exists ts1' ts, ts1 = ts1' ++ ts ++ [::T_num T_i32] /\
                         all (fun i => (i < length (tc_label C)) && (plop2 C i ts)) (ids ++ [::i0]).
Proof.
  move => C ts1 ts2 ids i0 HType.
  gen_ind_subst HType.
  - by exists t1s, ts.
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [ts' [H1 H2]].
    exists (ts ++ x), ts'. subst.
    split => //=.
    + repeat rewrite -catA. by f_equal => //=.
Qed.



Lemma Tee_local_typing: forall C i ts1 ts2,
    be_typing C [::BI_tee_local i] (Tf ts1 ts2) ->
    exists ts t, ts1 = ts2 /\ ts1 = ts ++ [::t] /\ i < length (tc_local C) /\
                 List.nth_error (tc_local C) i = Some t.
Proof.
  move => C i ts1 ts2 HType.
  gen_ind_subst HType.
  - by exists [::], t.
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [t [H1 [H2 [H3 H4]]]]. subst.
    exists (ts ++ x), t. subst.
    repeat (try split => //=).
    by rewrite -catA.
Qed.

Lemma Const_list_typing: forall s C vs t1s t2s,
    e_typing s C (v_to_e_list vs) (Tf t1s t2s) ->
    exists ts, map (typeof s) vs = map Some ts /\ t2s = t1s ++ ts /\
      e_typing s C (v_to_e_list vs) (Tf [::] ts).
Proof.
  move => s C vs.
  induction vs => //=; move => t1s t2s HType.
  - apply empty_typing in HType. subst. exists [::]. split => //. split; first by rewrite cats0.
    apply ety_a' => //. apply bet_empty.
  - rewrite -cat1s in HType.
    rewrite -cat1s.
    apply e_composition_typing in HType.
    destruct HType as [ts [ts1' [ts2' [ts3 [H1 [H2 [H3 H4]]]]]]].
    subst.
    apply AI_const_typing in H3 as (t & ? & ? & ?).
    apply IHvs in H4 as (ts' & Hts & Ht2s & Htyping).
    subst.
    eexists (_ :: _). split => //=. rewrite H. rewrite Hts. done.
    split; first repeat rewrite - catA => //=.
    rewrite separate1.
    eapply et_composition'.
    exact H1. rewrite <- (cats0 [:: t]) at 1. rewrite (separate1 t ts'). apply ety_weakening. exact Htyping.
Qed.

Ltac invert_be_typing:=
  repeat lazymatch goal with
  | H: (?es ++ [::?e])%list = [::_] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _; _] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _; _; _] |- _ =>
    extract_listn
  | H: be_typing _ [::] _ |- _ =>
    apply empty_btyping in H; subst
  | H: be_typing _ [:: BI_const _] _ |- _ =>
    apply BI_const_typing in H; subst
  | H: be_typing _ [:: BI_const _; BI_const _] _ |- _ =>
    apply BI_const2_typing in H; subst
  | H: be_typing _ [:: BI_const _; BI_const _; BI_const _] _ |- _ =>
      apply BI_const3_typing in H; subst
    | H: be_typing _ [::BI_ref_null _] _ |- _ =>
        apply BI_ref_null_typing in H; subst
    | H: be_typing _ [::BI_ref_null _; BI_ref_null _] _ |- _ =>
        apply BI_ref_null2_typing in H; subst
    | H: be_typing _ [::BI_ref_null _; BI_const _] _ |- _ =>
        apply BI_ref_null_const_typing in H; subst
    | H: be_typing _ [::BI_const _; BI_ref_null _] _ |- _ =>
        apply BI_const_ref_null_typing in H; subst
  | H: be_typing _ [::BI_unop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Unop_typing in H; destruct H as [H1 [ts H2]]; subst
    | H:be_typing _ [:: BI_ref_is_null] _ |- _ =>
        let ts := fresh "ts" in
        let t := fresh "t" in
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        apply Ref_is_null_typing in H; destruct H as (ts & t & H1 & H2); subst
    | H: be_typing _ [:: BI_ref_func _] _ |- _ =>
        let t := fresh "t" in
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        apply Ref_func_typing in H; destruct H as (t & H1 & H2); subst
    | H: be_typing _ [:: BI_call_reference _ ] _ |- _ =>
        let ts := fresh "ts" in
        let t1s := fresh "t1s" in
        let t2s := fresh "t2s" in
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        let H3 := fresh "H3" in
        apply Call_reference_typing in H; destruct H as (ts & t1s & t2s & H1 & H2 & H3); subst
    | H: be_typing _ [:: BI_throw _ ] _ |- _ =>
        let ts := fresh "ts" in
        let t1s := fresh "t1s" in
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        apply Throw_typing in H; destruct H as (ts & t1s & H1 & H2); subst
    | H: be_typing _ [:: BI_contnew _ ] _ |- _ =>
        let ts := fresh "ts" in
        let t1s := fresh "t1s" in
        let t2s := fresh "t2s" in
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        let H3 := fresh "H3" in
        apply Contnew_typing in H; destruct H as (ts & t1s & t2s & H1 & H2 & H3); subst
    | H: be_typing _ [::BI_resume _ _] _ |- _ =>
        let ts := fresh "ts" in
        let t1s := fresh "t1s" in
        let t2s := fresh "t2s" in
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        let H3 := fresh "H3" in
        let H4 := fresh "H4" in
        apply Resume_typing in H; destruct H as (ts & t1s & t2s & H1 & H2 & H3 & H4); subst
    | H : be_typing _ [:: BI_suspend _ ] _ |- _ =>
        let ts := fresh "ts" in
        let t1s := fresh "t1s" in
        let t2s := fresh "t2s" in
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        let H3 := fresh "H3" in
        apply Suspend_typing in H; destruct H as (ts & t1s & t2s & H1 & H2 & H3); subst
    | H : be_typing _ [:: BI_contbind _ _] _ |- _ =>
        let ts := fresh "ts" in
        let t0s := fresh "t0s" in
        let t1s := fresh "t1s" in
        let t2s := fresh "t2s" in
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        let H3 := fresh "H3" in
        let H4 := fresh "H4" in
        apply Contbind_typing in H; destruct H as (ts & t0s & t1s & t2s & H1 & H2 & H3 & H4); subst
    | H: be_typing _ [:: BI_resume_throw _ _ _] _ |- _ =>
        let ts := fresh "ts" in
        let t1s := fresh "t1s" in
        let t2s := fresh "t2s" in
        let t0s := fresh "t0s" in
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        let H3 := fresh "H3" in
        let H4 := fresh "H4" in
        let H5 := fresh "H5" in
        apply Resume_throw_typing in H; destruct H as (ts & t1s & t2s & t0s & H1 & H2 & H3 & H4 & H5); subst
  | H: be_typing _ [::BI_binop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Binop_typing in H; destruct H as [H1 [ts H2]]; subst
  | H: be_typing _ [::BI_testop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Testop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_relop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Relop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_cvtop _ _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Cvtop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_drop] _ |- _ =>
    apply Drop_typing in H; destruct H; subst
  | H: be_typing _ [::BI_select] _ |- _ =>
    let ts := fresh "ts" in
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Select_typing in H; destruct H as [ts [t [H1 H2]]]; subst
  | H: be_typing _ [::BI_if _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply If_typing in H; destruct H as [ts [H1 [H2 [H3 H4]]]]; subst
  | H: be_typing _ [::BI_br_if _] _ |- _ =>
    let ts := fresh "ts" in
    let ts' := fresh "ts'" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Br_if_typing in H; destruct H as [ts [ts' [H1 [H2 [H3 H4]]]]]; subst
  | H: be_typing _ [::BI_br_table _ _] _ |- _ =>
    let ts := fresh "ts" in
    let ts' := fresh "ts'" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Br_table_typing in H; destruct H as [ts [ts' [H1 H2]]]; subst
  | H: be_typing _ [::BI_tee_local _] _ |- _ =>
    let ts := fresh "ts" in
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Tee_local_typing in H; destruct H as [ts [t [H1 [H2 [H3 H4]]]]]; subst
  | H: be_typing _ (_ ++ _) _ |- _ =>
    let ts1 := fresh "ts1" in
    let ts2 := fresh "ts2" in
    let ts3 := fresh "ts3" in
    let ts4 := fresh "ts4" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply composition_typing in H; destruct H as [ts1 [ts2 [ts3 [ts4 [H1 [H2 [H3 H4]]]]]]]
  | H: be_typing _ [::_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: be_typing _ [::_;_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: be_typing _ [::_;_;_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: _ ++ [::_] = _ ++ [::_] |- _ =>
    apply concat_cancel_last in H; destruct H; subst
  end.

Lemma app_binop_type_preserve: forall op v1 v2 v,
    app_binop op v1 v2 = Some v ->
    typeof_num v = typeof_num v1.
Proof.
  move => op v1 v2 v.
  by elim: op; elim: v1; elim: v2 => //=; move => c1 c2 op H; destruct op; remove_bools_options.
Qed.

Lemma t_Unop_preserve: forall C v t op be tf,
    be_typing C [:: BI_const v; BI_unop t op] tf ->
    reduce_simple (to_e_list [::BI_const v; BI_unop t op]) (to_e_list [::be]) ->
    be_typing C [::be] tf.
Proof.
  move => C v t op be tf HType HReduce.
  destruct tf as [ts1 ts2].
  inversion HReduce; b_to_a_revert; subst.
  invert_be_typing.
  rewrite catA.
  apply bet_weakening_empty_1.
  replace (typeof_num v) with (typeof_num (app_unop op v)); first by apply bet_const.
  by destruct op; destruct v.
Qed.

Lemma t_Binop_preserve_success: forall C v1 v2 t op be tf,
    be_typing C [:: BI_const v1; BI_const v2; BI_binop t op] tf ->
    reduce_simple (to_e_list [::BI_const v1; BI_const v2; BI_binop t op]) (to_e_list [::be]) ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 t op be tf HType HReduce.
  destruct tf as [ts1 ts2].
  inversion HReduce; b_to_a_revert; subst.
  invert_be_typing.
  rewrite catA in H1. apply concat_cancel_last in H1. destruct H1; subst.
  repeat rewrite catA.
  apply bet_weakening_empty_1.
  apply app_binop_type_preserve in H0.
  rewrite -H1. rewrite -H0.
  by apply bet_const.
Qed.

Lemma t_Testop_i32_preserve: forall C c testop tf,
    be_typing C [::BI_const (VAL_int32 c); BI_testop T_i32 testop] tf ->
    be_typing C [::BI_const (VAL_int32 (wasm_bool (app_testop_i testop c)))] tf.
Proof.
  move => C c testop tf HType.
  gen_ind_subst HType.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1. simpl.
    apply bet_const.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType.
Qed.

Lemma t_Testop_i64_preserve: forall C c testop tf,
    be_typing C [::BI_const (VAL_int64 c); BI_testop T_i64 testop] tf ->
    be_typing C [::BI_const (VAL_int32 (wasm_bool (app_testop_i testop c)))] tf.
Proof.
  move => C c testop tf HType.
  gen_ind_subst HType.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1. simpl.
    by apply bet_const.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType.
Qed.

Lemma t_Relop_preserve: forall C v1 v2 t be op tf,
    be_typing C [::BI_const v1; BI_const v2; BI_relop t op] tf ->
    reduce_simple [:: AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] [::AI_basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 t be op tf HType HReduce.
  destruct tf as [ts1 ts2].
  inversion HReduce; subst.
  invert_be_typing.
  replace ([::T_num t;T_num t]) with ([::T_num t] ++ [::T_num t]) in H2 => //.
  rewrite catA in H2.
  apply concat_cancel_last in H2. destruct H2 as [H3 H4]. subst.
  rewrite catA in H1.
  apply concat_cancel_last in H1. destruct H1 as [H5 H6]. subst.
  repeat rewrite catA.
  apply bet_weakening_empty_1.
  by apply bet_const.
Qed.

Lemma typeof_deserialise: forall v t,
  typeof_num (wasm_deserialise v t) = t.
Proof.
  move=> v. by case.
Qed.

Lemma be_typing_const_deserialise: forall C v t,
    be_typing C [:: BI_const (wasm_deserialise (bits v) t)] (Tf [::] [:: T_num t]).
Proof.
  move => C v t.
  assert (be_typing C [:: BI_const (wasm_deserialise (bits v) t)] (Tf [::] [:: T_num (typeof_num (wasm_deserialise (bits v) t))])); first by apply bet_const.
  by rewrite typeof_deserialise in H.
Qed.

Lemma t_Convert_preserve: forall C v t1 t2 sx be tf,
    be_typing C [::BI_const v; BI_cvtop t2 CVO_convert t1 sx] tf ->
    reduce_simple [::AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] [::AI_basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v t1 t2 sx be tf HType HReduce.
  inversion HReduce; subst. rename H5 into E.
  gen_ind_subst HType.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1.
    by destruct t2; simpl in E;
      match type of E with
        option_map _ ?e = _ => destruct e eqn:HDestruct => //=
      end; inversion E; apply bet_const.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType; eauto.
Qed.

Lemma t_Reinterpret_preserve: forall C v t1 t2 be tf,
    be_typing C [::BI_const v; BI_cvtop t2 CVO_reinterpret t1 None] tf ->
    reduce_simple [::AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] [::AI_basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v t1 t2 be tf HType HReduce.
  inversion HReduce; subst.
  gen_ind_subst HType.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1.
    apply be_typing_const_deserialise.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType; eauto.
Qed.

Lemma t_Ref_is_null_preserve: forall s C v tf res,
    e_typing s C [::AI_const v; AI_basic BI_ref_is_null] tf ->
    reduce_simple [::AI_const v; AI_basic BI_ref_is_null] [::res] ->
    e_typing s C [::res] tf.
Proof.
  move => s C v tf res HType Hred.
  destruct tf as [ts1 ts2].
  rewrite (separate1 (AI_const _)) in HType.
  eapply e_composition_typing in HType as (ts & ts1' & ts2' & tres & -> & -> & Hv & Hop).
  apply et_to_bet in Hop; last by constructor.
  apply Ref_is_null_typing in Hop as (ts' & t & -> & ->).
  apply AI_const_typing in Hv as (t' & Ht & Hv & Hv').
  apply concat_cancel_last in Hv as [-> Htv].
  apply ety_weakening. apply et_weakening_empty_1.
  inversion Hred.
  all: try by apply ety_a'; econstructor.
  all: try by repeat (destruct vs => //).
  unfold lfilled, lfill in H2.
  destruct lh => //.
  - destruct (const_list l) => //. move/eqP in H2.
    destruct l => //. destruct v => //. destruct v => //.
    destruct l => //.
    destruct l => //.
  - destruct (const_list l) => //. fold lfill in H2.
    destruct (lfill _ _ _) => //.
    move/eqP in H2. destruct l => //. destruct v => //.
    destruct v => //. destruct l => //.
    destruct l => //.
      - destruct (const_list l) => //. fold lfill in H2.
    destruct (lfill _ _ _) => //.
    move/eqP in H2. destruct l => //. destruct v => //.
    destruct v => //. destruct l => //.
    destruct l => //.
Qed. 
  
  
  


Lemma t_Drop_preserve: forall s C v tf,
    e_typing s C [::AI_const v; AI_basic BI_drop] tf ->
    e_typing s C [::] tf.
Proof.
  move => s C v tf HType.
  destruct tf as [ts1 ts2].
  rewrite (separate1 (AI_const _)) in HType.
  eapply e_composition_typing in HType as (ts & ts1' & ts2' & tres & -> & -> & Hv & Hop).
  apply et_to_bet in Hop; last by constructor.
  apply Drop_typing in Hop as (tsb & ->).
  apply AI_const_typing in Hv as (t & _ & Hv & _).
  apply concat_cancel_last in Hv as [-> ->].
  apply et_weakening_empty_both.
  apply ety_a' => //. constructor.
Qed.


Lemma t_Select_preserve: forall s C v1 v2 n tf be,
    e_typing s C [::AI_const v1; AI_const v2; AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select] tf ->
    reduce_simple [::AI_const v1; AI_const v2; AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select] [::be]->
    e_typing s C [::be] tf.
Proof.
  move => s C v1 v2 n tf be HType HReduce.
  destruct tf as [ts1 ts2].
  rewrite (separate3 (AI_const _)) in HType.
  eapply e_composition_typing in HType as (ts & ts1' & ts2' & tres & -> & -> & Hv & Hop).
  apply et_to_bet in Hop; last by econstructor.
  apply Select_typing in Hop as (tsb & tb & -> & ->).
  fold (AI_const (VAL_num (VAL_int32 n))) in Hv.
  apply AI_const3_typing in Hv as (t1 & t2 & t3 & Ht1 & Ht2 & Ht3 & Hv' & ? & ? & ?). 
  rewrite (separate2 t1) in Hv'.
  rewrite - cat_app in Hv'. 
  rewrite catA in Hv'.
  rewrite (separate2 tb) in Hv'.
  rewrite - cat_app catA in Hv'. 
  apply concat_cancel_last in Hv' as [Hv' _].
  rewrite (separate1 t1) in Hv'.
  rewrite (separate1 tb) in Hv'.
  rewrite - cat_app - cat_app catA catA in Hv'. 
  apply concat_cancel_last in Hv' as [Hv' ->].
  apply concat_cancel_last in Hv' as [-> Hto].
  rewrite catA. apply et_weakening_empty_1. 
  inversion HReduce; subst; try by do 5 (destruct vs => //).
  - apply const_inj in H2 as ->. apply const_inj in H4 as ->.
    done.
  - apply const_inj in H2 as ->. apply const_inj in H4 as ->.
    exact H. 
  - unfold lfilled, lfill in H5. destruct lh => //.
    + destruct (const_list _) => //.
      apply b2p in H5.
      destruct l; first by destruct v1; destruct v.
      destruct l; first by destruct v2; destruct v.
      destruct l => //. destruct l => //. destruct l => //.
    + destruct (const_list _) => //.
      destruct (lfill _ _) => //.
      move/eqP in H5.
      destruct l; first by destruct v1; destruct v.
      destruct l; first by destruct v2; destruct v.
      do 3 (destruct l => //).
          + destruct (const_list _) => //.
      destruct (lfill _ _) => //.
      move/eqP in H5.
      destruct l; first by destruct v1; destruct v.
      destruct l; first by destruct v2; destruct v.
      do 3 (destruct l => //). 
Qed.

Lemma t_If_be_preserve: forall C c tf0 es1 es2 tf be,
  be_typing C ([::BI_const (VAL_int32 c); BI_if tf0 es1 es2]) tf ->
  reduce_simple (to_e_list [::BI_const (VAL_int32 c); BI_if tf0 es1 es2]) [::AI_basic be] ->
  be_typing C [::be] tf.
Proof.
  move => C c tf0 es1 es2 tf be HType HReduce.
  destruct tf.
  destruct tf0. 
  inversion HReduce; subst.
  - (* if_0 *)
    gen_ind_subst HType => //=.
    + (* Composition *)
      invert_be_typing.
      rewrite catA in H1. apply concat_cancel_last in H1. destruct H1. subst.
      apply bet_weakening.
      by apply bet_block.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
  - (* if_n0 *)
    gen_ind_subst HType => //=.
    + (* Composition *)
      invert_be_typing.
      rewrite catA in H2. apply concat_cancel_last in H2. destruct H2. subst.
      apply bet_weakening.
      by apply bet_block.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=. 
Qed.

Lemma t_Br_if_true_preserve: forall C c i tf be,
    be_typing C ([::BI_const (VAL_int32 c); BI_br_if i]) tf ->
    reduce_simple (to_e_list [::BI_const (VAL_int32 c); BI_br_if i]) [::AI_basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C c i tf be HType HReduce.
  inversion HReduce; subst.
  gen_ind_subst HType => //=.
  - (* Composition *)
    invert_be_typing.
    by apply bet_br => //=. 
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType => //=.
Qed.

Lemma t_Br_if_false_preserve: forall C c i tf,
    be_typing C ([::BI_const (VAL_int32 c); BI_br_if i]) tf ->
    reduce_simple (to_e_list [::BI_const (VAL_int32 c); BI_br_if i]) [::] ->
    be_typing C [::] tf.
Proof.
  move => C c i tf HType HReduce.
  inversion HReduce; subst.
  gen_ind_subst HType => //=.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType => //=.
Qed.

Lemma t_Br_table_preserve: forall C c ids i0 tf be,
    be_typing C ([::BI_const (VAL_int32 c); BI_br_table ids i0]) tf ->
    reduce_simple (to_e_list [::BI_const (VAL_int32 c); BI_br_table ids i0]) [::AI_basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C c ids i0 tf be HType HReduce.
  inversion HReduce; subst.
  (* in range *)
  - dependent induction HType => //=.
    + (* Composition *)
      invert_be_typing.
      rewrite catA in H0. apply concat_cancel_last in H0. destruct H0. subst.
      move/allP in H2.
      assert (HInd: (j < length (tc_label C)) && plop2 C j ts').
      -- apply H2. rewrite mem_cat. apply/orP. left. apply/inP.
         eapply List.nth_error_In. by eauto.
      -- remove_bools_options.
         by apply bet_br => //.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
  (* out of range *)
  - dependent induction HType => //=.
    + (* Composition *)
      invert_be_typing.
      rewrite catA in H1. apply concat_cancel_last in H1. destruct H1. subst.
      move/allP in H2.
      assert (HInd: (i0 < length (tc_label C)) && plop2 C i0 ts').
      -- apply H2. rewrite mem_cat. apply/orP. right. by rewrite mem_seq1.
      -- remove_bools_options.
         by apply bet_br => //.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
Qed.

Lemma t_Tee_local_preserve: forall s C v i tf,
    e_typing s C ([::AI_const v; AI_basic (BI_tee_local i)]) tf ->
    e_typing s C [::AI_const v; AI_const v; AI_basic (BI_set_local i)] tf.
Proof.
  move => s C v i tf HType.
   destruct tf as [ts1 ts2].
  rewrite (separate1 (AI_const _)) in HType.
  eapply e_composition_typing in HType as (ts & ts1' & ts2' & tres & -> & -> & Hv & Hop).
  apply et_to_bet in Hop; last by econstructor.
  apply Tee_local_typing in Hop as (tsb & H1 & H2 & Hres & Hi & HSome).
  apply AI_const_typing in Hv as (t & _ & Hv & ?).
  subst ts2'. rewrite Hres in Hv. 
  apply concat_cancel_last in Hv as [-> ->].
  subst tres. rewrite catA. apply et_weakening_empty_1.
  replace ([::AI_const v; AI_const v; AI_basic (BI_set_local i)]) with ([::AI_const v] ++ [::AI_const v] ++ [::AI_basic (BI_set_local i)]) => //.
  repeat (try rewrite catA; eapply ety_composition) => //.
  + instantiate (1 := ([::t])). done. 
  + instantiate (1 := ([::t] ++ [::t])).
    rewrite <- (cats0 [:: t]) at 1. apply ety_weakening. done. 
  + apply et_weakening_empty_2. apply ety_a'; first by econstructor.
    by apply bet_set_local.
Qed. 


(*
  Preservation for all be_typeable simple reductions.
*)

(*
Theorem t_be_simple_preservation: forall bes bes' es es' C tf,
    be_typing C bes tf ->
    reduce_simple es es' ->
    es_is_basic es ->
    es_is_basic es' ->
    to_e_list bes = es ->
    to_e_list bes' = es' ->
    be_typing C bes' tf.
Proof.
  move => bes bes' es es' C tf HType HReduce HAI_basic1 HAI_basic2 HBES1 HBES2.
  destruct tf.
  inversion HReduce; b_to_a_revert; subst; simpl in HType => //; basic_inversion.
  - (* Unop *)
    by eapply t_Unop_preserve; eauto => //=.
  - (* Binop_success *)
    by eapply t_Binop_preserve_success; eauto => //=.
  - (* testop_i T_i32 *)
    by apply t_Testop_i32_preserve => //.
  - (* testop_i T_i64 *)
    by apply t_Testop_i64_preserve => //.
  - (* relop *)
    by eapply t_Relop_preserve => //=; eauto.
  - (* Cvtop Convert success *)
    eapply t_Convert_preserve => //=.
    apply HType.
    by apply rs_convert_success => //=.
  - (* Cvtop Reinterpret *)
    eapply t_Reinterpret_preserve => //=.
    apply HType.
    by apply rs_reinterpret => //=.
  - (* Ref_is_null *)
    admi t.
  - admi t.
  - (* Nop *)
    apply Nop_typing in HType; subst => /=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - (* Drop *)
    eapply t_Drop_preserve => //=.
    by apply HType.
  - (* Select_false *)
    eapply t_Select_preserve => //=.
    + by apply HType.
    + by apply rs_select_false.
  - (* Select_true *)
    eapply t_Select_preserve => //=.
    + by apply HType.
    + by apply rs_select_true.
  - (* If_0 *)
    eapply t_If_be_preserve => //=.
    + by apply HType.
    + by apply rs_if_false.
  - (* If_n0 *)
    eapply t_If_be_preserve => //=.
    + by apply HType.
    + by apply rs_if_true.
  - (* br_if_0 *)
    eapply t_Br_if_false_preserve => //=.
    + by apply HType.
    + by apply rs_br_if_false.
  - (* br_if_n0 *)
    eapply t_Br_if_true_preserve => //=.
    + by apply HType.
    + by apply rs_br_if_true.
  - (* br_table -- in range *)
    eapply t_Br_table_preserve => //=.
    + by apply HType.
    + by apply rs_br_table.
  - (* br_table -- out of range default *)
    eapply t_Br_table_preserve => //=.
    + by apply HType.
    + by apply rs_br_table_length.
  - (* tee_local *)
    unfold is_const in H.
    destruct v => //. destruct b => //.
    eapply t_Tee_local_preserve => //=.
Qed. *)

Ltac auto_basic :=
  repeat lazymatch goal with
  | |- es_is_basic [::AI_basic _; AI_basic _; AI_basic _; AI_basic _] =>
    simpl; repeat (econstructor => //)
  | |- es_is_basic [::AI_basic _; AI_basic _; AI_basic _] =>
    simpl; repeat (econstructor => //)
  | |- es_is_basic [::AI_basic _; AI_basic _] =>
    simpl; repeat (econstructor => //)
  | |- es_is_basic [::AI_basic _] =>
    simpl; repeat (econstructor => //)
  | |- operations.es_is_basic [::AI_basic _; AI_basic _; AI_basic _; AI_basic _] =>
    simpl; repeat (econstructor => //)
  | |- operations.es_is_basic [::AI_basic _; AI_basic _; AI_basic _] =>
    simpl; repeat (econstructor => //)
  | |- operations.es_is_basic [::AI_basic _; AI_basic _] =>
    simpl; repeat (econstructor => //)
  | |- operations.es_is_basic [::AI_basic _] =>
    simpl; repeat (econstructor => //)
  | |- operations.e_is_basic (AI_basic ?e) =>
      done
end.

Ltac basic_inversion' :=
   repeat lazymatch goal with
         | H: True |- _ =>
           clear H
         | H: es_is_basic (_ ++ _) |- _ =>
           let Ha := fresh H in
           let Hb := fresh H in
           apply basic_concat in H; destruct H as [Ha Hb]
         | H: es_is_basic [::] |- _ =>
           clear H
         | H: es_is_basic [::_] |- _ =>
             try by inversion H
         | H: e_is_basic _ |- _ =>
             simpl in H; try done
         end.

(* No longer true with c_typing in e_typing *)
(*
Lemma t_const_ignores_context: forall s C C' es tf,
    const_list es ->
    e_typing s C es tf ->
    e_typing s C' es tf.
Proof.
  move => s C C' es tf HConst HType.

  remember (rev es) as es'.
  assert (es = rev es'). rewrite Heqes'. symmetry. by apply revK.
  rewrite H.
  generalize dependent tf. generalize dependent es.

  induction es' => //=; move => es HConst HRev1 HRev2 tf HType; destruct tf.
  - subst. simpl in HType. apply empty_typing in HType; subst.
    apply ety_a' => //. apply bet_weakening_empty_both. by apply bet_empty.
  - subst. 
    simpl. rewrite rev_cons. rewrite -cats1.
    simpl in HType. rewrite rev_cons in HType. rewrite -cats1 in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts [t1s' [t2s' [t3s H]]]].
    destruct H as [H1 [H2 [H3 H4]]].
    subst.
    apply ety_weakening.
    rewrite rev_cons in HConst. rewrite -cats1 in HConst.
    apply const_list_split in HConst. destruct HConst.
    
    eapply et_composition'.
    + eapply IHes' => //. 
      -- by apply H.
      -- by rewrite revK.
      -- by apply H3.
    + simpl in H0. move/andP in H0. destruct H0.
      remember [:: a] as x.
      induction H4; inversion Heqx; subst => //.
      induction H2; subst; inversion Heqx; subst => //.
      * constructor. constructor.
      * constructor. constructor.
      * destruct es; last by destruct es.
        inversion H4; subst.
        apply empty_btyping in H2_ as ->.
        by eapply IHbe_typing2.
      * apply ety_weakening.
        by eapply IHbe_typing.
      * destruct es; last by destruct es.
        inversion H4; subst.
        apply empty_typing in H4_ as ->.
        by eapply IHe_typing2.
      * apply ety_weakening.
        by eapply IHe_typing.
      * eapply ety_ref; eauto.
      * eapply ety_ref_cont; eauto.


        
(*        destruct cont; try by constructor.
        inversion H4; subst.
        constructor.
        intros vs x LI Hvs HLI. *)
Qed. 
 *)

Lemma t_const_ignores_context: forall s C C' es tf,
(*    strip C = strip C' -> *)
    const_list es ->
    e_typing s C es tf ->
    e_typing s C' es tf.
Proof.
  move => s C C' es tf (* HC *) HConst HType.

  remember (rev es) as es'.
  assert (es = rev es'). rewrite Heqes'. symmetry. by apply revK.
  rewrite H.
  generalize dependent tf. generalize dependent es.

  induction es' => //=; move => es HConst HRev1 HRev2 tf HType; destruct tf.
  - subst. simpl in HType. apply empty_typing in HType; subst.
    apply ety_a' => //. apply bet_weakening_empty_both. by apply bet_empty.
  - subst. 
    simpl. rewrite rev_cons. rewrite -cats1.
    simpl in HType. rewrite rev_cons in HType. rewrite -cats1 in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts [t1s' [t2s' [t3s H]]]].
    destruct H as [H1 [H2 [H3 H4]]].
    subst.
    apply ety_weakening.
    rewrite rev_cons in HConst. rewrite -cats1 in HConst.
    apply const_list_split in HConst. destruct HConst.
    
    eapply et_composition'.
    + eapply IHes' => //. 
      -- by apply H.
      -- by rewrite revK.
      -- by apply H3.
    + simpl in H0. move/andP in H0. destruct H0.
      remember [:: a] as x.
      induction H4; inversion Heqx; subst => //.
      induction H2; subst; inversion Heqx; subst => //.
      * constructor. constructor.
      * constructor. constructor.
      * destruct es; last by destruct es.
        inversion H4; subst.
        apply empty_btyping in H2_ as ->.
        by eapply IHbe_typing2.
      * apply ety_weakening.
        by eapply IHbe_typing.
      * destruct es; last by destruct es.
        inversion H4; subst.
        apply empty_typing in H4_ as ->.
        by eapply IHe_typing2.
      * apply ety_weakening.
        by eapply IHe_typing.
      * eapply ety_ref; eauto.
      * eapply ety_ref_cont; eauto.
      * eapply ety_ref_exn; eauto.
(*        inversion H4; subst; econstructor.
        exact H5.
        rewrite - HC. exact H6. exact H7. rewrite - HC. exact H8. *)
Qed. 



Lemma Block_typing: forall C t1s t2s es tn tm,
    be_typing C [::BI_block (Tf t1s t2s) es] (Tf tn tm) ->
    exists ts, tn = ts ++ t1s /\ tm = ts ++ t2s /\
               be_typing (upd_label C ([::t2s] ++ (tc_label C))) es (Tf t1s t2s).
Proof.
  move => C t1s t2s es tn tm HType.
  dependent induction HType => //=.
  - by exists [::].
  - invert_be_typing. 
    apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists (ts ++ x).
    repeat rewrite -catA.
    by repeat split => //=.
Qed.

Lemma Loop_typing: forall C t1s t2s es tn tm,
    be_typing C [::BI_loop (Tf t1s t2s) es] (Tf tn tm) ->
    exists ts, tn = ts ++ t1s /\ tm = ts ++ t2s /\
               be_typing (upd_label C ([::t1s] ++ (tc_label C))) es (Tf t1s t2s).
Proof.
  move => C t1s t2s es tn tm HType.
  dependent induction HType => //=.
  - by exists [::].
  - invert_be_typing.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists (ts ++ x).
    repeat rewrite -catA.
    by repeat split => //=.
Qed.

Lemma Try_table_typing: forall C i cs es tn tm,
    be_typing C [:: BI_try_table i cs es] (Tf tn tm) ->
    exists ts t1s t2s,
      get_type C i = Some (Tf t1s t2s) /\
      tn = ts ++ t1s /\ tm = ts ++ t2s /\
              List.Forall (fun c => exception_clause_identifier_typing C c) cs /\
            be_typing (upd_label C ([::t2s] ++ tc_label C)) es (Tf t1s t2s).
Proof.
  move => C i cs es tn tm HType.
  dependent induction HType => //=.
  - by exists [::], tn, tm .
  - invert_be_typing. 
    eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as (tn & tm & H0 & [H1 [H2 H3]]). subst.
    exists (ts ++ x), tn, tm.
    repeat rewrite -catA.
    by repeat split => //=.
Qed.

Lemma Break_typing: forall n C t1s t2s,
    be_typing C [::BI_br n] (Tf t1s t2s) ->
    exists ts ts0, n < size (tc_label C) /\
               plop2 C n ts /\
               t1s = ts0 ++ ts.
Proof.
  move => n C t1s t2s HType.
  dependent induction HType => //=.
  - by exists ts, t1s0.
  - invert_be_typing.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [ts0 [H1 [H2 H3]]]. subst.
    exists x, (ts ++ ts0).
    repeat split => //=.
    by rewrite -catA.
Qed.

Ltac et_dependent_ind H :=
  let Ht := type of H in
  lazymatch Ht with
  | e_typing ?s ?C ?es (Tf ?t1s ?t2s) =>
    let s2 := fresh "s2" in
    let C2 := fresh "C2" in
    let es2 := fresh "es2" in
    let tf2 := fresh "tf2" in
    remember s as s2 eqn:Hrems;
    remember C as C2 eqn:HremC;
    remember es as es2 eqn:Hremes;
    remember (Tf t1s t2s) as tf2 eqn:Hremtf;
    generalize dependent Hrems;
    generalize dependent HremC;
    generalize dependent Hremtf;
    generalize dependent s; generalize dependent C;
    generalize dependent t1s; generalize dependent t2s;
    induction H
  | e_typing ?s ?C ?es ?tf =>
    let s2 := fresh "s2" in
    let C2 := fresh "C2" in
    let es2 := fresh "es2" in
    remember s as s2 eqn:Hrems;
    remember C as C2 eqn:HremC;
    remember es as es2 eqn:Hremes;
    generalize dependent Hrems;
    generalize dependent HremC;
    generalize dependent s; generalize dependent C;
    induction H
  | _ => fail "hypothesis not an e_typing relation"
  end; intros; subst.

Lemma Label_typing: forall s C n es0 es ts1 ts2,
    e_typing s C [::AI_label n es0 es] (Tf ts1 ts2) ->
    exists ts ts2', ts2 = ts1 ++ ts2' /\
                    e_typing s C es0 (Tf ts ts2') /\
                    e_typing s (upd_label C ([::ts] ++ (tc_label C))) es (Tf [::] ts2') /\
                    length ts = n.
Proof.
  move => s C n es0 es ts1 ts2 HType.
  et_dependent_ind HType => //.
  - (* ety_a *)
    assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
    rewrite Hremes in H0. by basic_inversion'.
  - (* ety_composition *)
    apply extract_list1 in Hremes. destruct Hremes. subst.
    apply et_to_bet in HType1 => //.
    simpl in HType1. apply empty_btyping in HType1. subst.
    by eapply IHHType2 => //.
  - (* ety_weakening *)
    edestruct IHHType => //.
    inversion Hremtf; subst.
    destruct H as [ts2' [H1 [H2 [H3 H4]]]]. subst.
    by exists x, ts2'; try rewrite catA.     
  - (* ety_label *)
    inversion Hremes. inversion Hremtf. subst.
    by exists ts, ts2.
Qed.


Lemma Handler_typing: forall s C hs es ts1 ts2,
    e_typing s C [::AI_handler hs es] (Tf ts1 ts2) ->
    exists ts2', ts2 = ts1 ++ ts2' /\
              List.Forall (exception_clause_typing s C) hs /\
      e_typing s C es (Tf [::] ts2').
Proof.
  move => s C hs es ts1 ts2 HType.
  et_dependent_ind HType => //.
  - (* ety_a *)
    assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
    rewrite Hremes in H0. by basic_inversion'.
  - (* ety_composition *)
    apply extract_list1 in Hremes. destruct Hremes. subst.
    apply et_to_bet in HType1 => //.
    simpl in HType1. apply empty_btyping in HType1. subst.
    by eapply IHHType2 => //.
  - (* ety_weakening *)
    edestruct IHHType => //.
(*    subst t2s. destruct H0 as [Hclauses H]. *)
    destruct H as (-> & Hclauses & H). 
    inversion Hremtf; subst. 
    by exists x; try rewrite catA.     
  - (* ety_handler *)
    inversion Hremes. inversion Hremtf. subst.
    by exists ts2.  
Qed.

Lemma Prompt_typing: forall s C ts hs es ts1 ts2,
    e_typing s C [::AI_prompt ts hs es] (Tf ts1 ts2) ->
    (*    exists ts2', *) ts2 = ts1 ++ ts(* 2'*) /\
      List.Forall (fun h => continuation_clause_typing s C h ts) hs /\
      e_typing s empty_context (* (strip C) *) es (Tf [::] ts(*2'*)).
Proof.
  move => s C ts hs es ts1 ts2 HType.
  et_dependent_ind HType => //.
  - (* ety_a *)
    assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
    rewrite Hremes in H0. by basic_inversion'.
  - (* ety_composition *)
    apply extract_list1 in Hremes. destruct Hremes. subst.
    apply et_to_bet in HType1 => //.
    simpl in HType1. apply empty_btyping in HType1. subst.
    by eapply IHHType2 => //.
  - (* ety_weakening *)
    edestruct IHHType => //.
    subst t2s. destruct H0 as [Hclauses H].
(*    destruct H as (-> & Hclauses & H). *)
    inversion Hremtf; subst. 
    by (* exists x; *) try rewrite catA.     
  - (* ety_prompt *)
    inversion Hremes. inversion Hremtf. subst.
    done. (* by exists ts2.  *)
Qed.


(* Fixpoint well_formed hh :=
  match hh with
  | HH_base bef aft => const_list bef
  | HH_label bef _ _ hh _ => const_list bef && well_formed hh
  | HH_local bef _ _ hh _ => const_list bef && well_formed hh
  | HH_handler bef _ hh _ => const_list bef && well_formed hh
  end.

Lemma hfilled_is_well_formed x es hh LI :
  hfilled x hh es LI -> well_formed hh.
Proof.
  generalize dependent LI.
  unfold hfilled, hfill; induction hh ; fold hfill;
    (try fold hfill in IHhh); simpl; destruct (const_list l) => //=.
  - destruct (hfill _ _ _) => //.
    specialize (IHhh l2 (eq_refl l2)).
    intros; done.
  - destruct (hfill _ _ _) => //.
    specialize (IHhh l1 (eq_refl l1)).
    intros; done.
  - destruct x => //.
    destruct (List.forallb _ _) => //.
    all: destruct (hfill _ _ _) => //.
    all: specialize (IHhh l2 (eq_refl l2)).
    all: intros; done.
Qed. *)

Lemma typeof_default_vals s ts:
  map (typeof s) (default_vals ts) = map Some ts.
Proof.
  induction ts => //=.
  rewrite IHts; f_equal.
  destruct a => //=. destruct n => //=.
  destruct r => //=.
Qed. 

Lemma default_vals_typing s C ts:
  e_typing s C (v_to_e_list (default_vals ts)) (Tf [::] ts).
Proof.
  induction ts => //=.
  - apply ety_a' => //. constructor.
  - rewrite separate1. eapply et_composition'.
    2:{ instantiate (1 := [:: a]).
        rewrite (separate1 a ts).
        apply et_weakening_empty_1.
        exact IHts. }
    destruct a => //=.
    + apply ety_a' => //=. constructor => //.
      replace n with (typeof_num (bitzero n)) at 2 => //.
      apply bet_const. unfold bitzero => //. destruct n => //.
    + destruct r => //=.
      * apply ety_a' => //=. constructor => //.
        constructor.
      * apply ety_a' => //=. constructor => //.
        constructor.
      * apply ety_a' => //=. constructor => //.
        constructor.
Qed. 


(*
Lemma c_typing_iff_e_typing s C t1s t2s hh:
  well_formed hh ->
  c_typing s C (Cont_hh (Tf t1s t2s) hh)
  <->
    (forall vs x LI,
        e_typing s C vs (Tf [::] t1s) ->
        hfilled x hh vs LI ->
        e_typing s C LI (Tf [::] t2s)
    ).
Proof.
  intros Hhh.
  move: C t2s.
  induction hh; intros C t2s.
  - split.
    + intros Hc. inversion Hc; subst.
      intros vs x LI Hvs HLI.
      unfold hfilled, hfill in HLI.
      destruct (const_list l) eqn:Hl => //.
      move/eqP in HLI. subst LI.
      eapply et_composition'.
      exact H3.
      eapply et_composition'; last exact H6.
      apply et_weakening_empty_1.
      exact Hvs.
    + intros H.
      remember (v_to_e_list (default_vals t1s)) as ds.
      specialize (H ds 0 (l ++ ds ++ l0)).
      apply e_composition_typing in H as (ts & t1s' & t2s' & t3s & Hts & -> & Hl & Hdsl0);
        last first.
      { unfold hfilled, hfill.
        simpl in Hhh. rewrite Hhh. done. }
      { subst ds. by apply default_vals_typing. } 
      destruct ts => //. destruct t1s' => //.
      apply e_composition_typing in Hdsl0
          as (ts & t1s' & t2s'' & t3s' & -> & -> & Hds & Hl0).
      subst ds.
      apply Const_list_typing in Hds as (tsd & Htsd & -> & Hds).
      rewrite typeof_default_vals in Htsd.
      assert (tsd = t1s) as ->.
      { clear - Htsd. generalize dependent tsd.
        induction t1s; destruct tsd => //=.
        intros Htsd; inversion Htsd; subst.
        rewrite (IHt1s tsd) => //.  } 
      econstructor. exact Hl. rewrite - catA.
      simpl. apply ety_weakening. exact Hl0.
  - split.
    + intros Hc. inversion Hc; subst.
      intros vs x LI Hvs HLI.
      unfold hfilled, hfill in HLI; fold hfill in HLI.
      simpl in Hhh. move/andP in Hhh. destruct Hhh as [Hl Hhh].
      rewrite Hl in HLI.
      destruct (hfill _ _ _) eqn:Hfill => //.
      move/eqP in HLI; subst LI.
      eapply et_composition'. exact H9.
      eapply et_composition'; last exact H12.
      apply et_weakening_empty_1.
      eapply ety_label => //. exact H10.
      eapply IHhh in Hhh. destruct Hhh as [Hhh _].
      eapply Hhh in H11. exact H11.
      
      
*)



Definition leq_t_context C C' :=
  (strip C = strip C' \/ strip C = empty_context) /\
    (exists lloc, tc_local C' = tc_local C ++ lloc) /\
    (exists llab, tc_label C' = tc_label C ++ llab) /\
    (tc_return C = None \/ tc_return C = tc_return C')
.

Lemma strip_leq C : leq_t_context (strip C) C.
Proof.
  split; first by left.
  split; first by exists (tc_local C).
                    split; first by exists (tc_label C).
                                      by left.
Qed.

Lemma leq_strip C C' :
  leq_t_context C C' -> leq_t_context (strip C) (strip C').
Proof.
  intros (HC & [llab Hlab] & [lloc Hloc] & Hret).
  repeat split => //=; try exists [::] => //.
                            by left.
Qed. 

Lemma empty_context_leq C :
  leq_t_context empty_context C.
Proof.
  repeat split => //=.
  by right.
  eexists => //.
  eexists => //. by left.
Qed.

Lemma nth_error_set_nth_hit {A} k l d (x:A) :
  List.nth_error (set_nth d l k x) k = Some x.
Proof.
  generalize dependent k; induction l; intros k => //=.
  - destruct k => //=. induction k => //=.
  - destruct k => //=.
Qed.

Lemma nth_error_prefix {A} l l' i (x : A) :
  List.nth_error l i = Some x ->
  List.nth_error (l ++ l') i = Some x.
Proof.
  move:i. induction l => //=; intros i; destruct i => //=.
  intros H; by apply IHl.
Qed.

Lemma exception_clause_identifier_typing_leq: forall C C' h,
    exception_clause_identifier_typing C h ->
    leq_t_context C C' ->
    exception_clause_identifier_typing C' h.
Proof.
  intros C C' h Htype HC.
  inversion Htype; subst.
  - destruct HC as ([HC | Habs] & [lloc Hloc] & [llab Hlab] & Hret).
    2:{ destruct C; inversion Habs; subst.
        destruct x => //. } 
    econstructor; eauto.
    destruct C; inversion HC; subst. exact H.
    rewrite Hlab.
    apply nth_error_prefix => //.
  - destruct HC as ([HC | Habs] & [lloc Hloc] & [llab Hlab] & Hret).
    2:{ destruct C; inversion Habs; subst.
        destruct x => //. } 
    econstructor 2; eauto.
    destruct C; inversion HC; subst. exact H.
    rewrite Hlab.
    apply nth_error_prefix => //.
  - econstructor; eauto.
    destruct HC as (HC & [lloc Hloc] & [llab Hlab] & Hret).
    rewrite Hlab.
    apply nth_error_prefix => //.
  - econstructor; eauto.
    destruct HC as (HC & [lloc Hloc] & [llab Hlab] & Hret).
    rewrite Hlab.
    apply nth_error_prefix => //.
Qed.

 Lemma exception_clause_typing_leq: forall s C C' h,
    exception_clause_typing s C h ->
    leq_t_context C C' ->
    exception_clause_typing s C' h.
Proof.
  intros s C C' h Htype HC.
  inversion Htype; subst.
  - econstructor; eauto.
    destruct HC as (HC & [lloc Hloc] & [llab Hlab] & Hret).
    rewrite Hlab.
    apply nth_error_prefix => //.
      - econstructor; eauto.
    destruct HC as (HC & [lloc Hloc] & [llab Hlab] & Hret).
    rewrite Hlab.
    apply nth_error_prefix => //.
      - econstructor; eauto.
    destruct HC as (HC & [lloc Hloc] & [llab Hlab] & Hret).
    rewrite Hlab.
    apply nth_error_prefix => //.
      - econstructor; eauto.
    destruct HC as (HC & [lloc Hloc] & [llab Hlab] & Hret).
    rewrite Hlab.
    apply nth_error_prefix => //. 
Qed. 

Lemma continuation_clause_identifier_typing_leq: forall C C' h ts,
    continuation_clause_identifier_typing C h ts ->
    leq_t_context C C' ->
    continuation_clause_identifier_typing C' h ts.
Proof.
  intros C C' h ts Htype HC.
  inversion Htype; subst.
  all: destruct HC as ([HC | Habs] & [lloc Hloc] & [llab Hlab] & Hret).
  2,4: destruct C; inversion Habs; subst;
      destruct x => //. 
  all: econstructor; eauto.
  all: destruct C; inversion HC; subst.
  all: try exact H.
  all: rewrite Hlab.
  all: apply nth_error_prefix => //.
Qed.

 Lemma continuation_clause_typing_leq: forall s C C' h ts,
    continuation_clause_typing s C h ts ->
    leq_t_context C C' ->
    continuation_clause_typing s C' h ts.
 Proof.
   
  intros s C C' h ts Htype HC.
  inversion Htype; subst.
  all: econstructor; eauto.
  destruct HC as (HC & [lloc Hloc] & [llab Hlab] & Hret).
  rewrite Hlab.
  apply nth_error_prefix => //. 
Qed. 

(*
Lemma clause_typing_leq: forall C C' h ts,
    clause_typing C h ts ->
    leq_t_context C C' ->
    clause_typing C' h ts.
Proof.
  intros C C' h ts Htype HC.
  inversion Htype; subst.
  - constructor.
    eapply List.Forall_impl; last exact H.
    intros hc Hhc. eapply exception_clause_typing_leq.
    exact Hhc. exact HC.
  - constructor.
    eapply List.Forall_impl; last exact H.
    intros hc Hhc. eapply continuation_clause_typing_leq.
    exact Hhc. exact HC.
Qed. *)

(*
Lemma catch_ok_leq: forall C C' h,
    catch_ok C h ->
    leq_t_context C C' ->
    catch_ok C' h.
Proof.
  intros C C' h Htype HC.
  inversion Htype; subst.
  all: destruct HC as ([HC | Habs] & [lloc Hloc] & llab & Hlab).
  all: try by  destruct C; inversion Habs; subst;
    destruct x => //. 
  all: econstructor; eauto.
  all: try (destruct C; inversion HC; subst).
  all: try exact H.
  all: rewrite Hlab.
  all: apply nth_error_prefix => //.
Qed. *)


(* Lemma all_impl {A} P Q (l: list A):
  all P l -> (forall x, P x -> Q x) -> all Q l. *)

Lemma leq_upd_label C C' l:
  leq_t_context C C' ->
  leq_t_context (upd_label C (l ++ tc_label C)) (upd_label C' (l ++ tc_label C')).
Proof.
  intros (HC & [lloc Hloc] & [llab Hlab] & Hret).
  repeat split.
  - do 2 rewrite strip_upd_label. done.
  - exists lloc. done.
  - rewrite Hlab. exists llab. destruct C, C'; simpl in *.
    by rewrite catA.
  - simpl. done.
Qed.

(*Lemma leq_get_type C C' i:
  leq_t_context C C' -> get_type C i = get_type C' i.
Proof.
  destruct i => //=.
  intros ([HC | HC] & [lab Hlab] & loc & Hloc); destruct C, C';
    simpl in *; inversion HC; subst => //=.
  destruct i => //=.  *)

Lemma btyping_leq: forall C C' bes tf,
    be_typing C bes tf ->
    leq_t_context C C' ->
    be_typing C' bes tf.
Proof.
  intros C C' bes tf HType Hleq.
  generalize dependent C'. 
  induction HType; econstructor => //.
  all: remember Hleq as Hleq'; clear HeqHleq'.
  all: destruct Hleq as (HC & [lloc Hloc] & [llab Hlab] & Hret).

  all: try (destruct HC as [HC' | Habs];
            last by destruct C; inversion Habs; subst;
            (done + destruct x + (destruct i; try destruct i) +
               (destruct i'; try destruct i0) )).
  all: try by destruct C, C'; inversion HC'; subst.
  all: try by eapply IHHType; try apply leq_upd_label.
  all: try by eapply IHHType1; try apply leq_upd_label.
  all: try by eapply IHHType2; try apply leq_upd_label.
  all: try by move/eqP in H0; apply/eqP; rewrite Hlab; apply nth_error_prefix.
  all: try by rewrite Hloc; apply nth_error_prefix.
  all: try by rewrite Hloc List.length_app; lias.
  - by eapply List.Forall_impl; last exact H0;
    intros hc Hhc; eapply continuation_clause_identifier_typing_leq; eauto; eauto.
(*  - destruct HC as [HC | HC].
    destruct C, C'; inversion HC; subst; destruct x => //.
    destruct C; inversion HC; subst; destruct x => //.
    destruct i => //.  *)
  - unfold get_tag in H. destruct x.
    destruct HC as [HC | HC].
    destruct C, C'; inversion HC; subst; destruct i => //.
    destruct C; inversion HC; subst; destruct i => //.
  - unfold get_tag in H. destruct x.
    destruct HC as [HC | HC].
    destruct C, C'; inversion HC; subst; destruct i => //.
    destruct C; inversion HC; subst; destruct i0 => //.
  - unfold get_tag in H. destruct x.
    destruct HC as [HC | HC].
    destruct C, C'; inversion HC; subst; destruct i => //.
    destruct C; inversion HC; subst; destruct i0 => //.
  - by eapply List.Forall_impl; last exact H1;
    intros hc Hhc; eapply continuation_clause_identifier_typing_leq; eauto; eauto.
  - eapply List.Forall_impl; last exact H0.
    intros hc Hhc; eapply exception_clause_identifier_typing_leq; eauto; eauto.
  - subst C'; eapply IHHType. apply leq_upd_label. done.
  - rewrite Hlab List.length_app. lias. 
  - rewrite Hlab List.length_app. lias.
  - eapply sub_all; last exact H.
    unfold subpred. intros x Hx. move/andP in Hx. destruct Hx as [??].
    apply/andP. split. rewrite Hlab List.length_app; lias.
    apply/eqP. move/eqP in H1. rewrite Hlab. apply nth_error_prefix => //.
  - destruct Hret as [Habs | Hdone].
    by rewrite Habs in H. by rewrite -Hdone H.
Qed.


Lemma typing_leq: forall s C C' es tf,
    e_typing s C es tf ->
    leq_t_context C C' ->
    e_typing s C' es tf.
Proof.
  intros s C C' es tf HType Hleq.
  generalize dependent C'.
  induction HType; econstructor => //.
  all: remember Hleq as Hleq'; clear HeqHleq'.
  all: destruct Hleq as (HC & [lloc Hloc] & [llab Hlab]).
  all: try (destruct HC as [HC' | Habs];
            last by destruct C; inversion Habs; subst;
            (done + destruct x + destruct i)).
  all: try by destruct C, C'; inversion HC'; subst.
  all: try by eapply IHHType; try apply leq_strip.
  all: try by eapply IHHType1.
  all: try by eapply IHHType2; try apply leq_upd_label.
  all: try exact H.
  all: try exact H2.
  all: try exact H1.
  all: try exact H0.
  - eapply btyping_leq. exact H. exact Hleq'.
  - eapply List.Forall_impl; last exact H.
    intros h Hh. 
    eapply continuation_clause_typing_leq. exact Hh. exact Hleq'.
  - eapply List.Forall_impl; last exact H.
    intros h Hh. 
    eapply exception_clause_typing_leq. exact Hh. exact Hleq'.
(*    eapply List.Forall_impl; last exact H.
    intros h Hh.
    inversion Hh; subst.
    + destruct HC as [HC' | Habs];
        last by destruct C; inversion Habs; subst; destruct x.
      destruct C, C'; inversion HC'; subst.
      econstructor. exact H0. simpl.
      simpl in Hlab. rewrite Hlab. apply nth_error_prefix.
      done.
    + destruct HC as [HC' | Habs];
        last by destruct C; inversion Habs; subst; destruct x.
      destruct C, C'; inversion HC'; subst.
      econstructor 2. exact H0. simpl.
      simpl in Hlab. rewrite Hlab. apply nth_error_prefix.
      done.
    + destruct HC as [HC' | Habs];
        last by destruct C; inversion Habs; subst; destruct x.
      destruct C, C'; inversion HC'; subst.
      econstructor. exact H0. simpl.
      simpl in Hlab. rewrite Hlab. apply nth_error_prefix.
      done.
    + econstructor. 
      rewrite Hlab. apply nth_error_prefix.
      done.
    + econstructor. 
      rewrite Hlab. apply nth_error_prefix.
      done. *)
Qed.
  
(*
Definition leq_t_context C C' :=
  exists llab lloc, C' = upd_label (upd_local C (tc_local C ++ lloc)) (tc_label C ++ llab).

Lemma strip_leq C : leq_t_context (strip C) C.
Proof.
  exists (tc_label C), (tc_local C). destruct C => //=. 
Qed.


  
Lemma clause_typing_leq: forall C C' h ts,
    clause_typing C h ts ->
    leq_t_context C C' ->
    clause_typing C' h ts.
Proof.
  intros C C' h ts Htype HC.
  inversion Htype; subst.
  destruct HC as (llab & lloc & ->).
  econstructor; eauto.
  destruct C. simpl. simpl in H0.
  apply nth_error_prefix => //.
Qed.

(* Lemma all_impl {A} P Q (l: list A):
  all P l -> (forall x, P x -> Q x) -> all Q l. *)

Lemma btyping_leq: forall C C' bes tf,
    be_typing C bes tf ->
    leq_t_context C C' ->
    be_typing C' bes tf.
Proof.
  intros C C' bes tf HType Hleq.
  destruct Hleq as (llab & lloc & ->).
  gen_ind_subst HType; econstructor;
    try done;
    try (by eapply IHHType);
    try (by eapply IHHType1);
    try (by eapply IHHType2);
    try (by apply nth_error_prefix)
  .
  - eapply list.Forall_impl; eauto.
    intros h Hh. eapply clause_typing_leq.
    exact Hh. by eexists _,_.
  - eapply List.Forall_impl; eauto.
    intros h Hh. eapply clause_typing_leq.
    exact Hh. by eexists _,_.
  - rewrite List.length_app. lias.
  - apply/eqP. move/eqP in H0. apply nth_error_prefix => //.
  - rewrite List.length_app. lias.
  - apply/eqP. move/eqP in H0. apply nth_error_prefix => //.
  - eapply sub_all; last exact H.
    unfold subpred.
    intros x Hx. move/andP in Hx. destruct Hx as [??].
    apply/andP. split. rewrite List.length_app. lias.
    apply/eqP. move/eqP in H1. apply nth_error_prefix => //.
  - rewrite List.length_app. lias.
  - rewrite List.length_app. lias.
  - rewrite List.length_app. lias.
  - simpl. done.
Qed.




Lemma typing_leq: forall s C C' es tf,
    e_typing s C es tf ->
    leq_t_context C C' ->
    e_typing s C' es tf.
Proof.
  intros s C C' es tf HType Hleq.
  destruct Hleq as (llab & lloc & ->).
  gen_ind_subst HType; econstructor;
    try done;
    try (by eapply IHHType);
    try (by eapply IHHType1);
    try (by eapply IHHType2)
  .
  - eapply btyping_leq. exact H. by eexists _,_.
  - exact H.
  - exact H. 
  - done. 
  - eapply List.Forall_impl; last exact H.
    intros h Hh.
    inversion Hh; subst.
    econstructor. exact H0. simpl.
    apply nth_error_prefix.
    done.
  - exact H.
  - exact H0.
Qed.
  *)


Lemma Lfilled_break_typing: forall n m k lh vs LI ts s C t2s tss,
    e_typing s (upd_label C (tss ++ [::ts] ++ tc_label C)) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfilled n lh (vs ++ [::AI_basic (BI_br m)]) LI ->
    length tss = k ->
    n + k = m ->
    e_typing s C vs (Tf [::] ts).
Proof.
  move => n m k lh vs LI ts s C ts2 tss HType HConst HLength HLF HTSSLength HSum.
  apply const_es_exists in HConst. destruct HConst. subst.
  move/lfilledP in HLF.
  generalize dependent ts.
  generalize dependent ts2.
  generalize dependent LI.
  generalize dependent tss.
  generalize dependent n.
  induction lh.
  - move => n tss LI HLF ts2 ts HType HTSSLength.
    inversion HLF; subst.

    rewrite add0n in HLF.
    rewrite add0n in HType.
    apply const_es_exists in H4. destruct H4. subst.
    repeat rewrite -catA in HType.


    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    subst. clear H1.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H5 [H6 [H7 H8]]]]]]].
    subst.
    apply e_composition_typing in H8.
    destruct H8 as [ts0'' [t1s'' [t2s'' [t3s'' [H9 [H10 [H11 H12]]]]]]].
    subst.
    apply et_to_bet in H11; try auto_basic.
    apply Break_typing in H11.
    destruct H11 as [ts0 [ts1 [H13 [H14 H15]]]]. clear H13.
    unfold plop2 in H14. simpl in H14. move/eqP in H14.
    rewrite list_nth_prefix in H14.
    inversion H14. subst.
    clear H14.
    apply Const_list_typing in H7 as (ts' & Hts & H7 & Hconst).
    repeat rewrite length_is_size in HTSSLength.
    assert ((ts0'' ++ ts1 == t1s') && (ts0 == ts')).
    + apply concat_cancel_last_n => //=. by rewrite - catA.
      rewrite HTSSLength. rewrite v_to_e_size. rewrite - (size_map (typeof s)).
      rewrite Hts. rewrite size_map. done.
    + move/andP in H. destruct H.
      move/eqP in H0. subst.
      eapply t_const_ignores_context; last exact Hconst.
      destruct C => //. 
      apply v_to_e_is_const_list.
      
  - move => n0 tss LI HLF ts2 ts HType HTSSLength.
    inversion HLF. subst.
    repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    clear H2. clear H3.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H6 [H7' [H8' H9]]]]]]].
    destruct ts0' => //=.
    destruct t1s' => //=.
    clear H6. clear H7'.
    apply Label_typing in H9.
    destruct H9 as [ts0'' [t2s'' [H10 [H11 [H12 H13]]]]]. subst.
    simpl in H12.
    rewrite upd_label_overwrite in H12.
    rewrite -cat1s in H12. repeat rewrite catA in H12.
    remember ([::ts0''] ++ tss) as tss'. rewrite -catA in H12.
    replace (k.+1+length tss) with (k + length tss') in H8.
    eapply IHlh => //=.
    + by apply H8.
    + by apply H12.
    (* replace *)
    + assert (length tss' = length tss + 1).
      { rewrite Heqtss'. rewrite cat1s. simpl. by rewrite addn1. }
      by lias.
  - move => n0 tss LI HLF ts2 ts HType HTSSLength.
    inversion HLF. subst.
    repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    clear H2. clear H3.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H6' [H7' [H8' H9]]]]]]].
    destruct ts0' => //=.
    destruct t1s' => //=.
    clear H6'. clear H7'.
    apply Handler_typing in H9.
    destruct H9 as ( t2s'' & -> & Hclauses & H12). 
    (* simpl in H12.
    rewrite strip_upd_label in H12. *)
(*    rewrite -cat1s in H12. repeat rewrite catA in H12.
    remember ([::ts0''] ++ tss) as tss'. rewrite -catA in H12. 
    replace (k.+1+length tss) with (k + length tss') in H8. *)
    eapply IHlh => //=.
    + by apply H7.
    + rewrite - catA in H12. exact H12.
  - move => n0 tss LI HLF ts2 ts HType HTSSLength.
    inversion HLF. subst.
    repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    clear H2. clear H3.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H6' [H7' [H8' H9]]]]]]].
    destruct ts0' => //=.
    destruct t1s' => //=.
    clear H6'. clear H7'.
    apply Prompt_typing in H9.
    destruct H9 as ( -> & Hclauses & H12). 
    (* simpl in H12.
    rewrite strip_upd_label in H12. *)
(*    rewrite -cat1s in H12. repeat rewrite catA in H12.
    remember ([::ts0''] ++ tss) as tss'. rewrite -catA in H12. 
    replace (k.+1+length tss) with (k + length tss') in H8. *)
    eapply IHlh => //=.
    + by apply H8.
    + eapply typing_leq. exact H12.
      apply empty_context_leq.

Qed. 

Lemma Local_typing: forall s C n f es t1s t2s,
    e_typing s C [::AI_local n f es] (Tf t1s t2s) ->
    exists ts, t2s = t1s ++ ts /\
               s_typing s (Some ts) f es ts /\
               length ts = n.
Proof.
  move => s C n f es t1s t2s HType.
  remember ([::AI_local n f es]) as les.
  remember (Tf t1s t2s) as tf.
  generalize dependent Heqtf. generalize dependent t1s. generalize dependent t2s.
  induction HType; subst => //.
  - (* ety_a *)
    assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
    rewrite Heqles in H0. by basic_inversion'.
  - (* ety_composition *)
    apply extract_list1 in Heqles. destruct Heqles. subst.
    apply et_to_bet in HType1 => //.
    simpl in HType1. apply empty_btyping in HType1. subst.
    by eapply IHHType2 => //.
  - (* ety_weakening *)
    move => ts2 ts1 HTf.
    inversion HTf. subst.
    edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst. 
    exists x.
    repeat split => //=.
    by rewrite catA.
  - (* ety_local *)
    inversion Heqles. subst.
    move => t2s t1s HTf. inversion HTf. subst.
    by exists t2s.
Qed.

Lemma Return_typing: forall C t1s t2s,
    be_typing C [::BI_return] (Tf t1s t2s) ->
    exists ts ts', t1s = ts' ++ ts /\
                   tc_return C = Some ts.
Proof.
  move => C t1s t2s HType.
  dependent induction HType => //=.
  - by exists ts, t1s0.
  - invert_be_typing.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [ts' [H1 H2]]. subst.
    exists x, (ts ++ ts').
    split => //=.
    by rewrite -catA.
Qed.


Lemma Lfilled_return_typing: forall n lh vs LI ts s C lab t2s,
    e_typing s (upd_label C lab) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfilled n lh (vs ++ [::AI_basic BI_return]) LI ->
    Some ts = tc_return C ->
    e_typing s C vs (Tf [::] ts).
Proof.
  intros n lh; move: n.
  induction lh; move => n0 vs LI ts s C lab t2s HType HConst HLength HLF HReturn; move/lfilledP in HLF; inversion HLF; subst => //=.
  - repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H1 [H2 [H3 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s0 => //=.
    subst. clear H1.
    apply e_composition_typing in H3.
    destruct H3 as [ts1 [t1s1 [t2s1 [t3s1 [H9 [H6 [H7 H8]]]]]]].
    destruct ts1 => //=.
    destruct t1s1 => //=.
    subst. clear H5.
    apply e_composition_typing in H7.
    destruct H7 as [ts2 [t1s2 [t2s2 [t3s2 [H13 [H10 [H11 H12]]]]]]].
    destruct ts2 => //=.
    destruct t1s2 => //=.
    subst. clear H9. simpl in H8. simpl in H4.
    apply et_to_bet in H8; auto_basic. apply Return_typing in H8.
    destruct H8 as [ts1 [ts2 [H15 H14]]]. subst.
    apply const_es_exists in HConst. destruct HConst. subst.
    apply Const_list_typing in H12 as (ts' & Hts' & H12 & Hconst).
    rewrite -HReturn in H14. inversion H14. subst. clear H14.
    assert ((ts2 == t3s2) && (ts1 == ts')).
    + apply concat_cancel_last_n => //=.
      repeat rewrite length_is_size in HLength.
      rewrite v_to_e_size in HLength. rewrite HLength.
      rewrite - (size_map (typeof s)) Hts' size_map. done.
    + move/andP in H. destruct H.
      move/eqP in H0. subst.
      eapply t_const_ignores_context; last exact Hconst.
(*      done. *)
      apply v_to_e_is_const_list.
  - repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s0 => //=.
    subst. clear H2.
    apply e_composition_typing in H4.
    destruct H4 as [ts1 [t1s1 [t2s1 [t3s1 [H6 [H77 [H88 H9]]]]]]].
    destruct ts1 => //=.
    destruct t1s1 => //=.
    subst. clear H6.
    apply Label_typing in H9.
    destruct H9 as [ts' [ts2' [H10 [H11 [H12 H13]]]]].
    subst. simpl in H5.
    eapply IHlh => //.
    simpl in H12.
    apply H12.
    apply/lfilledP.
    by apply H8.
  - repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s0 => //=.
    subst. clear H2.
    apply e_composition_typing in H4.
    destruct H4 as [ts1 [t1s1 [t2s1 [t3s1 [H66 [H77 [H88 H9]]]]]]].
    destruct ts1 => //=.
    destruct t1s1 => //=.
    subst. 
    apply Handler_typing in H9.
    destruct H9 as ( ts2' &  -> & Hclauses & Htyping).
    subst. simpl in H5.
    eapply IHlh => //; last by apply/lfilledP; exact H7.
    instantiate (2 := lab).
    exact Htyping.
  - repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s0 => //=.
    subst. clear H2.
    apply e_composition_typing in H4.
    destruct H4 as [ts1 [t1s1 [t2s1 [t3s1 [H66 [H77 [H88 H9]]]]]]].
    destruct ts1 => //=.
    destruct t1s1 => //=.
    subst. 
    apply Prompt_typing in H9.
    destruct H9 as ((* ts2' & *) -> & Hclauses & Htyping).
    subst. simpl in H5.
    eapply IHlh => //; last by apply/lfilledP; exact H8.
    instantiate (2 := lab).
    eapply typing_leq. exact Htyping.
    apply empty_context_leq.
Qed. 




Lemma Local_return_typing: forall s C vs f LI tf n lh,
    e_typing s C [:: AI_local (length vs) f LI] tf ->
    const_list vs ->
    lfilled n lh (vs ++ [::AI_basic BI_return]) LI ->
(*    exists C', *) e_typing s C(*'*) vs tf. (* added exists C' *)
Proof.
  move => s C vs f LI tf n lh HType HConst HLF.
  destruct tf as [t1s t2s].
  apply Local_typing in HType.
  destruct HType as [ts [H1 [H2 H3]]]. subst.
  inversion H2. inversion H. subst. clear H4. clear H2. clear H.
  (* eexists. *) apply et_weakening_empty_1.
  assert (HET: e_typing s (upd_local_return C2 (tc_local C2 ++ tvs) (Some ts)) vs (Tf [::] ts)).
  { eapply Lfilled_return_typing; eauto. }
(*  apply et_to_bet in HET; last by apply const_list_is_basic. *)
  apply const_es_exists in HConst. destruct HConst. subst.
  apply Const_list_typing in HET as (ts' & Hts & HET & Hconst); subst => /=.
(*  exact Hconst. *)
  eapply t_const_ignores_context; last exact Hconst.
  by apply v_to_e_is_const_list. 
Qed.

Lemma to_b_to_e_list l:
  to_b_list (to_e_list l) = l.
Proof.
  induction l => //=.
  by rewrite IHl.
Qed.

Lemma typing_empty_context s C es tf:
  e_typing s empty_context es tf ->
  e_typing s C es tf.
Proof.
  intros H. eapply typing_leq. exact H. repeat split; first by right.
  exists (tc_local C) => //. exists (tc_label C) => //.
  by left.
Qed.

    
    


Theorem t_simple_preservation: forall s i es es' C loc lab ret tf,
    inst_typing s i C ->
    e_typing s (upd_label (upd_local_return C loc ret) lab) es tf ->
    reduce_simple es es' ->
    e_typing s (upd_label (upd_local_return C loc ret) lab) es' tf.
Proof.
  move => s i es es' C loc lab ret tf HInstType HType HReduce.
  inversion HReduce; subst; try by apply ety_trap.
(*  
  inversion HReduce; subst; try (by (apply et_to_bet in HType => //; auto_basic; apply ety_a' => //; auto_basic; eapply t_be_simple_preservation; try by eauto; auto_basic)); try by apply ety_trap. *)
  - (* Unop *)
    apply ety_a'; first by econstructor. eapply t_Unop_preserve; last exact HReduce.
    apply et_to_bet in HType => //. repeat (constructor => //).
  - (* Binop *)
    apply ety_a'; first by econstructor. eapply t_Binop_preserve_success; last exact HReduce.
    apply et_to_bet in HType => //. auto_basic.
  - (* Testop *)
    apply ety_a'; first auto_basic. eapply t_Testop_i32_preserve.
    apply et_to_bet in HType; try auto_basic => //.
  - (* Testop *)
    apply ety_a'; first auto_basic. eapply t_Testop_i64_preserve.
    apply et_to_bet in HType; try auto_basic => //.
  - (* Relop *)
    apply ety_a'; first auto_basic. eapply t_Relop_preserve; last exact HReduce.
    apply et_to_bet in HType => //. auto_basic.
  - (* Cvtop *)
    apply ety_a'; first auto_basic. eapply t_Convert_preserve; last exact HReduce.
    apply et_to_bet in HType => //. auto_basic.
  - (* Reinterpret *)
    apply ety_a'; first auto_basic. eapply t_Reinterpret_preserve; last exact HReduce.
    apply et_to_bet in HType; try auto_basic => //.
  - (* Ref_is_null *)
    simpl in HReduce.
    fold (AI_const (VAL_ref (VAL_ref_null t))) in HReduce.
    eapply t_Ref_is_null_preserve; last exact HReduce.
    done.
  - (* Ref_is_null *)
    eapply t_Ref_is_null_preserve; last exact HReduce.
    exact HType.
  - (* Prompt const *)
    et_dependent_ind HType => //.
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
      rewrite Hremes in H1. by basic_inversion'.
    + (* ety_composition *)
      apply extract_list1 in Hremes. destruct Hremes. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_btyping in HType1. subst.
      by eapply IHHType2 => //.
    + (* ety_weakening *)
      apply ety_weakening. by eapply IHHType => //.
    + (* ety_handler *)
      inversion Hremes; subst.
      eapply t_const_ignores_context; try exact HType. done. (* done. *)
  - (* Handler const *)
    et_dependent_ind HType => //.
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
      rewrite Hremes in H1. by basic_inversion'.
    + (* ety_composition *)
      apply extract_list1 in Hremes. destruct Hremes. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_btyping in HType1. subst.
      by eapply IHHType2 => //.
    + (* ety_weakening *)
      apply ety_weakening. by eapply IHHType => //.
    + (* ety_handler *)
      inversion Hremes; subst.
      eapply t_const_ignores_context; try exact HType. done. (* done. *) 
  - (* Nop *)
    apply et_to_bet in HType; try auto_basic. destruct tf. apply Nop_typing in HType; subst.
    apply et_weakening_empty_both. 
    apply ety_a'; first constructor. constructor.
  - (* Drop *)
    eapply t_Drop_preserve. exact HType.
  - (* Select *)
    eapply t_Select_preserve; last exact HReduce.
    exact HType.
  - (* Select *)
    eapply t_Select_preserve; last exact HReduce.
    exact HType.
  - (* Block *)
    destruct tf.
    apply e_composition_typing in HType.
    destruct HType as [ts [t1s' [t2s' [t3s [H2 [H3 [H4 H5]]]]]]]. subst.
    apply const_es_exists in H. destruct H. subst.
    apply Const_list_typing in H4 as (ts' & Hts' & H4 & Hconst). subst.
    apply et_to_bet in H5; try auto_basic. apply Block_typing in H5.
    destruct H5 as [t3s [H6 [H7 H8]]].
    subst.
    repeat rewrite length_is_size in H1. rewrite v_to_e_size in H1.
    assert ((t1s' == t3s) && (ts' == t1s)) => //=.
    + apply concat_cancel_last_n => //=. rewrite H1. rewrite - (size_map (typeof s)).
      rewrite Hts'. rewrite size_map => //. 
    + move/andP in H. destruct H.
      move/eqP in H. move/eqP in H0. subst. clear H6. clear H1.
      rewrite catA. apply et_weakening_empty_1.
      eapply ety_label => //.
      -- apply ety_a' => //=.
         apply bet_weakening_empty_both.
         by apply bet_empty.
      -- eapply et_composition'.
         ++ eapply t_const_ignores_context; last exact Hconst.
(*            done. *)
            apply v_to_e_is_const_list.
         ++ remember (to_e_list es0) as es1.
            symmetry in Heqes1. apply b_e_elim in Heqes1 as [Hes0 Hes1].
            apply ety_a' => //. rewrite - Hes0. exact H8. 
  - (* Loop *)
    destruct tf.
    apply e_composition_typing in HType.
    destruct HType as [ts [t1s' [t2s' [t3s [H2 [H3 [H4 H5]]]]]]]. subst.
    apply const_es_exists in H. destruct H. subst.
    apply Const_list_typing in H4 as (ts' & Hts' & H4 & Hconst). subst.
    apply et_to_bet in H5; last auto_basic. apply Loop_typing in H5.
    destruct H5 as [t3s [H6 [H7 H8]]]. subst.
    repeat rewrite length_is_size in H1. rewrite v_to_e_size in H1.
    assert ((t1s' == t3s) && (ts' == t1s)) => //=.
    + apply concat_cancel_last_n => //=. rewrite H1 - (size_map (typeof s)) Hts' size_map => //.
    + move/andP in H. destruct H.
      move/eqP in H. move/eqP in H0. subst. clear H6. clear H1.
      rewrite catA. apply et_weakening_empty_1.
      eapply ety_label => //.
      -- apply ety_a' => //=.
         ++ auto_basic. 
         ++ by apply bet_loop.
      -- eapply et_composition'.
         ++ eapply t_const_ignores_context; last exact Hconst.
            (* done. *)
            apply v_to_e_is_const_list.
         ++ remember (to_e_list es0) as es1.
            symmetry in Heqes1. apply b_e_elim in Heqes1 as [-> Hes1].
            apply ety_a' => //. 
      -- repeat rewrite length_is_size.
         unfold vs_to_vts. rewrite size_map.
         rewrite - (size_map (typeof s)) Hts' size_map => //. 
  - (* If *)
    apply ety_a'; try auto_basic. eapply t_If_be_preserve; last exact HReduce.
    apply et_to_bet in HType; try auto_basic => //.
  - (* If *)
    apply ety_a'; try auto_basic. eapply t_If_be_preserve; last exact HReduce.
    apply et_to_bet in HType; try auto_basic => //.
  - (* Label_const *)
    et_dependent_ind HType => //.
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
      rewrite Hremes in H1. by basic_inversion'.
    + (* ety_composition *)
      apply extract_list1 in Hremes. destruct Hremes. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_btyping in HType1. subst.
      by eapply IHHType2 => //.
    + (* ety_weakening *)
      apply ety_weakening.
      by eapply IHHType => //.
    + (* ety_label *)
      inversion Hremes; subst.
      eapply t_const_ignores_context; try exact HType2. done.
      (* done. *)
  - (* Label_lfilled_Break *)
    et_dependent_ind HType => //.
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
      rewrite Hremes in H2. by basic_inversion'.
    + (* ety_composition *)
      apply extract_list1 in Hremes. destruct Hremes. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_btyping in HType1. subst.
      by eapply IHHType2 => //=.
    + (* ety_weakening *)
      apply ety_weakening.
      by eapply IHHType => //.
    + (* ety_label *)
      inversion Hremes; subst.
      eapply et_composition' => //=.
      -- eapply Lfilled_break_typing => //=.
         ++ instantiate (4 := [::]). rewrite cat0s.
            by apply HType2.
         ++ by [].
         ++ simpl. rewrite addn0. by apply H1.
      -- by apply HType1.
  - (* Br_if *)
    apply ety_a'; first econstructor. eapply t_Br_if_false_preserve; last exact HReduce.
    apply et_to_bet in HType; try auto_basic => //.
  - (* Br_if *)
    apply ety_a'; first auto_basic. eapply t_Br_if_true_preserve; last exact HReduce.
    apply et_to_bet in HType; try auto_basic => //.
  - (* Br_table *)
    apply ety_a'; first auto_basic. eapply t_Br_table_preserve; last exact HReduce.
    apply et_to_bet in HType; try auto_basic => //.
  - (* Br_table *)
    apply ety_a'; first auto_basic. eapply t_Br_table_preserve; last exact HReduce.
    apply et_to_bet in HType; try auto_basic => //.    
  - (* Local_const *)
    et_dependent_ind HType => //.
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
      rewrite Hremes in H1. by basic_inversion'.
    + (* ety_composition *)
      apply extract_list1 in Hremes. destruct Hremes. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_btyping in HType1. subst.
      by eapply IHHType2 => //.
    + (* ety_weakening *)
      apply ety_weakening.
      by eapply IHHType => //.
    + (* ety_local *)
      inversion Hremes; (* inversion H; *) inversion H0;  subst.
      eapply t_const_ignores_context; try exact H6.
      done.
  - (* Local_lfilled_Return *)
    by eapply Local_return_typing; eauto. 
 
  - (* Tee_local *)
    destruct v => //.
    destruct b => //.
    all:fold_const; apply t_Tee_local_preserve.
    all:exact HType.
Qed.

    


Lemma t_simple_preservation_strip_empty_context: forall s es es' tf C,
    upd_label C [::] = empty_context ->
    e_typing s C es tf ->
    reduce_simple es es' ->
    e_typing s C es' tf.
Proof.
  move => s es es' tf C HC HType HReduce.
  destruct C; inversion HC; subst.
  inversion HReduce; subst; try by apply ety_trap.
(*  
  inversion HReduce; subst; try (by (apply et_to_bet in HType => //; auto_basic; apply ety_a' => //; auto_basic; eapply t_be_simple_preservation; try by eauto; auto_basic)); try by apply ety_trap. *)
  - (* Unop *)
    apply ety_a'; first by econstructor. eapply t_Unop_preserve; last exact HReduce.
    apply et_to_bet in HType => //. repeat (constructor => //).
  - (* Binop *)
    apply ety_a'; first by econstructor. eapply t_Binop_preserve_success; last exact HReduce.
    apply et_to_bet in HType => //. auto_basic.
  - (* Testop *)
    apply ety_a'; first auto_basic. eapply t_Testop_i32_preserve.
    apply et_to_bet in HType; try auto_basic => //.
  - (* Testop *)
    apply ety_a'; first auto_basic. eapply t_Testop_i64_preserve.
    apply et_to_bet in HType; try auto_basic => //.
  - (* Relop *)
    apply ety_a'; first auto_basic. eapply t_Relop_preserve; last exact HReduce.
    apply et_to_bet in HType => //. auto_basic.
  - (* Cvtop *)
    apply ety_a'; first auto_basic. eapply t_Convert_preserve; last exact HReduce.
    apply et_to_bet in HType => //. auto_basic.
  - (* Reinterpret *)
    apply ety_a'; first auto_basic. eapply t_Reinterpret_preserve; last exact HReduce.
    apply et_to_bet in HType; try auto_basic => //.
  - (* Ref_is_null *)
    simpl in HReduce.
    fold (AI_const (VAL_ref (VAL_ref_null t))) in HReduce.
    eapply t_Ref_is_null_preserve; last exact HReduce.
    done.
  - (* Ref_is_null *)
    eapply t_Ref_is_null_preserve; last exact HReduce.
    exact HType.
  - (* Prompt const *)
    et_dependent_ind HType => //.
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
      rewrite Hremes in H1. by basic_inversion'.
    + (* ety_composition *)
      apply extract_list1 in Hremes. destruct Hremes. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_btyping in HType1. subst.
      by eapply IHHType2 => //.
    + (* ety_weakening *)
      apply ety_weakening. by eapply IHHType => //.
    + (* ety_handler *)
      inversion Hremes; subst.
      eapply t_const_ignores_context; try exact HType. done. (* done. *)
  - (* Handler const *)
    et_dependent_ind HType => //.
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
      rewrite Hremes in H1. by basic_inversion'.
    + (* ety_composition *)
      apply extract_list1 in Hremes. destruct Hremes. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_btyping in HType1. subst.
      by eapply IHHType2 => //.
    + (* ety_weakening *)
      apply ety_weakening. by eapply IHHType => //.
    + (* ety_handler *)
      inversion Hremes; subst.
      eapply t_const_ignores_context; try exact HType. done. (* done. *) 
  - (* Nop *)
    apply et_to_bet in HType; try auto_basic. destruct tf. apply Nop_typing in HType; subst.
    apply et_weakening_empty_both. 
    apply ety_a'; first constructor. constructor.
  - (* Drop *)
    eapply t_Drop_preserve. exact HType.
  - (* Select *)
    eapply t_Select_preserve; last exact HReduce.
    exact HType.
  - (* Select *)
    eapply t_Select_preserve; last exact HReduce.
    exact HType.
  - (* Block *)
    destruct tf.
    apply e_composition_typing in HType.
    destruct HType as [ts [t1s' [t2s' [t3s [H2 [H3 [H4 H5]]]]]]]. subst.
    apply const_es_exists in H. destruct H. subst.
    apply Const_list_typing in H4 as (ts' & Hts' & H4 & Hconst). subst.
    apply et_to_bet in H5; try auto_basic. apply Block_typing in H5.
    destruct H5 as [t3s [H6 [H7 H8]]].
    subst.
    repeat rewrite length_is_size in H1. rewrite v_to_e_size in H1.
    assert ((t1s' == t3s) && (ts' == t1s)) => //=.
    + apply concat_cancel_last_n => //=. rewrite H1. rewrite - (size_map (typeof s)).
      rewrite Hts'. rewrite size_map => //. 
    + move/andP in H. destruct H.
      move/eqP in H. move/eqP in H0. subst. clear H6. clear H1.
      rewrite catA. apply et_weakening_empty_1.
      eapply ety_label => //.
      -- apply ety_a' => //=.
         apply bet_weakening_empty_both.
         by apply bet_empty.
      -- eapply et_composition'.
         ++ eapply t_const_ignores_context; last exact Hconst.
(*            done. *)
            apply v_to_e_is_const_list.
         ++ remember (to_e_list es0) as es1.
            symmetry in Heqes1. apply b_e_elim in Heqes1 as [Hes0 Hes1].
            apply ety_a' => //. rewrite - Hes0. exact H8. 
  - (* Loop *)
    destruct tf.
    apply e_composition_typing in HType.
    destruct HType as [ts [t1s' [t2s' [t3s [H2 [H3 [H4 H5]]]]]]]. subst.
    apply const_es_exists in H. destruct H. subst.
    apply Const_list_typing in H4 as (ts' & Hts' & H4 & Hconst). subst.
    apply et_to_bet in H5; last auto_basic. apply Loop_typing in H5.
    destruct H5 as [t3s [H6 [H7 H8]]]. subst.
    repeat rewrite length_is_size in H1. rewrite v_to_e_size in H1.
    assert ((t1s' == t3s) && (ts' == t1s)) => //=.
    + apply concat_cancel_last_n => //=. rewrite H1 - (size_map (typeof s)) Hts' size_map => //.
    + move/andP in H. destruct H.
      move/eqP in H. move/eqP in H0. subst. clear H6. clear H1.
      rewrite catA. apply et_weakening_empty_1.
      eapply ety_label => //.
      -- apply ety_a' => //=.
         ++ auto_basic. 
         ++ by apply bet_loop.
      -- eapply et_composition'.
         ++ eapply t_const_ignores_context; last exact Hconst.
            (* done. *)
            apply v_to_e_is_const_list.
         ++ remember (to_e_list es0) as es1.
            symmetry in Heqes1. apply b_e_elim in Heqes1 as [-> Hes1].
            apply ety_a' => //. 
      -- repeat rewrite length_is_size.
         unfold vs_to_vts. rewrite size_map.
         rewrite - (size_map (typeof s)) Hts' size_map => //. 
  - (* If *)
    apply ety_a'; try auto_basic. eapply t_If_be_preserve; last exact HReduce.
    apply et_to_bet in HType; try auto_basic => //.
  - (* If *)
    apply ety_a'; try auto_basic. eapply t_If_be_preserve; last exact HReduce.
    apply et_to_bet in HType; try auto_basic => //.
  - (* Label_const *)
    et_dependent_ind HType => //.
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
      rewrite Hremes in H1. by basic_inversion'.
    + (* ety_composition *)
      apply extract_list1 in Hremes. destruct Hremes. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_btyping in HType1. subst.
      by eapply IHHType2 => //.
    + (* ety_weakening *)
      apply ety_weakening.
      by eapply IHHType => //.
    + (* ety_label *)
      inversion Hremes; subst.
      eapply t_const_ignores_context; try exact HType2. done.
      (* done. *)
  - (* Label_lfilled_Break *)
    et_dependent_ind HType => //.
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
      rewrite Hremes in H2. by basic_inversion'.
    + (* ety_composition *)
      apply extract_list1 in Hremes. destruct Hremes. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_btyping in HType1. subst.
      by eapply IHHType2 => //=.
    + (* ety_weakening *)
      apply ety_weakening.
      by eapply IHHType => //.
    + (* ety_label *)
      inversion Hremes; subst.
      eapply et_composition' => //=.
      -- eapply Lfilled_break_typing => //=.
         ++ instantiate (4 := [::]). rewrite cat0s.
            by apply HType2.
         ++ by [].
         ++ simpl. rewrite addn0. by apply H1.
      -- by apply HType1.
  - (* Br_if *)
    apply ety_a'; first econstructor. eapply t_Br_if_false_preserve; last exact HReduce.
    apply et_to_bet in HType; try auto_basic => //.
  - (* Br_if *)
    apply ety_a'; first auto_basic. eapply t_Br_if_true_preserve; last exact HReduce.
    apply et_to_bet in HType; try auto_basic => //.
  - (* Br_table *)
    apply ety_a'; first auto_basic. eapply t_Br_table_preserve; last exact HReduce.
    apply et_to_bet in HType; try auto_basic => //.
  - (* Br_table *)
    apply ety_a'; first auto_basic. eapply t_Br_table_preserve; last exact HReduce.
    apply et_to_bet in HType; try auto_basic => //.    
  - (* Local_const *)
    et_dependent_ind HType => //.
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
      rewrite Hremes in H1. by basic_inversion'.
    + (* ety_composition *)
      apply extract_list1 in Hremes. destruct Hremes. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_btyping in HType1. subst.
      by eapply IHHType2 => //.
    + (* ety_weakening *)
      apply ety_weakening.
      by eapply IHHType => //.
    + (* ety_local *)
      inversion Hremes; (* inversion H; *) inversion H0;  subst.
      eapply t_const_ignores_context; try exact H6.
      done.
  - (* Local_lfilled_Return *)
    by eapply Local_return_typing; eauto. 
 
  - (* Tee_local *)
    destruct v => //.
    destruct b => //.
    all:fold_const; apply t_Tee_local_preserve.
    all:exact HType.
Qed.


Lemma Call_typing: forall j C t1s t2s,
    be_typing C [::BI_call j] (Tf t1s t2s) ->
    exists ts t1s' t2s', j < length (tc_func_t C) /\
    List.nth_error (tc_func_t C) j = Some (Tf t1s' t2s') /\
                         t1s = ts ++ t1s' /\
                         t2s = ts ++ t2s'.
Proof.
  move => j C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::], t1s, t2s.
  - invert_be_typing.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [t1s' [t2s' [H1 [H2 [H3 H4]]]]].
    subst.
    exists (ts ++ x), t1s', t2s'.
    repeat rewrite -catA.
    by repeat (split => //=).
Qed.

Lemma Call_indirect_typing: forall i C t1s t2s,
    be_typing C [::BI_call_indirect i] (Tf t1s t2s) ->
    exists tn tm ts, tc_table C <> nil /\
    get_type C i = Some (Tf tn tm) /\
    t1s = ts ++ tn ++ [::T_num T_i32] /\ t2s = ts ++ tm.
Proof.
  move => i C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t1s0, t2s, [::].
  - invert_be_typing.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [tm [ts' [H1 [H2 [H3 H5]]]]]. subst.
    exists x, tm, (ts ++ ts').
    by repeat rewrite -catA.
Qed.

(*
Lemma global_agree_same_type g1 g2 s t:
  typeof s (g_val g1) = Some t ->
  global_agree s g1 g2 ->
  typeof s (g_val g2) = Some t. 
*)

(*
Lemma globs_agree_function: forall s,
    function (globals_agree s (s_globals s)).
Proof.
  move => s. unfold function. move => x y1 y2 [H1 H2].
  unfold globals_agree in H1. unfold globals_agree in H2.
  remove_bools_options.
  unfold global_agree in H3. unfold global_agree in H4.
  remove_bools_options.
  - destruct y1; destruct y2 => //.
    simpl in H0. simpl in H2. simpl in H3. simpl in H4. by subst.
  - destruct y1; destruct y2 => //.
    simpl in H0, H2, H3, H4. subst.
Qed.
*)

Lemma functions_agree_function: forall s,
    function (functions_agree (s_funcs s)).
Proof.
  move => s. unfold function. move => x y1 y2 [H1 H2].
  unfold functions_agree in H1. unfold typing.functions_agree in H1.
  unfold functions_agree in H2. unfold typing.functions_agree in H2.
  by remove_bools_options.
Qed.

Lemma tc_func_reference1: forall j k i s f C tf,
  List.nth_error (inst_funcs i) j = Some k ->
  List.nth_error (s_funcs s) k = Some f ->
  inst_typing s i C ->
  List.nth_error (tc_func_t C) j = Some tf ->
  tf = cl_type f.
Proof.
  move => j k i s f C tf HN1 HN2 HInstType HN3.
  unfold inst_typing in HInstType.
  destruct i => //=.
  destruct C => //=.
  destruct tc_local => //=.
  destruct tc_label => //=.
  destruct tc_return => //=.
  move/andP in HInstType. destruct HInstType.
  repeat (move/andP in H; destruct H).
  simpl in HN1. simpl in HN3.
  eapply all2_projection in H4; eauto.
  unfold functions_agree in H4. move/andP in H4. destruct H4.
  unfold option_map in H5.
  rewrite HN2 in H5. move/eqP in H5.
  by inversion H5.
Qed.

(*Lemma tc_func_reference2: forall s C i j cl tf,
  List.nth_error (inst_types i) j = Some (cl_type cl) ->
  inst_typing s i C ->
  List.nth_error (tc_types_t C) j = Some tf ->
  tf = cl_type cl.
Proof.
  move => s C i j cl tf HN1 HIT HN2.
  apply inst_typing_types in HIT.
  rewrite HIT in HN2. rewrite HN1 in HN2.
  by inversion HN2.
Qed. *)

Lemma Invoke_func_native_typing: forall s i C a cl tn tm ts es t1s t2s,
    e_typing s C [::AI_invoke a] (Tf t1s t2s) ->
    store_typing s ->
    List.nth_error s.(s_funcs) a = Some cl ->
    cl = FC_func_native i (Tf tn tm) ts es ->
    exists ts' C', t1s = ts' ++ tn /\ t2s = ts' ++ tm /\
                inst_typing s i C' /\
               be_typing (upd_local_label_return C' (tc_local C' ++ tn ++ ts) ([::tm] ++ tc_label C') (Some tm)) es (Tf [::] tm).
Proof.
  move => s i C a cl tn tm ts es t1s t2s HType HST HNth Hcl.
  et_dependent_ind HType => //.
  - by destruct bes => //=.
  - apply extract_list1 in Hremes. destruct Hremes. subst.
    apply et_to_bet in HType1 => //=.
    apply empty_btyping in HType1. subst.
    by eapply IHHType2 => //=.
  - inversion Hremtf; subst.
    edestruct IHHType => //=.
    destruct H as [C' [H1 [H2 [H3 H4]]]]. subst.
    exists (ts0 ++ x), C'.
    by repeat split => //; rewrite catA.
  - inversion Hremes; subst.
    destruct s0. destruct HST as (Hfs & _).
    simpl in H. simpl in HNth. 
    rewrite H in HNth.
    inversion HNth; subst; clear HNth.
    inversion Hremtf; subst; clear Hremtf.
    apply List.nth_error_In in H.
    rewrite List.Forall_forall in Hfs.
    apply Hfs in H. destruct H as [tf Hf].
    inversion Hf; subst. inversion H6; subst.
    by exists [::], C. 
Qed.

Lemma Invoke_func_host_typing: forall s C a cl h tn tm t1s t2s,
    e_typing s C [::AI_invoke a] (Tf t1s t2s) ->
    List.nth_error s.(s_funcs) a = Some cl ->
    cl = FC_func_host (Tf tn tm) h ->
    exists ts, t1s = ts ++ tn /\ t2s = ts ++ tm.
Proof.
  move => s C a cl h tn tm t1s t2s HType HNth Hcl.
  et_dependent_ind HType => //.
  - by destruct bes => //=.
  - apply extract_list1 in Hremes. destruct Hremes. subst.
    apply et_to_bet in HType1 => //=.
    apply empty_btyping in HType1. subst.
    by eapply IHHType2 => //=.
  - inversion Hremtf; subst.
    edestruct IHHType => //=.
    exists (ts ++ x). destruct H. subst.
    by split; repeat rewrite catA.
  - inversion Hremes; subst.
    rewrite H in HNth.
    inversion HNth; subst; clear HNth.
    inversion Hremtf; subst.
    by exists [::].
Qed.

Lemma Get_local_typing: forall C i t1s t2s,
    be_typing C [::BI_get_local i] (Tf t1s t2s) ->
    exists t, List.nth_error (tc_local C) i = Some t /\
    t2s = t1s ++ [::t] /\
    i < length (tc_local C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Set_local_typing: forall C i t1s t2s,
    be_typing C [::BI_set_local i] (Tf t1s t2s) ->
    exists t, List.nth_error (tc_local C) i = Some t /\
    t1s = t2s ++ [::t] /\
    i < length (tc_local C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Get_global_typing: forall C i t1s t2s,
    be_typing C [::BI_get_global i] (Tf t1s t2s) ->
    exists t, option_map tg_t (List.nth_error (tc_global C) i) = Some t /\
    t2s = t1s ++ [::t] /\
    i < length (tc_global C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Set_global_typing: forall C i t1s t2s,
    be_typing C [::BI_set_global i] (Tf t1s t2s) ->
    exists g t, List.nth_error (tc_global C) i = Some g /\
    tg_t g = t /\
    is_mut g /\
    t1s = t2s ++ [::t] /\
    i < length (tc_global C).
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists g, (tg_t g).
  - invert_be_typing.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [t [H1 [H2 [H3 [H4 H5]]]]]. subst.
    exists x, (tg_t x).
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Load_typing: forall C t a off tp_sx t1s t2s,
    be_typing C [::BI_load t tp_sx a off] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::T_num T_i32] /\ t2s = ts ++ [::T_num t] /\
                    tc_memory C <> nil /\
                    load_store_t_bounds a (option_projl tp_sx) t.
Proof.
  move => C t a off tp_sx t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::].
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 [H3 H4]]]. subst.
    exists (ts ++ x).
    by repeat rewrite -catA.
Qed.

Lemma Store_typing: forall C t a off tp t1s t2s,
    be_typing C [::BI_store t tp a off] (Tf t1s t2s) ->
    t1s = t2s ++ [::T_num T_i32; T_num t] /\
    tc_memory C <> nil /\
    load_store_t_bounds a tp t.
Proof.
  move => C t a off tp t1s t2s HType.
  dependent induction HType; subst => //=.
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=. subst.
    by repeat rewrite -catA.
Qed.

Lemma Current_memory_typing: forall C t1s t2s,
    be_typing C [::BI_current_memory] (Tf t1s t2s) ->
    tc_memory C <> nil /\ t2s = t1s ++ [::T_num T_i32].
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=. subst.
    by repeat rewrite -catA.
Qed.

Lemma Grow_memory_typing: forall C t1s t2s,
    be_typing C [::BI_grow_memory] (Tf t1s t2s) ->
    exists ts, tc_memory C <> nil /\ t2s = t1s /\ t1s = ts ++ [::T_num T_i32].
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::].
  - invert_be_typing.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists (ts ++ x).
    by repeat rewrite -catA.
Qed.

Lemma store_typed_cl_typed: forall s n f,
    List.nth_error (s_funcs s) n = Some f ->
    store_typing s ->
    cl_typing s f (cl_type f).
Proof.
  move => s n f HN HST.
  unfold store_typing in HST.
  destruct s => //=.
  remove_bools_options.
  simpl in HN.
  destruct HST.
  rewrite -> List.Forall_forall in H.
  apply List.nth_error_In in HN.
  apply H in HN. unfold cl_type_check_single in HN. destruct HN.
  by inversion H1; subst.
Qed.

Lemma inst_t_context_local_empty: forall s i C,
    inst_typing s i C ->
    tc_local C = [::].
Proof.
  move => s i C HInstType.
  unfold inst_typing in HInstType.
  destruct i => //=.
  destruct C => //=.
  by destruct tc_local.
Qed.

Lemma inst_t_context_label_empty: forall s i C,
    inst_typing s i C ->
    tc_label C = [::].
Proof.
  move => s i C HInstType.
  unfold inst_typing in HInstType.
  destruct i => //=.
  destruct C => //=.
  by destruct tc_local; destruct tc_label.
Qed.

Lemma global_type_reference: forall s i j C v t,
    inst_typing s i C ->
    sglob_val s i j = Some v ->
    option_map tg_t (List.nth_error (tc_global C) j) = Some t ->
    typeof s v = Some t (* \/ typeof s v = T_ref T_corruptref *).
Proof.
  move => s i j C v t HInstType Hvref Htref.
  unfold sglob_val in Hvref.
  unfold sglob in Hvref.
  unfold sglob_ind in Hvref.
  destruct (List.nth_error i.(inst_globs) j) eqn:Hi => //=.
  remove_bools_options.
  unfold option_bind in Hoption0.
  remove_bools_options.
  unfold inst_typing in HInstType.
  destruct i => //=. destruct C => //=.
  destruct tc_local => //=. destruct tc_label => //=. destruct tc_return => //=.
  move/andP in HInstType. destruct HInstType.
  remove_bools_options.
  eapply all2_projection in H3; eauto.
  unfold globals_agree in H3. move/andP in H3. destruct H3.
  remove_bools_options.
  simpl in Hi. simpl in Hoption.
  unfold global_agree in H7.
  remove_bools_options => //.
Qed.

Lemma upd_label_unchanged: forall C lab,
    tc_label C = lab ->
    upd_label C lab = C.
Proof.
  move => C lab HLab.
  rewrite -HLab. unfold upd_label. by destruct C.
Qed.

Lemma upd_label_unchanged_typing: forall s C es tf,
    e_typing s C es tf ->
    e_typing s (upd_label C (tc_label C)) es tf.
Proof.
  move => s C es tf HType.
  by rewrite upd_label_unchanged.
Qed.

Lemma upd_label_upd_local_return_combine: forall C loc lab ret,
    upd_label (upd_local_return C loc ret) lab =
    upd_local_label_return C loc lab ret.
Proof.
  by [].
Qed.

Lemma set_nth_same_unchanged: forall {X:Type} (l:seq X) e i vd,
    List.nth_error l i = Some e ->
    set_nth vd l i e = l.
Proof.
  move => X l e i.
  generalize dependent l. generalize dependent e.
  induction i; move => e l vd HNth => //=.
  - destruct l => //=.
    simpl in HNth. by inversion HNth.
  - destruct l => //=.
    f_equal. apply IHi.
    by simpl in HNth.
Qed.

Lemma set_nth_map: forall {X Y:Type} (l:seq X) e i vd {f: X -> Y},
    i < size l ->
    map f (set_nth vd l i e) = set_nth (f vd) (map f l) i (f e).
Proof.
  move => X Y l e i.
  generalize dependent l. generalize dependent e.
  induction i; move => e l vd f HSize => //=.
  - by destruct l => //=.
  - destruct l => //=.
    f_equal.
    apply IHi.
    by simpl in HSize.
Qed.

Lemma n_zeros_typing: forall ts,
    map typeof_num (n_zeros ts) = ts.
Proof.
  induction ts => //=.
  by destruct a => //=; f_equal.
Qed.


Lemma global_agree_extension: forall g0 g1 g s,
    global_agree s g0 g ->
    glob_extension s g0 g1 ->
    global_agree s g1 g.
Proof.
  move => g0 g1 g s H1 H2.
  unfold global_agree.
  unfold global_agree in H1. unfold glob_extension in H2.
  destruct g => //=.
  destruct g0 => //=.
  destruct g1 => //=.
  simpl in H2. simpl in H1.
  remove_bools_options.
  subst.
  destruct g_mut; remove_bools_options; subst.
  + apply/andP. split => //. by rewrite H0.
  + destruct g_mut0 => //. apply/andP. split => //.
    remove_bools_options. rewrite H0 H. done.
(*    by rewrite H0. *)
(*  - destruct g_mut; remove_bools_options; subst.
    + apply/andP; split; first done. apply/orP; right. by rewrite H0.
    + destruct g_mut0 => //. apply/andP. split; first done. apply/orP. right.
      move/eqP in H2. by rewrite -H2 H0. *)
Qed.


Lemma glob_extension_C: forall sg sg' ig tcg s,
    all2 (globals_agree s sg) ig tcg ->
    all2 (glob_extension s) sg sg' ->
    all2 (globals_agree s sg') ig tcg.
Proof.
  move => sg sg' ig.
  generalize dependent sg; generalize dependent sg'.
  induction ig; move => sg' sg tcg s HA Hext => //=; destruct tcg => //=.
  - simpl in HA. remove_bools_options.
    edestruct IHig; eauto.
    unfold globals_agree in H. remove_bools_options.
    assert (size sg = size sg'); first by eapply all2_size; eauto.
    assert (a < length sg')%coq_nat.
    {
        rewrite length_is_size in H. rewrite length_is_size.
        rewrite -H1. by lias.
    }
    remember H2 as H5. clear HeqH5.
    rewrite <- List.nth_error_Some in H2.
    destruct (List.nth_error sg' a) eqn:HGlob => //=; eauto. clear H2.
    remember Hext as Hext1. clear HeqHext1.
    eapply all2_projection in Hext1; eauto.
    apply/andP. split => //=.
    + unfold globals_agree. apply/andP; split => //=; first by lias.
      unfold option_map. rewrite HGlob.
      apply/eqP. f_equal.
      by eapply global_agree_extension; eauto.
    + by eapply IHig; eauto.
Qed.

Lemma memi_agree_extension: forall m0 m1 n m,
    memi_agree m0 n m ->
    all2 mem_extension m0 m1 ->
    memi_agree m1 n m.
Proof.
  move => m0 m1 n m H1 H2.
  assert (size m0 = size m1) as HSize; first by eapply all2_size; eauto.
  unfold memi_agree.
  unfold memi_agree in H1. unfold mem_extension in H2.
  destruct m => //=.
  remove_bools_options.
  rewrite length_is_size in H.
  apply/andP; split => //=; first by rewrite HSize in H.
  rewrite HSize in H.
  rewrite -length_is_size in H.
  move/ltP in H.
  rewrite <- List.nth_error_Some in H.
  destruct (List.nth_error m1 n) eqn:HN => //=.
  unfold mem_typing. simpl.
  eapply all2_projection in H2; [| by apply Hoption | by apply HN ].
  unfold mem_typing in H0. simpl in H0.
  remove_bools_options.
  apply/andP; split.
  - apply N.leb_le. apply N.leb_le in H1. apply N.leb_le in H0.
    by lias.
  - rewrite H3 in H2. rewrite H2. by apply/eqP.
Qed.

Lemma mem_extension_C: forall sm sm' im tcm,
    all2 (memi_agree sm) im tcm ->
    all2 mem_extension sm sm' ->
    all2 (memi_agree sm') im tcm.
Proof.
  move => sm sm' im.
  generalize dependent sm; generalize dependent sm'.
  induction im; move => sm' sm tcm HA Hext => //=; destruct tcm => //=.
  simpl in HA. remove_bools_options.
  apply/andP; split => //=; last by eapply IHim; eauto.
  by eapply memi_agree_extension; eauto.
Qed.

Lemma tabi_agree_extension: forall t0 t1 n t,
    tabi_agree t0 n t ->
    all2 tab_extension t0 t1 ->
    tabi_agree t1 n t.
Proof.
  move => t0 t1 n t H1 H2.
  assert (size t0 = size t1) as HSize; first by eapply all2_size; eauto.
  unfold tabi_agree.
  unfold tabi_agree in H1. unfold tab_extension in H2.
  unfold tab_size in H2.
  destruct t => //=.
  destruct t0 => //=; try by destruct n.
  destruct t1 => //=.
  simpl in H2. simpl in H1.
  remove_bools_options.
  unfold tab_typing in H1.
  remove_bools_options.
  simpl in H3. simpl in H1.
  unfold tab_typing. simpl.
  simpl in HSize. inversion HSize.
  assert (n < size (t :: t0)).
  { rewrite - length_is_size.
    assert (List.nth_error (t :: t0) n <> None); first by rewrite Hoption.
    apply List.nth_error_Some in H4. lias. } 
  (* subst. clear HSize. 
  apply/andP; split => //=. 
 - rewrite length_is_size in H1. rewrite length_is_size. by rewrite H6 in H1.
  - *)
  assert (List.nth_error (t1 :: t2) n <> None).
  { apply List.nth_error_Some. rewrite length_is_size. simpl. rewrite -HSize.
    by lias. } 
  destruct (List.nth_error (t1 :: t2) n) eqn:HN => //=.
  destruct n => //=.
  - simpl in HN. simpl in Hoption. inversion HN. inversion Hoption. subst.
    apply/andP; split => //=; last by rewrite -H2.
    unfold tab_size. unfold tab_size in H1. by lias.
  - simpl in HN. simpl in Hoption.
    eapply all2_projection in H0; eauto.
    remove_bools_options.
    apply/andP; split => //=; last by rewrite -H7.
    unfold tab_size. unfold tab_size in H1. by lias.
Qed.

Lemma tab_extension_C: forall st st' it tct,
    all2 (tabi_agree st) it tct ->
    all2 tab_extension st st' ->
    all2 (tabi_agree st') it tct.
Proof.
  move => st st' it.
  generalize dependent st; generalize dependent st'.
  induction it; move => st' st tct HA Hext => //=; destruct tct => //=.
  simpl in HA. remove_bools_options.
  apply/andP; split => //=; last by eapply IHit; eauto.
  by eapply tabi_agree_extension; eauto.
Qed.



Lemma globals_agree_extension: forall s s' inst_globs tc_global,
    store_extension s s' ->
    all2 (globals_agree s (s_globals s)) inst_globs tc_global ->
    all2 (globals_agree s' (s_globals s)) inst_globs tc_global.
Proof.
  intros s s' inst_globs tc_global HST Hall.
  apply all2_Forall2.
  eapply List.Forall2_impl; last by apply all2_Forall2 in Hall; exact Hall.
  intros n g_val Hagree. simpl in Hagree.
  unfold globals_agree. move/andP in Hagree. destruct Hagree as [Hsize Hagree].
  move/eqP in Hagree. apply/andP. split; first done.
  destruct (List.nth_error (s_globals s) n) eqn:Hn => //=.
  simpl in Hagree. apply/eqP. unfold global_agree.
  f_equal. apply/andP.
  inversion Hagree. 
  unfold global_agree in H0; remove_bools_options.
  destruct (typeof_extension (datatypes.g_val g) HST) as [Htypeof | [[Hcorrupt _] | [Hcorrupt _]]].
  + split => //; first by rewrite H. rewrite H0 Htypeof. done.
  + rewrite Hcorrupt in H0. done. 
  + rewrite Hcorrupt in H0. done.
Qed.

Lemma glob_extension_extension: forall s s',
    store_extension s s' ->
    all2 (glob_extension s) (s_globals s) (s_globals s') ->
    all2 (glob_extension s') (s_globals s) (s_globals s').
Proof.
  intros s s' HST Hall.
  apply all2_Forall2.
  eapply List.Forall2_impl; last by apply all2_Forall2 in Hall; exact Hall.
  intros g g' Hext. simpl in Hext.
  unfold glob_extension. unfold glob_extension in Hext.
  destruct (g_mut g) => //. destruct (g_mut g') => //.
  destruct (typeof_extension (g_val g) HST) as [<- | [(Hcorrupt & tf & Habs) | [ Hcorrupt Habs]]].
  - destruct (typeof_extension (g_val g') HST) as [<- | [(Hcorrupt & tf & Habs) | [Hcorrupt Habs]]] => //.
    + rewrite Hcorrupt in Hext. remove_bools_options.    
      rewrite H in H0 => //.
    + rewrite Hcorrupt in Hext. remove_bools_options.
      rewrite H in H0 => //.
  - rewrite Hcorrupt in Hext. move/andP in Hext. destruct Hext as [_ ?] => //.
  - rewrite Hcorrupt in Hext. move/andP in Hext. destruct Hext as [_ ?] => //.
Qed. 


Lemma inst_typing_extension: forall s s' i C,
    store_extension s s' ->
    inst_typing s i C ->
    inst_typing s' i C.
Proof.
  move => s s' i C HST HIT.
  assert (store_extension s s') as HST'; first done.
  unfold store_extension in HST. unfold operations.store_extension in HST.
  unfold inst_typing in HIT. unfold typing.inst_typing in HIT.
  unfold inst_typing. unfold typing.inst_typing.
  destruct i => //=.
  destruct C => //=.
  destruct tc_local => //. destruct tc_label => //. destruct tc_return => //.
  remove_bools_options. rewrite - H5.
  repeat (apply/andP; split => //=; subst => //=).
  - eapply glob_extension_C. apply globals_agree_extension; eauto.
    apply glob_extension_extension; eauto.
  - by eapply tab_extension_C; eauto.
  - by eapply mem_extension_C; eauto.
  - by rewrite - H11.
Qed.



Lemma map_equiv {A B} (f: A -> B) f' l:
  (forall x, List.In x l -> f x = f' x) -> map f l = map f' l.
Proof.
  induction l => //=. intros H; rewrite H; last by left.
  rewrite IHl => //. intros x Hx. apply H. by right.
Qed.

Lemma map_in { A B } x l (f: A -> B):
  List.In x l -> List.In (f x) (map f l).
Proof.
  induction l => //=. intros [-> | H] => //=.
  by left. by right; apply IHl.
Qed. 

Lemma Forall2_nth_error {A B} (P : A -> B -> Prop) l1 l2 i v1:
  List.Forall2 P l1 l2 ->
  List.nth_error l1 i = Some v1 ->
  exists v2, List.nth_error l2 i = Some v2 /\ P v1 v2.
Proof.
  generalize dependent i; generalize dependent l2.
  induction l1; intros l2 i HP Hv1; destruct i => //=. 
  - simpl in Hv1. inversion Hv1; subst a.
    destruct l2; inversion HP; subst.
    exists b. split => //.
  - simpl in Hv1. destruct l2; inversion HP; subst.
    eapply IHl1; eauto.
Qed. 
    

Lemma nth_error_lt_Some {A} i (l: list A) v:
  List.nth_error l i = Some v -> i < length l.
Proof.
  generalize dependent i.
  induction l; intros i; destruct i => //.
  intros H; inversion H. apply IHl in H1. lias.
Qed.

Lemma nth_error_app_left {A} i (l: list A) l':
  i < length l ->
  List.nth_error (l ++ l') i = List.nth_error l i.
Proof.
  generalize dependent i.
  induction l => //=.
  intros i Hi.
  destruct i => //=.
  apply IHl. lias.
Qed.

Lemma take_full {A} n (l: list A):
  length (take n l) = n -> n <= length l.
Proof.
  generalize dependent n.
  induction l; intros n => //=.
  by intros <-.
  destruct n => //=.
  intros H. assert (length (take n l) = n); first lias.
  apply IHl in H0. lias.
Qed. 

Lemma nth_take {A} l n k (x: A):
  List.nth_error (take n l) k = Some x ->
  List.nth_error l k = Some x.
Proof.
  generalize dependent n; generalize dependent k.
  induction l => //=.
  destruct n, k => //=. 
  apply IHl.
Qed. 

Lemma value_typing_extension s s' C v t:
  store_extension s s' ->
  e_typing s C [::AI_const v] (Tf [::] [:: t]) ->
  e_typing s' C [::AI_const v] (Tf [::] [:: t]).
Proof.
  intros Hsext Htyp.
  apply AI_const_typing in Htyp as (tv & Htv & Htypes & Htyp).
  inversion Htypes; subst tv; clear Htypes.
  destruct v => //=.
  - apply ety_a'; first by constructor.
    simpl in Htv. inversion Htv; subst t.
    econstructor.
  - destruct v => //=.
    + apply ety_a'; first by constructor.
      simpl in Htv. inversion Htv; subst t.
      econstructor.
    + simpl in Htv.
      destruct (List.nth_error _ _) eqn:Hf => //.
      inversion Htv; subst t.
      eapply ety_ref.
      unfold store_extension in Hsext. remove_bools_options.
      rewrite - H. exact Hf. done.
    + simpl in Htv.
      destruct (List.nth_error _ _) eqn:Hf => //.
      simpl in Htyp.
      apply AI_ref_cont_typing in Htyp as (t0 & Ht0 & Htypes).
      inversion Htypes; subst; clear Htypes.
      inversion Htv; subst.
      unfold store_extension in Hsext. remove_bools_options.
      apply all2_Forall2 in H4.
      apply nth_error_lt_Some in Hf as Hflen. 
      eapply Forall2_nth_error in Hf as (cont' & Hcont' & Hc); last exact H4.
      eapply ety_ref_cont.
      rewrite - (cat_take_drop (length (s_conts s)) (s_conts s')).
      rewrite nth_error_app_left.
      exact Hcont'.
      rewrite length_is_size size_takel => //.
      apply List.Forall2_length in H4.
      symmetry in H4. apply take_full in H4.
      rewrite - length_is_size. done.
      simpl in Hc. destruct c, cont' => //.
      * simpl in Hc. move/eqP in Hc. inversion Hc; subst; done.
      * simpl in Hc. move/eqP in Hc. subst; done.
      * simpl in Hc. move/eqP in Hc. subst; done.
    + simpl in Htv.
      destruct (List.nth_error _ e) eqn:He => //.
      destruct (e_tag e0 == t0) eqn:Htag => //. 
      inversion Htv; subst.
      apply AI_ref_exn_typing in Htyp as (exn & Hexn & Hetag & _).
      unfold store_extension in Hsext. remove_bools_options.
      rewrite H0 in Hexn.
      eapply ety_ref_exn.
      eapply nth_take.
      exact Hexn.
      done.
Qed. 


Lemma frame_typing_extension: forall s s' f C,
    store_extension s s' ->
    frame_typing s f C ->
    frame_typing s' f C.
Proof.
  move => s s' f C HST HIT.
  inversion HIT. subst.
  eapply inst_typing_extension in H; eauto.
  eapply mk_frame_typing; eauto.
  eapply List.Forall2_impl; last exact H1.
  intros v t Ht.
  eapply value_typing_extension; last exact Ht.
  exact HST.
Qed. 

Lemma reflexive_all2_same: forall {X:Type} f (l: seq X),
    reflexive f ->
    all2 f l l.
Proof.
  move => X f l.
  induction l; move => H; unfold reflexive in H => //=.
  apply/andP. split => //=.
  by apply IHl.
Qed.

Lemma all2_tab_extension_same: forall t,
    all2 tab_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive. move => x. unfold tab_extension.
  by apply/andP.
Qed.

 Lemma all2_cont_extension_same: forall t,
    all2 cont_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive. move => x. unfold cont_extension.
  destruct x => //. 
Qed. 

Lemma all2_mem_extension_same: forall t,
    all2 mem_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive. move => x. unfold mem_extension.
  apply/andP; split => //.
  by apply N.leb_le; lias.
Qed.

Lemma all2_glob_extension_same: forall s t,
    (forall x, List.In x t -> typeof s (g_val x) <> None) ->   
    all2 (glob_extension s) t t.
Proof. 
  move => s t Hcorrupt.
  induction t => //=.
  apply/andP.
  split.
  - unfold glob_extension.
    destruct (g_mut a) => //. apply/andP; split => //.
    apply/andP; split => //.
    destruct (typeof s (g_val a)) eqn:H => //.
    exfalso.
    eapply Hcorrupt; last exact H. by left.
  - apply IHt. intros x Hx. apply Hcorrupt. by right.
Qed.

Ltac convert_et_to_bet:=
  lazymatch goal with
  | H: e_typing _ _ _ _ |- _ =>
    apply et_to_bet in H; try auto_basic; simpl in H
  end.

Ltac split_et_composition:=
  lazymatch goal with
  | H: e_typing _ _ (_ ++ _) _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let t2s := fresh "t2s" in
    let t3s := fresh "t3s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply e_composition_typing in H;
    destruct H as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]]; subst
  | H: typing.e_typing _ _ (_ ++ _) _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let t2s := fresh "t2s" in
    let t3s := fresh "t3s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply e_composition_typing in H;
    destruct H as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]]; subst
  end.

Ltac invert_e_typing:=
  repeat lazymatch goal with
  | H: e_typing _ _ (_ ++ _) _ |- _ =>
    split_et_composition
  | H: typing.e_typing _ _ (_ ++ _) _ |- _ =>
    split_et_composition
  | H: e_typing _ _ [::AI_label _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Label_typing in H;
    destruct H as [ts [t1s [H1 [H2 [H3 H4]]]]]; subst
  | H: typing.e_typing _ _ [::AI_label _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    eapply Label_typing in H; eauto;
    destruct H as [ts [t1s [H1 [H2 [H3 H4]]]]]; subst
    | H: e_typing _ _ [::AI_handler _ _] _ |- _ =>
        let ts := fresh "ts" in
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        let H3 := fresh "H3" in
        apply Handler_typing in H;
        destruct H as (ts & H1 & H2 & H3); subst
    | H: typing.e_typing _ _ [::AI_handler _ _] _ |- _ =>
        let ts := fresh "ts" in
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        let H3 := fresh "H3" in
        apply Handler_typing in H;
        destruct H as ( ts & H1 & H2 & H3); subst
    | H: e_typing _ _ [::AI_prompt _ _ _] _ |- _ =>
        let ts := fresh "ts" in
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        let H3 := fresh "H3" in
        apply Prompt_typing in H;
        destruct H as ((* ts & *) H1 & H2 & H3); subst
    | H: typing.e_typing _ _ [::AI_prompt _ _ _] _ |- _ =>
        let ts := fresh "ts" in
        let H1 := fresh "H1" in
        let H2 := fresh "H2" in
        let H3 := fresh "H3" in
        apply Prompt_typing in H;
        destruct H as ((* ts & *) H1 & H2 & H3); subst 
  end.


Lemma lfilled_es_type_exists: forall k lh es les s C tf,
    lfilled k lh es les ->
    e_typing s C les tf ->
    exists lab t1s t2s, e_typing s (upd_label C lab) es (Tf t1s t2s).
Proof.
  move => k lh es les s C tf HLF.
  generalize dependent tf.
  generalize dependent C.
  move/lfilledP in HLF.
  induction HLF; move => C tf HType; destruct tf.
  - invert_e_typing.
    exists (tc_label C), t1s0, t3s0 => //=.
    by rewrite upd_label_unchanged.
  - invert_e_typing.
    edestruct IHHLF; first by apply H4.
    destruct H0 as [t1s' t2s'].
    by eauto.
  - invert_e_typing.
    eapply IHHLF. exact H4. 
  - invert_e_typing.
    eapply IHHLF. eapply typing_leq. exact H4.
    apply empty_context_leq.
Qed.

Lemma store_extension_same: forall s,
    store_typing s ->
(*    (forall x, List.In x (s_globals s) -> typeof s (g_val x) <> None) ->   *)
    store_extension s s.
Proof.
  move => s Hcorrupt. unfold store_extension.
  repeat (apply/andP; split).
  + by apply/eqP.
  + done.
  + rewrite take_size. by apply all2_cont_extension_same. 
  + by apply all2_tab_extension_same.
  + by apply all2_mem_extension_same.
  + apply all2_glob_extension_same.
    destruct s; destruct Hcorrupt as (_ & _ & _ & Hg).
    rewrite List.Forall_forall in Hg.
    intros g Hin. apply Hg in Hin as [t Hgt].
    apply AI_const_typing in Hgt as (t0 & Hgt0 & _).
    rewrite Hgt0. done.
  + rewrite length_is_size. rewrite take_size. done.
Qed.

Lemma store_extension_cl_typing: forall s s' cl tf,
    store_extension s s' ->
    cl_typing s cl tf ->
    cl_typing s' cl tf.
Proof.
  move => s s' cl tf Hext HType.
  inversion HType; subst.
  - eapply cl_typing_native; eauto.
    by eapply inst_typing_extension; eauto.
  - by eapply cl_typing_host; eauto.
Qed.




Lemma all2_nth {A B} f (l1: list A) (l2 : list B) n x1:
  List.nth_error l1 n = Some x1 ->
  all2 f l1 l2 ->
  exists x2, List.nth_error l2 n = Some x2 /\ f x1 x2.
Proof.
  generalize dependent l2. generalize dependent n.
  induction l1 => //=.
  - destruct n => //.
  - intros n l2 Hx Hl2. destruct l2 => //.
    move/andP in Hl2. destruct Hl2 as [Hab Hl2].
    destruct n => //=.
    + exists b. inversion Hx; subst. done.
    + simpl in Hx. apply IHl1 => //.
Qed. 

Lemma store_extension_continuation_clause_typing s s' C h ts:
  store_extension s s' ->
  continuation_clause_typing s C h ts ->
  continuation_clause_typing s' C h ts.
Proof.
  intros Hsext Htyp.
  inversion Htyp; subst.
  all: econstructor; eauto.
  all: unfold store_extension in Hsext.
  all: remove_bools_options.
  by rewrite - H7.
  by rewrite - H6.
Qed.

Lemma store_extension_exception_clause_typing s s' C h:
  store_extension s s' ->
  exception_clause_typing s C h ->
  exception_clause_typing s' C h.
Proof.
  intros Hsext Htyp.
  inversion Htyp; subst.
  all: econstructor; eauto.
  all: unfold store_extension in Hsext.
  all: remove_bools_options.
  all: by rewrite - H7.
Qed. 


Lemma store_extension_e_typing: forall s s' C es tf,
    store_typing s ->
    store_extension s s' ->
    e_typing s C es tf -> e_typing s' C es tf.
Proof.
  move => s s' C es tf HST1 Hext HType.
  move: s' HST1 Hext.
  apply e_typing_ind' with (e := HType)
    (P := fun s C es tf (_ : e_typing s C es tf) => forall s',
            store_typing s ->
            store_extension s s' ->
            e_typing s' C es tf)
    (P0 := fun s rs f es ts (_ : s_typing s rs f es ts) => forall s',
             store_typing s ->
             store_extension s s' ->
             s_typing s' rs f es ts) ; clear HType s C es tf.
  - move=> s C bes tf HType s' HST1 (* HST2 *) Hext.
    apply ety_a'; first by apply to_e_list_basic.
    replace (operations.to_b_list (operations.to_e_list bes)) with bes => //.
    by apply b_e_elim.
  - move=> s C bes tf r1 r2 r3 HType1 IHHType1 IH2 IHHType2 s' HST1 (* HST2 *) Hext.
    eapply ety_composition.
    + by apply IHHType1.
    + by apply IHHType2.
  - move=> s C es tf t1s t2s HType IHHType s' HST1 (* HST2 *) Hext.
    eapply ety_weakening. by apply IHHType.
  - move=> s C tf s' HST1 (* HST2 *) Hext.
    by apply ety_trap.
  - move=> s C' n f es ts HType IHHType E s' HST1 (* HST2 *) Hext.
    apply ety_local => //.
    by eapply IHHType; try apply HST1 => //.
  - move => s C a tf cl Ha Hcl s' HST1 (* HST2 *) Hext.
    econstructor.
    unfold store_extension in Hext. remove_bools_options. rewrite - H. exact Ha.
    done. 
    
  - move => s C a cont tf Ha <- s' HST1 (* HST2 *) Hext.
    unfold store_extension in Hext. remove_bools_options.
    destruct (all2_nth Ha H4) as (cont' & Hs' & Hext).
    destruct cont'.
    + move/eqP in Hext; subst.
      econstructor. eapply nth_take. exact Hs'.
      done.
    + move/eqP in Hext. rewrite Hext.
      replace f with (typeof_cont (Cont_dagger f)) => //. econstructor.
      eapply nth_take. exact Hs'. constructor. (* done. *)
  - move => s C k i exn Hexn Hetag s' HST Hext.
    unfold store_extension in Hext. remove_bools_options.
    rewrite H0 in Hexn.
    econstructor.
    rewrite - (cat_take_drop (length (s_exns s)) (s_exns s')).
    apply nth_error_prefix. exact Hexn.
    exact Hetag.
  - intros s C x vs t1s t2s Hx Hvs IHvs s' HST Hext.
    econstructor => //.
    + unfold store_extension in Hext.
      remove_bools_options.
      rewrite - H5. exact Hx.
    + apply IHvs => //. 
  - intros s C vs k tf x ts t1s t2s cont Hx Htf Hk Hcont Htypes IHvs s' HST Hext.
    remember Hext as Hext'; clear HeqHext'.
    unfold store_extension in Hext.
    remove_bools_options.
    apply all2_Forall2 in H4.
    eapply Forall2_nth_error in H4 as (cont' & Hk' & Hcont').
    2: exact Hk.
    
    econstructor.
    2: exact Htf.
    rewrite - H5. done.
    rewrite - (cat_take_drop (length (s_conts s)) (s_conts s')).
    apply nth_error_prefix.
    exact Hk'.
    unfold cont_extension in Hcont'.
    destruct cont'.
    1-2: move/eqP in Hcont'.
    1-2: rewrite -Hcont' => //.
    apply IHvs => //. 
  - intros s C vs a i tf exn Hexn Hi Hvs s' HST Hext.
    econstructor => //.
    2: exact Hi.
    2: exact Hvs.
    unfold store_extension in Hext.
    remove_bools_options.
    rewrite H0 in Hexn.
    rewrite - (cat_take_drop (length (s_exns s)) (s_exns s')).
    apply nth_error_prefix.
    exact Hexn.
  - move => s C (* ts0 *) hs es ts Hclauses Hes IHHType s' HST1 (* HST2 *) Hext.
    econstructor.
    eapply List.Forall_impl; last exact Hclauses.
    intros h Hh.
    eapply store_extension_continuation_clause_typing; eauto.
    apply IHHType => //. 
  - move => s C (* ts0 *) hs es ts Hclauses Hes IHHType s' HST1 (* HST2 *) Hext.
    econstructor.
    eapply List.Forall_impl; last exact Hclauses.
    intros h Hh.
    eapply store_extension_exception_clause_typing; eauto.
    apply IHHType => //. 
  - move => s a C cl tf HNth HCLType s' HST1 (* HST2 *) Hext.
    replace (s_funcs s) with (s_funcs s') in HNth.
    eapply ety_invoke; eauto => //.
    unfold store_extension, operations.store_extension in Hext.
    by remove_bools_options. 
  - move=> s C es es' t1s t2s n HType1 IHHType1 HType2 IHHType2 E s' HST1 (* HST2 *) Hext.
    eapply ety_label => //; eauto.
  - move => s C t1s t2s h vs Hlen s'0 HST1 (* HST2 *) Hext.
    eapply ety_call_host ; eauto.
  - move=> s f es rs ts C C' HFType HContext HType IHHType E' s' HST1 (* HST2 *) Hext.
    eapply mk_s_typing; eauto.
    by eapply frame_typing_extension; eauto.
Defined. 


Lemma glob_extension_update_nth: forall sglobs n s g g',
    (forall x, List.In x sglobs -> typeof s (g_val x) <> None) ->  
  List.nth_error sglobs n = Some g ->
  glob_extension s g g' ->
  all2 (glob_extension s) sglobs (update_list_at sglobs n g').
Proof.
  move => sglobs n s.
  generalize dependent sglobs.
  induction n; move => sglobs g g' Hcorrupt HN Hext => //=; destruct sglobs => //.
  - simpl in HN. inversion HN. subst.
    apply/andP; split => //=.
    apply all2_glob_extension_same.
    intros x Hx. apply Hcorrupt. by right.
  - assert ((n.+1 < length (g0 :: sglobs))%coq_nat); first by rewrite -List.nth_error_Some; rewrite HN.
    erewrite <-update_list_at_is_set_nth; last by lias.
    simpl.
    apply/andP. split.
    + unfold glob_extension. destruct (g_mut g0) => //.
      apply/andP; split => //. apply/andP; split => //.
      destruct (typeof s (g_val g0)) eqn:Habs => //.
      exfalso. eapply Hcorrupt; last exact Habs. by left.
    + rewrite update_list_at_is_set_nth.
      * eapply IHn; eauto.
        intros x Hx. apply Hcorrupt. by right.
      * simpl in H. rewrite length_is_size in H. by lias.
Qed. 

Lemma tc_reference_glob_type: forall s i C n m gt g,
    inst_typing s i C ->
    List.nth_error i.(inst_globs) n = Some m ->
    List.nth_error s.(s_globals) m = Some g ->
    List.nth_error C.(tc_global) n = Some gt ->
    global_agree s g gt.
Proof.
  move => s i C n m gt g HIT HN1 HN2 HN3.
  unfold inst_typing in HIT. unfold typing.inst_typing in HIT.
  destruct i => //=.
  destruct C => //=.
  destruct tc_local => //=.
  destruct tc_label => //=.
  destruct tc_return => //=.
  remove_bools_options.
  eapply all2_projection in H3; eauto.
  unfold globals_agree in H3.
  rewrite HN2 in H3.
  by remove_bools_options.
Qed.

Lemma tc_reference_tag: forall s i C n m gt g,
    inst_typing s i C ->
    List.nth_error i.(inst_tags) n = Some m ->
    List.nth_error s.(s_tags) m = Some g ->
    List.nth_error C.(tc_tags_t) n = Some gt ->
    g = gt. 
Proof.
  move => s i C n m gt g HIT HN1 HN2 HN3.
  unfold inst_typing in HIT. unfold typing.inst_typing in HIT.
  destruct i => //=.
  destruct C => //=.
  destruct tc_local => //=.
  destruct tc_label => //=.
  destruct tc_return => //=.
  remove_bools_options.
  eapply all2_projection in H0; eauto.
  unfold tag_agree in H0.
  rewrite HN2 in H0.
  by remove_bools_options.
Qed.

Lemma mem_extension_update_nth: forall smems n m m',
  List.nth_error smems n = Some m ->
  mem_extension m m' ->
  all2 mem_extension smems (update_list_at smems n m').
Proof.
  move => smems n.
  generalize dependent smems.
  induction n; move => smems m m' HN Hext => //=; destruct smems => //.
  - simpl in HN. inversion HN. subst.
    apply/andP. split; first apply Hext.
   by apply all2_mem_extension_same.
  - assert ((n.+1 < length (m0 :: smems))%coq_nat); first by rewrite -List.nth_error_Some; rewrite HN.
    rewrite -update_list_at_is_set_nth; last by lias.
    simpl.
    apply/andP. split.
    + unfold mem_extension. apply/andP; split => //.
      apply N.leb_le; by lias.
    + rewrite update_list_at_is_set_nth.
      * by eapply IHn; eauto.
      * simpl in H. rewrite length_is_size in H. by lias.
Qed.

Lemma bytes_takefill_size: forall c l vs,
    size (bytes_takefill c l vs) = l.
Proof.
  move => c l. induction l => //=.
  by destruct vs => //=; f_equal.
Qed.

Lemma bytes_replicate_size: forall n b,
    size (bytes_replicate n b) = n.
Proof.
  induction n => //=.
  by move => b; f_equal.
Qed.

Lemma div_le: forall a b, b > 0 -> a/b <= a.
Proof.
  move => a b H.
  destruct b => //.
  destruct b => //; first by rewrite Nat.div_1_r; lias.
  destruct a => //.
  assert (a.+1/b.+2 < a.+1)%coq_nat.
  { by apply Nat.div_lt; lias. }
  by lias.
Qed.

(* Start of proof to write_bytes preserving memory type *)

Lemma list_fold_left_rev_prop: forall {X Y: Type} P f (l: seq X) (a1 a2: Y),
    List.fold_left f l a1 = a2 ->
    P a2 ->
    (forall a e a', P a' -> f a e = a' -> P a) ->
    P a1.
Proof.
  move => X Y P f l.
  elim: l => //=.
  - move => a1 a2 H. by subst.
  - move => e l IH a1 a2 HFold HP HNec.
    assert (HPF: P (f a1 e)); first by eapply IH; eauto.
    by eapply HNec; eauto.
Qed.
    
Lemma list_fold_left_restricted_trans: forall {X Y: Type} P R f (l: seq X) (a1 a2: Y),
    List.fold_left f l a1 = a2 ->
    P a1 ->
    P a2 ->
    (forall a e a', P a -> P a' -> f a e = a' -> R a a') ->
    (forall a, P a -> R a a) ->
    (forall a1 a2 a3, P a1 -> P a2 -> P a3 -> R a1 a2 -> R a2 a3 -> R a1 a3) ->
    (forall a e a', P a' -> f a e = a' -> P a) ->
    R a1 a2.
Proof.
  move => X Y P R f l.
  elim: l => //=.
  - move => a1 a2 H HP1 HP2 HF HRefl HTrans HNec. subst.
    by apply HRefl.
  - move => e l IH a1 a2 HFold HP1 HP2 HF HRefl HTrans HNec.
    assert (HPF: P (f a1 e)); first by eapply list_fold_left_rev_prop; eauto.
    assert (HRf2: R (f a1 e) a2); first by apply IH.
    assert (HR1f: R a1 (f a1 e)); first by eapply HF; eauto.
    by eapply HTrans; eauto.
Qed.
    
Definition proj2_some (acc: nat * option memory_list.memory_list) : Prop :=
  let (n, om) := acc in
  exists m, om = Some m.

Definition mem_type_proj2_preserve (acc1 acc2: nat * option memory_list.memory_list) : Prop :=
  let (n1, om1) := acc1 in
  let (n2, om2) := acc2 in
  (exists m1 m2,
      om1 = Some m1 /\
      om2 = Some m2 /\
      memory_list.length_mem m1 = memory_list.length_mem m2).

Lemma mem_type_proj2_preserve_trans: forall a1 a2 a3,
    proj2_some a1 ->
    proj2_some a2 ->
    proj2_some a3 ->
    mem_type_proj2_preserve a1 a2 ->
    mem_type_proj2_preserve a2 a3 ->
    mem_type_proj2_preserve a1 a3.
Proof.
  unfold mem_type_proj2_preserve, proj2_some.
  move => a1 a2 a3 HP1 HP2 HP3 HR12 HR23.
  destruct a1, a2, a3 => /=.
  destruct HP1, HP2, HP3, HR12, HR23. subst.
  repeat eexists; eauto.
  destruct H2 as [m2 [H21 [H22 HLen1]]].
  destruct H3 as [m2' [H31 [H32 HLen2]]].
  inversion H21. inversion H22. inversion H31. inversion H32. subst.
  by lias.
Qed.

Lemma write_bytes_preserve_type: forall m pos str m',
  write_bytes m pos str = Some m' ->
  (mem_size m = mem_size m') /\ (mem_max_opt m = mem_max_opt m').
Proof.
  unfold write_bytes, fold_lefti.
  move => m pos str m' H.
  remove_bools_options.
  match goal with | H : ?T = _ |- _ =>
                    match T with context [List.fold_left ?f ?str ?nom] => remember (List.fold_left f str nom) as fold_res
                    end
  end.
  assert (HPreserve: mem_type_proj2_preserve (0, Some (mem_data m)) fold_res).
  symmetry in Heqfold_res.
  destruct fold_res; subst.
  eapply list_fold_left_restricted_trans with (P := proj2_some); unfold proj2_some; eauto.
  - move => a e a' HP1 HP2 HF.
    unfold mem_type_proj2_preserve.
    destruct a as [n1 m1]. destruct a' as [n2 m2].
    destruct HP1 as [m3 HP1]; destruct HP2 as [m4 HP2].
    subst.
    repeat eexists.
    injection HF. move => H1 H2. subst. clear HF.
    unfold memory_list.mem_update in H1.
    destruct (pos + N.of_nat n1 <? N.of_nat (length (memory_list.ml_data m3)))%num eqn:HMemSize => //=.
    injection H1. move => H2. clear H1. subst.
    unfold memory_list.length_mem => /=.
    repeat rewrite length_is_size.
    repeat rewrite size_cat => /=.
    rewrite size_take. rewrite size_drop.
    apply N.ltb_lt in HMemSize.
    rewrite length_is_size in HMemSize.
    assert (N.to_nat (pos+N.of_nat n1) < size (memory_list.ml_data m3)); first by lias.
    rewrite H.
    by lias.
  - move => a HP. destruct a as [n1 m1].
    destruct HP as [m2 HP]. subst.
    unfold mem_type_proj2_preserve.
    by repeat eexists.
  - by apply mem_type_proj2_preserve_trans.
  - move => a e a' HP HF.
    destruct a as [n1 m1]. destruct a' as [n2 m2].
    destruct HP as [m3 HP]. subst.
    destruct m1; inversion HF => //=; subst.
    by eexists.
  - simpl in HPreserve. destruct fold_res. subst.
    destruct HPreserve as [m1 [m2 [H1 [H2 HLen]]]].
    inversion H1; inversion H2; subst; clear H1; clear H2.
    split => //.
    unfold mem_size, length_mem => /=.
    by rewrite HLen.
Qed.
  
Lemma mem_extension_store: forall m k off v tlen mem,
    store m k off (bits v) tlen = Some mem ->
    mem_extension m mem.
Proof.
  move => m k off v tlen mem HStore.
  unfold mem_extension.
  unfold store in HStore.
  destruct ((k + off + N.of_nat tlen <=? length_mem m)%num) eqn:HMemSize => //.
  remove_bools_options.
  apply write_bytes_preserve_type in HStore; destruct HStore as [H1 H2]; rewrite H1; rewrite H2.
  apply/andP; split => //=.
  apply N.leb_le.
  by lias.
Qed.

Lemma mem_extension_grow_memory: forall m c mem,
    mem_grow m c = (Some mem) ->
    mem_extension m mem.
Proof.
  move => m c mem HMGrow.
  unfold mem_extension.
  unfold mem_grow in HMGrow.
  destruct (mem_size m + c <=? page_limit)%num eqn:HLP => //.
  destruct (mem_max_opt m) eqn:HLimMax => //=.
  destruct ((mem_size m + c <=? n)%num) eqn:HLT => //.
  move : HMGrow.
  case: mem => mem_data_ mem_max_opt_ H.
  inversion H. subst. clear H.
  simpl.
  apply/andP.
  split => //.
  { unfold mem_size, length_mem, memory_list.length_mem in *.
    simpl.
    repeat rewrite length_is_size.
    rewrite size_cat.
    apply N.leb_le. 
    apply N.Div0.div_le_mono => //.
    by lias.
  }
  inversion HMGrow; subst; clear HMGrow.
  unfold mem_size, length_mem, memory_list.length_mem.
  simpl.
  apply/andP; split => //.
  apply N.leb_le.
  repeat rewrite length_is_size.
  rewrite size_cat.
  apply N.Div0.div_le_mono => //.
  by lias.
Qed.

Lemma Forall2_In {A B} P l1 (l2: list B) (x1 : A) :
  List.Forall2 P l1 l2 -> List.In x1 l1 -> exists x2, List.In x2 l2 /\ P x1 x2.
Proof.
  generalize dependent l2.
  induction l1 => //=.
  intros l2 Hall Hin.
  destruct l2; inversion Hall; subst.
  destruct Hin as [-> | Hin]; first by eexists b; split; first by left.
  edestruct IHl1 as (x2 & Hin2 & HP).
  exact H4. exact Hin.
  exists x2. split; try by right.
  exact HP.
Qed.


Lemma store_extension_glob_sound s s' g :
  store_extension s s' ->
  glob_sound s g ->
  glob_sound s' g.
Proof.
  intros Hext Hg.
  unfold glob_sound.
  destruct Hg as [t Ht]. exists t.
  eapply value_typing_extension; eauto.
Qed.


Lemma store_extension_c_typing s s' cont :
  store_typing s ->
  store_extension s s' ->
  c_typing s cont ->
  c_typing s' cont.
Proof.
  intros HST Hext Hcont.
  inversion Hcont; subst.
  constructor.
  econstructor.
  exact H.
  eapply store_extension_e_typing.
  exact HST. exact Hext. exact H0.
  exact H1.
  eapply store_extension_e_typing.
  exact HST. exact Hext. exact H2.
Qed. 

(*
Lemma glob_extension_sound s g g':
  glob_extension s g g' -> 
  glob_sound s g ->
  glob_sound s g'.
Proof.
  unfold glob_extension.
  destruct (g_mut g) => //.
  intros H; remove_bools_options. unfold glob_sound; rewrite - H0. done.
  destruct (g_mut g') => //.
  intros H; remove_bools_options. intros [t Ht].
  
  unfold glob_sound. ; rewrite H. done.
Qed.
*)

(* Could work if add a hypothesis on the globals on s' *)

 Lemma store_global_extension_store_typed: forall s s',
    store_typing s ->
    store_extension s s' ->
    (s_funcs s = s_funcs s') ->
    (s_tables s = s_tables s') ->
    (s_mems s = s_mems s') ->
    (s_tags s = s_tags s') ->
    (s_conts s = s_conts s') ->
    (s_exns s = s_exns s') ->
    List.Forall (glob_sound s') (s_globals s') ->
    store_typing s'.
Proof.
  move => s s' HST Hext HF (* HC *) HT HM HTg HC HE HG.
  remember HST as HST'. clear HeqHST'.
  unfold store_typing in HST.
  unfold store_typing.
  destruct s => //=.
  destruct s' => //=.
  destruct HST as (Hf & Ht & Hm (* & Hc *) & Hg & Hc & He).
  rewrite -> List.Forall_forall in Hf.
  rewrite -> List.Forall_forall in Ht. 
  repeat split => //; remove_bools_options; simpl in HF; simpl in HT; simpl in HM; simpl in HC; simpl in HTg; simpl in HE; (* simpl in HG; *) subst.
  - rewrite -> List.Forall_forall. move => x HIN.
    apply Hf in HIN. unfold cl_type_check_single in HIN.
    destruct HIN.
    unfold cl_type_check_single.
    exists x0.
    by eapply store_extension_cl_typing; eauto.
  - rewrite -> List.Forall_forall. move => x HIN.
    apply Ht in HIN. unfold tab_agree in HIN.
    destruct HIN.
    rewrite -> List.Forall_forall in H.
    unfold tab_agree.
    by rewrite -> List.Forall_forall.
  - unfold store_extension in Hext. simpl in Hext.
    remove_bools_options.
    rewrite List.Forall_forall.
    move => x HIN.
    destruct HST' as [_ [_ H8]].
    rewrite -> List.Forall_forall in H8.
    apply List.In_nth_error in HIN.
    destruct HIN as [n HN].
    apply H8. by eapply List.nth_error_In; eauto.
  - eapply List.Forall_impl; last exact Hc.
    intros cont Hcont.
    eapply store_extension_c_typing.
    exact HST'. exact Hext. exact Hcont.
  - eapply List.Forall_impl; last exact He.
    intros exn (t & Hexn & Htags).
    exists t. split => //. eapply store_extension_e_typing.
    exact HST'. exact Hext. exact Hexn.
(*  - rewrite List.Forall_forall.
    rewrite List.Forall_forall in Hg.
    intros x Hx.
    eapply store_extension_glob_sound.
    exact Hext.
    unfold store_extension in Hext; remove_bools_options.
    apply all2_Forall2 in H1.
    apply List.Forall2_flip in H1. 
    destruct (Forall2_In H1 Hx) as (x0 & Hx0 & Hext).
    eapply glob_extension_sound; last first.
    apply Hg. exact Hx0. done. *)
Qed.  

 Lemma store_memory_extension_store_typed: forall s s',
    store_typing s ->
    store_extension s s' ->
    (s_funcs s = s_funcs s') ->
    (s_tables s = s_tables s') ->
    (s_tags s = s_tags s') ->
    (s_conts s = s_conts s') ->
    (s_globals s = s_globals s') ->
    (s_exns s = s_exns s') ->
    List.Forall mem_agree (s_mems s') ->
    store_typing s'.
Proof.
  move => s s' HST Hext HF HT HC HG HTg HE HMem.
  remember HST as HST'. clear HeqHST'.
  unfold store_typing in HST.
  unfold store_typing.
  destruct s => //=.
  destruct s' => //=.
  destruct HST as (H & H0 & Hm (* & Hc *) & Hg & Hc & He).
  rewrite -> List.Forall_forall in H.
  rewrite -> List.Forall_forall in H0.
  repeat split => //; remove_bools_options; simpl in HF; simpl in HT; simpl in HC; simpl in HG; simpl in HTg; simpl in HE; subst.
  - rewrite -> List.Forall_forall. move => x HIN.
    apply H in HIN. unfold cl_type_check_single in HIN.
    destruct HIN.
    unfold cl_type_check_single.
    exists x0. by eapply store_extension_cl_typing; eauto.
  - rewrite -> List.Forall_forall. move => x HIN.
    apply H0 in HIN. unfold tab_agree in HIN.
    destruct HIN.
    rewrite -> List.Forall_forall in H1.
    unfold tab_agree.
    by rewrite -> List.Forall_forall.
  - eapply List.Forall_impl; last exact Hg.
    intros glob Hglob.
    eapply store_extension_glob_sound.
    exact Hext. exact Hglob.
  - eapply List.Forall_impl; last exact Hc.
    intros cont Hcont.
    eapply store_extension_c_typing.
    exact HST'. exact Hext. exact Hcont.
  - eapply List.Forall_impl; last exact He.
    intros exn (t & Hexn & Htags). exists t.
    split => //. eapply store_extension_e_typing.
    exact HST'. exact Hext. exact Hexn.
(*  - rewrite List.Forall_forall.
    rewrite List.Forall_forall in Hg.
    intros x Hx.
    eapply store_extension_glob_sound.
    exact Hext. 
    unfold store_extension in Hext; remove_bools_options.
    apply all2_Forall2 in H2.
    apply List.Forall2_flip in H2. 
    destruct (Forall2_In H2 Hx) as (x0 & Hx0 & Hext).
    eapply glob_extension_sound; last first.
    apply Hg. exact Hx0. done. *)
Qed. 

Lemma nth_error_map: forall {X Y:Type} l n (f: X -> Y) fv,
    List.nth_error (map f l) n = Some fv ->
    exists v,
      List.nth_error l n = Some v /\
      f v = fv.
Proof.
  move => X Y l n.
  generalize dependent l.
  induction n => //=; move => l f fv HNth; destruct l => //=.
  - destruct (map f (x::l)) eqn:HMap => //=.
    inversion HNth; subst.
    simpl in HMap. inversion HMap. subst.
    by eexists.
  - destruct (map f (x::l)) eqn:HMap => //=.
    simpl in HMap. inversion HMap. subst.
    by apply IHn.
Qed.
    
Lemma nth_error_update_list_hit: forall {X:Type} l n {x:X},
    n < length l ->
    List.nth_error (update_list_at l n x) n = Some x.
Proof.
  move => X l n. generalize dependent l.
  induction n => //=; destruct l => //=.
  - move => x' HLength.
    simpl. rewrite -cat1s.
    assert (n < length l); first by lias.
    assert (length (take n l) = n).
    { rewrite length_is_size. rewrite length_is_size in H.
      rewrite size_take. by rewrite H. }
    assert (List.nth_error (take n l ++ [:: x'] ++ List.skipn (n+1)%coq_nat l) (length (take n l)) = Some x'); first by apply list_nth_prefix.
    by rewrite H0 in H1.
Qed.

Lemma nth_error_update_list_others: forall {X:Type} l n m {x:X},
    n <> m ->
    n < length l ->
    List.nth_error (update_list_at l n x) m = List.nth_error l m.
Proof.
  move => X l n. move: l.
  induction n => //=; move => l m x Hne HLength.
  - destruct m => //=.
    by destruct l => //=.
  - destruct m => //=.
    + by destruct l => //=.
    + destruct l => //=.
      simpl in HLength.
      by apply IHn; lias.
Qed.

Lemma Forall_update: forall {X:Type} f l n {x:X},
    List.Forall f l ->
    f x ->
    n < length l ->
    List.Forall f (update_list_at l n x).
Proof.
  move => X f l n x HA Hf HLength.
  rewrite -> List.Forall_forall in HA.
  rewrite List.Forall_forall.
  move => x0 HIN.
  apply List.In_nth_error in HIN.
  destruct HIN as [n' HN].
  assert (n' < length (update_list_at l n x))%coq_nat.
  { rewrite <- List.nth_error_Some. by rewrite HN. }
  move/ltP in H.
  destruct (n == n') eqn:H1 => //=.
  - move/eqP in H1. subst.
    rewrite nth_error_update_list_hit in HN => //=. by inversion HN; subst.
  - move/eqP in H1.
    rewrite nth_error_update_list_others in HN => //=.
    apply HA.
    by eapply List.nth_error_In; eauto.
Qed.

Lemma store_typed_mem_agree: forall s n m,
    store_typing s ->
    List.nth_error (s_mems s) n = Some m ->
    mem_agree m.
Proof.
  move => s n m HST HN.
  unfold store_typing in HST.
  destruct s => //=.
  destruct HST as [_ [_ H]].
  rewrite -> List.Forall_forall in H.
  simpl in HN.
  apply H. by eapply List.nth_error_In; eauto.
Qed.

Lemma store_mem_agree: forall s n m k off vs tl mem,
    store_typing s ->
    List.nth_error (s_mems s) n = Some m ->
    store m k off vs tl = Some mem ->
    tl > 0 ->
    mem_agree mem.
Proof.
  move => s n m k off vs tl mem HST HN HStore HTL.
  unfold store in HStore.
  destruct ((k+off+N.of_nat tl <=? length_mem m)%num) eqn:H => //=.
  apply write_bytes_preserve_type in HStore.
  destruct HStore as [HMemSize HMemLim].
  assert (mem_agree m); first by eapply store_typed_mem_agree; eauto.
  unfold mem_agree in H0. rewrite HMemLim in H0.
  unfold mem_agree => //=.
  destruct (mem_max_opt mem) eqn:HLimMax => //=.
  by rewrite HMemSize in H0.
Qed.

Lemma mem_grow_mem_agree: forall s n m c mem,
    store_typing s ->
    List.nth_error (s_mems s) n = Some m ->
    mem_grow m c = Some mem ->
    mem_agree mem.
Proof.
  move => s n m c mem HST HN HGrow.
  assert (mem_agree m); first by eapply store_typed_mem_agree; eauto.
  unfold mem_grow in HGrow.
  unfold mem_agree. simpl.
  unfold mem_agree in H.
  destruct (mem_size m + c <=? page_limit)%num eqn:HLP => //.
  destruct (mem_max_opt m) eqn:HLimMax => //=.
  - destruct ((mem_size m + c <=? n0)%num) eqn:H1 => //.
    inversion HGrow. unfold mem_size, length_mem, memory_list.length_mem in *. simpl in *. subst. clear HGrow.
    rewrite length_is_size. rewrite size_cat.
    repeat rewrite - length_is_size. rewrite length_repeat.
    rewrite - N.div_add in H1 => //.
    apply N.leb_le in H1.
    by lias.
  - by inversion HGrow.
Qed.
    
Lemma reduce_inst_unchanged: forall s f es s' f' es',
    reduce s f es s' f' es' ->
    f.(f_inst) = f'.(f_inst).
Proof.
  move => s f es s' f' es' HReduce.
  by induction HReduce.
Qed.


Lemma set_nth_new {A} (x: A) l k y:
  k >= length l ->
  set_nth x l k y = l ++ ncons (k - length l) x [::y].
Proof.
  generalize dependent k. induction l => //=.
  - intros k Hk. rewrite set_nth_nil. f_equal. lias. 
  - intros k Hk. destruct k => //=. f_equal.
    apply IHl. lias.
Qed.

Fixpoint hholed_plug_value h v :=
  match h with
  | HH_base bef aft => HH_base (bef ++ [:: AI_const v]) aft
  | HH_label bef n es h aft => HH_label bef n es (hholed_plug_value h v) aft
  | HH_local bef n f h aft => HH_local bef n f (hholed_plug_value h v) aft
  | HH_handler bef hs h aft => HH_handler bef hs (hholed_plug_value h v) aft
  | HH_prompt bef ts hs h aft => HH_prompt bef ts hs (hholed_plug_value h v) aft
  end
.


Lemma is_const_AI_const v : is_const (AI_const v).
Proof. destruct v => //. destruct v => //. Qed.

Lemma hfilled_plug_value x v es h LI :
  hfilled x h (AI_const v :: es) LI <->
  hfilled x (hholed_plug_value h v) es LI.
Proof.
  generalize dependent LI. generalize dependent x.
  induction h; intros x LI. 
  - unfold hfilled, hfill => /=. unfold const_list. rewrite List.forallb_app => /=.
    rewrite is_const_AI_const. destruct (List.forallb is_const l) => //=.
    rewrite separate1. rewrite - cat_app. repeat rewrite catA. done.
  - simpl. unfold hfilled, hfill. fold hfill.
    destruct (const_list l) => //. unfold hfilled in IHh.
    split.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh x l2) as [IHh' _].
      rewrite Hfill in IHh'.
      specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ es) => //.
      move/eqP in IHh'; subst l2; done.
    + destruct (hfill _ (hholed_plug_value _ _) _) eqn:Hfill => //.
      destruct (IHh x l2) as [_ IHh'].
      rewrite Hfill in IHh'.
      specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ (_ :: es)) => //.
      move/eqP in IHh'; subst l2; done.
  - simpl. unfold hfilled, hfill. fold hfill.
    destruct (const_list l) => //. unfold hfilled in IHh.
    split.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh x l1) as [IHh' _].
      rewrite Hfill in IHh'.
      specialize (IHh' (eq_refl l1)).
      destruct (hfill _ _ es) => //.
      move/eqP in IHh'; subst l2; done.
    + destruct (hfill _ (hholed_plug_value _ _) _) eqn:Hfill => //.
      destruct (IHh x l1) as [_ IHh'].
      rewrite Hfill in IHh'.
      specialize (IHh' (eq_refl l1)).
      destruct (hfill _ _ (_ :: es)) => //.
      move/eqP in IHh'; subst l2; done.
  - simpl. unfold hfilled, hfill. fold hfill.
    destruct (const_list l) => //.
    destruct x as [x|  | |] => //.
    destruct (firstx_exception _ _ == _) eqn:Hclauses => //. 
    all: unfold hfilled in IHh.
    all: split.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh (Var_handler x) l2) as [IHh' _].
      rewrite Hfill in IHh'.
      specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ es) => //.
      move/eqP in IHh'; subst l3; done.
    + destruct (hfill _ (hholed_plug_value _ _) _) eqn:Hfill => //.
      destruct (IHh (Var_handler x) l2) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ (_ :: es)) => //.
      move/eqP in IHh'; subst l3; done.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh (Var_prompt_suspend t) l2) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ es) => //.
      move/eqP in IHh'; subst l3; done.
    + destruct (hfill _ (hholed_plug_value _ _) _) eqn:Hfill => //.
      destruct (IHh (Var_prompt_suspend t) l2) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ (_ :: es)) => //.
      move/eqP in IHh'; subst l3; done.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh (Var_prompt_switch t) l2) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ es) => //.
      move/eqP in IHh'; subst l3; done.
    + destruct (hfill _ (hholed_plug_value _ _) _) eqn:Hfill => //.
      destruct (IHh (Var_prompt_switch t) l2) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ (_ :: es)) => //.
      move/eqP in IHh'; subst l3; done.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh No_var l2) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ es) => //.
      move/eqP in IHh'; subst l3; done.
    + destruct (hfill _ (hholed_plug_value _ _) _) eqn:Hfill => //.
      destruct (IHh No_var l2) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ (_ :: es)) => //.
      move/eqP in IHh'; subst l3; done.
  - simpl. unfold hfilled, hfill. fold hfill.
    destruct (const_list l) => //.
    destruct x as [|x |x |] => //.
    2:destruct (firstx_continuation_suspend _ _ == _) eqn:Hclauses => //.
    3:destruct (firstx_continuation_switch _ _ == _) eqn:Hclauses => //. 
    all: unfold hfilled in IHh.
    all: split.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh (Var_handler t) l3) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l3)).
      destruct (hfill _ _ es) => //.
      move/eqP in IHh'; subst l3; done.
    + destruct (hfill _ (hholed_plug_value _ _) _) eqn:Hfill => //.
      destruct (IHh (Var_handler t) l3) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l3)).
      destruct (hfill _ _ (_ :: es)) => //.
      move/eqP in IHh'; subst l3; done.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh (Var_prompt_suspend x) l3) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l3)).
      destruct (hfill _ _ es) => //.
      move/eqP in IHh'; subst l3; done.
    + destruct (hfill _ (hholed_plug_value _ _) _) eqn:Hfill => //.
      destruct (IHh (Var_prompt_suspend x) l3) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l3)).
      destruct (hfill _ _ (_ :: es)) => //.
      move/eqP in IHh'; subst l3; done.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh (Var_prompt_switch x) l3) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l3)).
      destruct (hfill _ _ es) => //.
      move/eqP in IHh'; subst l3; done.
    + destruct (hfill _ (hholed_plug_value _ _) _) eqn:Hfill => //.
      destruct (IHh (Var_prompt_switch x) l3) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l3)).
      destruct (hfill _ _ (_ :: es)) => //.
      move/eqP in IHh'; subst l3; done.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh No_var l3) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l3)).
      destruct (hfill _ _ es) => //.
      move/eqP in IHh'; subst l3; done.
    + destruct (hfill _ (hholed_plug_value _ _) _) eqn:Hfill => //.
      destruct (IHh No_var l3) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l3)).
      destruct (hfill _ _ (_ :: es)) => //.
      move/eqP in IHh'; subst l3; done.
Qed.


Fixpoint hholed_plug_right h es :=
  match h with
  | HH_base bef aft => HH_base bef (es ++ aft)
  | HH_label bef n es' h aft => HH_label bef n es' (hholed_plug_right h es) aft
  | HH_local bef n f h aft => HH_local bef n f (hholed_plug_right h es) aft
  | HH_handler bef hs h aft => HH_handler bef hs (hholed_plug_right h es) aft
  | HH_prompt bef ts hs h aft => HH_prompt bef ts hs (hholed_plug_right h es) aft
  end
.

Lemma hfilled_app x h es1 es2 LI :
  hfilled x h (es1 ++ es2) LI <-> hfilled x (hholed_plug_right h es2) es1 LI.
Proof.
  generalize dependent LI. generalize dependent x.
  induction h; simpl; intros x LI;
    unfold hfilled, hfill; fold hfill; destruct (const_list _) => //.
  - by repeat rewrite catA.
  - unfold hfilled in IHh.
    split.
    + destruct (hfill _ _ _) eqn: Hfill => //.
      destruct (IHh x l2) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ es1) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ es1) eqn:Hfill => //.
      destruct (IHh x l2) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ (es1 ++ es2)) => //.
      move/eqP in IHh'. subst. done.
  - unfold hfilled in IHh.
    split.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh x l1) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l1)).
      destruct (hfill _ _ es1) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ es1) eqn:Hfill => //.
      destruct (IHh x l1) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l1)).
      destruct (hfill _ _ (_ ++ _)) => //.
      move/eqP in IHh'. subst. done.
  - destruct x as [x | | |] => //.
    destruct (firstx_exception _ _ == _) => //.
    all: unfold hfilled in IHh.
    all: split.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh (Var_handler x) l2) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ es1) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ es1) eqn:Hfill => //.
      destruct (IHh (Var_handler x) l2) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ (_ ++ _)) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh (Var_prompt_suspend t) l2) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ es1) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ es1) eqn:Hfill => //.
      destruct (IHh (Var_prompt_suspend t) l2) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ (_ ++ _)) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh (Var_prompt_switch t) l2) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ es1) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ es1) eqn:Hfill => //.
      destruct (IHh (Var_prompt_switch t) l2) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ (_ ++ _)) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh No_var l2) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ es1) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ es1) eqn:Hfill => //.
      destruct (IHh No_var l2) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ (_ ++ _)) => //.
      move/eqP in IHh'. subst. done.
  - destruct x as [|x |x |] => //.
    2:destruct (firstx_continuation_suspend _ _ == _) => //.
    3:destruct (firstx_continuation_switch _ _ == _) => //.
    all: unfold hfilled in IHh.
    all: split.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh (Var_handler t) l3) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l3)).
      destruct (hfill _ _ es1) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ es1) eqn:Hfill => //.
      destruct (IHh (Var_handler t) l3) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l3)).
      destruct (hfill _ _ (_ ++ _)) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh (Var_prompt_suspend x) l3) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l3)).
      destruct (hfill _ _ es1) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ es1) eqn:Hfill => //.
      destruct (IHh (Var_prompt_suspend x) l3) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l3)).
      destruct (hfill _ _ (_ ++ _)) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh (Var_prompt_switch x) l3) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l3)).
      destruct (hfill _ _ es1) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ es1) eqn:Hfill => //.
      destruct (IHh (Var_prompt_switch x) l3) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l3)).
      destruct (hfill _ _ (_ ++ _)) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ _) eqn:Hfill => //.
      destruct (IHh No_var l3) as [IHh' _].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l3)).
      destruct (hfill _ _ es1) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ es1) eqn:Hfill => //.
      destruct (IHh No_var l3) as [_ IHh'].
      rewrite Hfill in IHh'. specialize (IHh' (eq_refl l3)).
      destruct (hfill _ _ (_ ++ _)) => //.
      move/eqP in IHh'. subst. done.
Qed. 




Lemma store_extension_new_cont s cont:
  store_typing s ->
  store_extension s (new_cont s cont).
Proof.
  intros Hs.
  repeat (apply/andP; split) ; destruct s => //=.
  + rewrite take_size_cat => //.
    by apply all2_cont_extension_same. 
  + by apply all2_tab_extension_same.
  + by apply all2_mem_extension_same.
  + apply all2_glob_extension_same.
    destruct Hs as (_ & _ & _ & Hgs & _).
    rewrite List.Forall_forall in Hgs.
    intros g Hin. apply Hgs in Hin as [t Ht].
    apply AI_const_typing in Ht as (t0 & Ht0 & _).
    rewrite Ht0. done.
  + rewrite length_is_size take_size. done.
Qed.



Lemma store_extension_upd_cont s k cont tf:
  store_typing s ->
  List.nth_error (s_conts s) k = Some cont ->
  typeof_cont cont = tf -> 
  store_extension s (upd_s_cont s k (Cont_dagger tf)).
Proof.
  intros Hs Hk Hcontty.
  repeat (apply/andP; split); destruct s => //=.
  + unfold replace_nth_cont.
    simpl in Hk.
    clear- Hk Hcontty.
    generalize dependent k.
    induction s_conts; intros k Hk; first by rewrite take0.
    destruct k => //=.
    * rewrite length_is_size. rewrite drop0. rewrite take_size.
      apply/andP; split; last by apply all2_cont_extension_same.
      inversion Hk; subst. done. (* unfold cont_extension. by rewrite Hcontty. *)
    * simpl in Hk. apply/andP; split. unfold cont_extension. destruct a => //. 
      apply IHs_conts => //. 
  + by apply all2_tab_extension_same.
  + by apply all2_mem_extension_same.
  + apply all2_glob_extension_same.
    destruct Hs as (_ & _ & _ & Hgs & _).
    rewrite List.Forall_forall in Hgs.
    intros g Hin. apply Hgs in Hin as [t Ht].
    apply AI_const_typing in Ht as (t0 & Ht0 & _).
    rewrite Ht0. done.
  + rewrite length_is_size take_size. done.
Qed. 


Lemma typeof_new_cont s cont v t:
  typeof (new_cont s cont) v = Some t ->
  v = VAL_ref (VAL_ref_cont (length (s.(s_conts)))) \/ typeof s v = Some t.
Proof.
  intros Hv. 
  destruct v => //.
  - simpl in Hv. inversion Hv; by right.
  - destruct v => //.
    + simpl in Hv. inversion Hv; by right.
    + simpl in Hv. inversion Hv; by right.
    + simpl in Hv. destruct (List.nth_error _ _) eqn:Hf => //. inversion Hv.
      simpl. destruct (List.nth_error (s_conts s) f) eqn:Hf'.
      * right. erewrite nth_error_prefix in Hf; last exact Hf'.
        inversion Hf => //.
      * left. remember (s_conts s) as l. clear Heql.
        assert (f = length l) as -> => //. 
        generalize dependent f; induction l; destruct f => //=.
        -- destruct f => //. 
        -- intros Hf Hf'. f_equal. apply IHl => //.
    + simpl in Hv. inversion Hv; subst.
      simpl. by right.
Qed.

Lemma typeof_upd_cont s cont cont' k v:
  List.nth_error (s_conts s) k = Some cont ->
  typeof_cont cont = typeof_cont cont' ->
  typeof s v = typeof (upd_s_cont s k cont') v.
Proof.
  intros Hk Hconts. 
  destruct v => //.
  destruct v => //.
  simpl.
  remember (s_conts s) as l. clear Heql s.
  generalize dependent k. generalize dependent f. 
  induction l; destruct k, f => //=.
  - intros H; inversion H; subst. by rewrite Hconts.
  - intros H; inversion H; subst. by rewrite drop0.
  - intros H. apply IHl. done.
Qed.




Lemma et_const s v C t:
  typeof s v = Some t ->
  e_typing s C [::AI_const v] (Tf [::] [:: t]).
Proof.
  intros Ht. 
  destruct v; last destruct v => //.
  - apply ety_a' => //=. constructor => //. inversion Ht. apply bet_const.
  - apply ety_a' => //=. constructor => //. inversion Ht. constructor.
  - simpl in Ht. destruct (List.nth_error _ _) eqn:Hf => //. inversion Ht. eapply ety_ref.
    exact Hf. done.
  - simpl in Ht. destruct (List.nth_error _ _) eqn:Hf => //. inversion Ht.
    eapply ety_ref_cont.
    exact Hf.
    done.
  - simpl in Ht. destruct (List.nth_error _ _) eqn:He => //.
    destruct (_ == _) eqn:Htag => //. move/eqP in Htag.
    inversion Ht; subst.
    econstructor. exact He. done.
Qed. 


(* Lemma typing_core s C es t1s t2s:
  e_typing s C es (Tf t1s t2s) ->
  exists t1s' t2s', e_typing s C es (Tf t1s' t2s') /\
                 forall t1s t2s, e_typing s C es (Tf t1s t2s) ->
                            exists ts, t1s = ts ++ t1s' /\ t2s = ts ++ t2s'.
Proof.
  intros H. induction H.
  - induction H.
    all: eexists _,_ ; split; first try by constructor; constructor.
    all: try (intros t1s' t2s' Htyp; convert_et_to_bet; last by constructor).
    + apply BI_const_typing in Htyp; subst. 
      exists t1s'. split => //. by rewrite cats0.
    + apply Unop_typing in Htyp as (-> & ts & ->).
      exists ts. split => //.
    + apply Binop_typing in Htyp as (-> & ts & ->).
      exists ts; split => //. rewrite - catA. done.
    + apply Testop_typing in Htyp as (ts & -> & ->).
      exists ts. split => //.
    + apply Relop_typing in Htyp as (ts & -> & ->).
      exists ts. split => //.
    + apply Cvtop_typing in Htyp as (ts & -> & ->).
      exists ts. split => //.
    + apply Cvtop_typing in Htyp as (ts & -> & ->).
      exists ts. split => //.
    +  *)

(*
Lemma typing_twice s C es1 es2 tf1 tf2:
  e_typing s C es1 tf1 ->
  e_typing s C es1 tf2 ->
  e_typing s C es2 tf1 ->
  e_typing s C es2 tf2.
Proof.
  intros H11 H12 H21.
  induction H12.
  - induction 
      
  *)                  

(*
Lemma e_typing_replace_values s C es1 es2 ts x h LI1 LI2 tf:
  const_list es1 ->
(*  const_list es2 -> *)
  e_typing s C es1 (Tf [::] ts) ->
  e_typing s C es2 (Tf [::] ts) ->
  hfilled x h es1 LI1 ->
  hfilled x h es2 LI2 ->
  e_typing s C LI1 tf ->
  e_typing s C LI2 tf.
Proof.
  destruct tf as [t1s t2s].
  generalize dependent LI1; generalize dependent LI2; generalize dependent t1s;
    generalize dependent t2s; generalize dependent C.
  induction h; unfold hfilled, hfill; fold hfill; destruct (const_list l) eqn:Hcont => //; intros C t2s t1s LI2 LI1 Hconst1 (* Hconst2 *) Hes1 Hes2 HLI1 HLI2 Htype => //=.
  - move/eqP in HLI1; move/eqP in HLI2; subst.
    apply e_composition_typing in Htype as (ts' & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    apply ety_weakening. eapply et_composition'. exact Hleft.
    apply e_composition_typing in Hright as (ts'' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    apply ety_weakening. eapply et_composition'; last exact Hright.
    apply const_es_exists in Hconst1 as [vs1 ->].
    apply Const_list_typing in Hes1 as (tttt & Hvs1 & Htttt & Htyp1);
      simpl in Htttt; subst tttt.
    apply Const_list_typing in Hmid as (ts0 & Hvs1' & -> & Htyp1').
    rewrite Hvs1' in Hvs1.
    assert (ts0 = ts) as ->.
    { clear - Hvs1. generalize dependent ts0. induction ts => //=.
      intros ts0; destruct ts0 => //.
      intros ts0; destruct ts0 => //=.
      intros H; inversion H; subst.
      rewrite (IHts ts0) => //. }
    apply et_weakening_empty_1.
    exact Hes2.
  - destruct (hfill _ _ _) eqn:Hfill1 => //.
    destruct (hfill _ _ es2) eqn:Hfill2 => //.
    move/eqP in HLI1; move/eqP in HLI2; subst.
    apply e_composition_typing in Htype as (ts' & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    apply ety_weakening; eapply et_composition'; first exact Hleft.
    apply e_composition_typing in Hright as (ts'' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    apply ety_weakening; eapply et_composition'; last exact Hright.
    apply Label_typing in Hmid as (ts''' & ts2' & -> & Hl0 & Hmid & <-).
    apply et_weakening_empty_1. eapply ety_label. exact Hl0. 2: done.
    eapply IHh. done. (* done. *)
    eapply t_const_ignores_context; last exact Hes1. done. done.
    eapply t_const_ignores_context; last exact Hes2. done. done.
    unfold hfilled. rewrite Hfill1. done.
    unfold hfilled. rewrite Hfill2. done. done.
  - destruct (hfill _ _ _) eqn:Hfill1 => //.
    destruct (hfill _ _ es2) eqn:Hfill2 => //.
    move/eqP in HLI1; move/eqP in HLI2; subst.
    apply e_composition_typing in Htype as (ts' & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    apply ety_weakening; eapply et_composition'; first exact Hleft.
    apply e_composition_typing in Hright as (ts'' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    apply ety_weakening; eapply et_composition'; last exact Hright.
    apply Local_typing in Hmid as (ts''' & -> & Hmid & <-).
    apply et_weakening_empty_1. eapply ety_local. 2: done.
    inversion Hmid; subst.
    econstructor. exact H. done. 2: by left.
    eapply IHh. done. done.
    eapply t_const_ignores_context; last exact Hes1. a dmit. done.
    eapply t_const_ignores_context; last exact Hes2. a dmit. done.
    unfold hfilled. rewrite Hfill1. done.
    unfold hfilled. rewrite Hfill2. done. done.
  - destruct x => //.
    destruct (List.forallb _ _) => //.
    all: destruct (hfill _ _ _) eqn:Hfill1 => //.
    all: destruct (hfill _ _ es2) eqn:Hfill2 => //.
    all: move/eqP in HLI1; move/eqP in HLI2; subst.
    all: apply e_composition_typing in Htype as (ts' & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    all: apply ety_weakening; eapply et_composition'; first exact Hleft.
    all: apply e_composition_typing in Hright as (ts'' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    all: apply ety_weakening; eapply et_composition'; last exact Hright.
    all: apply Handler_typing in Hmid as (ts2' & -> & Hl0 & Hmid).
    all: apply et_weakening_empty_1.
    all: eapply ety_handler.
    all: try exact Hl0. 
    all: eapply IHh => //. 
    all: try by eapply t_const_ignores_context; last exact Hes1. 
    all: try by eapply t_const_ignores_context; last exact Hes2. 
    all: try by unfold hfilled; rewrite Hfill1. 
    all: try by unfold hfilled; rewrite Hfill2.
    done. done.
A  dmitted.   *)

Lemma e_typing_plug_value s C es1 es2 ts x h LI1 LI2 tf:
  const_list es1 ->
  const_list es2 ->
  e_typing s C es1 (Tf [::] ts) ->
  e_typing s C es2 (Tf [::] ts) ->
  hfilled x h es1 LI1 ->
  hfilled x h es2 LI2 ->
  e_typing s C LI1 tf ->
  e_typing s C LI2 tf.
Proof.
  destruct tf as [t1s t2s].
  generalize dependent x.
  generalize dependent LI1; generalize dependent LI2; generalize dependent t1s;
    generalize dependent t2s; generalize dependent C.
  induction h; unfold hfilled, hfill; fold hfill; destruct (const_list l) eqn:Hcont => //; intros C t2s t1s LI2 LI1 x Hconst1 Hconst2 Hes1 Hes2 HLI1 HLI2 Htype => //=.
  - move/eqP in HLI1; move/eqP in HLI2; subst.
    apply e_composition_typing in Htype as (ts' & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    apply ety_weakening. eapply et_composition'. exact Hleft.
    apply e_composition_typing in Hright as (ts'' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    apply ety_weakening. eapply et_composition'; last exact Hright.
    apply const_es_exists in Hconst1 as [vs1 ->].
    apply Const_list_typing in Hes1 as (tttt & Hvs1 & Htttt & Htyp1);
      simpl in Htttt; subst tttt.
    apply Const_list_typing in Hmid as (ts0 & Hvs1' & -> & Htyp1').
    rewrite Hvs1' in Hvs1.
    assert (ts0 = ts) as ->.
    { clear - Hvs1. generalize dependent ts0. induction ts => //=.
      intros ts0; destruct ts0 => //.
      intros ts0; destruct ts0 => //=.
      intros H; inversion H; subst.
      rewrite (IHts ts0) => //. }
    apply et_weakening_empty_1.
    exact Hes2.
  - destruct (hfill _ _ _) eqn:Hfill1 => //.
    destruct (hfill _ _ es2) eqn:Hfill2 => //.
    move/eqP in HLI1; move/eqP in HLI2; subst.
    apply e_composition_typing in Htype as (ts' & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    apply ety_weakening; eapply et_composition'; first exact Hleft.
    apply e_composition_typing in Hright as (ts'' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    apply ety_weakening; eapply et_composition'; last exact Hright.
    apply Label_typing in Hmid as (ts''' & ts2' & -> & Hl0 & Hmid & <-).
    apply et_weakening_empty_1. eapply ety_label. exact Hl0. 2: done.
    eapply IHh. done. done.
    eapply t_const_ignores_context; last exact Hes1. done. (* done. *)
    eapply t_const_ignores_context; last exact Hes2. done. (* done. *)
    unfold hfilled. instantiate (2 := x). rewrite Hfill1. done.
    unfold hfilled. rewrite Hfill2. done. done.
  - destruct (hfill _ _ _) eqn:Hfill1 => //.
    destruct (hfill _ _ es2) eqn:Hfill2 => //.
    move/eqP in HLI1; move/eqP in HLI2; subst.
    apply e_composition_typing in Htype as (ts' & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    apply ety_weakening; eapply et_composition'; first exact Hleft.
    apply e_composition_typing in Hright as (ts'' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    apply ety_weakening; eapply et_composition'; last exact Hright.
    apply Local_typing in Hmid as (ts''' & -> & Hmid & <-).
    apply et_weakening_empty_1. eapply ety_local. 2: done.
    inversion Hmid; subst.
    econstructor. exact H. done. 2: by left.
    eapply IHh. done. done.
    eapply t_const_ignores_context; last exact Hes1. done.
    eapply t_const_ignores_context; last exact Hes2.  done.
    unfold hfilled. instantiate (2 := x).
    rewrite Hfill1. done.
    unfold hfilled. rewrite Hfill2. done. done.
  - destruct x as [x | | |] => //.
    destruct (firstx_exception _ _ == _) => //.
    all: destruct (hfill _ _ _) eqn:Hfill1 => //.
    all: destruct (hfill _ _ es2) eqn:Hfill2 => //.
    all: move/eqP in HLI1; move/eqP in HLI2; subst.
    all: apply e_composition_typing in Htype as (ts' & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    all: apply ety_weakening; eapply et_composition'; first exact Hleft.
    all: apply e_composition_typing in Hright as (ts'' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    all: apply ety_weakening; eapply et_composition'; last exact Hright.
    all: apply Handler_typing in Hmid as ( ts2' &  -> & Hl0 & Hmid).
    all: apply et_weakening_empty_1.
    all: eapply ety_handler.
    all: try exact Hl0. 
    all: eapply IHh => //. 
    all: try by eapply t_const_ignores_context; last exact Hes1. 
    all: try by eapply t_const_ignores_context; last exact Hes2.
    all: try by instantiate (2 := Var_handler x); unfold hfilled; rewrite Hfill1.
    all: try by instantiate (2 := Var_prompt_switch t); unfold hfilled; rewrite Hfill1.
    all: try by instantiate (2 := Var_prompt_suspend t); unfold hfilled; rewrite Hfill1.

    all: try by instantiate (2 := No_var); unfold hfilled; rewrite Hfill1.
    all: try by unfold hfilled; rewrite Hfill2.
    done. done. done. done.
  - destruct x as [|x |x | ] => //.
    2:destruct (firstx_continuation_suspend _ _ == _) => //.
    3:destruct (firstx_continuation_switch _ _ == _) => //.
    all: destruct (hfill _ _ _) eqn:Hfill1 => //.
    all: destruct (hfill _ _ es2) eqn:Hfill2 => //.
    all: move/eqP in HLI1; move/eqP in HLI2; subst.
    all: apply e_composition_typing in Htype as (ts' & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    all: apply ety_weakening; eapply et_composition'; first exact Hleft.
    all: apply e_composition_typing in Hright as (ts'' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    all: apply ety_weakening; eapply et_composition'; last exact Hright.
    all: apply Prompt_typing in Hmid as (  -> & Hl0 & Hmid).
    all: apply et_weakening_empty_1.
    all: eapply ety_prompt.
    all: try exact Hl0. 
    all: eapply IHh => //. 
    all: try by eapply t_const_ignores_context; last exact Hes1. 
    all: try by eapply t_const_ignores_context; last exact Hes2.
    all: try by instantiate (2 := Var_handler t); unfold hfilled; rewrite Hfill1.
    all: try by instantiate (2 := Var_prompt_suspend x); unfold hfilled; rewrite Hfill1.
    all: try by instantiate (2 := Var_prompt_switch x); unfold hfilled; rewrite Hfill1.
    all: try by instantiate (2 := No_var); unfold hfilled; rewrite Hfill1.
    all: try by unfold hfilled; rewrite Hfill2.
    done. done. done. done.
Qed.


Lemma e_typing_plug_throw s C es1 (* es2 *) ts x h LI1 LI2 tf a t:
  const_list es1 ->
(*  const_list es2 -> *)
  e_typing s C es1 (Tf [::] ts) ->
  e_typing s C ((* es2 ++ *) [:: AI_ref_exn a t; AI_basic BI_throw_ref]) (Tf [::] ts) ->
  hfilled x h es1 LI1 ->
  hfilled x h ((* es2 ++ *) [:: AI_ref_exn a t; AI_basic BI_throw_ref]) LI2 ->
  e_typing s C LI1 tf ->
  e_typing s C LI2 tf.
Proof.
  destruct tf as [t1s t2s]. generalize dependent x.
  generalize dependent LI1; generalize dependent LI2; generalize dependent t1s;
    generalize dependent t2s; generalize dependent C.
  induction h; unfold hfilled, hfill; fold hfill; destruct (const_list l) eqn:Hcont => //; intros C t2s t1s LI2 LI1 x Hconst1 (* Hconst2 *) Hes1 Hes2 HLI1 HLI2 Htype => //=.
  - move/eqP in HLI1; move/eqP in HLI2; subst.
    apply e_composition_typing in Htype as (ts' & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    apply ety_weakening. eapply et_composition'. exact Hleft.
    apply e_composition_typing in Hright as (ts'' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    apply ety_weakening. eapply et_composition'; last exact Hright.
    apply const_es_exists in Hconst1 as [vs1 ->].
    apply Const_list_typing in Hes1 as (tttt & Hvs1 & Htttt & Htyp1);
      simpl in Htttt; subst tttt.
    apply Const_list_typing in Hmid as (ts0 & Hvs1' & -> & Htyp1').
    rewrite Hvs1' in Hvs1.
    assert (ts0 = ts) as ->.
    { clear - Hvs1. generalize dependent ts0. induction ts => //=.
      intros ts0; destruct ts0 => //.
      intros ts0; destruct ts0 => //=.
      intros H; inversion H; subst.
      rewrite (IHts ts0) => //. }
    apply et_weakening_empty_1.
    exact Hes2.
(*    eapply et_composition'. exact Hes2.  *)
  - destruct (hfill _ _ _) eqn:Hfill1 => //.
    destruct (hfill _ _ [:: _ ; _]) eqn:Hfill2 => //.
    move/eqP in HLI1; move/eqP in HLI2; subst.
(*    apply e_composition_typing in Hes2 as (ts0 & tx & ty & t3s & ? & -> & Hes2 & Hexnthrow).
    destruct ts0 => //. destruct tx => //. *)
    rewrite separate1 in Hes2 (* Hexnthrow *).
    apply e_composition_typing in Hes2 (* Hexnthrow *) as (ts0' & tx' & ty' & t3s' & ? & -> & Hexn & Hthrow).
    destruct ts0' => //. destruct tx' => //. 
    apply AI_ref_exn_typing in Hexn as (exn & Hexn & Hetag & ->). 
    apply et_to_bet in Hthrow; last by constructor.
    apply Throw_ref_typing in Hthrow as (tz & Htypes).
(*    destruct tz; last by destruct tz. *)
    apply concat_cancel_last in Htypes as [<- _]. 
    apply e_composition_typing in Htype as (ts' & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    apply ety_weakening; eapply et_composition'; first exact Hleft.
    apply e_composition_typing in Hright as (ts'' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    apply ety_weakening; eapply et_composition'; last exact Hright.
    apply Label_typing in Hmid as (ts''' & ts2' & -> & Hl0 & Hmid & <-).
    apply et_weakening_empty_1. eapply ety_label. exact Hl0. 2: done.
    eapply IHh. done. (* done. *)
    eapply t_const_ignores_context; last exact Hes1. done. (* done. *)
(*    eapply et_composition'.
    eapply t_const_ignores_context; last exact Hes2. done. (* done. *)

    simpl.
    apply ety_weakening.  *)
    rewrite (separate1 (AI_ref_exn a t)).
    eapply et_composition'.
(*    instantiate (1 := tz ++ _).
    apply et_weakening_empty_1. *)
    eapply ety_ref_exn. exact Hexn.
    exact Hetag.
    apply ety_a'. constructor => //.
    rewrite - (cat0s [:: T_ref _]).
    apply bet_throw_ref. unfold hfilled.
    instantiate (2 := x).
    rewrite Hfill1. done. 
    unfold hfilled. rewrite Hfill2. done. done.
  - destruct (hfill _ _ _) eqn:Hfill1 => //.
    destruct (hfill _ _ [::_;_]) eqn:Hfill2 => //.
    move/eqP in HLI1; move/eqP in HLI2; subst.
    apply e_composition_typing in Htype as (ts' & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    apply ety_weakening; eapply et_composition'; first exact Hleft.
    apply e_composition_typing in Hright as (ts'' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    apply ety_weakening; eapply et_composition'; last exact Hright.
    apply Local_typing in Hmid as (ts''' & -> & Hmid & <-).
    apply et_weakening_empty_1. eapply ety_local. 2: done.
    inversion Hmid; subst.
    econstructor. exact H. done. 2: by left.
    eapply IHh. done. (* done. *)
    eapply t_const_ignores_context; last exact Hes1. done. 
(*    apply e_composition_typing in Hes2 as (ts0 & tx & ty & t3s & ? & -> & Hes2 & Hexnthrow).
    destruct ts0 => //. destruct tx => //. *)
    rewrite separate1 in Hes2 (* Hexnthrow *).
    apply e_composition_typing in Hes2 (* Hexnthrow *) as (ts0' & tx' & ty' & t3s' & ? & -> & Hexn & Hthrow).
    destruct ts0' => //. destruct tx' => //. 
    apply AI_ref_exn_typing in Hexn as (exn & Hexn & Hetag & ->). 
    apply et_to_bet in Hthrow; last by constructor.
    apply Throw_ref_typing in Hthrow as (tz & Htypes).
    apply concat_cancel_last in Htypes as [-> _].
(*    eapply et_composition'.
    eapply t_const_ignores_context; last exact Hes2. done.
    simpl. apply ety_weakening. *)
    apply et_weakening_empty_1.
    rewrite separate1.
    eapply et_composition'.
(*    instantiate (1 := tz ++ _). apply et_weakening_empty_1. *)
    eapply ety_ref_exn. exact Hexn. exact Hetag.
    apply ety_a'. constructor => //.
    rewrite - (cat0s [:: T_ref _]).
    constructor. 
    unfold hfilled.
    instantiate (2 := x).
    rewrite Hfill1. done.
    unfold hfilled. rewrite Hfill2. done. done.
  - destruct x as [x| | |] => //.
    destruct (firstx_exception _ _ == _) => //.
    all: destruct (hfill _ _ _) eqn:Hfill1 => //.
    all: destruct (hfill _ _ [::_;_]) eqn:Hfill2 => //.
    all: move/eqP in HLI1; move/eqP in HLI2; subst.
    all: apply e_composition_typing in Htype as (ts' & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    all: apply ety_weakening; eapply et_composition'; first exact Hleft.
    all: apply e_composition_typing in Hright as (ts'' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    all: apply ety_weakening; eapply et_composition'; last exact Hright.
    all: apply Handler_typing in Hmid as ( ts2' &  -> & Hl0 & Hmid).
    all: apply et_weakening_empty_1.
    all: eapply ety_handler.
    all: try exact Hl0. 
    all: eapply IHh => //.
    all: try by instantiate (2 := Var_handler x); unfold hfilled; rewrite Hfill1.
    all: try by instantiate (2 := Var_prompt_switch t0); unfold hfilled; rewrite Hfill1.
    all: try by instantiate (2 := Var_prompt_suspend t0); unfold hfilled; rewrite Hfill1.
    all: try by instantiate (2 := No_var); unfold hfilled; rewrite Hfill1.
    all: try by unfold hfilled; rewrite Hfill2.
    all: try by eapply t_const_ignores_context; last exact Hes1.
    all: try done.
  - destruct x as [|x|x  |] => //.
    2:destruct (firstx_continuation_suspend _ _ == _) => //.
    3:destruct (firstx_continuation_switch _ _ == _) => //.
    all: destruct (hfill _ _ _) eqn:Hfill1 => //.
    all: destruct (hfill _ _ [::_;_]) eqn:Hfill2 => //.
    all: move/eqP in HLI1; move/eqP in HLI2; subst.
    all: apply e_composition_typing in Htype as (ts' & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    all: apply ety_weakening; eapply et_composition'; first exact Hleft.
    all: apply e_composition_typing in Hright as (ts'' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    all: apply ety_weakening; eapply et_composition'; last exact Hright.
    all: apply Prompt_typing in Hmid as (   -> & Hl0 & Hmid).
    all: apply et_weakening_empty_1.
    all: eapply ety_prompt.
    all: try exact Hl0. 
    all: eapply IHh => //.
    all: try by instantiate (2 := Var_prompt_suspend x); unfold hfilled; rewrite Hfill1.
    all: try by instantiate (2 := Var_prompt_switch x); unfold hfilled; rewrite Hfill1.
    all: try by instantiate (2 := Var_handler t0); unfold hfilled; rewrite Hfill1.
    all: try by instantiate (2 := No_var); unfold hfilled; rewrite Hfill1.
    all: try by unfold hfilled; rewrite Hfill2.
    all: try by eapply t_const_ignores_context; last exact Hes1.
    all: try done.
    all: rewrite separate1 in Hes2 (* Hexnthrow *).
    all: apply e_composition_typing in Hes2 (* Hexnthrow *) as (ts0' & tx' & ty' & t3s' & ? & -> & Hexn & Hthrow).
    all: destruct ts0' => //.
    all: destruct tx' => //. 
    all: apply AI_ref_exn_typing in Hexn as (exn & Hexn & Hetag & ->). 
    all: apply et_to_bet in Hthrow; last by constructor.
    all: apply Throw_ref_typing in Hthrow as (tz & Htypes).
    all: apply concat_cancel_last in Htypes as [-> _].
    all: apply et_weakening_empty_1.
(*    all: eapply et_composition'.
    all: try by eapply t_const_ignores_context; last exact Hes2.
    all: simpl.
    all: apply ety_weakening. *)
    all: rewrite separate1.
    all: eapply et_composition'.
(*    1,3: instantiate (1 := tz ++ _).
    all: try apply et_weakening_empty_1. *)
    all: try eapply ety_ref_exn.
    all: try exact Hexn.
    all: try exact Hetag.
    all: eapply ety_a'; first by constructor.
    all: rewrite - (cat0s [:: T_ref _]).
    all: apply bet_throw_ref.
Qed. 

(*
Lemma e_typing_plug_value v1 v2 s x h LI1 LI2 C tf:
  typeof s v1 = typeof s v2 ->
  hfilled x h [:: AI_const v1] LI1 ->
  hfilled x h [:: AI_const v2] LI2 ->
  e_typing s C LI1 tf ->
  e_typing s C LI2 tf.
Proof.
  destruct tf as [t1s t2s].
  generalize dependent LI1. generalize dependent LI2. generalize dependent t1s.
  generalize dependent t2s. generalize dependent C. 
  induction h; unfold hfilled, hfill; fold hfill; destruct (const_list _) eqn:Hconst => //; intros C t2s t1s LI2 LI1 Htypes HLI1 HLI2 Htype => //=.
  - move/eqP in HLI1; move/eqP in HLI2; subst.
    apply e_composition_typing in Htype as (ts & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    apply ety_weakening. eapply et_composition'. exact Hleft.
    rewrite separate1 in Hright.
    apply e_composition_typing in Hright as (ts' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    apply ety_weakening. rewrite separate1.  eapply et_composition'; last exact Hright.
    apply AI_const_typing in Hmid as (t & Ht & -> & Hmid).
    rewrite Htypes in Ht. apply et_weakening_empty_1.
    apply et_const. done.
  - destruct (hfill _ _ _) eqn:Hfill1 => //.
    destruct (hfill _ _ [::AI_const v2]) eqn:Hfill2 => //.
    move/eqP in HLI1; move/eqP in HLI2; subst.
    apply e_composition_typing in Htype as (ts & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    apply ety_weakening. eapply et_composition'. exact Hleft.
    apply e_composition_typing in Hright as (ts' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    apply ety_weakening. eapply et_composition'; last exact Hright.
    apply Label_typing in Hmid as (ts'' & ts2' & -> & Hl0 & Hmid & <-).
    apply et_weakening_empty_1. eapply ety_label. exact Hl0. 2: done.
    eapply IHh. done. unfold hfilled. rewrite Hfill1. done.
    unfold hfilled. rewrite Hfill2. done. done.
  - destruct (hfill _ _ _) eqn:Hfill1 => //.
    destruct (hfill _ _ [::AI_const v2]) eqn:Hfill2 => //.
    move/eqP in HLI1; move/eqP in HLI2; subst.
    apply e_composition_typing in Htype as (ts & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    apply ety_weakening. eapply et_composition'. exact Hleft.
    apply e_composition_typing in Hright as (ts' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    apply ety_weakening. eapply et_composition'; last exact Hright.
    apply Local_typing in Hmid as (ts'' & -> & Hmid & <-).
    apply et_weakening_empty_1. eapply ety_local. 2: done.
    inversion Hmid; subst.
    econstructor. exact H. done. 2: by left.
    eapply IHh. done. unfold hfilled. rewrite Hfill1. done.
    unfold hfilled. rewrite Hfill2. done. done.
  - destruct (List.forallb _ _) => //.
    destruct (hfill _ _ _) eqn:Hfill1 => //.
    destruct (hfill _ _ [::AI_const v2]) eqn:Hfill2 => //.
    move/eqP in HLI1; move/eqP in HLI2; subst.
    apply e_composition_typing in Htype as (ts & t1s' & t2s' & t3s & -> & -> & Hleft & Hright).
    apply ety_weakening. eapply et_composition'. exact Hleft.
    apply e_composition_typing in Hright as (ts' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Hright).
    apply ety_weakening. eapply et_composition'; last exact Hright.
    apply Handler_typing in Hmid as (ts2' & -> & Hl0 & Hmid).
    apply et_weakening_empty_1. eapply ety_handler. exact Hl0. 
    eapply IHh. done. unfold hfilled. rewrite Hfill1. done.
    unfold hfilled. rewrite Hfill2. done. done.
Qed. *)

Lemma hfilled_change es2 x y h es1 LI1:
  hfilled x h es1 LI1 -> y = No_var \/ y = x ->
  exists LI2, hfilled y h es2 LI2.
Proof.
  generalize dependent LI1. generalize dependent x. generalize dependent y.
  induction h; intros y x LI1; unfold hfilled, hfill; fold hfill; destruct (const_list _) => //.
  - intros _; eexists _; done.
  - intros Hfill Hy. unfold hfilled in IHh.
    specialize (IHh y x). destruct (hfill _ _ _) => //.
    destruct (IHh l2 (eq_refl l2)) as [LI2 Hfill2]. done.
    destruct (hfill _ _ es2) => //. eexists; done.
  - unfold hfilled in IHh.
    specialize (IHh y x).
    destruct (hfill _ _ _) => //.
    intros Hfill Hy.
    destruct (IHh l1 (eq_refl l1)) as [LI2 Hfill2].
    destruct Hy as [-> | ->]; (by left + right). 
    destruct (hfill _ _ es2) => //. eexists; done.
  - intros Hfill Hy. destruct x as [x | | |] => //.
    destruct (firstx_exception _ _ == _) eqn:Hx => //.
    all: unfold hfilled in IHh.
    specialize (IHh y (Var_handler x)).
    2: specialize (IHh y (Var_prompt_suspend t)).
    3: specialize (IHh y (Var_prompt_switch t)).
    4: specialize (IHh y No_var).
    all: destruct (hfill _ _ _) => //.
    all: destruct (IHh l2 (eq_refl l2)) as [LI2 Hfill2].
    all: try done.
    all: destruct Hy as [-> | ->].
    2: rewrite Hx. 
    all: destruct (hfill _ _ es2) => //.
    all: by eexists.
  - intros Hfill Hy. destruct x as [|x |x |] => //.
    2:destruct (firstx_continuation_suspend _ _ == _) eqn:Hx => //.
    3:destruct (firstx_continuation_switch _ _ == _) eqn:Hx => //.
    all: unfold hfilled in IHh.
    specialize (IHh y (Var_handler t)).
    2: specialize (IHh y (Var_prompt_suspend x)).
    3: specialize (IHh y (Var_prompt_switch x)).
    4: specialize (IHh y No_var).
    all: destruct (hfill _ _ _) => //.
    all: destruct (IHh l3 (eq_refl l3)) as [LI2 Hfill2].
    all: try done.
    all: destruct Hy as [-> | ->].
    all: try rewrite Hx.
    all: destruct (hfill _ _ es2) => //.
    all: by eexists.
Qed. 
    

  
(*
Lemma e_typing_plug_values vs1 vs2 s x h LI1 LI2 C tf:
  map (typeof s) vs1 = map (typeof s) vs2 ->
  hfilled x h (v_to_e_list vs1) LI1 ->
  hfilled x h (v_to_e_list vs2) LI2 ->
  e_typing s C LI1 tf ->
  e_typing s C LI2 tf.
Proof.
  generalize dependent h. generalize dependent LI1. generalize dependent LI2.
  generalize dependent vs2.
  induction vs1; destruct vs2; intros LI2 LI1 h Hvs HLI1 HLI2 Htype => //=.
  - unfold hfilled in HLI1, HLI2.
    destruct (hfill _ _ _) => //. move/eqP in HLI1; move/eqP in HLI2; subst l LI2.
    done.
  - destruct (hfilled_change (v_to_e_list (v :: vs1)) HLI1) as [LI3 HLI3].

    simpl in HLI1. rewrite separate1 in HLI1. 
    apply hfilled_app in HLI1. 
    simpl in HLI3. rewrite separate1 in HLI3.
    apply hfilled_app in HLI3 as HLI3'.
    inversion Hvs.
    specialize (e_typing_plug_value H0 HLI1 HLI3' Htype) as Htype'.

    simpl in HLI3. apply hfilled_plug_value in HLI3.
    simpl in HLI2. apply hfilled_plug_value in HLI2.
    eapply IHvs1. exact H1. exact HLI3. exact HLI2. exact Htype'.
Qed. 
*)
     
    
    
(*
Lemma typeof_default_vals s ts:
  map (typeof s) (default_vals ts) = map Some ts.
Proof.
  induction ts => //=.
  rewrite IHts => //=. f_equal.
  destruct a => //=. destruct n => //.
  destruct r => //=.
Qed. 
 *)



Lemma c_typing_new_cont s cont' cont:
  store_typing s ->
  c_typing s cont ->
  c_typing (new_cont s cont') cont.
Proof.
  intros Hs Hcont.
  eapply store_extension_c_typing.
  exact Hs. apply store_extension_new_cont. done. done.
Qed. 
  
Lemma c_typing_upd_cont s cont1 k cont tf:
  store_typing s ->
  List.nth_error (s_conts s) k = Some cont1 ->
  typeof_cont cont1 = tf -> 
  c_typing s cont ->
  c_typing (upd_s_cont s k (Cont_dagger tf)) cont.
Proof.
  intros Hs Hk <- Hcont.
  eapply store_extension_c_typing.
  exact Hs. eapply store_extension_upd_cont. done. exact Hk. done. done.
Qed. 
    


Lemma store_typing_new_cont s cont:
  store_typing s ->
  c_typing (new_cont s cont) cont -> 
  store_typing (new_cont s cont).
Proof.
  intros Hs Hcont.
  remember Hs as Hs'. clear HeqHs'.
  specialize (store_extension_new_cont cont Hs) as Hsext.
  unfold store_typing. unfold store_typing in Hs.
  destruct s => //=. 
  destruct Hs as (Hcl & Htabs & Hmems & Hgs & Hconts & Hexns).
  repeat split => //.
  + eapply List.Forall_impl; last exact Hcl.
    intros a [cl Hcltype].
    exists cl. eapply store_extension_cl_typing. exact Hsext. exact Hcltype.
  + eapply List.Forall_impl; last exact Hgs.
    intros g Hg. eapply store_extension_glob_sound.
    exact Hsext. exact Hg.
  + apply List.Forall_app. split; last by constructor.
    eapply List.Forall_impl; last exact Hconts.
    intros c Hc.
    apply c_typing_new_cont. done. done.
  + eapply List.Forall_impl; last exact Hexns.
    intros exn (t & Hexn & Htags). exists t.
    split => //. eapply store_extension_e_typing.
    exact Hs'. exact Hsext. exact Hexn.
Qed. 


Lemma forall_replace_cont P s_conts cont' k cont:
  List.nth_error s_conts k = Some cont ->
  List.Forall P s_conts ->
  P cont' ->
  List.Forall P (replace_nth_cont s_conts k cont').
Proof.
  generalize dependent k.
  induction s_conts; destruct k => //=.
  - intros Ha HP Hcont'. inversion Ha; subst a.
    constructor => //. simpl. rewrite drop0. by inversion HP.
  - intros Hk HP Hcont'. inversion HP; subst. constructor => //.
    apply IHs_conts => //.
Qed. 

Lemma store_typing_upd_cont s k cont tf:
  store_typing s ->
  List.nth_error (s_conts s) k = Some cont ->
  typeof_cont cont = tf ->
  store_typing (upd_s_cont s k (Cont_dagger tf)).
Proof.
  intros Hs Hk Hcontty.
  remember Hs as Hs'. clear HeqHs'.
  specialize (store_extension_upd_cont Hs Hk Hcontty) as H.
  unfold store_typing. unfold store_typing in Hs.
  destruct s => //=. 
  destruct Hs as (Hcl & Htabs & Hmems & Hgs & Hconts & Hexns).
  repeat split => //.
  + eapply List.Forall_impl; last exact Hcl.
    intros a [cl Hcltype].
    exists cl. eapply store_extension_cl_typing. exact H. done.
  + eapply List.Forall_impl; last exact Hgs.
    intros g Hg. eapply store_extension_glob_sound.
    exact H. exact Hg.
  + eapply forall_replace_cont. eauto.
    eapply List.Forall_impl; last exact Hconts.
    intros c Hc. eapply c_typing_upd_cont. done. eauto.
    done. done. constructor.
  + eapply List.Forall_impl; last exact Hexns.
    intros exn (t & Hexn & Htags). exists t.
    split => //. eapply store_extension_e_typing.
    exact Hs'. exact H. exact Hexn.
Qed. 


Lemma all2_trans {A} (f: A -> A -> bool) (l1: list A) l2 l3:
  (forall x1 x2 x3, f x1 x2 -> f x2 x3 -> f x1 x3) ->
  all2 f l1 l2 -> all2 f l2 l3 -> all2 f l1 l3.
Proof.
  move: l2 l3. induction l1; intros l2 l3 Hf H1 H2; destruct l2 => //.
  destruct l3 => //. apply/andP.
  move/andP in H1. move/andP in H2.
  destruct H2 as [Ha2 H2]. destruct H1 as [Ha1 H1].
  split; first eapply Hf. exact Ha1. exact Ha2.
  eapply IHl1. exact Hf. exact H1. exact H2.
Qed.

Lemma all2_trans_prefix {A} (f: A -> A -> bool) (l1: list A) l2 l3:
  (forall x1 x2 x3, f x1 x2 -> f x2 x3 -> f x1 x3) ->
  all2 f l1 (take (length l1) l2) -> all2 f l2 (take (length l2) l3) -> all2 f l1 (take (length l1) l3).
Proof.
  move: l2 l3. induction l1; intros l2 l3 Hf H1 H2; destruct l2, l3 => //.
  apply/andP.
  move/andP in H1. move/andP in H2.
  destruct H2 as [Ha2 H2]. destruct H1 as [Ha1 H1].
  split; first eapply Hf. exact Ha1. exact Ha2.
  eapply IHl1. exact Hf. exact H1. exact H2.
Qed.

Lemma all2_trans_variation {A} (f1: A -> A -> bool) (f2: A -> A -> bool) (l1: list A) l2 l3:
  (forall x1 x2 x3, List.In x3 l3 -> f1 x1 x2 -> f2 x2 x3 -> f1 x1 x3) ->
  all2 f1 l1 l2 -> all2 f2 l2 l3 -> all2 f1 l1 l3.
Proof.
  move: l2 l3. induction l1; intros l2 l3 Hf H1 H2; destruct l2 => //.
  destruct l3 => //. apply/andP.
  move/andP in H1. move/andP in H2.
  destruct H2 as [Ha2 H2]. destruct H1 as [Ha1 H1].
  split; first eapply Hf. by left. exact Ha1. exact Ha2.
  eapply IHl1. intros. eapply Hf => //. by right. exact H0. exact H3. exact H1. exact H2.
Qed.

(* Not true *) (* Lemma glob_extension_extension_reverse: forall s s',
    store_extension s s' ->
    all2 (glob_extension s') (s_globals s) (s_globals s') ->
    all2 (glob_extension s) (s_globals s) (s_globals s').
Proof.
  intros s s' HST Hall.
  apply all2_Forall2.
  eapply List.Forall2_impl; last by apply all2_Forall2 in Hall; exact Hall.
  intros g g' Hext. simpl in Hext.
  unfold glob_extension. unfold glob_extension in Hext.
  destruct (g_mut g) => //. destruct (g_mut g') => //.
  destruct (typeof_extension (g_val g) HST) as [Heq0 | (Hcorrupt & ft & Hg')].
  - destruct (typeof_extension (g_val g') HST) as [-> | (Hcorrupt  & ft & Hg')] => //.
    by rewrite Heq0.
    move/andP in Hext. destruct Hext as [Heq Habs].
    move/eqP in Heq. 
    apply/andP. split; last by rewrite Heq0.
    rewrite Heq in Habs. rewrite Hcorrupt in Habs.
    move/andP in Hext. destruct Hext as [-> ?] => //.
  - rewrite Hcorrupt in Hext. move/andP in Hext. destruct Hext as [_ ?] => //.
Qed.  *)

Lemma list_prefix_equiv (l1: list exception) l2 :
  (l1 = take (length l1) l2) <-> exists l', l2 = l1 ++ l'.
Proof.
  split.
  - intros H. (* ; move/eqP in H. *)
    exists (drop (length l1) l2). rewrite -> H at 1. rewrite cat_take_drop. done.
  - intros [l' ->].
    rewrite length_is_size take_size_cat. done. done.
Qed. 


Lemma store_extension_trans s1 s2 s3:
  (forall x : global, List.In x (s_globals s3) -> typeof s1 (g_val x) <> None) ->
  store_extension s1 s2 ->
  store_extension s2 s3 ->
  store_extension s1 s3.
Proof.
  unfold store_extension.
  intros Hcorrupt H12 H23; remove_bools_options.
  apply list_prefix_equiv in H7 as [additions2 Hexns2].
  apply list_prefix_equiv in H0 as [additions3 Hexns3].
  rewrite H12 H6 H5 H.
  repeat (apply/andP; split).
  - done.
  - done.
  - eapply all2_trans_prefix; try exact H4; try exact H11.
    intros c1 c2 c3 Hc1 Hc2.
    destruct c2, c3 => /=; simpl in Hc1, Hc2.
    + move/eqP in Hc1; subst c1. done.
    + move/eqP in Hc1; subst c1. move/eqP in Hc2; subst f. done.
    + move/eqP in Hc2; done.
    + move/eqP in Hc2; subst f. done.
  - eapply all2_trans; try exact H10; try exact H3.
    intros t1 t2 t3 Ht1 Ht2. move/andP in Ht1. move/andP in Ht2.
    destruct Ht1. destruct Ht2. move/eqP in H7. move/eqP in H14.
    apply/andP. split; first lias. by rewrite H7 H14.
  - eapply all2_trans; try exact H9; try exact H2.
    intros m1 m2 m3 Hm1 Hm2. move/andP in Hm1. move/andP in Hm2.
    destruct Hm1. destruct Hm2. move/eqP in H14. move/eqP in H7.
    apply/andP. apply N.leb_le in H13. apply N.leb_le in H0.
    split; first by apply N.leb_le; lias. by rewrite H7 H14.
  - eapply all2_trans_variation; try exact H8; try exact H1.
    unfold glob_extension. intros g1 g2 g3 Hin Hg1 Hg2.
    destruct (g_mut g1), (g_mut g2), (g_mut g3); remove_bools_options => //.
    + rewrite H14 H7. apply/andP => //.
    + apply/andP; split => //.
      destruct (@typeof_extension s1 s2 (g_val g2)), (@typeof_extension s1 s2 (g_val g3)).
      all: try by repeat (apply/andP; split => //); try rewrite H12; try rewrite H6; try (apply/eqP; apply list_prefix_equiv; eexists; exact Hexns2).
      * rewrite H13 H15 H0 H16. done.
      * destruct H16 as [[H16 _] | [H16 _]]; exfalso;
          eapply Hcorrupt; try exact Hin; try exact H16.
      * destruct H15 as [[H15 _] | [H15 _]]; rewrite H13 H15 in H14; done.
      * destruct H15 as [[H15 _] | [H15 _]];
          destruct H16 as [[H16 _] | [H16 _]];
          rewrite H13 H15 H16; done.
  - apply/eqP. apply list_prefix_equiv.  eexists. rewrite Hexns3 Hexns2.
    rewrite -catA. done.
Qed.        
  
Lemma typeof_upd_cont_corrupt s k cont v:
  typeof (upd_s_cont s k cont) v = None ->
  typeof s v = None.
Proof.
  destruct v => //. destruct v => //. destruct s => /=.
  generalize dependent k. generalize dependent f.
  induction s_conts; intros f k Hcorrupt => //.
  - destruct f => //. 
  - destruct k, f => //=.
    + simpl in Hcorrupt. rewrite drop0 in Hcorrupt. done.
    + simpl in Hcorrupt. eapply IHs_conts => //.
      exact Hcorrupt.
Qed.


Ltac inst_typing_equal i C H :=
  let loc := fresh "loc" in
  let lab := fresh "lab" in
  let ret := fresh "ret" in
  destruct C as [????? loc lab ret ??];
  destruct i;
  destruct loc => //;
                   destruct lab => //;
                                    destruct ret => //;
                                                     try exact H.

Lemma inst_typing_strip s i C:
  inst_typing s i C ->
  inst_typing s i (strip C).
Proof.
  intros H.
  inst_typing_equal i C H. 
Qed.

(* version with changing store, not necessary after all *)
(* simpler version coming next *) 
(* Lemma hfilled_typing x h es LI s C tf:
  store_typing s ->
  hfilled x h es LI ->
  e_typing s C LI tf ->
  exists tf' C', e_typing s C' es tf' /\
              forall snew es' LI' x', store_extension s snew ->
                                 e_typing snew C' es' tf' ->
                                 hfilled x' h es' LI' ->
                                 e_typing snew C LI' tf.
Proof.
  generalize dependent LI. generalize dependent C.
  generalize dependent tf. generalize dependent x.
  induction h; unfold hfilled, hfill; fold hfill;
    destruct (const_list _) eqn:Hconst => //.
  - intros x tf C LI HST HLI Htype.
    move/eqP in HLI; subst LI. destruct tf as [t1s t2s].
    apply e_composition_typing in Htype
        as (ts & t1s' & t2s' & t3s & -> & -> & Hbef & Hmidaft).
    apply e_composition_typing in Hmidaft
        as (ts' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Haft).
    eexists _,_. split; first exact Hmid.
    intros s0 es' LI' x' Hext Hes' HLI'.
    move/eqP in HLI'; subst.
    apply ety_weakening. eapply et_composition'.
    eapply store_extension_e_typing.
    exact HST. exact Hext.
    exact Hbef.
    apply ety_weakening. eapply et_composition'. exact Hes'.
    eapply store_extension_e_typing.
    exact HST. exact Hext.
    exact Haft.
  - intros x tf C LI HST HLI Htype.
    destruct (hfill _ _ _) eqn:Hfill => //.
    move/eqP in HLI; subst LI.
    destruct tf as [t1s t2s].
    apply e_composition_typing in Htype as (ts & t1s' & t2s' & t3s & -> & -> & Hbef & Hmidaft).
    apply e_composition_typing in Hmidaft as (ts' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Haft).
    apply Label_typing in Hmid as (ts'' & t2s' & -> & Hl0 & Hmid & <-).
    unfold hfilled in IHh.
    specialize (IHh x).
    rewrite Hfill in IHh.
    edestruct IHh as (tf' & C' & Hes & Hfillback).
    done. done. exact Hmid.
    eexists _,_. split; first exact Hes.
    intros s0 es' LI' x' Hext Hes' HLI'.
    destruct (hfill _ _ es') eqn:Hfill' => //.
    move/eqP in HLI'; subst LI'.
    apply ety_weakening. eapply et_composition'.
    eapply store_extension_e_typing.
    exact HST. exact Hext.
    exact Hbef.
    apply ety_weakening. eapply et_composition'.
    2:{ eapply store_extension_e_typing. exact HST. exact Hext. exact Haft. }
    apply et_weakening_empty_1. eapply ety_label => //.
    eapply store_extension_e_typing. exact HST. exact Hext. 
    exact Hl0.
    eapply Hfillback. exact Hext. exact Hes'. instantiate (1 := x').
    rewrite Hfill'. done.
  - intros x tf C LI HST HLI Htype.
    destruct (hfill _ _ _) eqn:Hfill => //.

    move/eqP in HLI; subst LI.
    destruct tf as [t1s t2s].
    apply e_composition_typing in Htype as (ts & t1s' & t2s' & t3s & -> & -> & Hbef & Hmidaft).
    apply e_composition_typing in Hmidaft as (ts' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Haft).
    apply Local_typing in Hmid as (ts'' & -> & Hmid & <-).
    unfold hfilled in IHh.
    specialize (IHh x).
    rewrite Hfill in IHh.
    inversion Hmid; subst.
    inversion H; subst. 
    edestruct IHh as (tf' & C' & Hes & Hfillback).
    done. done. exact H1.
    eexists _,_. split; first exact Hes.
    intros s0 es' LI' x' Hext Hes' HLI'.
    destruct (hfill _ _ es') eqn:Hfill' => //.
    move/eqP in HLI'; subst LI'.
    apply ety_weakening. eapply et_composition'.
    eapply store_extension_e_typing. exact HST. exact Hext. exact Hbef.
    apply ety_weakening. eapply et_composition'.
    2:{ eapply store_extension_e_typing. exact HST. exact Hext. exact Haft. } 
    apply et_weakening_empty_1. eapply ety_local => //. econstructor.
    eapply frame_typing_extension. exact Hext. exact H.
    done.
    eapply Hfillback. exact Hext. exact Hes'. instantiate (1 := x').
    rewrite Hfill'. done. by left.
  - destruct x as [x | |] => //.
    destruct (firstx_exception _ _ == _) eqn:Hclauses => //.
    all: destruct (hfill _ _ _) eqn:Hfill => //.
    all: intros tf C LI HST HLI Htype.
    all: move/eqP in HLI; subst LI.
    all: destruct tf as [t1s t2s].
    all: apply e_composition_typing in Htype as (ts & t1s' & t2s' & t3s & -> & -> & Hbef & Hmidaft).
    all: apply e_composition_typing in Hmidaft as (ts' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Haft).
    all: apply Handler_typing in Hmid as (ts'' & -> & Hclausest & Hmid).
    all: unfold hfilled in IHh.
    specialize (IHh (Var_handler x)).
    2: specialize (IHh (Var_prompt t)).
    3: specialize (IHh No_var).
    all: rewrite Hfill in IHh.
    all: edestruct IHh as (tf' & C' & Hes & Hfillback).
    all: try exact Hmid. all: try done.
    all: eexists _,_.
    all: split; first exact Hes.
    all: intros s0 es' LI' x' Hext Hes' HLI'.
    all: destruct x' as [x' | x' |] => //.
    1,4,7: destruct (firstx_exception _ x' == _) => //.
    all: destruct (hfill _ _ es') eqn:Hfill' => //.
    all: move/eqP in HLI'; subst LI'.
    all: apply ety_weakening.
    all: eapply et_composition'.
    all: try by eapply store_extension_e_typing; [exact HST | exact Hext | exact Hbef].
    all: apply ety_weakening.
    all: eapply et_composition'; last by eapply store_extension_e_typing; [exact HST | exact Hext | exact Haft].
    all: apply et_weakening_empty_1.
    all: eapply ety_handler => //.
    all: try (eapply List.Forall_impl; last exact Hclausest).
    all: try intros cl Hcl.
    all: try (eapply store_extension_exception_clause_typing; [exact Hext | exact Hcl]).
    all: eapply Hfillback; try exact Hes'.
    all: try exact Hext.
    all: try by instantiate (1 := Var_handler x'); rewrite Hfill' => //.
    all: try by instantiate (1 := Var_prompt x'); rewrite Hfill' => //.
    all: try by instantiate (1 := No_var); rewrite Hfill' => //.
  - destruct x as [|x  |] => //.
    2:destruct (firstx_continuation _ _ == _) eqn:Hclauses => //.
    all: destruct (hfill _ _ _) eqn:Hfill => //.
    all: intros tf C LI HST HLI Htype.
    all: move/eqP in HLI; subst LI.
    all: destruct tf as [t1s t2s].
    all: apply e_composition_typing in Htype as (ts & t1s' & t2s' & t3s & -> & -> & Hbef & Hmidaft).
    all: apply e_composition_typing in Hmidaft as (ts' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Haft).
    all: apply Prompt_typing in Hmid as ( -> & Hclausest & Hmid).
    all: unfold hfilled in IHh.
    specialize (IHh (Var_handler t)).
    2: specialize (IHh (Var_prompt x)).
    3: specialize (IHh No_var).
    all: rewrite Hfill in IHh.
    all: edestruct IHh as (tf' & C' & Hes & Hfillback).
    all: try exact Hmid. all: try done.
    all: eexists _,_.
    all: split; first exact Hes.
    all: intros s0 es' LI' x' Hext Hes' HLI'.
    all: destruct x' as [x' | x' |] => //.
    2,5,8: destruct (firstx_continuation _ x' == _) => //.
    all: destruct (hfill _ _ es') eqn:Hfill' => //.
    all: move/eqP in HLI'; subst LI'.
    all: apply ety_weakening.
    all: eapply et_composition'; first by eapply store_extension_e_typing ; [exact HST | exact Hext | exact Hbef].
    all: apply ety_weakening.
    all: eapply et_composition'; last by eapply store_extension_e_typing; [exact HST | exact Hext | exact Haft] .
    all: apply et_weakening_empty_1.
    all: eapply ety_prompt => //.
    all: try (eapply List.Forall_impl; last exact Hclausest).
    all: try intros cl Hcl.
    all: try (eapply store_extension_continuation_clause_typing; [exact Hext | exact Hcl]).
    all: eapply Hfillback; try exact Hes'.
    all: try exact Hext.
    all: try by instantiate (1 := Var_handler x'); rewrite Hfill' => //.
    all: try by instantiate (1 := Var_prompt x'); rewrite Hfill' => //.
    all: try by instantiate (1 := No_var); rewrite Hfill' => //.
Qed. *)


Lemma hfilled_typing x h es LI s C tf:
  hfilled x h es LI ->
  e_typing s C LI tf ->
  exists tf' C', e_typing s C' es tf'  /\
              forall es' LI' x', e_typing s C' es' tf' -> hfilled x' h es' LI' -> e_typing s C LI' tf.
Proof.
  generalize dependent LI. generalize dependent C. generalize dependent tf. generalize dependent x.
  induction h; unfold hfilled, hfill; fold hfill; destruct (const_list _) eqn:Hconst => //.
  - intros x tf C LI HLI Htype.
    move/eqP in HLI; subst LI. destruct tf as [t1s t2s].
    apply e_composition_typing in Htype as (ts & t1s' & t2s' & t3s & -> & -> & Hbef & Hmidaft).
    apply e_composition_typing in Hmidaft as (ts' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Haft).
    eexists _,_. split; first exact Hmid.
    intros es' LI' x' Hes' HLI'.
    move/eqP in HLI'; subst.
    apply ety_weakening. eapply et_composition'. exact Hbef.
    apply ety_weakening. eapply et_composition'. exact Hes'. exact Haft.
  - intros x tf C LI HLI Htype.
    destruct (hfill _ _ _) eqn:Hfill => //.
    move/eqP in HLI; subst LI.
    destruct tf as [t1s t2s].
    apply e_composition_typing in Htype as (ts & t1s' & t2s' & t3s & -> & -> & Hbef & Hmidaft).
    apply e_composition_typing in Hmidaft as (ts' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Haft).
    apply Label_typing in Hmid as (ts'' & t2s' & -> & Hl0 & Hmid & <-).
    unfold hfilled in IHh.
    specialize (IHh x).
    rewrite Hfill in IHh.
    edestruct IHh as (tf' & C' & Hes & Hfillback).
    done. exact Hmid.
    eexists _,_. split; first exact Hes.
    intros es' LI' x' Hes' HLI'.
    destruct (hfill _ _ es') eqn:Hfill' => //.
    move/eqP in HLI'; subst LI'.
    apply ety_weakening. eapply et_composition'. exact Hbef.
    apply ety_weakening. eapply et_composition'; last exact Haft.
    apply et_weakening_empty_1. eapply ety_label => //. exact Hl0.
    eapply Hfillback. exact Hes'. instantiate (1 := x'). rewrite Hfill'. done.
  - intros x tf C LI HLI Htype.
    destruct (hfill _ _ _) eqn:Hfill => //.

    move/eqP in HLI; subst LI.
    destruct tf as [t1s t2s].
    apply e_composition_typing in Htype as (ts & t1s' & t2s' & t3s & -> & -> & Hbef & Hmidaft).
    apply e_composition_typing in Hmidaft as (ts' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Haft).
    apply Local_typing in Hmid as (ts'' & -> & Hmid & <-).
    unfold hfilled in IHh.
    specialize (IHh x).
    rewrite Hfill in IHh.
    inversion Hmid; subst.
    inversion H; subst. 
    edestruct IHh as (tf' & (* i' & *) C' & Hes & (* HC' & *) Hfillback).
    done. exact H1.
    eexists _,_. split; first exact Hes.
    intros es' LI' x' Hes' HLI'.
    destruct (hfill _ _ es') eqn:Hfill' => //.
    move/eqP in HLI'; subst LI'.
    apply ety_weakening. eapply et_composition'. exact Hbef.
    apply ety_weakening. eapply et_composition'; last exact Haft.
    apply et_weakening_empty_1. eapply ety_local => //. econstructor. exact H.
    done.
    eapply Hfillback. exact Hes'. instantiate (1 := x').
    rewrite Hfill'. done. by left.
  - destruct x as [x| | |] => //.
    destruct (firstx_exception _ _ == _) eqn:Hclauses => //.
    all: destruct (hfill _ _ _) eqn:Hfill => //.
    all: intros tf C LI HLI Htype.
    all: move/eqP in HLI; subst LI.
    all: destruct tf as [t1s t2s].
    all: apply e_composition_typing in Htype as (ts & t1s' & t2s' & t3s & -> & -> & Hbef & Hmidaft).
    all: apply e_composition_typing in Hmidaft as (ts' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Haft).
    all: apply Handler_typing in Hmid as (ts'' & -> & Hclausest & Hmid).
    all: unfold hfilled in IHh.
    specialize (IHh (Var_handler x)).
    2: specialize (IHh (Var_prompt_suspend t)).
    3: specialize (IHh (Var_prompt_switch t)).
    4: specialize (IHh No_var).
    all: rewrite Hfill in IHh.
    all: edestruct IHh as (tf' & C' & Hes & Hfillback).
    all: try exact Hmid. all: try done.
    all: eexists _,_.
    all: split; first exact Hes.
    all: intros es' LI' x' Hes' HLI'.
    all: destruct x' as [x' | x' |x' |] => //.
    1,5,9,13: destruct (firstx_exception _ x' == _) => //.
    all: destruct (hfill _ _ es') eqn:Hfill' => //.
    all: move/eqP in HLI'; subst LI'.
    all: apply ety_weakening.
    all: eapply et_composition'; try exact Hbef.
    all: apply ety_weakening.
    all: eapply et_composition'; last exact Haft.
    all: apply et_weakening_empty_1.
    all: eapply ety_handler => //. 
    all: eapply Hfillback; try exact Hes'.
    all: try by instantiate (1 := Var_handler x'); rewrite Hfill' => //.
    all: try by instantiate (1 := Var_prompt_suspend x'); rewrite Hfill' => //.
    all: try by instantiate (1 := Var_prompt_switch x'); rewrite Hfill' => //.
    all: try by instantiate (1 := No_var); rewrite Hfill' => //.
  - destruct x as [|x|x  |] => //.
    2:destruct (firstx_continuation_suspend _ _ == _) eqn:Hclauses => //.
    3:destruct (firstx_continuation_switch _ _ == _) eqn:Hclauses => //.
    all: destruct (hfill _ _ _) eqn:Hfill => //.
    all: intros tf C LI HLI Htype.
    all: move/eqP in HLI; subst LI.
    all: destruct tf as [t1s t2s].
    all: apply e_composition_typing in Htype as (ts & t1s' & t2s' & t3s & -> & -> & Hbef & Hmidaft).
    all: apply e_composition_typing in Hmidaft as (ts' & t1s'' & t2s'' & t3s' & -> & -> & Hmid & Haft).
    all: apply Prompt_typing in Hmid as ( -> & Hclausest & Hmid).
    all: unfold hfilled in IHh.
    specialize (IHh (Var_handler t)).
    2: specialize (IHh (Var_prompt_suspend x)).
    3: specialize (IHh (Var_prompt_switch x)).
    4: specialize (IHh No_var).
    all: rewrite Hfill in IHh.
    all: edestruct IHh as (tf' & C' & Hes & Hfillback).
    all: try exact Hmid. all: try done.
    all: eexists _,_.
    all: split; first exact Hes.
    all: intros es' LI' x' Hes' HLI'.
    all: destruct x' as [x' | x' |x' |] => //.
    2,6,10,14: destruct (firstx_continuation_suspend _ x' == _) => //.
    6,9,12,15: destruct (firstx_continuation_switch _ x' == _) => //.
    all: destruct (hfill _ _ es') eqn:Hfill' => //.
    all: move/eqP in HLI'; subst LI'.
    all: apply ety_weakening.
    all: eapply et_composition'; try exact Hbef.
    all: apply ety_weakening.
    all: eapply et_composition'; last exact Haft.
    all: apply et_weakening_empty_1.
    all: eapply ety_prompt => //. 
    all: eapply Hfillback; try exact Hes'.
    all: try by instantiate (1 := Var_handler x'); rewrite Hfill' => //.
    all: try by instantiate (1 := Var_prompt_switch x'); rewrite Hfill' => //.
    all: try by instantiate (1 := Var_prompt_suspend x'); rewrite Hfill' => //.
    all: try by instantiate (1 := No_var); rewrite Hfill' => //.
Qed.



Lemma hfilled_hhplug x vs hh es LI:
  hfilled x (hhplug vs hh) es LI <->
    (const_list vs && hfilled x hh (vs ++ es) LI).
Proof.
  generalize dependent LI. generalize dependent x.
  induction hh; intros x LI.
  - unfold hfilled => /=. unfold const_list. rewrite List.forallb_app.
    destruct (List.forallb _ l); last by rewrite Bool.andb_false_r.
    destruct (List.forallb _ vs) => //=.
    split; move/eqP; intros ->; by repeat rewrite catA.
  - unfold hfilled => /=.
    destruct (const_list l); last by rewrite Bool.andb_false_r.
    unfold hfilled in IHhh.
    specialize (IHhh x).
    destruct (hfill _ _ es) => //.
    + destruct (IHhh l2) as [H _].
      specialize (H (eq_refl l2)).
      split.
      * move/eqP. intros ->. destruct (hfill _ _ _) => //.
        remove_bools_options. 
        rewrite H. simpl. subst; done.
      * destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
        remove_bools_options.
        rewrite H H0. done.
    + split; first done.
      intros H. destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
      remove_bools_options.
      destruct (IHhh l2) as [_ Habs]. apply Habs => //. rewrite H.
      rewrite (eq_refl l2). done.
  - unfold hfilled => /=.
    destruct (const_list l); last by rewrite Bool.andb_false_r.
    unfold hfilled in IHhh.
    specialize (IHhh x).
    destruct (hfill _ _ es) => //.
    + destruct (IHhh l1) as [H _].
      specialize (H (eq_refl l1)).
      split.
      * move/eqP. intros ->. destruct (hfill _ _ _) => //.
        remove_bools_options. 
        rewrite H. simpl. subst; done.
      * destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
        remove_bools_options.
        rewrite H H0. done.
    + split; first done.
      intros H. destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
      remove_bools_options.
      destruct (IHhh l1) as [_ Habs]. apply Habs => //. rewrite H.
      rewrite (eq_refl l1). done.
  - unfold hfilled => /=.
    destruct (const_list l); last by rewrite Bool.andb_false_r.
    destruct x as [x | | |] => /=.
    destruct (firstx_exception _ _ == _); last by rewrite Bool.andb_false_r.
    all: unfold hfilled in IHhh.
    specialize (IHhh (Var_handler x)).
    2: specialize (IHhh (Var_prompt_suspend t)).
    3: specialize (IHhh (Var_prompt_switch t)).
    4: specialize (IHhh No_var).
    all: destruct (hfill _ _ es) => //.
    + destruct (IHhh l2) as [H _].
      specialize (H (eq_refl l2)).
      split.
      * move/eqP. intros ->. destruct (hfill _ _ _) => //.
        remove_bools_options. 
        rewrite H. simpl. subst; done.
      * destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
        remove_bools_options.
        rewrite H H0. done.
    + split; first done.
      intros H. destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
      remove_bools_options.
      destruct (IHhh l2) as [_ Habs]. apply Habs => //. rewrite H.
      rewrite (eq_refl l2). done.
    + destruct (IHhh l2) as [H _].
      specialize (H (eq_refl l2)).
      split.
      * move/eqP. intros ->. destruct (hfill _ _ _) => //.
        remove_bools_options. 
        rewrite H. simpl. subst; done.
      * destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
        remove_bools_options.
        rewrite H H0. done.
    + split; first done.
      intros H. destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
      remove_bools_options.
      destruct (IHhh l2) as [_ Habs]. apply Habs => //. rewrite H.
      rewrite (eq_refl l2). done.
    + destruct (IHhh l2) as [H _].
      specialize (H (eq_refl l2)).
      split.
      * move/eqP. intros ->. destruct (hfill _ _ _) => //.
        remove_bools_options. 
        rewrite H. simpl. subst; done.
      * destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
        remove_bools_options.
        rewrite H H0. done.
    + split; first done.
      intros H. destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
      remove_bools_options.
      destruct (IHhh l2) as [_ Habs]. apply Habs => //. rewrite H.
      rewrite (eq_refl l2). done.
    + destruct (IHhh l2) as [H _].
      specialize (H (eq_refl l2)).
      split.
      * move/eqP. intros ->. destruct (hfill _ _ _) => //.
        remove_bools_options. 
        rewrite H. simpl. subst; done.
      * destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
        remove_bools_options.
        rewrite H H0. done.
    + split; first done.
      intros H. destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
      remove_bools_options.
      destruct (IHhh l2) as [_ Habs]. apply Habs => //. rewrite H.
      rewrite (eq_refl l2). done.
  - unfold hfilled => /=.
    destruct (const_list l); last by rewrite Bool.andb_false_r.
    destruct x as [|x|x  |] => /=.
    2:destruct (firstx_continuation_suspend _ _ == _); last by rewrite Bool.andb_false_r.
    3:destruct (firstx_continuation_switch _ _ == _); last by rewrite Bool.andb_false_r.
    all: unfold hfilled in IHhh.
    specialize (IHhh (Var_handler t)).
    2: specialize (IHhh (Var_prompt_suspend x)).
    3: specialize (IHhh (Var_prompt_switch x)).
    4: specialize (IHhh No_var).
    all: destruct (hfill _ _ es) => //.
    + destruct (IHhh l3) as [H _].
      specialize (H (eq_refl l3)).
      split.
      * move/eqP. intros ->. destruct (hfill _ _ _) => //.
        remove_bools_options. 
        rewrite H. simpl. subst; done.
      * destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
        remove_bools_options.
        rewrite H H0. done.
    + split; first done.
      intros H. destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
      remove_bools_options.
      destruct (IHhh l3) as [_ Habs]. apply Habs => //. rewrite H.
      rewrite (eq_refl l3). done.
       + destruct (IHhh l3) as [H _].
      specialize (H (eq_refl l3)).
      split.
      * move/eqP. intros ->. destruct (hfill _ _ _) => //.
        remove_bools_options. 
        rewrite H. simpl. subst; done.
      * destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
        remove_bools_options.
        rewrite H H0. done.
    + split; first done.
      intros H. destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
      remove_bools_options.
      destruct (IHhh l3) as [_ Habs]. apply Habs => //. rewrite H.
      rewrite (eq_refl l3). done.
       + destruct (IHhh l3) as [H _].
      specialize (H (eq_refl l3)).
      split.
      * move/eqP. intros ->. destruct (hfill _ _ _) => //.
        remove_bools_options. 
        rewrite H. simpl. subst; done.
      * destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
        remove_bools_options.
        rewrite H H0. done.
    + split; first done.
      intros H. destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
      remove_bools_options.
      destruct (IHhh l3) as [_ Habs]. apply Habs => //. rewrite H.
      rewrite (eq_refl l3). done.
         + destruct (IHhh l3) as [H _].
      specialize (H (eq_refl l3)).
      split.
      * move/eqP. intros ->. destruct (hfill _ _ _) => //.
        remove_bools_options. 
        rewrite H. simpl. subst; done.
      * destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
        remove_bools_options.
        rewrite H H0. done.
    + split; first done.
      intros H. destruct (hfill _ _ _); last by rewrite Bool.andb_false_r in H.
      remove_bools_options.
      destruct (IHhh l3) as [_ Habs]. apply Habs => //. rewrite H.
      rewrite (eq_refl l3). done.
Qed. 
    

Lemma Const_cat_typing s C es1 es2 ts1 ts2:
  const_list es1 ->
  const_list es2 ->
  e_typing s C (es1 ++ es2) (Tf [::] (ts1 ++ ts2)) ->
  (length es1 = length ts1 \/ length es2 = length ts2) ->
  e_typing s C es1 (Tf [::] ts1) /\ e_typing s C es2 (Tf [::] ts2).
Proof.
  intros Hconst1 Hconst2 Htyp Hlen.
  apply const_es_exists in Hconst2 as [vs2 ->].
  assert (length vs2 = length ts2) as Hlen2.
  { apply const_es_exists in Hconst1 as [vs1 ->].
    unfold v_to_e_list in Htyp. rewrite - map_cat in Htyp.
    apply Const_list_typing in Htyp as (ts & Hvsts & Hts & Htyp).
    simpl in Hts; subst ts.
    destruct Hlen.
    - repeat rewrite length_is_size. repeat rewrite length_is_size in H.
      rewrite size_map in H.
      assert (size vs1 + size vs2 = size ts1 + size ts2); last lias.
      do 2 rewrite - size_cat. rewrite - (size_map (typeof s) (vs1 ++ vs2)).
      rewrite Hvsts. rewrite size_map. done.
    - rewrite - H. repeat rewrite length_is_size. rewrite size_map. done. } 

  apply e_composition_typing in Htyp as (ts & t1s' & t2s' & t3s & Hts & Hts' & Hes1 & Hes2).
  destruct ts => //. destruct t1s' => //. clear Hts. simpl in Hts'; subst t2s'.
  apply Const_list_typing in Hes2 as (ts & Hvsts & Hts & Hes2).
  apply concat_cancel_last_n in Hts.
  2:{ repeat rewrite length_is_size in Hlen2. rewrite - Hlen2.
      rewrite - (size_map (typeof s) vs2). rewrite Hvsts. rewrite size_map. done. }
  remove_bools_options. subst. split => //. 
Qed.   


Lemma c_typing_hhplug s (* C *) ts t1s t2s hh vs:
  c_typing s (* C *) (Cont_hh (Tf (ts ++ t1s) t2s) hh) ->
(*  const_list vs -> *)
  e_typing s empty_context (* (strip C) *) (v_to_e_list vs) (Tf [::] ts) -> (* map (typeof s) vs = map Some ts ->  *)
  c_typing s (* C *) (Cont_hh (Tf t1s t2s) (hhplug (v_to_e_list vs) hh)).
Proof.
  intros Htyp Hvs.
  inversion Htyp. subst.
  apply const_es_exists in H2 as [vs' ->].
  apply Const_list_typing in H4 as (ts' & Hvs' & Hts & Hvst').
  simpl in Hts; subst ts'. 
  assert (size vs' = size ts + size t1s) as Hsize.
  { rewrite - (size_map (typeof s)).
    rewrite Hvs'. rewrite size_map. rewrite size_cat. done. }
  remember Hvst' as Hvst.
  clear HeqHvst.
  rewrite - (cat_take_drop (size ts) vs') in Hvst'.
  unfold v_to_e_list in Hvst'.
  rewrite map_cat in Hvst'.
  apply Const_cat_typing in Hvst' as [Hbef Haft]; cycle 1.
  - apply v_to_e_is_const_list.
  - apply v_to_e_is_const_list.
  - left. do 2 rewrite length_is_size. rewrite size_map.
    rewrite size_takel => //. lias.
  - remember H5 as HLI. clear HeqHLI.
    eapply (hfilled_change (v_to_e_list vs ++ v_to_e_list (drop (length ts) vs'))) in H5 as [LI2 HLI2].
    econstructor.
    2: exact Haft.
    apply v_to_e_is_const_list.
(*    rewrite - (cat_take_drop (size ts) vs') in H6. *)
    apply hfilled_hhplug.
    rewrite v_to_e_is_const_list => /=.
    exact HLI2.
    eapply e_typing_plug_value.
    7: exact H6.
    6: exact HLI2.
    5: exact HLI.
    apply v_to_e_is_const_list.
    rewrite v_to_e_cat.
    apply v_to_e_is_const_list.
    exact Hvst.
    eapply et_composition'.
    exact Hvs.
    apply et_weakening_empty_1.
    exact Haft.
    by left.
Qed. 
(*  
  (* exact H2. *)
  subst. intros vs0 x LI C Htags Hvs0 HLI.
(*   apply const_es_exists in Hconst as [vsv ->]. *)
  eapply H1. done. instantiate (1 := (vs ++ vs0)).
  apply Const_list_typing_empty.
  unfold vs_to_vts. do 2 rewrite map_cat.
  apply Const_list_typing in Hvs0 as (ts0 & Hvs0 & -> & _).
(*  apply Const_list_typing in Hvs as (ts1 & Hvsv & -> & _). *)
  rewrite Hvs Hvs0.
  done.
  instantiate (1 := x).
  apply hfilled_hhplug in HLI.
  unfold v_to_e_list; rewrite map_cat. done.
Qed. *)

Lemma store_extension_add_exn s e:
  store_typing s ->
  store_extension s (add_exn s e).
Proof.
  intros HST.
  unfold store_extension.
  destruct s => //=. 
  repeat (apply/andP; split => //).
  - rewrite length_is_size take_size.
    rewrite all2_cont_extension_same => //.
  - rewrite all2_tab_extension_same => //.
  - rewrite all2_mem_extension_same => //.
  - rewrite all2_glob_extension_same => //.
    destruct HST as (_ & _ & _ & Hgs & _).
    rewrite List.Forall_forall in Hgs.
    intros g Hin. apply Hgs in Hin as [t Htg].
    apply AI_const_typing in Htg as (t0 & Ht0 & _).
    rewrite Ht0. done.
  - apply/eqP. apply list_prefix_equiv. exists [::e]. done.
Qed. 


Lemma store_typing_add_exn s e :
  store_typing s ->
  exn_sound (add_exn s e) e ->
  store_typing (add_exn s e).
Proof.
  intros HST Hexnsound.
  eapply store_extension_add_exn in HST as Hext.
  remember HST as HST'; clear HeqHST'.
  unfold store_typing. destruct s => /=.
  destruct HST' as (Hfuncs & Htabs & Hmems & Hglobs & Hconts & Hexns).
  repeat split => //=.
  - eapply List.Forall_impl; last exact Hfuncs.
    intros cl [tf Hcl].
    exists tf.
    eapply store_extension_cl_typing.
    exact Hext.
    exact Hcl. 
  - eapply List.Forall_impl; last exact Hglobs.
    intros g [t Hg].
    exists t. eapply store_extension_e_typing.
    exact HST. exact Hext. exact Hg.
  - eapply List.Forall_impl; last exact Hconts.
    intros cont Hcont.
    eapply store_extension_c_typing.
    exact HST. exact Hext. exact Hcont.
  - apply List.Forall_app. split.
    + eapply List.Forall_impl; last exact Hexns.
      intros exn (t & Hexn & Htags).
      exists t. split => //. eapply store_extension_e_typing.
      exact HST. exact Hext. exact Hexn.
    + constructor. done. constructor.
Qed.

Lemma Forall2_forall {A B} (P : A -> B -> Prop) l1 l2 :
  List.Forall2 P l1 l2 <->
    (length l1 = length l2 /\
    forall i x y, List.nth_error l1 i = Some x ->
             List.nth_error l2 i = Some y ->
             P x y).
Proof.
  split.
  - generalize dependent l2. induction l1 => //=.
    + intros l2 Hl2. destruct l2; inversion Hl2.
      split; first done.
      intros i x y Hx Hy. destruct i => //.
    + intros l2 Hl2. destruct l2; inversion Hl2; subst.
      apply IHl1 in H4 as [-> IH].
      split; first done.
      intros i x y Hx Hy.
      destruct i.
      * inversion Hx; inversion Hy; subst. done.
      * inversion Hx; inversion Hy. eapply IH; eauto.
  - generalize dependent l2. induction l1 => //=.
    + intros l2 [Hlen HP]. destruct l2 => //.
    + intros l2 [Hlen HP]. destruct l2 => //.
      constructor.
      * eapply HP. instantiate (1 := 0) => //. done.
      * apply IHl1. simpl in Hlen. split; first lias.
        intros i x y Hx Hy.
        eapply HP. instantiate (1 := i.+1) => //. done.
Qed. 


Lemma stypes_get_type s inst C i :
  tc_types_t C = inst_types inst ->
  stypes s inst i = get_type C i.
Proof.
  destruct i => //=.
  intros ->. done.
Qed. 

Lemma update_list_at_Forall {A} P l i (x:A) :
  List.Forall P l ->
  P x ->
  List.Forall P (update_list_at l i x).
Proof.
  generalize dependent i.
  induction l; destruct i; unfold update_list_at; intros Hl Hx => //=.
  - constructor => //.
  - constructor => //.
  - constructor => //=. unfold List.skipn.
    by inversion Hl.
  - constructor => //=. by inversion Hl.
    apply IHl. by inversion Hl. done.
Qed. 


Lemma firstx_continuation_switch_In hs x :
  firstx_continuation_switch hs x ->
  List.In (DC_switch x) hs.
Proof.
  induction hs => //=.
  destruct a => //=.
  - intros H. right. by apply IHhs.
  - destruct (x == t) eqn:Hxt => //.
    + move/eqP in Hxt. subst x. by left.
    + intros H. right. by apply IHhs.
Qed. 

Lemma store_extension_reduce: forall s f es s' f' es' C tf loc lab ret,
    reduce s f es s' f' es' ->
    inst_typing s f.(f_inst) C ->
    e_typing s (upd_label (upd_local_return C loc ret) lab) es tf ->
    store_typing s ->
    store_extension s s' /\ store_typing s'.
Proof.
  move => s f es s' f' es' C tf loc lab ret (* Hcorrupt *) HReduce.
  generalize dependent C. generalize dependent tf.
  generalize dependent loc. generalize dependent lab. generalize dependent ret.
  induction HReduce; try move => ret lab loc tf C HIT HType HST; try intros; destruct tf ; (try by split => //; apply store_extension_same) ; (try by split; [apply store_extension_new_cont| apply store_typing_new_cont]); (try by eapply store_extension_upd_cont; eauto).
  - (* Throw *)
    subst s'. split.
    apply store_extension_add_exn. done.
    apply store_typing_add_exn. done.
    apply e_composition_typing in HType as (ts' & ts1 & ts2 & ts3 & -> & -> & Hves & Hthrow).
    convert_et_to_bet.
    apply Throw_typing in Hthrow as (ts'' & t1s' & Hx & ->).
    subst ves.
    apply Const_list_typing in Hves as (tsv & Htsv & Htypes & Hconst).
    eapply tc_reference_tag in HIT.
    2: exact H. 2: exact H0. 2: exact Hx.
    inversion HIT; subst t1s'.
    do 2 rewrite length_is_size in H2.
    apply concat_cancel_last_n in Htypes.
    2:{ rewrite - H2 size_map.
        rewrite - (size_map (typeof s) vcs) Htsv size_map.
        done. }
    remove_bools_options. subst.
    eexists. simpl.
    split; last exact H0.
    eapply t_const_ignores_context. apply v_to_e_is_const_list.
    eapply store_extension_e_typing.
    exact HST. apply store_extension_add_exn. exact HST.
    exact Hconst.
    
    
  - (* Contnew *)
    split; [apply store_extension_new_cont| apply store_typing_new_cont] => //.
    econstructor.
    + instantiate (1 := v_to_e_list (default_vals l)).
      apply v_to_e_is_const_list.
    + apply default_vals_typing.
    + subst hh. unfold hfilled, hfill => /=. done.
    + eapply et_composition'.
      apply default_vals_typing.
      rewrite separate1.
      rewrite separate1 in H2. destruct tf0.
      apply e_composition_typing in H2 as (ts & ts1 & ts2 & ts3 & -> & -> & Href & Hcontnew).
      apply AI_ref_typing in Href as (t & Ht & ->).
      apply et_to_bet in Hcontnew; last by constructor.
      apply Contnew_typing in Hcontnew as (ts' & tf & Htypes & Hts1' & ->).
      apply concat_cancel_last in Hts1' as [-> ->].
      simpl in Ht. destruct (List.nth_error _ x) eqn:Hfuncs => //. 
      eapply ety_composition.
      * instantiate (1 := (l ++ [:: _])). apply et_weakening_empty_1.
        eapply ety_ref. rewrite Hfuncs. done. done.
      * eapply ety_a' => /=. constructor => //.
        inversion Ht.
        inversion Htypes; subst.
        apply inst_typing_types in H1.
        erewrite <- (stypes_get_type s) in Htypes; last exact H1.
        rewrite H in Htypes.
        inversion Htypes; subst.
        inversion Ht.
        apply bet_call_reference => //.
  - (* resume *)
    split; [eapply store_extension_upd_cont| eapply store_typing_upd_cont]; try exact H2; try done.
  - (* Suspend *)
    split; [apply store_extension_new_cont| apply store_typing_new_cont] => //.
    apply Prompt_typing in HType as ((*ts2' &*) -> & Hclauses & HType).
    eapply hfilled_typing in HType as (tf' & (* i' & *) C' & HType & (* HC' & *) Hfillback).
    2: exact H2.
    destruct tf' as [t1s' t2s'].
    subst x.
    apply AI_suspend_desugared_typing in HType as (t1s'' & t2s'' & -> & Hvs & Htags).
    rewrite H0 in Htags.
    inversion Htags. subst.
    edestruct (hfilled_change (* (v_to_e_list vs') *) (v_to_e_list (default_vals t2s''))) as [LI' HLI']; first exact H2.
    by left.
    econstructor.
    3: exact HLI'. apply v_to_e_is_const_list.
    apply default_vals_typing.
    eapply Hfillback in HLI'.
    eapply store_extension_e_typing. exact HST.
    apply store_extension_new_cont.
    done.
    exact HLI'. 
    apply et_weakening_empty_1.
    apply default_vals_typing. 
  - (* Switch *)
    split.
    + eapply store_extension_trans; cycle 1.
      * eapply store_extension_upd_cont.
        -- done.
        -- exact H1.
        -- done.
      * eapply store_extension_new_cont.
        eapply store_typing_upd_cont. done.
        exact H1. done.
      * intros g Hin Habs.
        destruct s. destruct H6 as (_ & _ & _ & Hgs & _).
        simpl in *.
        rewrite List.Forall_forall in Hgs.
        apply Hgs in Hin as [t Ht].
        apply AI_const_typing in Ht as (t0 & Ht0 & _).
        rewrite Ht0 in Habs. done.
    + apply store_typing_new_cont.
      eapply store_typing_upd_cont; try exact H1; try done.
      apply c_typing_new_cont; try exact H2; try done.
      eapply store_typing_upd_cont. done. eauto. done.
      eapply c_typing_upd_cont. done. eauto. done.
      destruct tf0.
      apply Prompt_typing in H5 as (-> & Hclauses & HType).
      eapply hfilled_typing in HType as (tfn & C' & HType & Hfillback).
      2: exact H2.
      destruct tfn as [t1sn t2sn].
      destruct x.
      apply AI_switch_desugared_typing in HType as (ts' & t1s'' & t2s'' & cont & Htags & Hconts & Hcont & Htypes' & Htf & ->).
      inversion Htf; subst l l0.
      inversion H0; subst ts'.
      apply concat_cancel_last in H7 as [-> Htypes].
      inversion Htypes; subst tf'.
      clear Htypes Htf.
      rewrite List.Forall_forall in Hclauses.
      apply firstx_continuation_switch_In in H.
      apply Hclauses in H.
      inversion H; subst.
      rewrite H9 in Htags.
      inversion Htags; subst t2s.
      edestruct (hfilled_change (v_to_e_list (default_vals t2s''))) as [LI'' HLI'']; first exact H2.
      by left.
      econstructor.
      3: exact HLI''.
      apply v_to_e_is_const_list.
      apply default_vals_typing.
      eapply Hfillback in HLI''.
      exact HLI''. 
      apply et_weakening_empty_1.
      apply default_vals_typing. 

  - (* Contbind *)
    split.
    + eapply store_extension_trans; cycle 1.
      * eapply store_extension_upd_cont.
        -- done.
        -- exact H3.
        -- done. (* instantiate (1 := (Cont_dagger (Tf (ts ++ t1s) t2s))) => //.  *)
      * eapply store_extension_new_cont.
        eapply store_typing_upd_cont. done.
        exact H3. done.
      * intros g Hin Habs.
        destruct s. destruct HST as (_ & _ & _ & Hgs & _).
        simpl in *.
        rewrite List.Forall_forall in Hgs.
        apply Hgs in Hin as [t Ht].
        apply AI_const_typing in Ht as (t0 & Ht0 & _).
        rewrite Ht0 in Habs. done.
    + apply store_typing_new_cont.
      eapply store_typing_upd_cont; try exact H3; try done.
      eapply c_typing_new_cont; try exact H3; try done.
      eapply store_typing_upd_cont. done. eauto. done.
      eapply c_typing_upd_cont. done. eauto. done.
      apply e_composition_typing in HType as (ts' & t1s' & t2s' & t3s & -> & -> & Hvst & Hrest).
      apply const_es_exists in H as [vs' ->].
      apply Const_list_typing in Hvst as (tsv & Hvs' & -> & Hvstype).
      rewrite separate1 in Hrest.
      apply e_composition_typing in Hrest as (ts'' & t1s'' & t2s'' & t3s' & Ht & -> & Hreft & Hbindt).
      apply AI_ref_cont_typing in Hreft as (t & Hcont & ->).
      convert_et_to_bet.
      apply Contbind_typing in Hbindt as (tsnew & t0s & t1snew & t2snew & H0' & H1' & Ht' & ->).
(*      unfold stypes in H0. unfold stypes in H1. *)
      apply inst_typing_types in HIT.
      erewrite <- (stypes_get_type s) in H0'; last exact HIT.
      rewrite H0' in H0.
      erewrite <- (stypes_get_type s) in H1'; last exact HIT.
      rewrite H1' in H1.
      inversion H1; subst t1snew t2snew.
      inversion H0. apply concat_cancel_last_n in H4; last done.
      remove_bools_options.
      rewrite catA in Ht'.
      apply concat_cancel_last in Ht' as [-> ->].
      rewrite catA in Ht.
      apply concat_cancel_last_n in Ht; last first.
      { do 2 rewrite length_is_size in H2. rewrite H2.
        unfold v_to_e_list. rewrite size_map.
        erewrite <- size_map. instantiate (1 := Some). rewrite - Hvs'.
        rewrite size_map. done. }
      remove_bools_options. subst.
      unfold store_typing in HST.
      destruct s.
      destruct HST as (_ & _ & _ & _ & Hconts & _).
      apply List.nth_error_In in H3.
      edestruct List.Forall_forall as [Hforall _].
      eapply Hforall in Hconts; last exact H3.
      eapply c_typing_hhplug. exact Hconts.
      eapply t_const_ignores_context. apply v_to_e_is_const_list.
      exact Hvstype. 
  - (* Resume_throw *)
    apply e_composition_typing in HType as (ts' & t1s' & t2s' & t3s & -> & -> & Hves & Hrefcontthrow).
    subst ves.
    apply Const_list_typing in Hves as (tvs & Htvs & -> & Hconst).
    rewrite separate1 in Hrefcontthrow.
    apply e_composition_typing in Hrefcontthrow as (ts'' & t1s'' & t2s'' & t3s' & Htypes & -> & Hrefcont & Hresumethrow).
    apply AI_ref_cont_typing in Hrefcont as (tref & Htref & ->).
    convert_et_to_bet.
    apply Resume_throw_typing in Hresumethrow
        as (ts''' & t1s''' & t2s''' & t0s & Hgettype & Htags & Hclauses_& Htypes' & ->).
    rewrite catA in Htypes'.
    apply concat_cancel_last in Htypes' as [-> ->].
    eapply tc_reference_tag in HIT.
    2: exact H. 2: exact H0. 2: exact Htags.
    inversion HIT; subst.
    rewrite catA in Htypes.
    apply concat_cancel_last_n in Htypes.
    2:{ do 2 rewrite length_is_size in H2.
        rewrite -H2 size_map.
        rewrite -(size_map (typeof s) vcs) Htvs size_map.
        done. }
    remove_bools_options. subst t0s t1s'.
    split.
    + subst.
      eapply store_extension_trans; last first.
      * eapply store_extension_upd_cont.
        -- eapply store_typing_add_exn.
           done. eexists. split.
           ++ eapply store_extension_e_typing.
              exact HST. apply store_extension_add_exn.
              exact HST.
              eapply t_const_ignores_context.
              apply v_to_e_is_const_list.
              exact Hconst.
           ++ exact H0.
        -- exact H5.
        -- done.
      * apply store_extension_add_exn.
        exact HST.
      * intros g Hin Habs.
        destruct s. destruct HST as (_ & _ & _ & Hgs & _).
        simpl in *.
        rewrite List.Forall_forall in Hgs.
        apply Hgs in Hin as [t Ht].
        apply AI_const_typing in Ht as (t0 & Ht0 & _).
        rewrite Ht0 in Habs. done.
    + eapply store_typing_upd_cont.
      * apply store_typing_add_exn.
        -- exact HST.
        -- eexists. split.
           ++ eapply store_extension_e_typing.
              exact HST. apply store_extension_add_exn.
              exact HST.
              eapply t_const_ignores_context.
              apply v_to_e_is_const_list.
              exact Hconst.
           ++ exact H0.
      * exact H5.
      * done.
  - (* update glob *)
    rewrite (separate1 (AI_const v)) in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]]. subst.
    apply et_to_bet in H4; auto_basic. simpl in H4.
    apply Set_global_typing in H4 as (g & t & Hg & <- & Hmut & -> & Hi).
    apply AI_const_typing in H3 as (t & Ht & H3 & Hconst).
    apply concat_cancel_last in H3 as [-> H3]. 
    unfold supdate_glob in H.
    unfold option_bind in H.
    unfold supdate_glob_s in H.
    unfold option_map in H.
    assert (store_extension s s') as Hext.
    { remove_bools_options.
      unfold sglob_ind in Hoption.
      simpl in Hg.
      eapply tc_reference_glob_type in Hg; eauto.
      destruct g => //.
      destruct g0 => //.
      unfold global_agree in Hg. simpl in Hg.
      unfold is_mut in Hmut. simpl in Hmut. remove_bools_options. subst.
      simpl. unfold store_extension => //=.
      repeat (apply/andP; split) => //=.
      - rewrite take_size. by apply all2_cont_extension_same.
      - by apply all2_tab_extension_same.
      - by apply all2_mem_extension_same.
      - eapply glob_extension_update_nth ; eauto => //=.
        + destruct s. destruct HST as (_ & _ & _ & Hgs & _).
          rewrite List.Forall_forall in Hgs.
          intros g Hin. apply Hgs in Hin as [t Hgt].
          apply AI_const_typing in Hgt as (t0 & Ht0 & _).
          rewrite Ht0. done.
        + unfold glob_extension => //.
          unfold g_mut.
          apply/andP. unfold datatypes.g_val. 
          rewrite - H0. split => //. rewrite Ht => //.
      - rewrite length_is_size take_size. done.
    } 
    split => //.
    eapply store_global_extension_store_typed; eauto;
      destruct s => //=; destruct s' => //=; remove_bools_options => //.
    apply update_list_at_Forall.
    destruct HST as (_ & _ & _ & Hglobs & _) => //.
    eapply List.Forall_impl; last exact Hglobs.
    intros glob Hglob. eapply store_extension_glob_sound.
    exact Hext. exact Hglob.
    exists (tg_t g).
    eapply t_const_ignores_context.
    simpl. rewrite const_const => //.
    eapply store_extension_e_typing.
    exact HST. exact Hext. exact Hconst.
  - (* update memory : store none *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::BI_const (VAL_int32 k); BI_const v; BI_store t None a off] with ([::BI_const (VAL_int32 k); BI_const v] ++ [::BI_store t None a off]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    apply Store_typing in H6.
    destruct H6 as [H7 [H8 H9]]. subst.
    apply concat_cancel_last_n in H7 => //.
    remove_bools_options.
    inversion H4. subst. clear H4.
    assert (store_extension s (upd_s_mem s (update_list_at (s_mems s) i mem'))) as Hext.
    + unfold store_extension => //=.
      repeat (apply/andP; split) => //=.
      * rewrite take_size; by apply all2_cont_extension_same.
      * by apply all2_tab_extension_same.
      * eapply mem_extension_update_nth; eauto => //=. 
        by eapply mem_extension_store; eauto.
      * apply all2_glob_extension_same.
        destruct s; destruct HST as (_ & _ & _ & Hgs & _).
        rewrite List.Forall_forall in Hgs.
        intros g Hin. apply Hgs in Hin as [t Htg].
        apply AI_const_typing in Htg as (t0 & Ht0 & _).
        rewrite Ht0. done.
      * rewrite length_is_size take_size. done.
    + split => //.
      eapply store_memory_extension_store_typed; eauto => //=.
      remember HST as HST2. clear HeqHST2.
      unfold store_typing in HST.
      destruct s => //=.
      destruct HST as (_ & _ & H11 & _ ).
      simpl in H1.
      assert (i < length s_mems)%coq_nat.
      { apply List.nth_error_Some. by rewrite H1. }
      inversion H0; subst. clear H0.
      apply Forall_update => //=; last lias.
      eapply store_mem_agree; eauto.
      by destruct v => //=. 
  - (* store some *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::BI_const (VAL_int32 k); BI_const v; BI_store t (Some tp) a off] with ([::BI_const (VAL_int32 k); BI_const v] ++ [::BI_store t (Some tp) a off]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    apply Store_typing in H6.
    destruct H6 as [H7 [H8 H9]]. subst.
    apply concat_cancel_last_n in H7 => //.
    remove_bools_options.
    inversion H4. subst. clear H4.
    assert (store_extension s (upd_s_mem s (update_list_at (s_mems s) i mem'))) as Hext.
    { unfold store_extension => //=.
      repeat (apply/andP; split) => //=.
      * rewrite take_size; by apply all2_cont_extension_same.
      * by apply all2_tab_extension_same.
      * eapply mem_extension_update_nth; eauto => //=.
        by eapply mem_extension_store; eauto.
      * apply all2_glob_extension_same.
        destruct s; destruct HST as (_ & _ & _ & Hgs & _).
        rewrite List.Forall_forall in Hgs.
        intros g Hin. apply Hgs in Hin as [t Htg].
        apply AI_const_typing in Htg as (t0 & Ht0 & _).
        rewrite Ht0. done.
      * rewrite length_is_size take_size => //. 
    } 
    split => //.
    eapply store_memory_extension_store_typed; eauto => //=.
    remember HST as HST2. clear HeqHST2.
    unfold store_typing in HST.
    destruct s => //=.
    destruct HST as (_ & _ & H11 & _ ).
    simpl in H1.
    assert (i < length s_mems)%coq_nat.
    { apply List.nth_error_Some. by rewrite H1. }
    apply Forall_update => //=; last lias.
    eapply store_mem_agree; eauto.
    by destruct tp => //=. 
  - (* grow_memory *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::BI_const (VAL_int32 c); BI_grow_memory] with ([::BI_const (VAL_int32 c)] ++ [::BI_grow_memory]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    apply Grow_memory_typing in H6.
    destruct H6 as [ts' [H7 [H8 H9]]]. subst.
    apply concat_cancel_last in H9 => //. destruct H9. subst.
    assert (store_extension s (upd_s_mem s (update_list_at (s_mems s) i mem'))) as Hext.
    { unfold store_extension => //=.
      repeat (apply/andP; split) => //=.
      * rewrite take_size; by apply all2_cont_extension_same.
      * by apply all2_tab_extension_same.
      * eapply mem_extension_update_nth; eauto => //=.
        by eapply mem_extension_grow_memory; eauto.
      * apply all2_glob_extension_same.
        destruct s; destruct HST as (_ & _ & _ & Hgs & _).
        rewrite List.Forall_forall in Hgs.
        intros g Hin. apply Hgs in Hin as [t Htg].
        apply AI_const_typing in Htg as (t0 & Ht0 & _).
        rewrite Ht0. done.
      * rewrite length_is_size take_size => //. 
    }
    split => //.
    eapply store_memory_extension_store_typed; eauto => //=.
    remember HST as HST2. clear HeqHST2.
    unfold store_typing in HST.
    destruct s => //=.
    destruct HST as (_ & _ & H11 & _ ).
    simpl in H0.
    assert (i < length s_mems)%coq_nat.
    { apply List.nth_error_Some. by rewrite H0. }
    apply Forall_update => //=; last lias.
    eapply mem_grow_mem_agree; eauto.  
  - (* r_label *)
    eapply lfilled_es_type_exists in HType; eauto.
    destruct HType as [lab' [t1s [t2s HType]]].
    eapply IHHReduce; eauto.
    rewrite upd_label_overwrite in HType. by apply HType.
  - (* r_local *)
    apply Local_typing in HType.
    destruct HType as [ts [H1 [H2 H3]]]. subst.
    inversion H2. inversion H. subst.
    apply upd_label_unchanged_typing in H1.
    eapply IHHReduce => //=; eauto.
Qed.


Lemma store_extension_reduce_strip_empty_context:
  forall s f es s' f' es' tf C,
    upd_label C [::] = empty_context ->
    reduce s f es s' f' es' ->
    e_typing s C es tf ->
    store_typing s ->
    store_extension s s' /\ store_typing s'.
Proof.
  move => s f es s' f' es' tf C HC HReduce.
  generalize dependent tf. generalize dependent C. 
  induction HReduce; try move => C HC tf HType HST; try intros; destruct tf ; (try by split => //; apply store_extension_same) ; (try by split; [apply store_extension_new_cont| apply store_typing_new_cont]); (try by eapply store_extension_upd_cont; eauto).
  - (* Throw *)
    subst s'. split.
    apply store_extension_add_exn. done.
    apply store_typing_add_exn. done.
    apply e_composition_typing in HType as (ts' & ts1 & ts2 & ts3 & -> & -> & Hves & Hthrow).
    convert_et_to_bet.
    apply Throw_typing in Hthrow as (ts'' & t1s' & Hx & ->).
    destruct C; inversion HC; subst.
    destruct x => //.
    
  - (* Contnew *)
    split; [apply store_extension_new_cont| apply store_typing_new_cont] => //.
    econstructor.
    + instantiate (1 := v_to_e_list (default_vals l)).
      apply v_to_e_is_const_list.
    + apply default_vals_typing.
    + subst hh. unfold hfilled, hfill => /=. done.
    + eapply et_composition'.
      apply default_vals_typing.
      rewrite separate1.
      rewrite separate1 in H1. destruct tf0.
      apply e_composition_typing in H1 as (ts & ts1 & ts2 & ts3 & -> & -> & Href & Hcontnew).
      apply AI_ref_typing in Href as (t & Ht & ->).
      apply et_to_bet in Hcontnew; last by constructor.
      apply Contnew_typing in Hcontnew as (ts' & tf & Htypes & Hts1' & ->).
      apply concat_cancel_last in Hts1' as [-> ->].
      simpl in Ht. destruct (List.nth_error _ x) eqn:Hfuncs => //. 
      eapply ety_composition.
      * instantiate (1 := (l ++ [:: _])). apply et_weakening_empty_1.
        eapply ety_ref. rewrite Hfuncs. done. done.
      * eapply ety_a' => /=. constructor => //.
        inversion Ht.
        inversion Htypes; subst.
        destruct i; first by     destruct C; inversion HC; subst; destruct i.
        inversion H4; subst.
        inversion H; subst.
        inversion Ht.
        apply bet_call_reference => //.
  - (* resume *)
    split; [eapply store_extension_upd_cont| eapply store_typing_upd_cont]; try exact H2; try done.
  - (* Suspend *)
    split; [apply store_extension_new_cont| apply store_typing_new_cont] => //.
    apply Prompt_typing in HType as ((*ts2' &*) -> & Hclauses & HType).
    eapply hfilled_typing in HType as (tf' & (* i' & *) C' & HType & (* HC' & *) Hfillback).
    2: exact H2.
    destruct tf' as [t1s' t2s'].
    subst x.
    apply AI_suspend_desugared_typing in HType as (t1s'' & t2s'' & -> & Hvs & Htags).

    rewrite H0 in Htags. inversion Htags. subst.
    edestruct (hfilled_change (* (v_to_e_list vs') *) (v_to_e_list (default_vals t2s''))) as [LI' HLI']; first exact H2.
    by left.
    econstructor.
    3: exact HLI'. apply v_to_e_is_const_list.
    apply default_vals_typing.
    eapply Hfillback in HLI'.
    eapply store_extension_e_typing. exact HST.
    apply store_extension_new_cont.
    done.
    exact HLI'.   
    apply et_weakening_empty_1.
    apply default_vals_typing.
  - (* Switch *)
    split.
    + eapply store_extension_trans; cycle 1.
      * eapply store_extension_upd_cont.
        -- done.
        -- exact H1.
        -- done.
      * eapply store_extension_new_cont.
        eapply store_typing_upd_cont. done.
        exact H1. done.
      * intros g Hin Habs.
        destruct s. destruct H5 as (_ & _ & _ & Hgs & _).
        simpl in *.
        rewrite List.Forall_forall in Hgs.
        apply Hgs in Hin as [t Ht].
        apply AI_const_typing in Ht as (t0 & Ht0 & _).
        rewrite Ht0 in Habs. done.
    + apply store_typing_new_cont.
      eapply store_typing_upd_cont; try exact H1; try done.
      apply c_typing_new_cont; try exact H1; try done.
      eapply store_typing_upd_cont. done. eauto. done.
      eapply c_typing_upd_cont. done. eauto. done.
      destruct tf0.
      apply Prompt_typing in H4 as (-> & Hclauses & HType).
      eapply hfilled_typing in HType as (tfn & C' & HType & Hfillback).
      2: exact H2.
      destruct tfn as [t1sn t2sn].
      destruct x.
      apply AI_switch_desugared_typing in HType as (ts'' & tx & ty & cont & Htags & Hconts & Hcont & Hvs & Htf & ->).
      inversion Htf; subst l l0.
      inversion H0; subst ts''.
      apply concat_cancel_last in H6 as [-> Htypes'].
      inversion Htypes'; subst tf'.
      clear Htypes' Htf.
      rewrite List.Forall_forall in Hclauses.
      apply firstx_continuation_switch_In in H.
      apply Hclauses in H.
      inversion H; subst.
      rewrite H8 in Htags.
      inversion Htags; subst t2s.
      edestruct (hfilled_change (v_to_e_list (default_vals ty))) as [LI'' HLI'']; first exact H2.
      by left.
      econstructor.
      3: exact HLI''.
      apply v_to_e_is_const_list.
      apply default_vals_typing.
      eapply Hfillback in HLI''.
      exact HLI''.
      apply et_weakening_empty_1.
      apply default_vals_typing. 

  - (* Contbind *)
    split.
    + eapply store_extension_trans; cycle 1.
      * eapply store_extension_upd_cont.
        -- done.
        -- exact H3.
        -- done. 
      * eapply store_extension_new_cont.
        eapply store_typing_upd_cont. done.
        exact H3. done.
      * intros g Hin Habs.
        destruct s. destruct HST as (_ & _ & _ & Hgs & _).
        simpl in *.
        rewrite List.Forall_forall in Hgs.
        apply Hgs in Hin as [t Ht].
        apply AI_const_typing in Ht as (t0 & Ht0 & _).
        rewrite Ht0 in Habs. done.
    + apply store_typing_new_cont.
      eapply store_typing_upd_cont; try exact H3; try done.
      eapply c_typing_new_cont; try exact H3; try done.
      eapply store_typing_upd_cont. done. eauto. done.
      eapply c_typing_upd_cont. done. eauto. done.
      apply e_composition_typing in HType as (ts' & t1s' & t2s' & t3s & -> & -> & Hvst & Hrest).
      apply const_es_exists in H as [vs' ->].
      apply Const_list_typing in Hvst as (tsv & Hvs' & -> & Hvstype).
      rewrite separate1 in Hrest.
      apply e_composition_typing in Hrest as (ts'' & t1s'' & t2s'' & t3s' & Ht & -> & Hreft & Hbindt).
      apply AI_ref_cont_typing in Hreft as (t & Hcont & ->).
      convert_et_to_bet.
      apply Contbind_typing in Hbindt as (tsnew & t0s & t1snew & t2snew & H0' & H1' & Ht' & ->).
      destruct i; first by     destruct C; inversion HC; subst; destruct i.
      destruct i'; first by     destruct C; inversion HC; subst; destruct i.
      inversion H0'; inversion H0; inversion H1; inversion H1';
        subst.
      inversion H7; subst t1snew t2snew.
      inversion H5. apply concat_cancel_last_n in H4; last done.
      remove_bools_options. subst.
      rewrite catA in Ht'.
      apply concat_cancel_last in Ht' as [-> ->].
      rewrite catA in Ht.
      apply concat_cancel_last_n in Ht; last first.
      { do 2 rewrite length_is_size in H2. rewrite H2.
        unfold v_to_e_list. rewrite size_map.
        erewrite <- size_map. instantiate (1 := Some). rewrite - Hvs'.
        rewrite size_map. done. }
      remove_bools_options. subst.
      unfold store_typing in HST.
      destruct s.
      destruct HST as (_ & _ & _ & _ & Hconts & _).
      apply List.nth_error_In in H3.
      edestruct List.Forall_forall as [Hforall _].
      eapply Hforall in Hconts; last exact H3.
      eapply c_typing_hhplug. exact Hconts.
      eapply t_const_ignores_context. apply v_to_e_is_const_list.
      exact Hvstype. 
  - (* Resume_throw *)
    apply e_composition_typing in HType as (ts' & t1s' & t2s' & t3s & -> & -> & Hves & Hrefcontthrow).
    subst ves.
    apply Const_list_typing in Hves as (tvs & Htvs & -> & Hconst).
    rewrite separate1 in Hrefcontthrow.
    apply e_composition_typing in Hrefcontthrow as (ts'' & t1s'' & t2s'' & t3s' & Htypes & -> & Hrefcont & Hresumethrow).
    apply AI_ref_cont_typing in Hrefcont as (tref & Htref & ->).
    convert_et_to_bet.
    apply Resume_throw_typing in Hresumethrow
        as (ts''' & t1s''' & t2s''' & t0s & Hgettype & Htags & Hclauses_& Htypes' & ->).
        destruct C; inversion HC; subst.
    destruct x => //. 

  - (* update glob *)
    rewrite (separate1 (AI_const v)) in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]]. subst.
    apply et_to_bet in H4; auto_basic. simpl in H4.
    apply Set_global_typing in H4 as (g & t & Hg & <- & Hmut & -> & Hi).
        destruct C; inversion HC; subst.
    destruct i => //. 

  - (* update memory : store none *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::BI_const (VAL_int32 k); BI_const v; BI_store t None a off] with ([::BI_const (VAL_int32 k); BI_const v] ++ [::BI_store t None a off]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    apply Store_typing in H6.
    destruct H6 as [H7 [H8 H9]].
        destruct C; inversion HC; subst.
    done.

  - (* store some *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::BI_const (VAL_int32 k); BI_const v; BI_store t (Some tp) a off] with ([::BI_const (VAL_int32 k); BI_const v] ++ [::BI_store t (Some tp) a off]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    apply Store_typing in H6.
    destruct H6 as [H7 [H8 H9]].
        destruct C; inversion HC; subst.
    done.

  - (* grow_memory *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::BI_const (VAL_int32 c); BI_grow_memory] with ([::BI_const (VAL_int32 c)] ++ [::BI_grow_memory]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    apply Grow_memory_typing in H6.
    destruct H6 as [ts' [H7 [H8 H9]]].
        destruct C; inversion HC; subst.
    done. 

  - (* r_label *)
    eapply lfilled_es_type_exists in HType; eauto.
    destruct HType as [lab' [t1s [t2s HType]]].
    eapply IHHReduce.
    2: exact HType.
    done.
    done.
  - (* r_local *)
    apply Local_typing in HType.
    destruct HType as [ts [H1 [H2 H3]]]. subst.
    
    inversion H2. inversion H. subst.
    apply upd_label_unchanged_typing in H1.
    eapply store_extension_reduce.
    exact HReduce. exact H9. exact H1. done.
Qed.

Lemma store_extension_reduce_empty_context:
  forall s f es s' f' es' tf,
    reduce s f es s' f' es' ->
    e_typing s empty_context es tf ->
    store_typing s ->
    store_extension s s' /\ store_typing s'.
Proof.
  intros.
  eapply store_extension_reduce_strip_empty_context; eauto.
  done.
Qed. 
  

(* Lemma result_e_type: forall r ts s C,
    result_types_agree s ts r ->
    e_typing s C (result_to_stack r) (Tf [::] ts).
Proof.
  move => r ts s C HResType.
  destruct r => //=; last by apply ety_trap.
  generalize dependent ts.
  induction l => //=; move => ts HResType; simpl in HResType.
  - destruct ts => //=.
    apply ety_a' => //=.
    by apply bet_empty.
  - destruct ts => //=.
    simpl in HResType.
    remove_bools_options.
    unfold types_agree in H.
    rewrite -cat1s.
    eapply et_composition'; eauto => //=; last first.
    + remove_bools_options. subst.
      rewrite -cat1s.
      replace (typeof s a :: ts) with ([::typeof s a] ++ ts) => //.
      apply ety_weakening.
      by apply IHl.
    + move/eqP in H. destruct a => //=.
      * apply ety_a'; auto_basic.
        by apply bet_const.
      * destruct v0 => //.
        -- apply ety_a'; auto_basic.
           constructor => //.
        -- simpl. simpl in H.
           destruct (List.nth_error _ _) eqn:Hf => //.
           ++ eapply ety_ref. exact Hf. 
        
Qed. *)


(*Lemma typeof_new_cont s k cont v:
  List.nth_error (s_conts s) k = None ->
  typeof s v = typeof (upd_s_cont s k cont) v. *)

(*  Next two lemmas are true but no longer useful
Lemma new_cont_extension s k cont:
  (forall x,  List.In x (s_globals s) -> typeof s (g_val x) <> T_ref T_corruptref) ->
  List.nth_error (s_conts s) k = None ->
  store_extension s (upd_s_cont s k cont).
Proof.
  intros Hcorrupt Hk.
  repeat (apply/andP; split => //); destruct s => /=.
  - unfold replace_nth_cont.
    rewrite set_nth_new; last by apply List.nth_error_None in Hk; lias.
    rewrite take_size_cat => //. by apply all2_cont_extension_same.
  - by apply all2_tab_extension_same.
  - by apply all2_mem_extension_same.
  - by apply all2_glob_extension_same.
Qed.

Lemma upd_cont_extension s k cont cont':
  (forall x,  List.In x (s_globals s) -> typeof s (g_val x) <> T_ref T_corruptref) -> 
  List.nth_error (s_conts s) k = Some cont ->
  typeof_cont cont = typeof_cont cont' ->
  store_extension s (upd_s_cont s k cont').
Proof.
  intros Hcorrupt Hk Hcont.
  repeat (apply/andP; split => //); destruct s => /=.
  - clear Hcorrupt. unfold replace_nth_cont. simpl in Hk.
    generalize dependent k.
    induction s_conts; intros k Hk => //=; first by rewrite take0.
    destruct k => //=.
    + inversion Hk; subst. unfold cont_extension. rewrite Hcont.
      apply/andP; split => //. rewrite take_size. by apply all2_cont_extension_same.
    + apply/andP; split => //. unfold cont_extension. done.
      apply IHs_conts. done.
  - by apply all2_tab_extension_same.
  - by apply all2_mem_extension_same.
  - by apply all2_glob_extension_same.
Qed. 
*)

Lemma nth_error_set_nth {A} i l k x (y: A) v:
  i < length l ->
  List.nth_error (set_nth x l k y) i = Some v ->
  List.nth_error l i = Some v \/ i = k /\ v = y.
Proof.
  generalize dependent i. generalize dependent k.
  induction l => //=.
  intros k i Hi Hv.
  destruct i => //=.
  - destruct k => //=.
    + simpl in Hv. inversion Hv; by right.
    + simpl in Hv. by left.
  - destruct k => //=.
    + simpl in Hv. by left.
    + simpl in Hv. apply IHl in Hv as [? | [-> ->]] => //.
      by left. by right.
Qed. 
      
(*
Lemma in_set_nth {A} (x: A) l y k x':
  List.In x (set_nth y l k x') ->
  k < length l ->
  List.In x l \/ x = x'.
Proof.
  generalize dependent k.
  induction l; intros k Hin Hk.
  - simpl in Hk. lias. 
  - destruct k.
    + destruct Hin as [? | ?]. by right. by left; right.
    + destruct Hin as [? | ?]. by left; left.
      destruct (IHl k H) as [? | ?]. simpl in Hk. lias.
      by left; right. by right. 
Qed. *)

(*
Lemma typing_corrupt s C es t1s t2s:
  (List.In (T_ref T_corruptref) t1s \/ List.In (T_ref T_corruptref) t2s) ->
  e_typing s C es (Tf t1s t2s) ->
  False.
Proof.
  intros Hcorrupt Htype.
  remember (Tf t1s t2s) as tf.
  induction Htype.
  - induction H;
      try by  inversion Heqtf; subst;
      destruct Hcorrupt as [Habs | Habs] => //;
        inversion Habs as [Habs' | Habs'];
                                           inversion Habs'.
    + 
      inversion Habs. inversion Habs as [Habs' | Habs']. destruct v => //.  *)



Lemma length_set_nth {A} x (v: A) i l:
  i < length l ->
  length (set_nth x l i v) = length l.
Proof.
  generalize dependent i.
  induction l => //=.
  intros i Hi.
  destruct i => //=.
  rewrite IHl => //.
Qed.


Lemma t_preservation_locals: forall s f es s' f' es' C lab ret t1s t2s ts Ctyp,
    reduce s f es s' f' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s f.(f_inst) C ->
    Ctyp = upd_label (upd_local_return C (tc_local C ++ ts) ret) lab ->
    e_typing s Ctyp es (Tf t1s t2s) ->
    List.Forall2 (fun v tl => e_typing s empty_context [:: AI_const v] (Tf [::] [::tl])) (f_locs f) ts ->
    List.Forall2 (fun v tl => e_typing s' empty_context [:: AI_const v] (Tf [::] [::tl])) (f_locs f') ts.
Proof.
  move => s f es s' f' es' C lab ret t1s t2s ts Ctyp HReduce HST1 HST2 HIT1 -> HType Hlocs.
  assert (store_extension s s') as Hextension.
  { eapply store_extension_reduce in HReduce as [? _] => //.
    exact HIT1. exact HType. } 
  generalize dependent t2s. generalize dependent t1s.
  generalize dependent lab. 
  induction HReduce => //;
     let t1s := fresh "t1s" in let t2s := fresh "t2s" in move => lab t1s t2s HType.
  all: try by
    let v := fresh "v" in
    eapply List.Forall2_impl; last exact Hlocs;
    intros v t Htyp;
    eapply t_const_ignores_context; last exact Htyp;
    unfold const_list => /=; rewrite const_const.
  all: try by
    let v := fresh "v" in
    let t := fresh "t" in
    eapply List.Forall2_impl; last exact Hlocs;
    intros v t Htyp;
    eapply t_const_ignores_context; first (by unfold const_list; simpl; rewrite const_const);
    eapply store_extension_e_typing; last exact Htyp; done.
  - rewrite Forall2_forall.
    rewrite Forall2_forall in Hlocs.
    destruct Hlocs as [Hlen Hloctyp].
    split.
    + rewrite - Hlen H1.
      rewrite length_set_nth => //. 
    + intros j w t Hw Ht.
      rewrite H1 in Hw.
      apply nth_error_set_nth in Hw as [Hw | [-> ->]].
      3:{ rewrite Hlen. apply nth_error_lt_Some in Ht. done. } 
      * eapply t_const_ignores_context; last eapply Hloctyp; eauto.
        unfold const_list; simpl; rewrite const_const. done.
      * rewrite separate1 in HType.
        apply e_composition_typing in HType as (t0s' & t1s' & t2s' & t3s' & -> & -> & Hv & Hsetlocal).
        apply AI_const_typing in Hv as (tv & Htv & -> & Hv).
        eapply t_const_ignores_context;
          first by unfold const_list; simpl; rewrite const_const.
        replace t with tv; first exact Hv.
        convert_et_to_bet.
        apply Set_local_typing in Hsetlocal as (tv' & Htvs' & Htypes & Hi).
        apply concat_cancel_last in Htypes as [-> ->].
        simpl in Htvs'.
        apply inst_t_context_local_empty in HIT1.
        rewrite HIT1 in Htvs'.
        rewrite Htvs' in Ht. inversion Ht; done.
  - assert (exists lab' t1s' t2s', e_typing s (upd_label (upd_label (upd_local_return C (tc_local C ++ ts) ret) lab) lab') es (Tf t1s' t2s')) as (? & ? & ? & ?); first eapply lfilled_es_type_exists; eauto.
(*    rewrite upd_label_overwrite in H1.
    eapply IHHReduce in H1; eauto.
(*    + eapply List.Forall2_impl; last exact H1.
      intros v tv Hv.
      eapply t_const_ignores_context; last exact Hv.
      unfold const_list; simpl; rewrite const_const => //. *)
    + eapply List.Forall2_impl; last exact Hlocs.
      intros v tv Hv.
      eapply t_const_ignores_context; last exact Hv.
      unfold const_list; simpl; rewrite const_const => //.  *)
Qed.



(*

Lemma t_preservation_vs_type: forall s f es s' f' es' C C' lab ret t1s t2s ts,
(*    (forall x0 : global,
        List.In x0 (s_globals s) -> typeof s (g_val x0) <> None) -> *)
    reduce s f es s' f' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s f.(f_inst) C ->
    inst_typing s' f.(f_inst) C' ->
    map (typeof s) f.(f_locs) = map Some ts ->
    e_typing s (upd_label (upd_local_return C (tc_local C ++ ts) ret) lab) es (Tf t1s t2s) ->
(*    (forall v, List.In v f.(f_locs) -> typeof s v <> None) -> *)
    map (typeof s) f.(f_locs) = map (typeof s') f'.(f_locs) (* /\
      forall v, List.In v f'.(f_locs) -> typeof s' v <> None *).
Proof.
  move => s f es s' f' es' C C' lab ret t1s t2s ts (* Hcorruptg *) HReduce HST1 HST2 HIT1 HIT2 Hts HType.
  assert (store_extension s s') as Hextension.
  { eapply store_extension_reduce in HReduce as [? _] => //.
    exact HIT1. exact HType. } 
  generalize dependent t2s. generalize dependent t1s.
  generalize dependent lab. 
  induction HReduce => //;
     let t1s := fresh "t1s" in let t2s := fresh "t2s" in move => lab t1s t2s HType.
  - apply map_equiv. intros v Hin.
    destruct (@typeof_extension s (new_cont s (Cont_hh tf hh)) v) => //.
    exfalso. apply (map_in (typeof s)) in Hin. destruct H1 as [Habs _].
    rewrite Habs Hts in Hin. clear -Hin. induction ts => //. destruct Hin => //. 
  - apply map_equiv. intros v Hin.
    destruct (@typeof_extension s (upd_s_cont s k (Cont_dagger (Tf t1s t2s))) v) => //.
    exfalso. apply (map_in (typeof s)) in Hin. destruct H4 as [Habs _].
    rewrite Habs Hts in Hin. clear -Hin. induction ts => //. destruct Hin => //. 
  - apply map_equiv. intros v Hin.
    destruct (@typeof_extension s (new_cont s (Cont_hh (Tf t2s [::]) hh)) v) => //.
    exfalso. apply (map_in (typeof s)) in Hin. destruct H4 as [Habs _].
    rewrite Habs Hts in Hin. clear -Hin. induction ts => //. destruct Hin => //. 
  - apply map_equiv. intros v Hin.
    destruct (typeof_extension v Hextension) => //.
    exfalso. apply (map_in (typeof s)) in Hin. destruct H4 as [Habs _].
    rewrite Habs Hts in Hin. clear -Hin. induction ts => //. destruct Hin => //. 
  - apply map_equiv. intros v Hin.
    destruct (@typeof_extension s (upd_s_cont s k (Cont_dagger ft)) v) => //.
    exfalso. apply (map_in (typeof s)) in Hin. destruct H5 as [Habs _].
    rewrite Habs Hts in Hin. clear -Hin. induction ts => //. destruct Hin => //. 
  - (* convert_et_to_bet. *)
    rewrite (separate1 (AI_const _)) in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [? [? [? Hbet]]]]]]]; subst.
    apply et_to_bet in Hbet; auto_basic.
    apply Set_local_typing in Hbet as [t [Hnth [Hcat _]]].
    apply AI_const_typing in H4 as (t' & Ht & -> & Hconst).
    apply concat_cancel_last in Hcat as [-> <-].
    replace (tc_local C) with ([::]: list value_type) in *; last by symmetry; eapply inst_t_context_local_empty; eauto.
    rewrite H1.
    rewrite set_nth_map => //.
    rewrite set_nth_same_unchanged => //.
    rewrite Hts Ht. simpl in Hnth.
    clear - Hnth. generalize dependent i.
    induction ts; destruct i => //=.
    by intros ->. apply IHts.
  - apply map_equiv. intros vl Hin.
    destruct (@typeof_extension s s' vl) => //.
    exfalso. apply (map_in (typeof s)) in Hin. destruct H0 as [Habs _].
    rewrite Habs Hts in Hin. clear -Hin. induction ts => //. destruct Hin => //. 
  - assert (exists lab' t1s' t2s', e_typing s (upd_label (upd_label (upd_local_return C (tc_local C ++ ts) ret) lab) lab') es (Tf t1s' t2s')); first eapply lfilled_es_type_exists; eauto.
    destruct H1 as [lab' [t1s' [t2s' Het]]].
    rewrite upd_label_overwrite in Het.
    by eapply IHHReduce; eauto.
  - apply map_equiv. intros v Hv.
    destruct (@typeof_extension s s' v) as [-> | [Habs _]] => //.
    exfalso. apply (map_in (typeof s)) in Hv. 
    rewrite Habs Hts in Hv. clear -Hv. induction ts => //. destruct Hv => //. 
Qed. *)

Lemma inst_typing_func: forall s i j C a x,
  inst_typing s i C ->
  List.nth_error i.(inst_funcs) j = Some a ->
  List.nth_error (tc_func_t C) j = Some x ->
  exists cl, List.nth_error s.(s_funcs) a = Some cl.
Proof.
  move => s i j C a x HIT HNth1 HNth2.
  destruct s; destruct i; destruct C; destruct tc_local; destruct tc_label; destruct tc_return; unfold inst_typing, typing.inst_typing in * => //=; remove_bools_options; simpl in * => //=.
  unfold typing.functions_agree in H4.
  eapply all2_projection in H4; eauto.
  remove_bools_options; eauto.
Qed.

Lemma typeof_default ts s:
  map (typeof s) (default_vals ts) = map Some ts.
Proof.
  induction ts => //=.
  f_equal => //=. destruct a => //=. destruct n => //=. destruct r => //=.
Qed.

Lemma forall_values_type vs ts s C:
  List.Forall2 (fun v t => e_typing s C [:: AI_const v] (Tf [::] [:: t])) vs ts <->
    e_typing s C (v_to_e_list vs) (Tf [::] ts).
Proof.
  generalize dependent ts. induction vs => //=.
  - intros ts. destruct ts => //=.
    + split; last by intros; constructor. intros.
      apply ety_a'; first by constructor.
      constructor.
    + split; try by intros H; inversion H.
      intros H. apply empty_typing in H. done.
  - intros ts; destruct ts => //=.
    + split; try by intros H; inversion H.
      intros H. rewrite separate1 in H.
      apply e_composition_typing in H as (l1 & l2 & l3 & l4 & Hl & Hl' & Ha & Hrest).
      destruct l1, l2, l3 => //.
      apply AI_const_typing in Ha as (ta & Ha & -> & _).
      apply Const_list_typing in Hrest as (? & _ & ? & _) => //.
    + split.
      * intros H. inversion H; subst.
        rewrite separate1. eapply et_composition'.
        exact H3. rewrite (separate1 v ts).
        apply et_weakening_empty_1.
        apply IHvs => //.
      * intros H. rewrite separate1 in H.
        apply e_composition_typing in H as (t0s & t1s & t2s & t3s & Hts & Hts' & Ha & Hrest).
        destruct t0s, t1s => //.
        simpl in Hts'. subst t2s.
        apply AI_const_typing in Ha as (ta & Hta & -> & Ha).
        apply Const_list_typing in Hrest as (ts0 & Hts0 & Hts' & Hrest).
        inversion Hts'; subst.
        constructor => //.
        apply IHvs => //.
Qed. 

Lemma firstx_clause_typing hs s i l C:
  firstx_exception hs (Mk_tagidx i) = Clause_label l ->
  List.Forall (exception_clause_typing s C) hs ->
  (exists (* i0 *) ts0, (* List.nth_error (inst_tags inst) i0 = Some i /\ *)
              List.nth_error (s_tags s) i = Some (Tf ts0 [::]) /\
               List.nth_error (tc_label C) l = Some ts0) \/
    List.nth_error (tc_label C) l = Some [::] .
Proof.
  induction hs => //=. 
  destruct a => //=.
  + (* destruct (List.nth_error _ i0) eqn:Hi0 => //=. *)
    destruct (_ == t) eqn:Hit => //.
      * move/eqP in Hit. subst t. 
        intros Hl Hclauses.
        inversion Hl; subst i0.
        inversion Hclauses; subst.
        inversion H1; subst.
        left. exists ts. repeat split => //.
      * intros Hl Hclauses.
        apply IHhs => //. inversion Hclauses; subst.
        done.
  + destruct (_ == t) eqn:Hit => //.
    intros Hl Hclauses.
    apply IHhs => //. inversion Hclauses; subst.
    done.
  + intros Hl Hclauses.
    inversion Hl; subst i0.
    inversion Hclauses; subst.
    inversion H1; subst.
    right. done.
Qed. 

Lemma firstx_clause_typing_ref hs s i l C:
  firstx_exception hs (Mk_tagidx i) = Clause_label_ref l ->
  List.Forall (exception_clause_typing s C) hs ->
  (exists ts0, 
      List.nth_error (s_tags s) i = Some (Tf ts0 [::]) /\
        List.nth_error (tc_label C) l = Some (ts0 ++ [:: T_ref T_exnref])) \/
    List.nth_error (tc_label C) l = Some [:: T_ref T_exnref] .
Proof.
  induction hs => //=.
  destruct a => //=.
  + destruct (_ == t) eqn:Hit => //.
    intros Hl Hclauses.
    apply IHhs => //. inversion Hclauses; subst.
    done.
  + destruct (_ == t) eqn:Hit => //.
    * move/eqP in Hit. subst t.
      intros Hl Hclauses.
      inversion Hl; subst i0.
      inversion Hclauses; subst.
      inversion H1; subst.
      left. exists ts. repeat split => //.
    * intros Hl Hclauses.
      apply IHhs => //. inversion Hclauses; subst.
      done. 
  + intros Hl Hclauses.
    inversion Hl; subst i0.
    inversion Hclauses; subst.
    inversion H1; subst.
    right. done.
Qed.

Lemma firstx_clause_typing_cont hs s i l C ts:
  firstx_continuation_suspend hs (Mk_tagidx i) = Some l ->
  List.Forall (fun h => continuation_clause_typing s C h ts) hs ->
  exists ts1 ts2,
      List.nth_error (s_tags s) i = Some (Tf ts1 ts2) /\
      List.nth_error (tc_label C) l = Some (ts1 ++ [::T_ref (T_contref (Tf ts2 ts))]).
Proof.
  induction hs => //=.
  destruct a => //=.
  - destruct (_ == t) eqn:Hit.
    + move/eqP in Hit. subst t. 
      intros Hl Htyp.
      inversion Hl; subst i0.
      inversion Htyp; subst. inversion H1; subst.
      exists t1s', t2s'.
      repeat split => //.
    + intros Hl Htyp.
      apply IHhs => //.
      inversion Htyp; subst.
      done.
  - intros Hl Htyp. apply IHhs => //.
    inversion Htyp; subst. done.
Qed. 

(*
Lemma lfilled_preservation s f es s' f' es' n lh LI LI' C tf:
  store_typing s ->
  store_extension s s' ->
  reduce s f es s' f' es' ->
  (forall tf' C, e_typing s C es tf' -> e_typing s' C es' tf') ->
  lfilled n lh es LI ->
  lfilled n lh es' LI' ->
  e_typing s C LI tf ->
  e_typing s' C LI' tf.
Proof.
  generalize dependent n. generalize dependent tf.
  generalize dependent LI. generalize dependent LI'.
  generalize dependent C.
  induction lh; unfold lfilled, lfill; fold lfill;
    intros C LI' LI [tx ty] n0 HST Hsext Hred IH HLI HLI' Htyp.
  - destruct n0 => //.
    destruct (const_list l) eqn:Hconst => //.
    move/eqP in HLI. subst LI.
    move/eqP in HLI'. subst LI'.
    apply e_composition_typing in Htyp as (ts & t1s & t2s & t3s & -> & -> & Hl & Hesl0).
    apply e_composition_typing in Hesl0 as (ts' & t1s' & t2s' & t3s' & -> & -> & Hes & Hl0).
    apply ety_weakening.
    eapply et_composition'.
    eapply store_extension_e_typing. exact HST. exact Hsext.
    exact Hl.
    apply ety_weakening.
    eapply et_composition'; last first.
    eapply store_extension_e_typing. exact HST. exact Hsext.
    exact Hl0.
    apply IH. exact Hes.
  - destruct n0 => //.
    destruct (const_list _) eqn:Hconst => //.
    destruct (lfill _ _ es) eqn:Hfill => //.
    destruct (lfill _ _ es') eqn:Hfill' => //.
    move/eqP in HLI; subst LI.
    move/eqP in HLI'; subst LI'.
    apply e_composition_typing in Htyp as (ts & t1s & t2s & t3s & -> & -> & Hl & Hlabl1).
    rewrite separate1 in Hlabl1.
    apply e_composition_typing in Hlabl1 as (ts' & t1s' & t2s' & t3s' & -> & -> & Hlab & Hl1).
    apply Label_typing in Hlab as (tsl0 & t4s & -> & Hl0 & Hl2 & <-).
    apply ety_weakening.
    eapply et_composition'.
    eapply store_extension_e_typing. exact HST. exact Hsext.
    exact Hl.
    apply ety_weakening. rewrite separate1.
    eapply et_composition'; last first.
    eapply store_extension_e_typing. exact HST. exact Hsext.
    exact Hl1.
    apply et_weakening_empty_1.
    eapply ety_label; last done.
    eapply store_extension_e_typing. exact HST. exact Hsext.
    exact Hl0.
    eapply IHlh. exact HST. exact Hsext. exact Hred.
    exact IH. unfold lfilled. instantiate (2 := n0).
    rewrite Hfill. done.
    unfold lfilled. rewrite Hfill'. done.
    exact Hl2.
A dmitted. *)

Lemma exception_clause_desugar_typing s inst C cs csd:
  (inst_typing s inst (strip C) \/ upd_label C [::] = empty_context) ->
  List.Forall (exception_clause_identifier_typing C) cs ->
  map (desugar_exception_clause inst) cs = map Some csd ->
  List.Forall (exception_clause_typing s C) csd.
Proof.
  move:csd.
  induction cs; destruct csd => //=.
  intros HC Htyp Hcsd.
  inversion Hcsd.
  inversion Htyp; subst.
  constructor; last by apply IHcs.
  inversion H3; subst.
  all: simpl in H0.
  1-2: destruct (List.nth_error _ x) eqn:Hx => //.
  all: inversion H0; subst e.
  all: econstructor; eauto.
  all: destruct HC as [HC | HC];
    last by destruct C; inversion HC; subst; destruct x.
  all: apply inst_typing_tags in HC as Htags.
  all: apply all2_Forall2 in Htags.
  all: eapply Forall2_nth_error in Htags as (v & Hv & Hvag).
  all: try exact Hx.
  all: rewrite H in Hv.
  all: inversion Hv; subst v.
  all: unfold tag_agree in Hvag.
  all: destruct (List.nth_error _ t) => //.
  all: move/eqP in Hvag.
  all: by subst f. 
Qed. 

Lemma continuation_clause_desugar_typing s inst C cs csd ts:
  (inst_typing s inst (strip C) \/ upd_label C [::] = empty_context) ->
  List.Forall (fun h => continuation_clause_identifier_typing C h ts) cs ->
  map (desugar_continuation_clause inst) cs = map Some csd ->
  List.Forall (fun h => continuation_clause_typing s C h ts) csd.
Proof.
  move:csd.
  induction cs; destruct csd => //=.
  intros HC Htyp Hcsd.
  inversion Hcsd.
  inversion Htyp; subst.
  constructor; last by apply IHcs.
  inversion H3; subst.
  all: simpl in H0.
  all: destruct (List.nth_error _ x) eqn:Hx => //.
  all: inversion H0; subst c.
  all: econstructor; eauto.
  all: destruct HC as [HC | HC];
    last by destruct C; inversion HC; subst; destruct x.
  all: apply inst_typing_tags in HC as Htags.
  all: apply all2_Forall2 in Htags.
  all: eapply Forall2_nth_error in Htags as (v & Hv & Hvag); last exact Hx.
  all: rewrite H in Hv.
  all: inversion Hv; subst v.
  all: unfold tag_agree in Hvag.
  all: destruct (List.nth_error _ t) => //.
  all: move/eqP in Hvag.
  all: by subst f. 
Qed. 



  Lemma t_preservation_strip_empty_context:
  forall s f es s' f' es', 
  reduce s f es s' f' es' ->
  (forall C t1s t2s,
    upd_label C [::] = empty_context ->
    store_typing s ->
    store_typing s' ->
    store_extension s s' ->
    e_typing s C es (Tf t1s t2s) ->
    e_typing s' C es' (Tf t1s t2s)) /\ 
      forall C t1s t2s lab ret ts,
    store_typing s ->
    store_typing s' ->
    store_extension s s' ->
    inst_typing s f.(f_inst) C ->
    inst_typing s' f.(f_inst) C ->
    List.Forall2 (fun v tv => e_typing s empty_context [:: AI_const v] (Tf [::] [::tv]))
                 (f_locs f) ts ->
    e_typing s (upd_label (upd_local_return C (tc_local C ++ ts) ret) lab) es (Tf t1s t2s) ->
    e_typing s' (upd_label (upd_local_return C (tc_local C ++ ts) ret) lab) es' (Tf t1s t2s).
Proof.
  move => s f es s' f' es' HReduce.
  induction HReduce.
  
  1-41,43: split;
    [ intros C ty tx HC HST1 HST2 Hsext HType
    |
      intros C ty tx lab ret tslocs HST1 HST2 Hsext HIT1 HIT2 Hts HType
    ]; subst; try eauto; try by apply ety_trap
  .
  
  - (* reduce_simple *)
    eapply t_simple_preservation_strip_empty_context.
    exact HC.
    exact HType. exact H.
  - (* reduce_simple *)
    by eapply t_simple_preservation; eauto.
  - (* Ref_func *)
    convert_et_to_bet.
    apply Ref_func_typing in HType as (t & Hfuncs & ->).
    simpl in Hfuncs.
    destruct C; inversion HC; subst.
    destruct x => //.
  - (* Ref_func *)
    convert_et_to_bet.
    apply Ref_func_typing in HType as (t & Hfuncs & ->).
    simpl in Hfuncs.
    apply et_weakening_empty_1.
    eapply inst_typing_func in HIT1 as [cl Hcl]; eauto.
    econstructor; eauto.
    assert (t = cl_type cl) as ->; first by eapply tc_func_reference1; eauto.
    done.
  - (* Call *)
    convert_et_to_bet.
    apply Call_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [H1 [H2 [H3 H4]]]]]].
    destruct C; inversion HC; subst.
    destruct i => //.
  - (* Call *)
    convert_et_to_bet.
    apply Call_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [H1 [H2 [H3 H4]]]]]].
    subst. simpl in H1. simpl in H2.
    apply ety_weakening.
    eapply inst_typing_func in HIT1; eauto. destruct HIT1 as [cl HNthFunc].
    eapply ety_invoke; eauto.
    assert ((Tf t1s' t2s') = cl_type cl) as HFType; first by eapply tc_func_reference1; eauto.
    rewrite HFType.
    done.
    
  - (* Call_indirect *)
    convert_et_to_bet.
    replace [::BI_const (VAL_int32 c); BI_call_indirect i] with ([::BI_const (VAL_int32 c)] ++ [::BI_call_indirect i]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1' [H2 [H3 H4]]]]]]].
    subst.
    invert_be_typing.
    apply Call_indirect_typing in H4.
    destruct H4 as [tn [tm [ts'' [H5 [H6 [H7 H9]]]]]].
    destruct C; inversion HC; subst.
    destruct i => //.
  - (* Call_indirect *)
    convert_et_to_bet.
    replace [::BI_const (VAL_int32 c); BI_call_indirect i] with ([::BI_const (VAL_int32 c)] ++ [::BI_call_indirect i]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1' [H2 [H3 H4]]]]]]].
    subst.
    invert_be_typing.
    apply Call_indirect_typing in H4.
    destruct H4 as [tn [tm [ts'' [H5 [H6 [H7 H9]]]]]].
    rewrite catA in H7. apply concat_cancel_last in H7. destruct H7. subst. 
    simpl in *.
    repeat apply ety_weakening.
    eapply ety_invoke; eauto.
    apply inst_typing_types in HIT1.
    erewrite <- (stypes_get_type s) in H6; last exact HIT1.
    rewrite H6 in H1. inversion H1; done.
  - (* Call reference *)
    rewrite (separate1 (AI_ref x)) in HType.
    apply e_composition_typing in HType as (ts' & t1s' & t2s' & t3s & -> & -> & Hconst & Hcallref).
    convert_et_to_bet.
    apply Call_reference_typing in Hcallref as (ts'' & t1s'' & t2s'' & Htypes & -> & ->).
    simpl in Htypes.
    apply AI_ref_typing in Hconst as (t & Ht & Hconst).
    apply ety_weakening.
    rewrite catA in Hconst. apply concat_cancel_last in Hconst as [<- Hx].
    apply ety_weakening.
    econstructor. exact H.
    unfold get_type in Htypes.
    destruct i.
    destruct C; inversion HC; subst.
    destruct i => //.
    inversion Htypes; subst f0.
    inversion H0. done.
  -  (* Call reference *)
        rewrite (separate1 (AI_ref x)) in HType.
    apply e_composition_typing in HType as (ts' & t1s' & t2s' & t3s & -> & -> & Hconst & Hcallref).
    convert_et_to_bet.
    apply Call_reference_typing in Hcallref as (ts'' & t1s'' & t2s'' & Htypes & -> & ->).
    simpl in Htypes.
    apply AI_ref_typing in Hconst as (t & Ht & Hconst).
    apply ety_weakening.
    rewrite catA in Hconst. apply concat_cancel_last in Hconst as [<- Hx].
    apply ety_weakening.
    econstructor. exact H.
    apply inst_typing_types in HIT1.
    erewrite <- (stypes_get_type s) in Htypes; last exact HIT1.
    rewrite Htypes in H0. inversion H0 => //. 
  - (* Invoke native *)
    invert_e_typing.
    eapply Invoke_func_native_typing in H0; eauto.
    destruct H0 as [ts2 [C2 [H9 [H10 [H11 H12]]]]]. subst.
    apply Const_list_typing in H3 as (ts' & Hts' & H3 & Hconst).
    apply concat_cancel_last_n in H3.
    2:{ rewrite - (size_map Some ts') - Hts' size_map. done. } 
    remove_bools_options. subst.
    simpl in *.
    apply ety_weakening. apply et_weakening_empty_1.
    apply ety_local => //.
    eapply mk_s_typing; eauto.
    eapply mk_frame_typing; eauto.
    { rewrite H8. instantiate (1 := _ ++ _).
      apply List.Forall2_app.
      - rewrite forall_values_type.
        eapply t_const_ignores_context. apply v_to_e_is_const_list.
        exact Hconst.
      - rewrite forall_values_type.
        apply default_vals_typing. } 
    apply ety_a'; auto_basic => //=.
    assert (HC2Empty: tc_label C2 = [::]); first by eapply inst_t_context_label_empty; eauto.
    rewrite HC2Empty in H12.
    apply bet_block. simpl.
    rewrite HC2Empty.
    done.
  - (* Invoke native *)
    invert_e_typing.
    eapply Invoke_func_native_typing in H0; eauto.
    destruct H0 as [ts2 [C2 [H9 [H10 [H11 H12]]]]]. subst.
    apply Const_list_typing in H3 as (ts' & Hts' & H3 & Hconst).
    apply concat_cancel_last_n in H3.
    2:{ rewrite - (size_map Some ts') - Hts' size_map. done. } 
    remove_bools_options. subst.
    simpl in *.
    apply ety_weakening. apply et_weakening_empty_1.
    assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
    rewrite HCEmpty. simpl.
    apply ety_local => //.
    eapply mk_s_typing; eauto.
    eapply mk_frame_typing; eauto.
    { rewrite H8. instantiate (1 := _ ++ _).
      apply List.Forall2_app.
      - rewrite forall_values_type.
        eapply t_const_ignores_context. apply v_to_e_is_const_list.
        exact Hconst.
      - rewrite forall_values_type.
        apply default_vals_typing. } 
    apply ety_a'; auto_basic => //=.
    assert (HC2Empty: tc_label C2 = [::]); first by eapply inst_t_context_label_empty; eauto.
    rewrite HC2Empty in H12.
    apply bet_block. simpl.
    rewrite HC2Empty.
    done.
  - (* Invoke host *)
    apply e_composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H5' [H6 [H7 H8]]]]]]].
    subst.
    eapply Invoke_func_host_typing in H8; eauto.
    destruct H8 as [ts'' [H8 H9]]. subst.
    apply Const_list_typing in H7 as (tsv & Htsv & H7 & Hconst).
    apply concat_cancel_last_n in H7.
    2:{ rewrite - (size_map Some tsv) - Htsv size_map. done. } 
    remove_bools_options. subst.
    rewrite catA. apply et_weakening_empty_1.
    eapply ety_call_host.
    done.
  - (* Invoke host *)
    apply e_composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H5' [H6 [H7 H8]]]]]]].
    subst.
    eapply Invoke_func_host_typing in H8; eauto.
    destruct H8 as [ts'' [H8 H9]]. subst.
    apply Const_list_typing in H7 as (tsv & Htsv & H7 & Hconst).
    apply concat_cancel_last_n in H7.
    2:{ rewrite - (size_map Some tsv) - Htsv size_map. done. } 
    remove_bools_options. subst.
    rewrite catA. apply et_weakening_empty_1.
    eapply ety_call_host.
    done.
  - (* Try_table *)
    apply e_composition_typing in HType as (ts0 & t1s' & t2s' & t3s & -> & -> & Hvs & Htrytable).
    apply const_es_exists in H1 as [vs' ->].
    apply Const_list_typing in Hvs as (tsv & Htsv & -> & Hvs').
    convert_et_to_bet.
    apply Try_table_typing in Htrytable as (ts' & tn & tm & Htnm & Htypes & -> & Hclauses & Hes).
    destruct i; first by destruct C, i; inversion HC; subst.
    simpl in H.  inversion H; subst.
    simpl in Htnm. inversion Htnm; subst.
    apply concat_cancel_last_n in Htypes.
    2:{ do 2 rewrite length_is_size in H2.
        rewrite - H2. rewrite size_map.
        rewrite - (size_map (typeof s) vs'). rewrite Htsv.
        rewrite size_map. done. }
    remove_bools_options. subst.
    apply ety_weakening. apply et_weakening_empty_1.
    apply ety_handler.
    eapply exception_clause_desugar_typing; eauto.
    eapply ety_label.
    instantiate (1 := tm). 3: done.
    apply et_weakening_empty_both.
    apply ety_a' ; first by constructor.
    apply bet_empty.
    eapply et_composition'.
    eapply t_const_ignores_context. apply v_to_e_is_const_list. exact Hvs'.
    simpl in Hes. simpl.
    apply ety_a' => //.
    apply to_e_list_basic.
    rewrite to_b_to_e_list.
    exact Hes.
  - (* Try_table *)
    apply e_composition_typing in HType as (ts0 & t1s' & t2s' & t3s & -> & -> & Hvs & Htrytable).
    apply const_es_exists in H1 as [vs' ->].
    apply Const_list_typing in Hvs as (tsv & Htsv & -> & Hvs').
    convert_et_to_bet.
    apply Try_table_typing in Htrytable as (ts' & tn & tm & Htnm & Htypes & -> & Hclauses & Hes).
    unfold stypes in H.
    apply inst_typing_types in HIT1.
    rewrite - HIT1 in H. unfold get_type in Htnm. rewrite Htnm in H. 
    inversion H; subst.
    apply concat_cancel_last_n in Htypes.
    2:{ do 2 rewrite length_is_size in H2.
        rewrite - H2. rewrite size_map.
        rewrite - (size_map (typeof s) vs'). rewrite Htsv.
        rewrite size_map. done. }
    remove_bools_options. subst.
    apply ety_weakening. apply et_weakening_empty_1.
    apply ety_handler.
    eapply exception_clause_desugar_typing; eauto.
    left. rewrite strip_upd_label.
    rewrite strip_upd_local_return.
    apply inst_typing_strip => //. 
    eapply ety_label.
    instantiate (1 := t2s). 3: done.
    apply et_weakening_empty_both.
    apply ety_a' ; first by constructor.
    apply bet_empty.
    eapply et_composition'.
    eapply t_const_ignores_context. apply v_to_e_is_const_list. exact Hvs'.
    simpl in Hes. simpl.
    apply ety_a' => //.
    apply to_e_list_basic.
    rewrite to_b_to_e_list.
    exact Hes.

  - (* Throw *)
    apply e_composition_typing in HType as (ts' & t1s' & t2s' & t3s & -> & -> & Hvcs & Hthrow).
    apply Const_list_typing in Hvcs as (tsv & Htsv & -> & Hvcs).
    convert_et_to_bet.
    apply Throw_typing in Hthrow as (ts'' & t1s & Htags & Htypes).
    destruct C; inversion HC; subst.
    destruct x => //.
  - (* Throw *)
    apply e_composition_typing in HType as (ts' & t1s' & t2s' & t3s & -> & -> & Hvcs & Hthrow).
    apply Const_list_typing in Hvcs as (tsv & Htsv & -> & Hvcs).
    convert_et_to_bet.
    apply Throw_typing in Hthrow as (ts'' & t1s & Htags & Htypes).
    eapply tc_reference_tag in HIT1 as Htagseq.
    2: exact H. 2: exact H0. 2: exact Htags.
    inversion Htagseq; subst ts.
    apply concat_cancel_last_n in Htypes.
    2:{ do 2 rewrite length_is_size in H2. rewrite - H2. rewrite size_map.
        rewrite - (size_map (typeof s) vcs). rewrite Htsv. rewrite size_map.
        done. }
    remove_bools_options. subst tsv ts''. 
    
    apply ety_weakening.
    rewrite separate1.
    eapply et_composition'.
    + instantiate (1 := (t1s' ++ _)).
      apply et_weakening_empty_1. eapply ety_ref_exn.
      simpl. 
      rewrite - (cats0 [:: _]).
      rewrite list_nth_prefix. done. done.
    + apply ety_a' ; first by constructor.
      apply bet_throw_ref.
  - (* Throw_ref desugar *)
    rewrite separate1 in HType.
    apply e_composition_typing in HType as (ts & t1s & t2s & t3s & -> & -> & Hrefexn & Hthrowref).
    apply AI_ref_exn_typing in Hrefexn as (exn' & Hexn' & Hetag & ->).
    rewrite Hexn' in H; inversion H; subst exn'.
    convert_et_to_bet.
    apply Throw_ref_typing in Hthrowref as (ts' & Htypes).
    apply concat_cancel_last in Htypes as [<- _].
    apply ety_weakening.
    econstructor.
    exact Hexn'. done. done.
  - (* Throw_ref desugar *)
    rewrite separate1 in HType.
    apply e_composition_typing in HType as (ts & t1s & t2s & t3s & -> & -> & Hrefexn & Hthrowref).
    apply AI_ref_exn_typing in Hrefexn as (exn' & Hexn' & Hetag & ->).
    rewrite Hexn' in H; inversion H; subst exn'.
    convert_et_to_bet.
    apply Throw_ref_typing in Hthrowref as (ts' & Htypes).
    apply concat_cancel_last in Htypes as [<- _].
    apply ety_weakening.
    econstructor.
    exact Hexn'. done. done.
  - (* Throw_ref *)
    apply Handler_typing in HType as (ts2' & -> & Hhs & HLI).
    eapply hfilled_typing in HLI as ([t1s t2s] & (* i' & *) C' & HType & (* HC' & *) Hreconstruct).
    2: exact H.
    apply AI_throw_ref_desugared_typing in HType as (exn & Hexn & -> & -> ).
    apply et_weakening_empty_1.
    
    destruct s.
    destruct HST1 as (_ & _ & _ & _ & _ & Hexns).
    rewrite List.Forall_forall in Hexns.
    apply List.nth_error_In in Hexn.
    apply Hexns in Hexn as (tse & Hexn & Htags).
    eapply et_composition'.
    eapply t_const_ignores_context. apply v_to_e_is_const_list.
    exact Hexn.
    apply ety_a'; first by constructor.
    destruct (e_tag _) eqn:Htag.
    eapply firstx_clause_typing in Hhs; last exact H0.
    destruct Hhs as [(ts0' & Htagst & Hlab) | Hlab].
    + rewrite - (cat0s tse).
      apply bet_br.
      apply nth_error_lt_Some in Hlab => //.
      simpl in *.
      unfold plop2.
      rewrite Hlab => //.
      rewrite Htags in Htagst.
      inversion Htagst. done.
    + rewrite - (cats0 tse).
      apply bet_br.
      apply nth_error_lt_Some in Hlab => //.
      simpl in *.
      unfold plop2. simpl.
      rewrite Hlab => //. 
  - (* Throw_ref *)
    apply Handler_typing in HType as (ts2' & -> & Hhs & HLI).
    eapply hfilled_typing in HLI as ([t1s t2s] & (* i' & *) C' & HType & (* HC' & *) Hreconstruct).
    2: exact H.
    apply AI_throw_ref_desugared_typing in HType as (exn & Hexn & -> & ->).
    apply et_weakening_empty_1.
    destruct s.
    destruct HST1 as (_ & _ & _ & _ & _ & Hexns).
    rewrite List.Forall_forall in Hexns.
    apply List.nth_error_In in Hexn.
    apply Hexns in Hexn as (tse & Hexn & Htags).
    eapply et_composition'.
    eapply t_const_ignores_context. apply v_to_e_is_const_list.
    exact Hexn.
    apply ety_a'; first by constructor.
    destruct (e_tag _) eqn:He.
    eapply firstx_clause_typing in Hhs; last exact H0.
    destruct Hhs as [(ts0' & Htagst & Hlab) | Hlab].
    + rewrite - (cat0s tse).
      apply bet_br.
      simpl.
      apply nth_error_lt_Some in Hlab => //.
      simpl in *.
      unfold plop2. simpl.
      rewrite Hlab => //.
      rewrite Htags in Htagst.
      inversion Htagst. done.
    + rewrite - (cats0 tse).
      apply bet_br.
      simpl.
      apply nth_error_lt_Some in Hlab => //.
      simpl in *.
      unfold plop2. simpl.
      rewrite Hlab => //. 

  - (* Throw_ref_ref *) 
    apply Handler_typing in HType as (ts2' & -> & Hhs & HLI).
    eapply hfilled_typing in HLI as ([t1s t2s] & (* i' & *) C' & HType & (* HC' & *) Hreconstruct).
    2: exact H.
    apply AI_throw_ref_desugared_typing in HType as (exn & Hexn & -> & ->).
    apply et_weakening_empty_1.
    destruct s.
    destruct HST1 as (_ & _ & _ & _ & _ & Hexns).
    rewrite List.Forall_forall in Hexns.
    remember Hexn as Hexn'; clear HeqHexn'.
    apply List.nth_error_In in Hexn.
    apply Hexns in Hexn as (tse & Hexn & Htags).
    eapply et_composition'.
    eapply t_const_ignores_context. apply v_to_e_is_const_list.
    exact Hexn.
    rewrite separate1.
    eapply et_composition'.
    instantiate (1 := tse ++ _).
    apply et_weakening_empty_1.
    eapply ety_ref_exn.
    exact Hexn'. done. 
    
    apply ety_a'; first by constructor.
    destruct (e_tag _) eqn:He.
    eapply firstx_clause_typing_ref in Hhs; last exact H0.
    destruct Hhs as [(ts0' & Htagst & Hlab) | Hlab].
    + rewrite - (cat0s (tse ++ _)).
      apply bet_br.
      apply nth_error_lt_Some in Hlab => //.
      simpl in *.
      unfold plop2. 
      rewrite Hlab => //.
      rewrite Htags in Htagst.
      inversion Htagst. done.
    + apply bet_br.
      apply nth_error_lt_Some in Hlab => //.

      unfold plop2. 
      rewrite Hlab => //.       

  - (* Throw_ref_ref *) 
    apply Handler_typing in HType as (ts2' & -> & Hhs & HLI).
    eapply hfilled_typing in HLI as ([t1s t2s] & (* i' & *) C' & HType & (* HC' & *) Hreconstruct).
    2: exact H.
    apply AI_throw_ref_desugared_typing in HType as (exn & Hexn & -> & ->).
    apply et_weakening_empty_1.
    remember Hexn as Hexn'; clear HeqHexn'.
    destruct s.
    destruct HST1 as (_ & _ & _ & _ & _ & Hexns).
    rewrite List.Forall_forall in Hexns.
    apply List.nth_error_In in Hexn.
    apply Hexns in Hexn as (tse & Hexn & Htags).
    eapply et_composition'.
    eapply t_const_ignores_context. apply v_to_e_is_const_list.
    exact Hexn.
    rewrite separate1.
    eapply et_composition'.
    instantiate (1 := tse ++ _).
    apply et_weakening_empty_1.
    eapply ety_ref_exn.
    exact Hexn'. 
    done.
    apply ety_a'; first by constructor.
    destruct (e_tag _) eqn:He.
    eapply firstx_clause_typing_ref in Hhs; last exact H0.
    destruct Hhs as [(ts0' & Htagst & Hlab) | Hlab].
    + rewrite - (cat0s (tse ++ _)).
      apply bet_br.
      simpl.
      apply nth_error_lt_Some in Hlab => //.
      simpl in *.
      unfold plop2. simpl.
      rewrite Hlab => //.
      rewrite Htags in Htagst. inversion Htagst; subst.
      done.
    + apply bet_br.
      simpl.
      apply nth_error_lt_Some in Hlab => //.
      simpl in *.
      unfold plop2. simpl.
      rewrite Hlab => //.       
  - (* Contnew *)
    rewrite separate1 in HType.
    apply e_composition_typing in HType as (ts0 & t1s' & t2s' & t3s & -> & -> & HRef & HContnew).
    convert_et_to_bet.
    apply Contnew_typing in HContnew as (ts0' & tf' & Htypes & -> & ->).
    apply AI_ref_typing in HRef as (t & Ht & Hc).
    apply concat_cancel_last in Hc as [-> <-].
    simpl in Ht. destruct (List.nth_error _ x) eqn:Hfuncs => //.
    simpl in Ht; inversion Ht.  
    
    apply ety_weakening. apply et_weakening_empty_1.
    destruct i; first by     destruct C; inversion HC; subst; destruct i.
    inversion H. subst.
    inversion Htypes; subst.
    
(*    rewrite H1. *)
    eapply ety_ref_cont.
    + simpl. 
      rewrite list_nth_prefix. done. 
    + econstructor.
  - (* Contnew *)
    rewrite separate1 in HType.
    apply e_composition_typing in HType as (ts0 & t1s' & t2s' & t3s & -> & -> & HRef & HContnew).
    convert_et_to_bet.
    apply Contnew_typing in HContnew as (ts0' & tf' & Htypes & -> & ->).
    apply AI_ref_typing in HRef as (t & Ht & Hc).
    apply concat_cancel_last in Hc as [-> <-].
    simpl in Ht. destruct (List.nth_error _ x) eqn:Hfuncs => //.
    simpl in Ht; inversion Ht.  
    
    apply ety_weakening. apply et_weakening_empty_1.
    apply inst_typing_types in HIT1.
    erewrite <- (stypes_get_type s) in Htypes; last exact HIT1.
    rewrite H in Htypes.
    inversion Htypes; subst tf.
    
    rewrite H1.
    eapply ety_ref_cont.
    + simpl. 
      rewrite list_nth_prefix. done. 
    + econstructor.
  - (* Resume *)
    rewrite separate1 in HType.
    apply e_composition_typing in HType as (ts0 & t1s' & t2s' & t3s' & -> & -> & Hvs & Hrefres). 
    destruct (const_es_exists H) as [es ->].
    apply Const_list_typing in Hvs as (tsv & Htsv & -> & Hconst).
    apply e_composition_typing in Hrefres as (ts0' & t1s'' & t2s'' & t3s'' & Hts1 & -> & Hrefcont & Hresume).
    apply AI_ref_cont_typing in Hrefcont as (t & Ht & ->).
    simpl in Ht. rewrite H2 in Ht. inversion Ht; subst t. 
    convert_et_to_bet.
    remember HST1 as HST1' ; clear HeqHST1'.
    destruct s; destruct HST1 as (_ & _ & _ & _ & Hconts & _).
    rewrite List.Forall_forall in Hconts.
    remember H2 as H2'; clear HeqH2'.
    apply List.nth_error_In in H2.
    apply Hconts in H2.
    inversion H2; subst.
    apply Resume_typing in Hresume as (ts0'' & t1s''' & t2s''' & Htypes & Hclauses & Hts1' & ->).
    rewrite catA in Hts1'. apply concat_cancel_last in Hts1' as [-> Hcontref].
    inversion Hcontref; subst t1s''' t2s'''. 
    rewrite catA in Hts1.
    apply concat_cancel_last_n in Hts1.
    2:{ rewrite - (size_map Some tsv). rewrite - Htsv. rewrite size_map.
        repeat rewrite length_is_size in H1. rewrite - H1. rewrite size_map. done. } 
    remove_bools_options.
    do 2 apply ety_weakening.
    apply et_weakening_empty_1.
    apply ety_prompt.
    eapply continuation_clause_desugar_typing; eauto.
    eapply e_typing_plug_value.
    7:{ eapply store_extension_e_typing.
        3:{ exact H12. }
        done.
        eapply store_extension_upd_cont.
        done. eauto. done.
    }
    5: exact H11.
    exact H8.
    4: exact H3.
    done.
    { eapply store_extension_e_typing.
      3:{ exact H10. } 
      done. eapply store_extension_upd_cont; eauto.
    }
    { eapply store_extension_e_typing; last first.
      { eapply t_const_ignores_context.
        apply v_to_e_is_const_list. exact Hconst. }
      eapply store_extension_upd_cont; eauto.
      done. }
  - (* Resume *)
    rewrite separate1 in HType.
    apply e_composition_typing in HType as (ts0 & t1s' & t2s' & t3s' & -> & -> & Hvs & Hrefres). 
    destruct (const_es_exists H) as [es ->].
    apply Const_list_typing in Hvs as (tsv & Htsv & -> & Hconst).
    apply e_composition_typing in Hrefres as (ts0' & t1s'' & t2s'' & t3s'' & Hts1 & -> & Hrefcont & Hresume).
    apply AI_ref_cont_typing in Hrefcont as (t & Ht & ->).
    simpl in Ht. rewrite H2 in Ht. inversion Ht; subst t. 
    convert_et_to_bet.
    remember HST1 as HST1' ; clear HeqHST1'.
    destruct s; destruct HST1 as (_ & _ & _ & _ & Hconts & _).
    rewrite List.Forall_forall in Hconts.
    remember H2 as H2'; clear HeqH2'.
    apply List.nth_error_In in H2.
    apply Hconts in H2.
    inversion H2; subst.
    apply Resume_typing in Hresume as (ts0'' & t1s''' & t2s''' & Htypes & Hclauses & Hts1' & ->).
    rewrite catA in Hts1'. apply concat_cancel_last in Hts1' as [-> Hcontref].
    inversion Hcontref; subst t1s''' t2s'''. 
    rewrite catA in Hts1.
    apply concat_cancel_last_n in Hts1.
    2:{ rewrite - (size_map Some tsv). rewrite - Htsv. rewrite size_map.
        repeat rewrite length_is_size in H1. rewrite - H1. rewrite size_map. done. } 
    remove_bools_options.
    do 2 apply ety_weakening.
    apply et_weakening_empty_1.
    apply ety_prompt.
    eapply continuation_clause_desugar_typing; eauto.
    left. rewrite strip_upd_label strip_upd_local_return.
    apply inst_typing_strip => //. 
    eapply e_typing_plug_value.
    7:{ eapply store_extension_e_typing.
        3:{ apply typing_empty_context. exact H12. }
        done.
        eapply store_extension_upd_cont; eauto.
    }
    5: exact H11.
    exact H8.
    4: exact H3.
    done.
    { eapply store_extension_e_typing.
      3:{ apply typing_empty_context. exact H10. } 
      done.
      eapply store_extension_upd_cont; eauto.
    }
    { eapply store_extension_e_typing; last first.
      { eapply t_const_ignores_context.
        2: exact Hconst. done. }
      eapply store_extension_upd_cont; eauto.
      done. } 
  - (* Suspend desugar *)
    apply e_composition_typing in HType as (ts & t1s' & t2s' & t3s & -> & -> & Hvs & Hsus).
    convert_et_to_bet.
    apply Suspend_typing in Hsus as (ts' & t1s'' & t2s'' & Htag & Htypes & ->).
    destruct C; inversion HC; subst.
    destruct x => //.
  - (* Suspend desugar *)
    apply e_composition_typing in HType as (ts & t1s' & t2s' & t3s & -> & -> & Hvs & Hsus).
    apply Const_list_typing in Hvs as (tsv & Hvs & -> & Hvsempt).
    convert_et_to_bet.
    apply Suspend_typing in Hsus as (ts' & t1s'' & t2s'' & Htag & Htypes & ->).
    apply ety_weakening.
    eapply tc_reference_tag in HIT1.
    2: exact H. 2: exact H0. 2: exact Htag.
    inversion HIT1; subst.
    apply concat_cancel_last_n in Htypes; remove_bools_options.
    2:{ do 2 rewrite length_is_size in H1.
        rewrite - H1. apply (f_equal size) in Hvs.
        do 2 rewrite size_map in Hvs. done. }
    subst.
    apply et_weakening_empty_1.
    econstructor => //. exact H0. done.
  - (* Switch desugar *)
    apply e_composition_typing in HType as (ts & t1s' & t2s' & t3s & -> & -> & Hcont & Hswitch).
    rewrite separate1 in Hswitch.
    apply e_composition_typing in Hswitch as (ts' & t1s'' & t2s'' & t3s' & Htypes & -> & ? & Hswitch).
    convert_et_to_bet.
    apply Switch_typing in Hswitch as (ts'' & tf'' & t1s''' & t2s''' & tpref & Htag & Htype & -> & Htypes' & ->).

    destruct C; inversion HC; subst.
    destruct x => //.
  - (* Switch desugar *)
    apply e_composition_typing in HType as (ts & t1s' & t2s' & t3s & -> & -> & Hcont & Hswitch).
    apply Const_list_typing in Hcont as (tsv & Hvs & -> & Hconst).
    rewrite separate1 in Hswitch.
    apply e_composition_typing in Hswitch as (ts' & t1s'' & t2s'' & t3s' & Htypes & -> & Hcont & Hswitch).
    apply AI_ref_cont_typing in Hcont as (t & Hk & ->).
    convert_et_to_bet.
    apply Switch_typing in Hswitch as (ts'' & tf'' & t1s''' & t2s''' & tpref & Htag & Htype & -> & Htypes' & ->).
    rewrite catA in Htypes'.
    apply concat_cancel_last in Htypes' as [-> ->].
    apply ety_weakening.
    eapply tc_reference_tag in HIT1.
    2: exact H0. 2: exact H1. 2: exact Htag.
    apply inst_typing_types in HIT2.
    unfold get_type in Htype. unfold stypes in H.
    rewrite -HIT2 in H. simpl in Htype.
    rewrite Htype in H.
    inversion H.
    subst.
    simpl in Hk.
    destruct (List.nth_error _ k) eqn:Hk' => //.
    inversion Hk.
    inversion H2; subst c.
    rewrite H3 in H6.
    inversion H6; subst t1s ts''.
    do 2 rewrite length_is_size in H4.
    rewrite size_cat in H4. simpl in H4.
    assert (size vs = size t1s'''); first lias.
    rewrite catA in Htypes.
    apply concat_cancel_last_n in Htypes; remove_bools_options; subst.
    2:{ rewrite -H5. apply (f_equal size) in Hvs.
        do 2 rewrite size_map in Hvs. done. }
    apply ety_weakening.
    apply et_weakening_empty_1.
    econstructor.
    exact H1. exact H2. exact Hk'.
    done. done. 
  
  - (* Suspend *)
    apply Prompt_typing in HType as ((* ts2 & *) -> & Hclauses & HLI).
    eapply hfilled_typing in HLI as (ts1 & (* i' & *) C' & Hsuspend & (* HC' & *) Hrebuild).
    2: exact H2.
    destruct ts1 as [ts1 ts3].
    apply AI_suspend_desugared_typing in Hsuspend as (ts1'' & ts2'' & -> & Hconst & Htags ).
    rewrite H0 in Htags. inversion Htags; subst.
    apply et_weakening_empty_1.
    eapply et_composition'.
    + eapply t_const_ignores_context. apply v_to_e_is_const_list.
      
      eapply store_extension_e_typing; last exact Hconst. done.
      eapply store_extension_new_cont; eauto.
    + rewrite separate1. eapply et_composition'.
      * instantiate (1 := ts1'' ++ _). apply et_weakening_empty_1.
        eapply ety_ref_cont.
        unfold new_cont. simpl.
        rewrite - (cats0 [:: Cont_hh _ _]).
        apply list_nth_prefix. done.
      * apply ety_a'; first by constructor.
        eapply firstx_clause_typing_cont in H1 as (ts1' & ts2' & Htagsi0 & Hlabel); last exact Hclauses.
        rewrite - (cat0s (ts1'' ++ _)).
        constructor. simpl.
        apply nth_error_lt_Some in Hlabel. done.
        unfold plop2. simpl.
        simpl in Htagsi0.
        rewrite H0 in Htagsi0. inversion Htagsi0; subst.
        
        by rewrite Hlabel.

  - (* Suspend *)
    apply Prompt_typing in HType as ((* ts2 & *) -> & Hclauses & HLI).
    eapply hfilled_typing in HLI as (ts1 & (* i' & *) C' & Hsuspend & (* HC' & *) Hrebuild).
    2: exact H2.
    destruct ts1 as [ts1 ts3].
    apply AI_suspend_desugared_typing in Hsuspend as (ts1'' & ts2'' & -> & Hconst & Htags ).
    rewrite H0 in Htags. inversion Htags; subst.
    apply et_weakening_empty_1.
    eapply et_composition'.
    + eapply t_const_ignores_context. apply v_to_e_is_const_list.
      eapply store_extension_e_typing; last exact Hconst. done.
      eapply store_extension_new_cont; eauto.
    + rewrite separate1. eapply et_composition'.
      * instantiate (1 := ts1'' ++ _). apply et_weakening_empty_1.
        eapply ety_ref_cont.
        unfold new_cont. simpl.
        rewrite - (cats0 [:: Cont_hh _ _]).
        apply list_nth_prefix. done.
      * apply ety_a'; first by constructor.
        eapply firstx_clause_typing_cont in H1 as (ts1' & ts2' & Htagsi0 & Hlabel); last exact Hclauses.
        simpl in Hlabel.
        rewrite - (cat0s (ts1'' ++ _)).
        constructor. simpl.
        apply nth_error_lt_Some in Hlabel. done.
        unfold plop2. simpl.
        simpl in Htagsi0.
        rewrite H0 in Htagsi0.
        inversion Htagsi0; subst ts1'' ts2''.
        by rewrite Hlabel.
  - (* Switch *)
    apply Prompt_typing in HType as (-> & Hclauses & HLI).
    eapply hfilled_typing in HLI as (ts1 & C' & Hswitch & Hrebuild).
    2: exact H2.
    destruct ts1 as [ts1 ts3].
    destruct x.
    apply AI_switch_desugared_typing in Hswitch as (ts''' & ta & tb & cont & Htag & Hconts & Hcont & Hconst & Htf & ->).
    inversion Htf; subst ts'''.
    apply concat_cancel_last in H4 as [<- Htypes'].
    inversion Htypes'; subst tf'.
    apply firstx_continuation_switch_In in H.
    rewrite List.Forall_forall in Hclauses.
    apply Hclauses in H. inversion H; subst.
    rewrite H6 in Htag. inversion Htag; subst t2s; clear Htag.
    apply et_weakening_empty_1.
    rewrite H1 in Hconts. inversion Hconts; subst cont.
    simpl in Hcont.
    inversion Hcont; subst t1s' t2s'.
    constructor.
    { rewrite -List.Forall_forall in Hclauses.
      eapply List.Forall_impl; last exact Hclauses.
      intros cl Hcl.
      eapply store_extension_continuation_clause_typing.
      exact Hsext. exact Hcl. }
    destruct s.
    remember HST1 as HST1'; clear HeqHST1'.
    clear Hconts.
    destruct HST1 as (_ & _ & _ & _ & Hconts & _).
    rewrite List.Forall_forall in Hconts.
    remember H1 as H2'; clear HeqH2'.
    apply List.nth_error_In in H1.
    apply Hconts in H1.
    inversion H1; subst.
    eapply e_typing_plug_value.
    5: exact H10.
    done.
    4: exact H3.
    apply const_list_concat => //.
    apply v_to_e_is_const_list.
    eapply store_extension_e_typing.
    exact HST1'. exact Hsext. exact H9.
    2: eapply store_extension_e_typing; [exact HST1' | exact Hsext | exact H11].
    eapply ety_composition.
    eapply store_extension_e_typing; [exact HST1' | exact Hsext | ].
    eapply t_const_ignores_context.
    apply v_to_e_is_const_list.
    exact Hconst.
    apply et_weakening_empty_1.
    econstructor. simpl.
    rewrite - (cats0 (_ ++ _)).
    rewrite - catA.
    replace (length s_conts) with (length (replace_nth_cont s_conts k
       (Cont_dagger (Tf (t1s ++ [:: T_ref (T_contref (Tf tb ts))]) ts)))).  
    apply list_nth_prefix.
    unfold replace_nth_cont.
    do 2 rewrite length_is_size.
    repeat rewrite size_cat.

    apply nth_error_lt_Some in H2'.
    clear - H2'. simpl in H2'.
    rewrite length_is_size in H2'.
    rewrite size_takel; last lias.
    rewrite size_drop.
    simpl. lias.
    done.
  - (* Switch *)
    apply Prompt_typing in HType as (-> & Hclauses & HLI).
    eapply hfilled_typing in HLI as (ts1 & C' & Hswitch & Hrebuild).
    2: exact H2.
    destruct ts1 as [ts1 ts3].
    destruct x.
    apply AI_switch_desugared_typing in Hswitch as (ts''' & ta & tb & cont & Htag & Hk & Hcont & Hconst & Htf & ->).
    inversion Htf; subst ts'''.
    apply concat_cancel_last in H4 as [<- Htypes'].
    inversion Htypes'; subst tf'.
    rewrite H1 in Hk.
    inversion Hk; subst cont.
    inversion Hcont; subst t1s' t2s'.
    
    apply firstx_continuation_switch_In in H.
    rewrite List.Forall_forall in Hclauses.
    apply Hclauses in H. inversion H; subst.
    rewrite H6 in Htag. inversion Htag; subst t2s; clear Htag. 
    apply et_weakening_empty_1.
    constructor.
    { rewrite -List.Forall_forall in Hclauses.
      eapply List.Forall_impl; last exact Hclauses.
      intros cl Hcl.
      eapply store_extension_continuation_clause_typing.
      exact Hsext. exact Hcl. }
    destruct s.
    remember HST1 as HST1'; clear HeqHST1'.
    destruct HST1 as (_ & _ & _ & _ & Hconts & _).
    rewrite List.Forall_forall in Hconts.
    remember H1 as H2'; clear HeqH2'.
    apply List.nth_error_In in H1.
    apply Hconts in H1.
    inversion H1; subst.
    eapply e_typing_plug_value.
    5: exact H10.
    done.
    4: exact H3.
    apply const_list_concat => //.
    apply v_to_e_is_const_list.
    eapply store_extension_e_typing.
    exact HST1'. exact Hsext. exact H9.
    2: eapply store_extension_e_typing; [exact HST1' | exact Hsext | exact H11].
    eapply ety_composition.
    eapply store_extension_e_typing; [exact HST1' | exact Hsext | ].
    eapply t_const_ignores_context.
    apply v_to_e_is_const_list.
    exact Hconst.
    apply et_weakening_empty_1.
    econstructor. simpl.
    rewrite - (cats0 (_ ++ _)).
    rewrite - catA.
    replace (length s_conts) with (length (replace_nth_cont s_conts k
       (Cont_dagger (Tf (t1s ++ [:: T_ref (T_contref (Tf tb ts))]) ts)))).  
    apply list_nth_prefix.
    unfold replace_nth_cont.
    do 2 rewrite length_is_size.
    repeat rewrite size_cat.

    apply nth_error_lt_Some in H2'.
    clear - H2'. simpl in H2'.
    rewrite length_is_size in H2'.
    rewrite size_takel; last lias.
    rewrite size_drop.
    simpl. lias.
    done.

  - (* Contbind *)
    apply e_composition_typing in HType as (ts0' & t1s' & t2s' & t3s' & -> & -> & Hvs & Haft).
    apply const_es_exists in H as [vs0 ->].
    apply Const_list_typing in Hvs as (tvs0 & Hvst & -> & Hvs).
    rewrite separate1 in Haft.
    apply e_composition_typing in Haft as (ts0'' & t1s'' & t2s'' & t3s'' & Htypes & -> & Hrefcont & Hcontbind).
    apply AI_ref_cont_typing in Hrefcont as (t & Ht & ->).
    simpl in Ht. rewrite H3 in Ht. inversion Ht; subst t.
    convert_et_to_bet.
    apply Contbind_typing in Hcontbind as (ts1 & t0s & t1s''' & t2s''' & H0' & H1' & Htypes' & ->).
    destruct i; first by     destruct C; inversion HC; subst; destruct i.
    destruct i'; first by     destruct C; inversion HC; subst; destruct i.
    inversion H0'; inversion H1'; subst.
    inversion H0; inversion H1; subst.
    apply concat_cancel_last_n in H4 => //.
    remove_bools_options. subst.
    rewrite catA in Htypes'. apply concat_cancel_last in Htypes' as [-> _].
    rewrite catA in Htypes. apply concat_cancel_last_n in Htypes.
    2:{ rewrite - (size_map Some tvs0). rewrite - Hvst.
        rewrite size_map.
        do 2 rewrite length_is_size in H2.
        rewrite size_map in H2.
        rewrite - H2. done. }
    remove_bools_options. subst ts t1s'.
    do 2 apply ety_weakening. apply et_weakening_empty_1.
    eapply ety_ref_cont.
    + unfold new_cont. simpl. rewrite - (cats0 [:: _]).
      replace (length (s_conts s)) with (length (replace_nth_cont (s_conts s) k (Cont_dagger (Tf (tvs0 ++ t1s) t2s)))).
      * rewrite list_nth_prefix. done.
      * unfold replace_nth_cont. do 2 rewrite length_is_size.
        repeat rewrite size_cat.
        assert (k < size (s_conts s)).
        2:{ rewrite size_takel; last lias.
            rewrite size_drop. simpl. lias. }
        remember (s_conts s) as l.
        clear - H3.
        generalize dependent k; induction l; destruct k => //=.
        intros H; apply IHl in H. lias. 
    + done.
        - (* Contbind *)
    apply e_composition_typing in HType as (ts0' & t1s' & t2s' & t3s' & -> & -> & Hvs & Haft).
    apply const_es_exists in H as [vs0 ->].
    apply Const_list_typing in Hvs as (tvs0 & Hvst & -> & Hvs).
    rewrite separate1 in Haft.
    apply e_composition_typing in Haft as (ts0'' & t1s'' & t2s'' & t3s'' & Htypes & -> & Hrefcont & Hcontbind).
    apply AI_ref_cont_typing in Hrefcont as (t & Ht & ->).
    simpl in Ht. rewrite H3 in Ht. inversion Ht; subst t.
    convert_et_to_bet.
    apply Contbind_typing in Hcontbind as (ts1 & t0s & t1s''' & t2s''' & H0' & H1' & Htypes' & ->).
    apply inst_typing_types in HIT1.
    erewrite <- (stypes_get_type s) in H0'; last exact HIT1.
    erewrite <- (stypes_get_type s) in H1'; last exact HIT1.
    rewrite H0' in H0.
    rewrite H1' in H1.
    inversion H1; subst t1s''' t2s'''. clear H1.
    inversion H0. apply concat_cancel_last_n in H1 => //. remove_bools_options.
    clear H1 H5.
    rewrite catA in Htypes'. apply concat_cancel_last in Htypes' as [-> _].
    rewrite catA in Htypes. apply concat_cancel_last_n in Htypes.
    2:{ rewrite - (size_map Some tvs0). rewrite - Hvst.
        rewrite size_map.
        do 2 rewrite length_is_size in H2.
        rewrite H2. rewrite size_map. done. }
    remove_bools_options. subst ts t1s'.
    do 2 apply ety_weakening. apply et_weakening_empty_1.
(*    replace (Tf t1s t2s) with (typeof_cont (Cont_hh (Tf t1s t2s) (hhplug (v_to_e_list vs0) hh))) => //. *)
    eapply ety_ref_cont.
    + unfold new_cont. simpl. rewrite - (cats0 [:: _]).
      replace (length (s_conts s)) with (length (replace_nth_cont (s_conts s) k (Cont_dagger (Tf (tvs0 ++ t1s) t2s)))).
      * rewrite list_nth_prefix. done.
      * unfold replace_nth_cont. do 2 rewrite length_is_size.
        repeat rewrite size_cat.
        assert (k < size (s_conts s)).
        2:{ rewrite size_takel; last lias.
            rewrite size_drop. simpl. lias. }
        remember (s_conts s) as l.
        clear - H3.
        generalize dependent k; induction l; destruct k => //=.
        intros H; apply IHl in H. lias. 
    + done.

  - (* Resume_throw *)
    apply e_composition_typing in HType as (ts0' & t1s' & t2s' & t3s' & -> & -> & Hvs & Haft).

    apply Const_list_typing in Hvs as (tvs0 & Hvst & -> & Hvs).
    rewrite separate1 in Haft.
    apply e_composition_typing in Haft as (ts0'' & t1s'' & t2s'' & t3s'' & Htypes & -> & Hrefcont & Hresumethrow).
    apply AI_ref_cont_typing in Hrefcont as (t & Ht & ->).
    simpl in Ht. rewrite H5 in Ht. inversion Ht; subst t.
    convert_et_to_bet.
    apply Resume_throw_typing in Hresumethrow as (ts0''' & t1s''' & t2s''' & t0s & H3' & H0' & Hclauses & Htypes' & ->).
        destruct C; inversion HC; subst.
        destruct x => //.
          - (* Resume_throw *)
    apply e_composition_typing in HType as (ts0' & t1s' & t2s' & t3s' & -> & -> & Hvs & Haft).

    apply Const_list_typing in Hvs as (tvs0 & Hvst & -> & Hvs).
    rewrite separate1 in Haft.
    apply e_composition_typing in Haft as (ts0'' & t1s'' & t2s'' & t3s'' & Htypes & -> & Hrefcont & Hresumethrow).
    apply AI_ref_cont_typing in Hrefcont as (t & Ht & ->).
    simpl in Ht. rewrite H5 in Ht. inversion Ht; subst t.
    convert_et_to_bet.
    apply Resume_throw_typing in Hresumethrow as (ts0''' & t1s''' & t2s''' & t0s & H3' & H0' & Hclauses & Htypes' & ->).
    eapply tc_reference_tag in HIT1 as Htagseq.
    2: exact H. 2: exact H0. 2: exact H0'.
    apply inst_typing_types in HIT1 as Htypeseq.
    erewrite <- (stypes_get_type s) in H3'; last exact Htypeseq.
    rewrite H6 in H3'.
    inversion H3'; subst. clear H3'.
    inversion Htagseq; subst.
    clear Htagseq.
    rewrite catA in Htypes'. apply concat_cancel_last in Htypes' as [-> _].
    rewrite catA in Htypes. apply concat_cancel_last_n in Htypes.
    2:{ rewrite - (size_map Some tvs0).
        rewrite - Hvst. rewrite size_map.
        repeat rewrite length_is_size in H2. rewrite -H2.
        rewrite size_map. done. }
    remove_bools_options. 
    do 2 apply ety_weakening. apply et_weakening_empty_1.
    constructor.
    eapply continuation_clause_desugar_typing; eauto.
    left. rewrite strip_upd_label strip_upd_local_return.
    apply inst_typing_strip => //. 
    remember HST1 as HST1'; clear HeqHST1'.
    destruct s; destruct HST1 as (_ & _ & _ & _ & Hconts & _).
    remember H5 as H2'; clear HeqH2'.
    apply List.nth_error_In in H5.
    rewrite List.Forall_forall in Hconts.
    apply Hconts in H5.
    inversion H5; subst.

    eapply store_extension_e_typing; last first.
    + eapply e_typing_plug_throw.
      3:{ rewrite separate1.
          eapply et_composition'.
          eapply ety_ref_exn.
          instantiate (3 := add_exn  {|
            s_funcs := s_funcs;
            s_tables := s_tables;
            s_mems := s_mems;
            s_tags := s_tags;
            s_globals := s_globals;
            s_exns := s_exns;
            s_conts := s_conts
          |} _).
          instantiate (2 := length (datatypes.s_exns  {|
            s_funcs := s_funcs;
            s_tables := s_tables;
            s_mems := s_mems;
            s_tags := s_tags;
            s_globals := s_globals;
            s_exns := s_exns;
            s_conts := s_conts
          |})).
          simpl.
          rewrite - (cats0 [:: _]).
          rewrite list_nth_prefix.
          done. done.
          apply ety_a'; first by constructor.
          rewrite - (cat0s [:: T_ref _]).
          apply bet_throw_ref. } 
      5:{ apply typing_empty_context.
          eapply store_extension_e_typing.
          exact HST1'. apply store_extension_add_exn.
          exact HST1'.
          exact H13. } 
      3: exact H12.
      done.
      2: instantiate (1 := {| e_tag := _ ; e_fields := _ |}).
      2: exact H8.
      apply typing_empty_context.
      eapply store_extension_e_typing.
      exact HST1'. apply store_extension_add_exn.
      exact HST1'.
      exact H11.
    + eapply store_extension_upd_cont => //.
      apply store_typing_add_exn.
      exact HST1'.
      eexists. split.
      eapply store_extension_e_typing.
      exact HST1'.
      apply store_extension_add_exn.
      exact HST1'.
      eapply t_const_ignores_context.
      apply v_to_e_is_const_list.
      exact Hvs.
      simpl. done.
      exact H2'. done.
    + apply store_typing_add_exn.
      done.
      eexists. split.
      eapply store_extension_e_typing.
      exact HST1'.
      apply store_extension_add_exn.
      exact HST1'.
      eapply t_const_ignores_context.
      apply v_to_e_is_const_list.
      exact Hvs.
      simpl. done.

    
  - (* Get_local *)
    convert_et_to_bet.
    apply Get_local_typing in HType as (t & Ht & -> & Hj).
    destruct C; inversion HC; subst.
    destruct j => //.
  - (* Get_local *)
    convert_et_to_bet.
    apply Get_local_typing in HType as (t & Ht & -> & Hj).
    simpl in Ht. erewrite inst_t_context_local_empty in Ht; eauto.
    simpl in Ht.
    rewrite Forall2_forall in Hts.
    destruct Hts as [_ Hlocs]. eapply Hlocs in Ht; eauto.
    eapply t_const_ignores_context. simpl. rewrite const_const => //.
    apply et_weakening_empty_1.
    exact Ht. 

  - (* Set_local *)
    rewrite separate1 in HType.
    apply e_composition_typing in HType as (ts0 & t1s' & t2s' & t3s' & -> & -> & Hv & Hsetlocal).
    convert_et_to_bet.
    apply AI_const_typing in Hv as (tv & Htv & -> & Hv).
    apply Set_local_typing in Hsetlocal as (t & Ht & Htypes & Hi).
    destruct C; inversion HC; subst.
    destruct i => //.
      - (* Set_local *)
    rewrite separate1 in HType.
    apply e_composition_typing in HType as (ts0 & t1s' & t2s' & t3s' & -> & -> & Hv & Hsetlocal).
    convert_et_to_bet.
    apply AI_const_typing in Hv as (tv & Htv & -> & Hv).
    apply Set_local_typing in Hsetlocal as (t & Ht & Htypes & Hi).
    apply concat_cancel_last in Htypes as [-> ->].
    apply et_weakening_empty_both.
    apply ety_a'; first by constructor.
    constructor.
        

  - (* Get_global *)
    convert_et_to_bet.
    apply Get_global_typing in HType as (t & Hglob & -> & Hi).
    apply et_weakening_empty_1.
        destruct C; inversion HC; subst.
        destruct i => //.
  - (* Get_global *)
    convert_et_to_bet.
    apply Get_global_typing in HType as (t & Hglob & -> & Hi).
    apply et_weakening_empty_1.
    destruct (List.nth_error (tc_global _)) eqn:Hctxtg => //.
    inversion Hglob; subst t; clear Hglob.
    unfold sglob_val in H.
    unfold sglob in H.
    unfold sglob_ind in H.
    destruct (List.nth_error _ i) eqn:Hinstg => //.
    simpl in H. 
    destruct (List.nth_error _ g0) eqn:Hstoreg => //.
    inversion H; subst v; clear H.
    simpl in Hctxtg. 
    eapply tc_reference_glob_type in Hctxtg; eauto.
    apply List.nth_error_In in Hstoreg.
    destruct s; destruct HST1 as (_ & _ & _ & Hgs & _).
    rewrite List.Forall_forall in Hgs.
    apply Hgs in Hstoreg.
    destruct Hstoreg as [tg Htg].
    apply AI_const_typing in Htg as (tg' & Htg' & Htypes & Htg).
    inversion Htypes; subst tg'.
    unfold global_agree in Hctxtg. remove_bools_options.
    rewrite Htg' in H0. inversion H0; subst tg.
    eapply t_const_ignores_context. simpl. rewrite const_const. done.
    exact Htg. 
  - (* Set_Global *)
    rewrite separate1 in HType.
    apply e_composition_typing in HType as (ts0 & t1s' & t2s' & t3s & -> & -> & Hv & Hsetglobal).
    convert_et_to_bet.
    apply AI_const_typing in Hv as (tv & Htv & -> & Hv).
    apply Set_global_typing in Hsetglobal as (g & t & Hg & <- & Hmut & Htypes & Hi).
        destruct C; inversion HC; subst.
    destruct i => //. 
  - (* Set_Global *)
    rewrite separate1 in HType.
    apply e_composition_typing in HType as (ts0 & t1s' & t2s' & t3s & -> & -> & Hv & Hsetglobal).
    convert_et_to_bet.
    apply AI_const_typing in Hv as (tv & Htv & -> & Hv).
    apply Set_global_typing in Hsetglobal as (g & t & Hg & <- & Hmut & Htypes & Hi).
    apply concat_cancel_last in Htypes as [-> ->].
    apply et_weakening_empty_both.
    apply ety_a'; first by constructor.
    constructor.
  - (* Load None *)
    convert_et_to_bet.
    rewrite separate1 in HType.
    apply composition_typing in HType as (ts' & t1s' & t2s' & t3s' & -> & -> & Hconst & Hload).
    invert_be_typing.
    apply Load_typing in Hload as (ts0 & Htypes & -> & Hmem & Hbounds).
        destruct C; inversion HC; subst.
        done.
          - (* Load None *)
    convert_et_to_bet.
    rewrite separate1 in HType.
    apply composition_typing in HType as (ts' & t1s' & t2s' & t3s' & -> & -> & Hconst & Hload).
    invert_be_typing.
    apply Load_typing in Hload as (ts0 & Htypes & -> & Hmem & Hbounds).
    apply concat_cancel_last in Htypes as [-> Hk]. 
    eapply t_const_ignores_context; last first.
    + apply ety_a'; auto_basic.
      simpl.
      rewrite catA. apply bet_weakening_empty_1.
      assert (be_typing C [::BI_const (wasm_deserialise bs t)] (Tf [::] [:: T_num (typeof_num (wasm_deserialise bs t))])); first by apply bet_const.
      rewrite typeof_deserialise in H2. exact H2.
    + constructor => //.

  - (* Load Some *)
    convert_et_to_bet.
    rewrite separate1 in HType.
    apply composition_typing in HType as (ts' & t1s' & t2s' & t3s' & -> & -> & Hconst & Hload).
    invert_be_typing.
    apply Load_typing in Hload as (ts'' & Htypes & -> & Hmem & Hbounds).
        destruct C; inversion HC; subst.
        done.
          - (* Load Some *)
    convert_et_to_bet.
    rewrite separate1 in HType.
    apply composition_typing in HType as (ts' & t1s' & t2s' & t3s' & -> & -> & Hconst & Hload).
    invert_be_typing.
    apply Load_typing in Hload as (ts'' & Htypes & -> & Hmem & Hbounds).
    apply concat_cancel_last in Htypes as [-> Hnum]. 
    eapply t_const_ignores_context; last first.
    + apply ety_a'; auto_basic.
      simpl.
      assert (be_typing C [::BI_const (wasm_deserialise bs t)] (Tf [::] [:: T_num (typeof_num (wasm_deserialise bs t))])); first by apply bet_const.
      rewrite catA. apply bet_weakening_empty_1.
      rewrite typeof_deserialise in H2. by apply H2.
    + constructor => //.

  - (* Store None *)
    convert_et_to_bet.
    simpl in HType.
    replace [::BI_const (VAL_int32 k); BI_const v; BI_store t None a off] with ([::BI_const (VAL_int32 k); BI_const v] ++ [::BI_store t None a off]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Store_typing in H10.
    destruct H10 as [H11 [H12 H13]].
    destruct C; inversion HC; subst.
    done.
  - (* Store None *)
    convert_et_to_bet.
    simpl in HType.
    replace [::BI_const (VAL_int32 k); BI_const v; BI_store t None a off] with ([::BI_const (VAL_int32 k); BI_const v] ++ [::BI_store t None a off]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Store_typing in H10.
    destruct H10 as [H11 [H12 H13]].
    apply concat_cancel_last_n in H11 => //.
    move/andP in H11. destruct H11. move/eqP in H3. subst.
    apply ety_a'; auto_basic => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
        
  - (* Store Some *)
    convert_et_to_bet.
    simpl in HType.
    replace [::BI_const (VAL_int32 k); BI_const v; BI_store t (Some tp) a off] with ([::BI_const (VAL_int32 k); BI_const v] ++ [::BI_store t (Some tp) a off]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Store_typing in H10.
    destruct H10 as [H11 [H12 H13]].
    destruct C; inversion HC; subst.
    done.
  - (* Store Some *)
    convert_et_to_bet.
    simpl in HType.
    replace [::BI_const (VAL_int32 k); BI_const v; BI_store t (Some tp) a off] with ([::BI_const (VAL_int32 k); BI_const v] ++ [::BI_store t (Some tp) a off]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Store_typing in H10.
    destruct H10 as [H11 [H12 H13]].
    apply concat_cancel_last_n in H11 => //.
    move/andP in H11. destruct H11. move/eqP in H3. subst.
    apply ety_a'; auto_basic => //.
    apply bet_weakening_empty_both.
    by apply bet_empty.

  - (* Current_memory *)
    convert_et_to_bet.
    apply Current_memory_typing in HType.
    destruct HType as [H5 H6].
    destruct C; inversion HC; subst.
    done.
  - (* Current_memory *)
    convert_et_to_bet.
    apply Current_memory_typing in HType.
    destruct HType as [H5 H6]. subst.
    simpl.
    apply ety_a'; auto_basic.
    apply bet_weakening_empty_1.
    by apply bet_const. 

  - (* Grow_memory success *)
    convert_et_to_bet.
    replace [::BI_const (VAL_int32 c); BI_grow_memory] with ([::BI_const (VAL_int32 c)] ++ [::BI_grow_memory]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Grow_memory_typing in H10.
    destruct H10 as [ts'' [H11 [H12 H13]]].
    destruct C; inversion HC; subst.
    done.
  - (* Grow_memory success *)
    convert_et_to_bet.
    replace [::BI_const (VAL_int32 c); BI_grow_memory] with ([::BI_const (VAL_int32 c)] ++ [::BI_grow_memory]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Grow_memory_typing in H10.
    destruct H10 as [ts'' [H11 [H12 H13]]]. subst.
    simpl.
    apply ety_a'; auto_basic.
    rewrite catA.
    apply bet_weakening_empty_1.
    by apply bet_const.
  - (* Grow_memory fail *)
    convert_et_to_bet.
    replace [::BI_const (VAL_int32 c); BI_grow_memory] with ([::BI_const (VAL_int32 c)] ++ [::BI_grow_memory]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Grow_memory_typing in H10.
    destruct H10 as [ts'' [H11 [H12 H13]]].
    destruct C; inversion HC; subst.
    done.
  - (* Grow_memory fail *)
    convert_et_to_bet.
    replace [::BI_const (VAL_int32 c); BI_grow_memory] with ([::BI_const (VAL_int32 c)] ++ [::BI_grow_memory]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Grow_memory_typing in H10.
    destruct H10 as [ts'' [H11 [H12 H13]]]. subst.
    simpl.
    apply ety_a'; auto_basic.
    rewrite catA.
    apply bet_weakening_empty_1.
    by apply bet_const.
  - (* r_local *)
    apply Local_typing in HType as (ts' & -> & Hstyp & <-).
    apply et_weakening_empty_1.
    apply ety_local => //.
    inversion Hstyp. inversion H. subst.
    apply upd_label_unchanged_typing in H1.
    eapply mk_s_typing; eauto.
    + eapply mk_frame_typing => //. 
      * eapply inst_typing_extension; eauto.
(*        eapply store_extension_reduce; eauto. *)
        replace (f_inst f') with (f_inst f); eauto; first by eapply reduce_inst_unchanged; eauto.
      * eapply t_preservation_locals.
        exact HReduce. done. done.
        exact H8. 
        done.
        exact H1.
        eapply List.Forall2_impl; last exact H10.
        intros v tv Htv. exact Htv. 
    + fold_upd_context.
      eapply IHHReduce; eauto.

      eapply inst_typing_extension; eauto.
      (* eapply store_extension_reduce; eauto. *)
  - (* r_local *)
    apply Local_typing in HType as (ts' & -> & Hstyp & <-).
    apply et_weakening_empty_1.
    apply ety_local => //.
    inversion Hstyp. inversion H. subst.
    apply upd_label_unchanged_typing in H1.
    eapply mk_s_typing; eauto.
    + eapply mk_frame_typing => //. 
      * eapply inst_typing_extension; eauto.
(*        eapply store_extension_reduce; eauto. *)
        replace (f_inst f') with (f_inst f); eauto; first by eapply reduce_inst_unchanged; eauto.
      * eapply t_preservation_locals.
        exact HReduce. done. done.
        exact H8. 
        done.
        exact H1.
        eapply List.Forall2_impl; last exact H10.
        intros v tv Htv. exact Htv. 
    + fold_upd_context.
      eapply IHHReduce; eauto.
      eapply inst_typing_extension; eauto.
      (* eapply store_extension_reduce; eauto. *)

  - (* r_label *)
    
    generalize dependent k. generalize dependent les. generalize dependent les'.
    induction lh; move => les' les k HLF1 HLF2; move/lfilledP in HLF1; move/lfilledP in HLF2.
    all: split;
      [
        intros C tx ty HC HST1 HST2 Hsext HType
      |
        intros C tx ty lab ret ts HST1 HST2 Hsext HIT1 HIT2 Hts HType
      ].
                         
    + inversion HLF1.
      inversion HLF2. subst. clear HLF2. clear HLF1. clear H6.
      apply e_composition_typing in HType as (ts0 & t1s0 & t2s0 & t3s0 & -> & -> & Hvs & Haft).
      apply e_composition_typing in Haft as (ts1 & t1s1 & t2s1 & t3s1 & -> & -> & Hes & Hes'0).
      eapply et_composition'.
      -- instantiate (1 := ts0 ++ ts1 ++ t1s1).
         apply ety_weakening.
         eapply store_extension_e_typing.
         3: exact Hvs.
         done. eapply store_extension_reduce_strip_empty_context; eauto.
      -- eapply et_composition'; eauto.
         ++ instantiate (1 := ts0 ++ ts1 ++ t3s1).
            repeat apply ety_weakening.
            by eapply IHHReduce; eauto => //.
         ++ repeat apply ety_weakening.
            eapply store_extension_e_typing; try apply HST1 => //; try by [].
            (* eapply store_extension_reduce_strip_empty_context; eauto. *)
    + inversion HLF1.
      inversion HLF2. subst. clear HLF2. clear HLF1. clear H6.
      apply e_composition_typing in HType as (ts0 & t1s0 & t2s0 & t3s0 & -> & -> & Hvs & Haft).
      apply e_composition_typing in Haft as (ts1 & t1s1 & t2s1 & t3s1 & -> & -> & Hes & Hes'0).
      eapply et_composition'.
      -- instantiate (1 := ts0 ++ ts1 ++ t1s1).
         apply ety_weakening.
         eapply store_extension_e_typing.
         3: exact Hvs.
         done. eapply store_extension_reduce; eauto.
      -- eapply et_composition'; eauto.
         ++ instantiate (1 := ts0 ++ ts1 ++ t3s1).
            repeat apply ety_weakening.
            by eapply IHHReduce; eauto => //.
         ++ repeat apply ety_weakening.
            eapply store_extension_e_typing; try apply HST1 => //; try by [].
            (* eapply store_extension_reduce; eauto. *)

    + inversion HLF1. inversion HLF2. subst.
      inversion H11. subst. clear H11.
      move/lfilledP in H8. move/lfilledP in H18.
      apply e_composition_typing in HType.
      destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H2 [H3 [H4 H5]]]]]]]. subst.
      apply e_composition_typing in H5.
      destruct H5 as [ts1 [t1s1 [t2s1 [t3s1 [H10 [H11 [H12 H13]]]]]]]. subst.
      apply Label_typing in H12.
      destruct H12 as [ts2 [t2s2 [H14 [H15 [H16 H19]]]]]. subst.
      eapply et_composition'.
      -- instantiate (1 := ts0 ++ ts1 ++ t1s1).
         apply ety_weakening.
         eapply store_extension_e_typing.
         3: exact H4. done.
         eapply lfilled_es_type_exists in H16 as (? & ? & ? & Hes);
           last exact H8.
         eapply store_extension_reduce_strip_empty_context.
         3: exact Hes.
         done. exact HReduce. done.
      -- eapply et_composition'. 
         ++ instantiate (1 := ts0 ++ ts1 ++ t1s1 ++ t2s2).
            repeat apply ety_weakening.
            apply et_weakening_empty_1. 
            eapply ety_label. 3: done.
            ** simpl in H16. 
               eapply lfilled_es_type_exists in H16.
               2: exact H8. 
               destruct H16 as [lab' [t1s' [t2s' H16]]].
               rewrite upd_label_overwrite in H16.
               eapply store_extension_e_typing; try apply HST1 => //; try by [].
               (* eapply store_extension_reduce_strip_empty_context. 
               3: exact H16. done. exact HReduce. done. *)
            ** eapply IHlh; eauto.
         ++ repeat apply ety_weakening.
            simpl in H16. 
            eapply lfilled_es_type_exists in H16; eauto.
            destruct H16 as [lab' [t1s' [t2s' H16]]].
            rewrite upd_label_overwrite in H16. 
            eapply store_extension_e_typing; try apply HST1 => //; try by [].
            (* eapply store_extension_reduce_strip_empty_context.
            3: exact H16. done. exact HReduce. done. *)
    + inversion HLF1. inversion HLF2. subst.
      inversion H11. subst. clear H11.
      move/lfilledP in H8. move/lfilledP in H18.
      apply e_composition_typing in HType.
      destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H2 [H3 [H4 H5]]]]]]]. subst.
      apply e_composition_typing in H5.
      destruct H5 as [ts1 [t1s1 [t2s1 [t3s1 [H10 [H11 [H12 H13]]]]]]]. subst.
      apply Label_typing in H12.
      destruct H12 as [ts2 [t2s2 [H14 [H15 [H16 H19]]]]]. subst.
      eapply et_composition'.
      -- instantiate (1 := ts0 ++ ts1 ++ t1s1).
         apply ety_weakening.
         eapply store_extension_e_typing.
         3: exact H4. done.
         eapply lfilled_es_type_exists in H16 as (? & ? & ? & Hes);
           last exact H8.
         eapply store_extension_reduce; eauto.
         exact Hes.
      -- eapply et_composition'. 
         ++ instantiate (1 := ts0 ++ ts1 ++ t1s1 ++ t2s2).
            repeat apply ety_weakening.
            apply et_weakening_empty_1. 
            eapply ety_label. 3: done.
            ** simpl in H16. 
               eapply lfilled_es_type_exists in H16.
               2: exact H8. 
               destruct H16 as [lab' [t1s' [t2s' H16]]].
               rewrite upd_label_overwrite in H16.
               eapply store_extension_e_typing; try apply HST1 => //; try by [].
               (* eapply store_extension_reduce; eauto.
               exact H16.  *)
            ** eapply IHlh; eauto.
         ++ repeat apply ety_weakening.
            simpl in H16. 
            eapply lfilled_es_type_exists in H16; eauto.
            destruct H16 as [lab' [t1s' [t2s' H16]]].
            rewrite upd_label_overwrite in H16. 
            eapply store_extension_e_typing; try apply HST1 => //; try by [].
            (* eapply store_extension_reduce; eauto.
            exact H16.  *)
    + inversion HLF1. inversion HLF2; subst.
      apply e_composition_typing in HType as (ts0 & t1s0 & t2s0 & t3s0 & -> & -> & Hvs & Haft).
      apply e_composition_typing in Haft as (ts1 & t1s1 & t2s1 & t3s1 & -> & -> & Hes & Hes'0).
      apply Handler_typing in Hes as (t2s2 & -> & Hclauses & HLI).
      eapply et_composition'.
      -- instantiate (1 := ts0 ++ ts1 ++ t1s1).
         apply ety_weakening.
         eapply store_extension_e_typing.
         3: exact Hvs. done. 
         eapply lfilled_es_type_exists in HLI as (lab0 & t1s & t2s & Hes);
             last by apply lfilled_Ind_Equivalent; exact H7. 
         eapply store_extension_reduce_strip_empty_context.
         3: exact Hes. done. 
         exact HReduce. done. 
      -- eapply et_composition'; eauto.
         ++ instantiate (1 := ts0 ++ ts1 ++ t1s1 ++ _).
            do 2 apply ety_weakening. apply et_weakening_empty_1.
            apply ety_handler; eauto.
            eapply List.Forall_impl; last exact Hclauses.
            intros h Hh.
            eapply store_extension_exception_clause_typing; eauto.
            eapply IHlh; eauto.
            apply/lfilledP. exact H7.
            apply/lfilledP. exact H16.

         ++ do 2 apply ety_weakening.
            eapply store_extension_e_typing; last exact Hes'0.
            done.
            eapply lfilled_es_type_exists in HLI as (? & ? & ? & Hes);
              last by apply lfilled_Ind_Equivalent; exact H7.
            eapply store_extension_reduce_strip_empty_context.
            3: exact Hes. done. exact HReduce. done.
    + inversion HLF1. inversion HLF2; subst.
      apply e_composition_typing in HType as (ts0 & t1s0 & t2s0 & t3s0 & -> & -> & Hvs & Haft).
      apply e_composition_typing in Haft as (ts1 & t1s1 & t2s1 & t3s1 & -> & -> & Hes & Hes'0).
      apply Handler_typing in Hes as (t2s2 & -> & Hclauses & HLI).
      eapply et_composition'.
      -- instantiate (1 := ts0 ++ ts1 ++ t1s1).
         apply ety_weakening.
         eapply store_extension_e_typing.
         3: exact Hvs. done. 
         eapply lfilled_es_type_exists in HLI as (lab0 & t1s & t2s & Hes);
             last by apply lfilled_Ind_Equivalent; exact H7. 
         eapply store_extension_reduce; eauto.
         exact Hes. 
      -- eapply et_composition'; eauto.
         ++ instantiate (1 := ts0 ++ ts1 ++ t1s1 ++ _).
            do 2 apply ety_weakening. apply et_weakening_empty_1.
            apply ety_handler; eauto.
            eapply List.Forall_impl; last exact Hclauses.
            intros h Hh.
            eapply store_extension_exception_clause_typing; eauto.
            eapply IHlh; eauto.
            apply/lfilledP. exact H7.
            apply/lfilledP. exact H16.

         ++ do 2 apply ety_weakening.
            eapply store_extension_e_typing; last exact Hes'0.
            done.
            eapply lfilled_es_type_exists in HLI as (? & ? & ? & Hes);
              last by apply lfilled_Ind_Equivalent; exact H7.
            eapply store_extension_reduce; eauto.
            exact Hes. 
    + inversion HLF1. inversion HLF2; subst.
      apply e_composition_typing in HType as (ts0 & t1s0 & t2s0 & t3s0 & -> & -> & Hvs & Haft).
      apply e_composition_typing in Haft as (ts1 & t1s1 & t2s1 & t3s1 & -> & -> & Hes & Hes'0).
      apply Prompt_typing in Hes as (-> & Hclauses & HLI).
      eapply et_composition'.
      -- instantiate (1 := ts0 ++ ts1 ++ t1s1).
         apply ety_weakening.
         eapply store_extension_e_typing.
         3: exact Hvs. done. 
         eapply lfilled_es_type_exists in HLI as (lab0 & t1s & t2s & Hes);
             last by apply lfilled_Ind_Equivalent; exact H8. 
         eapply store_extension_reduce_strip_empty_context.
         3: exact Hes. done. exact HReduce. done. 
      -- eapply et_composition'; eauto.
         ++ instantiate (1 := ts0 ++ ts1 ++ t1s1 ++ _).
            do 2 apply ety_weakening. apply et_weakening_empty_1.
            apply ety_prompt; eauto.
            eapply List.Forall_impl; last exact Hclauses.
            intros h Hh.
            eapply store_extension_continuation_clause_typing; eauto.
            eapply IHlh; eauto.
            apply/lfilledP. exact H8.
            apply/lfilledP. exact H18. 

         ++ do 2 apply ety_weakening.
            eapply store_extension_e_typing; last exact Hes'0.
            done.
            eapply lfilled_es_type_exists in HLI as (? & ? & ? & Hes);
              last by apply lfilled_Ind_Equivalent; exact H8.
            eapply store_extension_reduce_strip_empty_context.
            3: exact Hes. done. exact HReduce. done.
    + inversion HLF1. inversion HLF2; subst.
      apply e_composition_typing in HType as (ts0 & t1s0 & t2s0 & t3s0 & -> & -> & Hvs & Haft).
      apply e_composition_typing in Haft as (ts1 & t1s1 & t2s1 & t3s1 & -> & -> & Hes & Hes'0).
      apply Prompt_typing in Hes as (-> & Hclauses & HLI).
      eapply et_composition'.
      -- instantiate (1 := ts0 ++ ts1 ++ t1s1).
         apply ety_weakening.
         eapply store_extension_e_typing.
         3: exact Hvs. done. 
         eapply lfilled_es_type_exists in HLI as (lab0 & t1s & t2s & Hes);
             last by apply lfilled_Ind_Equivalent; exact H8. 
         eapply store_extension_reduce_strip_empty_context.
         3: exact Hes. done. exact HReduce. done. 
      -- eapply et_composition'; eauto.
         ++ instantiate (1 := ts0 ++ ts1 ++ t1s1 ++ _).
            do 2 apply ety_weakening. apply et_weakening_empty_1.
            apply ety_prompt; eauto.
            eapply List.Forall_impl; last exact Hclauses.
            intros h Hh.
            eapply store_extension_continuation_clause_typing; eauto.
            eapply IHlh; eauto.
            apply/lfilledP. exact H8.
            apply/lfilledP. exact H18. 

         ++ do 2 apply ety_weakening.
            eapply store_extension_e_typing; last exact Hes'0.
            done.
            eapply lfilled_es_type_exists in HLI as (? & ? & ? & Hes);
              last by apply lfilled_Ind_Equivalent; exact H8.
            eapply store_extension_reduce_strip_empty_context.
            3: exact Hes. done. exact HReduce. done.
Qed.
  

(*

Lemma t_preservation_e: forall s f es s' f' es' C t1s t2s lab ret ts,
    reduce s f es s' f' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s f.(f_inst) C ->
    inst_typing s' f.(f_inst) C ->
    List.Forall2 (fun v tv => e_typing s empty_context [:: AI_const v] (Tf [::] [::tv]))
                 (f_locs f) ts ->
(*    map (typeof s) f.(f_locs) = map Some ts -> *)
    e_typing s (upd_label (upd_local_return C (tc_local C ++ ts) ret) lab) es (Tf t1s t2s) ->
    e_typing s' (upd_label (upd_local_return C (tc_local C ++ ts) ret) lab) es' (Tf t1s t2s).
Proof.
piggypack off previous lemma 
Qed. 
*)

  
Theorem t_preservation: forall s f es s' f' es' ts,
    reduce s f es s' f' es' ->
    config_typing s f es ts ->
    config_typing s' f' es' ts.
Proof.
  move => s f es s' f' es' ts HReduce HType.
  inversion HType. inversion H0. inversion H5. subst.
  assert (store_extension s s' /\ store_typing s').
  { apply upd_label_unchanged_typing in H7.
    eapply store_extension_reduce; eauto.
  }
  destruct H1.
  assert (inst_typing s' (f_inst f) C1); first by eapply inst_typing_extension; eauto.
  apply mk_config_typing; eauto.
  eapply mk_s_typing; eauto.
  - eapply mk_frame_typing; eauto.
    + symmetry. eapply reduce_inst_unchanged.
      exact HReduce.
    + eapply t_preservation_locals.
      * exact HReduce.
      * done.
      * done.
      * eauto.
      * done.
      * instantiate (1 := ts).
        instantiate (1 := [::]).
        instantiate (1 := tc_label C1).
        instantiate (1 := None).
        exact H7.
      * eapply List.Forall2_impl; last exact H16.
        intros v tv Htv. apply typing_empty_context. exact Htv. 
  - fold_upd_context.
    eapply t_preservation_strip_empty_context ; eauto.
Qed. 


