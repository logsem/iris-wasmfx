(** Proof of preservation **)

From Wasm Require Export common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program.Equality NArith ZArith_base.
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

(*
Lemma AI_ref_typing: forall s C r t1s t2s,
    e_typing s C [::AI_ref r] (Tf t1s t2s) ->
    exists cl tf,
      List.nth_error s.(s_funcs) r = Some cl /\
        cl_typing s cl tf /\
        t2s = t1s ++ [::T_ref (T_funcref tf)].
Proof.
  move => s C r t1s t2s HType.
  gen_ind_subst HType => //.
  - destruct bes => //.
  - apply extract_list1 in H2; inversion H2; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (cl & tf & Hf & Hcl & Ht2s) => //.
    exists cl, tf. repeat split => //. rewrite - catA. f_equal.
    done.
  - exists cl, tf; repeat split => //.
Qed. *)

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
  - edestruct IHHType as (t & Ht & Htype) => //.
    subst t2s. exists t. rewrite - catA. split => //. 
  - simpl. eexists. split => //. rewrite H. done. 
Qed.

(* Lemma AI_ref_cont_typing: forall s C r t1s t2s,
    e_typing s C [::AI_ref_cont r] (Tf t1s t2s) ->
    exists cl t1s' t2s',
      List.nth_error s.(s_funcs) r = Some cl /\
        cl_typing s cl (Tf t1s' t2s') /\
        t2s = t1s ++ [::T_ref (T_funcref (Cont t1s' t2s'))].
Proof.
  move => s C r t1s t2s HType.
  gen_ind_subst HType => //.
  - destruct bes => //.
  - apply extract_list1 in H2; inversion H2; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (cl & t1s' & t2s' & Hf & Hcl & Ht2s) => //.
    exists cl, t1s', t2s'. repeat split => //. rewrite - catA. f_equal.
    done.
  - exists cl, t1s, t2s; repeat split => //.
Qed. *)

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
    inversion H3; subst; rewrite H => //.
    eexists. split => //. split => //. eapply ety_ref_cont; eauto.
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
    exists ts t1s' t2s', List.nth_error (tc_types_t C) i = Some (Tf t1s' t2s') /\
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

    
Lemma Contnew_typing: forall C i t1s t2s,
    be_typing C [::BI_contnew i] (Tf t1s t2s) ->
    exists ts t1s' t2s', List.nth_error (tc_types_t C) i = Some (Tf t1s' t2s') /\
                      t1s = ts ++ [:: T_ref (T_funcref (Tf t1s' t2s'))] /\
                      t2s = ts ++ [:: T_ref (T_contref (Tf t1s' t2s'))].
Proof.
  move => C i t1s t2s HType.
  gen_ind_subst HType.
  - exists [::], t1, t2; repeat split => //.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (ts' & t1s' & t2s' & Htypes & ? & ?) => //=; subst.
    exists (ts ++ ts'), t1s', t2s'. repeat split => //=; by rewrite -catA.
Qed.

      
Lemma Resume_typing: forall C i hs t1s t2s,
    be_typing C [:: BI_resume i hs] (Tf t1s t2s) ->
    exists ts t1s' t2s', List.nth_error (tc_types_t C) i = Some (Tf t1s' t2s') /\
                      List.Forall (fun h => clause_typing C h t2s') hs /\
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
    exists ts t1s' t2s', List.nth_error (tc_tags_t C) i = Some (Tf t1s' t2s') /\
                      t1s = ts ++ t1s' /\
                      t2s = ts ++ t2s'.
Proof.
  move => C i t1s t2s HType.
  gen_ind_subst HType.
  - exists [::], t1s0, t2s0. repeat split => //.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_btyping in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType as (ts' & t1s' & t2s' & Htags & ? & ?) => //=; subst.
    exists (ts ++ ts'), t1s', t2s'. repeat split => //=; by rewrite -catA.
Qed. 

  
Lemma Contbind_typing: forall C i i' t1s t2s,
    be_typing C [::BI_contbind i i'] (Tf t1s t2s) ->
    exists ts t0s t1s' t2s',
      List.nth_error (tc_types_t C) i = Some (Tf (t0s ++ t1s') t2s') /\
        List.nth_error (tc_types_t C) i' = Some (Tf t1s' t2s') /\
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
      List.nth_error (tc_types_t C) i = Some (Tf t1s' t2s') /\
        List.nth_error (tc_tags_t C) x = Some (Tf t0s [::]) /\
        List.Forall (fun h => clause_typing C h t2s') hs /\
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
  destruct lh => //. destruct (const_list l) => //. move/eqP in H2.
  destruct l => //. destruct v => //. destruct v => //. destruct l => //.
  destruct l => //.
  destruct (const_list l) => //. fold lfill in H2. destruct (lfill _ _ _) => //.
  move/eqP in H2. destruct l => //. destruct v => //. destruct v => //. destruct l => //.
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
    admit.
  - admit.
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
              List.Forall (fun h => clause_typing (strip C) h ts2') hs /\
              e_typing s (strip C) es (Tf [::] ts2').
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
    destruct H as (-> & Hclauses & H).
    inversion Hremtf; subst.
    by exists x; try rewrite catA.     
  - (* ety_handler *)
    inversion Hremes. inversion Hremtf. subst.
    by exists ts2.
Qed.

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
  - rewrite List.app_length. lias.
  - apply/eqP. move/eqP in H0. apply nth_error_prefix => //.
  - rewrite List.app_length. lias.
  - apply/eqP. move/eqP in H0. apply nth_error_prefix => //.
  - eapply sub_all; last exact H.
    unfold subpred.
    intros x Hx. move/andP in Hx. destruct Hx as [??].
    apply/andP. split. rewrite List.app_length. lias.
    apply/eqP. move/eqP in H1. apply nth_error_prefix => //.
  - rewrite List.app_length. lias.
  - rewrite List.app_length. lias.
  - rewrite List.app_length. lias.
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
  - exact H0.
Qed. 
  


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
    unfold plop2 in H14. simpl in H14. move/eqP in H14. inversion H14. subst.
    clear H14.
    apply Const_list_typing in H7 as (ts' & Hts & H7 & Hconst).
    repeat rewrite length_is_size in HTSSLength.
    (* rewrite -catA in H0. *) rewrite list_nth_prefix in H0. inversion H0. subst. clear H0.
    assert ((ts0'' ++ ts1 == t1s') && (ts0 == ts')).
    + apply concat_cancel_last_n => //=. by rewrite - catA.
      rewrite HTSSLength. rewrite v_to_e_size. rewrite - (size_map (typeof s)).
      rewrite Hts. rewrite size_map. done.
    + move/andP in H. destruct H.
      move/eqP in H0. subst.
      eapply t_const_ignores_context; last exact Hconst.
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
    destruct H9 as (t2s'' & -> & Hclauses & H12). 
    simpl in H12.
    rewrite strip_upd_label in H12.
(*    rewrite -cat1s in H12. repeat rewrite catA in H12.
    remember ([::ts0''] ++ tss) as tss'. rewrite -catA in H12. 
    replace (k.+1+length tss) with (k + length tss') in H8. *)
    eapply IHlh => //=.
    + by apply H7.
    + eapply typing_leq. exact H12. eexists (tss ++ ts :: tc_label C), (tc_local C) => //=.
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
    subst. clear H6.
    apply Handler_typing in H9.
    destruct H9 as (ts2' & -> & Hclauses & Htyping).
    subst. simpl in H5.
    eapply IHlh => //; last by apply/lfilledP; exact H7.
    eapply typing_leq. exact Htyping. exists lab, (tc_local C) => //=.
Qed.

Lemma Local_return_typing: forall s C vs f LI tf n lh,
    e_typing s C [:: AI_local (length vs) f LI] tf ->
    const_list vs ->
    lfilled n lh (vs ++ [::AI_basic BI_return]) LI ->
    e_typing s C vs tf.
Proof.
  move => s C vs f LI tf n lh HType HConst HLF.
  destruct tf as [t1s t2s].
  apply Local_typing in HType.
  destruct HType as [ts [H1 [H2 H3]]]. subst.
  inversion H2. inversion H. subst. clear H4. clear H2. clear H.
  apply et_weakening_empty_1.
  assert (HET: e_typing s (upd_local_return C2 (tc_local C2 ++ tvs) (Some ts)) vs (Tf [::] ts)).
  { eapply Lfilled_return_typing; eauto. }
(*  apply et_to_bet in HET; last by apply const_list_is_basic. *)
  apply const_es_exists in HConst. destruct HConst. subst.
  apply Const_list_typing in HET as (ts' & Hts & HET & Hconst); subst => /=.
  eapply t_const_ignores_context; last exact Hconst.
  by apply v_to_e_is_const_list.
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
      by eapply t_const_ignores_context; eauto.
    
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
      by eapply t_const_ignores_context; eauto.
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
      by eapply t_const_ignores_context; eauto.
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
    i < length (tc_types_t C) /\
    List.nth_error (tc_types_t C) i = Some (Tf tn tm) /\
    t1s = ts ++ tn ++ [::T_num T_i32] /\ t2s = ts ++ tm.
Proof.
  move => i C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t1s0, t2s, [::].
  - invert_be_typing.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [tm [ts' [H1 [H2 [H3 [H4 H5]]]]]]. subst.
    exists x, tm, (ts ++ ts').
    by repeat rewrite -catA.
Qed.

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
  eapply all2_projection in H3; eauto.
  unfold functions_agree in H3. move/andP in H3. destruct H3.
  unfold option_map in H4.
  rewrite HN2 in H4. move/eqP in H4.
  by inversion H4.
Qed.

Lemma tc_func_reference2: forall s C i j cl tf,
  List.nth_error (inst_types i) j = Some (cl_type cl) ->
  inst_typing s i C ->
  List.nth_error (tc_types_t C) j = Some tf ->
  tf = cl_type cl.
Proof.
  move => s C i j cl tf HN1 HIT HN2.
  unfold inst_typing in HIT.
  destruct i => //=.
  destruct C => //=.
  destruct tc_local => //=.
  destruct tc_label => //=.
  destruct tc_return => //=.
  move/andP in HIT. destruct HIT.
  repeat (move/andP in H; destruct H).
  simpl in HN1. simpl in HN2.
  move/eqP in H. subst.
  rewrite HN1 in HN2.
  by inversion HN2.
Qed.

Lemma Invoke_func_native_typing: forall s i C a cl tn tm ts es t1s t2s,
    e_typing s C [::AI_invoke a] (Tf t1s t2s) ->
    List.nth_error s.(s_funcs) a = Some cl ->
    cl = FC_func_native i (Tf tn tm) ts es ->
    exists ts' C', t1s = ts' ++ tn /\ t2s = ts' ++ tm /\
                inst_typing s i C' /\
               be_typing (upd_local_label_return C' (tc_local C' ++ tn ++ ts) ([::tm] ++ tc_label C') (Some tm)) es (Tf [::] tm).
Proof.
  move => s i C a cl tn tm ts es t1s t2s HType HNth Hcl.
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
    rewrite H in HNth.
    inversion HNth; subst; clear HNth.
    inversion H0; subst.
    inversion H9; subst.
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
    inversion H0; subst.
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
  eapply all2_projection in H2; eauto.
  unfold globals_agree in H2. move/andP in H2. destruct H2.
  remove_bools_options.
  simpl in Hi. simpl in Hoption.
  unfold global_agree in H6.
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
  destruct t0 => //=.
  destruct t1 => //=.
  simpl in H2. simpl in H1.
  remove_bools_options.
  unfold tab_typing in H3.
  remove_bools_options.
  simpl in H3. simpl in H4.
  unfold tab_typing. simpl.
  simpl in HSize. inversion HSize. subst. clear HSize.
  apply/andP; split => //=.
  - rewrite length_is_size in H1. rewrite length_is_size. by rewrite H6 in H1.
  - assert (List.nth_error (t1 :: t2) n <> None).
    { apply List.nth_error_Some. rewrite length_is_size. simpl. rewrite -H6.
      by lias. }
    destruct (List.nth_error (t1 :: t2) n) eqn:HN => //=.
    destruct n => //=.
    + simpl in HN. simpl in Hoption. inversion HN. inversion Hoption. subst.
      apply/andP; split => //=; last by rewrite -H2.
      unfold tab_size. unfold tab_size in H3. by lias.
    + simpl in HN. simpl in Hoption.
      eapply all2_projection in H0; eauto.
      remove_bools_options.
      apply/andP; split => //=; last by rewrite -H7.
      unfold tab_size. unfold tab_size in H3. by lias.
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
  destruct (typeof_extension (datatypes.g_val g) HST) as [Htypeof | [Hcorrupt _]].
  + split => //; first by rewrite H. rewrite H0 Htypeof. done.
    (* rewrite Htypeof in H1. split; last done.
    apply/andP. split; first by rewrite H. by rewrite H1.  *)
  + rewrite Hcorrupt in H0. done. (* destruct Hcorrupt as (Hs & tf & Hs').
    rewrite Hs in H1. rewrite H1 in H0. done. *)
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
  destruct (typeof_extension (g_val g) HST) as [<- | [Hcorrupt _]].
  - destruct (typeof_extension (g_val g') HST) as [<- | [Hcorrupt _]] => //.
    rewrite Hcorrupt in Hext. remove_bools_options. rewrite H in H0 => //.
(*    move/andP in Hext. destruct Hext as [? ?] => //. *)
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
  remove_bools_options. rewrite - H4.
  repeat (apply/andP; split => //=; subst => //=).
  - eapply glob_extension_C. apply globals_agree_extension; eauto.
    apply glob_extension_extension; eauto.
  - by eapply tab_extension_C; eauto.
  - by eapply mem_extension_C; eauto.
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

Lemma frame_typing_extension: forall s s' f C,
    store_extension s s' ->
    frame_typing s f C ->
    frame_typing s' f C.
Proof.
  move => s s' f C HST HIT.
  unfold store_extension in HST. unfold operations.store_extension in HST.
  inversion HIT. subst.
  eapply inst_typing_extension in H; eauto.
  eapply mk_frame_typing; eauto.
  remember (f_locs f) as l.
  clear - H1 HST.
  generalize dependent tvs.
  induction l => //=.
  intros tvs; destruct tvs => //=.
  intros H; inversion H. rewrite H. f_equal; last by apply IHl.
  destruct (typeof_extension a HST) as [<- | [Hcorrupt _]] => //.
  by rewrite Hcorrupt in H1.
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
  done.
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
    exfalso. eapply Hcorrupt; last exact H. by left.
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
        destruct H as (ts & H1 & H2 & H3); subst 
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
    eapply IHHLF. eapply typing_leq. exact H4. apply strip_leq.
Qed.

Lemma store_extension_same: forall s,
    (forall x, List.In x (s_globals s) -> typeof s (g_val x) <> None) ->  
    store_extension s s.
Proof.
  move => s Hcorrupt. unfold store_extension.
  repeat (apply/andP; split).
  + by apply/eqP.
  + rewrite take_size. by apply all2_cont_extension_same.
  + by apply all2_tab_extension_same.
  + by apply all2_mem_extension_same.
  + by apply all2_glob_extension_same.
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

Lemma nth_take {A} l n k (x: A):
  List.nth_error (take n l) k = Some x ->
  List.nth_error l k = Some x.
Proof.
  generalize dependent n; generalize dependent k.
  induction l => //=.
  destruct n, k => //=. 
  apply IHl.
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

Lemma store_extension_e_typing: forall s s' C es tf,
    store_typing s ->
(*    store_typing s' -> *)
    store_extension s s' ->
    e_typing s C es tf -> e_typing s' C es tf.
Proof.
  move=> s s' C es tf HST1 (* HST2 *) Hext HType. move: s' HST1 (* HST2 *) Hext.
  apply e_typing_ind' with (e := HType)
    (P := fun s C es tf (_ : e_typing s C es tf) => forall s',
            store_typing s ->
        (*    store_typing s' -> *)
            store_extension s s' ->
            e_typing s' C es tf)
    (P0 := fun s rs f es ts (_ : s_typing s rs f es ts) => forall s',
             store_typing s ->
(*             store_typing s' -> *)
             store_extension s s' ->
             s_typing s' rs f es ts); clear HType s C es tf.
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
  - move=> s C n f es ts HType IHHType E s' HST1 (* HST2 *) Hext.
    apply ety_local => //.
    by eapply IHHType; try apply HST1 => //.
  - move => s C a tf cl Ha Hcl s' HST1 (* HST2 *) Hext.
    econstructor.
    unfold store_extension in Hext. remove_bools_options. rewrite - H. exact Ha.
    done. (* eapply store_extension_cl_typing. exact Hext. exact Hcl. *)
    
  - move => s C a cont Ha s' HST1 (* HST2 *) Hext.
    unfold store_extension in Hext. remove_bools_options.
    destruct (all2_nth Ha H3) as (cont' & Hs' & Hext).
    move/eqP in Hext. rewrite Hext.
    constructor. eapply nth_take. exact Hs'.
(*  - move => s C a Ha s' HST1 HST2 Hext.
    econstructor. unfold store_extension in Hext. remove_bools_options.
    rewrite - H3. exact Ha. *)
  - move => s C hs es ts Hclauses Hes IHHType s' HST1 (* HST2 *) Hext.
    econstructor. exact Hclauses. apply IHHType => //. 
  - move => s a C cl tf HNth HCLType s' HST1 (* HST2 *) Hext.
    replace (s_funcs s) with (s_funcs s') in HNth.
    eapply ety_invoke; eauto => //.
    by eapply store_extension_cl_typing; eauto.
    { unfold store_extension, operations.store_extension in Hext.
      by remove_bools_options. }  
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
  eapply all2_projection in H2; eauto.
  unfold globals_agree in H2.
  rewrite HN2 in H2.
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
      memory_list.mem_length m1 = memory_list.mem_length m2).

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
    destruct (pos + N.of_nat n1 <? N.of_nat (length (memory_list.ml_data m3)))%N eqn:HMemSize => //=.
    injection H1. move => H2. clear H1. subst.
    unfold memory_list.mem_length => /=.
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
    unfold mem_size, mem_length => /=.
    by rewrite HLen.
Qed.
  
Lemma mem_extension_store: forall m k off v tlen mem,
    store m k off (bits v) tlen = Some mem ->
    mem_extension m mem.
Proof.
  move => m k off v tlen mem HStore.
  unfold mem_extension.
  unfold store in HStore.
  destruct ((k + off + N.of_nat tlen <=? mem_length m)%N) eqn:HMemSize => //.
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
  destruct (mem_size m + c <=? page_limit)%N eqn:HLP => //.
  destruct (mem_max_opt m) eqn:HLimMax => //=.
  destruct ((mem_size m + c <=? n)%N) eqn:HLT => //.
  move : HMGrow.
  case: mem => mem_data_ mem_max_opt_ H.
  inversion H. subst. clear H.
  simpl.
  apply/andP.
  split => //.
  { unfold mem_size, mem_length, memory_list.mem_length in *.
    simpl.
    repeat rewrite length_is_size.
    rewrite size_cat.
    apply N.leb_le. 
    apply N.Div0.div_le_mono => //.
    by lias.
  }
  inversion HMGrow; subst; clear HMGrow.
  unfold mem_size, mem_length, memory_list.mem_length.
  simpl.
  apply/andP; split => //.
  apply N.leb_le.
  repeat rewrite length_is_size.
  rewrite size_cat.
  apply N.Div0.div_le_mono => //.
  by lias.
Qed.


 Lemma store_global_extension_store_typed: forall s s',
    store_typing s ->
    store_extension s s' ->
    (s_funcs s = s_funcs s') ->
    (s_conts s = s_conts s') ->
    (s_tables s = s_tables s') ->
    (s_mems s = s_mems s') ->
    store_typing s'.
Proof.
  move => s s' HST Hext HF HC HT HM.
  remember HST as HST'. clear HeqHST'.
  unfold store_typing in HST.
  unfold store_typing.
  destruct s => //=.
  destruct s' => //=.
  destruct HST as (Hf & Ht & Hm & Hc).
  rewrite -> List.Forall_forall in Hf.
  rewrite -> List.Forall_forall in Ht. 
  repeat split => //; remove_bools_options; simpl in HF; simpl in HT; simpl in HM; simpl in HC; subst.
  - rewrite -> List.Forall_forall. move => x HIN.
    apply Hf in HIN. unfold cl_type_check_single in HIN.
    destruct HIN.
    unfold cl_type_check_single.
    exists x0.
(*    inversion H1; subst. econstructor; eauto.
    + unfold inst_typing in H2. simpl in H2. destruct i, C; simpl in H2.
      unfold inst_typing => /=. destruct tc_local => //. destruct tc_label => //.
      destruct tc_return => //. remove_bools_options.
      rewrite H3 H4 H7 H2. repeat (apply/andP; split => //).
      apply all2_Forall2.
      eapply List.Forall2_impl; last by apply all2_Forall2 in H6; exact H6.
      intros i gt Hi. simpl in Hi. unfold globals_agree.
      move/andP in Hi; destruct Hi as [??]. apply/andP; split; last first.
      move/eqP in H9. rewrite - H9. apply/eqP. f_equal. *)

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
(*  - done. *)
  - rewrite List.Forall_forall. intros x Hin.
    rewrite List.Forall_forall in Hc.
    apply Hc in Hin. unfold continuation_typing in Hin.
    unfold continuation_typing. destruct x => //.
    destruct f => //. intros vs C x LI Hvs HLI.
    eapply Hin in HLI => //. eapply store_extension_e_typing; last exact HLI; try done. 
Qed. 

 Lemma store_memory_extension_store_typed: forall s s',
    store_typing s ->
    store_extension s s' ->
    (s_funcs s = s_funcs s') ->
    (s_tables s = s_tables s') ->
    (s_conts s = s_conts s') ->
    List.Forall mem_agree (s_mems s') ->
    store_typing s'.
Proof.
  move => s s' HST Hext HF HT HC HMem.
  remember HST as HST'. clear HeqHST'.
  unfold store_typing in HST.
  unfold store_typing.
  destruct s => //=.
  destruct s' => //=.
  destruct HST as (H & H0 & Hm & Hc).
  rewrite -> List.Forall_forall in H.
  rewrite -> List.Forall_forall in H0.
  repeat split => //; remove_bools_options; simpl in HF; simpl in HT; simpl in HC; subst.
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
    (*  - done. *)
  - apply List.Forall_forall. rewrite List.Forall_forall in Hc.
    intros cont Hin. apply Hc in Hin. destruct cont => //.
    destruct f => //. intros vs C x LI Hvs HLI. eapply Hin in HLI => //.
    eapply store_extension_e_typing; last exact HLI; try done. 
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
    assert (List.nth_error (take n l ++ [:: x'] ++ List.skipn (n+1)%Nrec l) (length (take n l)) = Some x'); first by apply list_nth_prefix.
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
  destruct ((k+off+N.of_nat tl <=? mem_length m)%N) eqn:H => //=.
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
  destruct (mem_size m + c <=? page_limit)%N eqn:HLP => //.
  destruct (mem_max_opt m) eqn:HLimMax => //=.
  - destruct ((mem_size m + c <=? n0)%N) eqn:H1 => //.
    inversion HGrow. unfold mem_size, mem_length, memory_list.mem_length in *. simpl in *. subst. clear HGrow.
    rewrite length_is_size. rewrite size_cat.
    repeat rewrite - length_is_size. rewrite List.repeat_length.
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
  end
.


Lemma is_const_AI_const v : is_const (AI_const v).
Proof. destruct v => //. destruct v => //. Qed.

Lemma hfilled_plug_value x v es h LI :
  hfilled x h (AI_const v :: es) LI <->
  hfilled x (hholed_plug_value h v) es LI.
Proof.
  generalize dependent LI.
  induction h; intros LI. 
  - unfold hfilled, hfill => /=. unfold const_list. rewrite List.forallb_app => /=.
    rewrite is_const_AI_const. destruct (List.forallb is_const l) => //=.
    rewrite separate1. rewrite - cat_app. repeat rewrite catA. done.
  - simpl. unfold hfilled, hfill. fold hfill.
    destruct (const_list l) => //. unfold hfilled in IHh.
    split.
    + destruct (hfill _ _ _) => //.
      destruct (IHh l2) as [IHh' _]. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ _) => //.
      move/eqP in IHh'; subst l2; done.
    + destruct (hfill _ (hholed_plug_value _ _) _) => //.
      destruct (IHh l2) as [_ IHh']. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ _) => //.
      move/eqP in IHh'; subst l2; done.
  - simpl. unfold hfilled, hfill. fold hfill.
    destruct (const_list l) => //. unfold hfilled in IHh.
    split.
    + destruct (hfill _ _ _) => //.
      destruct (IHh l1) as [IHh' _]. specialize (IHh' (eq_refl l1)).
      destruct (hfill _ _ _) => //.
      move/eqP in IHh'; subst l2; done.
    + destruct (hfill _ (hholed_plug_value _ _) _) => //.
      destruct (IHh l1) as [_ IHh']. specialize (IHh' (eq_refl l1)).
      destruct (hfill _ _ _) => //.
      move/eqP in IHh'; subst l2; done.
  - simpl. unfold hfilled, hfill. fold hfill.
    destruct (const_list l) => //.
    destruct (List.forallb _ _) => //. 
    unfold hfilled in IHh.
    split.
    + destruct (hfill _ _ _) => //.
      destruct (IHh l2) as [IHh' _]. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ _) => //.
      move/eqP in IHh'; subst l2; done.
    + destruct (hfill _ (hholed_plug_value _ _) _) => //.
      destruct (IHh l2) as [_ IHh']. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ _) => //.
      move/eqP in IHh'; subst l2; done.
Qed.


Fixpoint hholed_plug_right h es :=
  match h with
  | HH_base bef aft => HH_base bef (es ++ aft)
  | HH_label bef n es' h aft => HH_label bef n es' (hholed_plug_right h es) aft
  | HH_local bef n f h aft => HH_local bef n f (hholed_plug_right h es) aft
  | HH_handler bef hs h aft => HH_handler bef hs (hholed_plug_right h es) aft
  end
.

Lemma hfilled_app x h es1 es2 LI :
  hfilled x h (es1 ++ es2) LI <-> hfilled x (hholed_plug_right h es2) es1 LI.
Proof.
  generalize dependent LI.
  induction h; simpl; intros LI;
    unfold hfilled, hfill; fold hfill; destruct (const_list _) => //.
  - by repeat rewrite catA.
  - unfold hfilled in IHh.
    split.
    + destruct (hfill _ _ _) => //.
      destruct (IHh l2) as [IHh' _]. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ _) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ es1) => //.
      destruct (IHh l2) as [_ IHh']. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ _) => //.
      move/eqP in IHh'. subst. done.
  - unfold hfilled in IHh.
    split.
    + destruct (hfill _ _ _) => //.
      destruct (IHh l1) as [IHh' _]. specialize (IHh' (eq_refl l1)).
      destruct (hfill _ _ _) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ es1) => //.
      destruct (IHh l1) as [_ IHh']. specialize (IHh' (eq_refl l1)).
      destruct (hfill _ _ _) => //.
      move/eqP in IHh'. subst. done.
  - destruct (List.forallb _ _) => //.
    unfold hfilled in IHh.
    split.
    + destruct (hfill _ _ _) => //.
      destruct (IHh l2) as [IHh' _]. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ _) => //.
      move/eqP in IHh'. subst. done.
    + destruct (hfill _ _ es1) => //.
      destruct (IHh l2) as [_ IHh']. specialize (IHh' (eq_refl l2)).
      destruct (hfill _ _ _) => //.
      move/eqP in IHh'. subst. done.
Qed. 




Lemma store_extension_new_cont s cont:
   (forall x : global, List.In x (s_globals s) -> typeof s (g_val x) <> None) ->
  store_extension s (new_cont s cont).
Proof.
  intros Hcorrupt.
  repeat (apply/andP; split) ; destruct s => //=.
  + rewrite take_size_cat => //.
    by apply all2_cont_extension_same.
  + by apply all2_tab_extension_same.
  + by apply all2_mem_extension_same.
  + by apply all2_glob_extension_same.
Qed.

Lemma store_extension_upd_cont s k cont cont':
  (forall x : global, List.In x (s_globals s) -> typeof s (g_val x) <> None) ->
  List.nth_error (s_conts s) k = Some cont ->
  typeof_cont cont = typeof_cont cont' -> 
  store_extension s (upd_s_cont s k cont').
Proof.
  intros Hcorrupt Hk Hcontty.
  repeat (apply/andP; split); destruct s => //=.
  + unfold replace_nth_cont.
    simpl in Hk.
    clear- Hk Hcontty.
    generalize dependent k.
    induction s_conts; intros k Hk; first by rewrite take0.
    destruct k => //=.
    * rewrite take_size. apply/andP; split; last by apply all2_cont_extension_same.
      inversion Hk; subst. unfold cont_extension. by rewrite Hcontty.
    * simpl in Hk. apply/andP; split; first by apply/eqP.
      apply IHs_conts => //. 
  + by apply all2_tab_extension_same.
  + by apply all2_mem_extension_same.
  + by apply all2_glob_extension_same.
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
  - simpl in Ht. destruct (List.nth_error _ _) eqn:Hf => //. inversion Ht. apply ety_ref_cont.
    done.
Qed. 


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
Qed.

Lemma hfilled_change es2 x h es1 LI1:
  hfilled x h es1 LI1 ->
  exists LI2, hfilled x h es2 LI2.
Proof.
  generalize dependent LI1.
  induction h; intros LI1; unfold hfilled, hfill; fold hfill; destruct (const_list _) => //.
  - intros _; eexists _; done.
  - unfold hfilled in IHh. destruct (hfill _ _ _) => //.
    destruct (IHh l2 (eq_refl l2)) as [LI2 Hfill2].
    destruct (hfill _ _ es2) => //. intros _; eexists; done.
  - unfold hfilled in IHh. destruct (hfill _ _ _) => //.
    destruct (IHh l1 (eq_refl l1)) as [LI2 Hfill2].
    destruct (hfill _ _ es2) => //. intros _; eexists; done.
  - destruct (List.forallb _ _) => //.
    unfold hfilled in IHh. destruct (hfill _ _ _) => //.
    destruct (IHh l2 (eq_refl l2)) as [LI2 Hfill2].
    destruct (hfill _ _ es2) => //. intros _; eexists; done.
Qed. 
    

  

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
     
    
    

Lemma default_vals_typing s ts:
  map (typeof s) (default_vals ts) = map Some ts.
Proof.
  induction ts => //=.
  rewrite IHts => //=. f_equal.
  destruct a => //=. destruct n => //.
  destruct r => //=.
Qed. 

Lemma continuation_typing_new_cont s cont' cont:
  (forall x : global, List.In x (s_globals s) -> typeof s (g_val x) <> None) ->
  store_typing s ->
  continuation_typing s cont ->
  continuation_typing (new_cont s cont') cont.
Proof.
  intros Hcorrupt Hs Hcont.
  specialize (store_extension_new_cont cont' Hcorrupt) as Hsext.
  destruct cont => //. destruct f as [t1s t2s].
  intros vs C x LI Hvs HLI.
  destruct (hfilled_change (v_to_e_list (default_vals t1s)) HLI) as [LI' HLI'].
  eapply e_typing_plug_values.
  instantiate (1 := vs). rewrite Hvs.
  instantiate (1 := default_vals t1s). rewrite default_vals_typing. done.
  exact HLI'. exact HLI.
  eapply store_extension_e_typing. exact Hs. exact Hsext.
  eapply Hcont; last exact HLI'. apply default_vals_typing.
Qed. 
  


Lemma continuation_typing_upd_cont s cont1 cont2 k cont:
  (forall x : global, List.In x (s_globals s) -> typeof s (g_val x) <> None) ->
  store_typing s ->
  List.nth_error (s_conts s) k = Some cont1 ->
  typeof_cont cont1 = typeof_cont cont2 ->
  continuation_typing s cont ->
  continuation_typing (upd_s_cont s k cont2) cont.
Proof.
  intros Hcorrupt Hs Hk Hconts Hcont.
  specialize (store_extension_upd_cont Hcorrupt Hk Hconts) as Hsext. 
  destruct cont => //. destruct f as [t1s t2s].
  intros vs C x LI Hvs HLI.
  eapply store_extension_e_typing. 
  exact Hs. exact Hsext.
  eapply Hcont. 2: exact HLI.
  rewrite -Hvs. apply map_equiv.
  intros v Hin. eapply typeof_upd_cont. exact Hk. exact Hconts.
Qed. 

  

Lemma store_typing_new_cont s cont:
   (forall x : global, List.In x (s_globals s) -> typeof s (g_val x) <> None) ->
  store_typing s ->
  continuation_typing (new_cont s cont) cont ->
  store_typing (new_cont s cont).
Proof.
  intros Hcorrupt Hs Hcont.
  remember Hs as Hs'. clear HeqHs'.
  specialize (store_extension_new_cont cont Hcorrupt) as Hsext.
  unfold store_typing. unfold store_typing in Hs.
  destruct s => //=. 
  destruct Hs as (Hcl & Htabs & Hmems & Hconts).
  repeat split => //.
  + eapply List.Forall_impl; last exact Hcl.
    intros a [cl Hcltype].
    exists cl. eapply store_extension_cl_typing. exact Hsext. exact Hcltype. 
  + remember {|
            s_funcs := s_funcs;
            s_tables := s_tables;
            s_mems := s_mems;
            s_globals := s_globals;
            s_tags := s_tags;
            s_conts := s_conts
        |} as s.
    apply List.Forall_app. split.
    * eapply List.Forall_impl; last exact Hconts.
      intros cont' Hcont'. apply continuation_typing_new_cont. done. done. done.
    * constructor => //. 
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
    constructor => //. by inversion HP.
  - intros Hk HP Hcont'. inversion HP; subst. constructor => //.
    apply IHs_conts => //.
Qed. 

Lemma store_typing_upd_cont s k cont cont':
   (forall x : global, List.In x (s_globals s) -> typeof s (g_val x) <> None) ->
  store_typing s ->
  List.nth_error (s_conts s) k = Some cont ->
  typeof_cont cont = typeof_cont cont' ->
  continuation_typing (upd_s_cont s k cont') cont' ->
  store_typing (upd_s_cont s k cont').
Proof.
  intros Hcorrupt Hs Hk Hcontty Hcont.
  remember Hs as Hs'. clear HeqHs'.
  specialize (store_extension_upd_cont Hcorrupt Hk Hcontty) as H.
  unfold store_typing. unfold store_typing in Hs.
  destruct s => //=. (* simpl in *. *)
  destruct Hs as (Hcl & Htabs & Hmems & Hconts).
  repeat split => //.
  + eapply List.Forall_impl; last exact Hcl.
    intros a [cl Hcltype].
    exists cl. eapply store_extension_cl_typing. exact H. done.
  + eapply forall_replace_cont. exact Hk. 2:done.
    eapply List.Forall_impl; last exact Hconts.
    intros ??. eapply continuation_typing_upd_cont.
    exact Hcorrupt. exact Hs'. exact Hk. exact Hcontty. exact H0.
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

Lemma store_extension_trans s1 s2 s3:
  (forall x : global, List.In x (s_globals s3) -> typeof s1 (g_val x) <> None) ->
  store_extension s1 s2 ->
  store_extension s2 s3 ->
  store_extension s1 s3.
Proof.
  unfold store_extension.
  intros Hcorrupt H12 H23; remove_bools_options.
  rewrite H4 H. repeat (apply/andP; split).
  - done.
  - eapply all2_trans_prefix; try exact H3; try exact H8.
    intros c1 c2 c3 Hc1 Hc2.
    move/eqP in Hc1. move/eqP in Hc2. apply/eqP => //. by rewrite Hc1 Hc2.
  - eapply all2_trans; try exact H7; try exact H2.
    intros t1 t2 t3 Ht1 Ht2. move/andP in Ht1. move/andP in Ht2.
    destruct Ht1. destruct Ht2. move/eqP in H10. move/eqP in H12.
    apply/andP. split; first lias. by rewrite H10 H12.
  - eapply all2_trans; try exact H6; try exact H1.
    intros m1 m2 m3 Hm1 Hm2. move/andP in Hm1. move/andP in Hm2.
    destruct Hm1. destruct Hm2. move/eqP in H10. move/eqP in H12.
    apply/andP. apply N.leb_le in H9. apply N.leb_le in H11.
    split; first by apply N.leb_le; lias. by rewrite H10 H12.
  - eapply all2_trans_variation; try exact H5; try exact H0.
    unfold glob_extension. intros g1 g2 g3 Hin Hg1 Hg2.
    destruct (g_mut g1), (g_mut g2), (g_mut g3); remove_bools_options => //.
    + rewrite H12 H10. apply/andP => //.
    + apply/andP; split => //.
      destruct (@typeof_extension s1 s2 (g_val g2)), (@typeof_extension s1 s2 (g_val g3)).
      all: try by repeat (apply/andP; split => //); rewrite H4.
      * rewrite H11 H13 H9 H14. done.
      * destruct H14 as [H14 _]. exfalso. eapply Hcorrupt. exact Hin. exact H14.
      * destruct H13 as [H13 _]. rewrite H11 H13 in H12. done.
      * destruct H13 as [H13 _]. destruct H14 as [H14 _]. rewrite H11 H13 H14. done.
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
    simpl in Hcorrupt. eapply IHs_conts => //.
    exact Hcorrupt.
Qed.

(*
Lemma v_to_e_typing s C vs ts:
  map (typeof s) vs = map Some ts ->
  e_typing s C (v_to_e_list vs) (Tf [::] ts).
Proof.
  generalize dependent ts. induction vs; destruct ts => //=.
  - intros _. apply ety_a' => //. constructor.
  - intros H; inversion H. rewrite separate1. eapply et_composition'.
    + instantiate (1 := [:: v]).
      destruct a => //=.
      * apply ety_a'. constructor => //. inversion H1. apply bet_const.
      * destruct v0 => //=.
        -- apply ety_a'. constructor => //. inversion H1. constructor.
        -- unfold typeof in H1. unfold typeof_ref in H1.
           destruct (List.nth_error _ _) eqn:Hf => //.
           inversion H1. eapply ety_ref.
*)

Lemma store_extension_reduce: forall s f es s' f' es' C tf loc lab ret,
    (forall x : global, List.In x (s_globals s) -> typeof s (g_val x) <> None) ->
    reduce s f es s' f' es' ->
    inst_typing s f.(f_inst) C ->
    e_typing s (upd_label (upd_local_return C loc ret) lab) es tf ->
    store_typing s ->
    store_extension s s' /\ store_typing s'.
Proof.
  move => s f es s' f' es' C tf loc lab ret Hcorrupt HReduce.
  generalize dependent C. generalize dependent tf.
  generalize dependent loc. generalize dependent lab. generalize dependent ret.
  induction HReduce; try move => ret lab loc tf C HIT HType HST; try intros; destruct tf; (try by split => //; apply store_extension_same) ; (try by split; [apply store_extension_new_cont| apply store_typing_new_cont]); (try by eapply store_extension_upd_cont; eauto).
  - split; [apply store_extension_new_cont| apply store_typing_new_cont] => //.
    intros vs C' y LI Hvs HLI.
    unfold hfilled in HLI. unfold hfill in HLI. subst hh. simpl in HLI.
    move/eqP in HLI. subst LI. eapply et_composition'.
    apply Const_list_typing_empty.
    exact Hvs.
    rewrite separate1.

    rewrite separate1 in H2. destruct tf0.
    apply e_composition_typing in H2 as (ts & ts1 & ts2 & ts3 & -> & -> & Href & Hcontnew).
    apply AI_ref_typing in Href as (t & Ht & ->).
    apply et_to_bet in Hcontnew; last by constructor.
    apply Contnew_typing in Hcontnew as (ts' & t1s' & t2s' & Htypes & Hts1' & ->).
    apply concat_cancel_last in Hts1' as [-> ->].
    simpl in Ht. destruct (List.nth_error _ x) eqn:Hfuncs => //. 
    eapply ety_composition.
    + instantiate (1 := (l ++ [:: _])). apply et_weakening_empty_1.
      eapply ety_ref. rewrite Hfuncs. done. done.
    + eapply ety_a' => /=. constructor => //.
(*      replace C' with C. 2: admit. *)
      inversion Ht. unfold inst_typing in H1.
      destruct (f_inst f) eqn:Hi. destruct C.
      destruct tc_local => //. destruct tc_label => //.
      destruct tc_return => //. simpl in Htypes.
      repeat (move/andP in H1; destruct H1 as [H1 ?]).
      move/eqP in H1. subst inst_types. unfold stypes in H.  simpl in H.
      rewrite H in Htypes. inversion Htypes; subst. 
      
      apply bet_call_reference.
      rewrite H. by rewrite H2.
      done.

      
      simpl in Ht.
      admit.  
      inversion Ht. rewrite -H2 in Htypes.   
   instantiate (1 := f0).
      inversion Ht. eapply ety_ref. 
    
    Search (e_typing _ _ (v_to_e_list _) _). Search "Const_list".
  - edestruct store_extension_upd_cont.
    + exact Hcorrupt.
    + exact HST.
    + exact H3.
    + instantiate (1 := (Cont_dagger (Tf (ts ++ t1s) t2s))) => //. 
    + edestruct store_extension_new_cont; cycle 1.
      * exact H6.
      * apply List.nth_error_None in H4. apply List.nth_error_None.
        replace (length (s_conts (upd_s_cont s k (Cont_dagger (Tf (ts ++ t1s) t2s)))))
          with (length (s_conts s)); first exact H4.
        clear - H3. destruct s => /=. simpl in H3.
        generalize dependent k.
        induction s_conts; intros k Hk; destruct k => //.
        simpl in Hk. simpl. f_equal. apply IHs_conts => //. 
      * split; last exact H8.
        eapply store_extension_trans; last first.
        -- exact H7.
        -- exact H5.
        -- intros g Hin Habs.
           eapply Hcorrupt; last exact Habs.
           destruct s; simpl in Hin => //.
      * intros g Hin Habs. eapply Hcorrupt.
        -- instantiate (1 := g).
           destruct s; simpl in Hin => //.
        -- eapply typeof_upd_cont_corrupt. exact Habs.
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
      - eapply glob_extension_update_nth; eauto => //=.
        unfold glob_extension => //.
        unfold g_mut.
        apply/andP. unfold datatypes.g_val. 
        rewrite - H0. split => //.  rewrite Ht => //.
    } 
    split => //.
    by eapply store_global_extension_store_typed; eauto;
      destruct s => //=; destruct s' => //=; remove_bools_options.
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
      * by apply all2_glob_extension_same.
    + split => //.
      eapply store_memory_extension_store_typed; eauto => //=.
      remember HST as HST2. clear HeqHST2.
      unfold store_typing in HST.
      destruct s => //=.
      destruct HST as [_ [_ H11]].
      simpl in H1.
      assert (i < length s_mems)%coq_nat.
      { apply List.nth_error_Some. by rewrite H1. }
      inversion H0; subst. clear H0.
      apply Forall_update => //=.
      eapply store_mem_agree; eauto.
      * by destruct v => //=.
      * by move/ltP in H3.
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
      * by apply all2_glob_extension_same. } 
    split => //.
    eapply store_memory_extension_store_typed; eauto => //=.
    remember HST as HST2. clear HeqHST2.
    unfold store_typing in HST.
    destruct s => //=.
    destruct HST as [_ [_ H11]].
    simpl in H1.
    assert (i < length s_mems)%coq_nat.
    { apply List.nth_error_Some. by rewrite H1. }
    apply Forall_update => //=.
    eapply store_mem_agree; eauto.
    * by destruct tp => //=.
    * by move/ltP in H3.
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
      * by apply all2_glob_extension_same. }
    split => //.
    eapply store_memory_extension_store_typed; eauto => //=.
    remember HST as HST2. clear HeqHST2.
    unfold store_typing in HST.
    destruct s => //=.
    destruct HST as [_ [_ H11]].
    simpl in H0.
    assert (i < length s_mems)%coq_nat.
    { apply List.nth_error_Some. by rewrite H0. }
    apply Forall_update => //=.
    eapply mem_grow_mem_agree; eauto. by move/ltP in H1.
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
Qed. 

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
  
Lemma t_preservation_vs_type: forall s f es s' f' es' C C' lab ret t1s t2s ts,
    (forall x0 : global,
        List.In x0 (s_globals s) -> typeof s (g_val x0) <> None) ->
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
  move => s f es s' f' es' C C' lab ret t1s t2s ts Hcorruptg HReduce HST1 HST2 HIT1 HIT2 Hts HType.
  assert (store_extension s s') as Hextension.
  { eapply store_extension_reduce in HReduce as [? _] => //.
    exact HIT1. exact HType. } 
  generalize dependent t2s. generalize dependent t1s.
  generalize dependent lab. 
  induction HReduce => //;
     let t1s := fresh "t1s" in let t2s := fresh "t2s" in move => lab t1s t2s HType.
  - apply map_equiv. intros v Hin.
    destruct (@typeof_extension s (upd_s_cont s k (Cont_hh tf hh)) v) => //.
    exfalso. apply (map_in (typeof s)) in Hin. destruct H2 as [Habs _].
    rewrite Habs Hts in Hin. clear -Hin. induction ts => //. destruct Hin => //. 
  - apply map_equiv. intros v Hin.
    destruct (@typeof_extension s (upd_s_cont s k (Cont_dagger (Tf t1s t2s))) v) => //.
    exfalso. apply (map_in (typeof s)) in Hin. destruct H4 as [Habs _].
    rewrite Habs Hts in Hin. clear -Hin. induction ts => //. destruct Hin => //. 
  - apply map_equiv. intros v Hin.
    destruct (@typeof_extension s (upd_s_cont s k (Cont_hh (Tf t2s [::]) hh)) v) => //.
    exfalso. apply (map_in (typeof s)) in Hin. destruct H5 as [Habs _].
    rewrite Habs Hts in Hin. clear -Hin. induction ts => //. destruct Hin => //. 
  - apply map_equiv. intros v Hin.
    destruct (typeof_extension v Hextension) => //.
    exfalso. apply (map_in (typeof s)) in Hin. destruct H5 as [Habs _].
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
Qed.

Lemma inst_typing_func: forall s i j C a x,
  inst_typing s i C ->
  List.nth_error i.(inst_funcs) j = Some a ->
  List.nth_error (tc_func_t C) j = Some x ->
  exists cl, List.nth_error s.(s_funcs) a = Some cl.
Proof.
  move => s i j C a x HIT HNth1 HNth2.
    destruct s; destruct i; destruct C; destruct tc_local; destruct tc_label; destruct tc_return; unfold inst_typing, typing.inst_typing in * => //=; remove_bools_options; simpl in * => //=.
    remove_bools_options.
    unfold typing.functions_agree in H3.
    eapply all2_projection in H3; eauto.
    remove_bools_options; eauto.
Qed.

Lemma typeof_default ts s:
  map (typeof s) (default_vals ts) = map Some ts.
Proof.
  induction ts => //=.
  f_equal => //=. destruct a => //=. destruct n => //=. destruct r => //=.
Qed.

Lemma t_preservation_e: forall s f es s' f' es' C t1s t2s lab ret ts,
     (forall x0 : global,
        List.In x0 (s_globals s) -> typeof s (g_val x0) <> None) ->
    reduce s f es s' f' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s f.(f_inst) C ->
    inst_typing s' f.(f_inst) C ->
    (*     (forall v, List.In v f.(f_locs) -> typeof s v <> None) -> *)
    map (typeof s) f.(f_locs) = map Some ts ->
    e_typing s (upd_label (upd_local_return C (tc_local C ++ ts) ret) lab) es (Tf t1s t2s) ->
    e_typing s' (upd_label (upd_local_return C (tc_local C ++ ts) ret) lab) es' (Tf t1s t2s).
Proof.
  move => s f es s' f' es' C t1s t2s lab ret ts Hcorruptg HReduce HST1 HST2 HIT1 HIT2 Hts HType.
(*  specialize (t_preservation_vs_type Hcorruptg HReduce HST1 HST2 HIT1 HIT2 Hts HType) as Hlocs'.  *)
  generalize dependent C. generalize dependent ret. generalize dependent lab. generalize dependent t1s. generalize dependent t2s. 
(*  move: C ret lab t1s t2s. *)
  induction HReduce; (* move => C ret lab tx ty HIT1 HIT2 HType; *) intros ty tx lab ret C HIT1 HIT2 HType; subst; try eauto; try by apply ety_trap.
  - (* reduce_simple *)
    by eapply t_simple_preservation; eauto.
  - (* Ref_func *)
    convert_et_to_bet.
    apply Ref_func_typing in HType as (t & Hfuncs & ->).
    simpl in Hfuncs.
    apply et_weakening_empty_1.
    eapply inst_typing_func in HIT1 as [cl Hcl]; eauto.
    econstructor; eauto.
    assert (t = cl_type cl) as ->; first by eapply tc_func_reference1; eauto.
    eapply store_typed_cl_typed; eauto.
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
    by eapply store_typed_cl_typed; eauto.
  - (* Call_indirect *)
    convert_et_to_bet.
    replace [::BI_const (VAL_int32 c); BI_call_indirect i] with ([::BI_const (VAL_int32 c)] ++ [::BI_call_indirect i]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1' [H2 [H3 H4]]]]]]].
    subst.
    invert_be_typing.
    apply Call_indirect_typing in H4.
    destruct H4 as [tn [tm [ts'' [H5 [H6 [H7 [H8 H9]]]]]]].
    rewrite catA in H8. apply concat_cancel_last in H8. destruct H8. subst. 
    simpl in *.
    repeat apply ety_weakening.
    eapply ety_invoke; eauto.
    unfold stypes in H1.
    assert ((Tf tn tm) = cl_type cl) as HFType; first by eapply tc_func_reference2; eauto.
    rewrite HFType.
    by eapply store_typed_cl_typed; eauto.
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
    econstructor. exact H. unfold stypes in H0.
    assert (Tf t1s'' t2s'' = cl_type cl) as ->; first eapply tc_func_reference2; eauto.
    eapply store_typed_cl_typed; eauto.
    
    
  - (* Invoke native *)
    invert_e_typing.
    eapply Invoke_func_native_typing in H0; eauto.
    destruct H0 as [ts2 [C2 [H9 [H10 [H11 H12]]]]]. subst.
(*    apply et_to_bet in H3; last by apply const_list_is_basic; apply v_to_e_is_const_list. *)
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
    { rewrite H8. instantiate (1 := _ ++ _). do 2 rewrite map_cat.
      f_equal. 
      - exact Hts'.
      - rewrite typeof_default. done. } 
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
  - (* Contnew *)
    rewrite separate1 in HType.
    apply e_composition_typing in HType as (ts0 & t1s' & t2s' & t3s & -> & -> & HRef & HContnew).
    convert_et_to_bet.
    apply Contnew_typing in HContnew as (ts0' & t1s & t2s & Htypes & -> & ->).
    apply AI_ref_typing in HRef as (t & Ht & Hc).
    apply concat_cancel_last in Hc as [-> <-].
    apply ety_weakening. apply et_weakening_empty_1.
    replace (Tf t1s t2s) with (typeof_cont (Cont_hh tf (HH_base [::] [:: AI_ref x; AI_basic (BI_call_reference i)]))).
    + apply ety_ref_cont. simpl. unfold replace_nth_cont. rewrite nth_error_set_nth. done.
    + simpl. (* simpl in Ht. destruct (List.nth_error _ x) eqn:Hfuncs => //.
      inversion Ht. *) simpl in Htypes. unfold stypes in H. 
      destruct (f_inst f), C. unfold inst_typing in HIT1. destruct tc_local => //.
      destruct tc_label => //. destruct tc_return => //. remove_bools_options.
      rewrite H0 in H, Htypes. rewrite H in Htypes. by inversion Htypes.
  - (* Resume *)
    rewrite separate1 in HType.
    apply e_composition_typing in HType as (ts0 & t1s' & t2s' & t3s' & -> & -> & Hvs & Hrefres). 
    destruct (const_es_exists H) as [es ->].
    apply Const_list_typing in Hvs as (tsv & Htsv & -> & Hconst).
    apply e_composition_typing in Hrefres as (ts0' & t1s'' & t2s'' & t3s'' & Hts1 & -> & Hrefcont & Hresume).
    apply AI_ref_cont_typing in Hrefcont as (t & Ht & ->).
    convert_et_to_bet.
    apply Resume_typing in Hresume as (ts0'' & t1s''' & t2s''' & Htypes & Hclauses & Hts1' & ->).
    rewrite catA in Hts1'. apply concat_cancel_last in Hts1' as [-> ->].
    apply ety_weakening.
    apply concat_cancel_last_n in Hts1.
    { remove_bools_options; subst. apply et_weakening_empty_1. apply ety_handler.
      store_typing
    2:{ rewrite - (size_map Some tsv) - Htsv size_map.
    
  - (* Get_local *)
    convert_et_to_bet.
    apply Get_local_typing in HType.
    destruct HType as [t [H1 [H2 H3]]]. subst.
    apply ety_a'; auto_basic => //=.
    assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
    rewrite HCEmpty in H1. rewrite HCEmpty in H3. rewrite HCEmpty.
    simpl in H1. simpl in H3. simpl.
    apply nth_error_map in H1. destruct H1 as [v' [HNth Hvt]]. subst.
    apply bet_weakening_empty_1.
    rewrite H in HNth. inversion HNth; subst.
    by apply bet_const.
  - (* Set_local *)
    convert_et_to_bet.
    replace [::BI_const v; BI_set_local i] with ([::BI_const v] ++ [::BI_set_local i]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Set_local_typing in H10.
    destruct H10 as [t [H4 [H5 H6]]]. subst.
    apply ety_a'; auto_basic => //=.
    assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
    rewrite HCEmpty in H6. rewrite HCEmpty in H4. rewrite HCEmpty.
    simpl in H6. simpl in H5. simpl in H4. simpl.
    apply concat_cancel_last in H5. destruct H5. subst.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - (* Get_global *)
    convert_et_to_bet.
    apply Get_global_typing in HType.
    destruct HType as [t [H4 [H5 H6]]]. subst.
    apply ety_a'; auto_basic => //=.
    assert (tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
    rewrite H0 in H6. rewrite H0 in H4. rewrite H0.
    simpl in H6. simpl in H4. simpl.
    assert (typeof v = t); first by eapply global_type_reference; eauto.
    rewrite -H1.
    apply bet_weakening_empty_1.
    by apply bet_const.
  - (* Set_Global *)
    convert_et_to_bet.
    replace [::BI_const v; BI_set_global i] with ([::BI_const v] ++ [::BI_set_global i]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Set_global_typing in H10.
    destruct H10 as [g [t [H4 [H5 [H6 [H7 H8]]]]]]. subst.
    apply ety_a'; auto_basic => //=.
    simpl in H8. simpl in H4. simpl.
    apply concat_cancel_last in H7. destruct H7. subst.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - (* Load None *)
    convert_et_to_bet.
    replace [::BI_const (VAL_int32 k); BI_load t None a off] with ([::BI_const (VAL_int32 k)] ++ [::BI_load t None a off]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Load_typing in H10.
    destruct H10 as [ts  [H11 [H12 [H13 H14]]]].
    apply concat_cancel_last in H11. destruct H11. subst.
    eapply t_const_ignores_context => //=.
    instantiate (2 := s).
    apply ety_a'; auto_basic.
    simpl.
    assert (be_typing C [::BI_const (wasm_deserialise bs t)] (Tf [::] [:: typeof (wasm_deserialise bs t)])); first by apply bet_const.
    rewrite catA.
    apply bet_weakening_empty_1.
    rewrite typeof_deserialise in H2. by apply H2.
  - (* Load Some *)
    convert_et_to_bet.
    replace [::BI_const (VAL_int32 k); BI_load t (Some (tp, sx)) a off] with ([::BI_const (VAL_int32 k)] ++ [::BI_load t (Some (tp, sx)) a off]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H7 [H8 [H9 H10]]]]]]].
    invert_be_typing.
    apply Load_typing in H10.
    destruct H10 as [ts [H11 [H12 [H13 H14]]]].
    apply concat_cancel_last in H11. destruct H11. subst.
    eapply t_const_ignores_context => //=.
    instantiate (2 := s).
    apply ety_a'; auto_basic.
    simpl.
    assert (be_typing C [::BI_const (wasm_deserialise bs t)] (Tf [::] [:: typeof (wasm_deserialise bs t)])); first by apply bet_const.
    rewrite catA. apply bet_weakening_empty_1.
    rewrite typeof_deserialise in H2. by apply H2.
  - (* Store None *)
    + convert_et_to_bet.
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
    + convert_et_to_bet.
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
    destruct H10 as [ts [H11 [H12 H13]]]. subst.
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
    destruct H10 as [ts [H11 [H12 H13]]]. subst.
    simpl.
    apply ety_a'; auto_basic.
    rewrite catA.
    apply bet_weakening_empty_1.
    by apply bet_const.
  - (* r_label *)
    generalize dependent lh. generalize dependent les. generalize dependent les'.
    generalize dependent ty. generalize dependent tx. generalize dependent lab.
    induction k; move => lab tx ty les' les HType lh HLF1 HLF2; move/lfilledP in HLF1; move/lfilledP in HLF2.
    + inversion HLF1. inversion HLF2. subst. clear HLF1. clear HLF2.
      inversion H5. subst. clear H5. clear H0.
      apply e_composition_typing in HType.
      destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H2 [H3 [H4 H5]]]]]]]. subst.
      apply e_composition_typing in H5.
      destruct H5 as [ts1 [t1s1 [t2s1 [t3s1 [H6 [H7 [H8 H9]]]]]]]. subst.
      eapply et_composition'.
      -- instantiate (1 := ts0 ++ ts1 ++ t1s1).
         apply ety_weakening.
         by eapply t_const_ignores_context; eauto.
      -- eapply et_composition'; eauto.
         ++ instantiate (1 := ts0 ++ ts1 ++ t3s1).
            repeat apply ety_weakening.
            by eapply IHHReduce; eauto => //.
         ++ repeat apply ety_weakening.
            assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
            rewrite HCEmpty in H9. rewrite HCEmpty.
            replace (map typeof f'.(f_locs)) with (map typeof f.(f_locs)) => //.
            eapply store_extension_e_typing; try apply HST1 => //; try by [].
            eapply store_extension_reduce; eauto.
            by eapply t_preservation_vs_type; eauto.
    + inversion HLF1. inversion HLF2. subst.
      inversion H8. subst. clear H8.
      clear H6.
      move/lfilledP in H1. move/lfilledP in H7.
      apply e_composition_typing in HType.
      destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H2 [H3 [H4 H5]]]]]]]. subst.
      apply e_composition_typing in H5.
      destruct H5 as [ts1 [t1s1 [t2s1 [t3s1 [H10 [H11 [H12 H13]]]]]]]. subst.
      apply Label_typing in H12.
      destruct H12 as [ts2 [t2s2 [H14 [H15 [H16 H17]]]]]. subst.
      eapply et_composition'.
      -- instantiate (1 := ts0 ++ ts1 ++ t1s1).
         apply ety_weakening.
         by eapply t_const_ignores_context; eauto.
      -- eapply et_composition'; eauto.
         ++ instantiate (1 := ts0 ++ ts1 ++ t1s1 ++ t2s2).
            repeat apply ety_weakening.
            apply et_weakening_empty_1.
            eapply ety_label; eauto.
            * assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
              rewrite HCEmpty in H15. rewrite HCEmpty.
              simpl in H16. rewrite upd_label_overwrite in H16.
              eapply lfilled_es_type_exists in H16; eauto.
              destruct H16 as [lab' [t1s' [t2s' H16]]].
              rewrite upd_label_overwrite in H16.
              replace (map typeof f'.(f_locs)) with (map typeof f.(f_locs)) => //.
              eapply store_extension_e_typing; try apply HST1 => //; try by [].
              eapply store_extension_reduce; eauto.
              by eapply t_preservation_vs_type; eauto.
         ++ repeat apply ety_weakening.
            assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
            rewrite HCEmpty in H13. rewrite HCEmpty.
            simpl in H16. rewrite upd_label_overwrite in H16.
            eapply lfilled_es_type_exists in H16; eauto.
            destruct H16 as [lab' [t1s' [t2s' H16]]].
            rewrite upd_label_overwrite in H16.
            replace (map typeof f'.(f_locs)) with (map typeof f.(f_locs)) => //.
            eapply store_extension_e_typing; try apply HST1 => //; try by [].
            eapply store_extension_reduce; eauto.
            by eapply t_preservation_vs_type; eauto.
  - (* r_local *)
    apply Local_typing in HType.
    destruct HType as [ts [H1 [H2 H3]]]. subst.
    apply et_weakening_empty_1.
    apply ety_local => //.
    inversion H2. inversion H. subst.
    apply upd_label_unchanged_typing in H1.
    eapply mk_s_typing; eauto.
    + eapply mk_frame_typing => //.
      eapply inst_typing_extension; eauto.
      eapply store_extension_reduce; eauto.
      replace (f_inst f') with (f_inst f); eauto; first by eapply reduce_inst_unchanged; eauto.
    + fold_upd_context.
      eapply IHHReduce; eauto.
      eapply inst_typing_extension; eauto.
      eapply store_extension_reduce; eauto.
Qed.
  
Theorem t_preservation: forall s f es s' f' es' ts,
    reduce s f es s' f' es' ->
    config_typing s f es ts ->
    config_typing s' f' es' ts.
Proof.
  move => s f es s' f' es' ts HReduce HType.
  inversion HType. inversion H0. inversion H5. subst.
  assert (store_extension s s' /\ store_typing s').
  { apply upd_label_unchanged_typing in H7.
    by eapply store_extension_reduce; eauto. }
  destruct H1.
  assert (inst_typing s' (f_inst f) C1); first by eapply inst_typing_extension; eauto.
  apply mk_config_typing; eauto.
  eapply mk_s_typing; eauto.
  eapply mk_frame_typing; eauto.
  replace (f_inst f') with (f_inst f); eauto; first by eapply reduce_inst_unchanged; eauto.
  fold_upd_context.
  by eapply t_preservation_e; eauto.
Qed.


