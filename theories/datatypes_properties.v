(** Properties about Wasm datatypes (mainly equality relations) **)
(* (C) M. Bodin, J. Pichon - see LICENSE.txt *)

Require Import bytes common.
Require Export datatypes.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype seq.
From Stdlib Require Import Arith.PeanoNat.

From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Bullet Behavior "Strict Subproofs".


Scheme Equality for numtype.
Definition numtype_eqb v1 v2 : bool := numtype_eq_dec v1 v2.
Definition eqnumtypeP : Equality.axiom numtype_eqb :=
  eq_dec_Equality_axiom numtype_eq_dec.

Canonical Structure numtype_eqMixin := Equality.Mixin eqnumtypeP.
Canonical Structure numtype_eqType := Eval hnf in Equality.Pack (sort := numtype) (Equality.Class numtype_eqMixin).

Definition merge_list l := List.fold_left (fun acc i => acc + i) l 0.
Lemma merge_move x l : List.fold_left (fun acc i => acc + i) l x = x + List.fold_left (fun acc i => acc + i) l 0.
Proof.
  generalize dependent x.
  induction l; intros x => //=.
  - lias.
  - rewrite IHl.
    rewrite (IHl a).
    lias.
Qed. 

    
Lemma merge_nil : merge_list [::] = 0. Proof. done. Qed.
Lemma merge_list_singleton n : merge_list [:: n] = n. Proof. done. Qed. 
Lemma merge_cons x l : merge_list (x :: l) = x + merge_list l.
Proof.
  unfold merge_list => //=.
  by rewrite merge_move.
Qed. 


Fixpoint tu_size (tu: typeuse) :=
  match tu with
  | TU_def (DT_rec (RT_rec l) _) =>
      S (merge_list (map (fun '(ST_sub _ tus ct) =>
                            S (merge_list (map tu_size tus) +
                                 match ct with
                                 | CT_func (RT_res t1s) (RT_res t2s) =>
                                  S (merge_list (map (fun v =>
                                                     match v with
                                                     | VT_ref (RT_ref _ (HT_concrete tu)) =>
                                                         tu_size tu
                                                     | _ => 1
                                                     end) t1s) +
                                       merge_list  (map (fun v =>
                                                     match v with
                                                     | VT_ref (RT_ref _ (HT_concrete tu)) =>
                                                         tu_size tu
                                                     | _ => 1
                                                     end) t2s))
                              | CT_cont (RT_res t1s) (RT_res t2s) =>
                                  S (merge_list (map (fun v =>
                                                     match v with
                                                     | VT_ref (RT_ref _ (HT_concrete tu)) =>
                                                         tu_size tu
                                                     | _ => 1
                                                     end) t1s) +
                                    merge_list  (map (fun v =>
                                                     match v with
                                                     | VT_ref (RT_ref _ (HT_concrete tu)) =>
                                                         tu_size tu
                                                     | _ => 1
                                                     end) t2s))
                                 | CT_exn => 1
                              end)) l))
  | _ => 1
  end.
                                                  
                                                  


Lemma tu_size_not_zero t : tu_size t > 0.
Proof.
  destruct t => //=.
  destruct d => //=.
  destruct r => //=.
  lia. 
Qed.


Definition typeidx_eq_dec : forall tf1 tf2 : typeidx,
  {tf1 = tf2} + {tf1 <> tf2}.
Proof. decidable_equality. Defined.

Definition typeidx_eqb v1 v2 : bool := typeidx_eq_dec v1 v2.
Definition eqtypeidxP : Equality.axiom typeidx_eqb :=
  eq_dec_Equality_axiom typeidx_eq_dec.

Canonical Structure typeidx_eqMixin := Equality.Mixin eqtypeidxP.
Canonical Structure typeidx_eqType :=
  Eval hnf in Equality.Pack (sort := typeidx) (Equality.Class typeidx_eqMixin).

Definition typeuse_eq_dec : forall t1 t2: typeuse,
    { t1 = t2 } + { t1 <> t2 }.
Proof.
  assert (forall n t1 t2, tu_size t1 + tu_size t2 < n -> { t1 = t2 } + { t1 <> t2 }) as H.
  2:{ intros t1 t2; apply (H (S (tu_size t1 + tu_size t2))). done. }
  induction n; first lias.
  intros t1 t2 Hn.
  destruct t1, t2; try by (left + right).
  - destruct (typeidx_eq_dec t t0) eqn:Ht.
    + subst; by left.
    + right; intros Habs; inversion Habs; subst. done.
  - destruct d, d0.
    destruct (Nat.eqb n0 n1) eqn:Hn';
      last by right; intros Habs; inversion Habs; subst; rewrite Nat.eqb_refl in Hn'.
    apply Nat.eqb_eq in Hn' as ->.
    destruct r, r0.
    destruct l, l0; try by (left + right).
    destruct s, s0. 
    destruct (IHn (TU_def (DT_rec (RT_rec l) n1)) (TU_def (DT_rec (RT_rec l0) n1))) as [Heq | Hneq].
    + simpl in Hn. simpl. do 2 rewrite merge_cons in Hn.
      lia.
    + inversion Heq; subst l0; clear Heq. 
      destruct (Bool.eqb b b0) eqn:Hb;
        last by right; intros Habs; inversion Habs; subst; rewrite Bool.eqb_reflx in Hb.
      apply Bool.eqb_true_iff in Hb as ->.
      destruct l1, l2; try by right.
      * destruct c, c0; try by right.
        -- destruct r, r0, r1, r2.
           destruct l0, l2; try by right.
           ++ destruct l1, l3; try by (left + right).
              destruct (IHn (TU_def (DT_rec (RT_rec (ST_sub b0 [::] (CT_func (RT_res [::]) (RT_res l1)) :: l)) n1)) (TU_def (DT_rec (RT_rec (ST_sub b0 [::] (CT_func (RT_res [::]) (RT_res l3)) :: l)) n1))) as [Heq | Hneq].
              ** simpl in Hn. simpl. repeat rewrite merge_cons in Hn.
                 repeat rewrite merge_cons.
                 destruct v, v0; try lia.
                 destruct r, r0.
                 destruct h, h0.
                 specialize (tu_size_not_zero t) as Hnz.
                 specialize (tu_size_not_zero t0) as Hnz0.    
                 lia.
              ** inversion Heq; subst; clear Heq. 
                 destruct v, v0; try by right.
                 --- destruct (numtype_eq_dec n0 n2) as [-> | Hneq]; first by left.
                     right; intros Habs; inversion Habs; subst; done.
                 --- destruct r, r0.
                     destruct (Bool.eqb b b1) eqn:Hb;
                       last by right; intros Habs; inversion Habs; subst; rewrite Bool.eqb_reflx in Hb.
                     apply Bool.eqb_true_iff in Hb as ->.
                     destruct h, h0.
                     destruct (IHn t t0) as [-> | Hneq].
                     +++ simpl in Hn.
                         repeat rewrite merge_cons in Hn.
                         lia.
                     +++ by left.
                     +++ right; intros Habs; inversion Habs; subst => //.
              ** right; intros Habs; inversion Habs; subst => //.
           ++ destruct (IHn (TU_def (DT_rec (RT_rec (ST_sub b0 [::] (CT_func (RT_res l0) (RT_res l1)) :: l)) n1)) (TU_def (DT_rec (RT_rec (ST_sub b0 [::] (CT_func (RT_res l2) (RT_res l3)) :: l)) n1))) as [Heq | Hneq].
              ** simpl in Hn. simpl. repeat rewrite merge_cons in Hn.
                 repeat rewrite merge_cons.
                 destruct v, v0; try lia.
                 destruct r, r0.
                 destruct h, h0.
                 specialize (tu_size_not_zero t) as Hnz.
                 specialize (tu_size_not_zero t0) as Hnz0.    
                 lia.
              ** inversion Heq; subst; clear Heq. 
                 destruct v, v0; try by right.
                 --- destruct (numtype_eq_dec n0 n2) as [-> | Hneq]; first by left.
                     right; intros Habs; inversion Habs; subst; done.
                 --- destruct r, r0.
                     destruct (Bool.eqb b b1) eqn:Hb;
                       last by right; intros Habs; inversion Habs; subst; rewrite Bool.eqb_reflx in Hb.
                     apply Bool.eqb_true_iff in Hb as ->.
                     destruct h, h0.
                     destruct (IHn t t0) as [-> | Hneq].
                     +++ simpl in Hn.
                         repeat rewrite merge_cons in Hn.
                         lia.
                     +++ by left.
                     +++ right; intros Habs; inversion Habs; subst => //.
              ** right; intros Habs; inversion Habs; subst => //.
        -- destruct r, r0, r1, r2.
           destruct l0, l2; try by right.
           ++ destruct l1, l3; try by (left + right).
              destruct (IHn (TU_def (DT_rec (RT_rec (ST_sub b0 [::] (CT_func (RT_res [::]) (RT_res l1)) :: l)) n1)) (TU_def (DT_rec (RT_rec (ST_sub b0 [::] (CT_func (RT_res [::]) (RT_res l3)) :: l)) n1))) as [Heq | Hneq].
              ** simpl in Hn. simpl. repeat rewrite merge_cons in Hn.
                 repeat rewrite merge_cons.
                 destruct v, v0; try lia.
                 destruct r, r0.
                 destruct h, h0.
                 specialize (tu_size_not_zero t) as Hnz.
                 specialize (tu_size_not_zero t0) as Hnz0.    
                 lia.
              ** inversion Heq; subst; clear Heq. 
                 destruct v, v0; try by right.
                 --- destruct (numtype_eq_dec n0 n2) as [-> | Hneq]; first by left.
                     right; intros Habs; inversion Habs; subst; done.
                 --- destruct r, r0.
                     destruct (Bool.eqb b b1) eqn:Hb;
                       last by right; intros Habs; inversion Habs; subst; rewrite Bool.eqb_reflx in Hb.
                     apply Bool.eqb_true_iff in Hb as ->.
                     destruct h, h0.
                     destruct (IHn t t0) as [-> | Hneq].
                     +++ simpl in Hn.
                         repeat rewrite merge_cons in Hn.
                         lia.
                     +++ by left.
                     +++ right; intros Habs; inversion Habs; subst => //.
              ** right; intros Habs; inversion Habs; subst => //.
           ++ destruct (IHn (TU_def (DT_rec (RT_rec (ST_sub b0 [::] (CT_func (RT_res l0) (RT_res l1)) :: l)) n1)) (TU_def (DT_rec (RT_rec (ST_sub b0 [::] (CT_func (RT_res l2) (RT_res l3)) :: l)) n1))) as [Heq | Hneq].
              ** simpl in Hn. simpl. repeat rewrite merge_cons in Hn.
                 repeat rewrite merge_cons.
                 destruct v, v0; try lia.
                 destruct r, r0.
                 destruct h, h0.
                 specialize (tu_size_not_zero t) as Hnz.
                 specialize (tu_size_not_zero t0) as Hnz0.    
                 lia.
              ** inversion Heq; subst; clear Heq. 
                 destruct v, v0; try by right.
                 --- destruct (numtype_eq_dec n0 n2) as [-> | Hneq]; first by left.
                     right; intros Habs; inversion Habs; subst; done.
                 --- destruct r, r0.
                     destruct (Bool.eqb b b1) eqn:Hb;
                       last by right; intros Habs; inversion Habs; subst; rewrite Bool.eqb_reflx in Hb.
                     apply Bool.eqb_true_iff in Hb as ->.
                     destruct h, h0.
                     destruct (IHn t t0) as [-> | Hneq].
                     +++ simpl in Hn.
                         repeat rewrite merge_cons in Hn.
                         lia.
                     +++ by left.
                     +++ right; intros Habs; inversion Habs; subst => //.
              ** right; intros Habs; inversion Habs; subst => //.
        -- by left. 
      * destruct (IHn (TU_def (DT_rec (RT_rec (ST_sub b0 l1 c :: l)) n1))
                    (TU_def (DT_rec (RT_rec (ST_sub b0 l2 c0 :: l)) n1)))
          as [Heq | Hneq].
        -- simpl in Hn. simpl. repeat rewrite merge_cons in Hn.
           repeat rewrite merge_cons.
           specialize (tu_size_not_zero t) as Hnz.
           specialize (tu_size_not_zero t0) as Hnz0.
           lia.
        -- inversion Heq; subst; clear Heq.
           destruct (IHn t t0) as [-> | Hneq].
           ++ simpl in Hn. repeat rewrite merge_cons in Hn. lia.
           ++ by left.
           ++ right; intros Habs; inversion Habs; subst => //.
        -- right; intros Habs; inversion Habs; subst => //.
    + right; intros Habs; inversion Habs; subst => //.
  - destruct (Nat.eqb n0 n1) eqn:Hn';
      last by right; intros Habs; inversion Habs; subst; rewrite Nat.eqb_refl in Hn'.
    apply Nat.eqb_eq in Hn' as ->.
    by left. 
Defined.

Definition typeuse_eqb v1 v2 : bool := typeuse_eq_dec v1 v2.
Definition eqtypeuseP : Equality.axiom typeuse_eqb :=
  eq_dec_Equality_axiom typeuse_eq_dec.

Canonical Structure typeuse_eqMixin := Equality.Mixin eqtypeuseP.
Canonical Structure typeuse_eqType :=
  Eval hnf in Equality.Pack (sort := typeuse) (Equality.Class typeuse_eqMixin).


Definition heaptype_eq_dec : forall t1 t2: heaptype,
    { t1 = t2 } + { t1 <> t2 }.
Proof.
  destruct t1, t2.
  destruct (typeuse_eq_dec t t0) as [-> | Hneq].
  by left. right; intros Habs; inversion Habs => //.
Defined.

Definition heaptype_eqb v1 v2 : bool := heaptype_eq_dec v1 v2.
Definition eqheaptypeP : Equality.axiom heaptype_eqb :=
  eq_dec_Equality_axiom heaptype_eq_dec.

Canonical Structure heaptype_eqMixin := Equality.Mixin eqheaptypeP.
Canonical Structure heaptype_eqType :=
  Eval hnf in Equality.Pack (sort := heaptype) (Equality.Class heaptype_eqMixin).


Definition reftype_eq_dec : forall t1 t2: reftype,
    { t1 = t2 } + { t1 <> t2 }.
Proof.
  destruct t1, t2.
  destruct (Bool.eqb b b0) eqn:Hb;
    last by right; intros Habs; inversion Habs; subst; rewrite Bool.eqb_reflx in Hb.
  apply Bool.eqb_true_iff in Hb as ->.
  destruct (heaptype_eq_dec h h0) as [-> | Hneq].
  by left. right; intros Habs; inversion Habs => //.
Defined.

Definition reftype_eqb v1 v2 : bool := reftype_eq_dec v1 v2.
Definition eqreftypeP : Equality.axiom reftype_eqb :=
  eq_dec_Equality_axiom reftype_eq_dec.

Canonical Structure reftype_eqMixin := Equality.Mixin eqreftypeP.
Canonical Structure reftype_eqType :=
  Eval hnf in Equality.Pack (sort := reftype) (Equality.Class reftype_eqMixin).



Definition valtype_eq_dec : forall t1 t2: valtype,
    { t1 = t2 } + { t1 <> t2 }.
Proof.
  destruct t1, t2; try by right.
  destruct (numtype_eq_dec n n0) as [-> | Hneq].
  by left. right; intros Habs; inversion Habs => //.
  destruct (reftype_eq_dec r r0) as [-> | Hneq].
  by left. right; intros Habs; inversion Habs => //.
Defined. 

Definition valtype_eqb v1 v2 : bool := valtype_eq_dec v1 v2.
Definition eqvaltypeP : Equality.axiom valtype_eqb :=
  eq_dec_Equality_axiom valtype_eq_dec.

Canonical Structure valtype_eqMixin := Equality.Mixin eqvaltypeP.
Canonical Structure valtype_eqType :=
  Eval hnf in Equality.Pack (sort := valtype) (Equality.Class valtype_eqMixin).



Definition resulttype_eq_dec : forall t1 t2: resulttype,
    { t1 = t2 } + { t1 <> t2 }.
Proof.
  destruct t1, t2.
  generalize dependent l0.  
  induction l; destruct l0; try by right.
  by left.
  destruct (IHl l0) as [Heq | Hneq].
  inversion Heq; subst.
  destruct (valtype_eq_dec a v) as [-> | Hneq].
  by left. right; intros Habs; inversion Habs => //.
  right. intros Habs; inversion Habs; subst.
  done.
Defined.

Definition resulttype_eqb v1 v2 : bool := resulttype_eq_dec v1 v2.
Definition eqresulttypeP : Equality.axiom resulttype_eqb :=
  eq_dec_Equality_axiom resulttype_eq_dec.

Canonical Structure resulttype_eqMixin := Equality.Mixin eqresulttypeP.
Canonical Structure resulttype_eqType :=
  Eval hnf in Equality.Pack (sort := resulttype) (Equality.Class resulttype_eqMixin).



Definition comptype_eq_dec : forall t1 t2: comptype,
    { t1 = t2 } + { t1 <> t2 }.
Proof.
  destruct t1, t2; try by right.
  3: by left. 
  all: destruct (resulttype_eq_dec r r1) as [-> | Hneq].
  all: try by right; intros Habs; inversion Habs.
  all: destruct (resulttype_eq_dec r0 r2) as [-> | Hneq].
  all: try by right; intros Habs; inversion Habs.
  all: by left.
Defined.
Definition comptype_eqb v1 v2 : bool := comptype_eq_dec v1 v2.
Definition eqcomptypeP : Equality.axiom comptype_eqb :=
  eq_dec_Equality_axiom comptype_eq_dec.

Canonical Structure comptype_eqMixin := Equality.Mixin eqcomptypeP.
Canonical Structure comptype_eqType :=
  Eval hnf in Equality.Pack (sort := comptype) (Equality.Class comptype_eqMixin).



Definition subtype_eq_dec : forall t1 t2: subtype,
    { t1 = t2 } + { t1 <> t2 }.
Proof.
  destruct t1, t2.
  destruct (Bool.eqb b b0) eqn:Hb;
    last by right; intros Habs; inversion Habs; subst; rewrite Bool.eqb_reflx in Hb.
  apply Bool.eqb_true_iff in Hb as ->.
  destruct (comptype_eq_dec c c0) as [-> | Hneq].
  2: by right; intros Habs; inversion Habs => //.
  generalize dependent l0.
  induction l; destruct l0; try by right.
  by left.
  destruct (IHl l0) as [Heq | Hneq]; last by right; intros Habs; inversion Habs; subst.
  inversion Heq; subst.
  destruct (typeuse_eq_dec a t) as [-> | Hneq].
  by left. right; intros Habs; inversion Habs => //.
Defined.

Definition subtype_eqb v1 v2 : bool := subtype_eq_dec v1 v2.
Definition eqsubtypeP : Equality.axiom subtype_eqb :=
  eq_dec_Equality_axiom subtype_eq_dec.

Canonical Structure subtype_eqMixin := Equality.Mixin eqsubtypeP.
Canonical Structure subtype_eqType :=
  Eval hnf in Equality.Pack (sort := subtype) (Equality.Class subtype_eqMixin).



Definition rectype_eq_dec : forall t1 t2: rectype,
    { t1 = t2 } + { t1 <> t2 }.
Proof.
  destruct t1, t2.
  generalize dependent l0.  
  induction l; destruct l0; try by right.
  by left.
  destruct (IHl l0) as [Heq | Hneq].
  inversion Heq; subst.
  destruct (subtype_eq_dec a s) as [-> | Hneq].
  by left. right; intros Habs; inversion Habs => //.
  right. intros Habs; inversion Habs; subst.
  done.
Defined.

Definition rectype_eqb v1 v2 : bool := rectype_eq_dec v1 v2.
Definition eqrectypeP : Equality.axiom rectype_eqb :=
  eq_dec_Equality_axiom rectype_eq_dec.

Canonical Structure rectype_eqMixin := Equality.Mixin eqrectypeP.
Canonical Structure rectype_eqType :=
  Eval hnf in Equality.Pack (sort := rectype) (Equality.Class rectype_eqMixin).



Definition deftype_eq_dec : forall t1 t2: deftype,
    { t1 = t2 } + { t1 <> t2 }.
Proof.
  destruct t1, t2.
  destruct (Nat.eqb n0 n) eqn:Hn';
      last by right; intros Habs; inversion Habs; subst; rewrite Nat.eqb_refl in Hn'.
  apply Nat.eqb_eq in Hn' as ->.
  destruct (rectype_eq_dec r r0) as [-> | Hneq].
  by left. right; intros Habs; inversion Habs => //.
Defined. 

Definition deftype_eqb v1 v2 : bool := deftype_eq_dec v1 v2.
Definition eqdeftypeP : Equality.axiom deftype_eqb :=
  eq_dec_Equality_axiom deftype_eq_dec.

Canonical Structure deftype_eqMixin := Equality.Mixin eqdeftypeP.
Canonical Structure deftype_eqType :=
  Eval hnf in Equality.Pack (sort := deftype) (Equality.Class deftype_eqMixin).


  





From mathcomp Require Import ssrnat.

Canonical Structure immediate_eqType :=
  Eval hnf in Equality.Pack (sort := immediate) (Equality.Class nat_eqMixin).
Canonical Structure funcaddr_eqType :=
  Eval hnf in Equality.Pack (sort := funcaddr) (Equality.Class nat_eqMixin).
Canonical Structure tableaddr_eqType :=
  Eval hnf in Equality.Pack (sort := tableaddr) (Equality.Class nat_eqMixin).
Canonical Structure memaddr_eqType :=
  Eval hnf in Equality.Pack (sort := memaddr) (Equality.Class nat_eqMixin).
Canonical Structure globaladdr_eqType :=
  Eval hnf in Equality.Pack (sort := globaladdr) (Equality.Class nat_eqMixin).

Definition ascii_eq_dec : forall tf1 tf2 : Ascii.ascii,
  {tf1 = tf2} + {tf1 <> tf2}.
Proof. decidable_equality. Defined.

Definition ascii_eqb v1 v2 : bool := ascii_eq_dec v1 v2.
Definition eqasciiP : Equality.axiom ascii_eqb :=
  eq_dec_Equality_axiom ascii_eq_dec.

Canonical Structure ascii_eqMixin := Equality.Mixin eqasciiP.
Canonical Structure ascii_eqType :=
  Eval hnf in Equality.Pack (sort := Ascii.ascii) (Equality.Class ascii_eqMixin).

Definition byte_eqb v1 v2 : bool := Byte.byte_eq_dec v1 v2.
Definition eqbyteP : Equality.axiom byte_eqb :=
  eq_dec_Equality_axiom Byte.byte_eq_dec.

Canonical Structure byte_eqMixin := Equality.Mixin eqbyteP.
Canonical Structure byte_eqType :=
  Eval hnf in Equality.Pack (sort := Byte.byte) (Equality.Class byte_eqMixin).


Scheme Equality for packed_type.
Definition packed_type_eqb v1 v2 : bool := packed_type_eq_dec v1 v2.
Definition eqpacked_typeP : Equality.axiom packed_type_eqb :=
  eq_dec_Equality_axiom packed_type_eq_dec.

Canonical Structure packed_type_eqMixin := Equality.Mixin eqpacked_typeP.
Canonical Structure packed_type_eqType := Eval hnf in Equality.Pack (sort := packed_type) (Equality.Class packed_type_eqMixin).

Scheme Equality for mutability.
Definition mutability_eqb v1 v2 : bool := mutability_eq_dec v1 v2.
Definition eqmutabilityP : Equality.axiom mutability_eqb :=
  eq_dec_Equality_axiom mutability_eq_dec.

Canonical Structure mutability_eqMixin := Equality.Mixin eqmutabilityP.
Canonical Structure mutability_eqType := Eval hnf in Equality.Pack (sort := mutability) (Equality.Class mutability_eqMixin).

Definition global_type_eq_dec : forall g1 g2: global_type,
    { g1 = g2 } + { g1 <> g2 }.
Proof.
  intros g1 g2; destruct g1, g2.
  destruct (mutability_eq_dec tg_mut tg_mut0); last by right; intros Habs; inversion Habs; subst.
  destruct (valtype_eq_dec tg_t tg_t0); last by right; intros Habs; inversion Habs; subst.
  subst; by left.
Qed. 
Definition global_type_eqb v1 v2 : bool := global_type_eq_dec v1 v2.
Definition eqglobal_typeP : Equality.axiom global_type_eqb :=
  eq_dec_Equality_axiom global_type_eq_dec.

Canonical Structure global_type_eqMixin := Equality.Mixin eqglobal_typeP.
Canonical Structure global_type_eqType := Eval hnf in Equality.Pack (sort := global_type) (Equality.Class global_type_eqMixin). 


Definition t_context_eq_dec : forall x y : t_context, {x = y} + {x <> y}.
Proof. decidable_equality. Defined.

Definition t_context_eqb v1 v2 : bool := t_context_eq_dec v1 v2.
Definition eqt_contextP : Equality.axiom t_context_eqb :=
  eq_dec_Equality_axiom t_context_eq_dec.

Canonical Structure t_context_eqMixin := Equality.Mixin eqt_contextP.
Canonical Structure t_context_eqType := Eval hnf in Equality.Pack (sort := t_context) (Equality.Class t_context_eqMixin). 

Scheme Equality for sx.
Definition sx_eqb v1 v2 : bool := sx_eq_dec v1 v2.
Definition eqsxP : Equality.axiom sx_eqb :=
  eq_dec_Equality_axiom sx_eq_dec.

Canonical Structure sx_eqMixin := Equality.Mixin eqsxP.
Canonical Structure sx_eqType := Eval hnf in Equality.Pack (sort := sx) (Equality.Class sx_eqMixin).

Scheme Equality for unop_i.
Definition unop_i_eqb v1 v2 : bool := unop_i_eq_dec v1 v2.
Definition equnop_iP : Equality.axiom unop_i_eqb :=
  eq_dec_Equality_axiom unop_i_eq_dec.

Canonical Structure unop_i_eqMixin := Equality.Mixin equnop_iP.
Canonical Structure unop_i_eqType := Eval hnf in Equality.Pack (sort := unop_i) (Equality.Class unop_i_eqMixin).

Scheme Equality for unop_f.
Definition unop_f_eqb v1 v2 : bool := unop_f_eq_dec v1 v2.
Definition equnop_fP : Equality.axiom unop_f_eqb :=
  eq_dec_Equality_axiom unop_f_eq_dec.

Canonical Structure unop_f_eqMixin := Equality.Mixin equnop_fP.
Canonical Structure unop_f_eqType := Eval hnf in Equality.Pack (sort := unop_f) (Equality.Class unop_f_eqMixin).

Scheme Equality for binop_i.
Definition binop_i_eqb v1 v2 : bool := binop_i_eq_dec v1 v2.
Definition eqbinop_iP : Equality.axiom binop_i_eqb :=
  eq_dec_Equality_axiom binop_i_eq_dec.

Canonical Structure binop_i_eqMixin := Equality.Mixin eqbinop_iP.
Canonical Structure binop_i_eqType := Eval hnf in Equality.Pack (sort := binop_i) (Equality.Class binop_i_eqMixin).

Scheme Equality for binop_f.
Definition binop_f_eqb v1 v2 : bool := binop_f_eq_dec v1 v2.
Definition eqbinop_fP : Equality.axiom binop_f_eqb :=
  eq_dec_Equality_axiom binop_f_eq_dec.

Canonical Structure binop_f_eqMixin := Equality.Mixin eqbinop_fP.
Canonical Structure binop_f_eqType := Eval hnf in Equality.Pack (sort := binop_f) (Equality.Class binop_f_eqMixin).

Scheme Equality for testop.
Definition testop_eqb v1 v2 : bool := testop_eq_dec v1 v2.
Definition eqtestopP : Equality.axiom testop_eqb :=
  eq_dec_Equality_axiom testop_eq_dec.

Canonical Structure testop_eqMixin := Equality.Mixin eqtestopP.
Canonical Structure testop_eqType := Eval hnf in Equality.Pack (sort := testop) (Equality.Class testop_eqMixin).

Scheme Equality for relop_i.
Definition relop_i_eqb v1 v2 : bool := relop_i_eq_dec v1 v2.
Definition eqrelop_iP : Equality.axiom relop_i_eqb :=
  eq_dec_Equality_axiom relop_i_eq_dec.

Canonical Structure relop_i_eqMixin := Equality.Mixin eqrelop_iP.
Canonical Structure relop_i_eqType := Eval hnf in Equality.Pack (sort := relop_i) (Equality.Class relop_i_eqMixin).

Scheme Equality for relop_f.
Definition relop_f_eqb v1 v2 : bool := relop_f_eq_dec v1 v2.
Definition eqrelop_fP : Equality.axiom relop_f_eqb :=
  eq_dec_Equality_axiom relop_f_eq_dec.

Canonical Structure relop_f_eqMixin := Equality.Mixin eqrelop_fP.
Canonical Structure relop_f_eqType := Eval hnf in Equality.Pack (sort := relop_f) (Equality.Class relop_f_eqMixin).

Scheme Equality for cvtop.
Definition cvtop_eqb v1 v2 : bool := cvtop_eq_dec v1 v2.
Definition eqcvtopP : Equality.axiom cvtop_eqb :=
  eq_dec_Equality_axiom cvtop_eq_dec.

Canonical Structure cvtop_eqMixin := Equality.Mixin eqcvtopP.
Canonical Structure cvtop_eqType := Eval hnf in Equality.Pack (sort := cvtop) (Equality.Class cvtop_eqMixin).

 Definition value_eq_dec : forall v1 v2 : value, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition value_eqb v1 v2 : bool := value_eq_dec v1 v2.
Definition eqvalueP : Equality.axiom value_eqb :=
  eq_dec_Equality_axiom value_eq_dec.

Canonical Structure value_eqMixin := Equality.Mixin eqvalueP.
Canonical Structure value_eqType := Eval hnf in Equality.Pack (sort := value) (Equality.Class value_eqMixin). 

(** Some helper functions for [value] that can safely extract. **)
Definition value_num_rec_safe (P : Type)
           (i32 : Wasm_int.Int32.int -> P)
           (i64 : Wasm_int.Int64.int -> P)
           (f32 : Wasm_float.FloatSize32.T -> P)
           (f64 : Wasm_float.FloatSize64.T -> P) v : P :=
  value_num_rect i32 i64 f32 f64 v.

(*
Definition value_ref_rec_safe (P : Type)
  (null : reference_type -> P)
  (func : funcaddr -> P)
  (cont : funcaddr -> P)
  (exn : exnaddr -> tagidx -> P)
(*  (extern : externaddr -> P) *)
  v : P :=
  value_ref_rect null func cont (* extern *) exn v.
*)
(* Definition value_rec_safe (P : Type)
           (i32 : Wasm_int.Int32.int -> P)
           (i64 : Wasm_int.Int64.int -> P)
           (f32 : Wasm_float.FloatSize32.T -> P)
           (f64 : Wasm_float.FloatSize64.T -> P)
 (null : reference_type -> P)
  (func : funcaddr -> P)
  (extern : externaddr -> P)
           v : P :=
  value_rect (value_num_rec_safe i32 i64 f32 f64 v) (value_ref_rec_safe null func extern v) v. *)

(** Induction scheme for [basic_instruction]. **)
Definition basic_instruction_rect' :=
  ltac:(rect'_build basic_instruction_rect).

Definition basic_instruction_ind' (P : basic_instruction -> Prop) :=
  @basic_instruction_rect' P.

 Definition basic_instruction_eq_dec : forall e1 e2 : basic_instruction,
  {e1 = e2} + {e1 <> e2}.
Proof. decidable_equality_using basic_instruction_rect'. Defined.

Definition basic_instruction_eqb cl1 cl2 : bool :=
  basic_instruction_eq_dec cl1 cl2.
Definition eqbasic_instructionP : Equality.axiom basic_instruction_eqb :=
  eq_dec_Equality_axiom basic_instruction_eq_dec.

Canonical Structure basic_instruction_eqMixin := Equality.Mixin eqbasic_instructionP.
Canonical Structure basic_instruction_eqType :=
  Eval hnf in Equality.Pack (sort := basic_instruction) (Equality.Class basic_instruction_eqMixin). 

 Definition instance_eq_dec : forall (i1 i2 : instance), {i1 = i2} + {i1 <> i2}.
Proof. decidable_equality. Defined.

Definition instance_eqb i1 i2 : bool := instance_eq_dec i1 i2.

Definition eqinstanceP : Equality.axiom instance_eqb :=
  eq_dec_Equality_axiom instance_eq_dec.

Canonical Structure instance_eqMixin := Equality.Mixin eqinstanceP.
Canonical Structure instance_eqType := Eval hnf in Equality.Pack (sort := instance) (Equality.Class instance_eqMixin).



Local Definition administrative_instruction_rect :=
  @administrative_instruction_rect
  : forall (P : administrative_instruction -> Type), _.

 Definition funcinst_eq_dec : forall (cl1 cl2 : funcinst),
  {cl1 = cl2} + {cl1 <> cl2}.
Proof. decidable_equality. Defined.

Definition funcinst_eqb cl1 cl2 : bool := funcinst_eq_dec cl1 cl2.
Definition eqfuncinstP : Equality.axiom funcinst_eqb :=
  eq_dec_Equality_axiom funcinst_eq_dec.

Canonical Structure funcinst_eqMixin := Equality.Mixin eqfuncinstP.
Canonical Structure funcinst_eqType :=
  Eval hnf in Equality.Pack (sort := funcinst) (Equality.Class funcinst_eqMixin). 

Definition tableinst_eq_dec : forall v1 v2 : tableinst, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.
  
Definition tableinst_eqb v1 v2 : bool := tableinst_eq_dec v1 v2.
Definition eqtableinstP : Equality.axiom tableinst_eqb :=
  eq_dec_Equality_axiom tableinst_eq_dec.

Canonical Structure tableinst_eqMixin := Equality.Mixin eqtableinstP.
Canonical Structure tableinst_eqType := Eval hnf in Equality.Pack (sort := tableinst) (Equality.Class tableinst_eqMixin).

Definition global_eq_dec : forall v1 v2 : global, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition global_eqb v1 v2 : bool := global_eq_dec v1 v2.
Definition eqglobalP : Equality.axiom global_eqb :=
  eq_dec_Equality_axiom global_eq_dec.

Canonical Structure global_eqMixin := Equality.Mixin eqglobalP.
Canonical Structure global_eqType := Eval hnf in Equality.Pack (sort := global) (Equality.Class global_eqMixin). 




 
Definition frame_eq_dec : forall v1 v2 : frame, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition frame_eqb v1 v2 : bool := frame_eq_dec v1 v2.
Definition eqframeP : Equality.axiom frame_eqb :=
  eq_dec_Equality_axiom frame_eq_dec.

Canonical Structure frame_eqMixin := Equality.Mixin eqframeP.
Canonical Structure frame_eqType := Eval hnf in Equality.Pack (sort := frame) (Equality.Class frame_eqMixin).

Definition module_export_desc_eq_dec : forall v1 v2 : module_export_desc, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition module_export_desc_eqb v1 v2 : bool := module_export_desc_eq_dec v1 v2.
Definition eqmodule_export_descP : Equality.axiom module_export_desc_eqb :=
  eq_dec_Equality_axiom module_export_desc_eq_dec.

Canonical Structure module_export_desc_eqMixin := Equality.Mixin eqmodule_export_descP.
Canonical Structure module_export_desc_eqType :=
  Eval hnf in Equality.Pack (sort := module_export_desc) (Equality.Class module_export_desc_eqMixin).

Definition module_export_eq_dec : forall v1 v2 : module_export, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition module_export_eqb v1 v2 : bool := module_export_eq_dec v1 v2.
Definition eqmodule_exportP : Equality.axiom module_export_eqb :=
  eq_dec_Equality_axiom module_export_eq_dec.

Canonical Structure module_export_eqMixin := Equality.Mixin eqmodule_exportP.
Canonical Structure module_export_eqType := Eval hnf in Equality.Pack (sort := module_export) (Equality.Class module_export_eqMixin). 

(** Induction scheme for [administrative_instruction]. **)
Definition administrative_instruction_rect' :=
  ltac:(rect'_build administrative_instruction_rect).

Definition administrative_instruction_ind' (P : administrative_instruction -> Prop) :=
  @administrative_instruction_rect' P.

(** Administrative instructions frequently come in lists.
  Here is the corresponding induction principle. **)
(* TODO: rect'_build_list fails to generate wellformed definitions on newer versions
   of Coq. Use manual versions for now *)
(* Definition seq_administrative_instruction_rect' :=
  ltac:(rect'_build_list administrative_instruction_rect).

Definition seq_administrative_instruction_ind' (P : administrative_instruction -> Prop) :=
  @seq_administrative_instruction_rect' P. *)

 Definition administrative_instruction_eq_dec : forall e1 e2 : administrative_instruction,
  {e1 = e2} + {e1 <> e2}.
Proof. decidable_equality_using administrative_instruction_rect'. Defined.

Definition administrative_instruction_eqb cl1 cl2 : bool :=
  administrative_instruction_eq_dec cl1 cl2.
Definition eqadministrative_instructionP : Equality.axiom administrative_instruction_eqb :=
  eq_dec_Equality_axiom administrative_instruction_eq_dec.

Canonical Structure administrative_instruction_eqMixin := Equality.Mixin eqadministrative_instructionP.
Canonical Structure administrative_instruction_eqType :=
  Eval hnf in Equality.Pack (sort := administrative_instruction) (Equality.Class administrative_instruction_eqMixin). 

 Definition lholed_eq_dec : forall v1 v2 : lholed, {v1 = v2} + {v1 <> v2}.
Proof. 
  decidable_equality.
Defined.

Definition lholed_eqb v1 v2 : bool := lholed_eq_dec v1 v2.
Definition eqlholedP : Equality.axiom lholed_eqb :=
  eq_dec_Equality_axiom lholed_eq_dec.

Canonical Structure lholed_eqMixin := Equality.Mixin eqlholedP.
Canonical Structure lholed_eqType := Eval hnf in Equality.Pack (sort := lholed) (Equality.Class lholed_eqMixin). 


(* Definition handler_clauses_eq_dec : forall v1 v2 : handler_clauses, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition handler_clauses_eqb v1 v2 : bool := handler_clauses_eq_dec v1 v2.
Definition eqhandler_clausesP : Equality.axiom handler_clauses_eqb :=
  eq_dec_Equality_axiom handler_clauses_eq_dec.

Canonical Structure handler_clauses_eqMixin := Equality.Mixin eqhandler_clausesP.
Canonical Structure handler_clauses_eqType := Eval hnf in Equality.Pack (sort := handler_clauses) (Equality.Class handler_clauses_eqMixin). 
*)

Definition exception_clause_result_eq_dec : forall v1 v2 : exception_clause_result, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition exception_clause_result_eqb v1 v2 : bool := exception_clause_result_eq_dec v1 v2.
Definition eqexception_clause_resultP : Equality.axiom exception_clause_result_eqb :=
  eq_dec_Equality_axiom exception_clause_result_eq_dec.

Canonical Structure exception_clause_result_eqMixin := Equality.Mixin eqexception_clause_resultP.
Canonical Structure exception_clause_result_eqType := Eval hnf in Equality.Pack (sort := exception_clause_result) (Equality.Class exception_clause_result_eqMixin).
(*
Definition continuation_clause_result_eq_dec : forall v1 v2 : continuation_clause_result, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition continuation_clause_result_eqb v1 v2 : bool := continuation_clause_result_eq_dec v1 v2.
Definition eqcontinuation_clause_resultP : Equality.axiom continuation_clause_result_eqb :=
  eq_dec_Equality_axiom continuation_clause_result_eq_dec.

Canonical Structure continuation_clause_result_eqMixin := Equality.Mixin eqcontinuation_clause_resultP.
Canonical Structure continuation_clause_result_eqType := Eval hnf in Equality.Pack (sort := continuation_clause_result) (Equality.Class continuation_clause_result_eqMixin). 
*)


 Definition hholed_eq_dec : forall v1 v2 : hholed, {v1 = v2} + {v1 <> v2}.
 Proof. decidable_equality. Defined.


Definition hholed_eqb v1 v2 : bool := hholed_eq_dec v1 v2.
Definition eqhholedP : Equality.axiom hholed_eqb :=
  eq_dec_Equality_axiom hholed_eq_dec.

Canonical Structure hholed_eqMixin := Equality.Mixin eqhholedP.
Canonical Structure hholed_eqType := Eval hnf in Equality.Pack (sort := hholed) (Equality.Class hholed_eqMixin). 




Definition store_record_eq_dec : forall v1 v2 : store_record, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition store_record_eqb v1 v2 : bool := store_record_eq_dec v1 v2.
Definition eqstore_recordP : Equality.axiom store_record_eqb :=
  eq_dec_Equality_axiom store_record_eq_dec.

Canonical Structure store_record_eqMixin := Equality.Mixin eqstore_recordP.
Canonical Structure store_record_eqType := Eval hnf in Equality.Pack (sort := store_record) (Equality.Class store_record_eqMixin). 

Definition exception_eq_dec : forall v1 v2 : exception, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition exception_eqb v1 v2 : bool := exception_eq_dec v1 v2.
Definition eqexceptionP : Equality.axiom exception_eqb :=
  eq_dec_Equality_axiom exception_eq_dec.

Canonical Structure exception_eqMixin := Equality.Mixin eqexceptionP.
Canonical Structure exception_eqType := Eval hnf in Equality.Pack (sort := exception) (Equality.Class exception_eqMixin). 




Definition limits_eq_dec : forall v1 v2 : limits, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.
Definition limits_eqb v1 v2 : bool := limits_eq_dec v1 v2.
Definition eqlimitsP : Equality.axiom limits_eqb :=
  eq_dec_Equality_axiom limits_eq_dec.

Canonical Structure limits_eqMixin := Equality.Mixin eqlimitsP.
Canonical Structure limits_eqType := Eval hnf in Equality.Pack (sort := limits) (Equality.Class limits_eqMixin).


Definition table_type_eq_dec : forall v1 v2 : table_type, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.
Definition table_type_eqb v1 v2 : bool := table_type_eq_dec v1 v2.
Definition eqtable_typeP : Equality.axiom table_type_eqb :=
  eq_dec_Equality_axiom table_type_eq_dec.

Canonical Structure table_type_eqMixin := Equality.Mixin eqtable_typeP.
Canonical Structure table_type_eqType := Eval hnf in Equality.Pack (sort := table_type) (Equality.Class table_type_eqMixin).

Definition memory_type_eq_dec : forall v1 v2 : memory_type, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.
Definition memory_type_eqb v1 v2 : bool := memory_type_eq_dec v1 v2.
Definition eqmemory_typeP : Equality.axiom memory_type_eqb :=
  eq_dec_Equality_axiom memory_type_eq_dec.

Canonical Structure memory_type_eqMixin := Equality.Mixin eqmemory_typeP.
Canonical Structure memory_type_eqType := Eval hnf in Equality.Pack (sort := memory_type) (Equality.Class memory_type_eqMixin).

Definition memory_eq_dec : forall m1 m2: memory, {m1 = m2} + {m1 <> m2}.
Proof.
  by decidable_equality.
Defined.

Definition hostfuncidx_eq_dec : forall h1 h2:hostfuncidx, {h1 = h2} + {h1 <> h2}.
  by decidable_equality.
Defined.

Scheme Equality for res_crash.
Definition res_crash_eqb c1 c2 := is_left (res_crash_eq_dec c1 c2).
Definition eqres_crashP : Equality.axiom res_crash_eqb :=
  eq_dec_Equality_axiom res_crash_eq_dec.

Canonical Structure res_crash_eqMixin := Equality.Mixin eqres_crashP.
Canonical Structure res_crash_eqType := Eval hnf in Equality.Pack (sort := res_crash) (Equality.Class res_crash_eqMixin).

Definition continuation_eq_dec: forall r1 r2: continuation, { r1 = r2 } + { r1 <> r2 }.
Proof.
  decidable_equality.
Defined.
Definition continuation_eqb c1 c2 := is_left (continuation_eq_dec c1 c2).
Definition eqcontinuationP : Equality.axiom continuation_eqb :=
  eq_dec_Equality_axiom continuation_eq_dec.

Canonical Structure continuation_eqMixin := Equality.Mixin eqcontinuationP.
Canonical Structure continuation_eqType := Eval hnf in Equality.Pack (sort := continuation) (Equality.Class continuation_eqMixin).

Definition continuation_clause_eq_dec: forall r1 r2: continuation_clause, { r1 = r2 } + { r1 <> r2 }.
Proof.
  decidable_equality.
Defined.
Definition continuation_clause_eqb c1 c2 := is_left (continuation_clause_eq_dec c1 c2).
Definition eqcontinuation_clauseP : Equality.axiom continuation_clause_eqb :=
  eq_dec_Equality_axiom continuation_clause_eq_dec.

Canonical Structure continuation_clause_eqMixin := Equality.Mixin eqcontinuation_clauseP.
Canonical Structure continuation_clause_eqType := Eval hnf in Equality.Pack (sort := continuation_clause) (Equality.Class continuation_clause_eqMixin).

Definition exception_clause_eq_dec: forall r1 r2: exception_clause, { r1 = r2 } + { r1 <> r2 }.
Proof.
  decidable_equality.
Defined.
Definition exception_clause_eqb c1 c2 := is_left (exception_clause_eq_dec c1 c2).
Definition eqexception_clauseP : Equality.axiom exception_clause_eqb :=
  eq_dec_Equality_axiom exception_clause_eq_dec.

Canonical Structure exception_clause_eqMixin := Equality.Mixin eqexception_clauseP.
Canonical Structure exception_clause_eqType := Eval hnf in Equality.Pack (sort := exception_clause) (Equality.Class exception_clause_eqMixin).

Definition tagidx_eq_dec: forall r1 r2: tagidx, { r1 = r2 } + { r1 <> r2 }.
Proof.
  decidable_equality.
Defined.
Definition tagidx_eqb c1 c2 := is_left (tagidx_eq_dec c1 c2).
Definition eqtagidxP : Equality.axiom tagidx_eqb :=
  eq_dec_Equality_axiom tagidx_eq_dec.

Canonical Structure tagidx_eqMixin := Equality.Mixin eqtagidxP.
Canonical Structure tagidx_eqType := Eval hnf in Equality.Pack (sort := tagidx) (Equality.Class tagidx_eqMixin).

Definition res_step_eq_dec : forall r1 r2 : res_step, {r1 = r2} + {r1 <> r2}.
Proof.
  (decidable_equality_step;
    try by apply: (eq_comparable (_ : seq administrative_instruction)));
    decidable_equality.
Defined.

Definition res_step_eqb (r1 r2 : res_step) : bool := res_step_eq_dec r1 r2.
Definition eqres_stepP : Equality.axiom res_step_eqb :=
  eq_dec_Equality_axiom res_step_eq_dec.

Canonical Structure res_step_eqMixin := Equality.Mixin eqres_stepP.
Canonical Structure res_step_eqType := Eval hnf in Equality.Pack (sort := res_step) (Equality.Class res_step_eqMixin).



 Definition value_num_eq_dec : forall v1 v2 : value_num, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition value_num_eqb v1 v2 : bool := value_num_eq_dec v1 v2.
Definition eqvalue_numP : Equality.axiom value_num_eqb :=
  eq_dec_Equality_axiom value_num_eq_dec.

Canonical Structure value_num_eqMixin := Equality.Mixin eqvalue_numP.
Canonical Structure value_num_eqType := Eval hnf in Equality.Pack (sort := value_num) (Equality.Class value_num_eqMixin). 
