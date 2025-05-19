From mathcomp Require Import ssreflect ssrbool eqtype seq.
From Coq Require Import Eqdep_dec.
From stdpp Require Import base list.
From Wasm Require Export common operations opsem properties list_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".


Global Instance ai_list_eq_dec: EqDecision (seq.seq administrative_instruction).
Proof.
  eapply list_eq_dec.
  Unshelve.
  pose proof administrative_instruction_eq_dec. eauto.
Defined.
Global Instance ai_eq_dec: EqDecision (administrative_instruction).
Proof.
  pose proof administrative_instruction_eq_dec. eauto.
Defined.
Global Instance value_list_eq_dec: EqDecision (seq.seq value).
Proof.
  decidable_equality.
Defined.
Global Instance lholed_eq_dec : EqDecision (lholed).
Proof.
  decidable_equality.
Defined.


Fixpoint size_of_instruction e :=
  match e with
  | AI_prompt _ _ LI
  | AI_handler _ LI
  | AI_label _ _ LI 
  | AI_local _ _ LI => S (List.list_sum (map size_of_instruction LI))
  | _ => 1
  end.

Definition length_rec es := List.list_sum (map size_of_instruction es).


(* An object of [valid_holed n] is an lholed in shallow enough for a [br n] to 
   be placed inside and be stuck *)
(* We also enforce the constance of all the left-hand-sides *)
Inductive valid_holed : nat -> Type :=
| VH_base (n : nat) : list value -> list administrative_instruction -> valid_holed n
| VH_rec (n : nat) : list value -> nat -> list administrative_instruction ->
                   valid_holed n -> list administrative_instruction -> valid_holed (S n)
| VH_prompt (n : nat) : list value -> list value_type -> list continuation_clause -> valid_holed n -> list administrative_instruction -> valid_holed n
| VH_handler (n : nat) : list value -> list exception_clause -> valid_holed n -> list administrative_instruction -> valid_holed n
.

Definition list_value_type_eq_dec : forall t1 t2: list value_type,
    { t1 = t2 } + { t1 <> t2 }.
Proof. decidable_equality. Qed.

Definition list_continuation_clause_eq_dec : forall t1 t2: list continuation_clause,
    { t1 = t2 } + { t1 <> t2 }.
Proof. decidable_equality. Qed.
Definition list_exception_clause_eq_dec : forall t1 t2: list exception_clause,
    { t1 = t2 } + { t1 <> t2 }.
Proof. decidable_equality. Qed.

Definition valid_holed_eq_dec :
  forall i (lh1 lh2 : valid_holed i), { lh1 = lh2 } + { lh1 <> lh2 }.
Proof. 
  clear.
  induction lh1 ; intros.
  - destruct lh2 ; try by right.
    destruct (decide (l = l1)), (decide (l0 = l2)) ; solve [ by right ; intro H ; inversion H | by subst ; left].
  - set (k := S n) in lh2.

    pose (Logic.eq_refl : k = S n) as Hk.
    change lh2 with (match Hk in _ = w return valid_holed w with
                      | Logic.eq_refl => lh2 end).
    clearbody Hk k.
    destruct lh2.
    + right. intro Habs.
      assert ( match Hk in (_ = w) return (valid_holed w) with
               | Logic.eq_refl => VH_base n1 l2 l3
               end = VH_base (S n) l2 l3) as Hdone ; last by rewrite Hdone in Habs.
      rewrite -> Hk. done. 
    + pose proof (eq_add_S _ _ Hk) as Hn.
      
      assert (Hk = f_equal S Hn) as Hproof.
      apply Eqdep.EqdepTheory.UIP.
      
      replace (match Hk in _ = w return (valid_holed w) with
               | Logic.eq_refl => VH_rec l2 n2 l3 lh2 l4
               end) with
        ( VH_rec l2 n2 l3 (match Hn in _ = w return valid_holed w with
                           | Logic.eq_refl => lh2 end ) l4) ; last first.

      rewrite Hproof.
      destruct Hn. done.

    
      destruct (decide ( l = l2)), (decide (n0 = n2)), (decide (l0 = l3)),
      (decide ( l1 = l4)), (IHlh1 (match Hn in (_ = w) return (valid_holed w) with
     | Logic.eq_refl => lh2
                                   end)) ; try by right ; intro H ; inversion H.
      left ; by subst.
      right. intro H. inversion H.
      apply Eqdep.EqdepTheory.inj_pair2 in H4.
      done.
    + right. destruct n1 => //.
      intro Habs.
      pose proof (eq_add_S _ _ Hk) as Hn.
      assert (Hk = f_equal S Hn) as Hproof.
      apply Eqdep.EqdepTheory.UIP.
      replace (match Hk in (_ = w) return (valid_holed w) with
               | Logic.eq_refl => VH_prompt l2 l3 l4 lh2 l5
               end)
        with
        ( VH_prompt l2 l3 l4 (
              match Hk in (_ = w) return (valid_holed w) with
              | Logic.eq_refl => lh2
              end) l5) in Habs; first done.
      rewrite Hproof.
      destruct Hn. done.
    + right. destruct n1 => //.
      intro Habs.
      pose proof (eq_add_S _ _ Hk) as Hn.
      assert (Hk = f_equal S Hn) as Hproof.
      apply Eqdep.EqdepTheory.UIP.
      replace (match Hk in (_ = w) return (valid_holed w) with
               | Logic.eq_refl => VH_handler l2 l3 lh2 l4
               end)
        with
        ( VH_handler l2 l3 (
              match Hk in (_ = w) return (valid_holed w) with
              | Logic.eq_refl => lh2
              end) l4) in Habs; first done.
      rewrite Hproof.
      destruct Hn. done.
  - destruct lh2; try by right.
    destruct (decide (l = l3)), (list_value_type_eq_dec l0 l4), (list_continuation_clause_eq_dec l1 l5), (IHlh1 lh2), (decide (l2 = l6)); try by right; intros Habs; inversion Habs; subst.
    subst; by left.
    right. intros Habs; inversion Habs.
    apply Eqdep.EqdepTheory.inj_pair2 in H3.
    done.
  - destruct lh2; try by right.
    destruct (decide (l = l2)), (list_exception_clause_eq_dec l0 l3), (IHlh1 lh2), (decide (l1 = l4)); try by right; intros Habs; inversion Habs; subst.
    subst; by left.
    right. intros Habs; inversion Habs.
    apply Eqdep.EqdepTheory.inj_pair2 in H2.
    done.
Defined.    

(* Here, we only enforce the constance of the left-hand-sides, no constraint on depth *)
Inductive simple_valid_holed : Type :=
| SH_base : list value -> list administrative_instruction -> simple_valid_holed
| SH_rec : list value -> nat -> list administrative_instruction -> simple_valid_holed
           -> list administrative_instruction -> simple_valid_holed
| SH_prompt : list value -> list value_type -> list continuation_clause -> simple_valid_holed -> list administrative_instruction -> simple_valid_holed
| SH_handler : list value -> list exception_clause -> simple_valid_holed -> list administrative_instruction -> simple_valid_holed
.

Definition simple_valid_holed_eq_dec :
  forall lh1 lh2 : simple_valid_holed, { lh1 = lh2 } + { lh1 <> lh2 }.
Proof.
  intros. decidable_equality.
Defined. 
(*  generalize dependent lh2.
  induction lh1, lh2 ; auto.
  - destruct (decide (l = l1)), (decide (l0 = l2)).
    subst ; by left.
    all : try by right ; intro H ; inversion H.
  - destruct (decide (l = l2)), (decide (n = n0)), (decide (l0 = l3)),
    (decide (l1 = l4)) ; destruct (IHlh1 lh2) as [H0 | H0] ;
    try by right ; intro H ; inversion H.
    subst ; by left.
  - destruct (decide (l = l3)), (list_value_type_eq_dec l0 l4),
      (list_continuation_clause_eq_dec l1 l5), (IHlh1 lh2), (decide (l2 = l6)); try by right; intro H; inversion H.
    subst ; by left.
  - destruct (decide (l = l2)), 
      (list_exception_clause_eq_dec l0 l3), (IHlh1 lh2),
      (decide (l1 = l4)); try by right; intro H; inversion H.
    subst ; by left.
Defined. *)

Inductive llholed : Type :=
| LL_base : list value -> list administrative_instruction -> llholed
| LL_label : list value -> nat -> list administrative_instruction -> llholed -> list administrative_instruction -> llholed
| LL_local : list value -> nat -> frame -> llholed -> list administrative_instruction -> llholed
| LL_prompt : list value -> list value_type -> list continuation_clause -> llholed -> list administrative_instruction -> llholed
| LL_handler : list value -> list exception_clause -> llholed -> list administrative_instruction -> llholed
. 

Definition llholed_eq_dec :
  forall lh1 lh2 : llholed, { lh1 = lh2 } + { lh1 <> lh2 }.
Proof.
  intros.
  decidable_equality.
Qed.

(*
(* A term of type capped_nat n is an integer <= n *)
Inductive capped_nat : nat -> Type :=
| Zero (n : nat) : capped_nat n
| PlusOne (n : nat) : capped_nat n -> capped_nat (S n)
.

Fixpoint nat_of_capped_nat (p: nat) (n : capped_nat p) :=
  match n with
  | Zero _ => 0
  | PlusOne _ n => S (nat_of_capped_nat n)
  end.

Lemma capped_nat_capped p (n : capped_nat p) :
  (nat_of_capped_nat n) <= p.
Proof.
  induction n; lias.
Qed.

Lemma capped_nat_eq_dec:
  forall p (n1 n2: capped_nat p), { n1 = n2 } + { n1 <> n2 }.
Proof.
  induction n1; intros.
  - destruct n2 ; by (left + right).
  - set (k := S n) in n2.

    pose (Logic.eq_refl : k = S n) as Hk.
    change n2 with (match Hk in _ = w return capped_nat w with
                      | Logic.eq_refl => n2 end).
    clearbody Hk k.
    destruct n2.
    + right. subst n0. done.
    + pose proof (eq_add_S _ _ Hk) as Hn.
      
      assert (Hk = f_equal S Hn) as Hproof.
      apply Eqdep.EqdepTheory.UIP.
      
      replace (match Hk in _ = w return (capped_nat w) with
               | Logic.eq_refl => PlusOne n2
               end) with
        ( PlusOne (match Hn in _ = w return capped_nat w with
                           | Logic.eq_refl => n2 end )) ; last first.

      { rewrite Hproof.
        destruct Hn. done. } 
      destruct (IHn1 (match Hn in (_ = w) return capped_nat w with
                      | Logic.eq_refl => n2 end)).
      * left; by subst.
      * right. intro H. inversion H.
        apply Eqdep.EqdepTheory.inj_pair2 in H1.
        done.
Defined.     


Inductive offset : nat -> Type :=
(* OMinusS n represents an offset of S n; same with OPlusS *)
| OMinusS (n : nat) : capped_nat n -> offset (S n)
| OPlusS (n: nat) : nat -> offset n
.

Lemma offset_eq_dec :
  forall p (o1 o2: offset p), { o1 = o2 } + { o1 <> o2 }.
Proof.
  intros. destruct o1.
  - set (k := S n) in o2.

    pose (Logic.eq_refl : k = S n) as Hk.
    change o2 with (match Hk in _ = w return offset w with
                      | Logic.eq_refl => o2 end).
    clearbody Hk k.
    destruct o2; last by right; subst n0.
    pose proof (eq_add_S _ _ Hk) as Hn.
      
    assert (Hk = f_equal S Hn) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    
    replace (match Hk in _ = w return (offset w) with
               | Logic.eq_refl => OMinusS c0
               end) with
        ( OMinusS (match Hn in _ = w return capped_nat w with
                   | Logic.eq_refl => c0 end )) ; last first.

      { rewrite Hproof.
        destruct Hn. done. }
      destruct (capped_nat_eq_dec c 
                  (match Hn in (_ = w) return capped_nat w with
                   | Logic.eq_refl => c0 end)).
      * left; by subst.
      * right. intro H. inversion H.
        apply Eqdep.EqdepTheory.inj_pair2 in H1.
        done.
  - destruct o2.
    + by right.
    + destruct (decide (n0 = n1)).
      * subst; by left.
      * right; intros H; inversion H; done.
Qed.
*)

Inductive suselt : Type :=
| SuSuspend : nat  -> immediate -> suselt
| SuSwitch : tagidx -> suselt
.


Lemma suselt_eq_dec :
  forall (o1 o2: suselt), { o1 = o2 } + { o1 <> o2 }.
Proof.
  decidable_equality.
(*  intros. destruct o1.
  - set (k := Mk_tagidx n) in o2.

    pose (Logic.eq_refl : k = Mk_tagidx n) as Hk.
    change o2 with (match Hk in _ = w return suselt w with
                      | Logic.eq_refl => o2 end).
    clearbody Hk k.
    destruct o2; last by right; subst x.
    inversion Hk.
      
    assert (Hk = f_equal Mk_tagidx H0) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    
    replace (match Hk in _ = w return (suselt w) with
               | Logic.eq_refl => SuSuspend o0 i0
               end) with
        ( SuSuspend (match H0 in _ = w return offset w with
                   | Logic.eq_refl => o0 end ) i0) ; last first.

      { rewrite Hproof.
        destruct H0. done. }
      destruct (offset_eq_dec o 
                  (match H0 in (_ = w) return offset w with
                   | Logic.eq_refl => o0 end)), (decide (i = i0)); first by left; subst.
      all: right; intro H; inversion H.
      done.
      all: apply Eqdep.EqdepTheory.inj_pair2 in H2.
      all: done.
  - destruct o2.
    + by right.
    + destruct (t == t0) eqn:Ht.
      * move/eqP in Ht; subst; by left.
      * right; intros H; inversion H.
        subst t; rewrite eq_refl in Ht; done. *)
Qed. 

Inductive susholed : Type :=
| SuBase: list value -> list administrative_instruction -> susholed 
| SuLabel: list value -> nat -> list administrative_instruction -> susholed -> list administrative_instruction -> susholed
| SuLocal: list value -> nat -> frame -> susholed -> list administrative_instruction -> susholed
| SuHandler: list value -> list exception_clause -> susholed -> list administrative_instruction -> susholed
| SuPrompt: list value -> list value_type -> list (suselt) -> (susholed) -> list administrative_instruction -> susholed
.


Definition suslist_eq_dec:
  forall l1 l2 : list (suselt), { l1 = l2 } + { l1 <> l2 }.
Proof.
  decidable_equality.
Qed. 

Definition susholed_eq_dec:
  forall sh1 sh2: susholed , { sh1 = sh2 } + { sh1 <> sh2 }.
Proof.
  decidable_equality.
  (*
induction sh1; destruct sh2; try by right.
  - destruct ((l == l1) && (l0 == l2)) eqn:Habs.
    + remove_bools_options; subst; by left.
    + right; intros Habs'; inversion Habs';
        subst; repeat rewrite eq_refl in Habs.
      done.
  - destruct ((l == l2) && (n =? n0) && (l0 == l3) && (l1 == l4)) eqn:Hb.
    + destruct (IHsh1 sh2).
      * remove_bools_options.
        apply Nat.eqb_eq in H2.
        subst. by left.
      * right; intros Habs'; inversion Habs'; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H3.
        done.
    + right; intros Habs'; inversion Habs'; subst.
      repeat rewrite eq_refl in Hb.
      rewrite Nat.eqb_refl in Hb.
      done.
  - destruct ((l == l1) && (n =? n0) && (f == f0) && (l0 == l2)) eqn:Hb.
      + destruct (IHsh1 sh2).
      * remove_bools_options.
        apply Nat.eqb_eq in H2.
        subst. by left.
      * right; intros Habs'; inversion Habs'; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H3.
        done.
    + right; intros Habs'; inversion Habs'; subst.
      repeat rewrite eq_refl in Hb.
      rewrite Nat.eqb_refl in Hb.
      done.
  - destruct ((l == l2) && (l0 == l3) && (l1 == l4)) eqn:Hb.
    + destruct (IHsh1 sh2).
      * remove_bools_options.
        subst. by left.
      * right; intros Habs'; inversion Habs'; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        done.
    + right; intros Habs'; inversion Habs'; subst.
      repeat rewrite eq_refl in Hb.
      done.
  - destruct ((l == l3) && (l0 == l4) && (l2 == l6)) eqn:Hb.
    + destruct (suslist_eq_dec l1 l5) eqn:Hsus.
      * destruct (IHsh1 sh2).
        -- remove_bools_options.
           subst. by left.
        -- right; intros Habs'; inversion Habs'; subst.
           apply Eqdep.EqdepTheory.inj_pair2 in H3.
           done.
      * right; intros Habs'; inversion Habs'; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        done.
    + right; intros Habs'; inversion Habs'; subst.
      repeat rewrite eq_refl in Hb.
      done. *)
Qed. 


Inductive swelt : Type :=
| SwSwitch: nat -> swelt
| SwSuspend : tagidx -> immediate -> swelt
.


Lemma swelt_eq_dec :
  forall (o1 o2: swelt), { o1 = o2 } + { o1 <> o2 }.
Proof.
  decidable_equality.
(*  intros. destruct o1.
  - set (k := Mk_tagidx n) in o2.

    pose (Logic.eq_refl : k = Mk_tagidx n) as Hk.
    change o2 with (match Hk in _ = w return swelt w with
                      | Logic.eq_refl => o2 end).
    clearbody Hk k.
    destruct o2; last by right; subst x.
    inversion Hk.
      
    assert (Hk = f_equal Mk_tagidx H0) as Hproof.
    apply Eqdep.EqdepTheory.UIP.
    
    replace (match Hk in _ = w return (swelt w) with
               | Logic.eq_refl => SwSwitch o0
               end) with
        ( SwSwitch (match H0 in _ = w return offset w with
                   | Logic.eq_refl => o0 end )) ; last first.

      { rewrite Hproof.
        destruct H0. done. }
      destruct (offset_eq_dec o 
                  (match H0 in (_ = w) return offset w with
                   | Logic.eq_refl => o0 end)); first by left; subst.
      right; intro H; inversion H.
      apply Eqdep.EqdepTheory.inj_pair2 in H2.
      done.
  - destruct o2.
    + by right.
    + destruct ((t == t0) && (i == i0)) eqn:Ht.
      * remove_bools_options; subst; by left.
      * right; intros H; inversion H.
        subst; repeat rewrite eq_refl in Ht; done. *)
Qed. 


Inductive swholed : Type :=
| SwBase : list value -> list administrative_instruction -> swholed
| SwLabel : list value -> nat -> list administrative_instruction -> swholed -> list administrative_instruction -> swholed
| SwLocal  : list value -> nat -> frame -> swholed -> list administrative_instruction -> swholed
| SwHandler  : list value -> list exception_clause -> swholed-> list administrative_instruction -> swholed
| SwPrompt  : list value -> list value_type -> list (swelt) -> swholed-> list administrative_instruction -> swholed
.


Definition swlist_eq_dec:
  forall l1 l2 : list (swelt), { l1 = l2 } + { l1 <> l2 }.
Proof.
  decidable_equality.
Qed.

Definition swholed_eq_dec:
  forall sh1 sh2: swholed, { sh1 = sh2 } + { sh1 <> sh2 }.
Proof.
  decidable_equality.
(*  induction sh1; destruct sh2; try by right.
  - destruct ((l == l1) && (l0 == l2)) eqn:Habs.
    + remove_bools_options; subst; by left.
    + right; intros Habs'; inversion Habs';
        subst; repeat rewrite eq_refl in Habs.
      done.
  - destruct ((l == l2) && (n =? n0) && (l0 == l3) && (l1 == l4)) eqn:Hb.
    + destruct (IHsh1 sh2).
      * remove_bools_options.
        apply Nat.eqb_eq in H2.
        subst. by left.
      * right; intros Habs'; inversion Habs'; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H3.
        done.
    + right; intros Habs'; inversion Habs'; subst.
      repeat rewrite eq_refl in Hb.
      rewrite Nat.eqb_refl in Hb.
      done.
  - destruct ((l == l1) && (n =? n0) && (f == f0) && (l0 == l2)) eqn:Hb.
      + destruct (IHsh1 sh2).
      * remove_bools_options.
        apply Nat.eqb_eq in H2.
        subst. by left.
      * right; intros Habs'; inversion Habs'; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H3.
        done.
    + right; intros Habs'; inversion Habs'; subst.
      repeat rewrite eq_refl in Hb.
      rewrite Nat.eqb_refl in Hb.
      done.
  - destruct ((l == l2) && (l0 == l3) && (l1 == l4)) eqn:Hb.
    + destruct (IHsh1 sh2).
      * remove_bools_options.
        subst. by left.
      * right; intros Habs'; inversion Habs'; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        done.
    + right; intros Habs'; inversion Habs'; subst.
      repeat rewrite eq_refl in Hb.
      done.
  - destruct ((l == l3) && (l0 == l4) && (l2 == l6)) eqn:Hb.
    + destruct (swlist_eq_dec l1 l5) eqn:Hsus.
      * destruct (IHsh1 sh2).
        -- remove_bools_options.
           subst. by left.
        -- right; intros Habs'; inversion Habs'; subst.
           apply Eqdep.EqdepTheory.inj_pair2 in H3.
           done.
      * right; intros Habs'; inversion Habs'; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        done.
    + right; intros Habs'; inversion Habs'; subst.
      repeat rewrite eq_refl in Hb.
      done. *)
Qed.


Inductive exnelt : Type :=
| ExCatch: nat -> immediate -> exnelt
| ExCatchRef: nat -> immediate -> exnelt
.


Lemma exnelt_eq_dec :
  forall (o1 o2: exnelt), { o1 = o2 } + { o1 <> o2 }.
Proof.
  decidable_equality.
(*  intros. destruct o1.
  - set (k := Mk_tagidx n) in o2.

    pose (Logic.eq_refl : k = Mk_tagidx n) as Hk.
    change o2 with (match Hk in _ = w return exnelt w with
                      | Logic.eq_refl => o2 end).
    clearbody Hk k.
    destruct o2. 
    + inversion Hk.
      
      assert (Hk = f_equal Mk_tagidx H0) as Hproof.
      apply Eqdep.EqdepTheory.UIP.
      
      replace (match Hk in _ = w return (exnelt w) with
               | Logic.eq_refl => ExCatch o0 i0
               end) with
        ( ExCatch (match H0 in _ = w return offset w with
                   | Logic.eq_refl => o0 end ) i0) ; last first.

      { rewrite Hproof.
        destruct H0. done. }
      destruct (offset_eq_dec o 
                  (match H0 in (_ = w) return offset w with
                   | Logic.eq_refl => o0 end)), (decide (i = i0)); first by left; subst.
      all: right; intro H; inversion H.
      done.
      all: apply Eqdep.EqdepTheory.inj_pair2 in H2.
      all: done.
    + inversion Hk.
       assert (Hk = f_equal Mk_tagidx H0) as Hproof.
      apply Eqdep.EqdepTheory.UIP.
      
      replace (match Hk in _ = w return (exnelt w) with
               | Logic.eq_refl => ExCatchRef o0 i0
               end) with
        ( ExCatchRef (match H0 in _ = w return offset w with
                   | Logic.eq_refl => o0 end ) i0) ; last first.

      { rewrite Hproof.
        destruct H0. done. }
      by right.
  - set (k := Mk_tagidx n) in o2.

    pose (Logic.eq_refl : k = Mk_tagidx n) as Hk.
    change o2 with (match Hk in _ = w return exnelt w with
                      | Logic.eq_refl => o2 end).
    clearbody Hk k.
    destruct o2.
    + inversion Hk.
       assert (Hk = f_equal Mk_tagidx H0) as Hproof.
      apply Eqdep.EqdepTheory.UIP.
      
      replace (match Hk in _ = w return (exnelt w) with
               | Logic.eq_refl => ExCatch o0 i0
               end) with
        ( ExCatch (match H0 in _ = w return offset w with
                   | Logic.eq_refl => o0 end ) i0) ; last first.

      { rewrite Hproof.
        destruct H0. done. }
      by right.
    + inversion Hk.
      
      assert (Hk = f_equal Mk_tagidx H0) as Hproof.
      apply Eqdep.EqdepTheory.UIP.
      
      replace (match Hk in _ = w return (exnelt w) with
               | Logic.eq_refl => ExCatchRef o0 i0
               end) with
        ( ExCatchRef (match H0 in _ = w return offset w with
                   | Logic.eq_refl => o0 end ) i0) ; last first.

      { rewrite Hproof.
        destruct H0. done. }
      destruct (offset_eq_dec o 
                  (match H0 in (_ = w) return offset w with
                   | Logic.eq_refl => o0 end)), (decide (i = i0)); first by left; subst.
      all: right; intro H; inversion H.
      done.
      all: apply Eqdep.EqdepTheory.inj_pair2 in H2.
      all: done. *)
Qed. 


Inductive exnholed : Type :=
| ExBase  : list value -> list administrative_instruction -> exnholed
| ExLabel  : list value -> nat -> list administrative_instruction -> exnholed -> list administrative_instruction -> exnholed
| ExLocal  : list value -> nat -> frame -> exnholed -> list administrative_instruction -> exnholed
| ExHandler  : list value -> list (exnelt) -> exnholed -> list administrative_instruction -> exnholed
| ExPrompt  : list value -> list value_type -> list continuation_clause -> exnholed -> list administrative_instruction -> exnholed
.


Definition exnlist_eq_dec:
  forall l1 l2 : list (exnelt), { l1 = l2 } + { l1 <> l2 }.
Proof.
  decidable_equality.
Qed.

Definition exnholed_eq_dec:
  forall sh1 sh2: exnholed, { sh1 = sh2 } + { sh1 <> sh2 }.
Proof.
  decidable_equality.
(*  induction sh1; destruct sh2; try by right.
  - destruct ((l == l1) && (l0 == l2)) eqn:Habs.
    + remove_bools_options; subst; by left.
    + right; intros Habs'; inversion Habs';
        subst; repeat rewrite eq_refl in Habs.
      done.
  - destruct ((l == l2) && (n =? n0) && (l0 == l3) && (l1 == l4)) eqn:Hb.
    + destruct (IHsh1 sh2).
      * remove_bools_options.
        apply Nat.eqb_eq in H2.
        subst. by left.
      * right; intros Habs'; inversion Habs'; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H3.
        done.
    + right; intros Habs'; inversion Habs'; subst.
      repeat rewrite eq_refl in Hb.
      rewrite Nat.eqb_refl in Hb.
      done.
  - destruct ((l == l1) && (n =? n0) && (f == f0) && (l0 == l2)) eqn:Hb.
      + destruct (IHsh1 sh2).
      * remove_bools_options.
        apply Nat.eqb_eq in H2.
        subst. by left.
      * right; intros Habs'; inversion Habs'; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H3.
        done.
    + right; intros Habs'; inversion Habs'; subst.
      repeat rewrite eq_refl in Hb.
      rewrite Nat.eqb_refl in Hb.
      done.
  - destruct ((l == l2) && (l1 == l4)) eqn:Hb.
    + destruct (exnlist_eq_dec l0 l3) eqn:Hsus.
      * destruct (IHsh1 sh2).
        -- remove_bools_options.
           subst. by left.
        -- right; intros Habs'; inversion Habs'; subst.
           apply Eqdep.EqdepTheory.inj_pair2 in H2.
           done.
      * right; intros Habs'; inversion Habs'; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H1.
        done.
    + right; intros Habs'; inversion Habs'; subst.
      repeat rewrite eq_refl in Hb.
      done.
  - destruct ((l == l3) && (l0 == l4) && (l1 == l5) && (l2 == l6)) eqn:Hb.
    + destruct (IHsh1 sh2).
      * remove_bools_options.
        subst. by left.
      * right; intros Habs'; inversion Habs'; subst.
        apply Eqdep.EqdepTheory.inj_pair2 in H3.
        done.
    + right; intros Habs'; inversion Habs'; subst.
      repeat rewrite eq_refl in Hb.
      done. *)
Qed.
        
  

(* Since we enforced constance of the left-hand-sides, the fill operations are total
   functions *)
Fixpoint vfill n (vh : valid_holed n) es  :=
  match vh with
  | VH_base m bef aft => v_to_e_list bef ++ es ++ aft
  | VH_rec m bef n es0 vh aft =>
      v_to_e_list bef ++ AI_label n es0 (vfill vh es) :: aft
  | VH_prompt m bef tf hs vh aft =>
      v_to_e_list bef ++ AI_prompt tf hs (vfill vh es) :: aft
  | VH_handler m bef hs vh aft =>
      v_to_e_list bef ++ AI_handler hs (vfill vh es) :: aft
  end.
                                             
Fixpoint sfill sh es :=
  match sh with
  | SH_base bef aft => v_to_e_list bef ++ es ++ aft
  | SH_rec bef n es0 sh aft =>
      v_to_e_list bef ++ AI_label n es0 (sfill sh es) :: aft
  | SH_prompt bef tf hs sh aft =>
      v_to_e_list bef ++ AI_prompt tf hs (sfill sh es) :: aft
  | SH_handler bef hs sh aft =>
      v_to_e_list bef ++ AI_handler hs (sfill sh es) :: aft
  end.

Fixpoint llfill lh es :=
  match lh with
  | LL_base bef aft => v_to_e_list bef ++ es ++ aft
  | LL_label bef n es0 lh aft =>
      v_to_e_list bef ++ AI_label n es0 (llfill lh es) :: aft  
  | LL_local bef n f lh aft =>
      v_to_e_list bef ++ AI_local n f (llfill lh es) :: aft
  | LL_prompt bef tf hs lh aft =>
      v_to_e_list bef ++ AI_prompt tf hs (llfill lh es) :: aft
  | LL_handler bef hs lh aft =>
      v_to_e_list bef ++ AI_handler hs (llfill lh es) :: aft
  end.

Definition continuation_clause_of_suselt '(Mk_tagidx x) (l: suselt) :=
  match l with
  | SuSuspend x' i =>
      if (Nat.ltb x' x) then DC_catch (Mk_tagidx x') i
      else DC_catch (Mk_tagidx (S x')) i
(*  | SuSuspend _ (OMinusS _ x') i => DC_catch (Mk_tagidx (x - S (nat_of_capped_nat x'))) i
  | SuSuspend _ (OPlusS _ x') i => DC_catch (Mk_tagidx (x + S x')) i  *)
  | SuSwitch y => DC_switch y 
  end.

Fixpoint susfill x (lh: susholed) es :=
  match lh with
  | SuBase bef aft => v_to_e_list bef ++ es ++ aft
  | SuLabel bef n es0 lh aft => v_to_e_list bef ++ AI_label n es0 (susfill x lh es) :: aft
  | SuLocal bef n f lh aft => v_to_e_list bef ++ AI_local n f (susfill x lh es) :: aft
  | SuPrompt bef tf hs lh aft => v_to_e_list bef ++ AI_prompt tf (map (continuation_clause_of_suselt x) hs) (susfill x lh es) :: aft
  | SuHandler bef hs lh aft => v_to_e_list bef ++ AI_handler hs (susfill x lh es) :: aft
  end.

Definition continuation_clause_of_swelt '(Mk_tagidx x) (l: swelt) :=
  match l with
  | SwSwitch x' =>
      if (Nat.ltb x' x) then DC_switch (Mk_tagidx x')
      else DC_switch (Mk_tagidx (S x'))
(*  | SwSwitch _ (OMinusS _ x') => DC_switch (Mk_tagidx (x - S (nat_of_capped_nat x')))
  | SwSwitch _ (OPlusS _ x') => DC_switch (Mk_tagidx (x + S x')) *)
  | SwSuspend y i => DC_catch y i 
  end.

Fixpoint swfill (x: tagidx) (lh: swholed) es :=
  match lh with
  | SwBase bef aft => v_to_e_list bef ++ es ++ aft
  | SwLabel bef n es0 lh aft => v_to_e_list bef ++ AI_label n es0 (swfill x lh es) :: aft
  | SwLocal bef n f lh aft => v_to_e_list bef ++ AI_local n f (swfill x lh es) :: aft
  | SwPrompt bef tf hs lh aft => v_to_e_list bef ++ AI_prompt tf (map (continuation_clause_of_swelt x) hs) (swfill x lh es) :: aft
  | SwHandler bef hs lh aft => v_to_e_list bef ++ AI_handler hs (swfill x lh es) :: aft
  end.


Definition exception_clause_of_exnelt '(Mk_tagidx x) (l : exnelt) :=
  match l with
  | ExCatch x' i =>
      if (Nat.ltb x' x) then DE_catch (Mk_tagidx x') i
      else DE_catch (Mk_tagidx (S x')) i
  | ExCatchRef x' i =>
      if (Nat.ltb x' x) then DE_catch_ref (Mk_tagidx x') i
      else DE_catch_ref (Mk_tagidx (S x')) i
(*  | ExCatch _ (OMinusS _ x') i => DE_catch (Mk_tagidx (x - S (nat_of_capped_nat x'))) i
  | ExCatch _ (OPlusS _ x') i => DE_catch (Mk_tagidx (x + S x')) i 
  | ExCatchRef _ (OMinusS _ x') i => DE_catch_ref (Mk_tagidx (x - S (nat_of_capped_nat x'))) i
  | ExCatchRef _ (OPlusS _ x') i => DE_catch_ref (Mk_tagidx (x + S x')) i  *)
  end. 


Fixpoint exnfill (x: tagidx) (lh: exnholed) es :=
  match lh with
  | ExBase bef aft => v_to_e_list bef ++ es ++ aft
  | ExLabel bef n es0 lh aft => v_to_e_list bef ++ AI_label n es0 (exnfill x lh es) :: aft
  | ExLocal bef n f lh aft => v_to_e_list bef ++ AI_local n f (exnfill x lh es) :: aft
  | ExPrompt bef tf hs lh aft => v_to_e_list bef ++ AI_prompt tf hs (exnfill x lh es) :: aft
  | ExHandler bef hs lh aft => v_to_e_list bef ++ AI_handler (map (exception_clause_of_exnelt x) hs) (exnfill x lh es) :: aft
  end.



Definition sh_push_const sh vs :=
  match sh with
  | SH_base bef aft  => SH_base (vs ++ bef) aft 
  | SH_rec bef n es sh aft => SH_rec (vs ++ bef) n es sh aft
  | SH_prompt bef tf hs sh aft =>
      SH_prompt (vs ++ bef) tf hs sh aft
  | SH_handler bef hs sh aft =>
      SH_handler (vs ++ bef) hs sh aft
  end.

Definition sh_append sh expr :=
  match sh with
  | SH_base bef aft => SH_base bef (aft ++ expr)
  | SH_rec bef n es lh aft => SH_rec bef n es lh (aft ++ expr)
  | SH_prompt bef tf hs sh aft =>
      SH_prompt bef tf hs sh (aft ++ expr)
  | SH_handler bef hs sh aft =>
      SH_handler bef hs sh (aft ++ expr)
  end.

Definition sus_push_const (sh: susholed) vs :=
  match sh with
  | SuBase bef aft => SuBase (vs ++ bef) aft
  | SuLabel bef n es sh aft => SuLabel (vs ++ bef) n es sh aft
  | SuLocal bef n f sh aft => SuLocal (vs ++ bef) n f sh aft
  | SuPrompt bef tf hs sh aft => SuPrompt (vs ++ bef) tf hs sh aft
  | SuHandler bef hs sh aft => SuHandler (vs ++ bef) hs sh aft
  end.

Definition sus_append (sh: susholed) expr :=
  match sh with
  | SuBase bef aft => SuBase bef (aft ++ expr)
  | SuLabel bef n es sh aft => SuLabel bef n es sh (aft ++ expr)
  | SuLocal bef n f sh aft => SuLocal bef n f sh (aft ++ expr)
  | SuPrompt bef tf hs sh aft => SuPrompt bef tf hs sh (aft ++ expr)
  | SuHandler bef hs sh aft => SuHandler bef hs sh (aft ++ expr)
  end.


Definition sw_push_const (sh: swholed) vs :=
  match sh with
  | SwBase bef aft => SwBase (vs ++ bef) aft
  | SwLabel bef n es sh aft => SwLabel (vs ++ bef) n es sh aft
  | SwLocal bef n f sh aft => SwLocal (vs ++ bef) n f sh aft
  | SwPrompt bef tf hs sh aft => SwPrompt (vs ++ bef) tf hs sh aft
  | SwHandler bef hs sh aft => SwHandler (vs ++ bef) hs sh aft
  end.

Definition sw_append (sh: swholed) expr :=
  match sh with
  | SwBase bef aft => SwBase bef (aft ++ expr)
  | SwLabel bef n es sh aft => SwLabel bef n es sh (aft ++ expr)
  | SwLocal bef n f sh aft => SwLocal bef n f sh (aft ++ expr)
  | SwPrompt bef tf hs sh aft => SwPrompt bef tf hs sh (aft ++ expr)
  | SwHandler bef hs sh aft => SwHandler bef hs sh (aft ++ expr)
  end.


Definition exn_push_const (sh: exnholed) vs :=
  match sh with
  | ExBase bef aft => ExBase (vs ++ bef) aft
  | ExLabel bef n es sh aft => ExLabel (vs ++ bef) n es sh aft
  | ExLocal bef n f sh aft => ExLocal (vs ++ bef) n f sh aft
  | ExPrompt bef tf hs sh aft => ExPrompt (vs ++ bef) tf hs sh aft
  | ExHandler bef hs sh aft => ExHandler (vs ++ bef) hs sh aft
  end.

Definition exn_append (sh: exnholed) expr :=
  match sh with
  | ExBase bef aft => ExBase bef (aft ++ expr)
  | ExLabel bef n es sh aft => ExLabel bef n es sh (aft ++ expr)
  | ExLocal bef n f sh aft => ExLocal bef n f sh (aft ++ expr)
  | ExPrompt bef tf hs sh aft => ExPrompt bef tf hs sh (aft ++ expr)
  | ExHandler bef hs sh aft => ExHandler bef hs sh (aft ++ expr)
  end. 

Definition vh_push_const n (vh : valid_holed n) vs :=
  match vh with
  | VH_base n bef aft => VH_base n (vs ++ bef) aft
  | VH_rec n bef m es vh aft => VH_rec (n := n) (vs ++ bef) m es vh aft
  | VH_prompt n bef tf hs vh aft =>
      VH_prompt (n := n) (vs ++ bef) tf hs vh aft
  | VH_handler n bef hs vh aft =>
      VH_handler (n := n) (vs ++ bef) hs vh aft
  end.

Definition vh_append n (vh : valid_holed n) expr :=
  match vh with
  | VH_base n bef aft => VH_base n bef (aft ++ expr)
  | VH_rec n bef m es vh aft => VH_rec bef m es vh (aft ++ expr)
  | VH_prompt n bef tf hs vh aft =>
      VH_prompt (n := n) bef tf hs vh (aft ++ expr)
  | VH_handler n bef hs vh aft =>
      VH_handler (n := n) bef hs vh (aft ++ expr)
  end.


Definition llh_push_const lh vs :=
  match lh with
  | LL_base bef aft => LL_base (vs ++ bef) aft
  | LL_label bef m es lh aft => LL_label (vs ++ bef) m es lh aft 
  | LL_local bef n f lh aft => LL_local (vs ++ bef) n f lh aft
  | LL_prompt bef tf hs lh aft =>
      LL_prompt (vs ++ bef) tf hs lh aft
  | LL_handler bef hs lh aft =>
      LL_handler (vs ++ bef) hs lh aft
  end.

Definition llh_append lh expr :=
  match lh with
  | LL_base bef aft => LL_base bef (aft ++ expr)
  | LL_label bef m es lh aft => LL_label bef m es lh (aft ++ expr)
  | LL_local bef n f lh aft => LL_local bef n f lh (aft ++ expr)
  | LL_prompt bef tf hs lh aft =>
      LL_prompt bef tf hs lh (aft ++ expr)
  | LL_handler bef hs lh aft =>
      LL_handler bef hs lh (aft ++ expr)
  end.

(* given a [valid_holed (S m)], attemps to give back an « equal » [valid_holed m] *)
Fixpoint vh_decrease m (vh : valid_holed (S m)) : option (valid_holed m) :=
  match vh with
  | VH_base (S n) bef aft => Some (VH_base n bef aft)
  | VH_rec (S _) bef m es vh aft =>
      match vh_decrease vh with
      | Some vh' => Some (VH_rec bef m es vh' aft)
      | None => None
      end
  | VH_prompt (S n) bef tf hs vh aft =>
      match vh_decrease vh with
      | Some vh' => Some (VH_prompt bef tf hs vh' aft)
      | None => None
      end
  | VH_handler (S n) bef hs vh aft =>
      match vh_decrease vh with
      | Some vh' => Some (VH_handler bef hs vh' aft)
      | None => None
      end 
  | VH_base m _ _ | VH_rec m _ _ _ _ _
  | VH_prompt m _ _ _ _ _ | VH_handler m _ _ _ _
                    =>
                      (None : option (valid_holed m))
  end.

Fixpoint vh_increase m (vh : valid_holed m) :=
  match vh with
  | VH_base m bef aft => VH_base (S m) bef aft
  | VH_rec m bef n es vh aft => VH_rec bef n es (vh_increase vh) aft
  | VH_prompt m bef tf hs vh aft => VH_prompt bef tf hs (vh_increase vh) aft
  | VH_handler m bef hs vh aft => VH_handler bef hs (vh_increase vh) aft
  end.

Fixpoint vh_increase_repeat m (vh : valid_holed m) n : valid_holed (n + m) :=
  match n with 0 => vh
          | S n => vh_increase (vh_increase_repeat vh n) end.

(* Definition v_of_e e :=
  match e with
  | AI_basic (BI_const n) => Some (VAL_num n)
  | AI_basic (BI_ref_null r) => Some (VAL_ref (VAL_ref_null r))
  | AI_ref f => Some (VAL_ref (VAL_ref_func f))
  | AI_ref_cont f => Some (VAL_ref (VAL_ref_cont f))
  | AI_ref_exn f => Some (VAL_ref (VAL_ref_exn f))
  | _ => None
  end. *)

Fixpoint vh_of_lh lh i :=
  match lh with
  | LH_base bef aft =>
      match e_to_v_list_opt bef (* those (map v_of_e bef) *) with
      | Some bef => Some (VH_base i bef aft)
      |  _ => None end
  | LH_rec bef n es lh aft =>
      match i with
      | 0 => None
      | S i => 
          match e_to_v_list_opt bef (* those (map v_of_e bef) *) with
          |  Some bef => match vh_of_lh lh i with
                        | Some vh => Some (VH_rec bef n es vh aft)
                        | None => None end
          |  _ => None end
      end
  | LH_prompt bef tf hs lh aft =>
      match e_to_v_list_opt bef (* those (map v_of_e bef) *) with
      | Some bef => match vh_of_lh lh i with
                   | Some vh => Some (VH_prompt bef tf hs vh aft)
                   | None => None end
      | _ => None end
  | LH_handler bef hs lh aft =>
      match e_to_v_list_opt bef (* those (map v_of_e bef) *) with
      | Some bef => match vh_of_lh lh i with
                   | Some vh => Some (VH_handler bef hs vh aft)
                   | None => None end
      | _ => None end
  end. 

Fixpoint lh_of_vh i (vh : valid_holed i) :=
  match vh with
  | VH_base _ bef aft => LH_base (map AI_const bef) aft
  | VH_rec _ bef n es vh aft => LH_rec (map AI_const bef) n es
                                 (lh_of_vh vh) aft
  | VH_prompt _ bef tf hs vh aft =>
      LH_prompt (map AI_const bef) tf hs (lh_of_vh vh) aft
  | VH_handler _ bef hs vh aft =>
      LH_handler (map AI_const bef) hs (lh_of_vh vh) aft
  end.

Fixpoint lh_of_sh sh :=
  match sh with
  | SH_base bef aft => LH_base (map AI_const bef) aft
  | SH_rec bef n es sh aft => LH_rec (map AI_const bef) n es
                               (lh_of_sh sh) aft
  | SH_prompt bef tf hs sh aft =>
      LH_prompt (map AI_const bef) tf hs (lh_of_sh sh) aft
  | SH_handler bef hs sh aft =>
      LH_handler (map AI_const bef) hs (lh_of_sh sh) aft
  end.

Fixpoint hh_of_sush i sh :=
  match sh with
  | SuBase bef aft =>
      HH_base (map AI_const bef) aft
  | SuLabel bef n es sh aft =>
      HH_label (map AI_const bef) n es (hh_of_sush i sh) aft
  | SuLocal bef n f sh aft =>
      HH_local (map AI_const bef) n f (hh_of_sush i sh) aft
  | SuPrompt bef tf hs sh aft =>
      HH_prompt (map AI_const bef) tf
        (map (continuation_clause_of_suselt i) hs) (hh_of_sush i sh) aft
  | SuHandler bef hs sh aft =>
      HH_handler (map AI_const bef) hs (hh_of_sush i sh) aft
  end
.

Fixpoint hh_of_swh i sh :=
  match sh with
  | SwBase bef aft =>
      HH_base (map AI_const bef) aft
  | SwLabel bef n es sh aft =>
      HH_label (map AI_const bef) n es (hh_of_swh i sh) aft
  | SwLocal bef n f sh aft =>
      HH_local (map AI_const bef) n f (hh_of_swh i sh) aft
  | SwPrompt bef tf hs sh aft =>
      HH_prompt (map AI_const bef) tf
        (map (continuation_clause_of_swelt i) hs) (hh_of_swh i sh) aft
  | SwHandler bef hs sh aft =>
      HH_handler (map AI_const bef) hs (hh_of_swh i sh) aft
  end
.

Fixpoint hh_of_exnh i sh :=
  match sh with
  | ExBase bef aft =>
      HH_base (map AI_const bef) aft
  | ExLabel bef n es sh aft =>
      HH_label (map AI_const bef) n es (hh_of_exnh i sh) aft
  | ExLocal bef n f sh aft =>
      HH_local (map AI_const bef) n f (hh_of_exnh i sh) aft
  | ExPrompt bef tf hs sh aft =>
      HH_prompt (map AI_const bef) tf hs (hh_of_exnh i sh) aft
  | ExHandler bef hs sh aft =>
      HH_handler (map AI_const bef)
        (map (exception_clause_of_exnelt i) hs) (hh_of_exnh i sh) aft
  end
.


Fixpoint llh_of_lh lh :=
  match lh with
  | LH_base bef aft =>
      match e_to_v_list_opt bef (*those (map v_of_e bef) *) with
      | Some bef => Some (LL_base bef aft)
      | None => None end 
  | LH_rec bef n es lh aft =>
      match e_to_v_list_opt bef (*those (map v_of_e bef)*) with
      | Some bef =>
          match llh_of_lh lh with
          | Some lh' => Some (LL_label bef n es lh' aft)
          | None => None
          end
      | None => None end
  | LH_prompt bef tf hs lh aft =>
      match e_to_v_list_opt bef (*those (map v_of_e bef)*) with
      | Some bef =>
          match llh_of_lh lh with
          | Some lh' => Some (LL_prompt bef tf hs lh' aft)
          | None => None
          end
      | None => None
      end
  | LH_handler bef hs lh aft =>
      match e_to_v_list_opt bef (*those (map v_of_e bef)*) with
      | Some bef =>
          match llh_of_lh lh with
          | Some lh' => Some (LL_handler bef hs lh' aft)
          | None => None
          end
      | None => None
      end 
  end.


Inductive is_pure : lholed -> Prop :=
| BasePure : forall bef aft, is_pure (LH_base bef aft)
| LabelPure : forall bef n es lh aft, is_pure lh -> is_pure (LH_rec bef n es lh aft)
.


Fixpoint susholed_of_lholed lh :=
  match lh with
  | LH_base bef aft =>
      match e_to_v_list_opt bef with
      | Some bef => Some $ SuBase bef aft
      | None => None
      end
  | LH_rec bef n es lh aft =>
      match susholed_of_lholed lh with
      | Some lh =>
          match e_to_v_list_opt bef with
          | Some bef => Some $ SuLabel bef n es lh aft
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Fixpoint swholed_of_lholed lh :=
  match lh with
  | LH_base bef aft =>
      match e_to_v_list_opt bef with
      | Some bef => Some $ SwBase bef aft
      | None => None
      end
  | LH_rec bef n es lh aft =>
      match swholed_of_lholed lh with
      | Some lh =>
          match e_to_v_list_opt bef with
          | Some bef => Some $ SwLabel bef n es lh aft
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Fixpoint exnholed_of_lholed lh :=
  match lh with
  | LH_base bef aft =>
      match e_to_v_list_opt bef with
      | Some bef => Some $ ExBase bef aft
      | None => None
      end
  | LH_rec bef n es lh aft =>
      match exnholed_of_lholed lh with
      | Some lh =>
          match e_to_v_list_opt bef with
          | Some bef => Some $ ExLabel bef n es lh aft
          | None => None
          end
      | None => None
      end
  | _ => None
  end.

Fixpoint sus_trans sh1 sh2 :=
  match sh1 with
  | SuBase bef aft => sus_push_const (sus_append sh2 aft) bef
  | SuLabel bef n es sh aft => SuLabel bef n es (sus_trans sh sh2) aft
  | SuLocal bef n es sh aft => SuLocal bef n es (sus_trans sh sh2) aft
  | SuHandler bef hs sh aft => SuHandler bef hs (sus_trans sh sh2) aft
  | SuPrompt bef ts hs sh aft => SuPrompt bef ts hs (sus_trans sh sh2) aft
  end.

Fixpoint sw_trans sh1 sh2 :=
  match sh1 with
  | SwBase bef aft => sw_push_const (sw_append sh2 aft) bef
  | SwLabel bef n es sh aft => SwLabel bef n es (sw_trans sh sh2) aft
  | SwLocal bef n es sh aft => SwLocal bef n es (sw_trans sh sh2) aft
  | SwHandler bef hs sh aft => SwHandler bef hs (sw_trans sh sh2) aft
  | SwPrompt bef ts hs sh aft => SwPrompt bef ts hs (sw_trans sh sh2) aft
  end.

Fixpoint exn_trans sh1 sh2 :=
  match sh1 with
  | ExBase bef aft => exn_push_const (exn_append sh2 aft) bef
  | ExLabel bef n es sh aft => ExLabel bef n es (exn_trans sh sh2) aft
  | ExLocal bef n es sh aft => ExLocal bef n es (exn_trans sh sh2) aft
  | ExHandler bef hs sh aft => ExHandler bef hs (exn_trans sh sh2) aft
  | ExPrompt bef ts hs sh aft => ExPrompt bef ts hs (exn_trans sh sh2) aft
  end.




(* Tactics *)

Ltac rewrite_cats1_list :=
  match goal with
  | H: context [lfilled _ _ [?e1; ?e2; ?e3; ?e4] _] |- _  =>
      replace [e1; e2; e3; e4] with ([e1; e2; e3] ++ [e4])%SEQ in H => //
  | H: context [lfilled _ _ [?e1; ?e2; ?e3] _] |- _  =>
      replace [e1; e2; e3] with ([e1; e2] ++ [e3])%SEQ in H => //
  | H: context [lfilled _ _ [?e1; ?e2] _] |- _  =>
      rewrite - cat1s in H
  | H: context [lfilled _ _ [?e] _] |- _ =>
      replace [e] with ([] ++ [e])%SEQ in H => //
  | H: context [llfill _ [?e1; ?e2; ?e3; ?e4] = _] |- _  =>
      replace [e1; e2; e3; e4] with ([e1; e2; e3] ++ [e4])%SEQ in H => //
  | H: context [llfill _ [?e1; ?e2; ?e3] = _] |- _  =>
      replace [e1; e2; e3] with ([e1; e2] ++ [e3])%SEQ in H => //
  | H: context [llfill _ [?e1; ?e2] = _] |- _  =>
      rewrite - cat1s in H
  | H: context [llfill _ [?e] = _] |- _ =>
      replace [e] with ([] ++ [e])%SEQ in H => //
  | _ => idtac
  end.
