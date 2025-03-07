From mathcomp Require Import ssreflect ssrbool eqtype seq.
From iris.program_logic Require Import language.
From Coq Require Import Eqdep_dec.
From Wasm.iris.helpers Require Export lfill_prelude.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Definition expr := list administrative_instruction.

(* A value can be an immediate, a trap, a [br i] if it is in a context shallow enough,
   i.e. a [valid_holed i] ; or a return, in any context. *)
(* We use VH and SH instead of LH so that the fill operations are always total functions *)
Inductive val : Type :=
| immV : (list value) -> val
| trapV : val
| brV (i : nat) (lh : valid_holed i) : val
| retV : simple_valid_holed -> val
| callHostV : function_type -> hostfuncidx -> seq.seq value -> llholed -> val
| susV (i : tagidx) (sh: susholed) : val
| swV (tf: function_type) (i : tagidx) (sh: swholed) : val
| thrV (a : immediate) (i: tagidx) (sh: exnholed) : val
.

Definition val_eq_dec : forall v1 v2: val, {v1 = v2} + {v1 <> v2}.
Proof.
  intros v1 v2;destruct v1,v2;auto.
  - destruct (decide (l = l0));[subst;by left|right;intros Hcontr;congruence].
  - destruct (decide (i = i0)). subst.
    destruct (valid_holed_eq_dec lh lh0) as [-> | H].
    by left.
    right. intro. inversion H0.
    apply Eqdep.EqdepTheory.inj_pair2 in H2.
    done.
    right.
    intro.
    inversion H.
    apply eq_sigT_fst in H2.
    done.
  - destruct (simple_valid_holed_eq_dec s s0);subst;[by left|right;congruence..].
  - destruct (function_type_eq_dec f f0), (llholed_eq_dec l0 l2),
      (hostfuncidx_eq_dec h h0), (decide (l = l1)) ;subst; try by right;congruence.
    by left.
  - destruct (i == i0) eqn:Hi.
    + move/eqP in Hi; subst i0. destruct (susholed_eq_dec sh sh0).
      * subst. by left.
      * right. intros Habs; inversion Habs.
        done.
    + right. intros Habs; inversion Habs. subst i0.
      rewrite eq_refl in Hi => //.
  - destruct ((tf == tf0) && (i == i0)) eqn:H.
    + remove_bools_options; subst i0 tf0. destruct (swholed_eq_dec sh sh0).
      * subst. by left.
      * right. intros Habs; inversion Habs.
        done.
    + right. intros Habs; inversion Habs. subst i0 tf0.
      repeat rewrite eq_refl in H => //.
  - destruct ((a == a0) && (i == i0)) eqn:H.
    + remove_bools_options; subst i0 a0. destruct (exnholed_eq_dec sh sh0).
      * subst. by left.
      * right. intros Habs; inversion Habs.
        done.
    + right. intros Habs; inversion Habs. subst i0 a0.
      repeat rewrite eq_refl in H => //. 
Defined.

Definition val_eqb (v1 v2: val) : bool := val_eq_dec v1 v2.
Definition eqvalP : Equality.axiom val_eqb :=
  eq_dec_Equality_axiom val_eq_dec.

Canonical Structure val_eqMixin := Equality.Mixin eqvalP.
Canonical Structure val_eqType := Eval hnf in Equality.Pack (sort := val) (Equality.Class val_eqMixin).


Definition state : Type := store_record * (list value) * instance.

Definition observation := unit.

Definition of_val (v : val) : expr :=
  match v with
  | immV l => v_to_e_list l
  | trapV => [::AI_trap]
  | brV i vh => vfill vh [AI_basic (BI_br i)]
  | retV sh => sfill sh [AI_basic BI_return]
  | callHostV tf h vcs sh => llfill sh [AI_call_host tf h vcs]
  | susV i sh => susfill i sh [AI_suspend_desugared i]
  | swV tf i sh => swfill i sh [AI_switch_desugared tf i]
  | thrV a i sh => exnfill i sh [AI_ref_exn a i; AI_basic BI_throw_ref]
  end.

Lemma of_val_imm (vs : list value) :
  v_to_e_list vs = of_val (immV vs).
Proof. done. Qed.

(* The following operation mirrors the opsem of AI_trap *)
(* in which a trap value swallows all other stack values *)
(* and the opsem of br and return, which skips over all subsequent expressions *)
Definition val_combine (v1 v2 : val) :=
  match v1 with
  | immV l => match v2 with
             | immV l' => immV (l ++ l')
             | trapV => trapV
             | brV i vh => brV (vh_push_const vh l)
             | retV lh => retV (sh_push_const lh l)
             | callHostV tf h cvs sh => callHostV tf h cvs (llh_push_const sh l)
             | susV i sh => susV i (sus_push_const sh l)
             | swV tf i sh => swV tf i (sw_push_const sh l)
             | thrV a i sh => thrV a i (exn_push_const sh l)
             end
  | trapV => trapV
  | brV i vh => brV (vh_append vh (of_val v2))
  | retV lh => retV (sh_append lh (of_val v2))
  | callHostV tf h vcs sh => callHostV tf h vcs (llh_append sh (of_val v2))
  | susV i sh => susV i (sus_append sh (of_val v2))
  | swV tf i sh => swV tf i (sw_append sh (of_val v2))
  | thrV a i sh => thrV a i (exn_append sh (of_val v2))
  end.

(* Intuitively, when writing [NotVal e], we intend to mean e is not a value.
   This is however not enforced by the syntax *)
Inductive ValNotVal :=
  Val : val -> ValNotVal
| NotVal : expr -> ValNotVal
| ThrowRef : expr -> ValNotVal
.

Definition expr_of_val_not_val x :=
  match x with
  | Val v => of_val v
  | NotVal e => e
  | ThrowRef es => AI_basic BI_throw_ref :: es
  end.

Lemma expr_of_val_of_val_not_val v :
  of_val v = expr_of_val_not_val (Val v).
Proof. done. Qed.

Definition val_of_val_not_val x :=
  match x with
  | Val v => Some v
  | NotVal _ => None
  | ThrowRef _ => None 
  end.



(* Combining a val and a ValNotVal. It is intended that combining will yield a ValNotVal 
   representinig the concatenation of the function arguments, and verifies our
   invariant that [NotVal e] is used only when e is not a value *)
Definition val_not_val_combine (v1 : val) (v2 : ValNotVal) : ValNotVal :=
  match v1 with
  | immV l => match v2 with
             | Val (immV l') => Val (immV (l ++ l'))
             | Val trapV => match l with
                           | [] => Val trapV
                           | _ => NotVal (v_to_e_list l ++ [AI_trap])
                           end
             | Val (brV i vh) => Val (brV (vh_push_const vh l))
             | Val (retV lh) => Val (retV (sh_push_const lh l))
             | Val (callHostV tf h vcs lh) => Val (callHostV tf h vcs (llh_push_const lh l))
             | Val (susV i sh) => Val (susV i (sus_push_const sh l))
             | Val (swV tf i sh) => Val (swV tf i (sw_push_const sh l))
             | Val (thrV a i sh) => Val (thrV a i (exn_push_const sh l))
             | ThrowRef es =>
                 match separate_last l with
                 | Some (l, VAL_ref (VAL_ref_exn a i)) =>
                     Val (thrV a i (ExBase l es))
                 | None => ThrowRef es
                 | _ => NotVal (v_to_e_list l ++ [:: AI_basic BI_throw_ref] ++ es)
                 end
             | NotVal e => NotVal (v_to_e_list l ++ e)
             end
  | trapV => match expr_of_val_not_val v2 with
              [] => Val trapV
            | _ => NotVal (AI_trap :: expr_of_val_not_val v2)
            end
  | brV i vh =>
      Val (brV (vh_append vh (expr_of_val_not_val v2)))
  | retV lh =>
      Val (retV (sh_append lh (expr_of_val_not_val v2)))
  | callHostV tf h vcs lh =>
      Val (callHostV tf h vcs (llh_append lh (expr_of_val_not_val v2)))
  | susV i sh =>
      Val (susV i (sus_append sh (expr_of_val_not_val v2)))
  | swV tf i sh =>
      Val (swV tf i (sw_append sh (expr_of_val_not_val v2)))
  | thrV a i sh =>
      Val (thrV a i (exn_append sh (expr_of_val_not_val v2)))
  end.

(* performs a fold_left on a list of ValNotVals. Aborts if a NotVal is reached *)
Fixpoint merge_values (v : val) (vs : list ValNotVal) : ValNotVal  :=
  match vs with
  | [] => Val v
  | a :: vs => match val_not_val_combine v a with
             | Val v => merge_values v vs
             | ThrowRef es => ThrowRef (es ++ flatten (map expr_of_val_not_val vs))
             | NotVal e => NotVal (e ++ flatten (map expr_of_val_not_val vs))  end
  end.

Definition merge_values_list vs :=
  match vs with
  | Val v :: vs => merge_values v vs
  | [] => Val (immV [])
  | ThrowRef es :: vs => ThrowRef (es ++ flatten (map expr_of_val_not_val vs))
  | _ => NotVal (flatten (map expr_of_val_not_val vs))
  end.

(*
Fixpoint capped_nat_of_nat cap n :=
  match n with
  | 0 => Some (Zero cap)
  | S n => match cap with
          | 0 => None
          | S cap => match capped_nat_of_nat cap n with
                    | Some res => Some (PlusOne res)
                    | None => None
                    end
          end
  end.

Lemma capped_nat_of_nat_capped cap n :
  n <= cap -> exists (m : capped_nat cap),
      capped_nat_of_nat cap n = Some m /\
        nat_of_capped_nat m = n.
Proof.
  generalize dependent cap.
  induction n; intros.
  - exists (Zero cap). split => //=.
    destruct cap => //=.
  - destruct cap; first lia.
    assert (n <= cap) as Hn; first lia.
    apply IHn in Hn as (m & Hcap & <-).
    exists (PlusOne m). split => //=.
    rewrite Hcap. done.
Qed.

Lemma capped_nat_of_nat_None cap n :
  capped_nat_of_nat cap n = None -> n > cap.
Proof.
  generalize dependent cap.
  induction n => //=.
  all: destruct cap => //=.
  { intros; lias. }
  destruct (capped_nat_of_nat cap n) eqn:Hcap => //=.
  apply IHn in Hcap.
  intros; lias.
Qed. *)
    

Definition suselt_of_continuation_clause (c : continuation_clause) '(Mk_tagidx x) :=
  match c with
  | DC_catch (Mk_tagidx y) l =>
      if (Nat.ltb y x) then
        Some (SuSuspend y l)
      else if (Nat.eqb y x) then
             None
           else Some (SuSuspend (y - 1) l)
      (* match x with
      | S x' => 
          if (Nat.eqb y x) then None
          else if (Nat.ltb x y)
               then Some (SuSuspend (OPlusS (S x') (y - x - 1)) l) 
               else
                 match capped_nat_of_nat x' (x' - y) with
                 | Some res => Some (SuSuspend (OMinusS (n := x') res) l)
                 | None => None
                 end 
      | 0 => match y with
            | S y' => Some (SuSuspend (OPlusS 0 y') l)
            | 0 => None
            end
      end *)
  | DC_switch y => Some (SuSwitch y)
  end. 

Fixpoint suselts_of_continuation_clauses cs x :=
  match cs with
  | [::] => Some [::]
  | t :: q => match suselt_of_continuation_clause t x with
            | None => None
            | Some t' => match suselts_of_continuation_clauses q x with
                        | None => None
                        | Some q' => Some (t' :: q')
                        end
            end
  end
.



Lemma suselts_of_continuation_clauses_inj i cs ces:
  suselts_of_continuation_clauses cs i = Some ces ->
  map (continuation_clause_of_suselt i) ces = cs.
Proof.
  generalize dependent ces.
  induction cs; destruct ces => //=.
  all: destruct (suselt_of_continuation_clause a i) eqn:Hai => //.
  all: destruct (suselts_of_continuation_clauses cs i) eqn:Hcsi => //.
  intros H; inversion H; subst s0 l.
  rewrite IHcs => //.
  f_equal.
  destruct a => //=.
  - unfold suselt_of_continuation_clause in Hai.
    destruct i.
    destruct t.
    destruct (n0 <? n) eqn:Hn.
    + inversion Hai; subst s.
      simpl. rewrite Hn. done.
    + destruct (n0 =? n) eqn:Hn' => //.
      inversion Hai; subst.
      simpl.
      assert (n0 - 1 >= n).
      { apply Nat.ltb_ge in Hn.
        apply Nat.eqb_neq in Hn'.
        lia. }
      apply Nat.ltb_ge in H0.
      rewrite H0.
      repeat f_equal.
      apply Nat.ltb_ge in Hn.
      apply Nat.eqb_neq in Hn'.
      lia.
(*    destruct n.
    + destruct n0 => //.
      inversion Hai; subst s.
      simpl. done.
    + destruct (n0 =? S n) eqn:Hn => //.
      destruct (S n <? n0) eqn:Hn' => //.
      * apply Nat.ltb_lt in Hn'.
        inversion Hai; subst s.
        simpl.
        repeat f_equal.
        lia.
      * apply Nat.ltb_ge in Hn'.
        assert (n - n0 <= n); first lia.
        apply capped_nat_of_nat_capped in H0 as (m & Hm & Hmrev).
        rewrite Hm in Hai.
        inversion Hai; subst s.
        simpl. rewrite Hmrev.
        repeat f_equal.
        apply Nat.eqb_neq in Hn.
        lia. *)
  - unfold suselt_of_continuation_clause in Hai.
    destruct i. inversion Hai; subst s.
    simpl. done.
Qed. 


Lemma suselts_of_continuation_clauses_inv i l: 
 suselts_of_continuation_clauses
   (map (continuation_clause_of_suselt i) l) i = Some l.
Proof.
  induction l => //=.
  rewrite IHl.
  destruct a => //=.
  - unfold suselt_of_continuation_clause,
      continuation_clause_of_suselt.
    destruct i.
    destruct (n <? n0) eqn:Hn => //=.
    + rewrite Hn. done.
    + destruct (S n <? n0) eqn:Hn'.
      -- apply Nat.ltb_ge in Hn.
         apply Nat.ltb_lt in Hn'. lia.
      -- apply Nat.ltb_ge in Hn.
         apply Nat.ltb_ge in Hn'.
         destruct n0 => //=.
         ++ repeat f_equal. lia.
         ++ destruct (n =? n0) eqn:Hn'' => //=.
            ** apply Nat.eqb_eq in Hn''. lia.
            ** repeat f_equal. lia.
  - unfold suselt_of_continuation_clause,
      continuation_clause_of_suselt.
    destruct i => //=. 
Qed.

Definition swelt_of_continuation_clause (c : continuation_clause) '(Mk_tagidx x) :=
  match c with
  | DC_switch (Mk_tagidx y) =>
      if (Nat.ltb y x) then
        Some (SwSwitch y)
      else if (Nat.eqb y x) then
             None
           else Some (SwSwitch (y - 1))
(*      match x with
      | S x' => 
          if (Nat.eqb y x) then None
          else if (Nat.ltb x y)
               then Some (SwSwitch (OPlusS (S x') (y - x - 1))) 
               else
                 match capped_nat_of_nat x' (x' - y) with
                 | Some res => Some (SwSwitch (OMinusS (n := x') res))
                 | None => None
                 end 
      | 0 => match y with
            | S y' => Some (SwSwitch (OPlusS 0 y'))
            | 0 => None
            end
      end *)
  | DC_catch y l => Some (SwSuspend y l)
  end. 
  

Fixpoint swelts_of_continuation_clauses cs x :=
  match cs with
  | [::] => Some [::]
  | t :: q => match swelt_of_continuation_clause t x with
            | None => None
            | Some t' => match swelts_of_continuation_clauses q x with
                        | None => None
                        | Some q' => Some (t' :: q')
                        end
            end
  end
.


Lemma swelts_of_continuation_clauses_inj i cs ces:
  swelts_of_continuation_clauses cs i = Some ces ->
  map (continuation_clause_of_swelt i) ces = cs.
Proof.
  generalize dependent ces.
  induction cs; destruct ces => //=.
  all: destruct (swelt_of_continuation_clause a i) eqn:Hai => //.
  all: destruct (swelts_of_continuation_clauses cs i) eqn:Hcsi => //.
  intros H; inversion H; subst s0 l.
  rewrite IHcs => //.
  f_equal.
  destruct a => //=.
  - unfold swelt_of_continuation_clause in Hai.
    destruct i. inversion Hai; subst s.
    simpl. done.
  - unfold swelt_of_continuation_clause in Hai.
    destruct i.
    destruct t.
     destruct (n0 <? n) eqn:Hn.
    + inversion Hai; subst s.
      simpl. rewrite Hn. done.
    + destruct (n0 =? n) eqn:Hn' => //.
      inversion Hai; subst.
      simpl.
      assert (n0 - 1 >= n).
      { apply Nat.ltb_ge in Hn.
        apply Nat.eqb_neq in Hn'.
        lia. }
      apply Nat.ltb_ge in H0.
      rewrite H0.
      repeat f_equal.
      apply Nat.ltb_ge in Hn.
      apply Nat.eqb_neq in Hn'.
      lia.
(*    destruct n.
    + destruct n0 => //.
      inversion Hai; subst s.
      simpl. done.
    + destruct (n0 =? S n) eqn:Hn => //.
      destruct (S n <? n0) eqn:Hn' => //.
      * apply Nat.ltb_lt in Hn'.
        inversion Hai; subst s.
        simpl.
        repeat f_equal.
        lia.
      * apply Nat.ltb_ge in Hn'.
        assert (n - n0 <= n); first lia.
        apply capped_nat_of_nat_capped in H0 as (m & Hm & Hmrev).
        rewrite Hm in Hai.
        inversion Hai; subst s.
        simpl. rewrite Hmrev.
        repeat f_equal.
        apply Nat.eqb_neq in Hn.
        lia. *)
Qed.

Lemma swelts_of_continuation_clauses_inv i l: 
 swelts_of_continuation_clauses
   (map (continuation_clause_of_swelt i) l) i = Some l.
Proof.
  induction l => //=.
  rewrite IHl.
  destruct a => //=.
  - destruct i.
    destruct (n <? n0) eqn:Hn => //=.
    + rewrite Hn. rewrite Hn. done.
    + rewrite Hn. destruct (S n <? n0) eqn:Hn'.
      -- apply Nat.ltb_ge in Hn.
         apply Nat.ltb_lt in Hn'. lia.
      -- apply Nat.ltb_ge in Hn.
         apply Nat.ltb_ge in Hn'.
         destruct n0 => //=.
         ++ repeat f_equal. lia.
         ++ destruct (n =? n0) eqn:Hn'' => //=.
            ** apply Nat.eqb_eq in Hn''. lia.
            ** repeat f_equal. lia.
  - destruct i => //=. 
Qed.

Definition exnelt_of_exception_clause (c : exception_clause) '(Mk_tagidx x) :=
  match c with
  | DE_catch (Mk_tagidx y) l =>
      if (Nat.ltb y x) then
        Some (ExCatch y l)
      else if (Nat.eqb y x) then
             None
           else Some (ExCatch (y - 1) l)
(*      match x with
      | S x' => 
          if (Nat.eqb y x) then None
          else if (Nat.ltb x y)
               then Some (ExCatch (OPlusS (S x') (y - x - 1)) l) 
               else
                 match capped_nat_of_nat x' (x' - y) with
                 | Some res => Some (ExCatch (OMinusS (n := x') res) l)
                 | None => None
                 end 
      | 0 => match y with
            | S y' => Some (ExCatch (OPlusS 0 y') l)
            | 0 => None
            end
      end *)
  | DE_catch_ref (Mk_tagidx y) l =>
      if (Nat.ltb y x) then
        Some (ExCatchRef y l)
      else if (Nat.eqb y x) then
             None
           else Some (ExCatchRef (y - 1) l)
(*      match x with
      | S x' => 
          if (Nat.eqb y x) then None
          else if (Nat.ltb x y)
               then Some (ExCatchRef (OPlusS (S x') (y - x - 1)) l) 
               else
                 match capped_nat_of_nat x' (x' - y) with
                 | Some res => Some (ExCatchRef (OMinusS (n := x') res) l)
                 | None => None
                 end 
      | 0 => match y with
            | S y' => Some (ExCatchRef (OPlusS 0 y') l)
            | 0 => None
            end
      end *)
  | _ => None
  end. 


Fixpoint exnelts_of_exception_clauses es x :=
  match es with
  | [::] => Some [::]
  | t :: q => match exnelt_of_exception_clause t x with
            | None => None
            | Some t' => match exnelts_of_exception_clauses q x with
                        | None => None
                        | Some q' => Some (t' :: q')
                        end
            end
  end.


Lemma exnelts_of_exception_clauses_inj i cs ces:
  exnelts_of_exception_clauses cs i = Some ces ->
  map (exception_clause_of_exnelt i) ces = cs.
Proof.
  generalize dependent ces.
  induction cs; destruct ces => //=.
  all: destruct (exnelt_of_exception_clause a i) eqn:Hai => //.
  all: destruct (exnelts_of_exception_clauses cs i) eqn:Hcsi => //.
  intros H; inversion H; subst e0 l.
  rewrite IHcs => //.
  f_equal.
  destruct a => //=.
  - unfold exnelt_of_exception_clause in Hai.
    destruct i.
    destruct t.
    destruct (n0 <? n) eqn:Hn.
    + inversion Hai; subst e.
      simpl. rewrite Hn. done.
    + destruct (n0 =? n) eqn:Hn' => //.
      inversion Hai; subst.
      simpl.
      assert (n0 - 1 >= n).
      { apply Nat.ltb_ge in Hn.
        apply Nat.eqb_neq in Hn'.
        lia. }
      apply Nat.ltb_ge in H0.
      rewrite H0.
      repeat f_equal.
      apply Nat.ltb_ge in Hn.
      apply Nat.eqb_neq in Hn'.
      lia.
(*    destruct n.
    + destruct n0 => //.
      inversion Hai; subst e.
      simpl. done.
    + destruct (n0 =? S n) eqn:Hn => //.
      destruct (S n <? n0) eqn:Hn' => //.
      * apply Nat.ltb_lt in Hn'.
        inversion Hai; subst e.
        simpl.
        repeat f_equal.
        lia.
      * apply Nat.ltb_ge in Hn'.
        assert (n - n0 <= n); first lia.
        apply capped_nat_of_nat_capped in H0 as (m & Hm & Hmrev).
        rewrite Hm in Hai.
        inversion Hai; subst e.
        simpl. rewrite Hmrev.
        repeat f_equal.
        apply Nat.eqb_neq in Hn.
        lia. *)
  - unfold exnelt_of_exception_clause in Hai.
    destruct i.
    destruct t.
         destruct (n0 <? n) eqn:Hn.
    + inversion Hai; subst e.
      simpl. rewrite Hn. done.
    + destruct (n0 =? n) eqn:Hn' => //.
      inversion Hai; subst.
      simpl.
      assert (n0 - 1 >= n).
      { apply Nat.ltb_ge in Hn.
        apply Nat.eqb_neq in Hn'.
        lia. }
      apply Nat.ltb_ge in H0.
      rewrite H0.
      repeat f_equal.
      apply Nat.ltb_ge in Hn.
      apply Nat.eqb_neq in Hn'.
      lia.
    (* destruct n.
    + destruct n0 => //.
      inversion Hai; subst e.
      simpl. done.
    + destruct (n0 =? S n) eqn:Hn => //.
      destruct (S n <? n0) eqn:Hn' => //.
      * apply Nat.ltb_lt in Hn'.
        inversion Hai; subst e.
        simpl.
        repeat f_equal.
        lia.
      * apply Nat.ltb_ge in Hn'.
        assert (n - n0 <= n); first lia.
        apply capped_nat_of_nat_capped in H0 as (m & Hm & Hmrev).
        rewrite Hm in Hai.
        inversion Hai; subst e.
        simpl. rewrite Hmrev.
        repeat f_equal.
        apply Nat.eqb_neq in Hn.
        lia. *)
  - unfold exnelt_of_exception_clause in Hai.
    destruct i => //.
  - unfold exnelt_of_exception_clause in Hai.
    destruct i => //. 
Qed.

Lemma exnelts_of_exception_clauses_inv i l: 
 exnelts_of_exception_clauses
   (map (exception_clause_of_exnelt i) l) i = Some l.
Proof.
  induction l => //=.
  rewrite IHl.
  destruct a => //=.
  - destruct i => //=.
    destruct (n <? n0) eqn:Hn => //=.
    + rewrite Hn. done.
    + destruct (S n <? n0) eqn:Hn'.
      -- apply Nat.ltb_ge in Hn.
         apply Nat.ltb_lt in Hn'. lia.
      -- apply Nat.ltb_ge in Hn.
         apply Nat.ltb_ge in Hn'.
         destruct n0 => //=.
         ++ repeat f_equal. lia.
         ++ destruct (n =? n0) eqn:Hn'' => //=.
            ** apply Nat.eqb_eq in Hn''. lia.
            ** repeat f_equal. lia.
  - destruct i => //=.
     destruct (n <? n0) eqn:Hn => //=.
    + rewrite Hn. done.
    + destruct (S n <? n0) eqn:Hn'.
      -- apply Nat.ltb_ge in Hn.
         apply Nat.ltb_lt in Hn'. lia.
      -- apply Nat.ltb_ge in Hn.
         apply Nat.ltb_ge in Hn'.
         destruct n0 => //=.
         ++ repeat f_equal. lia.
         ++ destruct (n =? n0) eqn:Hn'' => //=.
            ** apply Nat.eqb_eq in Hn''. lia.
            ** repeat f_equal. lia.
Qed.
      

Fixpoint to_val_instr (instr : administrative_instruction) : ValNotVal :=
  match instr with
  | AI_trap => Val trapV
  | AI_basic (BI_br i) => Val (brV (VH_base i [] []))
  | AI_basic BI_return => Val (retV (SH_base [] []))
  | AI_suspend_desugared i => Val (susV i (SuBase [] []))
  | AI_switch_desugared tf i => Val (swV tf i (SwBase [] []))
  | AI_basic BI_throw_ref => ThrowRef [::]
  | AI_basic (BI_const v) => Val (immV [VAL_num v])
  | AI_basic (BI_ref_null r) => Val (immV [VAL_ref (VAL_ref_null r)])
  | AI_ref f => Val (immV [VAL_ref (VAL_ref_func f)])
  | AI_ref_cont f => Val (immV [VAL_ref (VAL_ref_cont f)])
  | AI_ref_exn e i => Val (immV [VAL_ref (VAL_ref_exn e i)])
  | AI_label n labe es =>
      match merge_values_list (map to_val_instr es) with
      | Val (brV i vh) => 
          match vh_decrease (VH_rec [] n labe vh []) with
          | Some vh' => Val (brV vh')
          | None => NotVal [instr]
          end 
      | Val (retV lh) => Val (retV (SH_rec [] n labe lh []))
      | Val (callHostV tf h cvs lh) => Val (callHostV tf h cvs (LL_label [] n labe lh []))
      | Val (susV i sh) => Val (susV i (SuLabel [] n labe sh []))
      | Val (swV tf i sh) => Val (swV tf i (SwLabel [] n labe sh []))
      | Val (thrV a i sh) => Val (thrV a i (ExLabel [] n labe sh []))
      | _ => NotVal [instr]
      end
 | AI_local n f es =>
      match merge_values_list (map to_val_instr es) with
      | Val (callHostV tf h cvs sh) =>
          Val (callHostV tf h cvs (LL_local [] n f sh []))
      | Val (susV i sh) => Val (susV i (SuLocal [] n f sh []))
      | Val (swV tf i sh) => Val (swV tf i (SwLocal [] n f sh []))
      | Val (thrV a i sh) => Val (thrV a i (ExLocal [] n f sh []))
      | _ => NotVal [instr]
      end 
  | AI_call_host tf h cvs => Val (callHostV tf h cvs (LL_base [] []))
  | AI_prompt ts hs es =>
      match merge_values_list (map to_val_instr es) with
      | Val (brV i vh) => Val (brV (VH_prompt [] ts hs vh []))
      | Val (retV lh) => Val (retV (SH_prompt [] ts hs lh []))
      | Val (callHostV tf h cvs lh) => Val (callHostV tf h cvs (LL_prompt []  ts hs lh []))
      | Val (susV i sh) => match suselts_of_continuation_clauses hs i with
                          | Some hs' => Val (susV i (SuPrompt [] ts hs' sh []))
                          | None => NotVal [instr]
                          end
      | Val (swV tf i sh) => match swelts_of_continuation_clauses hs i with
                            | Some hs' => Val (swV tf i (SwPrompt [] ts hs' sh []))
                            | None => NotVal [instr]
                            end
      | Val (thrV a i sh) => Val (thrV a i (ExPrompt [] ts hs sh []))
      | _ => NotVal [instr]
      end
  | AI_handler hs es =>
      match merge_values_list (map to_val_instr es) with
      | Val (brV i vh) => Val (brV (VH_handler [] hs vh []))
      | Val (retV lh) => Val (retV (SH_handler [] hs lh []))
      | Val (callHostV tf h cvs lh) => Val (callHostV tf h cvs (LL_handler [] hs lh []))
      | Val (susV i sh) => Val (susV i (SuHandler [] hs sh []))
      | Val (swV tf i sh) => Val (swV tf i (SwHandler [] hs sh []))
      | Val (thrV a i sh) => match exnelts_of_exception_clauses hs i with
                            | Some hs' => Val (thrV a i (ExHandler [] hs' sh []))
                            | None => NotVal [instr]
                            end
      | _ => NotVal [instr]
      end
  | _ => NotVal [instr]
  end.

Definition to_val (e : expr) : option val :=
  match merge_values_list (map to_val_instr e) with
  | Val v => Some v
  | _ => None
  end.

Definition prim_step (e : expr) (s : state) (os : list observation) (e' : expr) (s' : state) (fork_es' : list expr) : Prop :=
  let '(σ, locs, inst) := s in
  let '(σ', locs', inst') := s' in
    reduce σ (Build_frame locs inst) e σ' (Build_frame locs' inst') e' /\ os = [] /\ fork_es' = [].

  
Lemma val_not_val_combine_app v1 v2 :
  expr_of_val_not_val (val_not_val_combine v1 v2) = of_val v1 ++ expr_of_val_not_val v2.
Proof.
  intros.
  destruct v1, v2 => //=.
  destruct v => //=.
  by rewrite - v_to_e_cat.
  destruct l => //=.
  destruct lh => //= ; rewrite - v_to_e_cat ; by rewrite app_assoc.
  all : try by destruct s => //= ; rewrite - v_to_e_cat ; by rewrite app_assoc.
  all : try by destruct (of_val v) => //=.
  all : try by destruct e => //=.
  all : try by destruct lh => //= ; rewrite app_comm_cons ; rewrite app_assoc.
  all : try by destruct s => //= ; rewrite app_comm_cons ; rewrite app_assoc.
  all : try by destruct l0 => //= ; rewrite app_comm_cons ; rewrite app_assoc.
  all : try by destruct l1 => //= ; rewrite - v_to_e_cat ; rewrite app_assoc.
  all : try by destruct sh => //=; rewrite app_comm_cons app_assoc.
  all : try by destruct sh => //=; rewrite -v_to_e_cat app_assoc.
  all: try by destruct sh => //=; rewrite -app_assoc.
  destruct (separate_last l) as [[l' x]|] eqn:Hl.
    - destruct x => //.
      destruct v => //=.
      apply separate_last_spec in Hl. subst l.
      rewrite -v_to_e_cat. rewrite -app_assoc.
      done.
    - apply separate_last_None in Hl. subst l.
      done. 
Qed.

(* if we write val_not_val_combine_assoc v1 v2 as v1 + v2, this lemma is just plain
   associativity : v1 + (v2 + x) = (v1 + v2) + x. Because of typing, the phrasing is
   a little more complicated *)
Lemma val_not_val_combine_assoc v1 v2 x :
  val_not_val_combine v1 (val_not_val_combine v2 x) = 
    match val_not_val_combine v1 (Val v2) with
    | Val v3 => val_not_val_combine v3 x
    | NotVal es => NotVal (es ++ expr_of_val_not_val x)
    | ThrowRef es => ThrowRef (es ++ expr_of_val_not_val x)
    end.
Proof.
  
  destruct v1 as [ vs1 | | n1 vh1 | sh1 | tf1 h1 vcs1 llh1 | i1 sh1 | tf1 i1 sh1 | a1 i1 sh1 ],
      v2 as [ vs2 | | n2 vh2 | sh2 | tf2 h2 vcs2 llh2 | i2 sh2 | tf2 i2 sh2 | a2 i2 sh2 ],
          x as [[ vs0 | | n0 vh0 | sh0 | tf0 h0 vcs0 llh0 | i0 sh0 | tf0 i0 sh0 | a0 i0 sh0 ] | es0 | ].

  10:{ simpl.
       destruct (separate_last vs2) as [[??] |] eqn:Hlast.
       - destruct v => //=.
         2: destruct v => //=. 
         all: repeat rewrite cat_app.
         all: erewrite separate_last_app; last exact Hlast.
         all: simpl; try done.
         all: rewrite -v_to_e_cat.
         all: rewrite cat_app.
         all: rewrite app_assoc.
         all: done.
       - apply separate_last_None in Hlast as ->.
         rewrite cats0. done. } 
  all: simpl ; try done.

  all: (try destruct vs1).
  all: (try destruct vs2).
  all: (try destruct vs0).
  all: try destruct es0.

  all: simpl ; try done.
  
  all: (try rewrite - vh_push_const_app) ;
    (try rewrite - sh_push_const_app) ;
    (try rewrite - sus_push_const_app) ;
    (try rewrite - sw_push_const_app );
    (try rewrite - exn_push_const_app );
    (try rewrite - llh_push_const_app) ;
    (try rewrite - vh_append_app) ;
    (try rewrite - sh_append_app) ;
    (try rewrite - sus_append_app) ;
    (try rewrite - sw_append_app) ;
    (try rewrite - exn_append_app) ;
    (try rewrite - llh_append_app) ;
    (try rewrite - v_to_e_cat) ; 
    (try rewrite vh_append_nil) ;
    (try rewrite sh_append_nil) ;
    (try rewrite sus_append_nil) ;
    (try rewrite sw_append_nil) ;
    (try rewrite exn_append_nil) ;
    (try rewrite llh_append_nil) ;
    (try rewrite vh_push_const_nil) ;
    (try rewrite sh_push_const_nil) ;
    (try rewrite sus_push_const_nil) ;
    (try rewrite sw_push_const_nil) ;
    (try rewrite exn_push_const_nil) ;
    (try rewrite llh_push_const_nil) ;
    (try rewrite vh_append_nil) ;
    (try rewrite sh_append_nil) ;
    (try rewrite sus_append_nil) ;
    (try rewrite sw_append_nil) ;
    (try rewrite exn_append_nil) ;
    (try rewrite llh_append_nil) ;
    (try rewrite vh_push_const_nil) ;
    (try rewrite sh_push_const_nil) ;
    (try rewrite sus_push_const_nil) ;
    (try rewrite sw_push_const_nil) ;
    (try rewrite exn_push_const_nil) ;
    (try rewrite llh_push_const_nil) ;
    (try rewrite vh_push_const_append) ;
    (try rewrite sh_push_const_append) ;
    (try rewrite sus_push_const_append) ;
    (try rewrite sw_push_const_append) ;
    (try rewrite exn_push_const_append) ;
    (try rewrite llh_push_const_append)
     .

     
  all : simpl ; try done.
  
  all:
    (try destruct (vfill _ _) eqn:Habs ; try by apply vfill_is_nil in Habs as [? _]) ;
    (try rewrite - Habs) ;
    (try destruct (sfill _ _) eqn:Habs' ; try by apply sfill_is_nil in Habs' as [? _]) ;
    (try rewrite - Habs') ;
    (try destruct (llfill _ _) eqn:Habs'' ; try by apply llfill_is_nil in Habs'' as [? _]) ;
    (try rewrite - Habs'') ;
    (try destruct (susfill _ _) eqn:Habs'''; try by apply susfill_is_nil in Habs''' as [? _]);
    (try rewrite - Habs''') ;
    (try destruct (swfill _ _) eqn:Habs''''; try by apply swfill_is_nil in Habs'''' as [? _]);
    (try rewrite - Habs'''') ;
    (try destruct (exnfill _ _) eqn:Habs'''''; try by apply exnfill_is_nil in Habs''''' as [? _]);
    (try rewrite - Habs''''')
  .

  
  all : simpl ; try done.


  all : try by repeat rewrite cats0.
  all : try by repeat rewrite app_comm_cons ; rewrite app_assoc.
  all : try by rewrite app_nil_r.
  all : try by rewrite - app_assoc.
  all : try by destruct vh0 => //= ; rewrite - v_to_e_cat - app_assoc.
  all : try by destruct sh0 => //= ; rewrite - v_to_e_cat - app_assoc.
  all : try by destruct llh0 => //= ; rewrite - v_to_e_cat - app_assoc.
  all : try by destruct (vfill vh2 _) eqn:Habs2 ;
    (try by apply vfill_is_nil in Habs2 as [? _]) ;
    rewrite - Habs2 ;
    destruct vh2 => //= ; rewrite - app_assoc.
  all : try by destruct (sfill sh2 _) eqn:Habs2 ;
    (try by apply sfill_is_nil in Habs2 as [? _]) ;
    rewrite - Habs2 ;
    destruct sh2 => //= ; rewrite - app_assoc.
  all : try by destruct (susfill _ sh2 _) eqn:Habs2;
    (try by apply susfill_is_nil in Habs2 as [? _]);
    rewrite - Habs2;
    destruct sh2 => //=; rewrite - app_assoc.
  all : try by destruct (swfill _ sh2 _) eqn:Habs2;
    (try by apply swfill_is_nil in Habs2 as [? _]);
    rewrite - Habs2; destruct sh2; rewrite /= -app_assoc.
  all: try by destruct (exnfill _ sh2 _) eqn:Habs2;
    (try by apply exnfill_is_nil in Habs2 as [? _]);
    rewrite - Habs2; destruct sh2; rewrite /= -app_assoc.
  all : try by destruct (llfill llh2 _) eqn:Habs2 ;
    (try by apply llfill_is_nil in Habs2 as [? _]) ;
    rewrite - Habs2 ;
    destruct llh2 => //= ; rewrite - app_assoc.
  all : try by destruct vh2 => //= ; rewrite app_comm_cons app_assoc.
  all : try by destruct sh2 => //= ; rewrite app_comm_cons app_assoc.
  all : try by destruct llh2 => //= ; rewrite app_comm_cons app_assoc.
  all: try by repeat f_equal; destruct sh2 ; simpl; repeat rewrite -catA; repeat rewrite -cat_app.
  all: try by repeat f_equal; destruct vs2; 
    [ destruct v => //; destruct v => // 
    |  destruct (separate_last _) as [[??] |] eqn:Hlast;
       [ destruct v1 => //; destruct v1 => //=;
        apply separate_last_spec in Hlast;
        rewrite (separate1 (AI_ref_exn _ _));
        rewrite app_assoc;
        replace (v_to_e_list l ++ [AI_ref_exn e0 t]) with (v_to_e_list (l ++ [VAL_ref (VAL_ref_exn e0 t)]));
                                         [ repeat rewrite cat_app;
                                           rewrite -Hlast |
                                           by rewrite -v_to_e_cat => //]

       |  apply separate_last_None in Hlast
       ]
    ].
  
Qed.


Lemma merge_br i (vh : valid_holed i) es :
  merge_values (brV vh) es =
    Val (brV (vh_append vh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent vh.
  induction es => //=.
  intros. destruct vh ; simpl ; by rewrite cats0.
  intros.
  rewrite vh_append_app.
  rewrite - IHes.
  done.
Qed.

Lemma merge_return sh es :
  merge_values (retV sh) es =
    Val (retV (sh_append sh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent sh.
  induction es => //=.
  intros. destruct sh ; simpl ; by rewrite cats0.
  intros.
  rewrite sh_append_app.
  rewrite - IHes.
  done.
Qed.

Lemma merge_suspend x (sh : susholed) es :
  merge_values (susV x sh) es =
    Val (susV x (sus_append sh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent sh.
  induction es => //=.
  intros sh. rewrite sus_append_nil. done.
  intros. rewrite sus_append_app. rewrite - IHes. done.
Qed.

Lemma merge_switch tf x (sh : swholed) es :
  merge_values (swV tf x sh) es =
    Val (swV tf x (sw_append sh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent sh.
  induction es => //=.
  intros sh. rewrite sw_append_nil. done.
  intros. rewrite sw_append_app. rewrite - IHes. done.
Qed.

Lemma merge_throw a x (sh : exnholed) es :
  merge_values (thrV a x sh) es =
    Val (thrV a x (exn_append sh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent sh.
  induction es => //=.
  intros sh. rewrite exn_append_nil. done.
  intros. rewrite exn_append_app. rewrite - IHes. done.
Qed. 

Lemma merge_call_host tf h cvs sh es :
  merge_values (callHostV tf h cvs sh) es =
    Val (callHostV tf h cvs (llh_append sh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent sh.
  induction es => //=.
  intros. destruct sh ; simpl ; by rewrite cats0.
  intros.
  rewrite llh_append_app.
  rewrite - IHes.
  done.
Qed.

Lemma merge_trap es :
  merge_values trapV es =
    val_not_val_combine trapV (NotVal (flatten (map expr_of_val_not_val es))).
Proof.
  induction es => //=.
  destruct (expr_of_val_not_val a) eqn:Ha => //=.
Qed.


(* This next lemma proves two identities that had to be proven mutually recursively *)
Lemma merge_prepend_flatten vs :
  (forall v0, merge_values v0 vs = val_not_val_combine v0 (merge_values_list vs)) /\
    flatten (map expr_of_val_not_val vs) = expr_of_val_not_val (merge_values_list vs).
Proof.
  induction vs => //=. 
  - split => //. destruct v0 => //=.
    + by rewrite cats0.
    + by rewrite vh_append_nil.
    + by rewrite sh_append_nil.
    + by rewrite llh_append_nil.
    + by rewrite sus_append_nil.
    + by rewrite sw_append_nil.
    + by rewrite exn_append_nil.
  - destruct a => //=.
    + destruct IHvs as [IHvs1 IHvs2].
      rewrite (IHvs1 v).
      split.
      * intro v0 ; rewrite val_not_val_combine_assoc.
        destruct (val_not_val_combine v0 (Val v)) eqn:Hv0a.
        -- done.
        -- by rewrite IHvs2.
        -- by rewrite IHvs2.
      * rewrite IHvs2.
        by rewrite val_not_val_combine_app.
    + split ; last done.
      destruct v0 => //=.
      * by rewrite app_assoc.
      * destruct e => //=.
        by rewrite merge_trap.
      * rewrite merge_br.
        by rewrite vh_append_app.
      * rewrite merge_return.
        by rewrite sh_append_app. 
      * rewrite merge_call_host.
        by rewrite llh_append_app.
      * rewrite merge_suspend.
        by rewrite sus_append_app.
      * rewrite merge_switch.
        by rewrite sw_append_app.
      * rewrite merge_throw.
        by rewrite exn_append_app.
    + split; last done.
      destruct v0 => //=.
      * destruct (separate_last l) as [[??] |] eqn:Hlast.
        -- destruct v => //=.
           2: destruct v => //=.
           all: try rewrite -app_assoc.
           all: try done.
           rewrite merge_throw => /=. done.
        -- done.
      * rewrite merge_br.
        rewrite -vh_append_app. done.
      * rewrite merge_return.
        by rewrite -sh_append_app.
      * rewrite merge_call_host.
        by rewrite -llh_append_app.
      * rewrite merge_suspend.
        by rewrite -sus_append_app.
      * rewrite merge_switch.
        by rewrite -sw_append_app.
      * rewrite merge_throw.
        by rewrite -exn_append_app.
Qed.

(* For convenience, we provide lemmas for usage of each identity separately *)
Lemma merge_prepend v0 vs :
  merge_values v0 vs = val_not_val_combine v0 (merge_values_list vs).
Proof. by edestruct merge_prepend_flatten as [? _]. Qed.

Lemma merge_flatten vs :
  flatten (map expr_of_val_not_val vs) = expr_of_val_not_val (merge_values_list vs).
Proof. by edestruct merge_prepend_flatten as [_ ?]. Qed.

Lemma merge_ThrowRef a l e:
  merge_values_list (map to_val_instr (a :: l)) = ThrowRef e ->
  l = expr_of_val_not_val (merge_values_list (map to_val_instr l)) ->
  a = AI_basic BI_throw_ref /\ l = e. 
Proof.
  simpl.
  destruct (to_val_instr a) eqn:Ha => //=.
  - destruct v => //=.
    + rewrite merge_prepend.
      destruct (merge_values_list _) eqn:Hl => //=.
      * destruct v => //=.
        destruct l0 => //.
      * destruct (separate_last l0) as [[??]|] eqn:Hl0 => //.
        -- destruct v => //.
           destruct v => //.
        -- intros H; inversion H; subst.
           apply separate_last_None in Hl0 as ->.
           destruct a => //=.
           ++ destruct b => //=.
           ++ simpl in Ha.
              destruct (merge_values_list (map _ l1)) => //.
              destruct v => //.
              destruct (exnelts_of_exception_clauses _ _) => //.
           ++ simpl in Ha.
              destruct (merge_values_list (map _ l2)) => //.
              destruct v => //.
              ** destruct (suselts_of_continuation_clauses _ _) => //.
              ** destruct (swelts_of_continuation_clauses _ _) => //.
           ++ simpl in Ha.
              destruct (merge_values_list (map _ l1)) => //.
              destruct v => //.
              destruct i => //.
              destruct (vh_decrease lh) => //.
           ++ simpl in Ha.
              destruct (merge_values_list (map _ l0)) => //.
              destruct v => //.  
    + rewrite merge_trap => //=.
      destruct (flatten _) => //.
    + rewrite merge_br => //=.
    + rewrite merge_return => //=.
    + rewrite merge_call_host => //=.
    + rewrite merge_suspend => //=.
    + rewrite merge_switch => //=.
    + rewrite merge_throw => //=.
  - intros H; inversion H; subst e.
    destruct a => //=.
    destruct b => //=.
    + simpl in Ha. inversion Ha; subst e0 => //=.
      rewrite merge_flatten.
      intros Hl. rewrite -Hl. done.
    + simpl in Ha.
      destruct (merge_values_list (map _ l1)) => //.
      destruct v => //.
      destruct (exnelts_of_exception_clauses _ _) => //.
    + simpl in Ha.
      destruct (merge_values_list (map _ l2)) => //.
      destruct v => //.
      * destruct (suselts_of_continuation_clauses _ _) => //.
      * destruct (swelts_of_continuation_clauses _ _) => //.
    + simpl in Ha.
      destruct (merge_values_list (map _ l1)) => //. 
      destruct v => //.
      destruct i => //.
      destruct (vh_decrease lh) => //.
    + simpl in Ha.
      destruct (merge_values_list (map _ l0)) => //.
      destruct v => //. 
Qed. 



Lemma of_to_val_instr e : expr_of_val_not_val (to_val_instr e) = [e].
Proof.
  cut (forall n, size_of_instruction e < n -> expr_of_val_not_val (to_val_instr e) = [e]).
  intro H ; apply (H (S (size_of_instruction e))) ; try lia.
  intro n.
  generalize dependent e. 
  induction n ; first lia.
  intros e Hsize.
  destruct e => //=.
  - (* Basic instructions *)
    destruct b => //=.
  - (* Handlers *)
    destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge => //.
    destruct v => //.
    + (* Br *)
      simpl.
      repeat f_equal.
      remember (length_rec l0) as m'.
      assert (length_rec l0 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l0.
      generalize dependent lh.
      generalize dependent i.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l0 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge.
        inversion Hmerge.
        apply Eqdep.EqdepTheory.inj_pair2 in H2 ; subst lh ; clear Hmerge.
        subst i0.
        simpl.
        f_equal.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Constant *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge => //.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        
(*        apply vh_decrease_push_const_inv in Hvh as (vh'' & Hvh & Hpush). *)
        assert (size_of_instruction (AI_handler l l0) < S n).  simpl in Hsize. simpl. lia.
        eapply IHm in H0; eauto.
        rewrite -H0.
        destruct lh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Null reference *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        simpl in Hmerge.
        destruct v ; inversion Hmerge.
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        eapply IHm in H0; eauto.
        rewrite -H0.
        destruct lh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
      * (* Trap *)
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        simpl in Hmerge.
        destruct v ; inversion Hmerge.
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        eapply IHm in H0; eauto.
        rewrite -H0.
        destruct lh0 => //. 
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        simpl in Hmerge.
        destruct v ; inversion Hmerge.
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        eapply IHm in H0 => //.
        rewrite -H0.
        destruct lh0 => //. 
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
         simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        simpl in Hmerge.
        destruct v ; inversion Hmerge.
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        eapply IHm in H0 => //. rewrite -H0.
        destruct lh0 => //. 
        specialize (length_cons_rec (AI_ref_cont f) l0).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge.
        inversion Hmerge.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge.
        inversion Hmerge.
      * (* Handler *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_return in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge).
        -- rewrite merge_br in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst i0.
              apply Eqdep.EqdepTheory.inj_pair2 in H2.
              subst lh.
              simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_return in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge).
        -- rewrite merge_br in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst i0.
              apply Eqdep.EqdepTheory.inj_pair2 in H2.
              subst lh.
              simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           rewrite merge_switch in Hmerge => //. 

      * (* Label *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => // ; (try by rewrite merge_return in Hmerge) ; (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge);
                      try by rewrite merge_call_host in Hmerge.
        destruct (vh_decrease (VH_rec _ _ _ _ _)) eqn:Hdecr => //.
        rewrite merge_br in Hmerge.
        replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
        -- inversion Hmerge.
           subst i0.
           apply Eqdep.EqdepTheory.inj_pair2 in H2.
           subst lh.
           simpl in Hdecr.
           destruct i => //.
           destruct (vh_decrease lh0) eqn:Hdecr0 => //.
           inversion Hdecr; subst v.
           simpl. repeat f_equal.
           apply IHm in Hmerge2.
           ++ eapply vfill_decrease in Hdecr0.
              erewrite Hdecr0 in Hmerge2.
              exact Hmerge2.
           ++ simpl. simpl in Hsize. lia.
           ++ unfold length_rec in H; simpl in H.
              unfold length_rec. lia.
        -- clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia. 
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hl0 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //. 
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Call_host *)
        simpl in Hmerge. rewrite merge_call_host in Hmerge.
        simpl in Hmerge.
        destruct (flatten _) => //=.
    + (* Return *)
      simpl. 
      replace (sfill s [AI_basic BI_return]) with l0 ; first done.
      remember (length_rec l0) as m'.
      assert (length_rec l0 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l0.
      generalize dependent s.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l0 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge.
        inversion Hmerge.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge.
        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                 (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
        with l0 ; first done.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref_null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
      * (* Trap *)
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref_cont f) l0).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //. 
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
      * (* Handler *)
         rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge).
        -- rewrite merge_return in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst s. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge).
        -- rewrite merge_return in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst s. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           rewrite merge_switch in Hmerge => //. 
      * (* Label *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- rewrite merge_return in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           inversion Hmerge.
           simpl.
           rewrite (IHm s0 l2) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.
        -- rewrite merge_call_host in Hmerge => //. 
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) => //=.
        destruct v => //=.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
(*      * (* ??? *)
        simpl in Hmerge.
        destruct (merge_values_list _) => //=.
      destruct v => //=. 
        rewrite merge_call_host in Hmerge => //. *)
      * simpl in Hmerge.
        rewrite merge_call_host in Hmerge.
        simpl in Hmerge.
        destruct (flatten _) => //=. 
    + (* Call_host *)
      simpl. replace (llfill l2 [AI_call_host f h l1]) with l0 ; first done.
      remember (length_rec l0) as m'. 
      assert (length_rec l0 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l0.
      generalize dependent l2.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l0 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge.
        inversion Hmerge.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge.
        inversion Hmerge => //. 
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref null *)
          simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_ref f0) l0).
        lia.
      * (* Ref_exn *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_ref_cont f0) l0).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
      * (* Handler *)
         rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l4)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- rewrite merge_call_host in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l5)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- rewrite merge_call_host in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           rewrite merge_switch in Hmerge => //. 
      * (* Label *) 
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l4)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- by rewrite merge_return in Hmerge.
        -- rewrite merge_call_host in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           inversion Hmerge. subst.
           simpl.
           erewrite (IHm _ l4) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hmerge2 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge.
           inversion Hmerge ; subst.
           simpl.
           erewrite (IHm _ l3) => //=.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 ; first done.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.
           simpl in Hsize.
           lia.
           unfold length_rec in H.
           simpl in H.
           unfold length_rec. lia.
        -- rewrite merge_suspend in Hmerge => //. 
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Call host *)
        simpl in Hmerge.
        rewrite merge_call_host in Hmerge.
        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
          with l0 ; first done.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.  
    + (* Suspend *)
      simpl. repeat f_equal.
      remember (length_rec l0) as m'. 
      assert (length_rec l0 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l0.
      generalize dependent sh.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l0 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref null *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f) l0).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
          with l0 ; first done.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.  
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
      * (* Handler *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- rewrite merge_suspend in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- destruct (suselts_of_continuation_clauses l2 _) eqn:Hsuselts' => //.
           rewrite merge_suspend in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal.
              apply suselts_of_continuation_clauses_inj.
              exact Hsuselts'.
              
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           rewrite merge_switch in Hmerge => //. 
      * (* Label *) 
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- by rewrite merge_return in Hmerge.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           inversion Hmerge. subst.
           simpl.
           erewrite (IHm _ l2) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hmerge2 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //. 
           inversion Hmerge ; subst.
           simpl.
           erewrite (IHm _ l1) => //=.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 ; first done.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.
           simpl in Hsize.
           lia.
           unfold length_rec in H.
           simpl in H.
           unfold length_rec. lia.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Call host *)
        simpl in Hmerge.
        rewrite merge_call_host in Hmerge => //.
    + (* Switch *)
      simpl. repeat f_equal.
      remember (length_rec l0) as m'. 
      assert (length_rec l0 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l0.
      generalize dependent sh.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l0 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f) l0).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 

        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
          with l0 ; first done.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.  
      * (* Handler *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- rewrite merge_switch in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses l2 _) eqn:Hswelts' => //.
           rewrite merge_switch in Hmerge => //. 

           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal.
              apply swelts_of_continuation_clauses_inj.
              exact Hswelts'.
              
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
      * (* Label *) 
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- by rewrite merge_return in Hmerge.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           inversion Hmerge. subst.
           simpl.
           erewrite (IHm _ l2) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.

        -- rewrite merge_throw in Hmerge => //. 
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hmerge2 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
           inversion Hmerge ; subst.
           simpl.
           erewrite (IHm _ l1) => //=.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 ; first done.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.
           simpl in Hsize.
           lia.
           unfold length_rec in H.
           simpl in H.
           unfold length_rec. lia.

        -- rewrite merge_throw in Hmerge => //. 
      * (* Call host *)
        simpl in Hmerge.
        rewrite merge_call_host in Hmerge => //.
    + (* Throw *)
      destruct (exnelts_of_exception_clauses l i) eqn:Hexnelts => //. 
      simpl. repeat f_equal.
      apply exnelts_of_exception_clauses_inj => //. 
      remember (length_rec l0) as m'. 
      assert (length_rec l0 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l0.
      generalize dependent sh.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l0 => //=.
      destruct a0 ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        -- destruct v ; inversion Hmerge. subst.
           assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
           rewrite -(IHm sh0 l0 H0 Hmerge0).
           destruct sh0 => //.
           specialize (length_cons_rec (AI_ref_exn e t) l0).
           lia.
        -- destruct l0 => //.
           apply merge_ThrowRef in Hmerge0 as [-> ->].
           2:{
             clear - IHn Hsize.
             induction l0 => //=.
             assert (size_of_instruction a < n) as Han.
             { simpl in Hsize. lia. } 
             specialize (IHn a Han) as Ha'.
             destruct (to_val_instr a) eqn:Ha => /= ; simpl in Ha'.
             - rewrite merge_prepend.
               remember (merge_values_list (map _ l0)) as vnv.
               specialize (val_not_val_combine_app v vnv) as H'.
               destruct (val_not_val_combine v vnv) eqn:Hv ; simpl in H' ; simpl.
               all: rewrite H'.
               all: rewrite Ha'.
               all: rewrite IHl0.
               all: try done.
               all: simpl.
               all: simpl in Hsize.
               all: lia.
             - rewrite Ha'.
               f_equal.
               clear - IHn Hsize.
               induction l0 => //=.
               rewrite IHn.
               f_equal.
               apply IHl0.
               simpl. simpl in Hsize. lia.
               simpl in Hsize. lia.
             - destruct e0 => //.
               inversion Ha'; subst a.
               f_equal. simpl.
               clear - Hsize IHn.
               induction l0 => //=.
               rewrite IHn.
               f_equal.
               apply IHl0.
               simpl. simpl in Hsize. lia.
               simpl in Hsize. lia. } 
           simpl in Hmerge.
           inversion Hmerge.
           subst.
           done.
      * (* Ref_cont *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        simpl in Hmerge.
        inversion Hmerge.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f) l0).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
(*
        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
          with l0 ; first done.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.   *)
      * (* Handler *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge).
        destruct (exnelts_of_exception_clauses l2 _) eqn:Hexnels => //. 
           rewrite merge_throw in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           -- inversion Hmerge.
              subst. simpl.
              repeat f_equal.
              apply exnelts_of_exception_clauses_inj.
              exact Hexnels.
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           -- clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l4)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) eqn:Hswelts => //.
           rewrite merge_switch in Hmerge => //. 
        -- rewrite merge_throw in Hmerge => //. 
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal.
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
      * (* Label *) 
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- by rewrite merge_return in Hmerge.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           inversion Hmerge. subst.
           simpl.
           erewrite (IHm _ l3) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.


      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hmerge2 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
           inversion Hmerge ; subst.
           simpl.
           erewrite (IHm _ l2) => //=.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 ; first done.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.
           simpl in Hsize.
           lia.
           unfold length_rec in H.
           simpl in H.
           unfold length_rec. lia.
      * (* Call host *)
        simpl in Hmerge.
        rewrite merge_call_host in Hmerge => //.

  - (* Prompts *)
    destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge => //.
    destruct v => //.
    + (* Br *)
      simpl.
      repeat f_equal.
      remember (length_rec l1) as m'.
      assert (length_rec l1 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l1.
      generalize dependent lh.
      generalize dependent i.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l1 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge.
        inversion Hmerge.
        apply Eqdep.EqdepTheory.inj_pair2 in H2 ; subst lh ; clear Hmerge.
        subst i0.
        simpl.
        f_equal.
        clear - IHn Hsize.
        induction l1 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl1 at 1 => //=.
        simpl in Hsize.
        lia.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Constant *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge => //.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        
(*        apply vh_decrease_push_const_inv in Hvh as (vh'' & Hvh & Hpush). *)
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        eapply IHm in H0; eauto.
        rewrite -H0.
        destruct lh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l1).
        lia.
      * (* Null reference *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        simpl in Hmerge.
        destruct v ; inversion Hmerge.
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        eapply IHm in H0; eauto.
        rewrite -H0.
        destruct lh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l1).
        lia.
      * (* Trap *)
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        simpl in Hmerge.
        destruct v ; inversion Hmerge.
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        eapply IHm in H0; eauto.
        rewrite -H0.
        destruct lh0 => //. 
        specialize (length_cons_rec (AI_ref f) l1).
        lia.
      * (* Ref_exn *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        simpl in Hmerge.
        destruct v ; inversion Hmerge.
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        eapply IHm in H0 => //.
        rewrite -H0.
        destruct lh0 => //. 
        specialize (length_cons_rec (AI_ref_exn e t) l1).
        lia.
      * (* Ref_cont *)
         simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        simpl in Hmerge.
        destruct v ; inversion Hmerge.
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        eapply IHm in H0 => //. rewrite -H0.
        destruct lh0 => //. 
        specialize (length_cons_rec (AI_ref_cont f) l1).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge.
        inversion Hmerge.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge.
        inversion Hmerge.
      * (* Handler *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_return in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge).
        -- rewrite merge_br in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           ++ inversion Hmerge.
              subst i0.
              apply Eqdep.EqdepTheory.inj_pair2 in H2.
              subst lh.
              simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l1 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl1 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l4)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_return in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge).
        -- rewrite merge_br in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           ++ inversion Hmerge.
              subst i0.
              apply Eqdep.EqdepTheory.inj_pair2 in H2.
              subst lh.
              simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l1 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl1 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           rewrite merge_switch in Hmerge => //. 

      * (* Label *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => // ; (try by rewrite merge_return in Hmerge) ; (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge);
                      try by rewrite merge_call_host in Hmerge.
        destruct (vh_decrease (VH_rec _ _ _ _ _)) eqn:Hdecr => //.
        rewrite merge_br in Hmerge.
        replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
        -- inversion Hmerge.
           subst i0.
           apply Eqdep.EqdepTheory.inj_pair2 in H2.
           subst lh.
           simpl in Hdecr.
           destruct i => //.
           destruct (vh_decrease lh0) eqn:Hdecr0 => //.
           inversion Hdecr; subst v.
           simpl. repeat f_equal.
           apply IHm in Hmerge2.
           ++ eapply vfill_decrease in Hdecr0.
              erewrite Hdecr0 in Hmerge2.
              exact Hmerge2.
           ++ simpl. simpl in Hsize. lia.
           ++ unfold length_rec in H; simpl in H.
              unfold length_rec. lia.
        -- clear - IHn Hsize.
           induction l1 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl1 at 1 => //=.
           simpl in Hsize.
           lia. 
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hl1 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //. 
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Call_host *)
        simpl in Hmerge. rewrite merge_call_host in Hmerge.
        simpl in Hmerge.
        destruct (flatten _) => //=.
    + (* Return *)
      simpl. 
      replace (sfill s [AI_basic BI_return]) with l1 ; first done.
      remember (length_rec l1) as m'.
      assert (length_rec l1 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l1.
      generalize dependent s.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l1 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge.
        inversion Hmerge.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge.
        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                 (map (λ x, expr_of_val_not_val (to_val_instr x)) l1))
        with l1 ; first done.
        clear - IHn Hsize.
        induction l1 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl1 at 1 => //=.
        simpl in Hsize.
        lia.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l1) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_basic (BI_const v)) l1).
        lia.
      * (* Ref_null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l1) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l1).
        lia.
      * (* Trap *)
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l1) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref f) l1).
        lia.
      * (* Ref_exn *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l1) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref_exn e t) l1).
        lia.
      * (* Ref_cont *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l1) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref_cont f) l1).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //. 
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
      * (* Handler *)
         rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge).
        -- rewrite merge_return in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           ++ inversion Hmerge.
              subst s. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l1 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl1 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l4)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge).
        -- rewrite merge_return in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           ++ inversion Hmerge.
              subst s. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l1 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl1 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           rewrite merge_switch in Hmerge => //. 
      * (* Label *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- rewrite merge_return in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           inversion Hmerge.
           simpl.
           rewrite (IHm s0 l3) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l1 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl1 at 1 => //=.
           simpl in Hsize.
           lia.
        -- rewrite merge_call_host in Hmerge => //. 
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) => //=.
        destruct v => //=.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
(*      * (* ??? *)
        simpl in Hmerge.
        destruct (merge_values_list _) => //=.
      destruct v => //=. 
        rewrite merge_call_host in Hmerge => //. *)
      * simpl in Hmerge.
        rewrite merge_call_host in Hmerge.
        simpl in Hmerge.
        destruct (flatten _) => //=. 
    + (* Call_host *)
      simpl. replace (llfill l3 [AI_call_host f h l2]) with l1 ; first done.
      remember (length_rec l1) as m'. 
      assert (length_rec l1 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l1.
      generalize dependent l3.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l1 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge.
        inversion Hmerge.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge.
        inversion Hmerge => //. 
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l1) => //=.
        destruct l5 => //=. 
        specialize (length_cons_rec (AI_basic (BI_const v)) l1).
        lia.
      * (* Ref null *)
          simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l1) => //=.
        destruct l5 => //=. 
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l1).
        lia.
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l1) => //=.
        destruct l5 => //=. 
        specialize (length_cons_rec (AI_ref f0) l1).
        lia.
      * (* Ref_exn *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l1) => //=.
        destruct l5 => //=. 
        specialize (length_cons_rec (AI_ref_exn e t) l1).
        lia.
      * (* Ref_cont *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l1) => //=.
        destruct l5 => //=. 
        specialize (length_cons_rec (AI_ref_cont f0) l1).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
      * (* Handler *)
         rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l5)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- rewrite merge_call_host in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l1 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl1 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l6)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- rewrite merge_call_host in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l1 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl1 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           rewrite merge_switch in Hmerge => //. 
      * (* Label *) 
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l5)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- by rewrite merge_return in Hmerge.
        -- rewrite merge_call_host in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           inversion Hmerge. subst.
           simpl.
           erewrite (IHm _ l5) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l1 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl1 at 1 => //=.
           simpl in Hsize.
           lia.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hmerge2 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge.
           inversion Hmerge ; subst.
           simpl.
           erewrite (IHm _ l4) => //=.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 ; first done.
           clear - IHn Hsize.
           induction l1 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl1 at 1 => //=.
           simpl in Hsize.
           lia.
           simpl in Hsize.
           lia.
           unfold length_rec in H.
           simpl in H.
           unfold length_rec. lia.
        -- rewrite merge_suspend in Hmerge => //. 
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Call host *)
        simpl in Hmerge.
        rewrite merge_call_host in Hmerge.
        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l1))
          with l1 ; first done.
        clear - IHn Hsize.
        induction l1 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl1 at 1 => //=.
        simpl in Hsize.
        lia.  
    + (* Suspend *)
      destruct (suselts_of_continuation_clauses _ _) eqn:Hsuselts => //. 
      simpl. repeat f_equal.
      apply suselts_of_continuation_clauses_inj.
      exact Hsuselts.
      remember (length_rec l1) as m'. 
      assert (length_rec l1 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l1.
      generalize dependent sh.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l1 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l1).
        lia.
      * (* Ref null *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l1).
        lia.
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l1).
        lia.
      * (* Ref_exn *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_exn e t) l1).
        lia.
      * (* Ref_cont *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f) l1).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l1))
          with l1 ; first done.
        clear - IHn Hsize.
        induction l1 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl1 at 1 => //=.
        simpl in Hsize.
        lia.  
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
      * (* Handler *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l4)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- rewrite merge_suspend in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l1 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl1 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l5)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- destruct (suselts_of_continuation_clauses l4 _) eqn:Hsuselts' => //.
           rewrite merge_suspend in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal.
              apply suselts_of_continuation_clauses_inj.
              exact Hsuselts'.
              
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l1 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl1 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           rewrite merge_switch in Hmerge => //. 
      * (* Label *) 
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l4)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- by rewrite merge_return in Hmerge.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           inversion Hmerge. subst.
           simpl.
           erewrite (IHm _ l4) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l1 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl1 at 1 => //=.
           simpl in Hsize.
           lia.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hmerge2 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //. 
           inversion Hmerge ; subst.
           simpl.
           erewrite (IHm _ l3) => //=.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 ; first done.
           clear - IHn Hsize.
           induction l1 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl1 at 1 => //=.
           simpl in Hsize.
           lia.
           simpl in Hsize.
           lia.
           unfold length_rec in H.
           simpl in H.
           unfold length_rec. lia.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Call host *)
        simpl in Hmerge.
        rewrite merge_call_host in Hmerge => //.
    + (* Switch *)
      destruct (swelts_of_continuation_clauses _ _) eqn:Hswelts => //.
      simpl. repeat f_equal.
      apply swelts_of_continuation_clauses_inj.
      exact Hswelts.
      remember (length_rec l1) as m'. 
      assert (length_rec l1 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l1.
      generalize dependent sh.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l1 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l1).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l1).
        lia.
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l1).
        lia.
      * (* Ref_exn *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_exn e t) l1).
        lia.
      * (* Ref_cont *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f) l1).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 

        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l1))
          with l1 ; first done.
        clear - IHn Hsize.
        induction l1 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl1 at 1 => //=.
        simpl in Hsize.
        lia.  
      * (* Handler *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l4)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- rewrite merge_switch in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l1 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl1 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l5)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses l4 _) eqn:Hswelts' => //.
           rewrite merge_switch in Hmerge => //. 

           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal.
              apply swelts_of_continuation_clauses_inj.
              exact Hswelts'.
              
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l1 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl1 at 1 => //=.
              simpl in Hsize.
              lia.
      * (* Label *) 
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l4)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- by rewrite merge_return in Hmerge.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           inversion Hmerge. subst.
           simpl.
           erewrite (IHm _ l4) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l1 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl1 at 1 => //=.
           simpl in Hsize.
           lia.

        -- rewrite merge_throw in Hmerge => //. 
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hmerge2 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
           inversion Hmerge ; subst.
           simpl.
           erewrite (IHm _ l3) => //=.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 ; first done.
           clear - IHn Hsize.
           induction l1 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl1 at 1 => //=.
           simpl in Hsize.
           lia.
           simpl in Hsize.
           lia.
           unfold length_rec in H.
           simpl in H.
           unfold length_rec. lia.

        -- rewrite merge_throw in Hmerge => //. 
      * (* Call host *)
        simpl in Hmerge.
        rewrite merge_call_host in Hmerge => //.
    + (* Throw *)
      simpl. repeat f_equal.
      remember (length_rec l1) as m'. 
      assert (length_rec l1 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l1.
      generalize dependent sh.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l1 => //=.
      destruct a0 ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l1).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l1).
        lia.
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l1).
        lia.
      * (* Ref_exn *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        -- destruct v ; inversion Hmerge. subst.
           assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
           rewrite -(IHm sh0 l1 H0 Hmerge0).
           destruct sh0 => //.
           specialize (length_cons_rec (AI_ref_exn e t) l1).
           lia.
        -- destruct l1 => //.
           apply merge_ThrowRef in Hmerge0 as [-> ->].
           2:{
             clear - IHn Hsize.
             induction l1 => //=.
             assert (size_of_instruction a < n) as Han.
             { simpl in Hsize. lia. } 
             specialize (IHn a Han) as Ha'.
             destruct (to_val_instr a) eqn:Ha => /= ; simpl in Ha'.
             - rewrite merge_prepend.
               remember (merge_values_list (map _ l1)) as vnv.
               specialize (val_not_val_combine_app v vnv) as H'.
               destruct (val_not_val_combine v vnv) eqn:Hv ; simpl in H' ; simpl.
               all: rewrite H'.
               all: rewrite Ha'.
               all: rewrite IHl1.
               all: try done.
               all: simpl.
               all: simpl in Hsize.
               all: lia.
             - rewrite Ha'.
               f_equal.
               clear - IHn Hsize.
               induction l1 => //=.
               rewrite IHn.
               f_equal.
               apply IHl1.
               simpl. simpl in Hsize. lia.
               simpl in Hsize. lia.
             - destruct e0 => //.
               inversion Ha'; subst a.
               f_equal. simpl.
               clear - Hsize IHn.
               induction l1 => //=.
               rewrite IHn.
               f_equal.
               apply IHl1.
               simpl. simpl in Hsize. lia.
               simpl in Hsize. lia. } 
           simpl in Hmerge.
           inversion Hmerge.
           subst.

           done.
      * (* Ref_cont *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        simpl in Hmerge.
        inversion Hmerge.

        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f) l1).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
(*
        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
          with l0 ; first done.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.   *)
      * (* Handler *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge).
        destruct (exnelts_of_exception_clauses _ _) eqn:Hexnels => //. 
           rewrite merge_throw in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           -- inversion Hmerge.
              subst. simpl.
              repeat f_equal.
              apply exnelts_of_exception_clauses_inj.
              exact Hexnels.
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           -- clear - IHn Hsize.
              induction l1 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl1 at 1 => //=.
              simpl in Hsize.
              lia.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l4)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) eqn:Hswelts => //.
           rewrite merge_switch in Hmerge => //. 
        -- rewrite merge_throw in Hmerge => //. 
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal.
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l1 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl1 at 1 => //=.
              simpl in Hsize.
              lia.
      * (* Label *) 
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- by rewrite merge_return in Hmerge.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
           inversion Hmerge. subst.
           simpl.
           erewrite (IHm _ l3) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l1 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl1 at 1 => //=.
           simpl in Hsize.
           lia.


      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hmerge2 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
           inversion Hmerge ; subst.
           simpl.
           erewrite (IHm _ l2) => //=.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 ; first done.
           clear - IHn Hsize.
           induction l1 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl1 at 1 => //=.
           simpl in Hsize.
           lia.
           simpl in Hsize.
           lia.
           unfold length_rec in H.
           simpl in H.
           unfold length_rec. lia.
      * (* Call host *)
        simpl in Hmerge.
        rewrite merge_call_host in Hmerge => //.


  - (* Labels *) 
    destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge => //.
    destruct v => //.
    + (* Br *)
      destruct i => //.
      destruct (vh_decrease _) eqn:Hvh => //=.
      replace (vfill v [AI_basic (BI_br (S i))]) with l0 ; first done.
      remember (length_rec l0) as m'.
      assert (length_rec l0 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l0.
      generalize dependent lh ; generalize dependent v ; generalize dependent i.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l0 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge.
        inversion Hmerge.
        apply Eqdep.EqdepTheory.inj_pair2 in H2 ; subst lh ; clear Hmerge.
        simpl in Hvh.
        inversion Hvh ; subst ; clear Hvh => //=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
          with l0 ; first done.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge.
        inversion Hmerge.
      * (* Constant *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v1 ; inversion Hmerge.
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        apply vh_decrease_push_const_inv in Hvh as (vh'' & Hvh & Hpush).
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm i vh'' lh0 Hvh l0) => //.
        destruct vh'' ; simpl in Hpush ; subst v => //=.
        specialize (length_cons_rec (AI_basic (BI_const v0)) l0).
        lia.
      * (* Null reference *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        simpl in Hmerge.
        destruct v0 ; inversion Hmerge.
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        apply vh_decrease_push_const_inv in Hvh as (vh'' & Hvh & Hpush).
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm i vh'' lh0 Hvh l0) => //.
        destruct vh'' ; simpl in Hpush ; subst v => //=.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
      * (* Trap *)
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        simpl in Hmerge.
        destruct v0 ; inversion Hmerge.
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        apply vh_decrease_push_const_inv in Hvh as (vh'' & Hvh & Hpush).
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm i vh'' lh0 Hvh l0) => //.
        destruct vh'' ; simpl in Hpush ; subst v => //=.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        simpl in Hmerge.
        destruct v0 ; inversion Hmerge.
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        apply vh_decrease_push_const_inv in Hvh as (vh'' & Hvh & Hpush).
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm i vh'' lh0 Hvh l0) => //.
        destruct vh'' ; simpl in Hpush ; subst v => //=.
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
         simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        simpl in Hmerge.
        destruct v0 ; inversion Hmerge.
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        apply vh_decrease_push_const_inv in Hvh as (vh'' & Hvh & Hpush).
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm i vh'' lh0 Hvh l0) => //.
        destruct vh'' ; simpl in Hpush ; subst v => //=.
        specialize (length_cons_rec (AI_ref_cont f) l0).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge.
        inversion Hmerge.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge.
        inversion Hmerge.
      * (* Handler *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v0 => //; (try by rewrite merge_return in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge).
        -- rewrite merge_br in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst i0.
              apply Eqdep.EqdepTheory.inj_pair2 in H2.
              subst lh.
              simpl in Hvh.
              destruct (vh_decrease lh0) eqn:Hdecr => //.
              inversion Hvh; subst v.
              simpl.
              repeat f_equal. 
              eapply IHm.
              exact Hdecr.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v0 => //; (try by rewrite merge_return in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge).
        -- rewrite merge_br in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst i0.
              apply Eqdep.EqdepTheory.inj_pair2 in H2.
              subst lh.
              simpl in Hvh.
              destruct (vh_decrease lh0) eqn:Hdecr => //.
              inversion Hvh; subst v.
              simpl.
              repeat f_equal. 
              eapply IHm.
              exact Hdecr.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           rewrite merge_switch in Hmerge => //. 

      * (* Label *) 
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v0 => // ; (try by rewrite merge_return in Hmerge) ; (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge);
                      try by rewrite merge_call_host in Hmerge.
        destruct (vh_decrease (VH_rec _ _ _ _ _)) eqn:Hdecr => //.
        rewrite merge_br in Hmerge.
        replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
        inversion Hmerge.
        
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        simpl in Hdecr.
        destruct (vh_decrease lh0) eqn:Hdecr0 => //.
        inversion Hdecr; subst v0.
        simpl in Hvh.
        destruct i => //.
        destruct (vh_decrease v1) eqn:Hdecr1 => //.
        inversion Hvh; subst v.
        simpl. repeat f_equal.
        eapply IHm in Hmerge2.
        erewrite <- vfill_decrease.
        exact Hmerge2.
        exact Hdecr1.
        exact Hdecr0.
        simpl; simpl in Hsize; lia.
        unfold length_rec in H; simpl in H; unfold length_rec; lia.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hl1 => //.
        destruct v0 => //.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //. 
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Call_host *)
        simpl in Hmerge. rewrite merge_call_host in Hmerge.
        simpl in Hmerge.
        destruct (flatten _) => //=.
    + (* Return *)
      simpl. 
      replace (sfill s [AI_basic BI_return]) with l0 ; first done.
      remember (length_rec l0) as m'.
      assert (length_rec l0 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l0.
      generalize dependent s.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l0 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge.
        inversion Hmerge.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge.
        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                 (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
        with l0 ; first done.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref_null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
      * (* Trap *)
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref_cont f) l0).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //. 
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
      * (* Handler *)
         rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge).
        -- rewrite merge_return in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst s. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge).
        -- rewrite merge_return in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst s. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           rewrite merge_switch in Hmerge => //. 
      * (* Label *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- rewrite merge_return in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           inversion Hmerge.
           simpl.
           rewrite (IHm s0 l2) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.
        -- rewrite merge_call_host in Hmerge => //. 
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) => //=.
        destruct v => //=.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
(*      * (* ??? *)
        simpl in Hmerge.
        destruct (merge_values_list _) => //=.
      destruct v => //=. 
        rewrite merge_call_host in Hmerge => //. *)
      * simpl in Hmerge.
        rewrite merge_call_host in Hmerge.
        simpl in Hmerge.
        destruct (flatten _) => //=. 
    + (* Call_host *)
      simpl. replace (llfill l2 [AI_call_host f h l1]) with l0 ; first done.
      remember (length_rec l0) as m'. 
      assert (length_rec l0 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l0.
      generalize dependent l2.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l0 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge.
        inversion Hmerge.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge.
        inversion Hmerge => //. 
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref null *)
          simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_ref f0) l0).
        lia.
      * (* Ref_exn *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_ref_cont f0) l0).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
      * (* Handler *)
         rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l4)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- rewrite merge_call_host in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
            rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l5)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- rewrite merge_call_host in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           rewrite merge_switch in Hmerge => //. 
      * (* Label *) 
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l4)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- by rewrite merge_return in Hmerge.
        -- rewrite merge_call_host in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           inversion Hmerge. subst.
           simpl.
           erewrite (IHm _ l4) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hmerge2 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge.
           inversion Hmerge ; subst.
           simpl.
           erewrite (IHm _ l3) => //=.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 ; first done.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.
           simpl in Hsize.
           lia.
           unfold length_rec in H.
           simpl in H.
           unfold length_rec. lia.
        -- rewrite merge_suspend in Hmerge => //. 
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Call host *)
        simpl in Hmerge.
        rewrite merge_call_host in Hmerge.
        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
          with l0 ; first done.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.  
    + (* Suspend *)
      simpl. repeat f_equal.
      remember (length_rec l0) as m'. 
      assert (length_rec l0 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l0.
      generalize dependent sh.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l0 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref null *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f) l0).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
          with l0 ; first done.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.  
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
      * (* Handler *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- rewrite merge_suspend in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) eqn:Hsuselts => //.
           rewrite merge_suspend in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal.
              apply suselts_of_continuation_clauses_inj.
              exact Hsuselts.
              
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           rewrite merge_switch in Hmerge => //. 
      * (* Label *) 
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- by rewrite merge_return in Hmerge.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           inversion Hmerge. subst.
           simpl.
           erewrite (IHm _ l2) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hmerge2 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //. 
           inversion Hmerge ; subst.
           simpl.
           erewrite (IHm _ l1) => //=.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 ; first done.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.
           simpl in Hsize.
           lia.
           unfold length_rec in H.
           simpl in H.
           unfold length_rec. lia.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Call host *)
        simpl in Hmerge.
        rewrite merge_call_host in Hmerge => //.
    + (* Switch *)
      simpl. repeat f_equal.
      remember (length_rec l0) as m'. 
      assert (length_rec l0 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l0.
      generalize dependent sh.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l0 => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f) l0).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 

        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
          with l0 ; first done.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.  
      * (* Handler *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- rewrite merge_switch in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) eqn:Hswelts => //.
           rewrite merge_switch in Hmerge => //. 

           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal.
              apply swelts_of_continuation_clauses_inj.
              exact Hswelts.
              
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
      * (* Label *) 
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- by rewrite merge_return in Hmerge.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           inversion Hmerge. subst.
           simpl.
           erewrite (IHm _ l2) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.

        -- rewrite merge_throw in Hmerge => //. 
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hmerge2 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
           inversion Hmerge ; subst.
           simpl.
           erewrite (IHm _ l1) => //=.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 ; first done.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.
           simpl in Hsize.
           lia.
           unfold length_rec in H.
           simpl in H.
           unfold length_rec. lia.

        -- rewrite merge_throw in Hmerge => //. 
      * (* Call host *)
        simpl in Hmerge.
        rewrite merge_call_host in Hmerge => //.
    + (* Throw *)
      simpl. repeat f_equal.
      remember (length_rec l0) as m'. 
      assert (length_rec l0 < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l0.
      generalize dependent sh.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l0 => //=.
      destruct a0 ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        -- destruct v ; inversion Hmerge. subst.
           assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
           rewrite -(IHm sh0 l0 H0 Hmerge0).
           destruct sh0 => //.
           specialize (length_cons_rec (AI_ref_exn e t) l0).
           lia.
        -- destruct l0 => //.
           apply merge_ThrowRef in Hmerge0 as [-> ->].
           2:{
             clear - IHn Hsize.
             induction l0 => //=.
             assert (size_of_instruction a < n) as Han.
             { simpl in Hsize. lia. } 
             specialize (IHn a Han) as Ha'.
             destruct (to_val_instr a) eqn:Ha => /= ; simpl in Ha'.
             - rewrite merge_prepend.
               remember (merge_values_list (map _ l0)) as vnv.
               specialize (val_not_val_combine_app v vnv) as H'.
               destruct (val_not_val_combine v vnv) eqn:Hv ; simpl in H' ; simpl.
               all: rewrite H'.
               all: rewrite Ha'.
               all: rewrite IHl0.
               all: try done.
               all: simpl.
               all: simpl in Hsize.
               all: lia.
             - rewrite Ha'.
               f_equal.
               clear - IHn Hsize.
               induction l0 => //=.
               rewrite IHn.
               f_equal.
               apply IHl0.
               simpl. simpl in Hsize. lia.
               simpl in Hsize. lia.
             - destruct e0 => //.
               inversion Ha'; subst a.
               f_equal. simpl.
               clear - Hsize IHn.
               induction l0 => //=.
               rewrite IHn.
               f_equal.
               apply IHl0.
               simpl. simpl in Hsize. lia.
               simpl in Hsize. lia. } 
           simpl in Hmerge.
           inversion Hmerge.
           subst.
           done.
      * (* Ref_cont *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f) l0).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
(*
        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
          with l0 ; first done.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.   *)
      * (* Handler *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge).
        destruct (exnelts_of_exception_clauses _ _) eqn:Hexnels => //. 
           rewrite merge_throw in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           -- inversion Hmerge.
              subst. simpl.
              repeat f_equal.
              apply exnelts_of_exception_clauses_inj.
              exact Hexnels.
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           -- clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) eqn:Hswelts => //.
           rewrite merge_switch in Hmerge => //. 
        -- rewrite merge_throw in Hmerge => //. 
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal.
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l0 => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl0 at 1 => //=.
              simpl in Hsize.
              lia.
      * (* Label *) 
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- by rewrite merge_return in Hmerge.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
           inversion Hmerge. subst.
           simpl.
           erewrite (IHm _ l2) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.


      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hmerge2 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
           inversion Hmerge ; subst.
           simpl.
           erewrite (IHm _ l1) => //=.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 ; first done.
           clear - IHn Hsize.
           induction l0 => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl0 at 1 => //=.
           simpl in Hsize.
           lia.
           simpl in Hsize.
           lia.
           unfold length_rec in H.
           simpl in H.
           unfold length_rec. lia.
      * (* Call host *)
        simpl in Hmerge.
        rewrite merge_call_host in Hmerge => //.

  - (* Local *)
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v => //=.
    + (* Call host *)
      replace l with (llfill l1 [AI_call_host f0 h l0]) ; first done.
    remember (length_rec l) as m'. 
    assert (length_rec l < S m') ; first lia.
    remember (S m') as m.
    clear Heqm Heqm' m'.
    generalize dependent l.
    generalize dependent l1.
    induction m => //= ; first by intros ; lia.
    intros.
    destruct l => //=.
    destruct a ; try by inversion Hmerge.
    destruct b ; try by inversion Hmerge.
    * (* Br *)
      simpl in Hmerge.
      rewrite merge_br in Hmerge.
      inversion Hmerge.
    * (* Return *)
      simpl in Hmerge.
      rewrite merge_return in Hmerge.
      inversion Hmerge => //. 
    * (* Const *)
      simpl in Hmerge.
      rewrite merge_prepend in Hmerge.
      destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
        try by inversion Hmerge.
      destruct v0 ; inversion Hmerge. subst.
      assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
      erewrite <- (IHm _ l) => //=.
      destruct l3 => //=. 
      specialize (length_cons_rec (AI_basic (BI_const v)) l).
      lia.
    * (* Ref null *)
         simpl in Hmerge.
      rewrite merge_prepend in Hmerge.
      destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
        try by inversion Hmerge.
      destruct v ; inversion Hmerge. subst.
      assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
      erewrite <- (IHm _ l) => //=.
      destruct l3 => //=. 
      specialize (length_cons_rec (AI_basic (BI_ref_null r)) l).
      lia.
    * (* Trap *)
      simpl in Hmerge.
      rewrite merge_trap in Hmerge.
      destruct (flatten _) => //=.
    * (* Ref *)
      simpl in Hmerge.
      rewrite merge_prepend in Hmerge.
      destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
        try by inversion Hmerge.
      destruct v ; inversion Hmerge. subst.
      assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
      erewrite <- (IHm _ l) => //=.
      destruct l3 => //=. 
      specialize (length_cons_rec (AI_ref f1) l).
      lia.
    * (* Ref_exn *)
           simpl in Hmerge.
      rewrite merge_prepend in Hmerge.
      destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
        try by inversion Hmerge.
      destruct v ; inversion Hmerge. subst.
      assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
      erewrite <- (IHm _ l) => //=.
      destruct l3 => //=. 
      specialize (length_cons_rec (AI_ref_exn e t) l).
      lia.
    * (* Ref_cont *)
           simpl in Hmerge.
      rewrite merge_prepend in Hmerge.
      destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
        try by inversion Hmerge.
      destruct v ; inversion Hmerge. subst.
      assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
      erewrite <- (IHm _ l) => //=.
      destruct l3 => //=. 
      specialize (length_cons_rec (AI_ref_cont f1) l).
      lia.
    * (* Suspend *)
      simpl in Hmerge.
      rewrite merge_suspend in Hmerge => //. 
    * (* Switch *)
      simpl in Hmerge.
      rewrite merge_switch in Hmerge => //. 
    * (* Handler *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_throw in Hmerge).
        
        -- rewrite merge_call_host in Hmerge => //.
           inversion Hmerge; subst.
           simpl.
           f_equal.
           ++ f_equal.
              apply IHm.
              simpl. simpl in Hsize. lia.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec. simpl in H. lia.
           ++  clear - IHn Hsize.
              induction l => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //. 
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l4)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_throw in Hmerge).
        -- rewrite merge_call_host in Hmerge.
           inversion Hmerge; subst.
           simpl.
           f_equal.
           ++ f_equal.
              eapply IHm.
              simpl. simpl in Hsize. lia.
              done.
              unfold length_rec; unfold length_rec in H.
              simpl in H. lia.
           ++ clear - IHn Hsize.
              induction l => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) eqn:Hswelts => //.
           rewrite merge_switch in Hmerge => //. 
    * (* Label *) 
      rewrite map_cons in Hmerge.
      unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
      destruct (merge_values_list (map to_val_instr l3)) eqn:Hmerge2 => //.
      destruct v => //.
      -- destruct (vh_decrease _) => //.
         by rewrite merge_br in Hmerge.
      -- by rewrite merge_return in Hmerge.
      -- rewrite merge_call_host in Hmerge.
         inversion Hmerge ; subst. simpl.
         replace (flatten (map expr_of_val_not_val (map to_val_instr l))) with l.
         erewrite <- (IHm _ l3) => //.
         simpl in Hsize. simpl. lia.
         unfold length_rec in H.
         rewrite map_cons in H.
         simpl in H. unfold length_rec. lia.
         clear - IHn Hsize.
         induction l => //=.
         rewrite IHn ; last by simpl in Hsize ; lia.
         simpl.
         rewrite -> IHl at 1 => //=.
         simpl in Hsize.
         lia.
      -- rewrite merge_suspend in Hmerge => //.
      -- rewrite merge_switch in Hmerge => //.
      -- rewrite merge_throw in Hmerge => //. 
    * (* Local *)
      simpl in Hmerge.
      destruct (merge_values_list _) eqn:Hmerge2 => //.
      destruct v => //.
      -- rewrite merge_call_host in Hmerge.
         inversion Hmerge ; subst.
         simpl.
         erewrite (IHm _ l2) => //=.
         replace (flatten (map expr_of_val_not_val (map to_val_instr l))) with l ; first done.
         clear - IHn Hsize.
         induction l => //=.
         rewrite IHn ; last by simpl in Hsize ; lia.
         simpl.
         rewrite -> IHl at 1 => //=.
         simpl in Hsize.
         lia.
         simpl in Hsize.
         lia.
         unfold length_rec in H.
         simpl in H.
         unfold length_rec. lia.
      -- rewrite merge_suspend in Hmerge => //.
      -- rewrite merge_switch in Hmerge => //.
      -- rewrite merge_throw in Hmerge => //. 
    * (* Call host *)
      simpl in Hmerge.
      rewrite merge_call_host in Hmerge.
      inversion Hmerge => /=.
      rewrite map_map.
      replace (flatten
                 (map (λ x, expr_of_val_not_val (to_val_instr x)) l))
        with l ; first done.
      clear - IHn Hsize.
      induction l => //=.
      rewrite IHn ; last by simpl in Hsize ; lia.
      simpl.
      rewrite -> IHl at 1 => //=.
      simpl in Hsize.
      lia.
    + (* Suspend *)
      simpl. repeat f_equal.
      remember (length_rec l) as m'. 
      assert (length_rec l < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l.
      generalize dependent sh.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l).
        lia.
      * (* Ref null *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l).
        lia.
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f0) l).
        lia.
      * (* Ref_exn *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_exn e t) l).
        lia.
      * (* Ref_cont *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f0) l).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l))
          with l ; first done.
        clear - IHn Hsize.
        induction l => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl at 1 => //=.
        simpl in Hsize.
        lia.  
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
      * (* Handler *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- rewrite merge_suspend in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l))) with l in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) eqn:Hsuselts => //.
           rewrite merge_suspend in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l))) with l in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal.
              apply suselts_of_continuation_clauses_inj.
              exact Hsuselts.
              
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           rewrite merge_switch in Hmerge => //. 
      * (* Label *) 
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- by rewrite merge_return in Hmerge.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l))) with l in Hmerge.
           inversion Hmerge. subst.
           simpl.
           erewrite (IHm _ l1) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl at 1 => //=.
           simpl in Hsize.
           lia.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hmerge2 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //. 
           inversion Hmerge ; subst.
           simpl.
           erewrite (IHm _ l0) => //=.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l))) with l ; first done.
           clear - IHn Hsize.
           induction l => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl at 1 => //=.
           simpl in Hsize.
           lia.
           simpl in Hsize.
           lia.
           unfold length_rec in H.
           simpl in H.
           unfold length_rec. lia.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
      * (* Call host *)
        simpl in Hmerge.
        rewrite merge_call_host in Hmerge => //.
    + (* Switch *)
      simpl. repeat f_equal.
      remember (length_rec l) as m'. 
      assert (length_rec l < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l.
      generalize dependent sh.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l => //=.
      destruct a ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l).
        lia.
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f0) l).
        lia.
      * (* Ref_exn *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_exn e t) l).
        lia.
      * (* Ref_cont *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f0) l).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 

        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l))
          with l ; first done.
        clear - IHn Hsize.
        induction l => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl at 1 => //=.
        simpl in Hsize.
        lia.  
      * (* Handler *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- rewrite merge_switch in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l))) with l in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal. 
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl at 1 => //=.
              simpl in Hsize.
              lia.
        -- destruct (exnelts_of_exception_clauses _ _) => //.
           rewrite merge_throw in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) eqn:Hswelts => //.
           rewrite merge_switch in Hmerge => //. 

           replace (flatten (map expr_of_val_not_val (map to_val_instr l))) with l in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal.
              apply swelts_of_continuation_clauses_inj.
              exact Hswelts.
              
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl at 1 => //=.
              simpl in Hsize.
              lia.
      * (* Label *) 
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- by rewrite merge_return in Hmerge.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l))) with l in Hmerge.
           inversion Hmerge. subst.
           simpl.
           erewrite (IHm _ l1) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl at 1 => //=.
           simpl in Hsize.
           lia.

        -- rewrite merge_throw in Hmerge => //. 
      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hmerge2 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
           inversion Hmerge ; subst.
           simpl.
           erewrite (IHm _ l0) => //=.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l))) with l ; first done.
           clear - IHn Hsize.
           induction l => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl at 1 => //=.
           simpl in Hsize.
           lia.
           simpl in Hsize.
           lia.
           unfold length_rec in H.
           simpl in H.
           unfold length_rec. lia.

        -- rewrite merge_throw in Hmerge => //. 
      * (* Call host *)
        simpl in Hmerge.
        rewrite merge_call_host in Hmerge => //.
    + (* Throw *)
      simpl. repeat f_equal.
      remember (length_rec l) as m'. 
      assert (length_rec l < S m') ; first lia.
      remember (S m') as m.
      clear Heqm Heqm' m'.
      generalize dependent l.
      generalize dependent sh.
      induction m => //= ; first by intros ; lia.
      intros.
      destruct l => //=.
      destruct a0 ; try by inversion Hmerge.
      destruct b ; try by inversion Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l).
        lia.
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f0) l).
        lia.
      * (* Ref_exn *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        -- destruct v ; inversion Hmerge. subst.
           assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
           rewrite -(IHm sh0 l H0 Hmerge0).
           destruct sh0 => //.
           specialize (length_cons_rec (AI_ref_exn e t) l).
           lia.
        -- destruct l => //.
           apply merge_ThrowRef in Hmerge0 as [-> ->].
           2:{
             clear - IHn Hsize.
             induction l => //=.
             assert (size_of_instruction a < n) as Han.
             { simpl in Hsize. lia. } 
             specialize (IHn a Han) as Ha'.
             destruct (to_val_instr a) eqn:Ha => /= ; simpl in Ha'.
             - rewrite merge_prepend.
               remember (merge_values_list (map _ l)) as vnv.
               specialize (val_not_val_combine_app v vnv) as H'.
               destruct (val_not_val_combine v vnv) eqn:Hv ; simpl in H' ; simpl.
               all: rewrite H'.
               all: rewrite Ha'.
               all: rewrite IHl.
               all: try done.
               all: simpl.
               all: simpl in Hsize.
               all: lia.
             - rewrite Ha'.
               f_equal.
               clear - IHn Hsize.
               induction l => //=.
               rewrite IHn.
               f_equal.
               apply IHl.
               simpl. simpl in Hsize. lia.
               simpl in Hsize. lia.
             - destruct e0 => //.
               inversion Ha'; subst a.
               f_equal. simpl.
               clear - Hsize IHn.
               induction l => //=.
               rewrite IHn.
               f_equal.
               apply IHl.
               simpl. simpl in Hsize. lia.
               simpl in Hsize. lia. } 
           simpl in Hmerge.
           inversion Hmerge.
           subst.

           done.
      * (* Ref_cont *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values_list (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f0) l).
        lia.
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
(*
        inversion Hmerge => /=.
        rewrite map_map.
        replace (flatten
                   (map (λ x, expr_of_val_not_val (to_val_instr x)) l0))
          with l0 ; first done.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
        lia.   *)
      * (* Handler *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge).
        destruct (exnelts_of_exception_clauses _ _) eqn:Hexnels => //. 
           rewrite merge_throw in Hmerge.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l))) with l in Hmerge.
           -- inversion Hmerge.
              subst. simpl.
              repeat f_equal.
              apply exnelts_of_exception_clauses_inj.
              exact Hexnels.
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           -- clear - IHn Hsize.
              induction l => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl at 1 => //=.
              simpl in Hsize.
              lia.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l2)) eqn:Hmerge2 => //.
        destruct v => //; (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) eqn:Hswelts => //.
           rewrite merge_switch in Hmerge => //. 
        -- rewrite merge_throw in Hmerge => //. 
           replace (flatten (map expr_of_val_not_val (map to_val_instr l))) with l in Hmerge.
           ++ inversion Hmerge.
              subst. simpl.
              repeat f_equal.
              eapply IHm.
              simpl. simpl in Hsize. lias.
              exact Hmerge2.
              unfold length_rec in H.
              unfold length_rec.
              simpl in H. lias.
           ++ clear - IHn Hsize.
              induction l => //=.
              rewrite IHn ; last by simpl in Hsize ; lia.
              simpl.
              rewrite -> IHl at 1 => //=.
              simpl in Hsize.
              lia.
      * (* Label *) 
        rewrite map_cons in Hmerge.
        unfold merge_values_list, to_val_instr in Hmerge ; fold to_val_instr in Hmerge.
        destruct (merge_values_list (map to_val_instr l1)) eqn:Hmerge2 => //.
        destruct v => //.
        -- destruct (vh_decrease _) => //.
           by rewrite merge_br in Hmerge.
        -- by rewrite merge_return in Hmerge.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
           replace (flatten (map expr_of_val_not_val (map to_val_instr l))) with l in Hmerge.
           inversion Hmerge. subst.
           simpl.
           erewrite (IHm _ l1) => //.
           simpl in Hsize. simpl. lia.
           unfold length_rec in H.
           rewrite map_cons in H.
           simpl in H. unfold length_rec. lia.
           clear - IHn Hsize.
           induction l => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl at 1 => //=.
           simpl in Hsize.
           lia.


      * (* Local *)
        simpl in Hmerge.
        destruct (merge_values_list _) eqn:Hmerge2 => //.
        destruct v => //.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
           inversion Hmerge ; subst.
           simpl.
           erewrite (IHm _ l0) => //=.
           replace (flatten (map expr_of_val_not_val (map to_val_instr l))) with l ; first done.
           clear - IHn Hsize.
           induction l => //=.
           rewrite IHn ; last by simpl in Hsize ; lia.
           simpl.
           rewrite -> IHl at 1 => //=.
           simpl in Hsize.
           lia.
           simpl in Hsize.
           lia.
           unfold length_rec in H.
           simpl in H.
           unfold length_rec. lia.
      * (* Call host *)
        simpl in Hmerge.
        rewrite merge_call_host in Hmerge => //.
Qed.

Lemma flatten_simplify es :
  flatten (map expr_of_val_not_val (map to_val_instr es)) = es.
Proof.
  induction es => //=.
  rewrite of_to_val_instr IHes => //=.
Qed.
  

Lemma merge_to_val es :
  expr_of_val_not_val (merge_values_list (map to_val_instr es)) = es.
Proof.
  induction es => //=.
  specialize (of_to_val_instr a) ; intro Ha'.
  destruct (to_val_instr a) eqn:Ha => /= ; simpl in Ha'.
  - rewrite merge_prepend.
    remember (merge_values_list _) as vnv.
    specialize (val_not_val_combine_app v vnv) ; intro H.
    destruct (val_not_val_combine v vnv) eqn:Hv ; simpl in H ; simpl ; 
      rewrite H Ha' IHes ; subst ; done.
  - rewrite Ha'.
    rewrite flatten_simplify => //=.
  - rewrite app_comm_cons. rewrite Ha'.
    rewrite flatten_simplify => //. 
Qed.


Lemma of_to_val es v : to_val es = Some v -> of_val v = es.
Proof.
  unfold to_val. specialize (merge_to_val es) ; intro H.
  destruct (merge_values_list _) => //.
  simpl in H. intro H' ; inversion H' ; by subst.
Qed.


Lemma to_val_instr_AI_const a :
  to_val_instr (AI_const a) = Val (immV [:: a]).
Proof.
  destruct a => //=.
  destruct v => //=.
Qed. 

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  destruct v.
  - induction l => //=.
    unfold to_val.
    unfold merge_values_list.
    rewrite map_cons.
    rewrite to_val_instr_AI_const.
    unfold to_val in IHl.
    unfold of_val in IHl.    
    destruct (map to_val_instr _) eqn:Hmap; try by inversion IHl.
    destruct (merge_values_list (v :: l0)) eqn:Hmerge ; try by inversion IHl.
    inversion IHl ; subst => //.
    rewrite merge_prepend.
    rewrite Hmerge.
    done.
  - done.
  - unfold of_val, to_val. 
    cut (forall i (vh : valid_holed i) j, merge_values_list (map to_val_instr (vfill vh [AI_basic (BI_br (j + i))])) = Val (brV (vh_increase_repeat vh j))).
    intro H. specialize (H i lh 0).
    unfold vh_increase_repeat in H. simpl in H.
    by rewrite H.
    clear i lh.
    induction vh as [i bef aft | i bef n es vh Hvh aft | i bef ts hs vh Hvh aft | i bef hs vh Hvh aft ] => //= ; intro j.
    + induction bef => //=.
      * rewrite merge_br => //= ; rewrite flatten_simplify.
        assert (VH_base (j + i) [] aft = vh_increase_repeat (VH_base i [] aft) j) as H ;
          last by rewrite H.
        induction j ; unfold vh_increase_repeat => //=.
        fold vh_increase_repeat.
        rewrite - IHj => //=.
      * rewrite to_val_instr_AI_const merge_prepend.
        destruct (merge_values_list _) eqn:Hmerge => //.
        inversion IHbef ; subst v => //=.
        by rewrite - vh_increase_repeat_push_const. 
    + induction bef.
      * simpl. specialize (Hvh (S j)).
        replace (BI_br (S j + i)) with (BI_br (j + S i)) in Hvh ; last by rewrite - S_plus.
        rewrite Hvh => /=.
        rewrite vh_decrease_increase.
        rewrite merge_br.
        rewrite flatten_simplify => //=.
        rewrite vh_increase_repeat_rec.
        destruct (S_plus j i) => //.
      * simpl. rewrite to_val_instr_AI_const.
        rewrite merge_prepend.
        destruct (merge_values_list _) eqn:Hmerge => //.
        inversion IHbef ; subst v => //.
        simpl.
        by rewrite - vh_increase_repeat_push_const.
    + induction bef.
      * simpl.
        rewrite Hvh.
        rewrite merge_br.
        rewrite flatten_simplify.
        simpl.
        rewrite -vh_increase_repeat_prompt.
        done.
      * simpl. rewrite to_val_instr_AI_const.
        rewrite merge_prepend.
        destruct (merge_values_list _) eqn:Hmerge => //.
        inversion IHbef; subst v => //.
        simpl.
        by rewrite - vh_increase_repeat_push_const.
            + induction bef.
      * simpl.
        rewrite Hvh.
        rewrite merge_br.
        rewrite flatten_simplify.
        simpl.
        rewrite -vh_increase_repeat_handler.
        done.
      * simpl. rewrite to_val_instr_AI_const.
        rewrite merge_prepend.
        destruct (merge_values_list _) eqn:Hmerge => //.
        inversion IHbef; subst v => //.
        simpl.
        by rewrite - vh_increase_repeat_push_const.
  - unfold of_val, to_val.
    induction s.
    + induction l => //=.
      * rewrite merge_return.
        rewrite flatten_simplify.
        done.
      * rewrite to_val_instr_AI_const merge_prepend.
        destruct (merge_values_list _) => //=.
        inversion IHl ; subst => //=.
    + induction l => /=.
      * destruct (merge_values_list _) => //.
        inversion IHs ; subst => /=.
        rewrite merge_return.
        rewrite flatten_simplify.
        done.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHs.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //=.
            + induction l => /=.
      * destruct (merge_values_list _) => //.
        inversion IHs ; subst => /=.
        rewrite merge_return.
        rewrite flatten_simplify.
        done.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHs.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //=.
            + induction l => /=.
      * destruct (merge_values_list _) => //.
        inversion IHs ; subst => /=.
        rewrite merge_return.
        rewrite flatten_simplify.
        done.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHs.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //=.
  - unfold of_val, to_val => //=.
    induction l0 => //=.
    + induction l0 => //=.
      * rewrite merge_call_host.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        destruct (merge_values_list _) => //=.
        inversion IHl0 ; subst => //.
    + induction l0 => //=.
      * destruct (merge_values_list _) => //.
        inversion IHl0 ; subst => /=.
        rewrite merge_call_host.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHl0.
        destruct (merge_values_list _) => //.
        inversion IHl1 ; subst => //.
    +  induction l0 => //=.
      * destruct (merge_values_list _) => //.
        inversion IHl0 ; subst => /=.
        rewrite merge_call_host.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHl0.
        destruct (merge_values_list _) => //.
        inversion IHl1 ; subst => //.
            +  induction l0 => //=.
      * destruct (merge_values_list _) => //.
        inversion IHl0 ; subst => /=.
        rewrite merge_call_host.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHl0.
        destruct (merge_values_list _) => //.
        inversion IHl1 ; subst => //.
            +  induction l0 => //=.
      * destruct (merge_values_list _) => //.
        inversion IHl0 ; subst => /=.
        rewrite merge_call_host.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHl0.
        destruct (merge_values_list _) => //.
        inversion IHl1 ; subst => //.
  - unfold of_val, to_val => //=.
    induction sh => //=.
    + induction l => //=.
      * rewrite merge_suspend.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        destruct (merge_values_list _) => //=.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values_list _) => //.
        destruct v => //. 
        inversion IHsh ; subst => /=.
        rewrite merge_suspend.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //=.
    + induction l => //=.
      * destruct (merge_values_list _) => //.
        destruct v => //. 
        inversion IHsh ; subst => /=.
        rewrite merge_suspend.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values_list _) => //.
        destruct v => //. 
        inversion IHsh ; subst => /=.
        rewrite merge_suspend.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values_list _) => //.
        inversion IHsh ; subst => /=.
        rewrite suselts_of_continuation_clauses_inv.
        rewrite merge_suspend.
        rewrite flatten_simplify => //=.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //.

  - unfold of_val, to_val => //=.
    induction sh => //=.
    + induction l => //=.
      * rewrite merge_switch.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        destruct (merge_values_list _) => //=.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values_list _) => //.
        destruct v => //. 
        inversion IHsh ; subst => /=.
        rewrite merge_switch.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //=.
    + induction l => //=.
      * destruct (merge_values_list _) => //.
        destruct v => //. 
        inversion IHsh ; subst => /=.
        rewrite merge_switch.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values_list _) => //.
        destruct v => //. 
        inversion IHsh ; subst => /=.
        rewrite merge_switch.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values_list _) => //.
        inversion IHsh ; subst => /=.
        rewrite swelts_of_continuation_clauses_inv.
        rewrite merge_switch.
        rewrite flatten_simplify => //=.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //.
  - unfold of_val, to_val => //=.
    induction sh => //=.
    + induction l => //=.
      * rewrite merge_throw.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        destruct (merge_values_list _) => //=.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values_list _) => //.
        destruct v => //. 
        inversion IHsh ; subst => /=.
        rewrite merge_throw.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //=.
    + induction l => //=.
      * destruct (merge_values_list _) => //.
        destruct v => //. 
        inversion IHsh ; subst => /=.
        rewrite merge_throw.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values_list _) => //.
        destruct v => //. 
        inversion IHsh ; subst => /=.
        rewrite exnelts_of_exception_clauses_inv.
        rewrite merge_throw.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values_list _) => //.
        inversion IHsh ; subst => /=.
        rewrite merge_throw.
        rewrite flatten_simplify => //=.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values_list _) => //.
        inversion IHl ; subst => //.
        
Qed.


Lemma to_val_cons_is_none_or_cons : forall e0 e r,
  to_val (e0 :: e)%SEQ = r -> is_none_or (fun l => match l with | immV v => v != [] | _ => true end) r.
Proof.
  intros e0 e r H ; subst r.
  cut (forall n e0 e, length_rec (e0 :: e) < n ->  is_none_or (λ l : val, match l with
                         | immV v => v != []
                         | _ => true
                                                              end) (to_val (e0 :: e)%SEQ)).
  intro H ; apply (H (S (length_rec (e0 :: e)))) ; try lia.
  clear e e0.
  induction n => //= ; first lia.
  intros e0 e Hlen.
  destruct e0 => //.
  destruct b => //= ; unfold to_val => /=.
  - rewrite merge_br => //.
  - rewrite merge_return => //.
  - rewrite merge_prepend => /=.
    destruct e => //.
    assert (length_rec (a :: e) < n).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec => //=. lia.
    apply IHn in H.
    unfold to_val in H.
    destruct (merge_values_list _) => //.
    destruct v0 => //.
  - rewrite merge_prepend => /=.
    destruct e => //.
    assert (length_rec (a :: e) < n).
     unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec => //=. lia.
    apply IHn in H.
    unfold to_val in H.
    destruct (merge_values_list _) => //.
    destruct v => //.
  - unfold to_val => //=.
    rewrite merge_trap => /=.
    rewrite flatten_simplify => /=.
    destruct e => //=.
  - unfold to_val => /=. rewrite merge_prepend => /=.
    destruct e => //.
    assert (length_rec (a :: e) < n).
     unfold length_rec in Hlen ; simpl in Hlen.
     unfold length_rec => //=. lia.
     apply IHn in H.
     unfold to_val in H.
     destruct (merge_values_list _) => //.
     destruct v => //.
  - unfold to_val => /=. rewrite merge_prepend => /=.
    destruct e => //.
    assert (length_rec (a :: e) < n).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec => //=. lia.
    apply IHn in H.
    unfold to_val in H.
    destruct (merge_values_list _) => //.
    destruct v => //.
  - unfold to_val => /=. rewrite merge_prepend => /=.
    destruct e => //.
    assert (length_rec (a :: e) < n).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec => //=. lia.
    apply IHn in H.
    unfold to_val in H.
    destruct (merge_values_list _) => //.
    destruct v => //.
  - unfold to_val => /=. rewrite merge_suspend => //=.
  - unfold to_val => /=. rewrite merge_switch => //=.
  - unfold to_val.
    unfold merge_values_list, map, to_val_instr.
    fold to_val_instr.
    destruct l0 ; first done.
    assert (length_rec (a :: l0) < n).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec.
    rewrite map_cons.
    simpl.
    lia.
    apply IHn in H.
    unfold is_none_or in H.
    unfold to_val in H.
    destruct (merge_values_list _) => //.
    destruct v => //.
    + rewrite merge_br => //=.
    + rewrite merge_return => //=.
    + rewrite merge_call_host => //=.
    + rewrite merge_suspend => //=.
    + rewrite merge_switch => //=.
    + destruct (exnelts_of_exception_clauses _ _) eqn:Hexnelts => //.
      rewrite merge_throw => //=.
  - unfold to_val.
    unfold merge_values_list, map, to_val_instr.
    fold to_val_instr.
    destruct l1 ; first done.
    assert (length_rec (a :: l1) < n).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec.
    rewrite map_cons.
    simpl.
    lia.
    apply IHn in H.
    unfold is_none_or in H.
    unfold to_val in H.
    destruct (merge_values_list _) => //.
    destruct v => //.
    + rewrite merge_br => //=.
    + rewrite merge_return => //=.
    + rewrite merge_call_host => //=.
    + destruct (suselts_of_continuation_clauses _ _) => //.
      rewrite merge_suspend => //=.
    + destruct (swelts_of_continuation_clauses _ _) => //. 
      rewrite merge_switch => //=.
    + rewrite merge_throw => //=.
  - unfold to_val.
    unfold merge_values_list, map, to_val_instr.
    fold to_val_instr.
    destruct l0 ; first done.
    assert (length_rec (a :: l0) < n).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec.
    rewrite map_cons.
    simpl.
    lia.
    apply IHn in H.
    unfold is_none_or in H.
    unfold to_val in H.
    destruct (merge_values_list _) => //.
    destruct v => //.
    + destruct (vh_decrease _) eqn:Hdecr => //=.
      rewrite merge_br => //=.
    + rewrite merge_return => //=.
    + rewrite merge_call_host => //=.
    + rewrite merge_suspend => //=.
    + rewrite merge_switch => //=.
    + rewrite merge_throw => //=.
  - unfold to_val => //=.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v => //.
    rewrite merge_call_host => //.
    rewrite merge_suspend => //.
    rewrite merge_switch => //.
    rewrite merge_throw => //. 
  - unfold to_val => //=.
    rewrite merge_call_host => //=.
Qed.
    
Lemma to_val_trap_is_singleton : ∀ e,
    to_val e = Some trapV -> e = [::AI_trap].
Proof.
  intro e.
  destruct e => //=.
  destruct a => //=.
  destruct b => //= ; unfold to_val => /=.
  - by rewrite merge_br.
  - by rewrite merge_return.
  - rewrite merge_prepend.
    destruct (merge_values_list _) => //=.
    destruct v0 => //=.
  - rewrite merge_prepend.
    destruct (merge_values_list _) => //=.
    destruct v => //. 
  - unfold to_val => /=.
    destruct e => //=.
    rewrite of_to_val_instr.
    done.
  - unfold to_val => /=. rewrite merge_prepend.
    destruct (merge_values_list _) => //=.
    destruct v => //=.
  - unfold to_val => /=. rewrite merge_prepend.
    destruct (merge_values_list _) => //=.
    destruct v => //.
  - unfold to_val => /=. rewrite merge_prepend.
    destruct (merge_values_list _) => //=.
    destruct v => //.
  - unfold to_val => //=.
    rewrite merge_suspend => //=.
  - unfold to_val => /=; rewrite merge_switch => //.
  - unfold to_val => /=.
    destruct (merge_values_list _) => //=.
    destruct v => //=.
    rewrite merge_br => //=.
    rewrite merge_return => //=.
    rewrite merge_call_host => //=.
    rewrite merge_suspend => //.
    rewrite merge_switch => //.
    destruct (exnelts_of_exception_clauses _ _) => //.
    rewrite merge_throw => //.
  - unfold to_val => /=.
    destruct (merge_values_list _) => //=.
    destruct v => //=.
    rewrite merge_br => //=.
    rewrite merge_return => //=.
    rewrite merge_call_host => //=.
    destruct (suselts_of_continuation_clauses _ _) => //. 
    rewrite merge_suspend => //.
    destruct (swelts_of_continuation_clauses _ _) => //. 
    rewrite merge_switch => //.
    rewrite merge_throw => //. 
  - unfold to_val => /=.
    destruct (merge_values_list _) => //=.
    destruct v => //=.
    destruct i => //=.
    destruct (vh_decrease _) => //=.
    rewrite merge_br => //=.
    rewrite merge_return => //=.
    rewrite merge_call_host => //=.
    rewrite merge_suspend => //.
    rewrite merge_switch => //.
    rewrite merge_throw => //.
  - unfold to_val => //=.
    destruct (merge_values_list _) => //.
    destruct v => //.
    rewrite merge_call_host => //.
    rewrite merge_suspend => //.
    rewrite merge_switch => //. 
    rewrite merge_throw => //.
  - unfold to_val => //= ; rewrite merge_call_host => /=.
    destruct (flatten _) => //=.
Qed. 


Lemma flatten_map_expr_of_val_not_val vs :
  flatten (map expr_of_val_not_val vs) =
    expr_of_val_not_val (merge_values_list vs).
Proof.
  induction vs => //=.
  destruct a => //=.
  rewrite IHvs.
  rewrite merge_prepend.
  by rewrite val_not_val_combine_app.
Qed.

Lemma merge_app vs1 vs2:
  merge_values_list (vs1 ++ vs2) =
    match (merge_values_list vs1) with
    | Val v1 => val_not_val_combine v1 (merge_values_list vs2)
    | NotVal e1 => NotVal (e1 ++ expr_of_val_not_val (merge_values_list vs2))
    | ThrowRef es => ThrowRef (es ++ expr_of_val_not_val (merge_values_list vs2))
    end.
Proof.
  induction vs1 => //=.
  { destruct (merge_values_list vs2) => //.
    destruct v => //.
    by rewrite vh_push_const_nil.
    by rewrite sh_push_const_nil.
    by rewrite llh_push_const_nil.
    by rewrite sus_push_const_nil.
    by rewrite sw_push_const_nil.
    by rewrite exn_push_const_nil.
  }
  destruct a => //.
  { do 2 rewrite merge_prepend.
    rewrite IHvs1.  
    destruct (merge_values_list vs1) eqn:Hvs1 => //=.
    - by rewrite val_not_val_combine_assoc.
    - destruct v => //=.
      + by rewrite app_assoc. 
      + destruct e => //=.
      + destruct (merge_values_list vs2) ;
          by rewrite vh_append_app.
      + destruct (merge_values_list vs2) ;
          by rewrite sh_append_app.
      + destruct (merge_values_list vs2) ;
          by rewrite llh_append_app.
      + destruct (merge_values_list vs2);
          by rewrite sus_append_app.
      + destruct (merge_values_list vs2);
          by rewrite sw_append_app.
      + destruct (merge_values_list vs2);
          by rewrite exn_append_app.
    - destruct v => //=.
      + destruct (separate_last l) as [[??]|] eqn:Hl => //=.
        apply separate_last_spec in Hl as ->.
        destruct v => //=.
        * rewrite app_comm_cons app_assoc => //.
        * destruct v => //=.
          all: rewrite app_comm_cons app_assoc => //.
      + rewrite - vh_append_app => //.
      + rewrite - sh_append_app => //.
      + rewrite - llh_append_app => //.
      + rewrite - sus_append_app => //.
      + rewrite - sw_append_app => //.
      + rewrite - exn_append_app => //. 
    } 
    all: rewrite map_app.
  all: rewrite flatten_cat.
  all: rewrite (flatten_map_expr_of_val_not_val vs2).
  by rewrite catA.
  by rewrite app_assoc.
Qed.

Lemma to_val_is_immV es vs :
  to_val es = Some (immV vs) -> es = map (λ x, AI_const x) vs.
Proof.
  generalize dependent vs.
  induction es => //=.
  intros.
  unfold to_val in H.
  simpl in H.
  inversion H => //=.

  intros.
  unfold to_val in H ; simpl in H.
  destruct (to_val_instr a) eqn:Ha => //.
  rewrite merge_prepend in H.
  unfold to_val in IHes.
  destruct (merge_values_list _) => //.
  - destruct v, v0 => //.
    + simpl in H.
      inversion H ; subst.
      erewrite IHes => //.
      destruct a => //.
      destruct b => //.
      all: try by inversion Ha.
      all: simpl in Ha.
      all: destruct (merge_values_list _) => //.
      all: destruct v => //.
      destruct (exnelts_of_exception_clauses _ _) => //.
      destruct (suselts_of_continuation_clauses _ _) => //.
      destruct (swelts_of_continuation_clauses _ _) => //.
      destruct i => //. 
      destruct (vh_decrease _) => //.
    + simpl in H.
      destruct l => //.
    + simpl in H.
      destruct l => //.
    + simpl in H.
      destruct (vfill lh _) => //.
    + simpl in H.
      destruct (sfill _ _) => //.
    + simpl in H.
      destruct (llfill _ _) => //.
    + simpl in H.
      destruct (susfill _ _ _) => //.
    + simpl in H.
      destruct (swfill _ _ _) => //.
    + simpl in H.
      destruct (exnfill _ _ _) => //. 
  - destruct v => //.
    destruct e => //.
  - destruct v => //=.
    unfold val_not_val_combine in H.
    destruct (separate_last l) as [[??]|] => //.
    destruct v => //.
    destruct v => //. 
Qed.

Lemma merge_is_not_val_is_throw_ref es es' :
  (merge_values_list (map to_val_instr es) = NotVal es' ->
   es = es') /\
    (merge_values_list (map to_val_instr es) = ThrowRef es' ->
     es = AI_basic BI_throw_ref :: es').
Proof.
  generalize dependent es'.
  induction es => //= ; intro es'.
  destruct (to_val_instr a) eqn:Ha => //=.
  - destruct a => //= ; simpl in Ha.
    + destruct b => //= ; inversion Ha ; subst.
      * by rewrite merge_br.
      * by rewrite merge_return.
      * rewrite merge_prepend.
        destruct (merge_values_list _) eqn:Hmerge => //=.
        -- destruct v => //=.
           split; last by intros.
           intro H ; inversion H ; subst.
           rewrite (to_val_trap_is_singleton (e := es)) => //.
           unfold to_val ; by rewrite Hmerge.
        -- split; last by intros.
           intro H ; inversion H.
           edestruct IHes as [Hres _].
           by erewrite Hres.
        -- split; last by intros.
           intro H; inversion H.
           edestruct IHes as [_ Hres].
           by erewrite Hres.
      *  rewrite merge_prepend.
        destruct (merge_values_list _) eqn:Hmerge => //=.
        -- destruct v => //=.
           split; last by intros.
           intro H ; inversion H ; subst.
           rewrite (to_val_trap_is_singleton (e := es)) => //.
           unfold to_val ; by rewrite Hmerge.
        -- split; last by intros.
           intro H ; inversion H.
           edestruct IHes as [Hres _].
           by erewrite Hres.
        -- split; last by intros.
           intro H; inversion H.
           edestruct IHes as [_ Hres].
           by erewrite Hres.
    + inversion Ha; subst v.
      rewrite merge_trap => //=.
      rewrite flatten_simplify.
      destruct es => //=.
      split; last by intros.
      intro H; inversion H; subst. done.
    + inversion Ha; subst.
      rewrite merge_prepend.
      simpl.
      destruct (merge_values_list (map _ es)) eqn:Hmerge => //=.
      -- destruct v => //=.
         split; last done.
         intros H; inversion H; subst es'.
         rewrite (to_val_trap_is_singleton (e := es)) => //.
         unfold to_val ; by rewrite Hmerge.
      -- split; last by intros.
         intro H ; inversion H; subst.
         edestruct IHes as [Hres _].
         rewrite Hres => //.
      -- split; last by intros.
         intros H; inversion H; subst es'.
         edestruct IHes as [_ Hres].
         by erewrite Hres.
    + inversion Ha; subst v.
      rewrite merge_prepend.
      simpl.
      destruct (merge_values_list (map _ es)) eqn:Hmerge => //=.
      -- destruct v => //=.
         split; last done.
         intros H; inversion H; subst es'.
         rewrite (to_val_trap_is_singleton (e := es)) => //.
         unfold to_val ; by rewrite Hmerge.
      -- split; last by intros.
         intro H ; inversion H; subst.
         edestruct IHes as [Hres _].
         rewrite Hres => //.
    + inversion Ha; subst v.
      rewrite merge_prepend.
      simpl.
      destruct (merge_values_list (map _ es)) eqn:Hmerge => //=.
      -- destruct v => //=.
         split; last done.
         intros H; inversion H; subst es'.
         rewrite (to_val_trap_is_singleton (e := es)) => //.
         unfold to_val ; by rewrite Hmerge.
      -- split; last by intros.
         intro H ; inversion H; subst.
         edestruct IHes as [Hres _].
         rewrite Hres => //.
      -- split; last by intros.
         intros H; inversion H; subst es'.
         edestruct IHes as [_ Hres].
         by erewrite Hres.
    + inversion Ha; subst.
      rewrite merge_suspend => //.
    + inversion Ha; subst.
      rewrite merge_switch => //.
    + destruct (merge_values_list (map _ l0)) eqn:Hmerge => //.
      destruct v0 => //; try (inversion Ha; subst v).
      * rewrite merge_br => //.
      * rewrite merge_return => //.
      * rewrite merge_call_host => //.
      * rewrite merge_suspend => //.
      * rewrite merge_switch => //.
      * destruct (exnelts_of_exception_clauses _ _) => //.
        inversion Ha; subst v.
        rewrite merge_throw => //.
    + destruct (merge_values_list (map _ l1)) eqn:Hmerge => //.
      destruct v0 => //; try (inversion Ha; subst v).
      * rewrite merge_br => //.
      * rewrite merge_return => //.
      * rewrite merge_call_host => //.
      * destruct (suselts_of_continuation_clauses _ _) => //.
        inversion Ha; subst.
        rewrite merge_suspend => //.
      * destruct (swelts_of_continuation_clauses _ _) => //.
        inversion Ha; subst.
        rewrite merge_switch => //.
      * rewrite merge_throw => //.
    + destruct (merge_values_list (map _ l0)) eqn:Hmerge => //.
      destruct v0 => //; try (inversion Ha; subst v).
      * destruct i => //.
        destruct (vh_decrease _) => //.
        inversion Ha; subst v.
        rewrite merge_br => //.
      * rewrite merge_return => //.
      * rewrite merge_call_host => //.
      * rewrite merge_suspend => //.
      * rewrite merge_switch => //.
      * rewrite merge_throw => //.
    + destruct (merge_values_list (map _ l)) eqn:Hmerge => //.
      destruct v0 => //; try (inversion Ha; subst v).
      * rewrite merge_call_host => //.
      * rewrite merge_suspend => //.
      * rewrite merge_switch => //.
      * rewrite merge_throw => //.
    + inversion Ha; subst v.
      rewrite merge_call_host => //. 
  - rewrite flatten_simplify.
    split; last done.
    intro H ; inversion H.
    destruct a => // ; try by inversion Ha. 
    + destruct b => // ; try by inversion Ha.
    + simpl in Ha.
      destruct (merge_values_list (map _ l0)) => // ; try by inversion Ha. 
      destruct v => // ; try by inversion Ha.
      destruct (exnelts_of_exception_clauses _ _) eqn:Hexnelts => //.
      inversion Ha; subst e. done.
    + simpl in Ha.
      destruct (merge_values_list (map _ l1)) => // ; try by inversion Ha. 
      destruct v => // ; try by inversion Ha.
      * destruct (suselts_of_continuation_clauses _ _) => //. 
        inversion Ha; subst e. done.
      * destruct (swelts_of_continuation_clauses _ _) => //.
        inversion Ha; subst e. done.
    + simpl in Ha.
      destruct (merge_values_list (map _ l0)) => // ; try by inversion Ha. 
      destruct v => // ; try by inversion Ha.
      destruct i => // ; try by inversion Ha.
      destruct (vh_decrease lh) ; try by inversion Ha.
    + simpl in Ha.
      destruct (merge_values_list (map _ l)) => // ; try by inversion Ha.
      destruct v => // ; by inversion Ha.
  - rewrite flatten_simplify.
    split; first done.
    intros H; inversion H; subst es'.
    destruct a => //.
    + destruct b => //.
      simpl in Ha. inversion Ha; subst.
      done.
    + simpl in Ha. destruct (merge_values_list (map _ l0)) => //.
      destruct v => //.
      destruct (exnelts_of_exception_clauses _ _) => //.
    + simpl in Ha.
      destruct (merge_values_list (map _ l1)) => //.
      destruct v => //.
      destruct (suselts_of_continuation_clauses _ _) => //.
      destruct (swelts_of_continuation_clauses _ _) => //.
    + simpl in Ha. destruct (merge_values_list (map _ l0)) => //.
      destruct v => //.
      destruct i => //.
      destruct (vh_decrease _ ) => //.
    + simpl in Ha. destruct (merge_values_list (map _ l)) => //.
      destruct v => //. 
Qed.

Lemma merge_is_not_val es es' :
  (merge_values_list (map to_val_instr es) = NotVal es' ->
   es = es') .
Proof.
  edestruct merge_is_not_val_is_throw_ref as [Hres _].
  exact Hres.
Qed.

Lemma merge_is_throw_ref es es' :
    (merge_values_list (map to_val_instr es) = ThrowRef es' ->
     es = AI_basic BI_throw_ref :: es').
Proof.
  edestruct merge_is_not_val_is_throw_ref as [_ Hres].
  exact Hres.
Qed. 

Lemma extend_retV sh es :
  to_val (of_val (retV sh) ++ es) = Some (retV (sh_append sh es)).
Proof.
  unfold to_val.
  rewrite map_app.
  rewrite merge_app.
  specialize (to_of_val (retV sh)) as H.
  unfold to_val in H.
  destruct (merge_values_list _) => //.
  inversion H => /=.
  destruct (merge_values_list _) eqn:Hmerge => //=.
  - erewrite of_to_val.
    done.
    unfold to_val.
    by rewrite Hmerge.
  - by apply merge_is_not_val in Hmerge ; subst.
  - by apply merge_is_throw_ref in Hmerge; subst.
Qed.


Lemma e_to_v_opt_is_Some a v:
  e_to_v_opt a = Some v ->
  to_val_instr a = Val (immV [v]).
Proof.
  destruct a => //=.
  destruct b => //=.
  all: intros H; inversion H; subst.
  all: done.
Qed. 

Lemma splits_vals_e_to_val_hd : forall e1 e es vs,
    split_vals_e e1 = (vs, e :: es) ->
    to_val e1 = None
    ∨ (vs = [] ∧ to_val e1 = Some trapV)
(*    \/ (vs = [] /\ e1 = AI_basic BI_throw_ref :: es)
    \/ (∃ vs' v, separate_last vs = Some (vs', v) /\ (forall a i, v <> VAL_ref (VAL_ref_exn a i)) /\ e1 = v_to_e_list vs ++ AI_basic BI_throw_ref :: es) *)
    ∨ (∃ i, e = AI_basic (BI_br i) ∧ to_val e1 = Some (brV (VH_base i vs es)))
    ∨ (e = AI_basic BI_return ∧ to_val e1 = Some (retV (SH_base vs es)))
    \/ (∃ tf h vcs, e = AI_call_host tf h vcs /\ to_val e1 = Some (callHostV tf h vcs ((LL_base vs es))))
    \/ (∃ i, e = AI_suspend_desugared i /\ to_val e1 = Some (susV i (SuBase vs es)))
    \/ (∃ tf i, e = AI_switch_desugared tf i /\ to_val e1 = Some (swV tf i (SwBase vs es)))
    \/ (∃ a i vs', e = AI_basic BI_throw_ref /\ separate_last vs = Some (vs', VAL_ref (VAL_ref_exn a i)) /\ to_val e1 = Some (thrV a i (ExBase vs' es)))
    \/ (∃ i n es' LI (vh : valid_holed i),
          e = AI_label n es' LI /\ to_val e1 = Some (brV (VH_rec vs n es' vh es))
          /\ vfill vh [AI_basic (BI_br (S i))] = LI)
    \/ (∃ n es' LI sh, e = AI_label n es' LI /\ to_val e1 = Some (retV (SH_rec vs n es' sh es))
                      /\ sfill sh [AI_basic BI_return] = LI)
    \/ (∃ tf h vcs n es' LI sh, e = AI_label n es' LI /\ to_val e1 = Some (callHostV tf h vcs ((LL_label vs n es' sh es)))
                               /\ llfill sh [AI_call_host tf h vcs] = LI)
    \/ (∃ i n es' LI sh,
          e = AI_label n es' LI /\ to_val e1 = Some (susV i (SuLabel vs n es' sh es)) /\
            susfill i sh [AI_suspend_desugared i] = LI)
    \/ (∃ tf i n es' LI sh,
          e = AI_label n es' LI /\ to_val e1 = Some (swV tf i (SwLabel vs n es' sh es)) /\
            swfill i sh [AI_switch_desugared tf i] = LI)
    \/ (∃ a i n es' LI sh,
          e = AI_label n es' LI /\ to_val e1 = Some (thrV a i (ExLabel vs n es' sh es)) /\
            exnfill i sh [AI_ref_exn a i ; AI_basic BI_throw_ref] = LI)
    \/ (∃ i es' LI (vh : valid_holed i),
          e = AI_handler es' LI /\ to_val e1 = Some (brV (VH_handler vs es' vh es))
          /\ vfill vh [AI_basic (BI_br i)] = LI)
    \/ (∃ es' LI sh, e = AI_handler es' LI /\ to_val e1 = Some (retV (SH_handler vs es' sh es))
                      /\ sfill sh [AI_basic BI_return] = LI)
    \/ (∃ tf h vcs es' LI sh, e = AI_handler es' LI /\ to_val e1 = Some (callHostV tf h vcs ((LL_handler vs es' sh es)))
                               /\ llfill sh [AI_call_host tf h vcs] = LI)
    \/ (∃ i es' LI sh,
          e = AI_handler es' LI /\ to_val e1 = Some (susV i (SuHandler vs es' sh es)) /\
            susfill i sh [AI_suspend_desugared i] = LI)
    \/ (∃ tf i es' LI sh,
          e = AI_handler es' LI /\ to_val e1 = Some (swV tf i (SwHandler vs es' sh es)) /\
            swfill i sh [AI_switch_desugared tf i] = LI)
    \/ (∃ a i es' LI sh,
          e = AI_handler (map (exception_clause_of_exnelt i) es') LI /\ to_val e1 = Some (thrV a i (ExHandler vs es' sh es)) /\
            exnfill i sh [AI_ref_exn a i ; AI_basic BI_throw_ref] = LI)
    \/ (∃ i n es' LI (vh : valid_holed i),
          e = AI_prompt n es' LI /\ to_val e1 = Some (brV (VH_prompt vs n es' vh es))
          /\ vfill vh [AI_basic (BI_br i)] = LI)
    \/ (∃ n es' LI sh, e = AI_prompt n es' LI /\ to_val e1 = Some (retV (SH_prompt vs n es' sh es))
                      /\ sfill sh [AI_basic BI_return] = LI)
    \/ (∃ tf h vcs n es' LI sh, e = AI_prompt n es' LI /\ to_val e1 = Some (callHostV tf h vcs ((LL_prompt vs n es' sh es)))
                               /\ llfill sh [AI_call_host tf h vcs] = LI)
    \/ (∃ i n es' LI sh,
          e = AI_prompt n (map (continuation_clause_of_suselt i) es') LI /\ to_val e1 = Some (susV i (SuPrompt vs n es' sh es)) /\
            susfill i sh [AI_suspend_desugared i] = LI)
    \/ (∃ tf i n es' LI sh,
          e = AI_prompt n (map (continuation_clause_of_swelt i) es') LI /\ to_val e1 = Some (swV tf i (SwPrompt vs n es' sh es)) /\
            swfill i sh [AI_switch_desugared tf i] = LI)
    \/ (∃ a i n es' LI sh,
          e = AI_prompt n es' LI /\ to_val e1 = Some (thrV a i (ExPrompt vs n es' sh es)) /\
            exnfill i sh [AI_ref_exn a i ; AI_basic BI_throw_ref] = LI)
    \/ (∃ tf h vcs n f LI sh, e = AI_local n f LI /\ to_val e1 = Some (callHostV tf h vcs ((LL_local vs n f sh es)))
                             /\ llfill sh [AI_call_host tf h vcs] = LI)
    \/ (∃ i n f LI sh, e = AI_local n f LI /\ to_val e1 = Some (susV i (SuLocal vs n f sh es)) /\ susfill i sh [AI_suspend_desugared i] = LI)
    \/ (∃ tf i n f LI sh, e = AI_local n f LI /\ to_val e1 = Some (swV tf i (SwLocal vs n f sh es)) /\ swfill i sh [AI_switch_desugared tf i] = LI)
    \/ (∃ a i n f LI sh, e = AI_local n f LI /\ to_val e1 = Some (thrV a i (ExLocal vs n f sh es)) /\ exnfill i sh [AI_ref_exn a i; AI_basic BI_throw_ref] = LI)
.
Proof.
  intros e1.
  induction e1 ; intros e es vs Hsplit.
  { destruct vs => //. } 
  destruct vs => //.
  { simpl in Hsplit.
    destruct a => // ; try by left.
    destruct b => // ; simplify_eq;try by left.
    all: try by destruct (split_vals_e e1); inversion Hsplit.
    all: try (inversion Hsplit; subst e es).
    - (* Br *)
      unfold to_val => /=.
      rewrite merge_br flatten_simplify.
      (* right. right. *) right. right. left. 
      eexists. eauto.
    - (* Return *)
      unfold to_val => /=.
      rewrite merge_return flatten_simplify.
      (* right. right. *) right. right. right. left.
      eauto.
    - (* Trap *)
      destruct e1.
      + right;left;auto.
      + left. 
        unfold to_val. simpl.
        destruct (expr_of_val_not_val _) eqn:Ha => //.
        rewrite of_to_val_instr in Ha.
        done.
    (*   - simpl.
      destruct (merge_values_list _) eqn:Hmerge => //.
      destruct v => //. *)
    - (* Suspend *)
      (* right. right. *) right. right. right. right. right. left.
      eexists. split => //=.
      unfold to_val => //=.
      rewrite merge_suspend => //=.
      rewrite flatten_simplify => //.
    - (* Switch *)
      (* right. right. *) right. right. right. right. right. right. left.
      repeat eexists. unfold to_val => /=.
      rewrite merge_switch flatten_simplify => //.
    - (* Handler *)
      destruct (to_val (_ :: _)) eqn:Htv ; try by left.
      right. right. right. right.
      right. right. right. right.
      right. right. right. right.
      right. right. (* right. right. *)
      unfold to_val in Htv => /=. 
      simpl in Htv.
      destruct (merge_values_list _) eqn:Hmerge => //.
      destruct v0 => //.
      + (* Br *)
        rewrite merge_br flatten_simplify in Htv.
        inversion Htv; subst.
        left. repeat eexists.
        fold (of_val (brV lh)).
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //.
      + (* Return *)
        rewrite merge_return flatten_simplify in Htv.
        inversion Htv; subst.
        right; left. repeat eexists.
        fold (of_val (retV s)).
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //. 
      + (* Call_host *)
        rewrite merge_call_host flatten_simplify in Htv.
        inversion Htv ; subst.
        right; right; left. repeat eexists.
        fold (of_val (callHostV f h l1 l2)).
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //.
      + (* Suspend *)
        rewrite merge_suspend flatten_simplify in Htv.
        inversion Htv; subst.
        right; right; right; left.
        repeat eexists.
        fold (of_val (susV i sh)).
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //.
      + (* Switch *)
        rewrite merge_switch flatten_simplify in Htv.
        inversion Htv; subst.
        right; right; right; right; left.
        repeat eexists.
        fold (of_val (swV tf i sh)).
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //.
      + (* Throw *)
        destruct (exnelts_of_exception_clauses _ _) eqn:Helts => //. 
        rewrite merge_throw flatten_simplify in Htv.
        inversion Htv; subst.
        right; right; right; right; right; left.
        repeat eexists.
        fold (of_val (thrV a i sh)).
        apply exnelts_of_exception_clauses_inj in Helts.
        rewrite Helts.
        f_equal.
        symmetry.
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //.
    - (* Prompt *)
      destruct (to_val (_ :: _)) eqn:Htv ; try by left.
      right. right. right. right.
      right. right. right. right.
      right. right. right. right.
      right. right. right. right.
      right. right. right. right.
(*      right. right. *)
      unfold to_val in Htv => /=. 
      simpl in Htv.
      destruct (merge_values_list _) eqn:Hmerge => //.
      destruct v0 => //.
      + (* Br *)
        rewrite merge_br flatten_simplify in Htv.
        inversion Htv; subst.
        left. repeat eexists.
        fold (of_val (brV lh)).
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //.
      + (* Return *)
        rewrite merge_return flatten_simplify in Htv.
        inversion Htv; subst.
        right; left. repeat eexists.
        fold (of_val (retV s)).
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //. 
      + (* Call_host *)
        rewrite merge_call_host flatten_simplify in Htv.
        inversion Htv ; subst.
        right; right; left. repeat eexists.
        fold (of_val (callHostV f h l2 l3)).
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //.
      + (* Suspend *)
        destruct (suselts_of_continuation_clauses _ _) eqn:Helts => //. 
        rewrite merge_suspend flatten_simplify in Htv.
        inversion Htv; subst.
        right; right; right; left.
        repeat eexists.
        fold (of_val (susV i sh)).
        apply suselts_of_continuation_clauses_inj in Helts.
        rewrite Helts.
        symmetry.
        f_equal.
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //.
      + (* Switch *)
        destruct (swelts_of_continuation_clauses _ _) eqn:Helts => //.
        rewrite merge_switch flatten_simplify in Htv.
        inversion Htv; subst.
        right; right; right; right; left.
        repeat eexists.
        fold (of_val (swV tf i sh)).
        apply swelts_of_continuation_clauses_inj in Helts.
        rewrite Helts.
        f_equal. symmetry.
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //.
      + (* Throw *)
        rewrite merge_throw flatten_simplify in Htv.
        inversion Htv; subst.
        right; right; right; right; right; left.
        repeat eexists.
        fold (of_val (thrV a i sh)).
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //.
    - (* Label *)
      destruct (to_val (_ :: _)) eqn:Htv ; try by left.
      right. right. right. right.
      right. right. right. right.
(*      right. right. *)
      unfold to_val in Htv => /=.
      simpl in Htv.
      destruct (merge_values_list _) eqn:Hmerge => //.
      destruct v0 => //.
      + (* Br *)
        destruct i => //.
        destruct (vh_decrease _) eqn:Hdecr => //.
        rewrite merge_br flatten_simplify in Htv.
        inversion Htv ; subst.
        left. repeat eexists _.
        repeat split => //.
        assert (to_val l0 = Some (brV lh)).
        unfold to_val ; by rewrite Hmerge.
        apply of_to_val in H.
        unfold of_val in H.
        rewrite - (vfill_decrease _ Hdecr) => //.
      + (* Return *)
        rewrite merge_return flatten_simplify in Htv.
        inversion Htv ; subst.
        right ; left. repeat eexists _.
        repeat split => //.
        assert (to_val l0 = Some (retV s)).
        unfold to_val ; by rewrite Hmerge.
        apply of_to_val in H.
        unfold of_val in H => //.
      + (* Call_host *)
        rewrite merge_call_host flatten_simplify in Htv.
        inversion Htv ; subst.
        right ; right. left. repeat eexists _.
        repeat split => //.
        assert (to_val l0 = Some (callHostV f h l1 l2)).
        unfold to_val ; by rewrite Hmerge.
        apply of_to_val in H.
        unfold of_val in H => //.
      + (* Suspend *)
        rewrite merge_suspend flatten_simplify in Htv.
        inversion Htv; subst.
        right; right; right; left.
        repeat eexists.
        assert (to_val l0 = Some (susV i sh)).
        unfold to_val; by rewrite Hmerge.
        apply of_to_val in H.
        unfold of_val in H => //.
      + (* Switch *)
        rewrite merge_switch flatten_simplify in Htv.
        inversion Htv; subst.
        right; right; right; right; left.
        repeat eexists.
        assert (to_val l0 = Some (swV tf i sh)).
        unfold to_val; by rewrite Hmerge.
        apply of_to_val in H.
        unfold of_val in H => //.
      + (* Throw *)
        rewrite merge_throw flatten_simplify in Htv.
        inversion Htv; subst.
        right; right; right; right; right; left.
        repeat eexists.
        assert (to_val l0 = Some (thrV a i sh)).
        unfold to_val; by rewrite Hmerge.
        apply of_to_val in H.
        unfold of_val in H => //. 
        
    - (* Local *)
      destruct (to_val (_ :: _)) eqn:Htv ; try by left.
      right. right. right. right.
      right. right. right. right.
      right. right. right. right.
      right. right. right. right.
      right. right. right. right.
      right. right. right. right.
      right. right. (* right. right. *)
      unfold to_val in Htv => /=. 
      simpl in Htv.
      destruct (merge_values_list _) eqn:Hmerge => //.
      destruct v0 => //.
      + (* Call_host *)
        rewrite merge_call_host flatten_simplify in Htv.
        inversion Htv ; subst.
        left. repeat eexists.
        fold (of_val (callHostV f0 h l0 l1)).
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //.
      + (* Suspend *)
        rewrite merge_suspend flatten_simplify in Htv.
        inversion Htv; subst.
        right; left.
        repeat eexists.
        fold (of_val (susV i sh)).
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //.
      + (* Switch *)
        rewrite merge_switch flatten_simplify in Htv.
        inversion Htv; subst.
        right; right; left.
        repeat eexists.
        fold (of_val (swV tf i sh)).
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //.
      + (* Throw *)
        rewrite merge_throw flatten_simplify in Htv.
        inversion Htv; subst.
        right; right; right.
        repeat eexists.
        fold (of_val (thrV a i sh)).
        apply of_to_val.
        unfold to_val.
        rewrite Hmerge => //.
    - unfold to_val => /=.
      rewrite merge_call_host flatten_simplify.
      inversion Hsplit.
      (* right. right. *) right. right. right. right. left. repeat eexists.
  }
  simpl in Hsplit.
  destruct (e_to_v_opt a) eqn:Ha => //.
  apply e_to_v_opt_is_Some in Ha.
(*  destruct a => //.
  destruct b => //.
  - *)
  destruct (split_vals_e e1) eqn:Hsome.
  assert ((l, l0) = (vs, (e :: es)%SEQ)) as Heq%IHe1.
  { inversion Hsplit; subst. auto. }
  destruct Heq as
      [?|
         [(? & ?)|
(*           [ (? & ?) |
             [ (? & ? & ? & ? & ?) | *)
           [(? & ? & ?)|
             [(? & ?) |
               [(?&?&?&?&?)|
                 [(?&?&?) |
                   [(? & ? & ? & ?)|
                     [(? & ? & ? & ? & ? & ?)|
                       [(?&?&?&?&?&?&?&?)|
                         [(?&?&?&?&?&?&?)|
                           [(?&?&?&?&?&?&?&?&?&?)|
                             [(? & ? & ? & ? & ? & ? & ? & ?) |
                               [(? & ? & ? & ? & ? & ? & ? & ? & ?) |
                                 [(? & ? & ? & ? & ? & ? & ? & ? & ?) |
                                   [(?&?&?&?&?&?&?)|
                                     [(?&?&?&?&?&?)|
                                       [(?&?&?&?&?&?&?&?&?)|
                                         [(? & ? & ? & ? & ? & ? & ?) |
                                           [(? & ? & ? & ? & ? & ? & ? & ?) |
                                             [(? & ? & ? & ? & ? & ? & ? & ?) |
                                               [(?&?&?&?&?&?&?&?)|
                                                 [(?&?&?&?&?&?&?)|
                                                   [(?&?&?&?&?&?&?&?&?&?)|
                                                     [(? & ? & ? & ? & ? & ? & ? & ?) |
                                                       [(? & ? & ? & ? & ? & ? & ? & ? & ?) |
                                                         [(? & ? & ? & ? & ? & ? & ? & ?) |
                                                           
                                                           [(?&?&?&?&?&?&?&?&?&?) |
                                                           [(? & ? & ? & ? & ? & ? & ? & ?)|
                                                             [(? & ? & ? & ? & ? & ? & ? & ? & ?)|
                                                               (? & ? & ? & ? & ? & ? & ? & ? & ?)
         ]]]]]]]]]]]]]]]]]]]]]]]]]]]]](* ]] *) ; 
      unfold to_val => /= ; rewrite Ha merge_prepend.
  + (* Not Val *)
    unfold to_val in H.
    destruct (merge_values_list _) eqn:Hmerge; try by left.
    destruct v0; try by left.
    destruct v0; try by left.
    simpl. inversion Hsplit; subst.
    (* right. right. *)
    right. right. right. right. right. right. right. left.
    apply merge_is_throw_ref in Hmerge as ->.
    simpl in Hsome.
    inversion Hsome; subst.
    repeat eexists.
  + (* Trap *)
    left. unfold to_val in H0.
    destruct (merge_values_list _) => //.
    by inversion H0. 
  + (* Br *)
    unfold to_val in H0.
    destruct (merge_values_list _) => //.
    inversion H0 => /=.
    right. right. left. eexists _.
    split => //=. inversion Hsplit ; subst => //. 
  + (* Return *)
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => /=. right. right. right. left.
      split;auto. by inversion Hsplit. 
    + (* Call_host *)
      unfold to_val in H0.
      destruct (merge_values_list _) => //.
      inversion H0 => /=.
      right. right. right. right. left. repeat eexists.
      by inversion Hsplit. by inversion Hsplit. 
    + (* Suspend *)
      unfold to_val in H0.
      destruct (merge_values_list _) => //.
      inversion H0 => /=.
      right. right. right. right. right. left. repeat eexists.
      by inversion Hsplit. by inversion Hsplit.
    + (* Switch *)
      unfold to_val in H0.
      destruct (merge_values_list _) => //.
      inversion H0 => /=.
      right; right; right; right; right; right; left.
      repeat eexists. by inversion Hsplit. by inversion Hsplit.
    + (* Throw *)
      unfold to_val in H1.
      destruct (merge_values_list _) => //.
      inversion H1 => /=.
      right; right; right; right; right; right; right; left.
      repeat eexists. done.
      rewrite H0.
      apply separate_last_spec in H0 as ->.
      destruct x1; by inversion Hsplit.
    + (* Label br *)
      unfold to_val in H0.
      destruct (merge_values_list _) => //.
      inversion H0 => /=.
      right. right. right. right. right. right; right; right; left.
      repeat eexists _. repeat split => //. by inversion Hsplit. 
    + (* Label return *)
      unfold to_val in H0.
      destruct (merge_values_list _) => //.
      inversion H0 => /=. do 9 right.
      left. repeat eexists _. repeat split => //.
      by inversion Hsplit.
      
    + (* Label call_host *)
      unfold to_val in H0.
      destruct (merge_values_list _) => //. 
      inversion H0 => /=. do 10 right. left.
      repeat eexists _. repeat split => //.
      by inversion Hsplit.
    + (* Label suspend *)
      unfold to_val in H0.
       destruct (merge_values_list _) => //. 
      inversion H0 => /=. do 11 right. left.
      repeat eexists _. repeat split => //.
      by inversion Hsplit.
    + (* Label switch *)
      unfold to_val in H0.
       destruct (merge_values_list _) => //. 
      inversion H0 => /=. do 12 right. left.
      repeat eexists _. repeat split => //.
      by inversion Hsplit.
    + (* Label throw *)
      unfold to_val in H0.
       destruct (merge_values_list _) => //. 
      inversion H0 => /=. do 13 right. left.
      repeat eexists _. repeat split => //.
      by inversion Hsplit.
    + (* Handler br *)
      unfold to_val in H0.
      destruct (merge_values_list _) => //.
      inversion H0 => /=.
      do 14 right; left.
      repeat eexists _.
      repeat split => //. by inversion Hsplit. 
    + (* Handler return *)
      unfold to_val in H0.
      destruct (merge_values_list _) => //.
      inversion H0 => /=. do 15 right.
      left. repeat eexists _. repeat split => //.
      by inversion Hsplit.
      
    + (* Handler call_host *)
      unfold to_val in H0.
      destruct (merge_values_list _) => //. 
      inversion H0 => /=. do 16 right. left.
      repeat eexists _. repeat split => //.
      by inversion Hsplit.
    + (* Handler suspend *)
      unfold to_val in H0.
       destruct (merge_values_list _) => //. 
      inversion H0 => /=. do 17 right. left.
      repeat eexists _. repeat split => //.
      by inversion Hsplit.
    + (* Handler switch *)
      unfold to_val in H0.
       destruct (merge_values_list _) => //. 
      inversion H0 => /=. do 18 right. left.
      repeat eexists _. repeat split => //.
      by inversion Hsplit.
    + (* Handler throw *)
      unfold to_val in H0.
       destruct (merge_values_list _) => //. 
      inversion H0 => /=. do 19 right. left.
      repeat eexists _. repeat split => //.
      by inversion Hsplit.
    + (* Prompt br *)
      unfold to_val in H0.
      destruct (merge_values_list _) => //.
      inversion H0 => /=.
      do 20 right; left.
      repeat eexists _.
      repeat split => //. by inversion Hsplit. 
    + (* Prompt return *)
      unfold to_val in H0.
      destruct (merge_values_list _) => //.
      inversion H0 => /=. do 21 right.
      left. repeat eexists _. repeat split => //.
      by inversion Hsplit.
      
    + (* Prompt call_host *)
      unfold to_val in H0.
      destruct (merge_values_list _) => //. 
      inversion H0 => /=. do 22 right. left.
      repeat eexists _. repeat split => //.
      by inversion Hsplit.
    + (* Prompt suspend *)
      unfold to_val in H0.
       destruct (merge_values_list _) => //. 
      inversion H0 => /=. do 23 right. left.
      repeat eexists _. repeat split => //.
      by inversion Hsplit.
    + (* Prompt switch *)
      unfold to_val in H0.
       destruct (merge_values_list _) => //. 
      inversion H0 => /=. do 24 right. left.
      repeat eexists _. repeat split => //.
      by inversion Hsplit.
    + (* Prompt throw *)
      destruct H0 as [H0 ?].
      unfold to_val in H0.
       destruct (merge_values_list _) => //. 
      inversion H0 => /=. do 25 right. left.
      repeat eexists _. repeat split => //.
      by inversion Hsplit.
      
      
    + (* Local return *)
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => /=. do 26 right. left.
      repeat eexists _. repeat split => //.
      by inversion Hsplit.
       + (* Local suspend *)
      unfold to_val in H0.
       destruct (merge_values_list _) => //. 
      inversion H0 => /=. do 27 right. left.
      repeat eexists _. repeat split => //.
      by inversion Hsplit.
    + (* Local switch *)
      unfold to_val in H0.
       destruct (merge_values_list _) => //. 
      inversion H0 => /=. do 28 right. left.
      repeat eexists _. repeat split => //.
      by inversion Hsplit.
    + (* Local throw *)
      unfold to_val in H0.
      destruct (merge_values_list _) => //. 
      inversion H0 => /=. do 29 right.
      repeat eexists _. repeat split => //.
      by inversion Hsplit.

Qed.

Lemma to_val_None_prepend: forall es1 es2,
    to_val es2 = None ->
    to_val (es1 ++ es2) = None
    ∨ (∃ i (vh : valid_holed i), to_val es1 = Some (brV vh))
    ∨ (∃ sh, to_val es1 = Some (retV sh))
    \/ (∃ tf h cvs sh, to_val es1 = Some (callHostV tf h cvs sh))
    \/ (∃ i sh, to_val es1 = Some (susV i sh))
    \/ (∃ tf i sh, to_val es1 = Some (swV tf i sh))
    \/ (∃ a i sh, to_val es1 = Some (thrV a i sh))
    \/ (∃ vs a i es, es1 = v_to_e_list (vs ++ [::VAL_ref (VAL_ref_exn a i)]) /\
                      es2 = AI_basic BI_throw_ref :: es)
.
Proof.
  move => es1 es2 H.
  induction es1;try by left.
  destruct a;try by left.
  destruct b; try by left.
  - right ; left.
    unfold to_val => /=.
    rewrite merge_br flatten_simplify.
    eauto.
  - right ; right.
    unfold to_val => /=.
    rewrite merge_return flatten_simplify.
    eauto.
  - destruct IHes1 as [?|[[?[??]]|[[??]|[(?&?&?&?&?) | [(?&?&?)|[(?&?&?&?)|[(?&?&?&?) | (?&?&?&?&?&?)]]]]]]].
    + simpl. unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //=.
      all: by left. 
    + right;left. eexists _, (vh_push_const _ _). unfold to_val => /=.
      rewrite merge_prepend. unfold to_val in H0.
      destruct (merge_values_list _) ; try done. inversion H0 => //=. 
    + right;right. left. unfold to_val => /=. rewrite merge_prepend.  unfold to_val in H0.
      destruct (merge_values_list _) => //.  inversion H0 => //=.
      by repeat eexists. 
    + right;right; right; left. unfold to_val => /=. rewrite merge_prepend. unfold to_val in H0.
      destruct (merge_values_list _) => //. inversion H0 => //=.  by repeat eexists.
    + right; right; right; right; left.
      unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right. left.
      unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right; right. left.
      unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => //=. by repeat eexists.
    + repeat right. subst. repeat eexists.
      instantiate (3:= VAL_num v :: _).
      simpl. done.
  - destruct IHes1 as [?|[[?[??]]|[[??]|[(?&?&?&?&?) | [(?&?&?)|[(?&?&?&?)|[(?&?&?&?) | (?&?&?&?&?&?)]]]]]]].
    + simpl. unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //=.
      all: by left. 
    + right;left. eexists _, (vh_push_const _ _). unfold to_val => /=.
      rewrite merge_prepend. unfold to_val in H0.
      destruct (merge_values_list _) ; try done. inversion H0 => //=. 
    + right;right. left. unfold to_val => /=. rewrite merge_prepend.  unfold to_val in H0.
      destruct (merge_values_list _) => //.  inversion H0 => //=.
      by repeat eexists. 
    + right;right; right; left. unfold to_val => /=. rewrite merge_prepend. unfold to_val in H0.
      destruct (merge_values_list _) => //. inversion H0 => //=.  by repeat eexists.
    + right; right; right; right; left.
      unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right. left.
      unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right; right. left.
      unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => //=. by repeat eexists.
    + repeat right. subst. repeat eexists.
      instantiate (3:= VAL_ref (VAL_ref_null r) :: _).
      simpl. done.      
  - unfold to_val => /=. rewrite merge_trap => /=. rewrite flatten_simplify.
    destruct (es1 ++ es2) eqn:Habs => //.
    apply app_eq_nil in Habs as [-> ->].
    destruct IHes1 as [Habs | [ (? & ? & Habs) | [ [ ? Habs ] | [(?&?&?&?& Habs) | [(?&?&Habs)|[(? &?&?&Habs)|[(?&?&?&Habs) | (?&?&?&?&?&Habs)]] ]]]]] ; by inversion Habs.
    by left.
  - destruct IHes1 as [?|[[?[??]]|[[??]|[(?&?&?&?&?) | [(?&?&?)|[(?&?&?&?)|[(?&?&?&?) | (?&?&?&?&?&?)]]]]]]].
    + simpl. unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //=.
      all: by left. 
    + right;left. eexists _, (vh_push_const _ _). unfold to_val => /=.
      rewrite merge_prepend. unfold to_val in H0.
      destruct (merge_values_list _) ; try done. inversion H0 => //=. 
    + right;right. left. unfold to_val => /=. rewrite merge_prepend.  unfold to_val in H0.
      destruct (merge_values_list _) => //.  inversion H0 => //=.
      by repeat eexists. 
    + right;right; right; left. unfold to_val => /=. rewrite merge_prepend. unfold to_val in H0.
      destruct (merge_values_list _) => //. inversion H0 => //=.  by repeat eexists.
    + right; right; right; right; left.
      unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right. left.
      unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right; right. left.
      unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => //=. by repeat eexists.
    + repeat right. subst. repeat eexists.
      instantiate (3:= VAL_ref (VAL_ref_func f) :: _).
      simpl. done.
  - destruct IHes1 as [?|[[?[??]]|[[??]|[(?&?&?&?&?) | [(?&?&?)|[(?&?&?&?)|[(?&?&?&?) | (?&?&?&?&?&?)]]]]]]].
    + simpl. unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) eqn:Hmerge => //=.
      all: try by left.
      apply merge_is_throw_ref in Hmerge.
      destruct es1.
      * repeat right.
        repeat eexists.
        instantiate (3 := [::]) => //.
        exact Hmerge.
      * inversion Hmerge; subst a e0.
        right; right; right; right; right; right. left.
        repeat eexists.
        simpl. rewrite merge_throw. done.
    + right;left. eexists _, (vh_push_const _ _). unfold to_val => /=.
      rewrite merge_prepend. unfold to_val in H0.
      destruct (merge_values_list _) ; try done. inversion H0 => //=. 
    + right;right. left. unfold to_val => /=. rewrite merge_prepend.  unfold to_val in H0.
      destruct (merge_values_list _) => //.  inversion H0 => //=.
      by repeat eexists. 
    + right;right; right; left. unfold to_val => /=. rewrite merge_prepend. unfold to_val in H0.
      destruct (merge_values_list _) => //. inversion H0 => //=.  by repeat eexists.
    + right; right; right; right; left.
      unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right. left.
      unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right; right. left.
      unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => //=. by repeat eexists.
    + repeat right. subst. repeat eexists.
      instantiate (3:= VAL_ref (VAL_ref_exn e t) :: _).
      simpl. done.
  - destruct IHes1 as [?|[[?[??]]|[[??]|[(?&?&?&?&?) | [(?&?&?)|[(?&?&?&?)|[(?&?&?&?) | (?&?&?&?&?&?)]]]]]]].
    + simpl. unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //=.
      all: by left. 
    + right;left. eexists _, (vh_push_const _ _). unfold to_val => /=.
      rewrite merge_prepend. unfold to_val in H0.
      destruct (merge_values_list _) ; try done. inversion H0 => //=. 
    + right;right. left. unfold to_val => /=. rewrite merge_prepend.  unfold to_val in H0.
      destruct (merge_values_list _) => //.  inversion H0 => //=.
      by repeat eexists. 
    + right;right; right; left. unfold to_val => /=. rewrite merge_prepend. unfold to_val in H0.
      destruct (merge_values_list _) => //. inversion H0 => //=.  by repeat eexists.
    + right; right; right; right; left.
      unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right. left.
      unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right; right. left.
      unfold to_val => /=. rewrite merge_prepend.
      unfold to_val in H0. destruct (merge_values_list _) => //.
      inversion H0 => //=. by repeat eexists.
    + repeat right. subst. repeat eexists.
      instantiate (3:= VAL_ref (VAL_ref_cont f) :: _).
      simpl. done.
  - right; right; right; right; left.
    unfold to_val => /=. rewrite merge_suspend.
    repeat eexists.
  - right; right; right; right; right; left.
    unfold to_val => /=. rewrite merge_switch.
    repeat eexists.
  - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hmerge => // ; try by left.
    destruct v => // ; try by left.
    + right ; left.
      rewrite merge_br flatten_simplify.
      by repeat eexists.
    + right ; right. left.
      rewrite merge_return flatten_simplify.
      by eexists.
    + right ; right ; right; left.
      rewrite merge_call_host flatten_simplify.
      by repeat eexists.
    + right; right; right; right; left.
      rewrite merge_suspend flatten_simplify.
      by repeat eexists.
    + right; right; right; right; right; left.
      rewrite merge_switch flatten_simplify.
      by repeat eexists.
    + destruct (exnelts_of_exception_clauses _ _) eqn:Helts.
      * right; right; right; right; right; right; left.
        rewrite merge_throw flatten_simplify.
        by repeat eexists.
      * by left.
  - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hmerge => // ; try by left.
    destruct v => // ; try by left.
    + right ; left.
      rewrite merge_br flatten_simplify.
      by repeat eexists.
    + right ; right. left.
      rewrite merge_return flatten_simplify.
      by eexists.
    + right ; right ; right; left.
      rewrite merge_call_host flatten_simplify.
      by repeat eexists.
    + destruct (suselts_of_continuation_clauses _ _) ; last by left.
      right; right; right; right; left.
      rewrite merge_suspend flatten_simplify.
      by repeat eexists.
    + destruct (swelts_of_continuation_clauses _ _); last by left.
      right; right; right; right; right; left.
      rewrite merge_switch flatten_simplify.
      by repeat eexists.
    + right; right; right; right; right; right; left.
      rewrite merge_throw flatten_simplify.
      by repeat eexists.
  - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hmerge => // ; try by left.
    destruct v => // ; try by left.
    + destruct i => // ; try by left.
      destruct (vh_decrease _) ; try by left.
      right ; left.
      rewrite merge_br flatten_simplify.
      by repeat eexists.
    + right ; right. left.
      rewrite merge_return flatten_simplify.
      by eexists.
    + right ; right ; right; left.
      rewrite merge_call_host flatten_simplify.
      by repeat eexists.
    + right; right; right; right; left.
      rewrite merge_suspend flatten_simplify.
      by repeat eexists.
    + right; right; right; right; right; left.
      rewrite merge_switch flatten_simplify.
      by repeat eexists.
    + right; right; right; right; right; right; left.
      rewrite merge_throw flatten_simplify.
      by repeat eexists.
  - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hl ; try by left.
    destruct v ; try by left.
    + do 3 right ; left; repeat eexists.
      rewrite merge_call_host flatten_simplify.
      done.
    + do 4 right; left; repeat eexists.
      by rewrite merge_suspend flatten_simplify.
    + do 5 right; left; repeat eexists.
      by rewrite merge_switch flatten_simplify.
    + do 6 right; left; repeat eexists.
      by rewrite merge_throw flatten_simplify.
  - unfold to_val => /=.
    do 3 right ; left; repeat eexists.
    rewrite merge_call_host flatten_simplify.
    done.
Qed.

Lemma to_val_None_prepend_const : forall es1 es2,
    const_list es1 ->
    to_val es2 = None ->
    to_val (es1 ++ es2) = None \/ (* This second disjunct shouldn't exist in order to instantiate Iris *)
      ∃ vs a i es, es1 = v_to_e_list (vs ++ [::VAL_ref (VAL_ref_exn a i)]) /\ es2 = AI_basic BI_throw_ref :: es.
Proof.
  move => es1 es2 H H'.
  eapply to_val_None_prepend in H' as [ ? | [(i & vh & Hes1) | [[sh Hes1] | [(?&?&?&sh&Hes1) | [(?&sh&Hes1) | [(?&?&sh & Hes1) |[ (?&?&sh & Hes1) | (?&?&?&?&Hes1&Hes2)]]]]]]] ; first by left.
  - exfalso.
    generalize dependent i. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    all: unfold to_val in Hes1 ; simpl in Hes1.
    all: rewrite merge_prepend in Hes1.
    all: destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v0 => //.
    2-5: destruct v => //. 
    all: apply (IHes1 H i0 lh) => //.
    all: unfold to_val.
    all: by rewrite Hmerge.
  - exfalso.
    generalize dependent sh. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    all: unfold to_val in Hes1 ; simpl in Hes1.
    all: rewrite merge_prepend in Hes1.
    all: destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v0 => //.
    2-5: destruct v => //.
    all: apply (IHes1 H s) => //.
    all: unfold to_val.
    all: by rewrite Hmerge.
  - exfalso.
    generalize dependent sh. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    all: unfold to_val in Hes1 ; simpl in Hes1.
    all: rewrite merge_prepend in Hes1.
    all: destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v0 => //.
    2-5: destruct v => //.
    all: inversion Hes1; subst.
    all: apply (IHes1 H l0) => //.
    all: unfold to_val.
    all: by rewrite Hmerge.
  - exfalso.
    generalize dependent sh. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    all: unfold to_val in Hes1 ; simpl in Hes1.
    all: rewrite merge_prepend in Hes1.
    all: destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v0 => //.
    2-5: destruct v => //.
    all: inversion Hes1; subst.
    all: apply (IHes1 H sh0) => //.
    all: unfold to_val.
    all: by rewrite Hmerge.
  - exfalso.
    generalize dependent sh. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    all: unfold to_val in Hes1 ; simpl in Hes1.
    all: rewrite merge_prepend in Hes1.
    all: destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v0 => //.
    2-5: destruct v => //.
    all: inversion Hes1; subst.
    all: apply (IHes1 H sh0) => //.
    all: unfold to_val.
    all: by rewrite Hmerge.
  - exfalso.
    generalize dependent sh. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    all: unfold to_val in Hes1 ; simpl in Hes1.
    all: rewrite merge_prepend in Hes1.
    all: destruct (merge_values_list _) eqn:Hmerge => //.
    5:{ apply merge_is_throw_ref in Hmerge as ->.
        simpl in H. done. } 
    destruct v0 => //.
    2-5: destruct v => //.
    all: inversion Hes1; subst.
    all: apply (IHes1 H sh0) => //.
    all: unfold to_val.
    all: by rewrite Hmerge.
  - subst. right.
    repeat eexists.
Qed.

Lemma to_val_None_append: forall es1 es2,
    to_val es1 = None ->
    to_val (es1 ++ es2) = None.
Proof.
  move => es1 es2.
  induction es1 => //=.
  destruct a => //=.
  destruct b => //= ; unfold to_val => /=.
  - by rewrite merge_br flatten_simplify.
  - by rewrite merge_return flatten_simplify.
  - rewrite merge_prepend.
    unfold to_val in IHes1.
    destruct (merge_values_list _) eqn:Hmerge => //=.
    + destruct v0 => //=.
      assert (to_val es1 = Some trapV) ; first by unfold to_val ; rewrite Hmerge.
      apply to_val_trap_is_singleton in H as -> => //=.
    + rewrite merge_prepend.
      destruct (merge_values_list (map to_val_instr (es1 ++ es2)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
    + rewrite merge_prepend.
      destruct (merge_values_list (map _ (es1 ++ es2)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
  - rewrite merge_prepend.
    unfold to_val in IHes1.
    destruct (merge_values_list _) eqn:Hmerge => //=.
    + destruct v => //=.
      assert (to_val es1 = Some trapV) ; first by unfold to_val ; rewrite Hmerge.
      apply to_val_trap_is_singleton in H as -> => //=.
    + rewrite merge_prepend.
      destruct (merge_values_list (map to_val_instr (es1 ++ es2)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
    + rewrite merge_prepend.
      destruct (merge_values_list (map _ (es1 ++ es2)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
  - unfold to_val => /=.
    rewrite merge_trap => /=.
    rewrite flatten_simplify.
    destruct es1 => //=.
    rewrite of_to_val_instr => //.
  - unfold to_val => /=. rewrite merge_prepend.
    unfold to_val in IHes1.
    destruct (merge_values_list _) eqn:Hmerge => //=.
    + destruct v => //=.
      assert (to_val es1 = Some trapV) ; first by unfold to_val ; rewrite Hmerge.
      apply to_val_trap_is_singleton in H as -> => //=.
    + rewrite merge_prepend.
      destruct (merge_values_list (map to_val_instr (es1 ++ es2)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
    + rewrite merge_prepend.
      destruct (merge_values_list (map _ (es1 ++ es2)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
  - unfold to_val => /=. rewrite merge_prepend.
    unfold to_val in IHes1.
    destruct (merge_values_list _) eqn:Hmerge => //=.
    + destruct v => //=.
      assert (to_val es1 = Some trapV) ; first by unfold to_val ; rewrite Hmerge.
      apply to_val_trap_is_singleton in H as -> => //=.
    + rewrite merge_prepend.
      destruct (merge_values_list (map to_val_instr (es1 ++ es2)%list)) eqn:Hmerge' => //=.
      * by specialize (IHes1 Logic.eq_refl).
      * apply merge_is_throw_ref in Hmerge'.
        destruct es1 => //.
        inversion Hmerge'; subst.
        simpl in Hmerge. done.
  - unfold to_val => /=. rewrite merge_prepend.
    unfold to_val in IHes1.
    destruct (merge_values_list _) eqn:Hmerge => //=.
    + destruct v => //=.
      assert (to_val es1 = Some trapV) ; first by unfold to_val ; rewrite Hmerge.
      apply to_val_trap_is_singleton in H as -> => //=.
    + rewrite merge_prepend.
      destruct (merge_values_list (map to_val_instr (es1 ++ es2)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
    + rewrite merge_prepend.
      destruct (merge_values_list (map _ (es1 ++ es2)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
  - unfold to_val => //=.
    rewrite merge_suspend => //=.
  - rewrite /to_val /= merge_switch => //.
  - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v => //.
    + rewrite merge_br => //.
    + rewrite merge_return => //.
    + rewrite merge_call_host => //.
    + rewrite merge_suspend => //.
    + rewrite merge_switch => //.
    + destruct (exnelts_of_exception_clauses _ _) => //. 
      rewrite merge_throw => //.
        - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v => //.
    + rewrite merge_br => //.
    + rewrite merge_return => //.
    + rewrite merge_call_host => //.
    + destruct (suselts_of_continuation_clauses _ _) => //. 
      rewrite merge_suspend => //.
    + destruct (swelts_of_continuation_clauses _ _) => //. 
      rewrite merge_switch => //.
    + rewrite merge_throw => //. 
  - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v => //.
    + destruct i => //.
      destruct (vh_decrease _) eqn:Hdecr => //.
      rewrite merge_br => //.
    + rewrite merge_return => //.
    + rewrite merge_call_host => //.
    + rewrite merge_suspend => //.
    + rewrite merge_switch => //.
    + rewrite merge_throw => //. 
  - unfold to_val => /=.
    destruct (merge_values_list _) => //.
    destruct v => //.
    + rewrite merge_call_host => //.
    + rewrite merge_suspend => //.
    + rewrite merge_switch => //.
    + rewrite merge_throw => //. 
  - unfold to_val => /=. by rewrite merge_call_host flatten_simplify.
Qed.

Lemma to_val_not_trap_interweave : ∀ es es',
    const_list es -> es != [] ∨ es' != [] -> to_val (es ++ [AI_trap] ++ es')%SEQ = None.
Proof.
  intros es.
  induction es;intros es1 Hconst [Hnil | Hnil];try done.
  - destruct es1 => //=. unfold to_val => /=. rewrite of_to_val_instr => //. 
  - simpl in Hconst. apply andb_true_iff in Hconst as [Ha Hconst].
    destruct a => //.
    destruct b => //.
    all: simpl.
    all: unfold to_val => /=.
    all: rewrite merge_prepend.
    all: destruct (merge_values_list _) eqn:Hmerge => //.
    all: destruct es,es1 ; first simpl in Hmerge;
        [ inversion Hmerge => //
        |  assert (to_val ([] ++ [AI_trap] ++ s :: es1) = None);
           first (by apply IHes => //=; right);
           unfold to_val in H; 
           rewrite Hmerge in H => //
        |  assert (to_val ((a :: es) ++ [AI_trap] ++ []) = None);
           first (by apply IHes => //=; left);
           rewrite app_nil_r in H;
           unfold to_val in H;
           rewrite Hmerge in H => //
        | assert (to_val (a :: es ++ [AI_trap] ++ s :: es1) = None);
          first (by apply IHes => //=; right);
          unfold to_val in H;
          rewrite Hmerge in H => //].
    all: apply merge_is_throw_ref in Hmerge => //.
    all: inversion Hmerge; subst; simpl in Hconst => //. 
    
  - simpl in Hconst. apply andb_true_iff in Hconst as [Ha Hconst].
    destruct a => //.
    destruct b => //.
    all: simpl.
    all: unfold to_val => /=.
    all: rewrite merge_prepend.
    all: destruct (merge_values_list _) eqn:Hmerge => //.
    all: destruct es,es1 ; first simpl in Hmerge;
      [ inversion Hmerge => //
      | assert (to_val ([] ++ [AI_trap] ++ s :: es1) = None);
        first (by apply IHes => //=; right);
        unfold to_val in H;
        rewrite Hmerge in H => //
      | assert (to_val ((a :: es) ++ [AI_trap] ++ []) = None);
        first (by apply IHes => //=);
        rewrite app_nil_r in H;
        unfold to_val in H;
        rewrite Hmerge in H => //
      | assert (to_val (a :: es ++ [AI_trap] ++ s :: es1) = None);
        first (by apply IHes => //=; right);
        unfold to_val in H;
        rewrite Hmerge in H => //].
    all: apply merge_is_throw_ref in Hmerge => //.
    inversion Hmerge; subst; simpl in Hconst => //. 
  Qed.

Lemma const_list_to_val es :
  const_list es -> exists vs, to_val es = Some (immV vs).
Proof.
  induction es => //= ; intros.
  by eexists [].
  destruct a => //=.
  destruct b => //=.
  all: unfold to_val => /=.
  all: rewrite merge_prepend.
  all: apply IHes in H as [vs Htv].
  all: unfold to_val in Htv.
  all: destruct (merge_values_list _) => //=.
  all: inversion Htv => //=.
  all: by eexists.
Qed.

Lemma to_val_const_list: forall es vs,
  to_val es = Some (immV vs) ->
  const_list es.
Proof.
  move => es. 
  elim: es => [|e es'] //=.
  move => IH vs.
  destruct e => //=.
  destruct b => //= ; unfold to_val => /=. 
  - rewrite merge_br flatten_simplify => //.
  - rewrite merge_return flatten_simplify => //.
  - rewrite merge_prepend.
    unfold to_val in IH.
    destruct (merge_values_list _) => //.
    destruct v0 => //=.
    intro H ; inversion H ; subst.
    by eapply IH.
  - rewrite merge_prepend.
    unfold to_val in IH.
    destruct (merge_values_list _) => //.
    destruct v => //=.
    intro H ; inversion H ; subst.
    by eapply IH.
  - unfold to_val => /=.
    rewrite merge_trap flatten_simplify => /=.
    destruct es' => //=.
  - rewrite /to_val /= merge_prepend.
    unfold to_val in IH.
    destruct (merge_values_list _) => //.
    destruct v => //=.
    intro H ; inversion H ; subst.
    by eapply IH.
  - rewrite /to_val /= merge_prepend.
    unfold to_val in IH.
    destruct (merge_values_list _) => //.
    destruct v => //=.
    intro H ; inversion H ; subst.
    by eapply IH.
  - rewrite /to_val /= merge_prepend.
    unfold to_val in IH.
    destruct (merge_values_list _) => //.
    destruct v => //=.
    intro H ; inversion H ; subst.
    by eapply IH.
  - rewrite /to_val /= merge_suspend => //.
  - rewrite /to_val /= merge_switch => //.
  - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v => //.
    + rewrite merge_br => //.
    + rewrite merge_return => //.
    + rewrite merge_call_host => //.
    + rewrite merge_suspend => //.
    + rewrite merge_switch => //.
    + destruct (exnelts_of_exception_clauses _ _) => //. 
      rewrite merge_throw => //.
  - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v => //.
    + rewrite merge_br => //.
    + rewrite merge_return => //.
    + rewrite merge_call_host => //.
    + destruct (suselts_of_continuation_clauses _ _) => //. 
      rewrite merge_suspend => //.
    + destruct (swelts_of_continuation_clauses _ _) => //. 
      rewrite merge_switch => //.
    + rewrite merge_throw => //.
  - unfold to_val => /=.
    destruct (merge_values_list _) eqn:Hmerge => //.
    destruct v => //.
    + destruct i => //.
      destruct (vh_decrease lh) => //.
      rewrite merge_br => //.
    + rewrite merge_return => //.
    + rewrite merge_call_host => //.
    + rewrite merge_suspend => //.
    + rewrite merge_switch => //.
    + rewrite merge_throw => //.
  - unfold to_val => /=.
    destruct (merge_values_list _) => //.
    destruct v => //.
    + rewrite merge_call_host => //.
    + rewrite merge_suspend => //.
    + rewrite merge_switch => //.
    + rewrite merge_throw => //. 
  - unfold to_val => /= ; by rewrite merge_call_host.
Qed.

(*
Lemma val_head_stuck_reduce : ∀ locs1 s1 e1 locs2 s2 e2,
    reduce locs1 s1 e1 locs2 s2 e2 ->
    to_val e1 = None.
Proof.
  move => locs1 s1 e1 locs2 s2 e2 HRed;try by to_val_None_prepend_const.
  induction HRed => //= ; subst; try by to_val_None_prepend_const.
  - inversion H; subst => //= ;try by apply to_val_None_prepend_const;auto.
    + destruct ref => //=.
    + (* proof breaks here: ref-null and switch-desugared reduces *) 
    + unfold to_val => /=.
      apply const_list_to_val in H0 as [vs Htv].
      unfold to_val in Htv.
      destruct (merge_values_list _) => //.
      inversion Htv => //.
    + unfold to_val => /=.
      destruct (merge_values_list _) eqn:Hmerge => //.
      destruct v => //.
      destruct i0 => //.
      destruct (vh_decrease lh0) eqn:Hdecr => //.
      assert (to_val LI = Some (brV lh0)) ; first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H1.
      unfold of_val in H1.
      rewrite (vfill_decrease _ Hdecr) in H1.
      destruct (vfill_to_lfilled v [AI_basic (BI_br (S i0))]) as (Hk & Hfill).
      rewrite H1 in Hfill.
      edestruct lfilled_first_values as (Habs1 & Habs2 & _).
      exact H2.
      rewrite - (app_nil_l [_]) in Hfill.
      rewrite - cat_app in Hfill.
      exact Hfill.
      all : try done.
      inversion Habs1.
      subst.
      lia.
      assert (to_val LI = Some (retV s0)) ; first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H1. unfold of_val in H1. 
      specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfill.
      rewrite H1 in Hfill.
      edestruct lfilled_first_values as (Habs & _ & _).
      exact H2.
      rewrite - (app_nil_l [_]) in Hfill.
      rewrite - cat_app in Hfill.
      exact Hfill.
      all : try done.
      assert (to_val LI = Some (callHostV f0 h l l0)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H1. unfold of_val in H1.
      edestruct lfilled_llfill_first_values as [Habs _].
      exact H2.
      rewrite - (cat0s [_]) in H1.
      exact H1.
      all : try done.
    + unfold to_val => /=.
      apply const_list_to_val in H0 as [vs Htv].
      unfold to_val in Htv.
      destruct (merge_values_list _) => //.
      inversion Htv => //.
    + unfold to_val => /=.
      destruct (merge_values_list _) eqn:Hmerge => //.
      destruct v => //.
      assert (to_val es = Some (callHostV f1 h l l0)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H1. unfold of_val in H1.
      edestruct lfilled_llfill_first_values as [Habs _].
      exact H2.
      rewrite - (cat0s [_]) in H1.
      exact H1.
      all : try done.
    + destruct v => //.
      by destruct b => //=.
    + move/lfilledP in H1.
      inversion H1. subst es e.
      apply to_val_not_trap_interweave;auto.
      case: vs {H H1 H2 H4} H0 => //=.
      case: es' => //=.
      move => a l H. by right.
      move => a l H. by left.
  - apply to_val_None_prepend_const;auto.
    apply v_to_e_is_const_list.
  - apply to_val_None_prepend_const ; auto.
    apply v_to_e_is_const_list.
  - destruct k, lh ; unfold lfilled, lfill in H ; fold lfill in H => //.
    + destruct (const_list l) eqn:Hl => //.
      apply b2p in H ; subst.
      apply to_val_None_prepend_const, to_val_None_append => //.
    + destruct (const_list l) eqn:Hl => //.
      destruct (lfill _ _ _) eqn:Hfill => //.
      apply b2p in H ; subst.
      generalize dependent les'.
      induction l ; intros ;  unfold to_val => /=.
      * destruct (merge_values_list _) eqn:Hmerge => //.
        destruct v => //.
        -- destruct i => //.
           destruct (vh_decrease lh0) eqn:Hdecr => //.
           exfalso.
           assert (to_val l2 = Some (brV lh0)) ; first by unfold to_val ; rewrite Hmerge.
           apply of_to_val in H.
           unfold of_val in H.
           destruct (vfill_to_lfilled lh0 [AI_basic (BI_br (S i))]) as (Hk & Hfilled).
           rewrite H in Hfilled.
           assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
           rewrite - (app_nil_l [_]) in Hfilled.
           rewrite - cat_app in Hfilled.
           eapply lfilled_br_and_reduce ; first (exact HRed) ; (try exact Hfilled) => //=.
        -- exfalso.
           assert (to_val l2 = Some (retV s0)) ; first by unfold to_val ; rewrite Hmerge.
           apply of_to_val in H. unfold of_val in H.
           specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfilled.
           rewrite H in Hfilled.
           assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
           rewrite - (app_nil_l [_]) in Hfilled.
           rewrite - cat_app in Hfilled.
           eapply lfilled_return_and_reduce ; first (exact HRed) ;
             (try exact Hfilled) => //=.
        -- exfalso.
           assert (to_val l2 = Some (callHostV f0 h l l3)) ;
             first by unfold to_val ; rewrite Hmerge.
           apply of_to_val in H. unfold of_val in H.
           assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
           destruct (lfilled_implies_llfill H1) as [llh Hfilled].
           eapply llfill_call_host_and_reduce ; first (exact HRed) ; (try exact Hfilled) => //=.
      * destruct a => //.
        destruct b => //=.
        rewrite merge_prepend.
        unfold lfilled, lfill in H0 ; fold lfill in H0.
        rewrite Hl in H0.
        destruct (lfill _ _ es') eqn:Hfill' => //.
        apply b2p in H0.
        destruct les' => //.
        assert (lfilled (S k) (LH_rec l n l0 lh l1) es' les').
        unfold lfilled, lfill ; fold lfill.
        apply andb_true_iff in Hl as [? Hl]. unfold const_list, forallb ; rewrite Hl.
        rewrite Hfill'. by inversion H0.
        apply IHl in H => //.
        unfold to_val in H.
        destruct (merge_values_list _) => //.
      * unfold to_val => /=.
        unfold to_val in IHHRed.
        destruct (merge_values_list _) => //.
Qed.

Lemma val_head_stuck : forall e1 s1 κ e2 s2 efs,
  prim_step e1 s1 κ e2 s2 efs →
  to_val e1 = None.
Proof.
  rewrite /prim_step => e1 [[locs1 σ1] inst] κ e2 [[ locs2 σ2] inst'] efs.
  move => [HRed _].
  eapply val_head_stuck_reduce;eauto.
Qed.

Lemma wasm_mixin : LanguageMixin of_val to_val prim_step.
Proof. split; eauto using to_of_val, of_to_val, val_head_stuck. Qed.

Definition wasm_lang := Language wasm_mixin.
*)
