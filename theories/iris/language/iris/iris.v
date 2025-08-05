From mathcomp Require Import ssreflect ssrbool eqtype seq.
From iris.program_logic Require Import language.
From Coq Require Import Eqdep_dec.
From Wasm.iris.helpers Require Export lfill_prelude.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Definition expr0 := list administrative_instruction.

(* A value can be an immediate, a trap, a [br i] if it is in a context shallow enough,
   i.e. a [valid_holed i] ; or a return, in any context. *)
(* We use VH and SH instead of LH so that the fill operations are always total functions *)
Inductive val0 : Type :=
| immV : (list value) -> val0
| trapV : val0
| brV (i : nat) (lh : valid_holed i) : val0
| retV : simple_valid_holed -> val0
| callHostV : function_type -> hostfuncidx -> seq.seq value -> llholed -> val0
.


Inductive eff0 : Type :=
| susE (vs: list value) (i : tagidx) (sh: susholed) : eff0
| swE (vs: list value) (k: funcaddr) (tf: function_type) (i : tagidx) (sh: swholed) : eff0
| thrE (vs : list value) (a : immediate) (i: tagidx) (sh: exnholed) : eff0
.

Definition val0_eq_dec : forall v1 v2: val0, {v1 = v2} + {v1 <> v2}.
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
Defined.

Definition eff_eq_dec: forall e1 e2: eff0, {e1 = e2} + {e1 <> e2}.
Proof.
  intros e1 e2; destruct e1,e2; auto.
  - destruct ( (vs == vs0) &&  (i == i0)) eqn:Hi.
    + remove_bools_options; subst. 
      destruct (susholed_eq_dec sh sh0).
      * subst. by left.
      * right. intros Habs; inversion Habs.
        done.
    + right. intros Habs; inversion Habs. subst.
      repeat rewrite eq_refl in Hi => //.
  - destruct ((vs == vs0) && (k == k0) && (tf == tf0) && (i == i0)) eqn:H.
    + remove_bools_options; subst. destruct (swholed_eq_dec sh sh0).
      * subst. by left.
      * right. intros Habs; inversion Habs.
        done.
    + right. intros Habs; inversion Habs. subst.
      repeat rewrite eq_refl in H => //.
  - destruct ((vs == vs0) && (a == a0) && (i == i0)) eqn:H.
    + remove_bools_options; subst i0 a0. destruct (exnholed_eq_dec sh sh0).
      * subst. by left.
      * right. intros Habs; inversion Habs.
        done.
    + right. intros Habs; inversion Habs. subst.
      repeat rewrite eq_refl in H => //. 
Defined.

Definition val0_eqb (v1 v2: val0) : bool := val0_eq_dec v1 v2.
Definition eqval0P : Equality.axiom val0_eqb :=
  eq_dec_Equality_axiom val0_eq_dec.

Canonical Structure val0_eqMixin := Equality.Mixin eqval0P.
Canonical Structure val0_eqType := Eval hnf in Equality.Pack (sort := val0) (Equality.Class val0_eqMixin).

Definition state : Type := store_record (* * (list value) * instance *).

Definition observation := unit.

Definition of_val0 (v : val0) : expr0 :=
  match v with
  | immV l => v_to_e_list l
  | trapV => [::AI_trap]
  | brV i vh => vfill vh [AI_basic (BI_br i)]
  | retV sh => sfill sh [AI_basic BI_return]
  | callHostV tf h vcs sh => llfill sh [AI_call_host tf h vcs]
  end. 

Definition of_eff0 (e : eff0) : expr0 :=
  match e with 
  | susE vs i sh => susfill i sh [AI_suspend_desugared vs i]
  | swE vs k tf i sh => swfill i sh [AI_switch_desugared vs k tf i]
  | thrE vs a i sh => exnfill i sh [AI_throw_ref_desugared vs a i]
  end.

Lemma of_val_imm (vs : list value) :
  v_to_e_list vs = of_val0 (immV vs).
Proof. done. Qed.

(* The following operation mirrors the opsem of AI_trap *)
(* in which a trap value swallows all other stack values *)
(* and the opsem of br and return, which skips over all subsequent expressions *)
(*
Definition val_combine (v1 v2 : val) :=
  match v1 with
  | immV l => match v2 with
             | immV l' => immV (l ++ l')
             | trapV => trapV
             | brV i vh => brV (vh_push_const vh l)
             | retV lh => retV (sh_push_const lh l)
             | callHostV tf h cvs sh => callHostV tf h cvs (llh_push_const sh l)
(*             | susV i sh => susV i (sus_push_const sh l)
             | swV tf i sh => swV tf i (sw_push_const sh l)
             | thrV a i sh => thrV a i (exn_push_const sh l) *)
             end
  | trapV => trapV
  | brV i vh => brV (vh_append vh (of_val v2))
  | retV lh => retV (sh_append lh (of_val v2))
  | callHostV tf h vcs sh => callHostV tf h vcs (llh_append sh (of_val v2))
(*  | susV i sh => susV i (sus_append sh (of_val v2))
  | swV tf i sh => swV tf i (sw_append sh (of_val v2))
  | thrV a i sh => thrV a i (exn_append sh (of_val v2)) *)
  end.
*)

(* Intuitively, when writing [NotVal e], we intend to mean e is not a value.
   This is however not enforced by the syntax *)
Inductive ValNotVal :=
  Val : val0 -> ValNotVal
| Eff : eff0 -> ValNotVal
| NotVal : expr0 -> ValNotVal
.

Definition expr_of_val_not_val x :=
  match x with
  | Val v => of_val0 v
  | Eff e => of_eff0 e
  | NotVal e => e
(*  | ThrowRef es => AI_basic BI_throw_ref :: es
(*  | Suspend i es => AI_suspend_desugared i :: es *)
  | Switch tf i es => AI_switch_desugared tf i :: es *)
  end.

Lemma expr_of_val_of_val_not_val v :
  of_val0 v = expr_of_val_not_val (Val v).
Proof. done. Qed.

Definition val_of_val_not_val x :=
  match x with
  | Val v => Some v
  | _ => None
  end.



(* Combining two ValNotVals. It is intended that combining will yield a ValNotVal 
   representinig the concatenation of the function arguments, and verifies our
   invariant that [NotVal e] is used only when e is not a value *)
Definition val_not_val_combine (v1 : ValNotVal) (v2 : ValNotVal) : ValNotVal :=
  match v1 with
  | Val (immV l) =>
      match v2 with
      | Val (immV l') => Val (immV (l ++ l'))
      | Val trapV => match l with
                    | [] => Val trapV
                    | _ => NotVal (v_to_e_list l ++ [AI_trap])
                    end
      | Val (brV i vh) => Val (brV (vh_push_const vh l))
      | Val (retV lh) => Val (retV (sh_push_const lh l))
      | Val (callHostV tf h vcs lh) => Val (callHostV tf h vcs (llh_push_const lh l))
      | Eff (susE vs i sh) => Eff (susE vs i (sus_push_const sh l))
      | Eff (swE vs k tf i sh) => Eff (swE vs k tf i (sw_push_const sh l))
      | Eff (thrE vs a i sh) => Eff (thrE vs a i (exn_push_const sh l))
(*      | ThrowRef es =>
          match separate_last l with
          | Some (l, VAL_ref (VAL_ref_exn a i)) =>
              Eff (thrE a i (ExBase l es))
          | None => ThrowRef es
          | _ => NotVal (v_to_e_list l ++ [:: AI_basic BI_throw_ref] ++ es)
          end
(*      | Suspend i es =>
          match separate_last l with
          | Some (l, VAL_ref (VAL_ref_cont k)) =>
              Eff (susE i (SuBase l es))
          | None => Suspend i es
          | _ => NotVal (v_to_e_list l ++ AI_suspend_desugared i :: es)
          end *)
      | Switch tf i es =>
          match separate_last l with
          | Some (l, VAL_ref (VAL_ref_cont k)) =>
              Eff (swE k tf i (SwBase l es))
          | None => Switch tf i es
          | _ => NotVal (v_to_e_list l ++ AI_switch_desugared tf i :: es)
          end *)
      | NotVal e => NotVal (v_to_e_list l ++ e)
      end
  | Val trapV => match expr_of_val_not_val v2 with
              [] => Val trapV
            | _ => NotVal (AI_trap :: expr_of_val_not_val v2)
            end
  | Val (brV i vh) =>
      Val (brV (vh_append vh (expr_of_val_not_val v2)))
  | Val (retV lh) =>
      Val (retV (sh_append lh (expr_of_val_not_val v2)))
  | Val (callHostV tf h vcs lh) =>
      Val (callHostV tf h vcs (llh_append lh (expr_of_val_not_val v2)))
  | Eff (susE vs i sh) =>
      Eff (susE vs i (sus_append sh (expr_of_val_not_val v2)))
  | Eff (swE vs k tf i sh) =>
      Eff (swE vs k tf i (sw_append sh (expr_of_val_not_val v2)))
  | Eff (thrE vs a i sh) =>
      Eff (thrE vs a i (exn_append sh (expr_of_val_not_val v2)))
(*  | ThrowRef es =>
      ThrowRef (es ++ expr_of_val_not_val v2)
(*  | Suspend i es =>
      Suspend i (es ++ expr_of_val_not_val v2) *)
  | Switch tf i es =>
      Switch tf i (es ++ expr_of_val_not_val v2) *)
  | NotVal es =>
      NotVal (es ++ expr_of_val_not_val v2)
  end.

Definition val_combine v1 v2 :=
  match val_not_val_combine (Val v1) (Val v2) with
  | Val v => v
  | _ => trapV
  end.


Definition merge_values vs :=
  fold_left val_not_val_combine vs (Val (immV [])).

(*
(* performs a fold_left on a list of ValNotVals. Aborts if a NotVal is reached *)
Fixpoint merge_values (v : val) (vs : list ValNotVal) : ValNotVal  :=
  match vs with
  | [] => Val v
  | a :: vs => match val_not_val_combine v a with
             | Val v => merge_values v vs
             | Eff e => val_not_val_combin 
             | ThrowRef es => ThrowRef (es ++ flatten (map expr_of_val_not_val vs))
             | NotVal e => NotVal (e ++ flatten (map expr_of_val_not_val vs))  end
  end.
*)
(*
sDefinition merge_values_list vs :=
  match vs with
  | Val v :: vs => merge_values v vs
  | [] => Val (immV [])
  | ThrowRef es :: vs => ThrowRef (es ++ flatten (map expr_of_val_not_val vs))
  | _ => NotVal (flatten (map expr_of_val_not_val vs))
  end.
*)

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


  
  Lemma suselts_of_continuation_clauses_None cls i:
    suselts_of_continuation_clauses cls i = None ->
    is_Some (firstx_continuation_suspend cls i).
  Proof.
    induction cls => //=.
    destruct (suselt_of_continuation_clause a i) eqn:Helt => //.
    - destruct (suselts_of_continuation_clauses cls i) => //.
      destruct a => //. destruct (eqtype.eq_op i t) => //.
    - unfold suselt_of_continuation_clause in Helt.
      destruct i.
      destruct a => //.
      destruct t => //.
      destruct (n0 <? n) eqn:Hn => //.
      destruct (n0 =? n) eqn:Hn' => //.
      apply Nat.eqb_eq in Hn' as ->.
      rewrite eqtype.eq_refl. done.
  Qed.

  Lemma firstx_suspend_lookup dccs i x :
    firstx_continuation_suspend dccs i = Some x ->
    exists k, dccs !! k = Some (DC_catch i x).
  Proof.
    induction dccs => //=.
    destruct a => //=.
    - destruct (eqtype.eq_op i t) eqn:Hit => //.
      + intros H; inversion H; subst; clear H.
        apply b2p in Hit as ->.
        exists 0 => //.
      + intros H; apply IHdccs in H as [k Hres].
        exists (S k) => //.
    - intros H; apply IHdccs in H as [k Hres].
      exists (S k) => //.
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


  Lemma swelts_of_continuation_clauses_None cls i:
    swelts_of_continuation_clauses cls i = None ->
    firstx_continuation_switch cls i = true.
  Proof.
    induction cls => //=.
    destruct (swelt_of_continuation_clause a i) eqn:Helt => //.
    - destruct (swelts_of_continuation_clauses cls i) => //.
      destruct a => //. destruct (eqtype.eq_op i t) => //.
    - unfold swelt_of_continuation_clause in Helt.
      destruct i.
      destruct a => //.
      destruct t => //.
      destruct (n0 <? n) eqn:Hn => //.
      destruct (n0 =? n) eqn:Hn' => //.
      apply Nat.eqb_eq in Hn' as ->.
      rewrite eqtype.eq_refl. done.
  Qed.

  Lemma firstx_switch_lookup dccs i :
    firstx_continuation_switch dccs i = true ->
    exists k, dccs !! k = Some (DC_switch i).
  Proof.
    induction dccs => //=.
    destruct a => //=.
    - intros H; apply IHdccs in H as [k Hres].
      exists (S k) => //.
    - destruct (eqtype.eq_op i t) eqn:Hit => //.
      + intros H; inversion H; subst; clear H.
        apply b2p in Hit as ->.
        exists 0 => //.
      + intros H; apply IHdccs in H as [k Hres].
        exists (S k) => //.

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


(*  Lemma exnelts_of_exception_clauses_None cls i:
    exnelts_of_exception_clauses cls i = None ->
    is_Some (firstx_exception cls i).
  Proof.
    induction cls => //=.
    destruct (swelt_of_continuation_clause a i) eqn:Helt => //.
    - destruct (swelts_of_continuation_clauses cls i) => //.
      destruct a => //. destruct (eqtype.eq_op i t) => //.
    - unfold swelt_of_continuation_clause in Helt.
      destruct i.
      destruct a => //.
      destruct t => //.
      destruct (n0 <? n) eqn:Hn => //.
      destruct (n0 =? n) eqn:Hn' => //.
      apply Nat.eqb_eq in Hn' as ->.
      rewrite eqtype.eq_refl. done.
  Qed.

  Lemma firstx_switch_lookup dccs i :
    firstx_continuation_switch dccs i = true ->
    exists k, dccs !! k = Some (DC_switch i).
  Proof.
    induction dccs => //=.
    destruct a => //=.
    - intros H; apply IHdccs in H as [k Hres].
      exists (S k) => //.
    - destruct (eqtype.eq_op i t) eqn:Hit => //.
      + intros H; inversion H; subst; clear H.
        apply b2p in Hit as ->.
        exists 0 => //.
      + intros H; apply IHdccs in H as [k Hres].
        exists (S k) => //.

  Qed.  *)

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
  | AI_suspend_desugared vs i => Eff (susE vs i (SuBase [] []))
  | AI_switch_desugared vs k tf i => Eff (swE vs k tf i (SwBase [] []))
  | AI_throw_ref_desugared vs a i => Eff (thrE vs a i (ExBase [] []))
  | AI_basic (BI_const v) => Val (immV [VAL_num v])
  | AI_basic (BI_ref_null r) => Val (immV [VAL_ref (VAL_ref_null r)])
  | AI_ref f => Val (immV [VAL_ref (VAL_ref_func f)])
  | AI_ref_cont f => Val (immV [VAL_ref (VAL_ref_cont f)])
  | AI_ref_exn e i => Val (immV [VAL_ref (VAL_ref_exn e i)])
  | AI_label n labe es =>
      match merge_values (map to_val_instr es) with
      | Val (brV i vh) => 
          match vh_decrease (VH_rec [] n labe vh []) with
          | Some vh' => Val (brV vh')
          | None => NotVal [instr]
          end 
      | Val (retV lh) => Val (retV (SH_rec [] n labe lh []))
      | Val (callHostV tf h cvs lh) => Val (callHostV tf h cvs (LL_label [] n labe lh []))
      | Eff (susE vs i sh) => Eff (susE vs i (SuLabel [] n labe sh []))
      | Eff (swE vs k tf i sh) => Eff (swE vs k tf i (SwLabel [] n labe sh []))
      | Eff (thrE vs a i sh) => Eff (thrE vs a i (ExLabel [] n labe sh []))
      | _ => NotVal [instr]
      end
 | AI_local n f es =>
      match merge_values (map to_val_instr es) with
      | Val (callHostV tf h cvs sh) =>
          Val (callHostV tf h cvs (LL_local [] n f sh []))
      | Eff (susE vs i sh) => Eff (susE vs i (SuLocal [] n f sh []))
      | Eff (swE vs k tf i sh) => Eff (swE vs k tf i (SwLocal [] n f sh []))
      | Eff (thrE vs a i sh) => Eff (thrE vs a i (ExLocal [] n f sh []))
      | _ => NotVal [instr]
      end 
  | AI_call_host tf h cvs => Val (callHostV tf h cvs (LL_base [] []))
  | AI_prompt ts hs es =>
      match merge_values (map to_val_instr es) with
      | Val (brV i vh) => Val (brV (VH_prompt [] ts hs vh []))
      | Val (retV lh) => Val (retV (SH_prompt [] ts hs lh []))
      | Val (callHostV tf h cvs lh) => Val (callHostV tf h cvs (LL_prompt []  ts hs lh []))
      | Eff (susE vs i sh) => match suselts_of_continuation_clauses hs i with
                          | Some hs' => Eff (susE vs i (SuPrompt [] ts hs' sh []))
                          | None => NotVal [instr]
                          end
      | Eff (swE vs k tf i sh) => match swelts_of_continuation_clauses hs i with
                            | Some hs' => Eff (swE vs k tf i (SwPrompt [] ts hs' sh []))
                            | None => NotVal [instr]
                            end
      | Eff (thrE vs a i sh) => Eff (thrE vs a i (ExPrompt [] ts hs sh []))
      | _ => NotVal [instr]
      end
  | AI_handler hs es =>
      match merge_values (map to_val_instr es) with
      | Val (brV i vh) => Val (brV (VH_handler [] hs vh []))
      | Val (retV lh) => Val (retV (SH_handler [] hs lh []))
      | Val (callHostV tf h cvs lh) => Val (callHostV tf h cvs (LL_handler [] hs lh []))
      | Eff (susE vs i sh) => Eff (susE vs i (SuHandler [] hs sh []))
      | Eff (swE vs k tf i sh) => Eff (swE vs k tf i (SwHandler [] hs sh []))
      | Eff (thrE vs a i sh) => match exnelts_of_exception_clauses hs i with
                            | Some hs' => Eff (thrE vs a i (ExHandler [] hs' sh []))
                            | None => NotVal [instr]
                            end
      | _ => NotVal [instr]
      end
  | _ => NotVal [instr]
  end.

Definition to_val0 (e : expr0) : option val0 :=
  match merge_values (map to_val_instr e) with
  | Val v => Some v
  | _ => None
  end.

Definition to_eff0 (e : expr0) : option eff0 :=
  match merge_values (map to_val_instr e) with
  | Eff e => Some e
  | _ => None
  end.

Definition val : Type := val0 * frame.
Definition expr : Type := expr0 * frame.
Definition eff : Type := eff0 * frame.

Definition prim_step (e : expr) (s : state) (os : list observation) (e' : expr) (s' : state) (fork_es' : list expr) : Prop :=
  let '(e, f) := e in
  let '(e', f') := e' in
  reduce s f e s' f' e' /\ os = [] /\ fork_es' = [].

  
Lemma val_not_val_combine_app v1 v2 :
  expr_of_val_not_val (val_not_val_combine v1 v2) = expr_of_val_not_val v1 ++ expr_of_val_not_val v2.
Proof.
  intros.
  destruct v1, v2 => //=.
  all: try destruct v => //=.
  all: try destruct e => //=.
  all: try destruct v0 => //=. 
  by rewrite - v_to_e_cat.
  all: try by destruct l => //=.
  all: try by destruct lh => //= ; rewrite - v_to_e_cat ; by rewrite app_assoc.
  all : try by destruct s => //= ; rewrite - v_to_e_cat ; by rewrite app_assoc.
(*  all : try by destruct (of_val v) => //=. *)
(*  all : try by destruct e => //=. *)
  all : try by destruct lh => //= ; rewrite app_comm_cons ; rewrite app_assoc.
  all : try by destruct s => //= ; rewrite app_comm_cons ; rewrite app_assoc.
  all : try by destruct l0 => //= ; rewrite app_comm_cons ; rewrite app_assoc.
  all : try by destruct l1 => //= ; rewrite - v_to_e_cat ; rewrite app_assoc.
(*  all : try by destruct sh => //=; rewrite app_comm_cons app_assoc. *)
  all : try by destruct sh => //=; rewrite -v_to_e_cat app_assoc.
  all: try by destruct sh => //=; rewrite -app_assoc.
  destruct (vfill _ _) => //.
  destruct (sfill _ _) => //.
  destruct (llfill _ _) => //.
  destruct (susfill _ _ _) => //.
  destruct (swfill _ _ _) => //.
  destruct (exnfill _ _ _) => //. 
  all: destruct (separate_last l) as [[l' x]|] eqn:Hl.
  all: try by apply separate_last_None in Hl; subst.
  all: destruct x => //.
  all: destruct v => //=.
  all: apply separate_last_spec in Hl.
  all: subst l.
  all: rewrite -v_to_e_cat.
  all: rewrite -app_assoc.
  all: done.
Qed.

(* if we write val_not_val_combine_assoc v1 v2 as v1 + v2, this lemma is just plain
   associativity : v1 + (v2 + x) = (v1 + v2) + x. Because of typing, the phrasing used to be 
   a little more complicated *)
Lemma val_not_val_combine_assoc v1 v2 x :
  val_not_val_combine v1 (val_not_val_combine v2 x) =
    val_not_val_combine (val_not_val_combine v1 v2) x.
(*    match val_not_val_combine v1 (Val v2) with
    | Val v3 => val_not_val_combine v3 x
    | NotVal es => NotVal (es ++ expr_of_val_not_val x)
    | ThrowRef es => ThrowRef (es ++ expr_of_val_not_val x)
    end. *)
Proof.
  (* might this be simpler? *)
 (* unfold val_not_val_combine.
  destruct v1 => //=.
  - destruct v => //=.
    + destruct v2 => //=.
      * destruct v => //=.
        -- destruct x => //=.
           ++ destruct v => //=.
              ** by rewrite catA.
              ** destruct l0 => //=.
                 --- destruct l => //=.
                     by rewrite cats0.
                 --- destruct l => //=.
                     rewrite -v_to_e_cat.
                     simpl. repeat rewrite -cat_app.
                     rewrite -catA. done.
              ** rewrite vh_push_const_app => //.
              ** rewrite sh_push_const_app => //.
              ** rewrite llh_push_const_app => //.
           ++ destruct e => //=.
              ** rewrite sus_push_const_app => //.
              ** rewrite sw_push_const_app => //.
              ** rewrite exn_push_const_app => //.
           ++ rewrite -v_to_e_cat.
              rewrite -cat_app catA. done.
        -- destruct x => //=.
           ++ destruct v => //=.
              ** destruct l0 => //=.
                 --- destruct l => //=.
                     by rewrite app_nil_r.
                 --- destruct l => //=.
                     repeat rewrite -cat_app.
                     rewrite -catA. done.
              ** destruct l => //=.
                 repeat rewrite -cat_app.
                 rewrite -catA. done.
              ** destruct (vfill _ _) eqn:Hfill => //=.
                 --- apply vfill_is_nil in Hfill as [??] => //.
                 --- destruct l => //=.
                     repeat rewrite -cat_app.
                     rewrite -catA. done.
              ** destruct (sfill _ _) eqn:Hfill => //=.
                 --- apply sfill_is_nil in Hfill as [??] => //.
                 --- destruct l => //=.
                     repeat rewrite -cat_app.
                     by rewrite -catA.
              ** destruct (llfill _ _) eqn:Hfill => //=.
                 --- apply llfill_is_nil in Hfill as [??] => //.
                 --- destruct l => //=.
                     repeat rewrite -cat_app.
                     by rewrite -catA.
           ++ destruct e => //=.
              ** destruct (susfill _ _) eqn:Hfill => //=.
                 --- apply susfill_is_nil in Hfill as [??] => //.
                 --- destruct l => //=.
                     repeat rewrite -cat_app. by rewrite -catA.
              ** destruct (swfill _ _) eqn:Hfill => //=.
                 --- apply swfill_is_nil in Hfill as [??] => //.
                 --- destruct l => //=.
                     repeat rewrite -cat_app. by rewrite -catA.
              ** destruct (exnfill _  ) eqn:Hfill => //=.
                 --- apply exnfill_is_nil in Hfill as [??] => //.
                 --- destruct l => //=.
                     repeat rewrite -cat_app. by rewrite -catA.
           ++ destruct e => //=.
              ** destruct l => //=.
                 by rewrite app_nil_r.
              ** destruct l => //=.
                 repeat rewrite -cat_app. by rewrite -catA.
        -- rewrite vh_push_const_append => //.
        -- rewrite sh_push_const_append => //.
        -- rewrite llh_push_const_append => //.
      * destruct e => //=.
        -- rewrite sus_push_const_append => //.
        -- rewrite sw_push_const_append => //.
        -- rewrite exn_push_const_append => //.
      * by rewrite app_assoc.
    + destruct v2 => //=.
      * destruct v => //=.
        -- destruct x => //=.
           ++ destruct v => //=.
              ** destruct l => //=.
                 by rewrite -v_to_e_cat.
              ** destruct l => //=.
              ** destruct l => //=. 
                destruct (vfill _ _) eqn:Hfill.
                 --- apply vfill_is_nil in Hfill as [??] => //.
                 --- destruct l => //=.
                     +++ 
 *)

  destruct v1
    as [[ vs1 | | n1 vh1 | sh1 | tf1 h1 vcs1 llh1]
       |[ vs1 i1 sh1 | vs1 k1 tf1 i1 sh1 | vs1 a1 i1 sh1 ]
       | es1 ],
      v2 as [[ vs2 | | n2 vh2 | sh2 | tf2 h2 vcs2 llh2 ]
            |[ vs2 i2 sh2 | vs2 k2 tf2 i2 sh2 | vs2 a2 i2 sh2]
            | es2 ],
        x as [[ vs0 | | n0 vh0 | sh0 | tf0 h0 vcs0 llh0]
             | [vs0 i0 sh0 | vs0 k0 tf0 i0 sh0 | vs0 a0 i0 sh0 ]
             | es0 ].

  all: simpl ; try done.
  all: try (destruct (separate_last _) as [[??] |] eqn:Hlast => //=).
  all: try apply separate_last_spec in Hlast.
  all: try apply separate_last_None in Hlast.
(*  10:{ simpl.
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
  all: try by destruct (separate_last _) as [[??] |] eqn:Hlast; 
    [ destruct v; (try destruct v); (try done); by rewrite app_comm_cons app_assoc
    | done] .
  

  all: try by destruct (separate_last _) as [[??] |] eqn:Hlast;
    [ destruct v => //=;
                     [ destruct vs2 => //
                     | destruct v => //;
                                      (destruct vs2 => //=);
        apply separate_last_spec in Hlast;
        destruct l; inversion Hlast; subst => //=;
        rewrite -v_to_e_cat => //=;
                                rewrite -app_assoc; done
                     ]
    | apply separate_last_None in Hlast;
      subst => //=].

  1367:{
    destruct (separate_last 
 *)
  by rewrite catA.

  all: (try destruct vs1).
  all: (try destruct vs2).
  all: (try destruct vs0).
  all: try destruct es0.

  all: simpl ; try done.
  all: try by rewrite app_nil_r.
  all: try by rewrite cats0.
  
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
(*  all: try by destruct l. *)

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
(*  all: try by repeat f_equal; destruct sh2 ; simpl; repeat rewrite -catA; repeat rewrite -cat_app. *)
(*   all: try by repeat f_equal; destruct vs2; 
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
    ]. *)
(*  all: try by destruct v;
      (try destruct v);
      (destruct l;
       [ destruct vs2 ; inversion Hlast; subst => //=
       | inversion Hlast; subst; rewrite separate_last_trivial;
         destruct l => //=]). *)
(*  all: try by destruct v;
      [|destruct v];
    
    (destruct l;
       [ destruct vs2 => //=;
        inversion Hlast; subst => //=;
        rewrite separate_last_trivial;
        destruct vs1 => //=;
                         (try by rewrite -app_assoc);
                       try by rewrite cats0
       | inversion Hlast; subst => //=;
                                    repeat rewrite -cat_app;
        rewrite (app_comm_cons l);
        repeat rewrite -cat_app;
        rewrite (catA vs1 _ [::_]);
        rewrite separate_last_trivial;
        destruct vs1 => //=;
        rewrite -catA; done]). *)
(*  all: try by destruct v; [|destruct v]; simpl; (try done); by repeat rewrite app_nil_r. *)
(*  all: try by destruct v; [|destruct v]; simpl; (try done); repeat rewrite -cat_app; by rewrite -catA. *)
(*  all: try by destruct v => //=;
    destruct v => //=;
    destruct l => //=;
                  inversion Hlast; subst => //=;
      rewrite -v_to_e_cat => //=;
      repeat rewrite -cat_app; by rewrite -catA. *)
  all: try by destruct es2 => //=.
  all: try by destruct vh0; simpl;
      rewrite -v_to_e_cat;
      repeat rewrite -cat_app;
    repeat rewrite -catA.
  all: try by destruct sh0; simpl;
      rewrite -v_to_e_cat;
      repeat rewrite -cat_app;
    repeat rewrite -catA.
  all: try by destruct llh0; simpl;
      rewrite -v_to_e_cat;
      repeat rewrite -cat_app;
      repeat rewrite -catA.
(*  all: try by destruct v; [|destruct v]; simpl; (try done);
      repeat rewrite -cat_app; rewrite -catA;
      (try done);
    try (specialize (f_equal v_to_e_list Hlast) as H000;
         simpl in H000; rewrite H000;
         rewrite -v_to_e_cat => //=; repeat rewrite -catA). *)
  all: try by destruct vh2; simpl; repeat rewrite -cat_app; repeat rewrite -catA.
  all: try by destruct sh2; simpl; repeat rewrite -cat_app; repeat rewrite -catA.
  all: try by destruct llh2; simpl; repeat rewrite -cat_app; repeat rewrite -catA. 
Qed.


Lemma merge_br i (vh : valid_holed i) es :
  merge_values (Val (brV vh) :: es) =
    Val (brV (vh_append vh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent vh.
  induction es => //=.
  intros. destruct vh ; simpl ; by rewrite cats0.
  intros.
  rewrite vh_append_app.
  rewrite - IHes.
  unfold merge_values => //=.
  rewrite vh_push_const_append.
  done.
Qed.

Lemma merge_return sh es :
  merge_values (Val (retV sh) :: es) =
    Val (retV (sh_append sh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent sh.
  induction es => //=.
  intros. destruct sh ; simpl ; by rewrite cats0.
  intros.
  rewrite sh_append_app.
  rewrite - IHes.
  unfold merge_values => //=.
  rewrite sh_push_const_append.
  done.
Qed.

Lemma merge_suspend vs x (sh : susholed) es :
  merge_values (Eff (susE vs x sh) :: es) =
    Eff (susE vs x (sus_append sh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent sh.
  induction es => //=.
  intros sh. rewrite sus_append_nil.
  unfold merge_values => //=. rewrite sus_push_const_nil => //. 
  intros. rewrite sus_append_app. rewrite - IHes.
  unfold merge_values => //=.
  rewrite sus_push_const_append.
  done.
Qed.

Lemma merge_switch vs k tf x (sh : swholed) es :
  merge_values (Eff (swE vs k tf x sh) :: es) =
    Eff (swE vs k tf x (sw_append sh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent sh.
  induction es => //=.
  intros sh. unfold merge_values => //=.
  rewrite sw_append_nil. rewrite sw_push_const_nil. done.
  intros. rewrite sw_append_app. rewrite - IHes.
  unfold merge_values => /=.
  rewrite sw_push_const_append. done.
Qed.

Lemma merge_throw vs a x (sh : exnholed) es :
  merge_values (Eff (thrE vs a x sh) :: es) =
    Eff (thrE vs a x (exn_append sh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent sh.
  induction es => //=.
  intros sh.
  unfold merge_values => //=.
  rewrite exn_append_nil. rewrite exn_push_const_nil. done.
  intros. rewrite exn_append_app. rewrite - IHes.
  unfold merge_values => //=. 
  rewrite exn_push_const_append. done.
Qed.


Lemma merge_notval es es':
  merge_values (NotVal es :: es') =
    NotVal (es ++ (flatten (map expr_of_val_not_val es'))).
Proof.
  generalize dependent es.
  unfold merge_values => //=. 
  induction es' => //=.
  - intros; by rewrite app_nil_r.
  - intros.
    rewrite IHes'.
    by rewrite app_assoc.
Qed.


(* Lemma merge_ThrowRef es es':
  merge_values (ThrowRef es :: es') =
    ThrowRef (es ++ (flatten (map expr_of_val_not_val es'))).
Proof.
  generalize dependent es.
  unfold merge_values => //=. 
  induction es' => //=.
  - intros; by rewrite app_nil_r.
  - intros.
    rewrite IHes'.
    by rewrite app_assoc.
Qed. *)


(* Lemma merge_Suspend i es es':
  merge_values (Suspend i es :: es') =
    Suspend i (es ++ (flatten (map expr_of_val_not_val es'))).
Proof.
  generalize dependent es.
  unfold merge_values => //=. 
  induction es' => //=.
  - intros; by rewrite app_nil_r.
  - intros.
    rewrite IHes'.
    by rewrite app_assoc.
Qed. *)


(* Lemma merge_Switch tf i es es':
  merge_values (Switch tf i es :: es') =
    Switch tf i (es ++ (flatten (map expr_of_val_not_val es'))).
Proof.
  generalize dependent es.
  unfold merge_values => //=. 
  induction es' => //=.
  - intros; by rewrite app_nil_r.
  - intros.
    rewrite IHes'.
    by rewrite app_assoc.
Qed.  *)

Lemma merge_call_host tf h cvs sh es :
  merge_values (Val (callHostV tf h cvs sh) :: es) =
    Val (callHostV tf h cvs (llh_append sh (flatten (map expr_of_val_not_val es)))).
Proof.
  generalize dependent sh.
  induction es => //=.
  intros. destruct sh ; simpl ; by rewrite cats0.
  intros.
  rewrite llh_append_app.
  rewrite - IHes.
  rewrite /merge_values /= llh_push_const_append.
  done.
Qed.

Lemma merge_trap es :
  merge_values (Val trapV :: es) =
    val_not_val_combine (Val trapV) (NotVal (flatten (map expr_of_val_not_val es))).
Proof.
  unfold merge_values => //=.
  assert (Val trapV = val_not_val_combine (Val trapV) (NotVal [::])) => //=.
  rewrite H.
  rewrite - (app_nil_l (flatten _)).
  remember [] as l.
  clear Heql. clear H.
  generalize dependent l. 
  induction es => //=.
  - intros. destruct l => //=.
    by rewrite app_nil_r.
  - intros.
    simpl in IHes.
    destruct l => //=. 
    + destruct (expr_of_val_not_val a) eqn:Ha => //=.
      * exact (IHes []).
      * rewrite (IHes (a0 :: e)).
        simpl. done.
    + rewrite (IHes (a0 :: l ++ expr_of_val_not_val a)).
      simpl. rewrite app_assoc. done.
Qed.


(* This next lemma proves two identities that had to be proven mutually recursively *)
Lemma merge_prepend_flatten vs :
  (forall v0, merge_values (v0 :: vs) = val_not_val_combine v0 (merge_values vs)) /\
    flatten (map expr_of_val_not_val vs) = expr_of_val_not_val (merge_values vs).
Proof.
  induction vs => //=. 
  - unfold merge_values. split => //. destruct v0 => //=.
    + destruct v => //=.
      * by rewrite cats0.
      * by rewrite vh_append_nil vh_push_const_nil.
      * by rewrite sh_append_nil sh_push_const_nil.
      * by rewrite llh_append_nil llh_push_const_nil.
    + destruct e => //=.
      * by rewrite sus_append_nil sus_push_const_nil.
      * by rewrite sw_append_nil sw_push_const_nil.
      * by rewrite exn_append_nil exn_push_const_nil.
    + by rewrite app_nil_r.
(*    + by rewrite app_nil_r.
    + by rewrite app_nil_r. *)
(*    + by rewrite app_nil_r. *)
  - destruct IHvs as [IHvs1 IHvs2].
    rewrite (IHvs1 a).
    split.
    + intros v0; rewrite val_not_val_combine_assoc.
      rewrite - IHvs1.
      Opaque val_not_val_combine.
      unfold merge_values => //=.
      rewrite val_not_val_combine_assoc.
      done.
    + rewrite IHvs2.
      rewrite val_not_val_combine_app.
      done.
Qed.      

Transparent val_not_val_combine.

(* For convenience, we provide lemmas for usage of each identity separately *)
Lemma merge_prepend v0 vs :
  merge_values (v0 :: vs) = val_not_val_combine v0 (merge_values vs).
Proof. by edestruct merge_prepend_flatten as [? _]. Qed.

Lemma merge_flatten vs :
  flatten (map expr_of_val_not_val vs) = expr_of_val_not_val (merge_values vs).
Proof. by edestruct merge_prepend_flatten as [_ ?]. Qed.


(* Lemma merge_is_ThrowRef0 a l e:
  merge_values (map to_val_instr (a :: l)) = ThrowRef e ->
  l = expr_of_val_not_val (merge_values (map to_val_instr l)) ->
  a = AI_basic BI_throw_ref /\ l = e. 
Proof.
  simpl.
  destruct (to_val_instr a) eqn:Ha => //=.
  - destruct v => //=.
    + rewrite merge_prepend.
      destruct (merge_values _) eqn:Hl => //=.
      * destruct v => //=.
        destruct l0 => //.
      * destruct e0 => //=.
      * destruct (separate_last l0) as [[??]|] eqn:Hl0 => //.
        -- destruct v => //.
           destruct v => //.
        -- intros H; inversion H; subst.
           apply separate_last_None in Hl0 as ->.
           destruct a => //=.
           ++ destruct b => //=.
           ++ simpl in Ha.
              destruct (merge_values (map _ l1)) => //.
              destruct v => //.
              destruct e0 => //. 
              destruct (exnelts_of_exception_clauses _ _) => //.
           ++ simpl in Ha.
              destruct (merge_values (map _ l2)) => //.
              destruct v => //.
              destruct e0 => //. 
              ** destruct (suselts_of_continuation_clauses _ _) => //.
              ** destruct (swelts_of_continuation_clauses _ _) => //.
           ++ simpl in Ha.
              destruct (merge_values (map _ l1)) => //.
              destruct v => //.
              destruct i => //.
              destruct (vh_decrease lh) => //.
              destruct e0 => //. 
           ++ simpl in Ha.
              destruct (merge_values (map _ l0)) => //.
              destruct v => //.
              destruct e0 => //.
      * destruct (separate_last l0) as [[??]|] => //=.
        destruct v => //=.
        destruct v => //=.
(*      * destruct (separate_last l0) as [[??]|] => //=.
        destruct v => //=.
        destruct v => //=. *)
    + rewrite merge_trap => //=.
      destruct (flatten _) => //.
    + rewrite merge_br => //=.
    + rewrite merge_return => //=.
    + rewrite merge_call_host => //=.
  - destruct e0 => //=. 
    + rewrite merge_suspend => //=.
    + rewrite merge_switch => //=.
    + rewrite merge_throw => //=.
  - rewrite merge_notval => //.
  - rewrite merge_ThrowRef => //.
    intros H ->.
    inversion H; subst e.
    destruct a => //=.
    destruct b => //=.
    + simpl in Ha. inversion Ha; subst e0 => //=.
      rewrite merge_flatten. done.
    + simpl in Ha.
      destruct (merge_values (map _ l1)) => //.
      destruct v => //.
      destruct e => //. 
      destruct (exnelts_of_exception_clauses _ _) => //.
    + simpl in Ha.
      destruct (merge_values (map _ l2)) => //.
      destruct v => //.
      destruct e => //.
      * destruct (suselts_of_continuation_clauses _ _) => //.
      * destruct (swelts_of_continuation_clauses _ _) => //.
    + simpl in Ha.
      destruct (merge_values (map _ l1)) => //. 
      destruct v => //.
      destruct i => //.
      destruct (vh_decrease lh) => //.
      destruct e => //. 
    + simpl in Ha.
      destruct (merge_values (map _ l0)) => //.
      destruct v => //.
      destruct e => //.
(*  - rewrite merge_Suspend => //. *)
  - rewrite merge_Switch => //. 
Qed. *)



(* Lemma merge_is_Suspend0 a l i e:
  merge_values (map to_val_instr (a :: l)) = Suspend i e ->
  l = expr_of_val_not_val (merge_values (map to_val_instr l)) ->
  a = AI_suspend_desugared i /\ l = e. 
Proof.
  simpl.
  destruct (to_val_instr a) eqn:Ha => //=.
  - destruct v => //=.
    + rewrite merge_prepend.
      destruct (merge_values _) eqn:Hl => //=.
      * destruct v => //=.
        destruct l0 => //.
      * destruct e0 => //=.
      * destruct (separate_last l0) as [[??]|] eqn:Hl0 => //.
        destruct v => //.
        destruct v => //.
      * destruct (separate_last l0) as [[??]|] eqn:Hl0 => //.
        -- destruct v => //.
           destruct v => //.
        -- intros H; inversion H; subst.
           apply separate_last_None in Hl0 as ->.
           destruct a => //=.
           ++ destruct b => //=.
           ++ simpl in Ha.
              destruct (merge_values (map _ l1)) => //.
              destruct v => //.
              destruct e0 => //. 
              destruct (exnelts_of_exception_clauses _ _) => //.
           ++ simpl in Ha.
              destruct (merge_values (map _ l2)) => //.
              destruct v => //.
              destruct e0 => //. 
              ** destruct (suselts_of_continuation_clauses _ _) => //.
              ** destruct (swelts_of_continuation_clauses _ _) => //.
           ++ simpl in Ha.
              destruct (merge_values (map _ l1)) => //.
              destruct v => //.
              destruct i0 => //.
              destruct (vh_decrease lh) => //.
              destruct e0 => //. 
           ++ simpl in Ha.
              destruct (merge_values (map _ l0)) => //.
              destruct v => //.
              destruct e0 => //.
      * destruct (separate_last l0) as [[??]|] => //=.
        destruct v => //=.
        destruct v => //=.
    + rewrite merge_trap => //=.
      destruct (flatten _) => //.
    + rewrite merge_br => //=.
    + rewrite merge_return => //=.
    + rewrite merge_call_host => //=.
  - destruct e0 => //=. 
    + rewrite merge_suspend => //=.
    + rewrite merge_switch => //=.
    + rewrite merge_throw => //=.
  - rewrite merge_notval => //.
  - rewrite merge_ThrowRef => //.
  - rewrite merge_Suspend => //.
        intros H ->.
    inversion H; subst e.
    destruct a => //=.
    destruct b => //=.
    + simpl in Ha. inversion Ha; subst e0 => //=.
      rewrite merge_flatten. by subst. 
    + simpl in Ha.
      destruct (merge_values (map _ l1)) => //.
      destruct v => //.
      destruct e => //. 
      destruct (exnelts_of_exception_clauses _ _) => //.
    + simpl in Ha.
      destruct (merge_values (map _ l2)) => //.
      destruct v => //.
      destruct e => //.
      * destruct (suselts_of_continuation_clauses _ _) => //.
      * destruct (swelts_of_continuation_clauses _ _) => //.
    + simpl in Ha.
      destruct (merge_values (map _ l1)) => //. 
      destruct v => //.
      destruct i0 => //.
      destruct (vh_decrease lh) => //.
      destruct e => //. 
    + simpl in Ha.
      destruct (merge_values (map _ l0)) => //.
      destruct v => //.
      destruct e => //.
  - rewrite merge_Switch => //. 
Qed. *)


(*
Lemma merge_is_Switch0 a l tf i e:
  merge_values (map to_val_instr (a :: l)) = Switch tf i e ->
  l = expr_of_val_not_val (merge_values (map to_val_instr l)) ->
  a = AI_switch_desugared tf i /\ l = e. 
Proof.
  simpl.
  destruct (to_val_instr a) eqn:Ha => //=.
  - destruct v => //=.
    + rewrite merge_prepend.
      destruct (merge_values _) eqn:Hl => //=.
      * destruct v => //=.
        destruct l0 => //.
      * destruct e0 => //=.
      * destruct (separate_last l0) as [[??]|] => //=.
        destruct v => //=.
        destruct v => //=.
(*      * destruct (separate_last l0) as [[??]|] => //=.
        destruct v => //=.
        destruct v => //=. *)
      * destruct (separate_last l0) as [[??]|] eqn:Hl0 => //.
        -- destruct v => //.
           destruct v => //.
        -- intros H; inversion H; subst.
           apply separate_last_None in Hl0 as ->.
           destruct a => //=.
           ++ destruct b => //=.
           ++ simpl in Ha.
              destruct (merge_values (map _ l1)) => //.
              destruct v => //.
              destruct e0 => //. 
              destruct (exnelts_of_exception_clauses _ _) => //.
           ++ simpl in Ha.
              destruct (merge_values (map _ l2)) => //.
              destruct v => //.
              destruct e0 => //. 
              ** destruct (suselts_of_continuation_clauses _ _) => //.
              ** destruct (swelts_of_continuation_clauses _ _) => //.
           ++ simpl in Ha.
              destruct (merge_values (map _ l1)) => //.
              destruct v => //.
              destruct i0 => //.
              destruct (vh_decrease lh) => //.
              destruct e0 => //. 
           ++ simpl in Ha.
              destruct (merge_values (map _ l0)) => //.
              destruct v => //.
              destruct e0 => //.

    + rewrite merge_trap => //=.
      destruct (flatten _) => //.
    + rewrite merge_br => //=.
    + rewrite merge_return => //=.
    + rewrite merge_call_host => //=.
  - destruct e0 => //=. 
    + rewrite merge_suspend => //=.
    + rewrite merge_switch => //=.
    + rewrite merge_throw => //=.
  - rewrite merge_notval => //.
  - rewrite merge_ThrowRef => //.
(*  - rewrite merge_Suspend => //. *)
  - rewrite merge_Switch => //.
        intros H ->.
    inversion H; subst e.
    destruct a => //=.
    destruct b => //=.
    + simpl in Ha. inversion Ha; subst e0 => //=.
      rewrite merge_flatten. by subst. 
    + simpl in Ha.
      destruct (merge_values (map _ l1)) => //.
      destruct v => //.
      destruct e => //. 
      destruct (exnelts_of_exception_clauses _ _) => //.
    + simpl in Ha.
      destruct (merge_values (map _ l2)) => //.
      destruct v => //.
      destruct e => //.
      * destruct (suselts_of_continuation_clauses _ _) => //.
      * destruct (swelts_of_continuation_clauses _ _) => //.
    + simpl in Ha.
      destruct (merge_values (map _ l1)) => //. 
      destruct v => //.
      destruct i0 => //.
      destruct (vh_decrease lh) => //.
      destruct e => //. 
    + simpl in Ha.
      destruct (merge_values (map _ l0)) => //.
      destruct v => //.
      destruct e => //.

Qed. *)



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
    destruct (merge_values (map to_val_instr l0)) eqn:Hmerge => //.
    2: destruct e => //. 
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
      all: try by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
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
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
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
(*      * (* Throw_ref *)
        by rewrite merge_ThrowRef in Hmerge. *)
      * (* Trap *)
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
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
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try by destruct e0); try by inversion Hmerge.
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
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try by destruct e); try by inversion Hmerge.
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
      * (* Throw_ref *)
        simpl in Hmerge. rewrite merge_throw in Hmerge. inversion Hmerge.
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
        simpl in Hmerge.
(*        unfold merge_values, to_val_instr in Hmerge; fold to_val_instr in Hmerge. *)
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e => //.
        destruct v => //.
        all: (try by rewrite merge_return in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e => //.
        destruct v => //.
        all: (try by rewrite merge_return in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_suspend in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           ++ rewrite merge_switch in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 

      * (* Label *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e => //. 
        destruct v => //.
        all: (try by rewrite merge_return in Hmerge) ; (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge);
          (try by rewrite merge_notval in Hmerge);
          try by rewrite merge_call_host in Hmerge.
        destruct i0; first by rewrite merge_notval in Hmerge => //.
        destruct (vh_decrease _) eqn:Hdecr;
          last by rewrite merge_notval in Hmerge.
        (* destruct (vh_decrease (VH_rec _ _ _ _ _)) eqn:Hdecr => //. *)
        rewrite merge_br in Hmerge.
        replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
        -- inversion Hmerge.
           subst i.
           apply Eqdep.EqdepTheory.inj_pair2 in H2.
           subst lh.
           simpl in Hdecr.
(*           destruct i0 => //.
           destruct (vh_decrease lh0) eqn:Hdecr0 => //. 
           inversion Hdecr; subst v. *)
           simpl. repeat f_equal.
           apply IHm in Hmerge2.
           ++ eapply vfill_decrease in Hdecr.
              erewrite Hdecr in Hmerge2.
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
        destruct (merge_values (map _ l1)) eqn:Hl0 => //.
        2: destruct e => //. 
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
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
      all: try by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref_null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
(*      * (* Throw_ref *)
        by rewrite merge_ThrowRef in Hmerge. *)
      * (* Trap *)
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e0); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref_cont f) l0).
        lia.
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //. 
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //. 
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
      * (* Handler *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e => //. 
        destruct v => //.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e => //.
        destruct v => //.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_suspend in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           ++ rewrite merge_switch in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Label *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e => //.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _);
             last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l1)) => //=.
        2: destruct e => //=. 
        destruct v => //=.
        all: try by rewrite merge_notval in Hmerge.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
(*      * (* ??? *)
        simpl in Hmerge.
        destruct (merge_values _) => //=.
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
      all: try by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref null *)
          simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
(*      * (* Throw_ref *)
        by rewrite merge_ThrowRef in Hmerge. *)
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
           (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_ref f0) l0).
        lia.
      * (* Ref_exn *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
           (try destruct e0); try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
           (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_ref_cont f0) l0).
        lia.
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //. 
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
      * (* Handler *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l4)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l5)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_suspend in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           ++ rewrite merge_switch in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Label *) 
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l4)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l3)) eqn:Hmerge2 => //.
        2: destruct e => //.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
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
      all: try by rewrite merge_notval in Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        inversion Hmerge. subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        inversion Hmerge; subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
(*      * (* Throw_ref *)
        rewrite merge_ThrowRef in Hmerge => //.  *)
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
           (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        inversion Hmerge; subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
           (try destruct e0); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        inversion Hmerge; subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        -- destruct v ; inversion Hmerge.
        -- destruct e; inversion Hmerge; subst.
           assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
           rewrite -(IHm sh0 l0 H0 Hmerge0).
           destruct sh0 => //.
           specialize (length_cons_rec (AI_ref_cont f) l0).
           lia.
(*        -- inversion Hmerge; subst.
           simpl.
           destruct l0 => //. 
           apply merge_is_Suspend0 in Hmerge0 as [-> ->].
           done.
           clear - IHn Hsize.
           induction l0 => //=.
           assert (size_of_instruction a0 < n) as Han.
           { simpl in Hsize. lia. } 
           specialize (IHn a0 Han) as Ha'.
           rewrite merge_prepend.
           remember (merge_values (map _ l0)) as vnv.
           specialize (val_not_val_combine_app (to_val_instr a0) vnv) as H'.
           destruct (val_not_val_combine (to_val_instr a0) vnv) eqn:Hv ; simpl in H' ; simpl.
           all: rewrite H'.
           all: rewrite Ha'.
           all: rewrite IHl0.
           all: try done.
           all: simpl.
           all: simpl in Hsize.
           all: lia. *)
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //. 
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e. 
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
        -- destruct (suselts_of_continuation_clauses l2 _) eqn:Hsuselts' => //.
           2: by rewrite merge_notval in Hmerge.
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
           ++ rewrite merge_switch in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
      * (* Label *) 
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i0; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l1)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: try by rewrite merge_notval in Hmerge.
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
      all: try by rewrite merge_notval in Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        inversion Hmerge; subst.
        assert (size_of_instruction (AI_handler l l0) < S n).
        simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
            (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        inversion Hmerge; subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
(*      * (* Throw_ref *)
        rewrite merge_ThrowRef in Hmerge => //.  *)
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
            (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        inversion Hmerge; subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e0; inversion Hmerge; subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        -- destruct v ; inversion Hmerge.
        -- destruct e; inversion Hmerge; subst.
           assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize.
           simpl. lia.
           rewrite -(IHm sh0 l0 H0 Hmerge0).
           destruct sh0 => //.
           specialize (length_cons_rec (AI_ref_cont f) l0).
           lia.
(*        -- inversion Hmerge; subst.
           destruct l0 => //. apply merge_is_Switch0 in Hmerge0 as [-> ->] => //.
           clear - IHn Hsize.
           induction l0 => //=.
           assert (size_of_instruction a0 < n) as Han.
           { simpl in Hsize. lia. } 
           specialize (IHn a0 Han) as Ha'.
           rewrite merge_prepend.
           remember (merge_values (map _ l0)) as vnv.
           specialize (val_not_val_combine_app (to_val_instr a0) vnv) as H'.
           destruct (val_not_val_combine (to_val_instr a0) vnv) eqn:Hv ; simpl in H' ; simpl.
           all: rewrite H'.
           all: rewrite Ha'.
           all: rewrite IHl0.
           all: try done.
           all: simpl.
           all: simpl in Hsize.
           all: lia. *)
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //. 
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           ++ rewrite merge_suspend in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
        -- destruct (swelts_of_continuation_clauses l2 _) eqn:Hswelts' => //.
           2: by rewrite merge_notval in Hmerge.
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i0; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l1)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: try by rewrite merge_notval in Hmerge.
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
      all: try by rewrite merge_notval in Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        inversion Hmerge; subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        inversion Hmerge; subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
(*      * (* Throw_ref *)
        rewrite merge_ThrowRef in Hmerge => //.  *)
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        inversion Hmerge; subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        -- destruct v; inversion Hmerge.
        -- destruct e0 ; inversion Hmerge. subst.
           assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
           rewrite -(IHm sh0 l0 H0 Hmerge0).
           destruct sh0 => //.
           specialize (length_cons_rec (AI_ref_exn e t) l0).
           lia.
        (* -- inversion Hmerge; subst. destruct l0 => //.
           apply merge_is_ThrowRef0 in Hmerge0 as [-> ->] => //.
           clear - IHn Hsize.
           induction l0 => //=.
           assert (size_of_instruction a1 < n) as Han.
           { simpl in Hsize. lia. } 
           specialize (IHn a1 Han) as Ha'.
           rewrite merge_prepend.
           remember (merge_values (map _ l0)) as vnv.
           specialize (val_not_val_combine_app (to_val_instr a1) vnv) as H'.
           destruct (val_not_val_combine (to_val_instr a1) vnv) eqn:Hv ; simpl in H' ; simpl.
           all: rewrite H'.
           all: rewrite Ha'.
           all: rewrite IHl0.
           all: try done.
           all: simpl.
           all: simpl in Hsize.
           all: lia. *)
      * (* Ref_cont *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_handler l l0) < S n). simpl in Hsize. simpl. lia.
        simpl in Hmerge.
        inversion Hmerge.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f) l0).
        lia.
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //.
        inversion Hmerge => /=. subst.
        rewrite map_map.
        repeat f_equal.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn; last by simpl in Hsize; lia.
        simpl.
        rewrite -> IHl0 at 1 => //=.
        simpl in Hsize.
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
        destruct (exnelts_of_exception_clauses l2 _) eqn:Hexnels => //.
        2: by rewrite merge_notval in Hmerge.
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l4)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           ++ rewrite merge_suspend in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) eqn:Hswelts => //.
           ++ rewrite merge_switch in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i0; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l2)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: try by rewrite merge_notval in Hmerge.
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
    destruct (merge_values (map to_val_instr l1)) eqn:Hmerge => //.
    2: destruct e.
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
      all: try by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
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
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
            (try destruct e); try by inversion Hmerge.
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
(*      * (* Throw_ref *)
        by rewrite merge_ThrowRef in Hmerge. *)
      * (* Trap *)
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
            (try destruct e); try by inversion Hmerge.
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
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
            (try destruct e0); try by inversion Hmerge.
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
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
            (try destruct e); try by inversion Hmerge.
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
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //.
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_return in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l4)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_return in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_suspend in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           ++ rewrite merge_switch in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.

      * (* Label *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_return in Hmerge) ; (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge);
          (try by rewrite merge_notval in Hmerge);
          try by rewrite merge_call_host in Hmerge.
        destruct i0; first by rewrite merge_notval in Hmerge.
        destruct (vh_decrease lh0) eqn:Hdecr; last by rewrite merge_notval in Hmerge.
        (* destruct (vh_decrease (VH_rec _ _ _ _ _)) eqn:Hdecr => //. *)
        rewrite merge_br in Hmerge.
        replace (flatten (map expr_of_val_not_val (map to_val_instr l1))) with l1 in Hmerge.
        -- inversion Hmerge.
           subst i.
           apply Eqdep.EqdepTheory.inj_pair2 in H2.
           subst lh.
(*           simpl in Hdecr.
           destruct i => //.
           destruct (vh_decrease lh0) eqn:Hdecr0 => //. 
           inversion Hdecr; subst v. *)
           simpl. repeat f_equal.
           apply IHm in Hmerge2.
           ++ eapply vfill_decrease in Hdecr.
              erewrite Hdecr in Hmerge2.
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
        destruct (merge_values (map _ l2)) eqn:Hl1 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
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
      all: try by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l1) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_basic (BI_const v)) l1).
        lia.
      * (* Ref_null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
            (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l1) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l1).
        lia.
(*      * (* Throw_ref *)
        rewrite merge_ThrowRef in Hmerge => //.  *)
      * (* Trap *)
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
            (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l1) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref f) l1).
        lia.
      * (* Ref_exn *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
            (try destruct e0); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l1) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref_exn e t) l1).
        lia.
      * (* Ref_cont *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
            (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l1) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref_cont f) l1).
        lia.
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //. 
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //. 
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
      * (* Handler *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge. 
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all:(try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l4)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all:(try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_suspend in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           ++ rewrite merge_switch in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
      * (* Label *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l2)) => //=.
        2: destruct e.
        destruct v => //=.
        all: try by rewrite merge_notval in Hmerge.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
(*      * (* ??? *)
        simpl in Hmerge.
        destruct (merge_values _) => //=.
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
      all: try by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l1) => //=.
        destruct l5 => //=. 
        specialize (length_cons_rec (AI_basic (BI_const v)) l1).
        lia.
      * (* Ref null *)
          simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
           (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l1) => //=.
        destruct l5 => //=. 
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l1).
        lia.
(*      * (* Throw_ref *)
        rewrite merge_ThrowRef in Hmerge => //.  *)
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
           (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l1) => //=.
        destruct l5 => //=. 
        specialize (length_cons_rec (AI_ref f0) l1).
        lia.
      * (* Ref_exn *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
           (try destruct e0); try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l1) => //=.
        destruct l5 => //=. 
        specialize (length_cons_rec (AI_ref_exn e t) l1).
        lia.
      * (* Ref_cont *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
           (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l1) => //=.
        destruct l5 => //=. 
        specialize (length_cons_rec (AI_ref_cont f0) l1).
        lia.
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //. 
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
      * (* Handler *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l5)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l6)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_suspend in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           ++ rewrite merge_switch in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
      * (* Label *) 
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l5)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l4)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
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
      all: try by rewrite merge_notval in Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l1).
        lia.
      * (* Ref null *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l1).
        lia.
(*      * (* Throw_ref *)
        rewrite merge_ThrowRef in Hmerge => //.  *)
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l1).
        lia.
      * (* Ref_exn *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e0; inversion Hmerge; subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_exn e t) l1).
        lia.
      * (* Ref_cont *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        -- destruct v ; inversion Hmerge.
        -- destruct e; inversion Hmerge; subst.
           assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
           rewrite -(IHm sh0 l1 H0 Hmerge0).
           destruct sh0 => //.
           specialize (length_cons_rec (AI_ref_cont f) l1).
           lia.
        (* -- inversion Hmerge; subst.
           destruct l1 => //. 
           apply merge_is_Suspend0 in Hmerge0 as [-> ->] => //.
           clear - IHn Hsize.
           induction l1 => //=.
           assert (size_of_instruction a0 < n) as Han.
           { simpl in Hsize. lia. } 
           specialize (IHn a0 Han) as Ha'.
           rewrite merge_prepend.
           remember (merge_values (map _ l1)) as vnv.
           specialize (val_not_val_combine_app (to_val_instr a0) vnv) as H'.
           destruct (val_not_val_combine (to_val_instr a0) vnv) eqn:Hv ; simpl in H' ; simpl.
           all: rewrite H'.
           all: rewrite Ha'.
           all: rewrite IHl1.
           all: try done.
           all: simpl.
           all: simpl in Hsize.
           all: lia. *)
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //. 
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l4)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l5)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
        -- destruct (suselts_of_continuation_clauses l4 _) eqn:Hsuselts' => //.
           2: by rewrite merge_notval in Hmerge.
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
           ++ rewrite merge_switch in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Label *) 
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l4)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i0; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l3)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
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
      all: try by rewrite merge_notval in Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l1).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l1).
        lia.
(*      * (* Throw_ref *)
        rewrite merge_ThrowRef in Hmerge => //.  *)
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l1).
        lia.
      * (* Ref_exn *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e0; inversion Hmerge; subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_exn e t) l1).
        lia.
      * (* Ref_cont *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        -- destruct v ; inversion Hmerge.
        -- destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f) l1).
        lia.
(*        -- inversion Hmerge; subst.
           destruct l1 => //.
           apply merge_is_Switch0 in Hmerge0 as [-> ->] => //.
             clear - IHn Hsize.
           induction l1 => //=.
           assert (size_of_instruction a0 < n) as Han.
           { simpl in Hsize. lia. } 
           specialize (IHn a0 Han) as Ha'.
           rewrite merge_prepend.
           remember (merge_values (map _ l1)) as vnv.
           specialize (val_not_val_combine_app (to_val_instr a0) vnv) as H'.
           destruct (val_not_val_combine (to_val_instr a0) vnv) eqn:Hv ; simpl in H' ; simpl.
           all: rewrite H'.
           all: rewrite Ha'.
           all: rewrite IHl1.
           all: try done.
           all: simpl.
           all: simpl in Hsize.
           all: lia. *)
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //. 
           
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
        inversion Hmerge => /=.
        rewrite map_map.
        repeat f_equal.
        clear - IHn Hsize.
        induction l1 => //=.
        rewrite IHn ; last by simpl in Hsize ; lia.
        simpl.
        rewrite -> IHl1 at 1 => //=.
        simpl in Hsize.
        lia.  
      * (* Handler *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l4)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l5)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           ++ rewrite merge_suspend in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
        -- destruct (swelts_of_continuation_clauses l4 _) eqn:Hswelts' => //.
           2: rewrite merge_notval in Hmerge => //. 
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l4)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i0; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l3)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
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
      all: try by rewrite merge_notval in Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l1).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l1).
        lia.
(*      * (* Throw_ref *)
        rewrite merge_ThrowRef in Hmerge => //.  *)
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l1).
        lia.
      * (* Ref_exn *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        -- destruct v ; inversion Hmerge.
        -- destruct e0; inversion Hmerge; subst.
           assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
           rewrite -(IHm sh0 l1 H0 Hmerge0).
           destruct sh0 => //.
           specialize (length_cons_rec (AI_ref_exn e t) l1).
           lia.
(*        -- destruct l1 => //.
           inversion Hmerge; subst.
           apply merge_is_ThrowRef0 in Hmerge0 as [-> ->] => //.
           clear - IHn Hsize.
           induction l1 => //=.
           assert (size_of_instruction a1 < n) as Han.
           { simpl in Hsize. lia. } 
           specialize (IHn a1 Han) as Ha'.
           rewrite merge_prepend.
           remember (merge_values (map _ l1)) as vnv.
           specialize (val_not_val_combine_app (to_val_instr a1) vnv) as H'.
           destruct (val_not_val_combine (to_val_instr a1) vnv) eqn:Hv ; simpl in H' ; simpl.
           all: rewrite H'.
           all: rewrite Ha'.
           all: rewrite IHl1.
           all: try done.
           all: simpl.
           all: simpl in Hsize.
           all: lia. *)
      * (* Ref_cont *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_prompt l l0 l1) < S n). simpl in Hsize. simpl. lia.
        simpl in Hmerge.
        inversion Hmerge.

        rewrite -(IHm sh0 l1 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f) l1).
        lia.
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //.
        inversion Hmerge => /=.
        subst; rewrite map_map.
        repeat f_equal.
        clear - IHn Hsize.
        induction l1 => //=.
        rewrite IHn; last by simpl in Hsize ; lia.
        simpl. rewrite -> IHl1 at 1 => //=.
        simpl in Hsize. lia.
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e. 
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
        destruct (exnelts_of_exception_clauses _ _) eqn:Hexnels => //.
        2: rewrite merge_notval in Hmerge => //. 
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l4)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           ++ rewrite merge_suspend in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) eqn:Hswelts => //.
           ++ rewrite merge_switch in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i0; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l2)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
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
    destruct (merge_values (map to_val_instr l0)) eqn:Hmerge => //.
    2: destruct e.
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
      all: try by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
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
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
           (try destruct e); try by inversion Hmerge.
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
(*      * (* Throw_ref *)
        rewrite merge_ThrowRef in Hmerge => //. *)
      * (* Trap *)
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
           (try destruct e); try by inversion Hmerge.
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
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
           (try destruct e0); try by inversion Hmerge.
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
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
           (try destruct e); try by inversion Hmerge.
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
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //. 
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v0.
        all: (try by rewrite merge_return in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v0.
        all: (try by rewrite merge_return in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_suspend in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           ++ rewrite merge_switch in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.

      * (* Label *) 
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e. destruct v0.
        all: (try by rewrite merge_return in Hmerge) ; (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_notval in Hmerge);
          try by rewrite merge_call_host in Hmerge.
        destruct i0; first by rewrite merge_notval in Hmerge.
        destruct (vh_decrease lh0) eqn:Hdecr; last by rewrite merge_notval in Hmerge.
        (*destruct (vh_decrease (VH_rec _ _ _ _ _)) eqn:Hdecr => //.*)
        rewrite merge_br in Hmerge.
        replace (flatten (map expr_of_val_not_val (map to_val_instr l0))) with l0 in Hmerge.
        inversion Hmerge.
        
        subst i0.
        apply Eqdep.EqdepTheory.inj_pair2 in H2.
        subst lh.
        (* simpl in Hdecr.
        destruct (vh_decrease lh0) eqn:Hdecr0 => //.
        inversion Hdecr; subst v0. *)
        simpl in Hvh.
        destruct i => //.
        destruct (vh_decrease v0) eqn:Hdecr1 => //. 
        inversion Hvh; subst v.
        simpl. repeat f_equal.
        eapply IHm in Hmerge2.
        erewrite <- vfill_decrease.
        exact Hmerge2.
        exact Hdecr1.
        exact Hdecr.
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
        destruct (merge_values (map _ l1)) eqn:Hl1 => //.
        2: destruct e.
        destruct v0 => //.
        all: try by rewrite merge_notval in Hmerge.
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
      all: try by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref_null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
            (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
(*      * (* Throw_ref *)
        rewrite merge_ThrowRef in Hmerge => //.  *)
      * (* Trap *)
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
            (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
            (try destruct e0); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
            (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite (IHm s0 l0) => //=.
        destruct s0 => //=.
        specialize (length_cons_rec (AI_ref_cont f) l0).
        lia.
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //. 
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //. 
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
      * (* Handler *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all:(try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e. destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_suspend in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           ++ rewrite merge_switch in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Label *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e. destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l1)) => //=.
        2: destruct e.
        destruct v => //=.
        all: try by rewrite merge_notval in Hmerge.
        -- rewrite merge_call_host in Hmerge => //.
        -- rewrite merge_suspend in Hmerge => //.
        -- rewrite merge_switch in Hmerge => //.
        -- rewrite merge_throw in Hmerge => //. 
(*      * (* ??? *)
        simpl in Hmerge.
        destruct (merge_values _) => //=.
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
      all: try by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          (try destruct e); try by inversion Hmerge.
        destruct v0 ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref null *)
          simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
            (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
(*      * (* Throw_ref *)
        rewrite merge_ThrowRef in Hmerge => //.  *)
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
            (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_ref f0) l0).
        lia.
      * (* Ref_exn *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
            (try destruct e0); try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
             simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
            (try destruct e); try by inversion Hmerge.
        destruct v ; inversion Hmerge. subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        erewrite (IHm _ l0) => //=.
        destruct l4 => //=. 
        specialize (length_cons_rec (AI_ref_cont f0) l0).
        lia.
      * (* Throw_ref *)
        simpl in Hmerge.
        rewrite merge_throw in Hmerge => //. 
      * (* Suspend *)
        simpl in Hmerge.
        rewrite merge_suspend in Hmerge => //.
      * (* Switch *)
        simpl in Hmerge.
        rewrite merge_switch in Hmerge => //. 
      * (* Handler *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l4)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l5)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_suspend in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           ++ rewrite merge_switch in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Label *) 
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l4)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l3)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
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
      all: try by rewrite merge_notval in Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref null *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
(*      * (* Throw_ref *)
        rewrite merge_ThrowRef in Hmerge => //.  *)
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e0; inversion Hmerge; subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        -- destruct v ; inversion Hmerge.
        -- destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f) l0).
        lia.
        (* --  inversion Hmerge; subst.
           simpl.
           destruct l0 => //. 
           apply merge_is_Suspend0 in Hmerge0 as [-> ->].
           done.
           clear - IHn Hsize.
           induction l0 => //=.
           assert (size_of_instruction a0 < n) as Han.
           { simpl in Hsize. lia. } 
           specialize (IHn a0 Han) as Ha'.
           rewrite merge_prepend.
           remember (merge_values (map _ l0)) as vnv.
           specialize (val_not_val_combine_app (to_val_instr a0) vnv) as H'.
           destruct (val_not_val_combine (to_val_instr a0) vnv) eqn:Hv ; simpl in H' ; simpl.
           all: rewrite H'.
           all: rewrite Ha'.
           all: rewrite IHl0.
           all: try done.
           all: simpl.
           all: simpl in Hsize.
           all: lia. *)
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //. 
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) eqn:Hsuselts => //.
           2: by rewrite merge_notval in Hmerge.
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
           ++ rewrite merge_switch in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Label *) 
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i0; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l1)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
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
      all: try by rewrite merge_notval in Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
(*      * (* Throw_ref *)
        rewrite merge_ThrowRef in Hmerge => //.  *)
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e0; inversion Hmerge; subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_exn e t) l0).
        lia.
      * (* Ref_cont *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        -- destruct v ; inversion Hmerge.
        -- destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f) l0).
        lia.
(*        -- inversion Hmerge; subst.
           destruct l0 => //. apply merge_is_Switch0 in Hmerge0 as [-> ->] => //.
           clear - IHn Hsize.
           induction l0 => //=.
           assert (size_of_instruction a0 < n) as Han.
           { simpl in Hsize. lia. } 
           specialize (IHn a0 Han) as Ha'.
           rewrite merge_prepend.
           remember (merge_values (map _ l0)) as vnv.
           specialize (val_not_val_combine_app (to_val_instr a0) vnv) as H'.
           destruct (val_not_val_combine (to_val_instr a0) vnv) eqn:Hv ; simpl in H' ; simpl.
           all: rewrite H'.
           all: rewrite Ha'.
           all: rewrite IHl0.
           all: try done.
           all: simpl.
           all: simpl in Hsize.
           all: lia. *)
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //. 
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           ++ rewrite merge_suspend in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
        -- destruct (swelts_of_continuation_clauses _ _) eqn:Hswelts => //.
           2: rewrite merge_notval in Hmerge => //.
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i0; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l1)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
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
      all: try by rewrite merge_notval in Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.

        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l0).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l0).
        lia.
(*      * (* Throw_ref *)
        rewrite merge_ThrowRef in Hmerge => //. *)
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f) l0).
        lia.
      * (* Ref_exn *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        -- destruct v ; inversion Hmerge.
        -- destruct e0; inversion Hmerge; subst.
           assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
           rewrite -(IHm sh0 l0 H0 Hmerge0).
           destruct sh0 => //.
           specialize (length_cons_rec (AI_ref_exn e t) l0).
           lia.
(*        -- inversion Hmerge; subst. destruct l0 => //.
           apply merge_is_ThrowRef0 in Hmerge0 as [-> ->] => //.
           clear - IHn Hsize.
           induction l0 => //=.
           assert (size_of_instruction a1 < n) as Han.
           { simpl in Hsize. lia. } 
           specialize (IHn a1 Han) as Ha'.
           rewrite merge_prepend.
           remember (merge_values (map _ l0)) as vnv.
           specialize (val_not_val_combine_app (to_val_instr a1) vnv) as H'.
           destruct (val_not_val_combine (to_val_instr a1) vnv) eqn:Hv ; simpl in H' ; simpl.
           all: rewrite H'.
           all: rewrite Ha'.
           all: rewrite IHl0.
           all: try done.
           all: simpl.
           all: simpl in Hsize.
           all: lia. *)

      * (* Ref_cont *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l0)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_label n0 l l0) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l0 H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f) l0).
        lia.
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //.
        inversion Hmerge; subst => /=.
        rewrite map_map.
        repeat f_equal.
        clear - IHn Hsize.
        induction l0 => //=.
        rewrite IHn; last by simpl in Hsize; lia.
        simpl. rewrite -> IHl0 at 1 => //=.
        simpl in Hsize. lia.
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
        destruct (exnelts_of_exception_clauses _ _) eqn:Hexnels => //.
        2: by rewrite merge_notval in Hmerge.
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           ++ rewrite merge_suspend in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) eqn:Hswelts => //.
           ++ rewrite merge_switch in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //.
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i0; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l1)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
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
    destruct (merge_values _) eqn:Hmerge => //.
    2: destruct e.
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
    all: try by rewrite merge_notval in Hmerge.
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
      destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
        (try destruct e); try by inversion Hmerge.
      destruct v0 ; inversion Hmerge. subst.
      assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
      erewrite <- (IHm _ l) => //=.
      destruct l3 => //=. 
      specialize (length_cons_rec (AI_basic (BI_const v)) l).
      lia.
    * (* Ref null *)
         simpl in Hmerge.
      rewrite merge_prepend in Hmerge.
      destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
         (try destruct e); try by inversion Hmerge.
      destruct v ; inversion Hmerge. subst.
      assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
      erewrite <- (IHm _ l) => //=.
      destruct l3 => //=. 
      specialize (length_cons_rec (AI_basic (BI_ref_null r)) l).
      lia.
(*    * (* Throw_ref *)
      rewrite merge_ThrowRef in Hmerge => //.  *)
    * (* Trap *)
      simpl in Hmerge.
      rewrite merge_trap in Hmerge.
      destruct (flatten _) => //=.
    * (* Ref *)
      simpl in Hmerge.
      rewrite merge_prepend in Hmerge.
      destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
        (try destruct e); try by inversion Hmerge.
      destruct v ; inversion Hmerge. subst.
      assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
      erewrite <- (IHm _ l) => //=.
      destruct l3 => //=. 
      specialize (length_cons_rec (AI_ref f1) l).
      lia.
    * (* Ref_exn *)
           simpl in Hmerge.
      rewrite merge_prepend in Hmerge.
      destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
         (try destruct e0); try by inversion Hmerge.
      destruct v ; inversion Hmerge. subst.
      assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
      erewrite <- (IHm _ l) => //=.
      destruct l3 => //=. 
      specialize (length_cons_rec (AI_ref_exn e t) l).
      lia.
    * (* Ref_cont *)
           simpl in Hmerge.
      rewrite merge_prepend in Hmerge.
      destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
         (try destruct e); try by inversion Hmerge.
      destruct v ; inversion Hmerge. subst.
      assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
      erewrite <- (IHm _ l) => //=.
      destruct l3 => //=. 
      specialize (length_cons_rec (AI_ref_cont f1) l).
      lia.
    * (* Throw_ref *)
      rewrite merge_throw in Hmerge => //. 
    * (* Suspend *)
      simpl in Hmerge.
      rewrite merge_suspend in Hmerge => //. 
    * (* Switch *)
      simpl in Hmerge.
      rewrite merge_switch in Hmerge => //. 
    * (* Handler *)
      rewrite map_cons in Hmerge.
      simpl in Hmerge.
      destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
      2: destruct e.
      destruct v.
      all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_notval in Hmerge).
        
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l4)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_suspend in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
        -- destruct (swelts_of_continuation_clauses _ _) eqn:Hswelts => //.
           ++ rewrite merge_switch in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
    * (* Label *) 
      rewrite map_cons in Hmerge.
      simpl in Hmerge.
      destruct (merge_values (map to_val_instr l3)) eqn:Hmerge2 => //.
      2: destruct e.
      destruct v => //.
      all: try by rewrite merge_notval in Hmerge.
      -- destruct i; first by rewrite merge_notval in Hmerge.
         destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
      destruct (merge_values (map _ l2)) eqn:Hmerge2 => //.
      2: destruct e.
      destruct v => //.
      all: try by rewrite merge_notval in Hmerge.
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
      all: try by rewrite merge_notval in Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l).
        lia.
      * (* Ref null *)
           simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l).
        lia.
(*      * (* Throw_ref *)
        rewrite merge_ThrowRef in Hmerge => //.  *)
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f0) l).
        lia.
      * (* Ref_exn *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e0; inversion Hmerge; subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_exn e t) l).
        lia.
      * (* Ref_cont *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        -- destruct v ; inversion Hmerge.
        -- destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f0) l).
        lia.
        (* -- inversion Hmerge; subst.
           simpl.
           destruct l => //. 
           apply merge_is_Suspend0 in Hmerge0 as [-> ->].
           done.
           clear - IHn Hsize.
           induction l => //=.
           assert (size_of_instruction a0 < n) as Han.
           { simpl in Hsize. lia. } 
           specialize (IHn a0 Han) as Ha'.
           rewrite merge_prepend.
           remember (merge_values (map _ l)) as vnv.
           specialize (val_not_val_combine_app (to_val_instr a0) vnv) as H'.
           destruct (val_not_val_combine (to_val_instr a0) vnv) eqn:Hv ; simpl in H' ; simpl.
           all: rewrite H'.
           all: rewrite Ha'.
           all: rewrite IHl.
           all: try done.
           all: simpl.
           all: simpl in Hsize.
           all: lia. *)
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //. 
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           ++ rewrite merge_throw in Hmerge => //.
           ++ rewrite merge_notval in Hmerge => //. 
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) eqn:Hsuselts => //.
           2: by rewrite merge_notval in Hmerge.
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
           rewrite merge_notval in Hmerge => //. 
      * (* Label *) 
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i0; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l0)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
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
      all: try by rewrite merge_notval in Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l).
        lia.
(*      * (* Throw_ref *)
        by rewrite merge_ThrowRef in Hmerge. *)
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f0) l).
        lia.
      * (* Ref_exn *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e0; inversion Hmerge; subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_exn e t) l).
        lia.
      * (* Ref_cont *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        -- destruct v ; inversion Hmerge.
        -- destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f0) l).
        lia.
(*        -- inversion Hmerge; subst.
           simpl.
           destruct l => //. 
           apply merge_is_Switch0 in Hmerge0 as [-> ->].
           done.
           clear - IHn Hsize.
           induction l => //=.
           assert (size_of_instruction a0 < n) as Han.
           { simpl in Hsize. lia. } 
           specialize (IHn a0 Han) as Ha'.
           rewrite merge_prepend.
           remember (merge_values (map _ l)) as vnv.
           specialize (val_not_val_combine_app (to_val_instr a0) vnv) as H'.
           destruct (val_not_val_combine (to_val_instr a0) vnv) eqn:Hv ; simpl in H' ; simpl.
           all: rewrite H'.
           all: rewrite Ha'.
           all: rewrite IHl.
           all: try done.
           all: simpl.
           all: simpl in Hsize.
           all: lia. *)
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //. 
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
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
           rewrite merge_notval in Hmerge => //.
      * (* Prompt *)
        rewrite map_cons in Hmerge.
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_throw in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
           rewrite merge_notval in Hmerge => //.
        -- destruct (swelts_of_continuation_clauses _ _) eqn:Hswelts => //.
           2: rewrite merge_notval in Hmerge => //.
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i0; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l0)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
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
      all: try by rewrite merge_notval in Hmerge.
      * (* Br *)
        simpl in Hmerge.
        rewrite merge_br in Hmerge => //.
      * (* Return *)
        simpl in Hmerge.
        rewrite merge_return in Hmerge => //.
      * (* Const *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v0 ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_const v)) l).
        lia.
      * (* Ref null *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_basic (BI_ref_null r)) l).
        lia.
(*      * (* Throw_ref *)
        rewrite merge_ThrowRef in Hmerge => //. *)
      * (* Trap *) 
        simpl in Hmerge.
        rewrite merge_trap in Hmerge.
        destruct (flatten _) => //=.
      * (* Ref *)
                simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref f0) l).
        lia.
      * (* Ref_exn *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        -- destruct v ; inversion Hmerge.
        -- destruct e0; inversion Hmerge; subst.
           assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
           rewrite -(IHm sh0 l H0 Hmerge0).
           destruct sh0 => //.
           specialize (length_cons_rec (AI_ref_exn e t) l).
           lia.
(*        -- inversion Hmerge; subst. destruct l => //.
           apply merge_is_ThrowRef0 in Hmerge0 as [-> ->] => //.
           clear - IHn Hsize.
           induction l => //=.
           assert (size_of_instruction a1 < n) as Han.
           { simpl in Hsize. lia. } 
           specialize (IHn a1 Han) as Ha'.
           rewrite merge_prepend.
           remember (merge_values (map _ l)) as vnv.
           specialize (val_not_val_combine_app (to_val_instr a1) vnv) as H'.
           destruct (val_not_val_combine (to_val_instr a1) vnv) eqn:Hv ; simpl in H' ; simpl.
           all: rewrite H'.
           all: rewrite Ha'.
           all: rewrite IHl.
           all: try done.
           all: simpl.
           all: simpl in Hsize.
           all: lia. *)
      * (* Ref_cont *)
        simpl in Hmerge.
        rewrite merge_prepend in Hmerge.
        destruct (merge_values (map to_val_instr l)) eqn:Hmerge0 ;
          try by inversion Hmerge.
        destruct v ; inversion Hmerge.
        destruct e; inversion Hmerge; subst.
        assert (size_of_instruction (AI_local n0 f l) < S n). simpl in Hsize. simpl. lia.
        rewrite -(IHm sh0 l H0 Hmerge0).
        destruct sh0 => //.
        specialize (length_cons_rec (AI_ref_cont f0) l).
        lia.
      * (* Throw_ref *)
        rewrite merge_throw in Hmerge => //.
        inversion Hmerge; subst; rewrite map_map => //=.
        repeat f_equal.
        clear - IHn Hsize.
        induction l => //=.
        rewrite IHn; last by simpl in Hsize; lia.
        simpl. rewrite -> IHl at 1 => //=.
        simpl in Hsize. lia.
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
        destruct (exnelts_of_exception_clauses _ _) eqn:Hexnels => //.
        2: by rewrite merge_notval in Hmerge.
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l2)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: (try by rewrite merge_br in Hmerge); (try by rewrite merge_call_host in Hmerge); (try by rewrite merge_suspend in Hmerge); (try by rewrite merge_switch in Hmerge); (try by rewrite merge_return in Hmerge); (try by rewrite merge_notval in Hmerge).
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           rewrite merge_suspend in Hmerge => //.
           rewrite merge_notval in Hmerge => //. 
        -- destruct (swelts_of_continuation_clauses _ _) eqn:Hswelts => //.
           rewrite merge_switch in Hmerge => //.
                      rewrite merge_notval in Hmerge => //. 
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
        simpl in Hmerge.
        destruct (merge_values (map to_val_instr l1)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
        -- destruct i0; first by rewrite merge_notval in Hmerge.
           destruct (vh_decrease _); last by rewrite merge_notval in Hmerge.
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
        destruct (merge_values (map _ l0)) eqn:Hmerge2 => //.
        2: destruct e.
        destruct v => //.
        all: try by rewrite merge_notval in Hmerge.
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
  expr_of_val_not_val (merge_values (map to_val_instr es)) = es.
Proof.
  induction es => //=.
  specialize (of_to_val_instr a) ; intro Ha'.
  rewrite merge_prepend.
  remember (merge_values _) as vnv.
  specialize (val_not_val_combine_app (to_val_instr a) vnv) ; intro H.
  destruct (val_not_val_combine (to_val_instr a) vnv) eqn:Hv ; simpl in H ; simpl ; 
    rewrite H Ha' IHes ; subst ; done.
Qed.


(* Lemma merge_is_Suspend l i e:
  merge_values (map to_val_instr (l)) = Suspend i e ->
  l = AI_suspend_desugared i :: e.
Proof.
  destruct l => //.
  intro H.
  apply merge_is_Suspend0 in H as [-> ->] => //.
  by rewrite merge_to_val.
Qed. *)

(* Lemma merge_is_Switch l tf i e:
  merge_values (map to_val_instr (l)) = Switch tf i e ->
  l = AI_switch_desugared tf i :: e. 
Proof.
  destruct l => //.
  intro H.
  apply merge_is_Switch0 in H as [-> ->] => //.
  by rewrite merge_to_val.
Qed.

Lemma merge_is_ThrowRef l e:
  merge_values (map to_val_instr (l)) = ThrowRef e ->
  l = AI_basic BI_throw_ref :: e.
Proof.
  destruct l => //.
  intro H.
  apply merge_is_ThrowRef0 in H as [-> ->] => //.
  by rewrite merge_to_val.
Qed. *)
  
Lemma of_to_val0 es v : to_val0 es = Some v -> of_val0 v = es.
Proof.
  unfold to_val0. specialize (merge_to_val es) ; intro H.
  destruct (merge_values _) => //.
  simpl in H. intro H' ; inversion H' ; by subst.
Qed.

Lemma of_to_eff0 es e : to_eff0 es = Some e -> of_eff0 e = es.
Proof.
  unfold to_eff0. specialize (merge_to_val es) ; intro H.
  destruct (merge_values _) => //.
  simpl in H. intros H'; inversion H'; by subst.
Qed. 

Lemma to_val_instr_AI_const a :
  to_val_instr (AI_const a) = Val (immV [:: a]).
Proof.
  destruct a => //=.
  destruct v => //=.
Qed.

Lemma to_val_AI_const a : to_val0 [AI_const a] = Some (immV [:: a]).
Proof. rewrite /to_val0 /= to_val_instr_AI_const //. Qed.

Lemma to_of_val0 v : to_val0 (of_val0 v) = Some v.
Proof.
  destruct v.
  - induction l => //=.
    unfold to_val0.
    simpl.
    unfold to_val0 in IHl.
    simpl in IHl.
(*    unfold merge_values.
    rewrite map_cons.
    rewrite to_val_instr_AI_const.
    unfold to_val in IHl.
    unfold of_val in IHl.     *)
    rewrite to_val_instr_AI_const.
    destruct (map to_val_instr _) eqn:Hmap; try by inversion IHl.
    destruct (merge_values (v :: l0)) eqn:Hmerge ; try by inversion IHl.
    inversion IHl ; subst => //.
    rewrite merge_prepend.
    rewrite Hmerge.
    done.
  - done.
  - unfold of_val0, to_val0. 
    cut (forall i (vh : valid_holed i) j, merge_values (map to_val_instr (vfill vh [AI_basic (BI_br (j + i))])) = Val (brV (vh_increase_repeat vh j))).
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
        destruct (merge_values _) eqn:Hmerge => //.
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
        destruct (merge_values _) eqn:Hmerge => //.
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
        destruct (merge_values _) eqn:Hmerge => //.
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
        destruct (merge_values _) eqn:Hmerge => //.
        inversion IHbef; subst v => //.
        simpl.
        by rewrite - vh_increase_repeat_push_const.
  - unfold of_val0, to_val0.
    induction s.
    + induction l => //=.
      * rewrite merge_return.
        rewrite flatten_simplify.
        done.
      * rewrite to_val_instr_AI_const merge_prepend.
        destruct (merge_values _) => //=.
        inversion IHl ; subst => //=.
    + induction l => /=.
      * destruct (merge_values _) => //.
        inversion IHs ; subst => /=.
        rewrite merge_return.
        rewrite flatten_simplify.
        done.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHs.
        destruct (merge_values _) => //.
        inversion IHl ; subst => //=.
            + induction l => /=.
      * destruct (merge_values _) => //.
        inversion IHs ; subst => /=.
        rewrite merge_return.
        rewrite flatten_simplify.
        done.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHs.
        destruct (merge_values _) => //.
        inversion IHl ; subst => //=.
            + induction l => /=.
      * destruct (merge_values _) => //.
        inversion IHs ; subst => /=.
        rewrite merge_return.
        rewrite flatten_simplify.
        done.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHs.
        destruct (merge_values _) => //.
        inversion IHl ; subst => //=.
  - unfold of_val0, to_val0 => //=.
    induction l0 => //=.
    + induction l0 => //=.
      * rewrite merge_call_host.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        destruct (merge_values _) => //=.
        inversion IHl0 ; subst => //.
    + induction l0 => //=.
      * destruct (merge_values _) => //.
        inversion IHl0 ; subst => /=.
        rewrite merge_call_host.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHl0.
        destruct (merge_values _) => //.
        inversion IHl1 ; subst => //.
    +  induction l0 => //=.
      * destruct (merge_values _) => //.
        inversion IHl0 ; subst => /=.
        rewrite merge_call_host.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHl0.
        destruct (merge_values _) => //.
        inversion IHl1 ; subst => //.
            +  induction l0 => //=.
      * destruct (merge_values _) => //.
        inversion IHl0 ; subst => /=.
        rewrite merge_call_host.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHl0.
        destruct (merge_values _) => //.
        inversion IHl1 ; subst => //.
            +  induction l0 => //=.
      * destruct (merge_values _) => //.
        inversion IHl0 ; subst => /=.
        rewrite merge_call_host.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHl0.
        destruct (merge_values _) => //.
        inversion IHl1 ; subst => //.
Qed.

Lemma to_of_eff0 e : to_eff0 (of_eff0 e) = Some e.
Proof.
  destruct e.
  - unfold of_eff0, to_eff0 => //=.
    induction sh => //=.
    + induction l => //=.
      * rewrite merge_suspend.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        destruct (merge_values _) => //=.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values _) => //.
        destruct e => //. 
        inversion IHsh ; subst => /=.
        rewrite merge_suspend.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values _) => //.
        inversion IHl ; subst => //=.
    + induction l => //=.
      * destruct (merge_values _) => //.
        destruct e => //. 
        inversion IHsh ; subst => /=.
        rewrite merge_suspend.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values _) => //.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values _) => //.
        destruct e => //. 
        inversion IHsh ; subst => /=.
        rewrite merge_suspend.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values _) => //.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values _) => //.
        inversion IHsh ; subst => /=.
        rewrite suselts_of_continuation_clauses_inv.
        rewrite merge_suspend.
        rewrite flatten_simplify => //=.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values _) => //.
        inversion IHl ; subst => //.

  - unfold of_eff0, to_eff0 => //=.
    induction sh => //=.
    + induction l => //=.
      * rewrite merge_switch flatten_simplify => //.
(*      * rewrite merge_prepend merge_Switch.
        rewrite flatten_simplify => //. *)
      * rewrite to_val_instr_AI_const merge_prepend.
        destruct (merge_values _) => //=.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values _) => //.
        destruct e => //. 
        inversion IHsh ; subst => /=.
        rewrite merge_switch.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values _) => //.
        inversion IHl ; subst => //=.
    + induction l => //=.
      * destruct (merge_values _) => //.
        destruct e => //. 
        inversion IHsh ; subst => /=.
        rewrite merge_switch.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values _) => //.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values _) => //.
        destruct e => //. 
        inversion IHsh ; subst => /=.
        rewrite merge_switch.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values _) => //.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values _) => //.
        inversion IHsh ; subst => /=.
        rewrite swelts_of_continuation_clauses_inv.
        rewrite merge_switch.
        rewrite flatten_simplify => //=.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values _) => //.
        inversion IHl ; subst => //.
  - unfold of_eff0, to_eff0 => //=.
    induction sh => //=.
    + induction l => //=.
      * rewrite merge_throw. (* rewrite merge_prepend merge_ThrowRef. *)
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        destruct (merge_values _) => //=.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values _) => //.
        destruct e => //. 
        inversion IHsh ; subst => /=.
        rewrite merge_throw.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values _) => //.
        inversion IHl ; subst => //=.
    + induction l => //=.
      * destruct (merge_values _) => //.
        destruct e => //. 
        inversion IHsh ; subst => /=.
        rewrite merge_throw.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values _) => //.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values _) => //.
        destruct e => //. 
        inversion IHsh ; subst => /=.
        rewrite exnelts_of_exception_clauses_inv.
        rewrite merge_throw.
        rewrite flatten_simplify => //.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values _) => //.
        inversion IHl ; subst => //.
    + induction l => //=.
      * destruct (merge_values _) => //.
        inversion IHsh ; subst => /=.
        rewrite merge_throw.
        rewrite flatten_simplify => //=.
      * rewrite to_val_instr_AI_const merge_prepend.
        clear IHsh.
        destruct (merge_values _) => //.
        inversion IHl ; subst => //.
        
Qed.


Lemma to_val_cons_is_none_or_cons : forall e0 e r,
  to_val0 (e0 :: e)%SEQ = r -> is_none_or (fun l => match l with | immV v => v != [] | _ => true end) r.
Proof.
  intros e0 e r H ; subst r.
  cut (forall n e0 e, length_rec (e0 :: e) < n ->  is_none_or (λ l : val0, match l with
                         | immV v => v != []
                         | _ => true
                                                              end) (to_val0 (e0 :: e)%SEQ)).
  intro H ; apply (H (S (length_rec (e0 :: e)))) ; try lia.
  clear e e0.
  induction n => //= ; first lia.
  intros e0 e Hlen.
  destruct e0 => //.
  destruct b => //= ; unfold to_val0 => /=.
  all: try rewrite /to_val0 /= merge_notval => //=. 
  - rewrite merge_br => //.
  - rewrite merge_return => //.
  - rewrite merge_prepend => /=.
    destruct e => //.
    assert (length_rec (a :: e) < n).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec => //=. lia.
    apply IHn in H.
    unfold to_val0 in H.
    destruct (merge_values _) => //.
    destruct v0 => //.
    destruct e0 => //. 
  - rewrite merge_prepend => /=.
    destruct e => //.
    assert (length_rec (a :: e) < n).
     unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec => //=. lia.
    apply IHn in H.
    unfold to_val0 in H.
    destruct (merge_values _) => //.
    destruct v => //.
    destruct e0 => //.
  - unfold to_val0 => //=.
    rewrite merge_trap => /=.
    rewrite flatten_simplify => /=.
    destruct e => //=.
  - unfold to_val0 => /=. rewrite merge_prepend => /=.
    destruct e => //.
    assert (length_rec (a :: e) < n).
     unfold length_rec in Hlen ; simpl in Hlen.
     unfold length_rec => //=. lia.
     apply IHn in H.
     unfold to_val0 in H.
     destruct (merge_values _) => //.
     destruct v => //.
     destruct e0 => //. 
  - unfold to_val0 => /=. rewrite merge_prepend => /=.
    destruct e => //.
    assert (length_rec (a :: e) < n).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec => //=. lia.
    apply IHn in H.
    unfold to_val0 in H.
    destruct (merge_values _) => //.
    destruct v => //.
    destruct e1 => //. 
  - unfold to_val0 => /=. rewrite merge_prepend => /=.
    destruct e => //.
    assert (length_rec (a :: e) < n).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec => //=. lia.
    apply IHn in H.
    unfold to_val0 in H.
    destruct (merge_values _) => //.
    destruct v => //.
    destruct e0 => //.
  - unfold to_val0 => /=. rewrite merge_throw => //=. 
  - unfold to_val0 => /=. rewrite merge_suspend => //=.
  - unfold to_val0 => /=. rewrite merge_switch => //=.
  - unfold to_val0.
    simpl. 
    destruct l0; first by rewrite merge_notval.
    assert (length_rec (a :: l0) < n).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec.
    rewrite map_cons.
    simpl.
    lia.
    apply IHn in H.
    unfold is_none_or in H.
    unfold to_val0 in H.
    destruct (merge_values _) => //.
    2: destruct e0.
    destruct v => //.
    all: try by rewrite merge_notval.
    + rewrite merge_br => //=.
    + rewrite merge_return => //=.
    + rewrite merge_call_host => //=.
    + rewrite merge_suspend => //=.
    + rewrite merge_switch => //=.
    + destruct (exnelts_of_exception_clauses _ _) eqn:Hexnelts => //.
      rewrite merge_throw => //=.
      rewrite merge_notval => //. 
  - unfold to_val0.
    simpl.
    destruct l1 ; first by rewrite merge_notval.
    assert (length_rec (a :: l1) < n).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec.
    rewrite map_cons.
    simpl.
    lia.
    apply IHn in H.
    unfold is_none_or in H.
    unfold to_val0 in H.
    destruct (merge_values _) => //.
    2: destruct e0.
    destruct v => //.
    all: try by rewrite merge_notval.
    + rewrite merge_br => //=.
    + rewrite merge_return => //=.
    + rewrite merge_call_host => //=.
    + destruct (suselts_of_continuation_clauses _ _) => //.
      rewrite merge_suspend => //=.
      rewrite merge_notval => //. 
    + destruct (swelts_of_continuation_clauses _ _) => //. 
      rewrite merge_switch => //=.
      rewrite merge_notval => //. 
    + rewrite merge_throw => //=.
  - unfold to_val0.
    simpl.
    destruct l0 ; first by rewrite merge_notval.
    assert (length_rec (a :: l0) < n).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec.
    rewrite map_cons.
    simpl.
    lia.
    apply IHn in H.
    unfold is_none_or in H.
    unfold to_val0 in H.
    destruct (merge_values _) => //.
    2: destruct e0.
    destruct v => //.
    all: try by rewrite merge_notval.
    + destruct i.
      2: destruct (vh_decrease _) eqn:Hdecr => //=.
      all: try rewrite merge_notval => //. 
      rewrite merge_br => //=.
    + rewrite merge_return => //=.
    + rewrite merge_call_host => //=.
    + rewrite merge_suspend => //=.
    + rewrite merge_switch => //=.
    + rewrite merge_throw => //=.
  - unfold to_val0 => //=.
    destruct (merge_values (map _ l)) eqn:Hmerge => //.
    2: destruct e0.
    destruct v => //.
    all: try by rewrite merge_notval.
    rewrite merge_call_host => //.
    rewrite merge_suspend => //.
    rewrite merge_switch => //.
    rewrite merge_throw => //. 
  - unfold to_val0 => //=.
    rewrite merge_call_host => //=.
Qed.
    
Lemma to_val_trap_is_singleton : ∀ e,
    to_val0 e = Some trapV -> e = [::AI_trap].
Proof.
  intro e.
  destruct e => //=.
  destruct a => //=.
  destruct b => //= ; unfold to_val0 => /=.
  all: try by rewrite /to_val0 /= merge_notval.
  - by rewrite merge_br.
  - by rewrite merge_return.
  - rewrite merge_prepend.
    destruct (merge_values _) => //=.
    destruct v0 => //=.
    destruct e0 => //=. 
  - rewrite merge_prepend.
    destruct (merge_values _) => //=.
    destruct v => //.
    destruct e0 => //.
(*  - rewrite merge_ThrowRef => //. *)
  - rewrite /to_val0 /= merge_trap.
    destruct e => //=. 
    rewrite of_to_val_instr => //=.
  - unfold to_val0 => /=. rewrite merge_prepend.
    destruct (merge_values _) => //=.
    destruct v => //=.
    destruct e0 => //. 
  - unfold to_val0 => /=. rewrite merge_prepend.
    destruct (merge_values _) => //=.
    destruct v => //.
    destruct e1 => //. 
  - unfold to_val0 => /=. rewrite merge_prepend.
    destruct (merge_values _) => //=.
    destruct v => //.
    destruct e0 => //.
  - rewrite /to_val0 /= merge_throw => //. 
  - unfold to_val0 => //=.
    rewrite merge_suspend => //=.
  - unfold to_val0 => /=; rewrite merge_switch => //.
  - unfold to_val0 => /=.
    destruct (merge_values (map _ l0)) => //=.
    2: destruct e0.
    destruct v => //=.
    all: try by rewrite merge_notval.
    rewrite merge_br => //=.
    rewrite merge_return => //=.
    rewrite merge_call_host => //=.
    rewrite merge_suspend => //.
    rewrite merge_switch => //.
    destruct (exnelts_of_exception_clauses _ _) => //.
    rewrite merge_throw => //.
    rewrite merge_notval => //. 
  - unfold to_val0 => /=.
    destruct (merge_values (map _ _)) => //=.
    2: destruct e0.
    destruct v => //=.
    all: try by rewrite merge_notval.
    rewrite merge_br => //=.
    rewrite merge_return => //=.
    rewrite merge_call_host => //=.
    destruct (suselts_of_continuation_clauses _ _) => //. 
    rewrite merge_suspend => //.
    rewrite merge_notval => //. 
    destruct (swelts_of_continuation_clauses _ _) => //. 
    rewrite merge_switch => //.
    rewrite merge_notval => //. 
    rewrite merge_throw => //. 
  - unfold to_val0 => /=.
    destruct (merge_values (map _ _)) => //=.
    2: destruct e0.
    destruct v => //=.
    all: try by rewrite merge_notval.
    destruct i => //=.
    2: destruct (vh_decrease _) => //=.
    all: try by rewrite merge_notval.
    rewrite merge_br => //=.
    rewrite merge_return => //=.
    rewrite merge_call_host => //=.
    rewrite merge_suspend => //.
    rewrite merge_switch => //.
    rewrite merge_throw => //.
  - unfold to_val0 => //=.
    destruct (merge_values (map _ _)) => //.
    2: destruct e0 => //. 
    destruct v => //.
    all: try by rewrite merge_notval.
    rewrite merge_call_host => //.
    rewrite merge_suspend => //.
    rewrite merge_switch => //. 
    rewrite merge_throw => //.
  - unfold to_val0 => //= ; rewrite merge_call_host => /=.
    destruct (flatten _) => //=.
Qed. 


Lemma flatten_map_expr_of_val_not_val vs :
  flatten (map expr_of_val_not_val vs) =
    expr_of_val_not_val (merge_values vs).
Proof.
  induction vs => //=.
  destruct a => //=.
  all: rewrite IHvs.
  all: rewrite merge_prepend.
  all: by rewrite val_not_val_combine_app.
Qed.

Lemma merge_app vs1 vs2:
  merge_values (vs1 ++ vs2) =
    val_not_val_combine (merge_values vs1) (merge_values vs2).
Proof.
  induction vs1 => //=.
  { destruct (merge_values vs2) => //.
    destruct v => //.
    by rewrite vh_push_const_nil.
    by rewrite sh_push_const_nil.
    by rewrite llh_push_const_nil.
    destruct e => //. 
    by rewrite sus_push_const_nil.
    by rewrite sw_push_const_nil.
    by rewrite exn_push_const_nil.
  }
  do 2 rewrite merge_prepend.
  rewrite IHvs1.
  rewrite val_not_val_combine_assoc.
  done.
Qed. 

Lemma to_val_is_immV es vs :
  to_val0 es = Some (immV vs) -> es = map (λ x, AI_const x) vs.
Proof.
  generalize dependent vs.
  induction es => //=.
  intros.
  unfold to_val0 in H.
  simpl in H.
  inversion H => //=.

  intros.
  unfold to_val0 in H ; simpl in H.
  destruct (to_val_instr a) eqn:Ha => //.
  3: by rewrite merge_notval in H.
(*  3: by rewrite merge_ThrowRef in H. *)
(*  3: by rewrite merge_Suspend in H. *)
(*  3: by rewrite merge_Switch in H. *)
  2: destruct e => //=.
  2: by rewrite merge_suspend in H.
  2: by rewrite merge_switch in H.
  2: by rewrite merge_throw in H.
  rewrite merge_prepend in H.
  unfold to_val0 in IHes.
  destruct (merge_values _) => //.
  - destruct v, v0 => //.
    + simpl in H.
      inversion H ; subst.
      erewrite IHes => //.
      destruct a => //.
      destruct b => //.
      all: try by inversion Ha.
      all: simpl in Ha.
      all: destruct (merge_values _) => //.
      all: try destruct v => //.
      all: try destruct e => //. 
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
  - destruct v, e => //. 
    + simpl in H.
      destruct (susfill _ _ _) => //.
    + simpl in H.
      destruct (swfill _ _ _) => //.
    + simpl in H.
      destruct (exnfill _ _ _) => //. 
  - destruct v => //.
    destruct e => //.
(*  - destruct v => //=.
    unfold val_not_val_combine in H.
    destruct (separate_last l) as [[??]|] => //.
    destruct v => //.
    destruct v => //.
  - destruct v => //.
    simpl in H. destruct (separate_last _) as [[??]|] => //.
    destruct v => //. destruct v => //. *)
(*  - destruct v => //.
    simpl in H. destruct (separate_last _) as [[??]|] => //.
    destruct v => //. destruct v => //. *)
Qed.




Lemma merge_is_NotVal  es es' :
  merge_values (map to_val_instr es) = NotVal es' ->
   es = es'.
Proof.
  generalize dependent es'.
  induction es => //= ; intro es'.
  destruct (to_val_instr a) eqn:Ha => //=.
  - destruct a => //= ; simpl in Ha.
    + destruct b => //= ; inversion Ha ; subst.
      * by rewrite merge_br.
      * by rewrite merge_return.
      * rewrite merge_prepend.
        destruct (merge_values _) eqn:Hmerge => //=.
        -- destruct v => //=.
           intro H ; inversion H ; subst.
           rewrite (to_val_trap_is_singleton (e := es)) => //.
           unfold to_val0 ; by rewrite Hmerge.
        -- destruct e => //.
        -- intro H ; inversion H.
           by erewrite IHes.
(*        -- intro H; inversion H.
           apply merge_is_ThrowRef in Hmerge as -> => //.
(*        -- intro H; inversion H.
           apply merge_is_Suspend in Hmerge as -> => //. *)
        -- intro H; inversion H.
           apply merge_is_Switch in Hmerge as -> => //.  *)
      * rewrite merge_prepend.
         destruct (merge_values _) eqn:Hmerge => //=.
        -- destruct v => //=.
           intro H ; inversion H ; subst.
           rewrite (to_val_trap_is_singleton (e := es)) => //.
           unfold to_val0 ; by rewrite Hmerge.
        -- destruct e => //.
        -- intro H ; inversion H.
           by erewrite IHes.
(*        -- intro H; inversion H.
           apply merge_is_ThrowRef in Hmerge as -> => //.
(*        -- intro H; inversion H.
           apply merge_is_Suspend in Hmerge as -> => //. *)
        -- intro H; inversion H.
           apply merge_is_Switch in Hmerge as -> => //. *)
    + inversion Ha; subst v.
      rewrite merge_trap => //=.
      rewrite flatten_simplify.
      destruct es => //=.
      intro H; inversion H; subst. done.
    + inversion Ha; subst.
      rewrite merge_prepend.
       destruct (merge_values _) eqn:Hmerge => //=.
        -- destruct v => //=.
           intro H ; inversion H ; subst.
           rewrite (to_val_trap_is_singleton (e := es)) => //.
           unfold to_val0 ; by rewrite Hmerge.
        -- destruct e => //.
        -- intro H ; inversion H.
           by erewrite IHes.
(*        -- intro H; inversion H.
           apply merge_is_ThrowRef in Hmerge as -> => //.
(*        -- intro H; inversion H.
           apply merge_is_Suspend in Hmerge as -> => //. *)
        -- intro H; inversion H.
           apply merge_is_Switch in Hmerge as -> => //. *)
    + inversion Ha; subst v.
      rewrite merge_prepend.
       destruct (merge_values _) eqn:Hmerge => //=.
        -- destruct v => //=.
           intro H ; inversion H ; subst.
           rewrite (to_val_trap_is_singleton (e := es)) => //.
           unfold to_val0 ; by rewrite Hmerge.
        -- destruct e0 => //.
        -- intro H ; inversion H.
           by erewrite IHes.
(*        -- intro H; inversion H.
           apply merge_is_Suspend in Hmerge as -> => //. *)
(*        -- intro H; inversion H.
           apply merge_is_Switch in Hmerge as -> => //. *)
    + inversion Ha; subst v.
      rewrite merge_prepend.
      destruct (merge_values _) eqn:Hmerge => //=.
        -- destruct v => //=.
           intro H ; inversion H ; subst.
           rewrite (to_val_trap_is_singleton (e := es)) => //.
           unfold to_val0 ; by rewrite Hmerge.
        -- destruct e => //.
        -- intro H ; inversion H.
           by erewrite IHes.
(*        -- intro H; inversion H.
           apply merge_is_ThrowRef in Hmerge as -> => //. *)
    + destruct (merge_values (map _ l0)) eqn:Hmerge => //.
      2: destruct e => //.
      destruct v0 => //; try (inversion Ha; subst v).
      * rewrite merge_br => //.
      * rewrite merge_return => //.
      * rewrite merge_call_host => //.
      * destruct (exnelts_of_exception_clauses _ _) => //.
    + destruct (merge_values (map _ l1)) eqn:Hmerge => //.
      2: destruct e => //.
      destruct v0 => //; try (inversion Ha; subst v).
      * rewrite merge_br => //.
      * rewrite merge_return => //.
      * rewrite merge_call_host => //.
      * destruct (suselts_of_continuation_clauses _ _) => //.
      * destruct (swelts_of_continuation_clauses _ _) => //.
    + destruct (merge_values (map _ l0)) eqn:Hmerge => //.
      2: destruct e => //. 
      destruct v0 => //; try (inversion Ha; subst v).
      * destruct i => //.
        destruct (vh_decrease _) => //.
        inversion Ha; subst v.
        rewrite merge_br => //.
      * rewrite merge_return => //.
      * rewrite merge_call_host => //.
    + destruct (merge_values (map _ l)) eqn:Hmerge => //.
      2: destruct e => //. 
      destruct v0 => //; try (inversion Ha; subst v).
      rewrite merge_call_host => //.
    + inversion Ha; subst v.
      rewrite merge_call_host => //.
  - destruct e => //=.
    + rewrite merge_suspend => //.
    + rewrite merge_switch => //.
    + rewrite merge_throw => //. 
  - rewrite merge_notval => //=.
    rewrite flatten_map_expr_of_val_not_val.
    rewrite merge_to_val.
    intros H; inversion H.
    destruct a => //=.
    destruct b => //=.
    all: try by inversion Ha; subst.
    + simpl in Ha.
      destruct (merge_values (map _ l0)) eqn:Hmerge => //.
      all: try by inversion Ha; subst.
      * destruct v => //; inversion Ha; subst => //.
      * destruct e0 => //.
        destruct (exnelts_of_exception_clauses _ _) => //.
        inversion Ha; subst => //.
    + simpl in Ha.
      destruct (merge_values (map _ l1)) eqn:Hmerge => //.
      all: try by inversion Ha; subst.
      * destruct v => //; inversion Ha; subst => //.
      * destruct e0 => //.
        -- destruct (suselts_of_continuation_clauses _ _) => //.
           inversion Ha; subst => //.
        -- destruct (swelts_of_continuation_clauses _ _) => //.
           inversion Ha; subst => //.
    + simpl in Ha.
      destruct (merge_values (map _ l0)) eqn:Hmerge => //.
      all: try by inversion Ha; subst.
      * destruct v => //.
        all: try by inversion Ha; subst => //.
        destruct i => //; try by inversion Ha; subst => //.
        destruct (vh_decrease _) => //.
        inversion Ha; subst => //. 
      * destruct e0 => //.
    + simpl in Ha.
      destruct (merge_values (map _ l)) eqn:Hmerge => //.
      all: try by inversion Ha; subst.
      * destruct v => //; inversion Ha; subst => //.
      * destruct e0 => //=. 
(*  - rewrite merge_ThrowRef => //.
(*  - rewrite merge_Suspend => //. *)
  - rewrite merge_Switch => //.  *)
Qed.     



Lemma extend_retV sh es :
  to_val0 (of_val0 (retV sh) ++ es) = Some (retV (sh_append sh es)).
Proof.
  unfold to_val0.
  rewrite map_app.
  rewrite merge_app.
  specialize (to_of_val0 (retV sh)) as H.
  unfold to_val0 in H.
  destruct (merge_values _) => //.
  inversion H => /=.
  destruct (merge_values _) eqn:Hmerge => //=.
  - erewrite of_to_val0.
    done.
    unfold to_val0.
    by rewrite Hmerge.
  - erewrite of_to_eff0.
    done.
    unfold to_eff0.
    by rewrite Hmerge.
  - by apply merge_is_NotVal in Hmerge ; subst.
(*  - by apply merge_is_ThrowRef in Hmerge; subst.
(*  - by apply merge_is_Suspend in Hmerge; subst. *)
  - by apply merge_is_Switch in Hmerge; subst. *)
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
    to_val0 e1 = None /\ to_eff0 e1 = None 
    ∨ (vs = [] ∧ to_val0 e1 = Some trapV)
(*    \/ (vs = [] /\ e1 = AI_basic BI_throw_ref :: es)
    \/ (∃ vs' v, separate_last vs = Some (vs', v) /\ (forall a i, v <> VAL_ref (VAL_ref_exn a i)) /\ e1 = v_to_e_list vs ++ AI_basic BI_throw_ref :: es) *)
    ∨ (∃ i, e = AI_basic (BI_br i) ∧ to_val0 e1 = Some (brV (VH_base i vs es)))
    ∨ (e = AI_basic BI_return ∧ to_val0 e1 = Some (retV (SH_base vs es)))
    \/ (∃ tf h vcs, e = AI_call_host tf h vcs /\ to_val0 e1 = Some (callHostV tf h vcs ((LL_base vs es))))
    \/ (∃ bef i, e = AI_suspend_desugared bef i /\ to_eff0 e1 = Some (susE bef i (SuBase vs es)))
    \/ (∃ bef k tf i, e = AI_switch_desugared bef k tf i /\ to_eff0 e1 = Some (swE bef k tf i (SwBase vs es)))
    \/ (∃ bef a i, e = AI_throw_ref_desugared bef a i /\ to_eff0 e1 = Some (thrE bef a i (ExBase vs es)))
    \/ (∃ i n es' LI (vh : valid_holed i),
          e = AI_label n es' LI /\ to_val0 e1 = Some (brV (VH_rec vs n es' vh es))
          /\ vfill vh [AI_basic (BI_br (S i))] = LI)
    \/ (∃ n es' LI sh, e = AI_label n es' LI /\ to_val0 e1 = Some (retV (SH_rec vs n es' sh es))
                      /\ sfill sh [AI_basic BI_return] = LI)
    \/ (∃ tf h vcs n es' LI sh, e = AI_label n es' LI /\ to_val0 e1 = Some (callHostV tf h vcs ((LL_label vs n es' sh es)))
                               /\ llfill sh [AI_call_host tf h vcs] = LI)
    \/ (∃ bef i n es' LI sh,
          e = AI_label n es' LI /\ to_eff0 e1 = Some (susE bef i (SuLabel vs n es' sh es)) /\
            susfill i sh [AI_suspend_desugared bef i] = LI)
    \/ (∃ bef k tf i n es' LI sh,
          e = AI_label n es' LI /\ to_eff0 e1 = Some (swE bef k tf i (SwLabel vs n es' sh es)) /\
            swfill i sh [AI_switch_desugared bef k tf i] = LI)
    \/ (∃ bef a i n es' LI sh,
          e = AI_label n es' LI /\ to_eff0 e1 = Some (thrE bef a i (ExLabel vs n es' sh es)) /\
            exnfill i sh [AI_throw_ref_desugared bef a i] = LI)
    \/ (∃ i es' LI (vh : valid_holed i),
          e = AI_handler es' LI /\ to_val0 e1 = Some (brV (VH_handler vs es' vh es))
          /\ vfill vh [AI_basic (BI_br i)] = LI)
    \/ (∃ es' LI sh, e = AI_handler es' LI /\ to_val0 e1 = Some (retV (SH_handler vs es' sh es))
                      /\ sfill sh [AI_basic BI_return] = LI)
    \/ (∃ tf h vcs es' LI sh, e = AI_handler es' LI /\ to_val0 e1 = Some (callHostV tf h vcs ((LL_handler vs es' sh es)))
                               /\ llfill sh [AI_call_host tf h vcs] = LI)
    \/ (∃ bef i es' LI sh,
          e = AI_handler es' LI /\ to_eff0 e1 = Some (susE bef i (SuHandler vs es' sh es)) /\
            susfill i sh [AI_suspend_desugared bef i] = LI)
    \/ (∃ bef k tf i es' LI sh,
          e = AI_handler es' LI /\ to_eff0 e1 = Some (swE bef k tf i (SwHandler vs es' sh es)) /\
            swfill i sh [AI_switch_desugared bef k tf i] = LI)
    \/ (∃ bef a i es' LI sh,
          e = AI_handler (map (exception_clause_of_exnelt i) es') LI /\ to_eff0 e1 = Some (thrE bef a i (ExHandler vs es' sh es)) /\
            exnfill i sh [AI_throw_ref_desugared bef a i] = LI)
    \/ (∃ i n es' LI (vh : valid_holed i),
          e = AI_prompt n es' LI /\ to_val0 e1 = Some (brV (VH_prompt vs n es' vh es))
          /\ vfill vh [AI_basic (BI_br i)] = LI)
    \/ (∃ n es' LI sh, e = AI_prompt n es' LI /\ to_val0 e1 = Some (retV (SH_prompt vs n es' sh es))
                      /\ sfill sh [AI_basic BI_return] = LI)
    \/ (∃ tf h vcs n es' LI sh, e = AI_prompt n es' LI /\ to_val0 e1 = Some (callHostV tf h vcs ((LL_prompt vs n es' sh es)))
                               /\ llfill sh [AI_call_host tf h vcs] = LI)
    \/ (∃ bef i n es' LI sh,
          e = AI_prompt n (map (continuation_clause_of_suselt i) es') LI /\ to_eff0 e1 = Some (susE bef i (SuPrompt vs n es' sh es)) /\
            susfill i sh [AI_suspend_desugared bef i] = LI)
    \/ (∃ bef k tf i n es' LI sh,
          e = AI_prompt n (map (continuation_clause_of_swelt i) es') LI /\ to_eff0 e1 = Some (swE bef k tf i (SwPrompt vs n es' sh es)) /\
            swfill i sh [AI_switch_desugared bef k tf i] = LI)
    \/ (∃ bef a i n es' LI sh,
          e = AI_prompt n es' LI /\ to_eff0 e1 = Some (thrE bef a i (ExPrompt vs n es' sh es)) /\
            exnfill i sh [AI_throw_ref_desugared bef a i] = LI)
    \/ (∃ tf h vcs n f LI sh, e = AI_local n f LI /\ to_val0 e1 = Some (callHostV tf h vcs ((LL_local vs n f sh es)))
                             /\ llfill sh [AI_call_host tf h vcs] = LI)
    \/ (∃ bef i n f LI sh, e = AI_local n f LI /\ to_eff0 e1 = Some (susE bef i (SuLocal vs n f sh es)) /\ susfill i sh [AI_suspend_desugared bef i] = LI)
    \/ (∃ bef k tf i n f LI sh, e = AI_local n f LI /\ to_eff0 e1 = Some (swE bef k tf i (SwLocal vs n f sh es)) /\ swfill i sh [AI_switch_desugared bef k tf i] = LI)
    \/ (∃ bef a i n f LI sh, e = AI_local n f LI /\ to_eff0 e1 = Some (thrE bef a i (ExLocal vs n f sh es)) /\ exnfill i sh [AI_throw_ref_desugared bef a i] = LI)
.
Proof.
  intros e1.
  induction e1 ; intros e es vs Hsplit.
  { destruct vs => //. } 
  destruct vs => //.
  { simpl in Hsplit.
    destruct a => // ; try by left; rewrite /to_val0 /to_eff0 /= merge_notval.
    destruct b => // ; simplify_eq;try by left; rewrite /to_val0 /to_eff0 /= merge_notval.
    all: try by destruct (split_vals_e e1); inversion Hsplit.
    all: try (inversion Hsplit; subst e es).
    - (* Br *)
      unfold to_val0 => /=.
      rewrite merge_br flatten_simplify.
      (* right. right. *) right. right. left. 
      eexists. eauto.
    - (* Return *)
      unfold to_val0 => /=.
      rewrite merge_return flatten_simplify.
      (* right. right. *) right. right. right. left.
      eauto.
(*    - (* Throw_ref *)
      left. rewrite /to_val0 /to_eff0 /= merge_ThrowRef => //.  *)
    - (* Trap *)
      destruct e1.
      + right;left;auto.
      + left. 
        unfold to_val0, to_eff0. simpl.
        rewrite merge_trap => //=. 
        destruct (expr_of_val_not_val _) eqn:Ha => //.
        by rewrite of_to_val_instr in Ha.
    - (* Throw_ref *)
      right. right. right. right. right. right. right. left.
      repeat eexists => //.
      rewrite /to_eff0 /= merge_throw flatten_simplify => //. 
    - (* Suspend *)
      right. right. right. right. right. left.
      do 2 eexists. split => //=.
      unfold to_eff0 => //=.
      rewrite merge_suspend => //=.
      rewrite flatten_simplify => //.
    - (* Switch *)
       right. right. right. right. right. right. left.
       repeat eexists => //.
       rewrite /to_eff0 /= merge_switch flatten_simplify => //. 
    - (* Handler *)
      destruct (to_val0 (_ :: _)) eqn:Htv.
      + right. right. right. right.
        right. right. right. right.
        right. right. right. right.
        right. right. (* right. right. *)
        unfold to_val0 in Htv => /=. 
        simpl in Htv.
        destruct (merge_values (map _ l0)) eqn:Hmerge => //.
        2: destruct e. 
        destruct v0 => //.
        all: try by rewrite merge_notval in Htv.
        * (* Br *)
          rewrite merge_br flatten_simplify in Htv.
          inversion Htv; subst.
          left. repeat eexists.
          fold (of_val0 (brV lh)).
          apply of_to_val0.
          unfold to_val0.
          rewrite Hmerge => //.
        * (* Return *)
          rewrite merge_return flatten_simplify in Htv.
          inversion Htv; subst.
          right; left. repeat eexists.
          fold (of_val0 (retV s)).
          apply of_to_val0.
          unfold to_val0.
          rewrite Hmerge => //. 
        * (* Call_host *)
          rewrite merge_call_host flatten_simplify in Htv.
          inversion Htv ; subst.
          right; right; left. repeat eexists.
          fold (of_val0 (callHostV f h l1 l2)).
          apply of_to_val0.
          unfold to_val0.
          rewrite Hmerge => //.
        * (* Suspend *)
          rewrite merge_suspend in Htv => //.
        * (* Switch *)
          rewrite merge_switch in Htv => //.
        * (* Throw_ref *)
          destruct (exnelts_of_exception_clauses _ _) => //. 
          rewrite merge_throw in Htv => //.
          rewrite merge_notval in Htv => //.
      + destruct (to_eff0 (_ :: _)) eqn:Hte; try by left.
        right. right. right. right.
        right. right. right. right.
        right. right. right. right.
        right. right. (* right. right. *)
        unfold to_eff0 in Hte => /=. 
        simpl in Hte.
        destruct (merge_values (map _ l0)) eqn:Hmerge => //.
        2: destruct e0. 
        destruct v => //.
        all: try by rewrite merge_notval in Hte.
        * (* Br *)
          rewrite merge_br in Hte => //.
        * (* Return *)
          rewrite merge_return in Hte => //.
        * (* Call_host *)
          rewrite merge_call_host in Hte => //.
        * (* Suspend *)
          rewrite merge_suspend flatten_simplify in Hte.
          inversion Hte; subst.
          right; right; right; left.
          repeat eexists.
          fold (of_eff0 (susE vs i sh)).
          apply of_to_eff0.
          unfold to_eff0.
          rewrite Hmerge => //.
        * (* Switch *)
          rewrite merge_switch flatten_simplify in Hte.
          inversion Hte; subst.
          right; right; right; right; left.
          repeat eexists.
          fold (of_eff0 (swE vs k tf i sh)).
          apply of_to_eff0.
          unfold to_eff0.
          rewrite Hmerge => //.
        * (* Throw *)
          destruct (exnelts_of_exception_clauses _ _) eqn:Helts => //. 
          rewrite merge_throw flatten_simplify in Hte.
          inversion Hte; subst.
          right; right; right; right; right; left.
          repeat eexists.
          fold (of_eff0 (thrE vs a i sh)).
          apply exnelts_of_exception_clauses_inj in Helts.
          rewrite Helts.
          f_equal.
          symmetry.
          apply of_to_eff0.
          unfold to_eff0.
          rewrite Hmerge => //.
          rewrite merge_notval in Hte => //. 
    - (* Prompt *)
      destruct (to_val0 (_ :: _)) eqn:Htv.
      + right. right. right. right.
        right. right. right. right.
        right. right. right. right.
        right. right. right. right.
        right. right. right. right.
        (*      right. right. *)
        unfold to_val0 in Htv => /=. 
        simpl in Htv.
        destruct (merge_values (map _ l1)) eqn:Hmerge => //.
        2: destruct e.
        destruct v0 => //.
        all: try by rewrite merge_notval in Htv.
        * (* Br *)
          rewrite merge_br flatten_simplify in Htv.
          inversion Htv; subst.
          left. repeat eexists.
          fold (of_val0 (brV lh)).
          apply of_to_val0.
          unfold to_val0.
          rewrite Hmerge => //.
        * (* Return *)
          rewrite merge_return flatten_simplify in Htv.
          inversion Htv; subst.
          right; left. repeat eexists.
          fold (of_val0 (retV s)).
          apply of_to_val0.
          unfold to_val0.
          rewrite Hmerge => //. 
        * (* Call_host *)
          rewrite merge_call_host flatten_simplify in Htv.
          inversion Htv ; subst.
          right; right; left. repeat eexists.
          fold (of_val0 (callHostV f h l2 l3)).
          apply of_to_val0.
          unfold to_val0.
          rewrite Hmerge => //.
        * (* Suspend *)
          destruct (suselts_of_continuation_clauses _ _).
          rewrite merge_suspend in Htv => //.
          rewrite merge_notval in Htv => //.
        * (* Switch *)
          destruct (swelts_of_continuation_clauses _ _).
          rewrite merge_switch in Htv => //.
          rewrite merge_notval in Htv => //.
        * (* Throw *)
          rewrite merge_throw in Htv => //.
      + destruct (to_eff0 (_ :: _)) eqn:Hte; try by left.
        right. right. right. right.
        right. right. right. right.
        right. right. right. right.
        right. right. right. right.
        right. right. right. right.
        (*      right. right. *)
        unfold to_eff0 in Hte => /=. 
        simpl in Hte.
        destruct (merge_values (map _ l1)) eqn:Hmerge => //.
        2: destruct e0.
        destruct v => //.
        all: try by rewrite merge_notval in Hte.
        * (* Br *)
          rewrite merge_br in Hte => //.
        * (* Return *)
          rewrite merge_return in Hte => //.
        * (* Call_host *)
          rewrite merge_call_host in Hte => //. 
        * (* Suspend *)
          destruct (suselts_of_continuation_clauses _ _) eqn:Helts => //. 
          rewrite merge_suspend flatten_simplify in Hte.
          inversion Hte; subst.
          right; right; right; left.
          repeat eexists.
          fold (of_eff0 (susE vs i sh)).
          apply suselts_of_continuation_clauses_inj in Helts.
          rewrite Helts.
          symmetry.
          f_equal.
          apply of_to_eff0.
          unfold to_eff0.
          rewrite Hmerge => //.
          rewrite merge_notval in Hte => //. 
        * (* Switch *)
          destruct (swelts_of_continuation_clauses _ _) eqn:Helts => //.
          2: by rewrite merge_notval in Hte.
          rewrite merge_switch flatten_simplify in Hte.
          inversion Hte; subst.
          right; right; right; right; left.
          repeat eexists.
          fold (of_eff0 (swE vs k tf i sh)).
          apply swelts_of_continuation_clauses_inj in Helts.
          rewrite Helts.
          f_equal. symmetry.
          apply of_to_eff0.
          unfold to_eff0.
          rewrite Hmerge => //.
        * (* Throw *)
          rewrite merge_throw flatten_simplify in Hte.
          inversion Hte; subst.
          right; right; right; right; right; left.
          repeat eexists.
          fold (of_eff0 (thrE vs a i sh)).
          apply of_to_eff0.
          unfold to_eff0.
          rewrite Hmerge => //.
    - (* Label *)
      destruct (to_val0 (_ :: _)) eqn:Htv.
      + right. right. right. right.
        right. right. right. right.
        (*      right. right. *)
        unfold to_val0 in Htv => /=.
        simpl in Htv.
        destruct (merge_values (map _ _)) eqn:Hmerge => //.
        2: destruct e.
        destruct v0 => //.
        all: try by rewrite merge_notval in Htv.
        * (* Br *)
          destruct i => //.
          2: destruct (vh_decrease _) eqn:Hdecr => //.
          all: try by rewrite merge_notval in Htv.
          rewrite merge_br flatten_simplify in Htv.
          inversion Htv ; subst.
          left. repeat eexists _.
          repeat split => //.
          assert (to_val0 l0 = Some (brV lh)).
          unfold to_val0 ; by rewrite Hmerge.
          apply of_to_val0 in H.
          unfold of_val0 in H.
          rewrite - (vfill_decrease _ Hdecr) => //.
        * (* Return *)
          rewrite merge_return flatten_simplify in Htv.
          inversion Htv ; subst.
          right ; left. repeat eexists _.
          repeat split => //.
          assert (to_val0 l0 = Some (retV s)).
          unfold to_val0 ; by rewrite Hmerge.
          apply of_to_val0 in H.
          unfold of_val0 in H => //.
        * (* Call_host *)
          rewrite merge_call_host flatten_simplify in Htv.
          inversion Htv ; subst.
          right ; right. left. repeat eexists _.
          repeat split => //.
          assert (to_val0 l0 = Some (callHostV f h l1 l2)).
          unfold to_val0 ; by rewrite Hmerge.
          apply of_to_val0 in H.
          unfold of_val0 in H => //.
        * (* Suspend *)
          rewrite merge_suspend in Htv => //.
        * (* Switch *)
          rewrite merge_switch in Htv => //.
        * (* Throw *)
          rewrite merge_throw in Htv => //.
      + destruct (to_eff0 (_ :: _)) eqn:Hte; try by left.
        right. right. right. right.
        right. right. right. right.
        (*      right. right. *)
        unfold to_eff0 in Hte => /=.
        simpl in Hte.
        destruct (merge_values (map _ _)) eqn:Hmerge => //.
        2: destruct e0.
        destruct v => //.
        all: try by rewrite merge_notval in Hte.
        * (* Br *)
          destruct i.
          2: destruct (vh_decrease _).
          all: try by rewrite merge_notval in Hte.
          by rewrite merge_br in Hte.
        * (* Return *)
          rewrite merge_return in Hte => //.
        * (* Call_host *)
          rewrite merge_call_host in Hte => //. 
        * (* Suspend *)
          rewrite merge_suspend flatten_simplify in Hte.
          inversion Hte; subst.
          right; right; right; left.
          repeat eexists.
          assert (to_eff0 l0 = Some (susE vs i sh)).
          unfold to_eff0; by rewrite Hmerge.
          apply of_to_eff0 in H.
          unfold of_eff0 in H => //.
        * (* Switch *)
          rewrite merge_switch flatten_simplify in Hte.
          inversion Hte; subst.
          right; right; right; right; left.
          repeat eexists.
          assert (to_eff0 l0 = Some (swE vs k tf i sh)).
          unfold to_eff0; by rewrite Hmerge.
          apply of_to_eff0 in H.
          unfold of_eff0 in H => //.
        * (* Throw *)
          rewrite merge_throw flatten_simplify in Hte.
          inversion Hte; subst.
          right; right; right; right; right; left.
          repeat eexists.
          assert (to_eff0 l0 = Some (thrE vs a i sh)).
          unfold to_eff0; by rewrite Hmerge.
          apply of_to_eff0 in H.
          unfold of_eff0 in H => //. 
        
    - (* Local *)
      destruct (to_val0 (_ :: _)) eqn:Htv.
      + right. right. right. right.
        right. right. right. right.
        right. right. right. right.
        right. right. right. right.
        right. right. right. right.
        right. right. right. right.
        right. right. (* right. right. *)
        unfold to_val0 in Htv => /=. 
        simpl in Htv.
        destruct (merge_values (map _ _)) eqn:Hmerge => //.
        2: destruct e.
        destruct v0 => //.
        all: try by rewrite merge_notval in Htv.
        * (* Call_host *)
          rewrite merge_call_host flatten_simplify in Htv.
          inversion Htv ; subst.
          left. repeat eexists.
          fold (of_val0 (callHostV f0 h l0 l1)).
          apply of_to_val0.
          unfold to_val0.
          rewrite Hmerge => //.
        * (* Suspend *)
          rewrite merge_suspend in Htv => //.
        * (* Switch *)
          rewrite merge_switch in Htv => //.
        * (* Throw *)
          rewrite merge_throw in Htv => //.
      + destruct (to_eff0 (_ :: _)) eqn:Hte; last by left.
        right. right. right. right.
        right. right. right. right.
        right. right. right. right.
        right. right. right. right.
        right. right. right. right.
        right. right. right. right.
        right. right. (* right. right. *)
        unfold to_eff0 in Hte => /=. 
        simpl in Hte.
        destruct (merge_values (map _ _)) eqn:Hmerge => //.
        2: destruct e0.
        destruct v => //.
        all: try by rewrite merge_notval in Hte.
        * (* Call_host *)
          rewrite merge_call_host in Hte => //.
        * (* Suspend *)
          rewrite merge_suspend flatten_simplify in Hte.
          inversion Hte; subst.
          right; left.
          repeat eexists.
          fold (of_eff0 (susE vs i sh)).
          apply of_to_eff0.
          unfold to_eff0.
          rewrite Hmerge => //.
        * (* Switch *)
          rewrite merge_switch flatten_simplify in Hte.
          inversion Hte; subst.
          right; right; left.
          repeat eexists.
          fold (of_eff0 (swE vs k tf i sh)).
          apply of_to_eff0.
          unfold to_eff0.
          rewrite Hmerge => //.
        * (* Throw *)
          rewrite merge_throw flatten_simplify in Hte.
          inversion Hte; subst.
          right; right; right.
          repeat eexists.
          fold (of_eff0 (thrE vs a i sh)).
          apply of_to_eff0.
          unfold to_eff0.
          rewrite Hmerge => //.
    - unfold to_val0 => /=.
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
      [(? & ?)|
         [(? & ?)|
           [(? & ? & ?)|
             [(? & ?) |
               [(?&?&?&?&?)|
                 [(?&?&?&?) |
                   [(? & ? & ? & ? & ? & ?)|
                     [(? & ? & ? & ? & ?)|
                       [(?&?&?&?&?&?&?&?)|
                         [(?&?&?&?&?&?&?)|
                           [(?&?&?&?&?&?&?&?&?&?)|
                             [(? & ? & ? & ? & ? & ? & ? & ? & ? ) |
                               [(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?) |
                                 [(? & ? & ? & ? & ? & ? & ? & ? & ? & ?) |
                                   [(?&?&?&?&?&?&?)|
                                     [(?&?&?&?&?&?)|
                                       [(?&?&?&?&?&?&?&?&?)|
                                         [(? & ? & ? & ? & ? & ? & ? & ?) |
                                           [(? & ? & ? & ? & ? & ? & ? & ? & ? & ?) |
                                             [(? & ? & ? & ? & ? & ? & ? & ? & ?) |
                                               [(?&?&?&?&?&?&?&?)|
                                                 [(?&?&?&?&?&?&?)|
                                                   [(?&?&?&?&?&?&?&?&?&?)|
                                                     [(? & ? & ? & ? & ? & ? & ? & ? & ?) |
                                                       [(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?) |
                                                         [(? & ? & ? & ? & ? & ? & ? & ? & ?) |
                                                           
                                                           [(?&?&?&?&?&?&?&?&?&?) |
                                                           [(? & ? & ? & ? & ? & ? & ? & ? & ?)|
                                                             [(? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?)|
                                                               (? & ? & ? & ? & ? & ? & ? & ? & ? & ?)
         ]]]]]]]]]]]]]]]]]]]]]]]]]]]]](* ]] *) ; 
      unfold to_val0, to_eff0 => /= ; rewrite Ha merge_prepend.
  + (* Not Val *)
    unfold to_val0 in H.
    unfold to_eff0 in H0.
    destruct (merge_values _) eqn:Hmerge; try by left.
(*    all: destruct v0; try by left.
    all: destruct v0; try by left.
    all: simpl.
    all: inversion Hsplit; subst.
    * right. right. right. right. right. right. right. left.
      apply merge_is_ThrowRef in Hmerge as ->.
      simpl in Hsome.
      inversion Hsome; subst.
      repeat eexists.
    * right. right. right. right. right. right. left.
      apply merge_is_Switch in Hmerge as ->.
      simpl in Hsome.
      inversion Hsome; subst.
      repeat eexists. *)
  + (* Trap *)
    left. unfold to_val0 in H0.
    destruct (merge_values _) => //.
    by inversion H0. 
  + (* Br *)
    unfold to_val0 in H0.
    destruct (merge_values _) => //.
    inversion H0 => /=.
    right. right. left. eexists _.
    split => //=. inversion Hsplit ; subst => //. 
  + (* Return *)
    unfold to_val0 in H0. destruct (merge_values _) => //.
    inversion H0 => /=. right. right. right. left.
    split;auto. by inversion Hsplit. 
  + (* Call_host *)
    unfold to_val0 in H0.
    destruct (merge_values _) => //.
    inversion H0 => /=.
    right. right. right. right. left. repeat eexists.
    by inversion Hsplit. by inversion Hsplit.
(*  + (* Throw_ref *)
    unfold to_eff0 in H0.
    destruct (merge_values _) => //.
    inversion H0 => /=.
    right. right. right. right. right. right. right. left.
    repeat eexists.
    by inversion Hsplit. *)
  + (* Suspend *)
    unfold to_eff0 in H0.
    destruct (merge_values _) => //.
    inversion H0 => /=.
    right. right. right. right. right. left. repeat eexists.
    by inversion Hsplit. by inversion Hsplit.
  + (* Switch *)
    unfold to_eff0 in H0.
    destruct (merge_values _) => //.
    inversion H0 => /=.
    right; right; right; right; right; right; left.
    repeat eexists. done.
    by inversion Hsplit.
  + (* Throw *)
    unfold to_eff0 in H0.
    destruct (merge_values _) => //.
    inversion H0 => /=.
    right; right; right; right; right; right; right; left.
    repeat eexists. done.
    by inversion Hsplit.

  + (* Label br *)
    unfold to_val0 in H0.
    destruct (merge_values _) => //.
    inversion H0 => /=.
    right. right. right. right. right. right; right; right; left.
    repeat eexists _. repeat split => //. by inversion Hsplit. 
  + (* Label return *)
    unfold to_val0 in H0.
    destruct (merge_values _) => //.
    inversion H0 => /=. do 9 right.
    left. repeat eexists _. repeat split => //.
    by inversion Hsplit.
    
  + (* Label call_host *)
    unfold to_val0 in H0.
    destruct (merge_values _) => //. 
    inversion H0 => /=. do 10 right. left.
    repeat eexists _. repeat split => //.
    by inversion Hsplit.
  + (* Label suspend *)
    unfold to_eff0 in H0.
    destruct (merge_values _) => //. 
    inversion H0 => /=. do 11 right. left.
    repeat eexists _. repeat split => //.
    by inversion Hsplit.
  + (* Label switch *)
    unfold to_eff0 in H0.
    destruct (merge_values _) => //. 
    inversion H0 => /=. do 12 right. left.
    repeat eexists _. repeat split => //.
    by inversion Hsplit.
  + (* Label throw *)
    unfold to_eff0 in H0.
    destruct (merge_values _) => //. 
    inversion H0 => /=. do 13 right. left.
    repeat eexists _. repeat split => //.
    by inversion Hsplit.
  + (* Handler br *)
    unfold to_val0 in H0.
    destruct (merge_values _) => //.
    inversion H0 => /=.
    do 14 right; left.
    repeat eexists _.
    repeat split => //. by inversion Hsplit. 
  + (* Handler return *)
    unfold to_val0 in H0.
    destruct (merge_values _) => //.
    inversion H0 => /=. do 15 right.
    left. repeat eexists _. repeat split => //.
    by inversion Hsplit.
    
  + (* Handler call_host *)
    unfold to_val0 in H0.
    destruct (merge_values _) => //. 
    inversion H0 => /=. do 16 right. left.
    repeat eexists _. repeat split => //.
    by inversion Hsplit.
  + (* Handler suspend *)
    unfold to_eff0 in H0.
    destruct (merge_values _) => //. 
    inversion H0 => /=. do 17 right. left.
    repeat eexists _. repeat split => //.
    by inversion Hsplit.
  + (* Handler switch *)
    unfold to_eff0 in H0.
    destruct (merge_values _) => //. 
    inversion H0 => /=. do 18 right. left.
    repeat eexists _. repeat split => //.
    by inversion Hsplit.
  + (* Handler throw *)
    unfold to_eff0 in H0.
    destruct (merge_values _) => //. 
    inversion H0 => /=. do 19 right. left.
    repeat eexists _. repeat split => //.
    by inversion Hsplit.
  + (* Prompt br *)
    unfold to_val0 in H0.
    destruct (merge_values _) => //.
    inversion H0 => /=.
    do 20 right; left.
    repeat eexists _.
    repeat split => //. by inversion Hsplit. 
  + (* Prompt return *)
    unfold to_val0 in H0.
    destruct (merge_values _) => //.
    inversion H0 => /=. do 21 right.
    left. repeat eexists _. repeat split => //.
    by inversion Hsplit.
    
  + (* Prompt call_host *)
    unfold to_val0 in H0.
    destruct (merge_values _) => //. 
    inversion H0 => /=. do 22 right. left.
    repeat eexists _. repeat split => //.
    by inversion Hsplit.
  + (* Prompt suspend *)
    unfold to_eff0 in H0.
    destruct (merge_values _) => //. 
    inversion H0 => /=. do 23 right. left.
    repeat eexists _. repeat split => //.
    by inversion Hsplit.
  + (* Prompt switch *)
    unfold to_eff0 in H0.
    destruct (merge_values _) => //. 
    inversion H0 => /=. do 24 right. left.
    repeat eexists _. repeat split => //.
    by inversion Hsplit.
  + (* Prompt throw *)
    destruct H0 as [H0 ?].
    unfold to_eff0 in H0.
    destruct (merge_values _) => //. 
    inversion H0 => /=. do 25 right. left.
    repeat eexists _. repeat split => //.
    by inversion Hsplit.
    
    
  + (* Local return *)
    unfold to_val0 in H0. destruct (merge_values _) => //.
    inversion H0 => /=. do 26 right. left.
    repeat eexists _. repeat split => //.
    by inversion Hsplit.
  + (* Local suspend *)
    unfold to_eff0 in H0.
    destruct (merge_values _) => //. 
    inversion H0 => /=. do 27 right. left.
    repeat eexists _. repeat split => //.
    by inversion Hsplit.
  + (* Local switch *)
    unfold to_eff0 in H0.
    destruct (merge_values _) => //. 
    inversion H0 => /=. do 28 right. left.
    repeat eexists _. repeat split => //.
    by inversion Hsplit.
  + (* Local throw *)
    unfold to_eff0 in H0.
    destruct (merge_values _) => //. 
    inversion H0 => /=. do 29 right.
    repeat eexists _. repeat split => //.
    by inversion Hsplit.

Qed.

Lemma to_val_None_prepend: forall es1 es2,
    to_val0 es2 = None ->
    to_val0 (es1 ++ es2) = None 
    ∨ (∃ i (vh : valid_holed i), to_val0 es1 = Some (brV vh))
    ∨ (∃ sh, to_val0 es1 = Some (retV sh))
    \/ (∃ tf h cvs sh, to_val0 es1 = Some (callHostV tf h cvs sh))
(*    \/ (∃ i sh, to_eff0 es1 = Some (susE i sh))
    \/ (∃ k tf i sh, to_eff0 es1 = Some (swE k tf i sh))
    \/ (∃ a i sh, to_eff0 es1 = Some (thrE a i sh))
    \/ (∃ vs a i es, es1 = v_to_e_list (vs ++ [::VAL_ref (VAL_ref_exn a i)]) /\
                      es2 = AI_basic BI_throw_ref :: es)
    \/ (∃ vs k tf i es, es1 = v_to_e_list (vs ++ [::VAL_ref (VAL_ref_cont k)]) /\
                    es2 = AI_switch_desugared tf i :: es) *)
.
Proof.
  move => es1 es2 H.
  induction es1;try by left.
  destruct a;try by left; rewrite /to_val0 /= merge_notval.
  destruct b; try by left; rewrite /to_val0 /= merge_notval.
  - right ; left.
    unfold to_val0 => /=.
    rewrite merge_br flatten_simplify.
    eauto.
  - right ; right.
    unfold to_val0 => /=.
    rewrite merge_return flatten_simplify.
    eauto.
  - destruct IHes1 as [?|[[?[??]]|[[??]|(* [*) (?&?&?&?&?) ]]] (* | [(?&?&?)|[(?&?&?&?)|[(?&?&?&?) | (?&?&?&?&?&?)]]]]]]] *).
    + simpl. unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //=.
      destruct e => //=.
      all: try by left.
    + right;left. eexists _, (vh_push_const _ _). unfold to_val0 => /=.
      rewrite merge_prepend. unfold to_val0 in H0.
      destruct (merge_values _) ; try done.
      inversion H0 => //=. 
    + right;right. left. unfold to_val0 => /=.
      rewrite merge_prepend.  unfold to_val0 in H0.
      destruct (merge_values _) => //.  inversion H0 => //=.
      by repeat eexists. 
    + right;right; right (* ; left *) .
      unfold to_val0 => /=. rewrite merge_prepend. unfold to_val0 in H0.
      destruct (merge_values _) => //. inversion H0 => //=.
      by repeat eexists.
(*    + right; right; right; right; left.
      unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right. left.
      unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right; right. left.
      unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //.
      inversion H0 => //=. by repeat eexists.
    + repeat right. subst. repeat eexists.
      instantiate (3:= VAL_num v :: _).
      simpl. done. *)
  - destruct IHes1 as [?|[[?[??]]|[[??]|(* [ *) (?&?&?&?&?) ]]] (* | [(?&?&?)|[(?&?&?&?)|[(?&?&?&?) | (?&?&?&?&?&?)]]]]]]] *) .
    + simpl. unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //=.
      destruct e.
      all: by left. 
    + right;left. eexists _, (vh_push_const _ _). unfold to_val0 => /=.
      rewrite merge_prepend. unfold to_val0 in H0.
      destruct (merge_values _) ; try done. inversion H0 => //=. 
    + right;right. left. unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0.
      destruct (merge_values _) => //.  inversion H0 => //=.
      by repeat eexists. 
    + right;right; right (*; left *) . unfold to_val0 => /=.
      rewrite merge_prepend. unfold to_val0 in H0.
      destruct (merge_values _) => //. inversion H0 => //=.
      by repeat eexists.
(*    + right; right; right; right; left.
      unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right. left.
      unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right; right. left.
      unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //.
      inversion H0 => //=. by repeat eexists.
    + repeat right. subst. repeat eexists.
      instantiate (3:= VAL_ref (VAL_ref_null r) :: _).
      simpl. done.       *)
(*  - unfold to_val0 => /=.
    rewrite merge_ThrowRef => //=. by left. *)
  - rewrite /to_val0 /= merge_trap => /=.
    rewrite flatten_simplify.
    destruct (es1 ++ es2) eqn:Habs => //.
    apply app_eq_nil in Habs as [-> ->].
    destruct IHes1 as [Habs | [ (? & ? & Habs) | [ [ ? Habs ] | (* [ *) (?&?&?&?& Habs) ]]] (* | [(?&?&Habs)|[(? &?&?&Habs)|[(?&?&?&Habs) | (?&?&?&?&?&Habs)]] ]]]]] *) ; by inversion Habs.
    by left.
  - destruct IHes1 as [?|[[?[??]]|[[??]|(* [ *)(?&?&?&?&?) ]]] (* | [(?&?&?)|[(?&?&?&?)|[(?&?&?&?) | (?&?&?&?&?&?)]]]]]]] *).
    + simpl. unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //=.
      destruct e.
      all: by left. 
    + right;left. eexists _, (vh_push_const _ _). unfold to_val0 => /=.
      rewrite merge_prepend. unfold to_val0 in H0.
      destruct (merge_values _) ; try done. inversion H0 => //=. 
    + right;right. left. unfold to_val0 => /=.
      rewrite merge_prepend.  unfold to_val0 in H0.
      destruct (merge_values _) => //.  inversion H0 => //=.
      by repeat eexists. 
    + right;right; right (*; left *) .
      unfold to_val0 => /=. rewrite merge_prepend. unfold to_val0 in H0.
      destruct (merge_values _) => //. inversion H0 => //=.  by repeat eexists.
(*    + right; right; right; right; left.
      unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right. left.
      unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right; right. left.
      unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //.
      inversion H0 => //=. by repeat eexists.
    + repeat right. subst. repeat eexists.
      instantiate (3:= VAL_ref (VAL_ref_func f) :: _).
      simpl. done. *)
  - destruct IHes1 as [?|[[?[??]]|[[??]|(* [ *) (?&?&?&?&?) ]]] (* | [(?&?&?)|[(?&?&?&?)|[(?&?&?&?) | (?&?&?&?&?&?)]]]]]]] *).
    + simpl. unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) eqn:Hmerge => //=.
      destruct e0.
      all: try by left.
(*      apply merge_is_throw_ref in Hmerge.
      destruct es1.
      * repeat right.
        repeat eexists.
        instantiate (3 := [::]) => //.
        exact Hmerge.
      * inversion Hmerge; subst a e0.
        right; right; right; right; right; right. left.
        repeat eexists.
        simpl. rewrite merge_throw. done. *)
    + right;left. eexists _, (vh_push_const _ _). unfold to_val0 => /=.
      rewrite merge_prepend. unfold to_val0 in H0.
      destruct (merge_values _) ; try done. inversion H0 => //=. 
    + right;right. left. unfold to_val0 => /=. rewrite merge_prepend.  unfold to_val0 in H0.
      destruct (merge_values _) => //.  inversion H0 => //=.
      by repeat eexists. 
    + right;right; right(* ; left *).
      unfold to_val0 => /=. rewrite merge_prepend. unfold to_val0 in H0.
      destruct (merge_values _) => //. inversion H0 => //=.
      by repeat eexists.
(*    + right; right; right; right; left.
      unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right. left.
      unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right; right. left.
      unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //.
      inversion H0 => //=. by repeat eexists.
    + repeat right. subst. repeat eexists.
      instantiate (3:= VAL_ref (VAL_ref_exn e t) :: _).
      simpl. done. *)
  - destruct IHes1 as [?|[[?[??]]|[[??]|(* [ *) (?&?&?&?&?) ]]] (* | [(?&?&?)|[(?&?&?&?)|[(?&?&?&?) | (?&?&?&?&?&?)]]]]]]] *) .
    + simpl. unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //=.
      destruct e.
      all: by left. 
    + right;left. eexists _, (vh_push_const _ _). unfold to_val0 => /=.
      rewrite merge_prepend. unfold to_val0 in H0.
      destruct (merge_values _) ; try done. inversion H0 => //=. 
    + right;right. left. unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0.
      destruct (merge_values _) => //.  inversion H0 => //=.
      by repeat eexists. 
    + right;right; right (*; left*) . unfold to_val0 => /=.
      rewrite merge_prepend. unfold to_val0 in H0.
      destruct (merge_values _) => //. inversion H0 => //=.
      by repeat eexists.
(*    + right; right; right; right; left.
      unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right. left.
      unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //.
      inversion H0 => //=. by repeat eexists.
    + right; right; right; right; right; right. left.
      unfold to_val0 => /=. rewrite merge_prepend.
      unfold to_val0 in H0. destruct (merge_values _) => //.
      inversion H0 => //=. by repeat eexists.
    + repeat right. subst. repeat eexists.
      instantiate (3:= VAL_ref (VAL_ref_cont f) :: _).
      simpl. done. *)
  - rewrite /to_val0 /= merge_throw => //.
    by left.
  - rewrite /to_val0 /= merge_suspend => //.
    by left.
  - rewrite /to_val0 /= merge_switch => //.
    by left.
(*  - right; right; right; right; left.
    unfold to_val0 => /=. rewrite merge_suspend.
    repeat eexists.
  - right; right; right; right; right; left.
    unfold to_val0 => /=. rewrite merge_switch.
    repeat eexists. *)
  - unfold to_val0 => /=.
    destruct (merge_values (map _ l0)) eqn:Hmerge => //.
    2: destruct e.
    destruct v => //.
    all: try by rewrite merge_notval; left.
    + right ; left.
      rewrite merge_br flatten_simplify.
      by repeat eexists.
    + right ; right. left.
      rewrite merge_return flatten_simplify.
      by eexists.
    + right ; right ; right (*; left *) .
      rewrite merge_call_host flatten_simplify.
      by repeat eexists.
    + rewrite merge_suspend; left => //.
    + rewrite merge_switch; left => //.
    + destruct (exnelts_of_exception_clauses _ _).
      rewrite merge_throw; left => //.
      rewrite merge_notval; left => //. 
(*    + right; right; right; right; left.
      rewrite merge_suspend flatten_simplify.
      by repeat eexists.
    + right; right; right; right; right; left.
      rewrite merge_switch flatten_simplify.
      by repeat eexists.
    + destruct (exnelts_of_exception_clauses _ _) eqn:Helts.
      * right; right; right; right; right; right; left.
        rewrite merge_throw flatten_simplify.
        by repeat eexists.
      * by left. *)
  - unfold to_val0 => /=.
    destruct (merge_values (map _ l1)) eqn:Hmerge => // ; try by left.
    2: destruct e.
    destruct v => //.
    all: try by left; rewrite merge_notval.
    + right ; left.
      rewrite merge_br flatten_simplify.
      by repeat eexists.
    + right ; right. left.
      rewrite merge_return flatten_simplify.
      by eexists.
    + right ; right ; right (*; left *).
      rewrite merge_call_host flatten_simplify.
      by repeat eexists.
    + destruct (suselts_of_continuation_clauses _ _).
      rewrite merge_suspend; left => //.
      rewrite merge_notval; left => //.
    + destruct (swelts_of_continuation_clauses _ _).
      rewrite merge_switch; left => //.
      rewrite merge_notval; left => //.
    + rewrite merge_throw; left => //. 
(*    + destruct (suselts_of_continuation_clauses _ _) ; last by left.
      right; right; right; right; left.
      rewrite merge_suspend flatten_simplify.
      by repeat eexists.
    + destruct (swelts_of_continuation_clauses _ _); last by left.
      right; right; right; right; right; left.
      rewrite merge_switch flatten_simplify.
      by repeat eexists.
    + right; right; right; right; right; right; left.
      rewrite merge_throw flatten_simplify.
      by repeat eexists. *)
  - unfold to_val0 => /=.
    destruct (merge_values (map _ _)) eqn:Hmerge => // ; try by left.
    2: destruct e.
    destruct v => //.
    all: try by rewrite merge_notval; left.
    + destruct i.
      2: destruct (vh_decrease _).
      all: try by left; rewrite merge_notval.
      right ; left.
      rewrite merge_br flatten_simplify.
      by repeat eexists.
    + right ; right. left.
      rewrite merge_return flatten_simplify.
      by eexists.
    + right ; right ; right (*; left *) . 
      rewrite merge_call_host flatten_simplify.
      by repeat eexists.
    + rewrite merge_suspend ; left => //.
    + rewrite merge_switch; left => //.
    + rewrite merge_throw; left => //. 
(*    + right; right; right; right; left.
      rewrite merge_suspend flatten_simplify.
      by repeat eexists.
    + right; right; right; right; right; left.
      rewrite merge_switch flatten_simplify.
      by repeat eexists.
    + right; right; right; right; right; right; left.
      rewrite merge_throw flatten_simplify.
      by repeat eexists. *)
  - unfold to_val0 => /=.
    destruct (merge_values (map _ _)) eqn:Hl.
    2: destruct e.
    destruct v.
    all: try by left; rewrite merge_notval.
    + do 3 right (* ; left *) ; repeat eexists.
      rewrite merge_call_host flatten_simplify.
      done.
    + rewrite merge_suspend; left => //.
    + rewrite merge_switch; left => //.
    + rewrite merge_throw; left => //. 
(*    + do 4 right; left; repeat eexists.
      by rewrite merge_suspend flatten_simplify.
    + do 5 right; left; repeat eexists.
      by rewrite merge_switch flatten_simplify.
    + do 6 right; left; repeat eexists.
      by rewrite merge_throw flatten_simplify. *)
  - unfold to_val0 => /=.
    do 3 right ; (* left; *) repeat eexists.
    rewrite merge_call_host flatten_simplify.
    done.
Qed.

Lemma to_val_None_prepend_const : forall es1 es2,
    const_list es1 ->
    to_val0 es2 = None ->
    to_val0 (es1 ++ es2) = None .
Proof.
  move => es1 es2 H H'.
  eapply to_val_None_prepend in H' as [ ? | [(i & vh & Hes1) | [[sh Hes1] |(* [ *)(?&?&?&sh&Hes1)  ]]] (* | [(?&sh&Hes1) | [(?&?&sh & Hes1) |[ (?&?&sh & Hes1) | (?&?&?&?&Hes1&Hes2)]]]]]]] *) ; first done.
  - exfalso.
    generalize dependent i. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    all: unfold to_val0 in Hes1 ; simpl in Hes1.
    all: rewrite merge_prepend in Hes1.
    all: destruct (merge_values _) eqn:Hmerge => //.
    destruct v0 => //.
    all: try destruct e => //.
    all: try destruct e0 => //.
    2-6: destruct v => //. 
    all: apply (IHes1 H i0 lh) => //.
    all: unfold to_val0.
    all: by rewrite Hmerge.
  - exfalso.
    generalize dependent sh. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    all: unfold to_val0 in Hes1 ; simpl in Hes1.
    all: rewrite merge_prepend in Hes1.
    all: destruct (merge_values _) eqn:Hmerge => //.
    destruct v0 => //.
    all: try destruct e => //.
    all: try destruct e0 => //. 
    2-6: destruct v => //.
    all: apply (IHes1 H s) => //.
    all: unfold to_val0.
    all: by rewrite Hmerge.
  - exfalso.
    generalize dependent sh. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    all: unfold to_val0 in Hes1 ; simpl in Hes1.
    all: rewrite merge_prepend in Hes1.
    all: destruct (merge_values _) eqn:Hmerge => //.
    destruct v0 => //.
    all: try destruct e => //.
    all: try destruct e0 => //. 
    2-6: destruct v => //.
    all: inversion Hes1; subst.
    all: apply (IHes1 H l0) => //.
    all: unfold to_val0.
    all: by rewrite Hmerge.
(*  - exfalso.
    generalize dependent sh. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    all: unfold to_val0 in Hes1 ; simpl in Hes1.
    all: rewrite merge_prepend in Hes1.
    all: destruct (merge_values _) eqn:Hmerge => //.
    destruct v0 => //.
    2-5: destruct v => //.
    all: inversion Hes1; subst.
    all: apply (IHes1 H sh0) => //.
    all: unfold to_val0.
    all: by rewrite Hmerge.
  - exfalso.
    generalize dependent sh. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    all: unfold to_val0 in Hes1 ; simpl in Hes1.
    all: rewrite merge_prepend in Hes1.
    all: destruct (merge_values _) eqn:Hmerge => //.
    destruct v0 => //.
    2-5: destruct v => //.
    all: inversion Hes1; subst.
    all: apply (IHes1 H sh0) => //.
    all: unfold to_val0.
    all: by rewrite Hmerge.
  - exfalso.
    generalize dependent sh. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    all: unfold to_val0 in Hes1 ; simpl in Hes1.
    all: rewrite merge_prepend in Hes1.
    all: destruct (merge_values _) eqn:Hmerge => //.
    5:{ apply merge_is_throw_ref in Hmerge as ->.
        simpl in H. done. } 
    destruct v0 => //.
    2-5: destruct v => //.
    all: inversion Hes1; subst.
    all: apply (IHes1 H sh0) => //.
    all: unfold to_val0.
    all: by rewrite Hmerge.
  - subst. right.
    repeat eexists. *)
Qed.

Lemma to_val_None_append: forall es1 es2,
    to_val0 es1 = None ->
    to_val0 (es1 ++ es2) = None.
Proof.
  move => es1 es2.
  induction es1 => //=.
  destruct a => //=; unfold to_val0 => /=.
  destruct b => //= ; unfold to_val0 => /=.
  all: try by repeat rewrite merge_notval.
  - by rewrite merge_br flatten_simplify.
  - by rewrite merge_return flatten_simplify.
  - rewrite merge_prepend.
    unfold to_val0 in IHes1.
    destruct (merge_values _) eqn:Hmerge => //=.
    + destruct v0 => //=.
      assert (to_val0 es1 = Some trapV) ; first by unfold to_val0 ; rewrite Hmerge.
      apply to_val_trap_is_singleton in H as -> => //=.
      rewrite merge_prepend.
      rewrite merge_trap.
      simpl. destruct (flatten _) => //=.
    + destruct e => //=.
      all: rewrite merge_prepend.
      all: destruct (merge_values (map to_val_instr (es1 ++ es2)%list)) => //=.
      all: try by specialize (IHes1 Logic.eq_refl).
      all: destruct e => //. 
    + rewrite merge_prepend.
      destruct (merge_values (map _ (es1 ++ es2)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
      destruct e0 => //.
(*    + rewrite merge_prepend.
      destruct (merge_values (map _ (_ ++ _)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
      destruct e0 => //.
    + rewrite merge_prepend.
      destruct (merge_values (map _ (_ ++ _)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
      destruct e0 => //. *)
  - rewrite merge_prepend.
    unfold to_val0 in IHes1.
    destruct (merge_values _) eqn:Hmerge => //=.
    + destruct v => //=.
      assert (to_val0 es1 = Some trapV) ; first by unfold to_val0 ; rewrite Hmerge.
      apply to_val_trap_is_singleton in H as -> => //=.
      rewrite merge_prepend.
      rewrite merge_trap.
      simpl. destruct (flatten _) => //=.
    + destruct e => //=.
      all: rewrite merge_prepend.
      all: destruct (merge_values (map to_val_instr (es1 ++ es2)%list)) => //=.
      all: try by specialize (IHes1 Logic.eq_refl).
      all: destruct e => //. 
    + rewrite merge_prepend.
      destruct (merge_values (map _ (es1 ++ es2)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
      destruct e0 => //.
(*    + rewrite merge_prepend.
      destruct (merge_values (map _ (_ ++ _)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
      destruct e0 => //.
    + rewrite merge_prepend.
      destruct (merge_values (map _ (_ ++ _)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
      destruct e0 => //. *)
(*  - rewrite /to_val0 /= merge_ThrowRef.
    rewrite merge_ThrowRef.
    done. *)
  - unfold to_val0 => /=.
    rewrite merge_trap => /=.
    rewrite flatten_simplify.
    destruct es1 => //=.
    rewrite merge_trap /=.
    rewrite of_to_val_instr => //.
  - rewrite /to_val0 /= merge_prepend.
    unfold to_val0 in IHes1.
    destruct (merge_values _) eqn:Hmerge => //=.
    + destruct v => //=.
      assert (to_val0 es1 = Some trapV) ; first by unfold to_val0 ; rewrite Hmerge.
      apply to_val_trap_is_singleton in H as -> => //=.
      rewrite merge_prepend.
      rewrite merge_trap.
      simpl. destruct (flatten _) => //=.
    + destruct e => //=.
      all: rewrite merge_prepend.
      all: destruct (merge_values (map to_val_instr (es1 ++ es2)%list)) => //=.
      all: try by specialize (IHes1 Logic.eq_refl).
      all: destruct e => //. 
    + rewrite merge_prepend.
      destruct (merge_values (map _ (es1 ++ es2)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
      destruct e0 => //.
(*    + rewrite merge_prepend.
      destruct (merge_values (map _ (_ ++ _)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
      destruct e0 => //.
    + rewrite merge_prepend.
      destruct (merge_values (map _ (_ ++ _)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
      destruct e0 => //. *)
  - rewrite /to_val0 /= merge_prepend.
    unfold to_val0 in IHes1.
    destruct (merge_values _) eqn:Hmerge => //=.
    + destruct v => //=.
      assert (to_val0 es1 = Some trapV) ; first by unfold to_val0 ; rewrite Hmerge.
      apply to_val_trap_is_singleton in H as -> => //=.
      rewrite merge_prepend.
      rewrite merge_trap.
      simpl. destruct (flatten _) => //=.
    + destruct e => //=.
      all: rewrite merge_prepend.
      all: destruct (merge_values (map to_val_instr (es1 ++ es2)%list)) => //=.
      all: try by specialize (IHes1 Logic.eq_refl).
      destruct e => //.
      destruct e1 => //. 
    + rewrite merge_prepend.
      destruct (merge_values (map _ (es1 ++ es2)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
      destruct e1 => //.
(*    + rewrite merge_prepend.
      destruct (merge_values (map _ (_ ++ _)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
      destruct e1 => //.
    + rewrite merge_prepend.
      destruct (merge_values (map _ (_ ++ _)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
      destruct e1 => //. *)
  - rewrite /to_val0 /= merge_prepend.
    unfold to_val0 in IHes1.
    destruct (merge_values _) eqn:Hmerge => //=.
    + destruct v => //=.
      assert (to_val0 es1 = Some trapV) ; first by unfold to_val0 ; rewrite Hmerge.
      apply to_val_trap_is_singleton in H as -> => //=.
      rewrite merge_prepend.
      rewrite merge_trap.
      simpl. destruct (flatten _) => //=.
    + destruct e => //=.
      all: rewrite merge_prepend.
      all: destruct (merge_values (map to_val_instr (es1 ++ es2)%list)) => //=.
      all: try by specialize (IHes1 Logic.eq_refl).
      all: destruct e => //. 
    + rewrite merge_prepend.
      destruct (merge_values (map _ (es1 ++ es2)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
      destruct e0 => //.
(*    + rewrite merge_prepend.
      destruct (merge_values (map _ (_ ++ _)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
      destruct e0 => //.
    + rewrite merge_prepend.
      destruct (merge_values (map _ (_ ++ _)%list)) => //=.
      by specialize (IHes1 Logic.eq_refl).
      destruct e0 => //. *)
  - rewrite /to_val0 /= merge_throw merge_throw => //.
  - unfold to_val0 => //=.
    do 2 rewrite merge_suspend => //=.
  - rewrite /to_val0 /= merge_switch merge_switch => //.
  - unfold to_val0 => /=.
    destruct (merge_values (map _ _)) eqn:Hmerge => //.
    2: destruct e.
    destruct v => //.
    all: try by repeat rewrite merge_notval.
    + rewrite merge_br => //.
    + rewrite merge_return => //.
    + rewrite merge_call_host => //.
    + repeat rewrite merge_suspend => //.
    + repeat rewrite merge_switch => //.
    + destruct (exnelts_of_exception_clauses _ _) => //. 
      repeat rewrite merge_throw => //.
      repeat rewrite merge_notval => //.
  - unfold to_val0 => /=.
    destruct (merge_values (map _ _)) eqn:Hmerge => //.
    2: destruct e.
    destruct v => //.
    all: try by repeat rewrite merge_notval.
    + rewrite merge_br => //.
    + rewrite merge_return => //.
    + rewrite merge_call_host => //.
    + destruct (suselts_of_continuation_clauses _ _).
      repeat rewrite merge_suspend => //.
      repeat rewrite merge_notval => //. 
    + destruct (swelts_of_continuation_clauses _ _).
      repeat rewrite merge_switch => //.
      repeat rewrite merge_notval => //. 
    + repeat rewrite merge_throw => //.
  - destruct (merge_values (map _ _)) eqn:Hmerge => //.
    2: destruct e.
    destruct v => //.
    all: try by repeat rewrite merge_notval.
    + destruct i => //.
      2: destruct (vh_decrease _) eqn:Hdecr => //.
      all: try by repeat rewrite merge_notval.
      rewrite merge_br => //.
    + rewrite merge_return => //.
    + rewrite merge_call_host => //.
    + repeat rewrite merge_suspend => //.
    + repeat rewrite merge_switch => //.
    + repeat rewrite merge_throw => //. 
  - destruct (merge_values (map _ _)) => //.
    2: destruct e.
    destruct v => //.
    all: try by repeat rewrite merge_notval.
    + rewrite merge_call_host => //.
    + repeat rewrite merge_suspend => //.
    + repeat rewrite merge_switch => //.
    + repeat rewrite merge_throw => //. 
  - unfold to_val0 => /=. by rewrite merge_call_host flatten_simplify.
Qed.


Lemma to_eff_None_prepend: forall es1 es2,
    to_eff0 es2 = None ->
    to_eff0 (es1 ++ es2) = None 
(*    ∨ (∃ i (vh : valid_holed i), to_val0 es1 = Some (brV vh))
    ∨ (∃ sh, to_val0 es1 = Some (retV sh))
    \/ (∃ tf h cvs sh, to_val0 es1 = Some (callHostV tf h cvs sh)) *)
    \/ (∃ vs i sh, to_eff0 es1 = Some (susE vs i sh))
    \/ (∃ vs k tf i sh, to_eff0 es1 = Some (swE vs k tf i sh))
    \/ (∃ vs a i sh, to_eff0 es1 = Some (thrE vs a i sh))
(*    \/ (∃ vs a i es, es1 = v_to_e_list (vs ++ [::VAL_ref (VAL_ref_exn a i)]) /\
                      es2 = AI_basic BI_throw_ref :: es)
    \/ (∃ vs k tf i es, es1 = v_to_e_list (vs ++ [::VAL_ref (VAL_ref_cont k)]) /\
                    es2 = AI_switch_desugared tf i :: es) *)
.
Proof.
  move => es1 es2 H.
  induction es1;try by left.
  destruct a;try by left; rewrite /to_eff0 /= merge_notval.
  destruct b; try by left; rewrite /to_eff0 /= merge_notval.
  - left; rewrite /to_eff0 /= merge_br => //. 
  - left; rewrite /to_eff0 /= merge_return => //. 
  - destruct IHes1 as [?| [(?&?&?&?)|[(?&?&?&?&?&?)|(* [ *)(?&?&?&?&?) ]]]. (* | [(?&?&?&?&?&?) | (?&?&?&?&?&?&?)]]]]] . *)
    + simpl. unfold to_eff0 => /=. rewrite merge_prepend.
      unfold to_eff0 in H0. destruct (merge_values _) => //=.
      destruct v0 => //=.
      all: try by left.
    + right;left. eexists _, _, (sus_push_const _ _).
      unfold to_eff0 => /=.
      rewrite merge_prepend. unfold to_eff0 in H0.
      destruct (merge_values _) ; try done.
      inversion H0 => //=. 
    + right;right. left. unfold to_eff0 => /=.
      rewrite merge_prepend.  unfold to_eff0 in H0.
      destruct (merge_values _) => //.  inversion H0 => //=.
      by repeat eexists. 
    + right;right; right .
      unfold to_eff0 => /=. rewrite merge_prepend. unfold to_eff0 in H0.
      destruct (merge_values _) => //. inversion H0 => //=.
      by repeat eexists.
(*    + right; right; right; right; left. subst.
      repeat eexists. instantiate (3 := VAL_num v :: _).
      simpl. done.
    + repeat right. subst. repeat eexists.
      instantiate (2:= VAL_num v :: _).
      simpl. done.  *)
  - destruct IHes1 as [? | [(?&?&?&?)|[(?&?&?&?&?&?)|(* [ *) (?&?&?&?&?)]]]. (* | [(?&?&?&?&?&?) | (?&?&?&?&?&?&?)]]]]] . *)
    + simpl. unfold to_eff0 => /=. rewrite merge_prepend.
      unfold to_eff0 in H0. destruct (merge_values _) => //=.
      destruct v.
      all: by left. 
    + right;left. eexists _, _, (sus_push_const _ _). unfold to_eff0 => /=.
      rewrite merge_prepend. unfold to_eff0 in H0.
      destruct (merge_values _) ; try done. inversion H0 => //=. 
    + right;right. left. unfold to_eff0 => /=. rewrite merge_prepend.
      unfold to_eff0 in H0.
      destruct (merge_values _) => //.  inversion H0 => //=.
      by repeat eexists. 
    + right;right; right . unfold to_eff0 => /=.
      rewrite merge_prepend. unfold to_eff0 in H0.
      destruct (merge_values _) => //. inversion H0 => //=.
      by repeat eexists.
(*    + right; right; right; right; left.
      subst. repeat eexists.
      instantiate (3 := VAL_ref (VAL_ref_null r) :: _).
      done.
    + repeat right. subst. repeat eexists.
      instantiate (2 := VAL_ref (VAL_ref_null r) :: _).
      simpl. done.        *)
(*  - unfold to_eff0 => /=.
    rewrite merge_ThrowRef => //=. by left. *)
  - rewrite /to_eff0 /= merge_trap => /=.
    rewrite flatten_simplify.
    destruct (es1 ++ es2) eqn:Habs => //.
    all: by left.
  - destruct IHes1 as [? | [(?&?&?&?)|[(?&?&?&?&?&?)|(* [ *) (?&?&?&?&?)]]]. (* | [(?&?&?&?&?&?) | (?&?&?&?&?&?&?)]]]]] . *)
    + simpl. unfold to_eff0 => /=. rewrite merge_prepend.
      unfold to_eff0 in H0. destruct (merge_values _) => //=.
      destruct v.
      all: by left. 
    + right;left. eexists _,_, (sus_push_const _ _). unfold to_eff0 => /=.
      rewrite merge_prepend. unfold to_eff0 in H0.
      destruct (merge_values _) ; try done. inversion H0 => //=. 
    + right;right. left. unfold to_eff0 => /=. rewrite merge_prepend.
      unfold to_eff0 in H0.
      destruct (merge_values _) => //.  inversion H0 => //=.
      by repeat eexists. 
    + right;right; right . unfold to_eff0 => /=.
      rewrite merge_prepend. unfold to_eff0 in H0.
      destruct (merge_values _) => //. inversion H0 => //=.
      by repeat eexists.
(*    + right; right; right; right; left.
      subst. repeat eexists.
      instantiate (3 := VAL_ref (VAL_ref_func f) :: _).
      done.
    + repeat right. subst. repeat eexists.
      instantiate (2 := VAL_ref (VAL_ref_func f) :: _).
      simpl. done. *)
  - destruct IHes1 as [? | [(?& ?&?&?)|[(?&?&?&?&?&?)|(* [ *) (?&?&?&?&?)]]]. (* | [(?&?&?&?&?&?) | (?&?&?&?&?&?&?)]]]]] . *)
    + simpl. unfold to_eff0 => /=. rewrite merge_prepend.
      unfold to_eff0 in H0. destruct (merge_values _) eqn:Hmerge => //=.
      destruct v.
      all: try by left.
(*      apply merge_is_ThrowRef in Hmerge.
      destruct es1.
      * right; right; right; right; left.
        repeat eexists.
        instantiate (3 := [::]) => //.
        exact Hmerge.
      * inversion Hmerge; subst a e0.
        right; right; right. left.
        repeat eexists.
        simpl. rewrite merge_prepend. simpl.
        rewrite merge_ThrowRef. done. *)
    + right;left. eexists _, _, (sus_push_const _ _). unfold to_eff0 => /=.
      rewrite merge_prepend. unfold to_eff0 in H0.
      destruct (merge_values _) ; try done. inversion H0 => //=. 
    + right;right. left. unfold to_eff0 => /=. rewrite merge_prepend.
      unfold to_eff0 in H0.
      destruct (merge_values _) => //.  inversion H0 => //=.
      by repeat eexists. 
    + right;right; right . unfold to_eff0 => /=.
      rewrite merge_prepend. unfold to_eff0 in H0.
      destruct (merge_values _) => //. inversion H0 => //=.
      by repeat eexists.
(*    + right; right; right; right; left.
      subst. repeat eexists.
      instantiate (3 := VAL_ref (VAL_ref_exn e t) :: _).
      done.
    + repeat right. subst. repeat eexists.
      instantiate (2 := VAL_ref (VAL_ref_exn e t) :: _).
      simpl. done. *)
  - destruct IHes1 as [? | [(?&?&?&?)|[(?&?&?&?&?&?)|(* [ *) (?&?&?&?&?)]]]. (* | [(?&?&?&?&?&?) | (?&?&?&?&?&?&?)]]]]] . *)
    + simpl. unfold to_eff0 => /=. rewrite merge_prepend.
      unfold to_eff0 in H0. destruct (merge_values _) eqn:Hmerge => //=.
      destruct v.
      all: try by left.
(*      apply merge_is_Switch in Hmerge.
      destruct es1.
      * right; right; right; right; right.
        repeat eexists.
        instantiate (2 := [::]) => //.
        exact Hmerge.
      * inversion Hmerge; subst.
        right; right. left.
        repeat eexists.
        simpl. rewrite merge_prepend. simpl.
        rewrite merge_Switch. done. *)
    + right;left. eexists _,_, (sus_push_const _ _). unfold to_eff0 => /=.
      rewrite merge_prepend. unfold to_eff0 in H0.
      destruct (merge_values _) ; try done. inversion H0 => //=. 
    + right;right. left. unfold to_eff0 => /=. rewrite merge_prepend.
      unfold to_eff0 in H0.
      destruct (merge_values _) => //.  inversion H0 => //=.
      by repeat eexists. 
    + right;right; right. unfold to_eff0 => /=.
      rewrite merge_prepend. unfold to_eff0 in H0.
      destruct (merge_values _) => //. inversion H0 => //=.
      by repeat eexists.
(*    + right; right; right; right; left.
      subst. repeat eexists.
      instantiate (3 := VAL_ref (VAL_ref_cont f) :: _).
      done.
    + repeat right. subst. repeat eexists.
      instantiate (2 := VAL_ref (VAL_ref_cont f) :: _).
      simpl. done.    *)
  - right; right; right.
    unfold to_eff0 => /=. rewrite merge_throw.
    repeat eexists.
  - right; left.
    unfold to_eff0 => /=. rewrite merge_suspend.
    repeat eexists.
  - right; right; left.
    rewrite /to_eff0 /= merge_switch; repeat eexists => //. 
  - unfold to_eff0 => /=.
    destruct (merge_values (map _ l0)) eqn:Hmerge => //.
    2: destruct e.
    destruct v => //.
    all: try by rewrite merge_notval; left.
    + left; rewrite merge_br => //. 
    + left; rewrite merge_return => //. 
    + left; rewrite merge_call_host => //. 
    + right; left.
      rewrite merge_suspend flatten_simplify.
      by repeat eexists.
    + right; right; left.
      rewrite merge_switch flatten_simplify.
      by repeat eexists.
    + destruct (exnelts_of_exception_clauses _ _) eqn:Helts.
      * right; right; right.
        rewrite merge_throw flatten_simplify.
        by repeat eexists.
      * by left; rewrite merge_notval. 
  - unfold to_eff0 => /=.
    destruct (merge_values (map _ l1)) eqn:Hmerge => // ; try by left.
    2: destruct e.
    destruct v => //.
    all: try by left; rewrite merge_notval.
    + left; rewrite merge_br => //. 
    + left; rewrite merge_return => //. 
    + left; rewrite merge_call_host => //. 
    + destruct (suselts_of_continuation_clauses _ _) ;
        last by left; rewrite merge_notval.
      right; left.
      rewrite merge_suspend flatten_simplify.
      by repeat eexists.
    + destruct (swelts_of_continuation_clauses _ _);
        last by left; rewrite merge_notval.
      right; right; left.
      rewrite merge_switch flatten_simplify.
      by repeat eexists.
    + right; right; right.
      rewrite merge_throw flatten_simplify.
      by repeat eexists. 
  - unfold to_eff0 => /=.
    destruct (merge_values (map _ _)) eqn:Hmerge => // ; try by left.
    2: destruct e.
    destruct v => //.
    all: try by rewrite merge_notval; left.
    + destruct i.
      2: destruct (vh_decrease _).
      all: try by left; rewrite merge_notval.
      by left; rewrite merge_br.
    + left; rewrite merge_return => //. 
    + left; rewrite merge_call_host => //. 
    + right; left.
      rewrite merge_suspend flatten_simplify.
      by repeat eexists.
    + right; right; left.
      rewrite merge_switch flatten_simplify.
      by repeat eexists.
    + right; right; right.
      rewrite merge_throw flatten_simplify.
      by repeat eexists. 
  - unfold to_eff0 => /=.
    destruct (merge_values (map _ _)) eqn:Hl.
    2: destruct e.
    destruct v.
    all: try by left; rewrite merge_notval.
    + left; rewrite merge_call_host => //. 
    + do 1 right; left; repeat eexists.
      by rewrite merge_suspend flatten_simplify.
    + do 2 right; left; repeat eexists.
      by rewrite merge_switch flatten_simplify.
    + do 3 right; repeat eexists.
      by rewrite merge_throw flatten_simplify. 
  - unfold to_eff0 => /=.
    rewrite merge_call_host; left => //. 
Qed.

Lemma to_eff_None_prepend_const : forall es1 es2,
    const_list es1 ->
    to_eff0 es2 = None ->
    to_eff0 (es1 ++ es2) = None (* \/
      (exists vs a i es',
          es1 = vs ++ [:: AI_ref_exn a i] /\
            es2 = AI_basic BI_throw_ref :: es') \/
      (exists vs k tf i es',
          es1 = vs ++ [:: AI_ref_cont k] /\
            es2 = AI_switch_desugared tf i :: es') *)
       .
Proof.
  move => es1 es2 H H'.
  eapply to_eff_None_prepend in H' as [ ? | [(?&?&sh&Hes1) | [(?&?&?&?&sh & Hes1) |(* [ *)  (?& ?&?&sh & Hes1)]]]; (* | [(?&?&?&?&Hes1&Hes2) | (?&?&?&?&?&Hes1&Hes2)]]]]];*)  first done.
  - exfalso.
    generalize dependent sh. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    all: unfold to_eff0 in Hes1 ; simpl in Hes1.
    all: rewrite merge_prepend in Hes1.
    all: destruct (merge_values _) eqn:Hmerge => //.
    destruct v0 => //.
    all: try by destruct v => //.
    4: destruct e0 => //=.
    1-3, 5: destruct e => //=.
    all: inversion Hes1; subst.
    all: apply (IHes1 H sh0) => //.
    all: unfold to_eff0.
    all: by rewrite Hmerge.
  - exfalso. generalize dependent sh. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    all: unfold to_eff0 in Hes1 ; simpl in Hes1.
    all: rewrite merge_prepend in Hes1.
    all: destruct (merge_values _) eqn:Hmerge => //.
(*    11:{ apply merge_is_Switch in Hmerge as ->.
         simpl in H. done. }  *)
    destruct v0 => //.
    all: try by destruct v => //.
    4: destruct e0 => //.
    1-3, 5: destruct e => //. 
    all: inversion Hes1; subst.
    all: apply (IHes1 H sh0) => //.
    all: unfold to_eff0.
    all: by rewrite Hmerge.
  - exfalso.
    generalize dependent sh. 
    induction es1 => //=.
    intros.
    destruct a => //=.
    destruct b => //=.
    all: unfold to_eff0 in Hes1 ; simpl in Hes1.
    all: rewrite merge_prepend in Hes1.
    all: destruct (merge_values _) eqn:Hmerge => //.
(*    9:{ apply merge_is_ThrowRef in Hmerge as ->.
        simpl in H. done. }  *)
    destruct v0 => //.
    all: try by destruct v => //.
    4: destruct e0 => //.
    1-3,5: destruct e => //. 
    all: inversion Hes1; subst.
    all: apply (IHes1 H sh0) => //.
    all: unfold to_eff0.
    all: by rewrite Hmerge.
(*  - subst. right. left.
    repeat eexists.
    rewrite -v_to_e_cat => //.
  - subst. right. right.
    repeat eexists.
    rewrite -v_to_e_cat => //.  *)
Qed.

       
Lemma to_eff_None_append: forall es1 es2,
    (const_list es1 -> False) ->
    to_eff0 es1 = None ->
    to_eff0 (es1 ++ es2) = None.
Proof.
  move => es1 es2.
  induction es1 => //=.
  { intros H; exfalso; apply H => //. }
  destruct a => //=; unfold to_eff0 => /=.
  destruct b => //= ; unfold to_eff0 => /=.
  all: try by repeat rewrite merge_notval.
  - repeat rewrite merge_br => //. 
  - repeat rewrite merge_return => //. 
  - repeat rewrite merge_prepend.
    unfold to_eff0 in IHes1.
    destruct (merge_values _) eqn:Hmerge => //=.
    + destruct v0 => //=.
      all: by intros H Htriv; specialize (IHes1 H Htriv);
        destruct (merge_values (map _ (_ ++ _)%list));
        try destruct v0. 
    + destruct e => //=.
    + by intros H Htriv; specialize (IHes1 H Htriv);
        destruct (merge_values (map _ (_ ++ _)%list));
        try destruct v0. 
  - rewrite merge_prepend.
    unfold to_eff0 in IHes1.
    destruct (merge_values _) eqn:Hmerge => //=.
    + rewrite merge_prepend. destruct v => //=.
      all: by intros H Htriv; specialize (IHes1 H Htriv);
          destruct (merge_values (map _ (_ ++ _)%list));
        try destruct v. 
    + destruct e => //=.
    + rewrite merge_prepend.
      by intros H Htriv; specialize (IHes1 H Htriv);
          destruct (merge_values (map _ (_ ++ _)%list));
        try destruct v.
  - intros. rewrite merge_trap => //.
    destruct (flatten _) => //.
  - repeat rewrite merge_prepend.
    unfold to_eff0 in IHes1.
    destruct (merge_values _) eqn:Hmerge => //=.
    + destruct v => //=.
      all: by intros H Htriv; specialize (IHes1 H Htriv);
        destruct (merge_values (map _ (_ ++ _)%list));
        try destruct v.
    + destruct e => //.
    + by intros H Htriv; specialize (IHes1 H Htriv);
        destruct (merge_values (map _ (_ ++ _)%list));
      try destruct v.
  - repeat rewrite merge_prepend.
    unfold to_eff0 in IHes1.
    destruct (merge_values _) eqn:Hmerge => //=.
    + destruct v => //=.
      all: by intros H Htriv; specialize (IHes1 H Htriv);
        destruct (merge_values (map _ (_ ++ _)%list));
        try destruct v.
    + destruct e0 => //.
    + by intros H Htriv; specialize (IHes1 H Htriv);
        destruct (merge_values (map _ (_ ++ _)%list));
      try destruct v.
  - repeat rewrite merge_prepend.
    unfold to_eff0 in IHes1.
    destruct (merge_values _) eqn:Hmerge => //=.
    + destruct v => //=.
      all: by intros H Htriv; specialize (IHes1 H Htriv);
        destruct (merge_values (map _ (_ ++ _)%list));
        try destruct v.
    + destruct e => //.
    + by intros H Htriv; specialize (IHes1 H Htriv);
        destruct (merge_values (map _ (_ ++ _)%list));
      try destruct v.
  - rewrite merge_throw => //.
  - rewrite merge_suspend => //.
  - rewrite merge_switch => //.
  - destruct (merge_values (map _ l0)) eqn:Hmerge => //=.
    + destruct v => //.
      all: intros _ H.
      all: try by rewrite merge_notval.
      by rewrite merge_br.
      by rewrite merge_return.
      by rewrite merge_call_host.
    + destruct e => //.
      rewrite merge_suspend => //.
      rewrite merge_switch => //.
      destruct (exnelts_of_exception_clauses _ _) => //. 
      rewrite merge_throw => //.
      by intros _ H; rewrite merge_notval.
    + by intros _ H; rewrite merge_notval.
  - destruct (merge_values (map _ l1)) eqn:Hmerge => //=.
    + destruct v => //.
      all: intros _ H.
      all: try by rewrite merge_notval.
      by rewrite merge_br.
      by rewrite merge_return.
      by rewrite merge_call_host.
    + destruct e => //.
      destruct (suselts_of_continuation_clauses _ _) => //.
      rewrite merge_suspend => //.
      by intros _ H; rewrite merge_notval.
      destruct (swelts_of_continuation_clauses _ _) => //. 
      rewrite merge_switch => //.
      by intros _ H; rewrite merge_notval.
      rewrite merge_throw => //.
    + by intros _ H; rewrite merge_notval.
  - destruct (merge_values (map _ l0)) eqn:Hmerge => //=.
    + destruct v => //.
      all: intros _ H.
      all: try by rewrite merge_notval.
      destruct i => //.
      by rewrite merge_notval.
      destruct (vh_decrease _) => //.
      by rewrite merge_br.
      by rewrite merge_notval.
      by rewrite merge_return.
      by rewrite merge_call_host.
    + destruct e => //.
      rewrite merge_suspend => //.
      rewrite merge_switch => //.
      rewrite merge_throw => //.
    + by intros _ H; rewrite merge_notval.
  - destruct (merge_values (map _ l)) eqn:Hmerge => //=.
    + destruct v => //.
      all: intros _ H.
      all: try by rewrite merge_notval.
      by rewrite merge_call_host.
    + destruct e => //.
      rewrite merge_suspend => //.
      rewrite merge_switch => //.
      rewrite merge_throw => //.
    + by intros _ H; rewrite merge_notval.
  - intros. rewrite merge_call_host => //. 
Qed. 

Lemma const_list_to_val es :
  const_list es -> exists vs, to_val0 es = Some (immV vs) /\ v_to_e_list vs = es.
Proof.
  induction es => //= ; intros.
  by eexists [].
  destruct a => //=.
  destruct b => //=.
  all: unfold to_val0 => /=.
  all: rewrite merge_prepend.
  all: apply IHes in H as (vs & Htv & Hte).
  all: unfold to_val0 in Htv.
  all: destruct (merge_values _) => //=.
  all: inversion Htv => //=.
  all: eexists; split => //=.
  all: by rewrite Hte.
Qed.

Lemma to_val_not_trap_interweave : ∀ es es',
    const_list es -> es != [] ∨ es' != [] -> to_val0 (es ++ [AI_trap] ++ es')%SEQ = None.
Proof.
  intros es es1 Hconst Hnil.
  unfold to_val0.
  rewrite map_app merge_app /=.
  apply const_list_to_val in Hconst as (vs & Htv & Hvs).
  unfold to_val0 in Htv.
  destruct (merge_values _) => //.
  inversion Htv; subst.
  rewrite merge_trap flatten_simplify /=.
  destruct es1 => //.
  destruct vs => //.
  destruct Hnil => //.
Qed. 



Lemma to_val_to_eff es v e:
  to_val0 es = Some v -> to_eff0 es = Some e -> False.
Proof.
  unfold to_val0, to_eff0.
  destruct (merge_values _) => //. 
Qed.

Lemma const_list_to_eff vs :
  const_list vs -> to_eff0 vs = None.
Proof.
  intros H; apply const_list_to_val in H as (vs' & Hvs' & Hes').
  destruct (to_eff0 vs) eqn:He => //.
  exfalso; eapply to_val_to_eff => //.
Qed. 

Lemma to_val_const_list: forall es vs,
  to_val0 es = Some (immV vs) ->
  const_list es.
Proof.
  move => es. 
  elim: es => [|e es'] //=.
  move => IH vs.
  destruct e => //=; unfold to_val0 => /=.
  destruct b => //= ; unfold to_val0 => /=.
  all: try by rewrite merge_notval.
  - rewrite merge_br flatten_simplify => //.
  - rewrite merge_return flatten_simplify => //.
  - rewrite merge_prepend.
    unfold to_val0 in IH.
    destruct (merge_values _) => //.
    destruct v0 => //=.
    intro H ; inversion H ; subst.
    by eapply IH.
    destruct e => //=. 
  - rewrite merge_prepend.
    unfold to_val0 in IH.
    destruct (merge_values _) => //.
    destruct v => //=.
    intro H ; inversion H ; subst.
    by eapply IH.
    destruct e => //=.
(*  - rewrite merge_ThrowRef => //=.  *)
  - rewrite merge_trap flatten_simplify => /=.
    destruct es' => //=.
  - rewrite /to_val0 /= merge_prepend.
    unfold to_val0 in IH.
    destruct (merge_values _) => //.
    destruct v => //=.
    intro H ; inversion H ; subst.
    by eapply IH.
    destruct e => //. 
  - rewrite /to_val0 /= merge_prepend.
    unfold to_val0 in IH.
    destruct (merge_values _) => //.
    destruct v => //=.
    intro H ; inversion H ; subst.
    by eapply IH.
    destruct e0 => //. 
  - rewrite /to_val0 /= merge_prepend.
    unfold to_val0 in IH.
    destruct (merge_values _) => //.
    destruct v => //=.
    intro H ; inversion H ; subst.
    by eapply IH.
    destruct e => //.
  - rewrite /to_val0 /= merge_throw => //. 
  - rewrite /to_val0 /= merge_suspend => //.
  - rewrite /to_val0 /= merge_switch => //.
  - unfold to_val0 => /=.
    destruct (merge_values (map _ _)) eqn:Hmerge => //.
    2: destruct e.
    destruct v => //.
    all: try by rewrite merge_notval.
    + rewrite merge_br => //.
    + rewrite merge_return => //.
    + rewrite merge_call_host => //.
    + rewrite merge_suspend => //.
    + rewrite merge_switch => //.
    + destruct (exnelts_of_exception_clauses _ _) => //. 
      rewrite merge_throw => //.
      rewrite merge_notval => //. 
  - unfold to_val0 => /=.
    destruct (merge_values $ map _ _) eqn:Hmerge => //.
    2: destruct e.
    destruct v => //.
    all: try by rewrite merge_notval.
    + rewrite merge_br => //.
    + rewrite merge_return => //.
    + rewrite merge_call_host => //.
    + destruct (suselts_of_continuation_clauses _ _) => //. 
      rewrite merge_suspend => //.
      rewrite merge_notval => //. 
    + destruct (swelts_of_continuation_clauses _ _) => //. 
      rewrite merge_switch => //.
      rewrite merge_notval => //. 
    + rewrite merge_throw => //.
  - unfold to_val0 => /=.
    destruct (merge_values $ map _ _) eqn:Hmerge => //.
    2: destruct e => //. 
    destruct v => //.
    all: try by rewrite merge_notval.
    + destruct i => //.
      2: destruct (vh_decrease lh) => //.
      all: try by rewrite merge_notval.
      rewrite merge_br => //.
    + rewrite merge_return => //.
    + rewrite merge_call_host => //.
    + rewrite merge_suspend => //.
    + rewrite merge_switch => //.
    + rewrite merge_throw => //.
  - destruct (merge_values $ map _ _) => //.
    2: destruct e.
    destruct v => //.
    all: try by rewrite merge_notval.
    + rewrite merge_call_host => //.
    + rewrite merge_suspend => //.
    + rewrite merge_switch => //.
    + rewrite merge_throw => //. 
  - unfold to_val0 => /= ; by rewrite merge_call_host.
Qed.

Lemma to_val_filled_trap n lh LI:
  lfilled n lh [AI_trap] LI -> to_val0 LI = None \/ LI = [AI_trap].
Proof.
  intros H.
  move/lfilledP in H.
  remember [AI_trap] as etrap.
  induction H; subst.
  - apply const_list_to_val in H as (vs' & Hvs' & Hes').
    unfold to_val0.
    unfold to_val0 in Hvs'.
    repeat rewrite map_app.
    repeat rewrite merge_app.
    destruct (merge_values _) eqn:Hmerge => //=. 
    inversion Hvs'; subst.
    rewrite merge_trap.
    destruct (flatten _) eqn:Hl; last by left.
    simpl.
    rewrite merge_flatten in Hl.
    rewrite merge_to_val in Hl.
    subst.
    destruct vs'; first by right.
    by left.
(*    specialize (f_equal expr_of_val_not_val Hmerge) as H.
    rewrite merge_to_val in H.
    destruct vs' => //=.
    by left. *) 
  - unfold to_val0.
    repeat rewrite map_app.
    repeat rewrite merge_app.
    apply const_list_to_val in H as (vs' & Hvs' & Hes').
    unfold to_val0 in Hvs'.
    destruct (merge_values _) eqn:Hmerge => //.
    inversion Hvs'; subst.
    simpl.
    destruct IHlfilledInd as [?| ->] => //.
    + unfold to_val0 in H.
      destruct (merge_values $ map _ LI) eqn:HLI => //.
      all: try by rewrite merge_notval; left.
      destruct e => //=.
      * rewrite merge_suspend; by left.
      * rewrite merge_switch; by left.
      * rewrite merge_throw; by left.
    + left. simpl.
      rewrite merge_notval => //. 
  -  unfold to_val0.
    repeat rewrite map_app.
    repeat rewrite merge_app.
    apply const_list_to_val in H as (vs' & Hvs' & Hes').
    unfold to_val0 in Hvs'.
    destruct (merge_values _) eqn:Hmerge => //.
    inversion Hvs'; subst.
    simpl.
    destruct IHlfilledInd as [?| ->] => //.
    + unfold to_val0 in H.
      destruct (merge_values $ map _ LI) eqn:HLI => //.
      all: try by rewrite merge_notval; left.
      destruct e => //=.
      * rewrite merge_suspend; by left.
      * rewrite merge_switch; by left.
      * destruct (exnelts_of_exception_clauses _ _).
        rewrite merge_throw; by left.
        rewrite merge_notval; by left.
    + left. simpl.
      rewrite merge_notval => //.
  - unfold to_val0.
    repeat rewrite map_app.
    repeat rewrite merge_app.
    apply const_list_to_val in H as (vs' & Hvs' & Hes').
    unfold to_val0 in Hvs'.
    destruct (merge_values _) eqn:Hmerge => //.
    inversion Hvs'; subst.
    simpl.
    destruct IHlfilledInd as [?| ->] => //.
    + unfold to_val0 in H.
      destruct (merge_values $ map _ LI) eqn:HLI => //.
      all: try by rewrite merge_notval; left.
      destruct e => //=.
      * destruct (suselts_of_continuation_clauses _ _).
        rewrite merge_suspend; by left.
        rewrite merge_notval; by left.
      * destruct (swelts_of_continuation_clauses _ _).
        rewrite merge_switch; by left.
        rewrite merge_notval; by left.
      * rewrite merge_throw; by left.
    + left. simpl.
      rewrite merge_notval => //. 
Qed.


Lemma to_eff_filled_trap n lh LI:
  lfilled n lh [AI_trap] LI -> to_eff0 LI = None.
Proof.
  intros H.
  move/lfilledP in H.
  remember [AI_trap] as etrap.
  induction H; subst.
  - apply const_list_to_eff in H.
    unfold to_eff0.
    unfold to_eff0 in H.
    repeat rewrite map_app.
    repeat rewrite merge_app.
    destruct (merge_values _) eqn:Hmerge => //=.
    destruct v => //=.
    + rewrite merge_trap => //=. 
      destruct (flatten _) eqn:Hl => //.
      destruct l => //.
    + rewrite merge_trap => //=.
      destruct (flatten _) => //=. 
  - unfold to_eff0.
    repeat rewrite map_app.
    repeat rewrite merge_app.
    apply const_list_to_eff in H.
    unfold to_eff0 in H.
    destruct (merge_values _) eqn:Hmerge => //.
    specialize (IHlfilledInd Logic.eq_refl).
    unfold to_eff0 in IHlfilledInd.
    simpl. destruct v => //=.
    all: destruct (merge_values (map _ LI)) eqn:HLI => //=.
    all: try destruct v => //.
    all: try by rewrite merge_notval.
    all: try destruct i.
    all: try destruct (vh_decrease _).
    all: try by rewrite merge_notval.
    all: try by rewrite merge_br => //.
    all: try by rewrite merge_return => //.
    all: rewrite merge_call_host => //.
  - unfold to_eff0.
    repeat rewrite map_app.
    repeat rewrite merge_app.
    apply const_list_to_eff in H.
    unfold to_eff0 in H.
    destruct (merge_values _) eqn:Hmerge => //.
    specialize (IHlfilledInd Logic.eq_refl).
    unfold to_eff0 in IHlfilledInd.
    simpl. destruct v => //=.
    all: destruct (merge_values (map _ LI)) eqn:HLI => //=.
    all: try destruct v => //.
    all: try destruct (exnelts_of_exception_clauses _ _).
    all: try by rewrite merge_notval.
    all: try by rewrite merge_br => //.
    all: try by rewrite merge_return => //.
    all: rewrite merge_call_host => //.
  - unfold to_eff0.
    repeat rewrite map_app.
    repeat rewrite merge_app.
    apply const_list_to_eff in H.
    unfold to_eff0 in H.
    destruct (merge_values _) eqn:Hmerge => //.
    specialize (IHlfilledInd Logic.eq_refl).
    unfold to_eff0 in IHlfilledInd.
    simpl. destruct v => //=.
    all: destruct (merge_values (map _ LI)) eqn:HLI => //=.
    all: try destruct v => //.
    all: try destruct (suselts_of_continuation_clauses _ _).
    all: try destruct (swelts_of_continuation_clauses _ _).
    all: try by rewrite merge_notval.
    all: try by rewrite merge_br => //.
    all: try by rewrite merge_return => //.
    all: rewrite merge_call_host => //.
Qed. 


Lemma suselts_firstx hs i l:
  suselts_of_continuation_clauses hs i = Some l ->
  firstx_continuation_suspend hs i = None .
Proof.
  generalize dependent l.
  induction hs => //=.
  destruct (suselt_of_continuation_clause _ _) eqn:Helt => //. 
  destruct (suselts_of_continuation_clauses _ _) => //.
  rewrite (IHhs l Logic.eq_refl) => //=.
  intros l0 H; inversion H; subst.
  destruct i.
  simpl in Helt.
  destruct a => //=.
  destruct t => //=.
  destruct (_ == _) eqn:Habs => //.
  move/eqP in Habs.
  inversion Habs; subst n0.
  destruct (n <? n) eqn:Hn; try by apply Nat.ltb_lt in Hn; lia.
  rewrite (Nat.eqb_refl n) in Helt.
  done.
Qed.

Lemma swelts_firstx hs i l:
  swelts_of_continuation_clauses hs i = Some l ->
  firstx_continuation_switch hs i = false.
Proof.
  generalize dependent l.
  induction hs => //=.
  destruct (swelt_of_continuation_clause _ _) eqn:Helt => //. 
  destruct (swelts_of_continuation_clauses _ _) => //.
  rewrite (IHhs l Logic.eq_refl) => //=.
  intros l0 H; inversion H; subst.
  destruct i.
  simpl in Helt.
  destruct a => //=.
  destruct t => //=.
  destruct (_ == _) eqn:Habs => //.
  move/eqP in Habs.
  inversion Habs; subst n0.
  destruct (n <? n) eqn:Hn; try by apply Nat.ltb_lt in Hn; lia.
  rewrite (Nat.eqb_refl n) in Helt.
  done.
Qed.

Lemma exnelts_firstx hs i l:
  exnelts_of_exception_clauses hs i = Some l ->
  firstx_exception hs i = No_label .
Proof.
  generalize dependent l.
  induction hs => //=.
  destruct (exnelt_of_exception_clause _ _) eqn:Helt => //. 
  destruct (exnelts_of_exception_clauses _ _) => //.
  rewrite (IHhs l Logic.eq_refl) => //=.
  intros l0 H; inversion H; subst.
  destruct i.
  simpl in Helt.
  destruct a => //=.
  all: destruct t => //=.
  all: destruct (_ == _) eqn:Habs => //.
  all: move/eqP in Habs.
  all: inversion Habs; subst n0.
  all: destruct (n <? n) eqn:Hn; try by apply Nat.ltb_lt in Hn; lia.
  all: rewrite (Nat.eqb_refl n) in Helt.
  all: done.
Qed.

Lemma llfill_switch sh vs k tf i es:
  llfill sh [AI_switch_desugared vs k tf i] = es ->
  (exists sh, to_eff0 es = Some $ swE vs k tf i sh) \/
    merge_values (map to_val_instr es) = NotVal es.
Proof.
  generalize dependent es.
  induction sh; intros es <- => //=.
  - left. exists (SwBase l l0).
    replace (v_to_e_list l ++ [:: AI_switch_desugared vs k tf i & l0]) with (of_eff0 (swE vs k tf i (SwBase l l0))) => //.
    apply to_of_eff0.
  - edestruct IHsh as [[sh' Hsw] | Hnv] => //.
    + left. apply of_to_eff0 in Hsw.
      unfold of_eff0 in Hsw.
      rewrite -Hsw.
      replace (v_to_e_list l ++ (AI_label n l0 (swfill i sh' [AI_switch_desugared vs k tf i]) :: l1)%SEQ) with (of_eff0 (swE vs k tf i (SwLabel l n l0 sh' l1))) => //.
      rewrite to_of_eff0.
      by eexists.
    + right. repeat rewrite map_app. repeat rewrite merge_app.
      simpl.
      rewrite Hnv. rewrite merge_notval. simpl.
      rewrite flatten_simplify.
      specialize (v_to_e_is_const_list l) as Hl.
      apply const_list_to_val in Hl as (vs' & Hvs & Heq).
      apply v_to_e_inj in Heq as ->.
      unfold to_val0 in Hvs.
      destruct (merge_values $ map _ $ v_to_e_list l) => //.
      inversion Hvs; subst.
      simpl. done.
  - edestruct IHsh as [[sh' Hsw] | Hnv] => //.
    + left. apply of_to_eff0 in Hsw.
      unfold of_eff0 in Hsw.
      rewrite -Hsw.
      replace (v_to_e_list l ++ (AI_local n f (swfill i sh' [AI_switch_desugared vs k tf i]) :: l0)%SEQ) with (of_eff0 (swE vs k tf i (SwLocal l n f sh' l0))) => //.
      rewrite to_of_eff0.
      by eexists.
    + right. repeat rewrite map_app. repeat rewrite merge_app.
      simpl.
      rewrite Hnv. rewrite merge_notval. simpl.
      rewrite flatten_simplify.
      specialize (v_to_e_is_const_list l) as Hl.
      apply const_list_to_val in Hl as (vs' & Hvs & Heq).
      apply v_to_e_inj in Heq as ->.
      unfold to_val0 in Hvs.
      destruct (merge_values $ map _ $ v_to_e_list l) => //.
      inversion Hvs; subst.
      simpl. done.
  - edestruct IHsh as [[sh' Hsw] | Hnv] => //.
    + destruct (swelts_of_continuation_clauses l1 i) eqn:Helts.
      * left. apply of_to_eff0 in Hsw.
        unfold of_eff0 in Hsw.
        rewrite -Hsw.
        replace (v_to_e_list l ++ (AI_prompt l0 l1 (swfill i sh' [AI_switch_desugared vs k tf i]) :: l2)%SEQ) with (of_eff0 (swE vs k tf i (SwPrompt l l0 l3 sh' l2))) => //.
        rewrite to_of_eff0.
        by eexists. simpl.
        apply swelts_of_continuation_clauses_inj in Helts.
        rewrite Helts. done.
      * right. repeat rewrite map_app. repeat rewrite merge_app.
        simpl. unfold to_eff0 in Hsw.
        destruct (merge_values _) => //.
        inversion Hsw; subst.
        rewrite Helts.
        rewrite merge_notval flatten_simplify.
        specialize (v_to_e_is_const_list l) as Hl.
        apply const_list_to_val in Hl as (vs' & Hvs & Heq).
        apply v_to_e_inj in Heq as ->.
        unfold to_val0 in Hvs.
        destruct (merge_values $ map _ $ v_to_e_list l) => //.
        inversion Hvs; subst.
        simpl. done.
    + right. repeat rewrite map_app. repeat rewrite merge_app.
      simpl.
      rewrite Hnv. rewrite merge_notval. simpl.
      rewrite flatten_simplify.
      specialize (v_to_e_is_const_list l) as Hl.
      apply const_list_to_val in Hl as (vs' & Hvs & Heq).
      apply v_to_e_inj in Heq as ->.
      unfold to_val0 in Hvs.
      destruct (merge_values $ map _ $ v_to_e_list l) => //.
      inversion Hvs; subst.
      simpl. done.
  - edestruct IHsh as [[sh' Hsw] | Hnv] => //.
    + left. apply of_to_eff0 in Hsw.
      unfold of_eff0 in Hsw.
      rewrite -Hsw.
      replace (v_to_e_list l ++ (AI_handler l0 (swfill i sh' [AI_switch_desugared vs k tf i]) :: l1)%SEQ) with (of_eff0 (swE vs k tf i (SwHandler l l0 sh' l1))) => //.
      rewrite to_of_eff0.
      by eexists.
    + right. repeat rewrite map_app. repeat rewrite merge_app.
      simpl.
      rewrite Hnv. rewrite merge_notval. simpl.
      rewrite flatten_simplify.
      specialize (v_to_e_is_const_list l) as Hl.
      apply const_list_to_val in Hl as (vs' & Hvs & Heq).
      apply v_to_e_inj in Heq as ->.
      unfold to_val0 in Hvs.
      destruct (merge_values $ map _ $ v_to_e_list l) => //.
      inversion Hvs; subst.
      simpl. done.
Qed. 

Lemma reduce_not_val s1 f1 e1 s2 f2 e2 :
  reduce s1 f1 e1 s2 f2 e2 ->
  merge_values (map to_val_instr e1) = NotVal e1 \/
    exists vs k tf tf' i sh hh,
      to_eff0 e1 = Some (swE vs k tf i sh) /\
        List.nth_error (s_conts s1) k = Some (Cont_dagger tf') /\
        s2 = s1 /\ f2 = f1 /\ hfilled No_var hh [::AI_trap] e2.
Proof.
  intros H; induction H; subst; try by left.
  all: try rewrite map_app merge_app.
  all: try specialize (v_to_e_is_const_list vcs) as H1'.
  all: try specialize (v_to_e_is_const_list vs) as H1'.
  all: try apply const_list_to_val in H1' as (? & Hvs & Hes).
  all: try apply const_list_to_val in H1 as (? & Hvs & Hes).
  all: try (remember H as H'; clear HeqH'; apply const_list_to_val in H' as (? & Hvs & Hes)).
  all: try unfold to_val0 in Hvs.
  all: try by left; destruct (merge_values _) => //; inversion Hvs; subst; try rewrite /= Hes.
  all: try by left; destruct v => //; destruct v.
  - left. inversion H; subst => //=.
    all: try rewrite map_app merge_app.
    all: try by apply const_list_to_val in H0 as (? & Hvs & ?);
      unfold to_val0 in Hvs;
      destruct (merge_values _) => //; inversion Hvs; subst.
    all: try by destruct v => //; destruct v => //.
    all: try by destruct v1, v2;
      try destruct v;
      try destruct v0.
    + destruct ref => //=.
    + destruct (merge_values $ map _ _) eqn:Hmerge => //.
      * destruct v => //=.
        -- destruct i0 => //=.
           destruct (vh_decrease _) eqn:Hdecr => //=.
            assert (to_val0 LI = Some (brV lh0)) ;
             first by unfold to_val0 ; rewrite Hmerge.
            apply of_to_val0 in H1.
            unfold of_val0 in H1.
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
        -- assert (to_val0 LI = Some (retV s0)) ; first by unfold to_val0 ; rewrite Hmerge.
           apply of_to_val0 in H1. unfold of_val0 in H1. 
           specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfill.
           rewrite H1 in Hfill.
           edestruct lfilled_first_values as (Habs & _ & _).
           exact H2.
           rewrite - (app_nil_l [_]) in Hfill.
           rewrite - cat_app in Hfill.
           exact Hfill.
           all : try done.
        -- assert (to_val0 LI = Some (callHostV f0 h l l0)) ;
             first by unfold to_val0 ; rewrite Hmerge.
           apply of_to_val0 in H1. unfold of_val0 in H1.
           edestruct lfilled_llfill_first_values as [Habs _].
           exact H2.
           rewrite - (cat0s [_]) in H1.
           exact H1.
           all : try done.
      * destruct e => //=.
         -- assert (to_eff0 LI = Some (susE vs0 i0 sh));
             first by unfold to_eff0; rewrite Hmerge.
           apply of_to_eff0 in H1.
           unfold of_eff0 in H1.
           specialize (susfill_to_hfilled i0 sh [AI_suspend_desugared vs0 i0]) as Hfill.
           rewrite H1 in Hfill.
           apply hfilled_to_llfill in Hfill as [llh Hfill].
           edestruct lfilled_llfill_first_values as [Habs _].
           exact H2.
           instantiate (2 := [::]).
           exact Hfill.
           all: done.
        -- assert (to_eff0 LI = Some (swE vs0 k tf i0 sh));
             first by unfold to_eff0; rewrite Hmerge.
           apply of_to_eff0 in H1.
           unfold of_eff0 in H1.
           specialize (swfill_to_hfilled i0 sh [AI_switch_desugared vs0 k tf i0]) as Hfill.
           rewrite H1 in Hfill.
           apply hfilled_to_llfill in Hfill as [llh Hfill].
           edestruct lfilled_llfill_first_values as [Habs _].
           exact H2.
           instantiate (2 := [::]).
           exact Hfill.
           all: done.
        -- assert (to_eff0 LI = Some (thrE vs0 a i0 sh));
             first by unfold to_eff0; rewrite Hmerge.
           apply of_to_eff0 in H1.
           unfold of_eff0 in H1.
           specialize (exnfill_to_hfilled i0 sh [AI_throw_ref_desugared vs0 a i0]) as Hfill.
           rewrite H1 in Hfill.
           apply hfilled_to_llfill in Hfill as [llh Hfill].
           edestruct lfilled_llfill_first_values as [Habs _].
           exact H2.
           instantiate (2 := [::]).
           exact Hfill.
           all: done.
    + destruct (merge_values $ map _ _) eqn:Hmerge => //.
      * destruct v => //=.
        assert (to_val0 es = Some (callHostV f1 h l l0)) ;
          first by unfold to_val0 ; rewrite Hmerge.
        apply of_to_val0 in H1. unfold of_val0 in H1.
        edestruct lfilled_llfill_first_values as [Habs _].
        exact H2.
        rewrite - (cat0s [_]) in H1.
        exact H1.
        all : try done.
      * destruct e => //=.
        -- assert (to_eff0 es = Some (susE vs i0 sh));
             first by unfold to_eff0; rewrite Hmerge.
           apply of_to_eff0 in H1. unfold of_eff0 in H1.
           specialize (susfill_to_hfilled i0 sh [AI_suspend_desugared vs i0]) as Hfill.
           rewrite H1 in Hfill.
           apply hfilled_to_llfill in Hfill as [llh Hfill].
           edestruct lfilled_llfill_first_values as [Habs _].
           exact H2.
           instantiate (2 := [::]).
           exact Hfill.
           all: done.
        -- assert (to_eff0 es = Some (swE vs k tf i0 sh));
             first by unfold to_eff0; rewrite Hmerge.
           apply of_to_eff0 in H1. unfold of_eff0 in H1.
           specialize (swfill_to_hfilled i0 sh [AI_switch_desugared vs k tf i0]) as Hfill.
           rewrite H1 in Hfill.
           apply hfilled_to_llfill in Hfill as [llh Hfill].
           edestruct lfilled_llfill_first_values as [Habs _].
           exact H2.
           instantiate (2 := [::]).
           exact Hfill.
           all: done.
        -- assert (to_eff0 es = Some (thrE vs a i0 sh));
             first by unfold to_eff0; rewrite Hmerge.
           apply of_to_eff0 in H1. unfold of_eff0 in H1.
           specialize (exnfill_to_hfilled i0 sh [AI_throw_ref_desugared vs a i0]) as Hfill.
           rewrite H1 in Hfill.
           apply hfilled_to_llfill in Hfill as [llh Hfill].
           edestruct lfilled_llfill_first_values as [Habs _].
           exact H2.
           instantiate (2 := [::]).
           exact Hfill.
           all: done.
    + destruct v => //=. destruct b => //=.
    + move/lfilledP in H1.
      remember 0 as z.
      remember [AI_trap] as es.
      induction H1; subst.
      all: repeat rewrite map_app.
      all: repeat rewrite merge_app.
      all: apply const_list_to_val in H1 as (vs' & Hvs' & Hes').
      all: unfold to_val0 in Hvs'.
      all: destruct (merge_values _) => //.
      all: inversion Hvs'; subst.
      all: simpl.
      * rewrite merge_trap merge_flatten => //=.
        rewrite merge_to_val.
        destruct es' => //=.
        destruct vs' => //=.
      * destruct (decide (LI = [AI_trap])).
        -- subst => //=.
           rewrite merge_notval.
           rewrite flatten_simplify => //. 
        -- rewrite IHlfilledInd => //=.
           rewrite merge_notval => //=.
           rewrite flatten_simplify => //.
           econstructor => //.
           by apply/lfilledP.
      * destruct (decide (LI = [AI_trap])).
        -- subst => //=.
           rewrite merge_notval.
           rewrite flatten_simplify => //. 
        -- rewrite IHlfilledInd => //=.
           rewrite merge_notval => //=.
           rewrite flatten_simplify => //.
           econstructor => //.
           by apply/lfilledP.
  - simpl. left.
    destruct (merge_values $ map _ LI) eqn:Hmerge => //=.
    + destruct v => //=.
      * exfalso.
        assert (to_val0 LI = Some $ brV lh);
          first by unfold to_val0; rewrite Hmerge.
        apply of_to_val0 in H1.
        unfold of_val0 in H1.
        apply hfilled_to_llfill in H as [llh Hllh].
        destruct (vfill_to_lfilled lh [AI_basic (BI_br i0)]).
        rewrite H1 in H2.
        edestruct lfilled_llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact H2.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_val0 LI = Some $ retV s0);
          first by unfold to_val0; rewrite Hmerge.
        apply of_to_val0 in H1.
        unfold of_val0 in H1.
        apply hfilled_to_llfill in H as [llh Hllh].
        specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hsh.
        rewrite H1 in Hsh.
        edestruct lfilled_llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hsh.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_val0 LI = Some $ callHostV f0 h l0 l1);
          first by unfold to_val0; rewrite Hmerge.
        apply of_to_val0 in H1.
        unfold of_val0 in H1.
        apply hfilled_to_llfill in H as [llh Hllh].
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact H1.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
    + destruct e => //=.
       * exfalso.
        assert (to_eff0 LI = Some $ susE vs0 i0 sh);
          first by unfold to_eff0; rewrite Hmerge.
        apply of_to_eff0 in H1.
        unfold of_eff0 in H1.
        specialize (susfill_to_hfilled i0 sh [AI_suspend_desugared vs0 i0]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H as [llh Hllh].
        rewrite H1 in Hfill.
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hfill.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_eff0 LI = Some $ swE vs0 k tf i0 sh);
          first by unfold to_eff0; rewrite Hmerge.
        apply of_to_eff0 in H1.
        unfold of_eff0 in H1.
        specialize (swfill_to_hfilled i0 sh [AI_switch_desugared vs0 k tf i0]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H as [llh Hllh].
        rewrite H1 in Hfill.
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hfill.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * destruct (exnelts_of_exception_clauses _ _) eqn:Helts => //.
        exfalso.
        assert (to_eff0 LI = Some $ thrE vs0 a0 i0 sh);
          first by unfold to_eff0; rewrite Hmerge.
        apply of_to_eff0 in H1.
        unfold of_eff0 in H1.
        specialize (exnfill_to_hfilled i0 sh [AI_throw_ref_desugared vs0 a0 i0]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H as [llh Hllh].
        rewrite H1 in Hfill.
        edestruct llfill_first_values as (Hres & _).
        instantiate (3 := []).
        exact Hfill.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
        inversion Hres; subst.
        erewrite exnelts_firstx in H0 => //.
  - simpl. left.
    destruct (merge_values $ map _ LI) eqn:Hmerge => //=.
    + destruct v => //=.
       * exfalso.
        assert (to_val0 LI = Some $ brV lh);
          first by unfold to_val0; rewrite Hmerge.
        apply of_to_val0 in H1.
        unfold of_val0 in H1.
        apply hfilled_to_llfill in H as [llh Hllh].
        destruct (vfill_to_lfilled lh [AI_basic (BI_br i0)]).
        rewrite H1 in H2.
        edestruct lfilled_llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact H2.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_val0 LI = Some $ retV s0);
          first by unfold to_val0; rewrite Hmerge.
        apply of_to_val0 in H1.
        unfold of_val0 in H1.
        apply hfilled_to_llfill in H as [llh Hllh].
        specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hsh.
        rewrite H1 in Hsh.
        edestruct lfilled_llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hsh.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_val0 LI = Some $ callHostV f0 h l0 l1);
          first by unfold to_val0; rewrite Hmerge.
        apply of_to_val0 in H1.
        unfold of_val0 in H1.
        apply hfilled_to_llfill in H as [llh Hllh].
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact H1.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
    + destruct e => //=.
       * exfalso.
        assert (to_eff0 LI = Some $ susE vs0 i0 sh);
          first by unfold to_eff0; rewrite Hmerge.
        apply of_to_eff0 in H1.
        unfold of_eff0 in H1.
        specialize (susfill_to_hfilled i0 sh [AI_suspend_desugared vs0 i0]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H as [llh Hllh].
        rewrite H1 in Hfill.
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hfill.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_eff0 LI = Some $ swE vs0 k tf i0 sh);
          first by unfold to_eff0; rewrite Hmerge.
        apply of_to_eff0 in H1.
        unfold of_eff0 in H1.
        specialize (swfill_to_hfilled i0 sh [AI_switch_desugared vs0 k tf i0]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H as [llh Hllh].
        rewrite H1 in Hfill.
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hfill.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * destruct (exnelts_of_exception_clauses _ _) eqn:Helts => //.
        exfalso.
        assert (to_eff0 LI = Some $ thrE vs0 a0 i0 sh);
          first by unfold to_eff0; rewrite Hmerge.
        apply of_to_eff0 in H1.
        unfold of_eff0 in H1.
        specialize (exnfill_to_hfilled i0 sh [AI_throw_ref_desugared vs0 a0 i0]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H as [llh Hllh].
        rewrite H1 in Hfill.
        edestruct llfill_first_values as (Habs & _).
        instantiate (3 := []).
        exact Hfill.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
        inversion Habs; subst.
        erewrite exnelts_firstx in H0 => //.
(*  - left. simpl.
    destruct (merge_values _) => //.
    inversion Hvs; subst.
    simpl. done. *)
  - simpl. left. 
    destruct (merge_values $ map _ LI) eqn:Hmerge => //=.
    + destruct v => //=.
       * exfalso.
        assert (to_val0 LI = Some $ brV lh) as Htv;
          first by unfold to_val0; rewrite Hmerge.
        apply of_to_val0 in Htv.
        unfold of_val0 in Htv.
        apply hfilled_to_llfill in H2 as [llh Hllh].
        destruct (vfill_to_lfilled lh [AI_basic (BI_br i)]) as [_ Hvh].
        rewrite Htv in Hvh.
        edestruct lfilled_llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hvh.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_val0 LI = Some $ retV s0) as Htv;
          first by unfold to_val0; rewrite Hmerge .
        apply of_to_val0 in Htv.
        unfold of_val0 in Htv.
        apply hfilled_to_llfill in H2 as [llh Hllh].
        specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hsh.
        rewrite Htv in Hsh.
        edestruct lfilled_llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hsh.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_val0 LI = Some $ callHostV f0 h l0 l1) as Htv;
          first by unfold to_val0; rewrite Hmerge.
        apply of_to_val0 in Htv.
        unfold of_val0 in Htv.
        apply hfilled_to_llfill in H2 as [llh Hllh].
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Htv.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
    + destruct e => //.
        * destruct (suselts_of_continuation_clauses _ _) eqn:Helts => //. 
        exfalso.
        assert (to_eff0 LI = Some $ susE vs0 i sh);
          first by unfold to_eff0; rewrite Hmerge.
        apply of_to_eff0 in H.
        unfold of_eff0 in H.
        specialize (susfill_to_hfilled i sh [AI_suspend_desugared vs0 i]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H2 as [llh Hllh].
        rewrite H in Hfill.
        edestruct llfill_first_values as [Hres _].
        instantiate (3 := []).
        exact Hfill.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
        inversion Hres; subst.
        erewrite suselts_firstx in H1 => //. 
      * exfalso.
        assert (to_eff0 LI = Some $ swE vs0 k tf i sh);
          first by unfold to_eff0; rewrite Hmerge.
        apply of_to_eff0 in H.
        unfold of_eff0 in H.
        specialize (swfill_to_hfilled i sh [AI_switch_desugared vs0 k tf i]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H2 as [llh Hllh].
        rewrite H in Hfill.
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hfill.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_eff0 LI = Some $ thrE vs0 a0 i sh);
          first by unfold to_eff0; rewrite Hmerge.
        apply of_to_eff0 in H.
        unfold of_eff0 in H.
        specialize (exnfill_to_hfilled i sh [AI_throw_ref_desugared vs0 a0 i]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H2 as [llh Hllh].
        rewrite H in Hfill.
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hfill.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
  - simpl. left.
    destruct (merge_values $ map _ LI) eqn:Hmerge => //.
    + destruct v => //=.
      * exfalso.
        assert (to_val0 LI = Some $ brV lh) as Htv;
          first by unfold to_val0; rewrite Hmerge.
        apply of_to_val0 in Htv.
        unfold of_val0 in Htv.
        apply hfilled_to_llfill in H2 as [llh Hllh].
        destruct (vfill_to_lfilled lh [AI_basic (BI_br i)]) as [_ Hvh].
        rewrite Htv in Hvh.
        edestruct lfilled_llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hvh.
        instantiate (2 := []). 
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_val0 LI = Some $ retV s0) as Htv;
          first by unfold to_val0; rewrite Hmerge.
        apply of_to_val0 in Htv.
        unfold of_val0 in Htv.
        apply hfilled_to_llfill in H2 as [llh Hllh].
        specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hsh.
        rewrite Htv in Hsh.
        edestruct lfilled_llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hsh.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_val0 LI = Some $ callHostV f0 h l l0) as Htv;
          first by unfold to_val0; rewrite Hmerge.
        apply of_to_val0 in Htv.
        unfold of_val0 in Htv.
        apply hfilled_to_llfill in H2 as [llh Hllh].
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Htv.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
    + destruct e => //=.
      * exfalso.
        assert (to_eff0 LI = Some $ susE vs0 i sh);
          first by unfold to_eff0; rewrite Hmerge.
        apply of_to_eff0 in H0.
        unfold of_eff0 in H0.
        specialize (susfill_to_hfilled i sh [AI_suspend_desugared vs0 i]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H2 as [llh Hllh].
        rewrite H0 in Hfill.
        edestruct llfill_first_values as [Hres _].
        instantiate (3 := []).
        exact Hfill.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * destruct (swelts_of_continuation_clauses _ _) eqn:Helts => //. 
        exfalso.
        assert (to_eff0 LI = Some $ swE vs0 k0 tf i sh);
          first by unfold to_eff0; rewrite Hmerge.
        apply of_to_eff0 in H0.
        unfold of_eff0 in H0.
        specialize (swfill_to_hfilled i sh [AI_switch_desugared vs0 k0 tf i]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H2 as [llh Hllh].
        rewrite H0 in Hfill.
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hfill.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
        inversion Habs; subst.
        erewrite swelts_firstx in H => //. 
      * exfalso.
        assert (to_eff0 LI = Some $ thrE vs0 a i sh);
          first by unfold to_eff0; rewrite Hmerge.
        apply of_to_eff0 in H0.
        unfold of_eff0 in H0.
        specialize (exnfill_to_hfilled i sh [AI_throw_ref_desugared vs0 a i]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H2 as [llh Hllh].
        rewrite H0 in Hfill.
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hfill.
        instantiate (2 := []).
        exact Hllh.
        all: try done. 
  - right. repeat eexists. exact H.
    instantiate (1 := HH_base [] []).
    unfold hfilled, hfill => //=.  
  - destruct IHreduce as [Hes | (vs' & k' & tf & tf' & i & sh & hh & Hes & Hcont & -> & -> & Htrap)].
    + destruct lh ; unfold lfilled, lfill in H0 ; fold lfill in H0 => //.
    1-2: destruct k => //. 
    all: destruct (const_list l) eqn:Hl => //.
    2-4: destruct (lfill _ _ _) eqn:Hfill => //.
    2-3: assert (lfilled k lh es l2) as Hfilled0;
      first by unfold lfilled ; rewrite Hfill.
    4: assert (lfilled k lh es l3) as Hfilled0;
      first by unfold lfilled; rewrite Hfill.
    all: move/eqP in H0; subst les.
    all: repeat rewrite map_app merge_app.
    all: apply const_list_to_val in Hl as (vs & Hvs & Hves).
    all: unfold to_val0 in Hvs.
    all: destruct (merge_values _) => //.
    all: inversion Hvs; subst.
    * rewrite Hes => //=. rewrite merge_to_val => //. by left.
    * simpl.
        destruct (merge_values $ map _ l2) eqn:Hmerge => //=.
        all: try by left; rewrite merge_notval flatten_simplify => //=.
        -- destruct v => //=.
           all: try by left; rewrite merge_notval flatten_simplify => //=.
           ++ destruct i.
              2: destruct (vh_decrease _) eqn:Hdecr.
              all: try by left; rewrite merge_notval flatten_simplify => //=.
              exfalso.
              assert (to_val0 l2 = Some (brV lh0)) ;
                first by unfold to_val0 ; rewrite Hmerge.
              apply of_to_val0 in H0.
              unfold of_val0 in H0.
              destruct (vfill_to_lfilled lh0 [AI_basic (BI_br (S i))]) as (Hk & Hfilled).
              rewrite H0 in Hfilled.
              
              rewrite - (app_nil_l [_]) in Hfilled.
              rewrite - cat_app in Hfilled.
              eapply lfilled_br_and_reduce.
              exact H.
              3: exact Hfilled.
              done.
              lia.
              exact Hfilled0.
           ++ exfalso.
              assert (to_val0 l2 = Some (retV s0)) ;
                first by unfold to_val0 ; rewrite Hmerge.
              apply of_to_val0 in H0. unfold of_val0 in H0.
              specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfilled.
              rewrite H0 in Hfilled.
              rewrite - (app_nil_l [_]) in Hfilled.
              rewrite - cat_app in Hfilled.
              eapply lfilled_return_and_reduce.
              exact H.
              2: exact Hfilled.
              done. done.
           ++ exfalso.
              assert (to_val0 l2 = Some (callHostV f0 h l l3)) ;
                first by unfold to_val0 ; rewrite Hmerge.
              apply of_to_val0 in H0. unfold of_val0 in H0.
              destruct (lfilled_implies_llfill Hfilled0) as (llh & _ & Hfilled).
              rewrite - (app_nil_l [_]) in H0.
              rewrite - cat_app in H0.
              eapply llfill_call_host_and_reduce ; first exact H.
              2: exact H0.
              2: exact Hfilled.
              done.
        -- destruct e => //=.
           ++ exfalso.
              assert (to_eff0 l2 = Some (susE vs0 i sh));
                first by unfold to_eff0; rewrite Hmerge.
              apply of_to_eff0 in H0. unfold of_eff0 in H0.
              eapply susfill_suspend_and_reduce.
              exact H. exact H0.
              done. 
           ++ assert (to_eff0 l2 = Some (swE vs0 k0 tf i sh));
                first by unfold to_eff0; rewrite Hmerge.
              remember H0 as H0'; clear HeqH0'.
              apply of_to_eff0 in H0. unfold of_eff0 in H0.
              edestruct swfill_switch_and_reduce as (tf'' & sh' & hh & Hsw & Hdag & Hs & Hf & Htrap).
              exact H. exact H0. done.
              subst s' f'.
              apply lfilled_implies_llfill in Hfilled0 as (lll & _ & Hlll).
              destruct (llfill_trans Hsw Hlll) as [lll' Hlll'].
              apply llfill_switch in Hlll' as [[sh'' Hsw'] | Hnv].
              ** right.
                 destruct (lfilled_hfilled_trans Htrap H1) as [hh' Hhh'].
                 repeat eexists.
                 unfold to_eff0.
                 repeat rewrite map_app merge_app.
                 simpl.
                 unfold to_eff0 in Hsw'.
                 destruct (merge_values $ map _ l2) => //.
                 inversion Hsw'; subst.
                 rewrite merge_switch flatten_simplify.
                 specialize (v_to_e_is_const_list vs) as Hvs'.
                 apply const_list_to_val in Hvs' as (vs' & Hvs'' & Heq).
                 apply v_to_e_inj in Heq as ->.
                 unfold to_val0 in Hvs''.
                 destruct (merge_values $ map _ $ v_to_e_list _) => //.
                 inversion Hvs''; subst.
                 simpl. done.
                 done. done.
              ** unfold to_eff0 in H0'.
                 rewrite Hnv in H0'. done.

         ++ exfalso.
            assert (to_eff0 l2 = Some $ thrE vs0 a i sh);
              first by unfold to_eff0; rewrite Hmerge.
            apply of_to_eff0 in H0. unfold of_eff0 in H0.
            eapply exnfill_throw_ref_and_reduce.
            exact H. exact H0. done.

      * simpl.
        destruct (merge_values $ map _ l2) eqn:Hmerge => //=.
        all: try by left; rewrite merge_notval flatten_simplify => //=.
        -- destruct v => //=.
           all: try by left; rewrite merge_notval flatten_simplify => //=.
           ++ exfalso.
              assert (to_val0 l2 = Some (brV lh0)) ;
                first by unfold to_val0 ; rewrite Hmerge.
              apply of_to_val0 in H0.
              unfold of_val0 in H0.
              destruct (vfill_to_lfilled lh0 [AI_basic (BI_br i)]) as (Hk & Hfilled).
              rewrite H0 in Hfilled.
              
              rewrite - (app_nil_l [_]) in Hfilled.
              rewrite - cat_app in Hfilled.
              eapply lfilled_br_and_reduce.
              exact H.
              3: exact Hfilled.
              done.
              lia.
              exact Hfilled0.
           ++ exfalso.
              assert (to_val0 l2 = Some (retV s0)) ;
                first by unfold to_val0 ; rewrite Hmerge.
              apply of_to_val0 in H0. unfold of_val0 in H0.
              specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfilled.
              rewrite H0 in Hfilled.
              rewrite - (app_nil_l [_]) in Hfilled.
              rewrite - cat_app in Hfilled.
              eapply lfilled_return_and_reduce.
              exact H.
              2: exact Hfilled.
              done. done.
           ++ exfalso.
              assert (to_val0 l2 = Some (callHostV f0 h l l3)) ;
                first by unfold to_val0 ; rewrite Hmerge.
              apply of_to_val0 in H0. unfold of_val0 in H0.
              destruct (lfilled_implies_llfill Hfilled0) as (llh & _ & Hfilled).
              rewrite - (app_nil_l [_]) in H0.
              rewrite - cat_app in H0.
              eapply llfill_call_host_and_reduce ; first exact H.
              2: exact H0.
              2: exact Hfilled.
              done.
        -- destruct e => //=.
                ++ exfalso.
              assert (to_eff0 l2 = Some (susE vs0 i sh));
                first by unfold to_eff0; rewrite Hmerge.
              apply of_to_eff0 in H0. unfold of_eff0 in H0.
              eapply susfill_suspend_and_reduce.
              exact H. exact H0.
              done.
                ++ assert (to_eff0 l2 = Some (swE vs0 k0 tf i sh));
                first by unfold to_eff0; rewrite Hmerge.
              remember H0 as H0'; clear HeqH0'.
              apply of_to_eff0 in H0. unfold of_eff0 in H0.
              edestruct swfill_switch_and_reduce as (tf' & sh' & hh & Hsw & Hdag & Hs & Hf & Htrap).
              exact H. exact H0. done.
              subst s' f'.
              apply lfilled_implies_llfill in Hfilled0 as (lll & _ & Hlll).
              destruct (llfill_trans Hsw Hlll) as [lll' Hlll'].
              apply llfill_switch in Hlll' as [[sh'' Hsw'] | Hnv].
              ** right.
                 destruct (lfilled_hfilled_trans Htrap H1) as [hh' Hhh'].
                 repeat eexists.
                 unfold to_eff0.
                 repeat rewrite map_app merge_app.
                 simpl.
                 unfold to_eff0 in Hsw'.
                 destruct (merge_values $ map _ l2) => //.
                 inversion Hsw'; subst.
                 rewrite merge_switch flatten_simplify.
                 specialize (v_to_e_is_const_list vs) as Hvs'.
                 apply const_list_to_val in Hvs' as (vs' & Hvs'' & Heq).
                 apply v_to_e_inj in Heq as ->.
                 unfold to_val0 in Hvs''.
                 destruct (merge_values $ map _ $ v_to_e_list _) => //.
                 inversion Hvs''; subst.
                 simpl. done.
                 done. done.
              ** unfold to_eff0 in H0'.
                 rewrite Hnv in H0'. done.

         ++ exfalso.
            assert (to_eff0 l2 = Some $ thrE vs0 a i sh);
              first by unfold to_eff0; rewrite Hmerge.
            apply of_to_eff0 in H0. unfold of_eff0 in H0.
            eapply exnfill_throw_ref_and_reduce.
            exact H. exact H0. done.
          

      * simpl.
        destruct (merge_values $ map _ l3) eqn:Hmerge => //=.
        all: try by left; rewrite merge_notval flatten_simplify => //=.
        -- destruct v => //=.
           all: try by left; rewrite merge_notval flatten_simplify => //=.
           ++ exfalso.
              assert (to_val0 l3 = Some (brV lh0)) ;
                first by unfold to_val0 ; rewrite Hmerge.
              apply of_to_val0 in H0.
              unfold of_val0 in H0.
              destruct (vfill_to_lfilled lh0 [AI_basic (BI_br i)]) as (Hk & Hfilled).
              rewrite H0 in Hfilled.
              
              rewrite - (app_nil_l [_]) in Hfilled.
              rewrite - cat_app in Hfilled.
              eapply lfilled_br_and_reduce.
              exact H.
              3: exact Hfilled.
              done.
              lia.
              exact Hfilled0.
           ++ exfalso.
              assert (to_val0 l3 = Some (retV s0)) ;
                first by unfold to_val0 ; rewrite Hmerge.
              apply of_to_val0 in H0. unfold of_val0 in H0.
              specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfilled.
              rewrite H0 in Hfilled.
              rewrite - (app_nil_l [_]) in Hfilled.
              rewrite - cat_app in Hfilled.
              eapply lfilled_return_and_reduce.
              exact H.
              2: exact Hfilled.
              done. done.
           ++ exfalso.
              assert (to_val0 l3 = Some (callHostV f0 h l l4)) ;
                first by unfold to_val0 ; rewrite Hmerge.
              apply of_to_val0 in H0. unfold of_val0 in H0.
              destruct (lfilled_implies_llfill Hfilled0) as (llh & _ & Hfilled).
              rewrite - (app_nil_l [_]) in H0.
              rewrite - cat_app in H0.
              eapply llfill_call_host_and_reduce ; first exact H.
              2: exact H0.
              2: exact Hfilled.
              done.
        -- destruct e => //=.
           ++ exfalso.
              assert (to_eff0 l3 = Some (susE vs0 i sh));
                first by unfold to_eff0; rewrite Hmerge.
              apply of_to_eff0 in H0. unfold of_eff0 in H0.
              eapply susfill_suspend_and_reduce.
              exact H. exact H0.
              done. 
           ++ destruct (swelts_of_continuation_clauses _ _) eqn:Helts;
                last by left; rewrite merge_notval flatten_simplify.
             assert (to_eff0 l3 = Some (swE vs0 k0 tf i sh));
                first by unfold to_eff0; rewrite Hmerge.
              remember H0 as H0'; clear HeqH0'.
              apply of_to_eff0 in H0. unfold of_eff0 in H0.
              edestruct swfill_switch_and_reduce as (tf' & sh' & hh & Hsw & Hdag & Hs & Hf & Htrap).
              exact H. exact H0. done.
              subst s' f'.
              apply lfilled_implies_llfill in Hfilled0 as (lll & _ & Hlll).
              destruct (llfill_trans Hsw Hlll) as [lll' Hlll'].
              apply llfill_switch in Hlll' as [[sh'' Hsw'] | Hnv].
              ** right.
                 destruct (lfilled_hfilled_trans Htrap H1) as [hh' Hhh'].
                 repeat eexists.
                 unfold to_eff0.
                 repeat rewrite map_app merge_app.
                 simpl.
                 unfold to_eff0 in Hsw'.
                 destruct (merge_values $ map _ l3) => //.
                 inversion Hsw'; subst.
                 rewrite Helts.
                 rewrite merge_switch flatten_simplify.
                 specialize (v_to_e_is_const_list vs) as Hvs'.
                 apply const_list_to_val in Hvs' as (vs' & Hvs'' & Heq).
                 apply v_to_e_inj in Heq as ->.
                 unfold to_val0 in Hvs''.
                 destruct (merge_values $ map _ $ v_to_e_list _) => //.
                 inversion Hvs''; subst.
                 simpl. done.
                 done. done.
              ** unfold to_eff0 in H0'.
                 rewrite Hnv in H0'. done.

         ++ exfalso.
            assert (to_eff0 l3 = Some $ thrE vs0 a i sh);
              first by unfold to_eff0; rewrite Hmerge.
            apply of_to_eff0 in H0. unfold of_eff0 in H0.
            eapply exnfill_throw_ref_and_reduce.
            exact H. exact H0. done.
    + apply of_to_eff0 in Hes.
      unfold of_eff0 in Hes.
      specialize (swfill_to_hfilled i sh [AI_switch_desugared vs' k' tf i]) as Hfill.
      rewrite Hes in Hfill.
      apply hfilled_to_llfill in Hfill as [llh Hllh].
      apply lfilled_implies_llfill in H0 as (llh' & _ & Hllh').
      destruct (llfill_trans Hllh Hllh') as [lll Hlll].
      apply llfill_switch in Hlll as [[ lll' Hlll' ] | Hnv].
      * right.
        destruct (lfilled_hfilled_trans Htrap H1) as [hh' Hhh'].
        repeat eexists. exact Hlll'.
        exact Hcont. exact Hhh'.
      * left. done.


  - destruct IHreduce as [Hes | (vs & k & tf & tfk & i & sh & hh & Hes & Hcont & -> & -> & Htrap)].
    + left. simpl. rewrite Hes. done.
    + right. 
      unfold to_eff0 => /=.
      unfold to_eff0 in Hes.
      destruct (merge_values _) => //.
      inversion Hes; subst. simpl.
      repeat eexists.
      exact Hcont.
      instantiate (1 := HH_local [] n f hh []).
      unfold hfilled, hfill; fold hfill => /=.
      unfold hfilled in Htrap.
      destruct (hfill _ _ _) => //=.
      move/eqP in Htrap; subst => //. 
Qed.
      

      
        
        
        


Lemma val_head_stuck_reduce : ∀ locs1 s1 e1 locs2 s2 e2,
    reduce locs1 s1 e1 locs2 s2 e2 ->
    to_val0 e1 = None.
Proof.
    intros.
  apply reduce_not_val in H.
  unfold to_val0.
  unfold to_eff0 in H.
  destruct H as [Hes | (vs & k & tf & tf' & i & sh & hh & Hes & _)].
  by rewrite Hes.
  by destruct (merge_values _).
Qed. 
(*  intros.
  apply reduce_not_val in H.
  unfold to_val0.
  rewrite H => //. 
Qed.  *)
(*

  move => locs1 s1 e1 locs2 s2 e2 HRed;try by to_val_None_prepend_const.
  induction HRed => //= ; subst; try by to_val_None_prepend_const.
  all: try by apply to_val_None_prepend_const; try apply v_to_e_is_const_list.
  - inversion H; subst => //= ;try by apply to_val_None_prepend_const;auto.
    + destruct ref => //=.
    + apply const_list_to_val in H0 as (vs & Hvs & ?).
      unfold to_val0 => /=.
      unfold to_val0 in Hvs.
      destruct (merge_values _) => //=.
      inversion Hvs; subst.
      done.
    + apply const_list_to_val in H0 as (vs & Hvs & ?).
      unfold to_val0 => /=.
      unfold to_val0 in Hvs.
      destruct (merge_values _) => //=.
      inversion Hvs; subst.
      done.
    + destruct v => //=.
      destruct v => //=.
    + destruct v1, v2 => //=.
      all: destruct v => //=.
      all: destruct v0 => //=.
    + destruct v1, v2 => //=.
      all: destruct v => //=.
      all: destruct v0 => //. 
    + unfold to_val0 => /=.
      apply const_list_to_val in H0 as (vs & Htv & ?).
      unfold to_val0 in Htv.
      destruct (merge_values _) => //.
      inversion Htv => //.
    + unfold to_val0 => /=.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      * destruct v => //.
        -- destruct i0 => //.
           destruct (vh_decrease lh0) eqn:Hdecr => //.
           assert (to_val0 LI = Some (brV lh0)) ;
             first by unfold to_val0 ; rewrite Hmerge.
           apply of_to_val0 in H1.
           unfold of_val0 in H1.
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
        -- assert (to_val0 LI = Some (retV s0)) ; first by unfold to_val0 ; rewrite Hmerge.
           apply of_to_val0 in H1. unfold of_val0 in H1. 
           specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfill.
           rewrite H1 in Hfill.
           edestruct lfilled_first_values as (Habs & _ & _).
           exact H2.
           rewrite - (app_nil_l [_]) in Hfill.
           rewrite - cat_app in Hfill.
           exact Hfill.
           all : try done.
        -- assert (to_val0 LI = Some (callHostV f0 h l l0)) ;
             first by unfold to_val0 ; rewrite Hmerge.
           apply of_to_val0 in H1. unfold of_val0 in H1.
           edestruct lfilled_llfill_first_values as [Habs _].
           exact H2.
           rewrite - (cat0s [_]) in H1.
           exact H1.
           all : try done.
      * destruct e => //=.
    + unfold to_val0 => /=.
      apply const_list_to_val in H0 as (vs & Htv & ?).
      unfold to_val0 in Htv.
      destruct (merge_values _) => //.
      inversion Htv => //.
    + unfold to_val0 => /=.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      2: destruct e => //. 
      destruct v => //.
      assert (to_val0 es = Some (callHostV f1 h l l0)) ;
        first by unfold to_val0 ; rewrite Hmerge.
      apply of_to_val0 in H1. unfold of_val0 in H1.
      edestruct lfilled_llfill_first_values as [Habs _].
      exact H2.
      rewrite - (cat0s [_]) in H1.
      exact H1.
      all : try done.
    + destruct v => //.
      by destruct b => //=.
    + apply to_val_filled_trap in H1 as [?|?] => //.
  - unfold to_val0 => /=.
    destruct (merge_values $ map _ _) eqn:HLI => //=.
    + destruct v => //=.
      * exfalso.
        assert (to_val0 LI = Some $ brV lh);
          first by unfold to_val0; rewrite HLI.
        apply of_to_val0 in H1.
        unfold of_val0 in H1.
        apply hfilled_to_llfill in H as [llh Hllh].
        destruct (vfill_to_lfilled lh [AI_basic (BI_br i0)]).
        rewrite H1 in H2.
        edestruct lfilled_llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact H2.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_val0 LI = Some $ retV s0);
          first by unfold to_val0; rewrite HLI.
        apply of_to_val0 in H1.
        unfold of_val0 in H1.
        apply hfilled_to_llfill in H as [llh Hllh].
        specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hsh.
        rewrite H1 in Hsh.
        edestruct lfilled_llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hsh.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_val0 LI = Some $ callHostV f0 h l0 l1);
          first by unfold to_val0; rewrite HLI.
        apply of_to_val0 in H1.
        unfold of_val0 in H1.
        apply hfilled_to_llfill in H as [llh Hllh].
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact H1.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
    + destruct e => //=.
      destruct (exnelts_of_exception_clauses _ _) => //.
  - unfold to_val0 => /=.
    destruct (merge_values $ map _ _) eqn:HLI => //=.
    + destruct v => //=.
      * exfalso.
        assert (to_val0 LI = Some $ brV lh) as Htv;
          first by unfold to_val0; rewrite HLI.
        apply of_to_val0 in Htv.
        unfold of_val0 in Htv.
        apply hfilled_to_llfill in H as [llh Hllh].
        destruct (vfill_to_lfilled lh [AI_basic (BI_br i0)]) as [_ Hvh].
        rewrite Htv in Hvh.
        edestruct lfilled_llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hvh.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_val0 LI = Some $ retV s0) as Htv;
          first by unfold to_val0; rewrite HLI.
        apply of_to_val0 in Htv.
        unfold of_val0 in Htv.
        apply hfilled_to_llfill in H as [llh Hllh].
        specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hsh.
        rewrite Htv in Hsh.
        edestruct lfilled_llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hsh.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_val0 LI = Some $ callHostV f0 h l0 l1) as Htv;
          first by unfold to_val0; rewrite HLI.
        apply of_to_val0 in Htv.
        unfold of_val0 in Htv.
        apply hfilled_to_llfill in H as [llh Hllh].
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Htv.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
    + destruct e => //=.
      destruct (exnelts_of_exception_clauses _ _) => //.
  - unfold to_val0 => /=.
    destruct (merge_values $ map _ _) eqn:HLI => //=.
    + destruct v => //=.
      * exfalso.
        assert (to_val0 LI = Some $ brV lh) as Htv;
          first by unfold to_val0; rewrite HLI.
        apply of_to_val0 in Htv.
        unfold of_val0 in Htv.
        apply hfilled_to_llfill in H2 as [llh Hllh].
        destruct (vfill_to_lfilled lh [AI_basic (BI_br i)]) as [_ Hvh].
        rewrite Htv in Hvh.
        edestruct lfilled_llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hvh.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_val0 LI = Some $ retV s0) as Htv;
          first by unfold to_val0; rewrite HLI.
        apply of_to_val0 in Htv.
        unfold of_val0 in Htv.
        apply hfilled_to_llfill in H2 as [llh Hllh].
        specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hsh.
        rewrite Htv in Hsh.
        edestruct lfilled_llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hsh.
        instantiate (2 := []).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_val LI = Some $ callHostV f0 h l0 l1) as Htv;
          first by unfold to_val; rewrite HLI.
        apply of_to_val in Htv.
        unfold of_val in Htv.
        apply hfilled_to_llfill in H4 as [llh Hllh].
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Htv.
        exact Hllh.
        all: try done.
    + destruct e => //=.
      destruct (suselts_of_continuation_clauses _ _) => //.
      destruct (swelts_of_continuation_clauses _ _) => //. 
  - unfold to_val => /=.
    destruct (merge_values $ map _ _) eqn:HLI => //=.
    + destruct v => //=.
      * exfalso.
        assert (to_val LI = Some $ brV lh) as Htv;
          first by unfold to_val; rewrite HLI.
        apply of_to_val in Htv.
        unfold of_val in Htv.
        apply hfilled_to_llfill in H4 as [llh Hllh].
        destruct (vfill_to_lfilled lh [AI_basic (BI_br i)]) as [_ Hvh].
        rewrite Htv in Hvh.
        edestruct lfilled_llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hvh.
        instantiate (2 := _ ++ [_]).
        rewrite -cat_app -catA.
        exact Hllh.
        all: try done.
        by apply const_list_concat.
      * exfalso.
        assert (to_val LI = Some $ retV s0) as Htv;
          first by unfold to_val; rewrite HLI.
        apply of_to_val in Htv.
        unfold of_val in Htv.
        apply hfilled_to_llfill in H4 as [llh Hllh].
        specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hsh.
        rewrite Htv in Hsh.
        edestruct lfilled_llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hsh.
        instantiate (2 := _ ++ [_]).
        rewrite -cat_app -catA.
        exact Hllh.
        all: try done.
        by apply const_list_concat.
      * exfalso.
        assert (to_val LI = Some $ callHostV f0 h l l0) as Htv;
          first by unfold to_val; rewrite HLI.
        apply of_to_val in Htv.
        unfold of_val in Htv.
        apply hfilled_to_llfill in H4 as [llh Hllh].
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Htv.
        instantiate (2 := _ ++ [_]).
        rewrite -cat_app -catA.
        exact Hllh.
        all: try done.
        by apply const_list_concat.
    + destruct e => //=.
      destruct (suselts_of_continuation_clauses _ _) => //.
      destruct (swelts_of_continuation_clauses _ _) => //. 
  - destruct v => //=. destruct v => //=.
  - destruct v => //=. destruct v => //=.
  - destruct lh ; unfold lfilled, lfill in H ; fold lfill in H => //.
    1-2: destruct k => //. 
    all: destruct (const_list l) eqn:Hl => //.
    2-4: destruct (lfill _ _ _) eqn:Hfill => //.
    all: move/eqP in H; subst les.
    all: apply to_val_None_prepend_const => //.
    2: rewrite separate1.
    all: apply to_val_None_append => //.
    all: unfold to_val => /=.
    all: destruct (merge_values $ map _ _) eqn:Hmerge => //.
    all: try destruct e => //=.
    all: try by destruct (exnelts_of_exception_clauses _ _) => //.
    all: try by destruct (suselts_of_continuation_clauses _ _) => //.
    all: try by destruct (swelts_of_continuation_clauses _ _) => //. 
    all: destruct v => //.
    + destruct i => //.
      destruct (vh_decrease lh0) eqn:Hdecr => //.
      exfalso.
      assert (to_val l2 = Some (brV lh0)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H.
      unfold of_val in H.
      destruct (vfill_to_lfilled lh0 [AI_basic (BI_br (S i))]) as (Hk & Hfilled).
      rewrite H in Hfilled.
      assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
      rewrite - (app_nil_l [_]) in Hfilled.
      rewrite - cat_app in Hfilled.
      eapply lfilled_br_and_reduce.
      exact HRed.
      3: exact Hfilled.
      done.
      lia.
      exact H1.
    + exfalso.
      assert (to_val l2 = Some (retV s0)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H. unfold of_val in H.
      specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfilled.
      rewrite H in Hfilled.
      assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
      rewrite - (app_nil_l [_]) in Hfilled.
      rewrite - cat_app in Hfilled.
      eapply lfilled_return_and_reduce.
      exact HRed.
      2: exact Hfilled.
      done. done.
    + exfalso.
      assert (to_val l2 = Some (callHostV f0 h l3 l4)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H. unfold of_val in H.
      assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
      destruct (lfilled_implies_llfill H1) as [llh Hfilled].
      rewrite - (app_nil_l [_]) in H.
      rewrite - cat_app in H.
      eapply llfill_call_host_and_reduce ; first (exact HRed).
      2: exact H.
      2: exact Hfilled.
      done.
    + exfalso.
      assert (to_val l2 = Some (brV lh0));
        first by unfold to_val; rewrite Hmerge.
      apply of_to_val in H. unfold of_val in H.
      assert (lfilled k lh es l2); first by unfold lfilled; rewrite Hfill.
      destruct (vfill_to_lfilled lh0 [AI_basic (BI_br i)]) as (Hk & Hfilled).
      rewrite H in Hfilled.
      rewrite - (app_nil_l [_]) in Hfilled.
      rewrite - cat_app in Hfilled.
      eapply lfilled_br_and_reduce.
      exact HRed.
      3: exact Hfilled.
      done. lia. done.
    + exfalso.
      assert (to_val l2 = Some (retV s0)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H. unfold of_val in H.
      specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfilled.
      rewrite H in Hfilled.
      assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
      rewrite - (app_nil_l [_]) in Hfilled.
      rewrite - cat_app in Hfilled.
      eapply lfilled_return_and_reduce.
      exact HRed.
      2: exact Hfilled.
      done. done.
    +  exfalso.
      assert (to_val l2 = Some (callHostV f0 h l3 l4)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H. unfold of_val in H.
      assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
      destruct (lfilled_implies_llfill H1) as [llh Hfilled].
      rewrite - (app_nil_l [_]) in H.
      rewrite - cat_app in H.
      eapply llfill_call_host_and_reduce ; first (exact HRed).
      2: exact H.
      2: exact Hfilled.
      done.
    + exfalso.
      assert (to_val l3 = Some (brV lh0));
        first by unfold to_val; rewrite Hmerge.
      apply of_to_val in H. unfold of_val in H.
      assert (lfilled k lh es l3); first by unfold lfilled; rewrite Hfill.
      destruct (vfill_to_lfilled lh0 [AI_basic (BI_br i)]) as (Hk & Hfilled).
      rewrite H in Hfilled.
      rewrite - (app_nil_l [_]) in Hfilled.
      rewrite - cat_app in Hfilled.
      eapply lfilled_br_and_reduce.
      exact HRed.
      3: exact Hfilled.
      done. lia. done.
    + exfalso.
      assert (to_val l3 = Some (retV s0)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H. unfold of_val in H.
      specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfilled.
      rewrite H in Hfilled.
      assert (lfilled k lh es l3) ; first by unfold lfilled ; rewrite Hfill.
      rewrite - (app_nil_l [_]) in Hfilled.
      rewrite - cat_app in Hfilled.
      eapply lfilled_return_and_reduce.
      exact HRed.
      2: exact Hfilled.
      done. done.
    + exfalso.
      assert (to_val l3 = Some (callHostV f0 h l4 l5)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H. unfold of_val in H.
      assert (lfilled k lh es l3) ; first by unfold lfilled ; rewrite Hfill.
      destruct (lfilled_implies_llfill H1) as [llh Hfilled].
      rewrite - (app_nil_l [_]) in H.
      rewrite - cat_app in H.
      eapply llfill_call_host_and_reduce ; first (exact HRed).
      2: exact H.
      2: exact Hfilled.
      done.
  - unfold to_val => /=.
    unfold to_val in IHHRed.
    destruct (merge_values $ map _ _) => //.
    destruct e => //. 
Qed.
*)



(*
Lemma throw_ref_no_reduce s f es s' f' es' :
  reduce s f (AI_basic BI_throw_ref :: es) s' f' es' -> False.
Proof.
  remember (S (length es)) as m.
  assert (length es < m); first lia.
  clear Heqm.
  generalize dependent es.
  induction m; intros; first lia.
  remember (_ :: _) as esc.
  induction H0; inversion Heqesc; subst => //.
  all: try by destruct vs => //=; inversion H6; subst.
  all: try by destruct v => //; destruct v => //. 
  all: try by destruct vcs => //=; inversion H1; destruct v => //; destruct v => //. 
  - inversion H0; subst => //=.
    + destruct ref => //=.
    + destruct v => //=. destruct v => //=.
    + destruct v1 => //=. destruct v => //=.
    + destruct v1 => //=. destruct v => //=.
    + destruct vs => //=.
      inversion H2; subst => //.
    + destruct vs => //=.
      inversion H2; subst => //. 
    + move/lfilledP in H3.
      inversion H3; subst.
      all: try by destruct bef => //; inversion H4; subst.
      destruct vs => //=.
      inversion H4; subst => //.
  - destruct vcs => //=.
    inversion H11; destruct v => //; destruct v => //. 
  - destruct vcs => //=.
    inversion H7; destruct v => //. destruct v => //.
  - destruct vs => //=.
    inversion H7; subst => //.
  - move/lfilledP in H1.
    inversion H1; subst.
    all: try by destruct bef => //; inversion H4; subst.
    all: destruct vs => //; try by inversion H4; subst.
    destruct es0 => //=.
    + clear -H0.
      remember [] as n.
      induction H0 ; inversion Heqn => //=.
      all: try by destruct vs.
      all: try by destruct ves.
      * inversion H; subst => //=.
        all: try by destruct vs => //.
        move/lfilledP in H2.
        inversion H2 => //=.
        destruct vs => //. destruct bef => //. destruct bef => //.
      * move/lfilledP in H.
        inversion H; subst.
        all: try destruct bef => //. 
        all: destruct vs => //.
        destruct es => //. 
    + destruct es'0 => //=.
      * rewrite cats0 in H4.
        apply IHreduce => //.
        exact IHm.

      * inversion H4; subst.
      eapply IHm.
      2: exact H0. lia.
  *)  

Lemma eff_head_stuck_reduce : ∀ s1 f1 e1 s2 f2 e2,
    reduce s1 f1 e1 s2 f2 e2 ->
    to_eff0 e1 = None \/ exists vs k tf tf' i sh hh, to_eff0 e1 = Some (swE vs k tf i sh) /\ List.nth_error (s_conts s1) k = Some (Cont_dagger tf') /\ s2 = s1 /\ f2 = f1 /\ hfilled No_var hh [::AI_trap] e2.
Proof.
   move => s1 f1 e1 s2 f2 e2 HRed.
  apply reduce_not_val in HRed.
  destruct HRed; try by right.
  left. unfold to_eff0; rewrite H => //.
Qed.
(*  move => s1 f1 e1 s2 f2 e2 HRed.
  apply reduce_not_val in HRed.
  unfold to_eff0; rewrite HRed => //.
Qed. *)
(*
  induction HRed => //= ; subst; try by left. 
  all: try by left; edestruct to_eff_None_prepend_const as [? | [(? & ? & ? & ? & ? & ?) | (? & ? & ? & ? & ? & ? & ?)]] => //; try apply v_to_e_is_const_list. 
  - left. inversion H; subst => //= ;try by left.
    all: try by edestruct to_eff_None_prepend_const as [? | [(? & ? & ? & ? & ? & ?) | (? & ? & ? & ? & ? & ? & ?)]] => //. 
    + destruct ref => //=.
    + apply const_list_to_eff in H0.
      unfold to_eff0 => /=.
      unfold to_eff0 in H0.
      destruct (merge_values $ map _ _) eqn:Hmerge => //=.
      destruct v => //=.
    + apply const_list_to_eff in H0.
      unfold to_eff0 => /=.
      unfold to_eff0 in H0.
      destruct (merge_values _) => //=.
      destruct v => //. 
    + destruct v => //=.
      destruct v => //=.
    + destruct v1, v2 => //=.
      all: destruct v => //=.
      all: destruct v0 => //=.
    + destruct v1, v2 => //=.
      all: destruct v => //=.
      all: destruct v0 => //.
    + unfold to_eff0 => /=.
      apply const_list_to_eff in H0.
      unfold to_eff0 in H0.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      destruct v => //=.
      destruct i => //=.
      destruct (vh_decrease _) => //.
    + unfold to_eff0 => /=.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      * destruct v => //.
        destruct i0 => //.
        destruct (vh_decrease lh0) eqn:Hdecr => //.
      * destruct e => //=.
        -- assert (to_eff0 LI = Some (susE i0 sh));
             first by unfold to_eff0; rewrite Hmerge.
           apply of_to_eff0 in H1.
           unfold of_eff0 in H1.
           specialize (susfill_to_hfilled i0 sh [AI_suspend_desugared i0]) as Hfill.
           rewrite H1 in Hfill.
           apply hfilled_to_llfill in Hfill as [llh Hfill].
           edestruct lfilled_llfill_first_values as [Habs _].
           exact H2.
           instantiate (2 := [::]).
           exact Hfill.
           all: done.
        -- assert (to_eff0 LI = Some (swE k tf i0 sh));
             first by unfold to_eff0; rewrite Hmerge.
           apply of_to_eff0 in H1.
           unfold of_eff0 in H1.
           specialize (swfill_to_hfilled i0 sh [AI_ref_cont k; AI_switch_desugared tf i0]) as Hfill.
           rewrite H1 in Hfill.
           apply hfilled_to_llfill in Hfill as [llh Hfill].
           edestruct lfilled_llfill_first_values as [Habs _].
           exact H2.
           instantiate (2 := [:: _]).
           exact Hfill.
           all: done.
        -- assert (to_eff0 LI = Some (thrE a i0 sh));
             first by unfold to_eff0; rewrite Hmerge.
           apply of_to_eff0 in H1.
           unfold of_eff0 in H1.
           specialize (exnfill_to_hfilled i0 sh [AI_ref_exn a i0; AI_basic BI_throw_ref]) as Hfill.
           rewrite H1 in Hfill.
           apply hfilled_to_llfill in Hfill as [llh Hfill].
           edestruct lfilled_llfill_first_values as [Habs _].
           exact H2.
           instantiate (2 := [:: _]).
           exact Hfill.
           all: done.
           
    + unfold to_eff0 => /=.
      apply const_list_to_eff0 in H0.
      unfold to_eff0 in H0.
      destruct (merge_values _) => //.
      destruct v => //. 
    + unfold to_eff0 => /=.
      destruct (merge_values $ map _ _) eqn:Hmerge => //.
      destruct v => //. 
      destruct e => //.
      * assert (to_eff0 es = Some (susE i0 sh));
          first by unfold to_eff0; rewrite Hmerge.
        apply of_to_eff0 in H1. unfold of_eff0 in H1.
        specialize (susfill_to_hfilled i0 sh [AI_suspend_desugared i0]) as Hfill.
        rewrite H1 in Hfill.
        apply hfilled_to_llfill in Hfill as [llh Hfill].
        edestruct lfilled_llfill_first_values as [Habs _].
        exact H2.
        instantiate (2 := [::]).
        exact Hfill.
        all: done.
      * assert (to_eff0 es = Some (swE k tf i0 sh));
          first by unfold to_eff0; rewrite Hmerge.
        apply of_to_eff0 in H1. unfold of_eff0 in H1.
        specialize (swfill_to_hfilled i0 sh [AI_ref_cont k; AI_switch_desugared tf i0]) as Hfill.
        rewrite H1 in Hfill.
        apply hfilled_to_llfill in Hfill as [llh Hfill].
        edestruct lfilled_llfill_first_values as [Habs _].
        exact H2.
        instantiate (2 := [:: _]).
        exact Hfill.
        all: done.
      * assert (to_eff0 es = Some (thrE a i0 sh));
          first by unfold to_eff0; rewrite Hmerge.
        apply of_to_eff0 in H1. unfold of_eff0 in H1.
        specialize (exnfill_to_hfilled i0 sh [AI_ref_exn a i0; AI_basic BI_throw_ref]) as Hfill.
        rewrite H1 in Hfill.
        apply hfilled_to_llfill in Hfill as [llh Hfill].
        edestruct lfilled_llfill_first_values as [Habs _].
        exact H2.
        instantiate (2 := [:: _]).
        exact Hfill.
        all: done.
    + destruct v => //.
      by destruct b => //=.
    + apply to_eff_filled_trap in H1 => //.
  - left. unfold to_eff0 => /=.
    destruct (merge_values $ map _ _) eqn:HLI => //=.
    + destruct v => //=.
    + destruct e => //=. 
      * exfalso.
        assert (to_eff0 LI = Some $ susE i sh);
          first by unfold to_eff0; rewrite HLI.
        apply of_to_eff0 in H2.
        unfold of_eff0 in H2.
        specialize (susfill_to_hfilled i sh [AI_suspend_desugared i]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H0 as [llh Hllh].
        rewrite H2 in Hfill.
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hfill.
        instantiate (2 := [_]).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_eff0 LI = Some $ swE k tf i sh);
          first by unfold to_eff0; rewrite HLI.
        apply of_to_eff0 in H2.
        unfold of_eff0 in H2.
        specialize (swfill_to_hfilled i sh [AI_ref_cont k; AI_switch_desugared tf i]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H0 as [llh Hllh].
        rewrite H2 in Hfill.
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := [_]).
        exact Hfill.
        instantiate (2 := [_]).
        exact Hllh.
        all: try done.
      * destruct (exnelts_of_exception_clauses _ _) eqn:Helts => //.
        exfalso.
        assert (to_eff LI = Some $ thrE a0 i sh);
          first by unfold to_eff; rewrite HLI.
        apply of_to_eff in H2.
        unfold of_eff in H2.
        specialize (exnfill_to_hfilled i sh [AI_ref_exn a0 i; AI_basic BI_throw_ref]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H0 as [llh Hllh].
        rewrite H2 in Hfill.
        edestruct llfill_first_values as (_ & Hres).
        instantiate (3 := [_]).
        exact Hfill.
        instantiate (2 := [_]).
        exact Hllh.
        all: try done.
        destruct Hres as [Heq ->] => //.
        inversion Heq; subst.
        erewrite exnelts_firstx in H1 => //.
  - left. unfold to_eff => /=.
    destruct (merge_values $ map _ _) eqn:HLI => //=.
    + destruct v => //=.
    + destruct e => //=. 
      * exfalso.
        assert (to_eff LI = Some $ susE i sh);
          first by unfold to_eff; rewrite HLI.
        apply of_to_eff in H0.
        unfold of_eff in H0.
        specialize (susfill_to_hfilled i sh [AI_suspend_desugared i]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H1 as [llh Hllh].
        rewrite H0 in Hfill.
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := []).
        exact Hfill.
        instantiate (2 := [_]).
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_eff LI = Some $ swE k tf i sh);
          first by unfold to_eff; rewrite HLI.
        apply of_to_eff in H0.
        unfold of_eff in H0.
        specialize (swfill_to_hfilled i sh [AI_ref_cont k; AI_switch_desugared tf i]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H1 as [llh Hllh].
        rewrite H0 in Hfill.
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := [_]).
        exact Hfill.
        instantiate (2 := [_]).
        exact Hllh.
        all: try done.
      * destruct (exnelts_of_exception_clauses _ _) eqn:Helts => //.
        exfalso.
        assert (to_eff LI = Some $ thrE a0 i sh);
          first by unfold to_eff; rewrite HLI.
        apply of_to_eff in H0.
        unfold of_eff in H0.
        specialize (exnfill_to_hfilled i sh [AI_ref_exn a0 i; AI_basic BI_throw_ref]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H1 as [llh Hllh].
        rewrite H0 in Hfill.
        edestruct llfill_first_values as (_ & Hres).
        instantiate (3 := [_]).
        exact Hfill.
        instantiate (2 := [_]).
        exact Hllh.
        all: try done.
        destruct Hres as [Heq ->] => //.
        inversion Heq; subst.
        erewrite exnelts_firstx in H2 => //.
  - left. unfold to_eff => /=.
    destruct (merge_values $ map _ _) eqn:HLI => //=.
    + destruct v => //=.
    + destruct e => //=. 
      * destruct (suselts_of_continuation_clauses _ _) eqn:Helts => //. 
        exfalso.
        assert (to_eff LI = Some $ susE i sh);
          first by unfold to_eff; rewrite HLI.
        apply of_to_eff in H0.
        unfold of_eff in H0.
        specialize (susfill_to_hfilled i sh [AI_suspend_desugared i]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H4 as [llh Hllh].
        rewrite H0 in Hfill.
        edestruct llfill_first_values as [Hres _].
        instantiate (3 := []).
        exact Hfill.
        exact Hllh.
        all: try done.
        inversion Hres; subst.
        erewrite suselts_firstx in H3 => //. 
      * exfalso.
        assert (to_eff LI = Some $ swE k tf i sh);
          first by unfold to_eff; rewrite HLI.
        apply of_to_eff in H0.
        unfold of_eff in H0.
        specialize (swfill_to_hfilled i sh [AI_ref_cont k; AI_switch_desugared tf i]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H4 as [llh Hllh].
        rewrite H0 in Hfill.
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := [_]).
        exact Hfill.
        exact Hllh.
        all: try done.
      * exfalso.
        assert (to_eff LI = Some $ thrE a0 i sh);
          first by unfold to_eff; rewrite HLI.
        apply of_to_eff in H0.
        unfold of_eff in H0.
        specialize (exnfill_to_hfilled i sh [AI_ref_exn a0 i; AI_basic BI_throw_ref]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H4 as [llh Hllh].
        rewrite H0 in Hfill.
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := [_]).
        exact Hfill.
        exact Hllh.
        all: try done.
  - left. unfold to_eff => /=.
    destruct (merge_values $ map _ _) eqn:HLI => //=.
    + destruct v => //=.
    + destruct e => //=. 
      * exfalso.
        assert (to_eff LI = Some $ susE i sh);
          first by unfold to_eff; rewrite HLI.
        apply of_to_eff in H1.
        unfold of_eff in H1.
        specialize (susfill_to_hfilled i sh [AI_suspend_desugared i]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H4 as [llh Hllh].
        rewrite H1 in Hfill.
        edestruct llfill_first_values as [Hres _].
        instantiate (3 := []).
        exact Hfill.
        instantiate (2 := _ ++ [_]).
        rewrite -cat_app -catA.
        exact Hllh.
        all: try done.
        apply const_list_concat => //. 
      * destruct (swelts_of_continuation_clauses _ _) eqn:Helts => //. 
        exfalso.
        assert (to_eff LI = Some $ swE k0 tf i sh);
          first by unfold to_eff; rewrite HLI.
        apply of_to_eff in H1.
        unfold of_eff in H1.
        specialize (swfill_to_hfilled i sh [AI_ref_cont k0; AI_switch_desugared tf i]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H4 as [llh Hllh].
        rewrite H1 in Hfill.
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := [_]).
        exact Hfill.
        instantiate (2 := _ ++ [_]).
        rewrite -cat_app -catA.
        exact Hllh.
        all: try done.
        apply const_list_concat => //.
        inversion Habs; subst.
        erewrite swelts_firstx in H0 => //. 
      * exfalso.
        assert (to_eff LI = Some $ thrE a i sh);
          first by unfold to_eff; rewrite HLI.
        apply of_to_eff in H1.
        unfold of_eff in H1.
        specialize (exnfill_to_hfilled i sh [AI_ref_exn a i; AI_basic BI_throw_ref]) as Hfill.
        apply hfilled_to_llfill in Hfill as [llh' Hfill].
        apply hfilled_to_llfill in H4 as [llh Hllh].
        rewrite H1 in Hfill.
        edestruct llfill_first_values as [Habs _].
        instantiate (3 := [_]).
        exact Hfill.
        instantiate (2 := _ ++ [_]).
        rewrite -cat_app -catA.
        exact Hllh.
        all: try done.
        apply const_list_concat => //.
  - right. repeat eexists. exact H.
  - left. destruct v => //=. destruct v => //=.
  - left. destruct v => //=. destruct v => //=.
  - destruct IHHRed as [Hes | (k' & tf & tfk & i & sh & Hes & Hdag & -> & -> & ->)].
    + left. destruct lh ; unfold lfilled, lfill in H ; fold lfill in H => //.
      1-2: destruct k => //. 
      all: destruct (const_list l) eqn:Hl => //.
      2-4: destruct (lfill _ _ _) eqn:Hfill => //.
      all: move/eqP in H; subst les.
      all: unfold to_eff.
      all: repeat rewrite map_app.
      all: repeat rewrite merge_app.
      all: apply const_list_to_val in Hl as [vs Hvs].
      all: unfold to_val in Hvs.
      all: destruct (merge_values _) => //.
      all: inversion Hvs; subst.
      all: unfold to_eff in Hes.
      all: destruct (merge_values _) eqn:Hmerge => //.
      all: try by apply val_head_stuck_reduce in HRed;
        unfold to_val in HRed;
        rewrite Hmerge in HRed.
      * destruct v => //=.
        -- destruct (merge_values (map _ l0)) eqn:Hmerge0 => //=.
           ++ destruct v => //=.
              destruct l1 => //=.
              destruct vs => //=.
           ++ destruct e => //=.
              ** 
      
      all: induction l => //=.
      
      2:{ simpl in Hl. remove_bools_options.
          

      
      all: edestruct to_eff_None_prepend_const.
      all: try exact Hl.
      all: try exact H.
      2:{ 
      2:{ 
    2: rewrite separate1.
    all: apply to_val_None_append => //.
    all: unfold to_val => /=.
    all: destruct (merge_values $ map _ _) eqn:Hmerge => //.
    all: try destruct e => //=.
    all: try by destruct (exnelts_of_exception_clauses _ _) => //.
    all: try by destruct (suselts_of_continuation_clauses _ _) => //.
    all: try by destruct (swelts_of_continuation_clauses _ _) => //. 
    all: destruct v => //.
    + destruct i => //.
      destruct (vh_decrease lh0) eqn:Hdecr => //.
      exfalso.
      assert (to_val l2 = Some (brV lh0)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H.
      unfold of_val in H.
      destruct (vfill_to_lfilled lh0 [AI_basic (BI_br (S i))]) as (Hk & Hfilled).
      rewrite H in Hfilled.
      assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
      rewrite - (app_nil_l [_]) in Hfilled.
      rewrite - cat_app in Hfilled.
      eapply lfilled_br_and_reduce.
      exact HRed.
      3: exact Hfilled.
      done.
      lia.
      exact H1.
    + exfalso.
      assert (to_val l2 = Some (retV s0)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H. unfold of_val in H.
      specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfilled.
      rewrite H in Hfilled.
      assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
      rewrite - (app_nil_l [_]) in Hfilled.
      rewrite - cat_app in Hfilled.
      eapply lfilled_return_and_reduce.
      exact HRed.
      2: exact Hfilled.
      done. done.
    + exfalso.
      assert (to_val l2 = Some (callHostV f0 h l3 l4)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H. unfold of_val in H.
      assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
      destruct (lfilled_implies_llfill H1) as [llh Hfilled].
      rewrite - (app_nil_l [_]) in H.
      rewrite - cat_app in H.
      eapply llfill_call_host_and_reduce ; first (exact HRed).
      2: exact H.
      2: exact Hfilled.
      done.
    + exfalso.
      assert (to_val l2 = Some (brV lh0));
        first by unfold to_val; rewrite Hmerge.
      apply of_to_val in H. unfold of_val in H.
      assert (lfilled k lh es l2); first by unfold lfilled; rewrite Hfill.
      destruct (vfill_to_lfilled lh0 [AI_basic (BI_br i)]) as (Hk & Hfilled).
      rewrite H in Hfilled.
      rewrite - (app_nil_l [_]) in Hfilled.
      rewrite - cat_app in Hfilled.
      eapply lfilled_br_and_reduce.
      exact HRed.
      3: exact Hfilled.
      done. lia. done.
    + exfalso.
      assert (to_val l2 = Some (retV s0)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H. unfold of_val in H.
      specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfilled.
      rewrite H in Hfilled.
      assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
      rewrite - (app_nil_l [_]) in Hfilled.
      rewrite - cat_app in Hfilled.
      eapply lfilled_return_and_reduce.
      exact HRed.
      2: exact Hfilled.
      done. done.
    +  exfalso.
      assert (to_val l2 = Some (callHostV f0 h l3 l4)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H. unfold of_val in H.
      assert (lfilled k lh es l2) ; first by unfold lfilled ; rewrite Hfill.
      destruct (lfilled_implies_llfill H1) as [llh Hfilled].
      rewrite - (app_nil_l [_]) in H.
      rewrite - cat_app in H.
      eapply llfill_call_host_and_reduce ; first (exact HRed).
      2: exact H.
      2: exact Hfilled.
      done.
    + exfalso.
      assert (to_val l3 = Some (brV lh0));
        first by unfold to_val; rewrite Hmerge.
      apply of_to_val in H. unfold of_val in H.
      assert (lfilled k lh es l3); first by unfold lfilled; rewrite Hfill.
      destruct (vfill_to_lfilled lh0 [AI_basic (BI_br i)]) as (Hk & Hfilled).
      rewrite H in Hfilled.
      rewrite - (app_nil_l [_]) in Hfilled.
      rewrite - cat_app in Hfilled.
      eapply lfilled_br_and_reduce.
      exact HRed.
      3: exact Hfilled.
      done. lia. done.
    + exfalso.
      assert (to_val l3 = Some (retV s0)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H. unfold of_val in H.
      specialize (sfill_to_lfilled s0 [AI_basic BI_return]) as Hfilled.
      rewrite H in Hfilled.
      assert (lfilled k lh es l3) ; first by unfold lfilled ; rewrite Hfill.
      rewrite - (app_nil_l [_]) in Hfilled.
      rewrite - cat_app in Hfilled.
      eapply lfilled_return_and_reduce.
      exact HRed.
      2: exact Hfilled.
      done. done.
    + exfalso.
      assert (to_val l3 = Some (callHostV f0 h l4 l5)) ;
        first by unfold to_val ; rewrite Hmerge.
      apply of_to_val in H. unfold of_val in H.
      assert (lfilled k lh es l3) ; first by unfold lfilled ; rewrite Hfill.
      destruct (lfilled_implies_llfill H1) as [llh Hfilled].
      rewrite - (app_nil_l [_]) in H.
      rewrite - cat_app in H.
      eapply llfill_call_host_and_reduce ; first (exact HRed).
      2: exact H.
      2: exact Hfilled.
      done.
  - unfold to_val => /=.
    unfold to_val in IHHRed.
    destruct (merge_values $ map _ _) => //.
    destruct e => //. 
Qed. *)

Definition to_val (e : expr) : option val :=
  let '(e, f) := e in
  match to_val0 e with
  | Some v => Some (v, f)
  | None => None
  end.

Definition to_eff (e : expr) : option eff :=
  let '(e, f) := e in
  match to_eff0 e with
  | Some v => Some (v, f)
  | None => None
  end.

Lemma val_head_stuck : forall e1 s1 κ e2 s2 efs,
  prim_step e1 s1 κ e2 s2 efs →
  to_val e1 = None.
Proof.
  rewrite /prim_step => e1 s1 κ e2 s2 efs /=.
  destruct e1 as [e1 f1].
  destruct e2 as [e2 f2].
  move => [HRed _].
  unfold to_val.
  erewrite val_head_stuck_reduce;eauto.
Qed.

Definition of_val (v : val) : expr :=
  let '(v, f) := v in
  (of_val0 v, f).

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof.
  destruct v => //=.
  rewrite to_of_val0 //.
Qed.

Lemma of_to_val e v : to_val e = Some v -> of_val v = e.
Proof.
  destruct e, v => //=.
  destruct (to_val0 e) eqn: Htv => //.
  intros H; inversion H; subst.
  f_equal.
  by eapply of_to_val0.
Qed.

Definition of_eff (v : eff) : expr :=
  let '(v, f) := v in
  (of_eff0 v, f).

Lemma to_of_eff v : to_eff (of_eff v) = Some v.
Proof.
  destruct v => //=.
  rewrite to_of_eff0 //.
Qed.

Lemma of_to_eff e v : to_eff e = Some v -> of_eff v = e.
Proof.
  destruct e, v => //=.
  destruct (to_eff0 e) eqn: Htv => //.
  intros H; inversion H; subst.
  f_equal.
  by eapply of_to_eff0.
Qed. 

Lemma wasm_mixin : LanguageMixin of_val to_val prim_step.
Proof. split; eauto using to_of_val, of_to_val, val_head_stuck. Qed.

(* Definition wasm_lang := Language wasm_mixin. *)

Canonical Structure valO := leibnizO val.
Canonical Structure wasm_lang : language := Language wasm_mixin.
