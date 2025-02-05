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

Definition v_of_e e :=
  match e with
  | AI_basic (BI_const n) => Some (VAL_num n)
  | AI_basic (BI_ref_null r) => Some (VAL_ref (VAL_ref_null r))
  | AI_ref f => Some (VAL_ref (VAL_ref_func f))
  | AI_ref_cont f => Some (VAL_ref (VAL_ref_cont f))
  | AI_ref_exn f => Some (VAL_ref (VAL_ref_exn f))
  | _ => None
  end.

Fixpoint vh_of_lh lh i :=
  match lh with
  | LH_base bef aft =>
      match those (map v_of_e bef) with
      | Some bef => Some (VH_base i bef aft)
      |  _ => None end
  | LH_rec bef n es lh aft =>
      match i with
      | 0 => None
      | S i => 
          match those (map v_of_e bef) with
          |  Some bef => match vh_of_lh lh i with
                        | Some vh => Some (VH_rec bef n es vh aft)
                        | None => None end
          |  _ => None end
      end
  | LH_prompt bef tf hs lh aft =>
      match those (map v_of_e bef) with
      | Some bef => match vh_of_lh lh i with
                   | Some vh => Some (VH_prompt bef tf hs vh aft)
                   | None => None end
      | _ => None end
  | LH_handler bef hs lh aft =>
      match those (map v_of_e bef) with
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

Fixpoint llh_of_lh lh :=
  match lh with
  | LH_base bef aft =>
      match those (map v_of_e bef) with
      | Some bef => Some (LL_base bef aft)
      | None => None end 
  | LH_rec bef n es lh aft =>
      match those (map v_of_e bef) with
      | Some bef =>
          match llh_of_lh lh with
          | Some lh' => Some (LL_label bef n es lh' aft)
          | None => None
          end
      | None => None end
  | LH_prompt bef tf hs lh aft =>
      match those (map v_of_e bef) with
      | Some bef =>
          match llh_of_lh lh with
          | Some lh' => Some (LL_prompt bef tf hs lh' aft)
          | None => None
          end
      | None => None
      end
  | LH_handler bef hs lh aft =>
      match those (map v_of_e bef) with
      | Some bef =>
          match llh_of_lh lh with
          | Some lh' => Some (LL_handler bef hs lh' aft)
          | None => None
          end
      | None => None
      end 
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
