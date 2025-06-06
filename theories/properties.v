(** Miscellaneous properties about Wasm operations **)

From Wasm Require Export datatypes_properties operations typing opsem common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
(* From StrongInduction Require Import StrongInduction. *) 
From Coq Require Import Bool Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Require Import Lia.

Set Bullet Behavior "Strict Subproofs".

(** * Basic Lemmas **)

Lemma const_const v :
  is_const (AI_const v).
Proof.
  destruct v => //=.
  destruct v => //=.
Qed.

Lemma const_const_inv v :
  is_const v -> exists iv, v = AI_const iv.
Proof.
  destruct v => //.
  destruct b => //.
  all: intros _.
  by eexists (VAL_num v).
  by eexists (VAL_ref (VAL_ref_null r)).
  by eexists (VAL_ref (VAL_ref_func f)).
  by eexists (VAL_ref (VAL_ref_exn e t)).
  by eexists (VAL_ref (VAL_ref_cont f)).
Qed. 
       

Lemma const_inj v1 v2 :
  AI_const v1 = AI_const v2 -> v1 = v2.
Proof.
  destruct v1, v2; destruct v, v0 => //=; try by intros H; inversion H; subst => //.
Qed.


Lemma app_app {A} (es1 es2 es3 es4: list A) :
  es1 ++ es2 = es3 ++ es4 ->
  length es1 = length es3 ->
  (es1, es2) = (es3, es4).
Proof.
  move: es2 es3 es4.
  elim: es1; destruct es3 => //=; move => es4 H2 Hlen; try by subst.
  inversion H2; subst; clear H2.
  inversion Hlen; clear Hlen.
  apply H in H3 => //.
  by inversion H3 => //; subst.
Qed.

Lemma combine_app {T1 T2: Type} (l1 l3: list T1) (l2 l4: list T2):
  length l1 = length l2 ->
  List.combine (l1 ++ l3) (l2 ++ l4) = List.combine l1 l2 ++ List.combine l3 l4.
Proof.
  generalize dependent l2.
  generalize dependent l3.
  generalize dependent l4.
  induction l1; move => l4 l3 l2 Hlen => /=; first by destruct l2 => //.
  - destruct l2 => //=.
    simpl in Hlen.
    inversion Hlen; subst; clear Hlen.
    f_equal.
    by apply IHl1.
Qed.

Lemma const_list_concat: forall vs1 vs2,
    const_list vs1 ->
    const_list vs2 ->
    const_list (vs1 ++ vs2).
Proof.
  move => vs1 vs2. elim vs1 => {vs1} //=.
  - move => a vs1' IHvs1 H1 H2. simpl in H1. simpl.
    apply andb_true_iff in H1. destruct H1. rewrite IHvs1 //=. by rewrite andbT.
Qed.

Lemma const_list_split: forall vs1 vs2,
    const_list (vs1 ++ vs2) ->
    const_list vs1 /\
    const_list vs2.
Proof.
  induction vs1 => //=; move => vs2 HConst.
  move/andP in HConst. destruct HConst.
  apply IHvs1 in H0. destruct H0.
  split => //.
  by apply/andP.
Qed.    

(** This lemma justifies the computation “to the first non-[const_list]”. **)
Lemma const_list_concat_inv : forall vs1 vs2 e1 e2 es1 es2,
  const_list vs1 ->
  const_list vs2 ->
  ~ is_const e1 ->
  ~ is_const e2 ->
  vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2 ->
  vs1 = vs2 /\ e1 = e2 /\ es1 = es2.
Proof.
  induction vs1 => vs2 e1 e2 es1 es2 C1 C2 N1 N2; destruct vs2 => /=; inversion 1; subst;
    try move: C1 => /= /andP [? ?] //;
    try move: C2 => /= /andP [? ?] //.
  - done.
  - apply IHvs1 in H2 => //. move: H2 => [? [? ?]]. by subst.
Qed.

Lemma const_list_take: forall vs l,
    const_list vs ->
    const_list (take l vs).
Proof.
  move => vs. induction vs => //=.
  - move => l HConst. destruct l => //=.
    + simpl. simpl in HConst. apply andb_true_iff in HConst. destruct HConst.
      apply andb_true_iff. split => //. by apply IHvs.
Qed.

Lemma v_to_e_is_const_list: forall vs,
    const_list (v_to_e_list vs).
Proof.
  move => vs. 
  induction vs => //=.
  rewrite IHvs. 
  unfold is_const.
  unfold e_to_v_opt.
  destruct a => //.
  destruct v => //. 
Qed.

Lemma v_to_e_cat: forall vs1 vs2,
    v_to_e_list vs1 ++ v_to_e_list vs2 = v_to_e_list (vs1 ++ vs2).
Proof.
  move => vs1. elim: vs1 => //=.
  - move => a l IH vs2. by rewrite IH.
Qed.



Lemma v_to_e_inj: forall vs1 vs2,
    v_to_e_list vs1 = v_to_e_list vs2 ->
    vs1 = vs2.
Proof.
  move => vs1.
  induction vs1; move => vs2; destruct vs2 => //=.
  move => Heq. inversion Heq; subst.
  f_equal; last 
    by apply IHvs1.
  destruct a, v; inversion H0 => //.
  destruct v => //.
  destruct v, v0 => //.
  destruct v, v0; inversion H2 => //. 
Qed.

Lemma split_vals_e_v_to_e_duality: forall es vs es',
    split_vals_e es = (vs, es') ->
    es = (v_to_e_list vs) ++ es'.
Proof.
  move => es vs. move: es. elim: vs => //.
  - move=> es es'. destruct es => //=.
    + by inversion 1.
    + destruct (e_to_v_opt a) => //.
      * by destruct (split_vals_e es).
      * by inversion 1.
  - move => a l H es es' HSplit. unfold split_vals_e in HSplit.
    destruct es => //. fold split_vals_e in HSplit.
    destruct (e_to_v_opt a0) eqn:Ha0 => //.
    destruct (split_vals_e es) eqn:Heqn.
    inversion HSplit; subst. simpl. f_equal; last by apply: H.
    destruct a0, a; inversion Ha0 => //.
    destruct b => //. by inversion H1.
    destruct b => //. by inversion H1.
Qed.

Lemma const_list_cons : forall a l,
  const_list (a :: l) = is_const a && const_list l.
Proof. by []. Qed.

Lemma v_to_e_list0 : v_to_e_list [::] = [::].
Proof. reflexivity. Qed.

 Lemma v_to_e_list1 : forall v, v_to_e_list [:: v] = [:: AI_const v].
Proof. reflexivity. Qed. 

Lemma e_is_trapP : forall e, reflect (e = AI_trap) (e_is_trap e).
Proof.
  case => //= >; by [ apply: ReflectF | apply: ReflectT ].
Qed.

Lemma es_is_trapP : forall l, reflect (l = [::AI_trap]) (es_is_trap l).
Proof.
  case; first by apply: ReflectF.
  move=> // a l. case l => //=.
  - apply: (iffP (e_is_trapP _)); first by elim.
    by inversion 1.
  - move=> >. by apply: ReflectF.
Qed.


Lemma split_n_is_take_drop: forall es n,
    split_n es n = (take n es, drop n es).
Proof.
  move => es n. move: es. elim:n => //=.
  - move => es. by destruct es.
  - move => n IH es'. destruct es' => //=.
    + by rewrite IH.
Qed.

Lemma update_list_at_is_set_nth: forall {X:Type} (l:list X) n x,
    n < size l ->
    set_nth x l n x = update_list_at l n x.
Proof.
  move => X l n x. move: n. elim: l => //=.
  move => a l IH n HLen. destruct n => //=.
  unfold update_list_at. simpl. f_equal. by apply IH.
Qed.

Lemma length_is_size: forall {X:Type} (l: list X),
    length l = size l.
Proof.
  move => X l. by elim: l.
Qed.

Lemma v_to_e_take_exchange: forall vs n,
    v_to_e_list (take n vs) = take n (v_to_e_list vs).
Proof.
  move => vs n. move: vs. elim:n => //=.
  - move => vs. by destruct vs.
  - move => n IH vs'. destruct vs' => //=.
    + by rewrite IH.
Qed.

Lemma v_to_e_drop_exchange: forall vs n,
    v_to_e_list (drop n vs) = drop n (v_to_e_list vs).
Proof.
  move => vs n. move: vs. elim:n => //=.
  - move => vs. by destruct vs.
  - move => n IH vs'. by destruct vs' => //=.
Qed.

Lemma v_to_e_size: forall vs,
    size (v_to_e_list vs) = size vs.
Proof.
  move => vs. elim: vs => //=.
  - move => a l IH. by f_equal.
Qed.      
      
(** This lemma is useful when an instruction consumes some expressions on the stack:
  we usually have to split a list of expressions by the expressions effectively
  consumed by the instructions and the one left. **)
Lemma v_to_e_take_drop_split: forall l n,
  v_to_e_list l = v_to_e_list (take n l) ++ v_to_e_list (drop n l).
Proof.
  move => l n. rewrite v_to_e_cat. by rewrite cat_take_drop.
Qed.

Lemma v_to_e_take: forall l n,
  v_to_e_list (take n l) = take n (v_to_e_list l).
Proof.
  move => + n. induction n => //.
  - move => l. by repeat rewrite take0.
  - move => l. destruct l => //. simpl. f_equal. by apply IHn.
Qed.

Lemma v_to_e_drop: forall l n,
  v_to_e_list (drop n l) = drop n (v_to_e_list l).
Proof.
  move => + n. induction n => //.
  - move => l. by repeat rewrite drop0.
  - move => l. destruct l => //. simpl. f_equal. by apply IHn.
Qed.

Lemma v_to_e_rev: forall l,
  v_to_e_list (rev l) = rev (v_to_e_list l).
Proof.
  elim => //=.
  move => a l IH. rewrite rev_cons. rewrite -cats1. rewrite -v_to_e_cat.
  rewrite rev_cons. rewrite -cats1. by rewrite -IH.
Qed.

Lemma to_b_list_concat: forall es1 es2 : seq administrative_instruction,
    to_b_list (es1 ++ es2) = to_b_list es1 ++ to_b_list es2.
Proof.
  induction es1 => //=.
  move => es2. by f_equal.
Qed.

Lemma to_e_list_basic: forall bes,
    es_is_basic (to_e_list bes).
Proof.
  induction bes => //=.
  constructor => //=.
Qed.

Lemma basic_concat: forall es1 es2,
    es_is_basic (es1 ++ es2) ->
    es_is_basic es1 /\ es_is_basic es2.
Proof.
  intros. apply List.Forall_app. done.
Qed.

Lemma basic_split: forall es1 es2,
    es_is_basic es1 ->
    es_is_basic es2 ->
    es_is_basic (es1 ++ es2).
Proof.
  intros. apply List.Forall_app => //.
Qed.

(* Lemma const_list_is_basic: forall es,
    const_list es ->
    es_is_basic es.
Proof.
  induction es => //=.
  move => H. move/andP in H. destruct H.
  split.
  - destruct a => //.
    unfold e_is_basic. by eauto.
  - by apply IHes.                                 
Qed. *)

Lemma to_b_list_rev: forall es : seq administrative_instruction,
    rev (to_b_list es) = to_b_list (rev es).
Proof.
  induction es => //=.
  repeat rewrite rev_cons.
  rewrite IHes.
  repeat rewrite -cats1.
  by rewrite to_b_list_concat.
Qed.

Lemma vs_to_vts_cat C: forall vs1 vs2,
    vs_to_vts C (vs1 ++ vs2) = vs_to_vts C vs1 ++ vs_to_vts C vs2.
Proof.
  induction vs1 => //=.
  move => vs2. by rewrite IHvs1.
Qed.
  
Lemma vs_to_vts_rev C: forall vs,
    vs_to_vts C (rev vs) = rev (vs_to_vts C vs).
Proof.
  induction vs => //=.
  repeat rewrite rev_cons.
  repeat rewrite -cats1.
  rewrite vs_to_vts_cat.
  by rewrite IHvs.
Qed.
  
Lemma const_es_exists: forall es,
    const_list es ->
    exists vs, es = v_to_e_list vs.
Proof.
  induction es => //=.
  - by exists [::].
  - move => HConst.
    move/andP in HConst. destruct HConst.
    destruct a => //=.
    + destruct b => //=.
      * edestruct IHes => //=.
        exists (VAL_num v :: x). simpl. by rewrite H1.
      * edestruct IHes => //=.
        exists (VAL_ref (VAL_ref_null r) :: x). simpl. by rewrite H1.
    + edestruct IHes => //=.
      exists (VAL_ref (VAL_ref_func f) :: x). simpl. by rewrite H1.
    + edestruct IHes => //=.
      exists (VAL_ref (VAL_ref_exn e t) :: x). simpl. by rewrite H1.
    + edestruct IHes => //=.
      exists (VAL_ref (VAL_ref_cont f) :: x). simpl. by rewrite H1.
Qed.

Lemma b_e_elim: forall bes es,
    to_e_list bes = es ->
    bes = to_b_list es /\ es_is_basic es.
Proof.
  induction bes; move => es H => //=.
  - rewrite -H => //=. split => //. 
  - simpl in H. assert (es = to_e_list (a :: bes)) as H1.
    + by rewrite -H.
    + rewrite H1. split.
      -- simpl. f_equal. by apply IHbes.
      -- by apply to_e_list_basic.
Qed.

Lemma e_b_elim: forall bes es,
    bes = to_b_list es ->
    es_is_basic es ->
    es = to_e_list bes.
Proof.
  induction bes; move => es H1 H2 => //=.
  - by destruct es => //=.
  - destruct es => //=. simpl in H1. inversion H2; subst. 
    inversion H1; subst. destruct a0 => //. 
    f_equal. apply IHbes => //=.
Qed.
    
Lemma to_e_list_injective: forall bes bes',
    to_e_list bes = to_e_list bes' ->
    bes = bes'.
Proof.
  move => bes bes' H.
  apply b_e_elim in H; destruct H; subst => //=.
  induction bes' => //=.
  f_equal. apply IHbes'. by apply to_e_list_basic.
Qed.

Lemma to_e_list_cat: forall bes1 bes2,
    to_e_list (bes1 ++ bes2) = to_e_list bes1 ++ to_e_list bes2.
Proof.
  induction bes1 => //.
  move => bes2. simpl. by f_equal.
Qed.

Lemma concat_cancel_last: forall {X:Type} (l1 l2: seq X) (e1 e2:X),
    l1 ++ [::e1] = l2 ++ [::e2] ->
    l1 = l2 /\ e1 = e2.
Proof.
  move => X l1 l2 e1 e2 H.
  assert (rev (l1 ++ [::e1]) = rev (l2 ++ [::e2])); first by rewrite H.
  repeat rewrite rev_cat in H0. inversion H0.
  rewrite - (revK l1). rewrite H3. split => //. by apply revK.
Qed.

Lemma concat_cancel_last_n: forall (l1 l2 l3 l4: seq value_type),
    l1 ++ l2 = l3 ++ l4 ->
    size l2 = size l4 ->
    (l1 == l3) && (l2 == l4).
Proof.
  move => l1 l2 l3 l4 HCat HSize.
  rewrite -eqseq_cat; first by apply/eqP.
  assert (size (l1 ++ l2) = size (l3 ++ l4)); first by rewrite HCat.
  repeat rewrite size_cat in H.
  rewrite HSize in H. by lias.
Qed.

Lemma extract_list1 : forall {X:Type} (es: seq X) (e1 e2:X),
    es ++ [::e1] = [::e2] ->
    es = [::] /\ e1 = e2.
Proof.
  move => X es e1 e2 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma extract_list2 : forall {X:Type} (es: seq X) (e1 e2 e3:X),
    es ++ [::e1] = [::e2; e3] ->
    es = [::e2] /\ e1 = e3.
Proof.
  move => X es e1 e2 e3 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma extract_list3 : forall {X:Type} (es: seq X) (e1 e2 e3 e4:X),
    es ++ [::e1] = [::e2; e3; e4] ->
    es = [::e2; e3] /\ e1 = e4.
Proof.
  move => X es e1 e2 e3 e4 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma extract_list4 : forall {X:Type} (es: seq X) (e1 e2 e3 e4 e5:X),
    es ++ [::e1] = [::e2; e3; e4; e5] ->
    es = [::e2; e3; e4] /\ e1 = e5.
Proof.
  move => X es e1 e2 e3 e4 e5 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma list_nth_prefix: forall {X:Type} (l1 l2: seq X) x,
    List.nth_error (l1 ++ [::x] ++ l2) (length l1) = Some x.
Proof.
  move => X. induction l1 => //=.
Qed.




(** * Tactics **)

(** [gen_ind] perform an induction over predicates like [be_typing], generalising its parameters,
  but not generalising any section variables such as [host_function].
  The reason for this tactic is that [dependent induction] is far too aggressive
  in its generalisation, and prevents the use of some lemmas. **)

(** The first step is to name each parameter of the predicate. **)
Ltac gen_ind_pre H :=
  let rec aux v :=
    lazymatch v with
    | ?f ?x =>
      let only_do_if_ok_direct t cont :=
        lazymatch t with
        | Type => idtac
        | _ => cont tt
        end in
      let t := type of x in
      only_do_if_ok_direct t ltac:(fun _ =>
        let t :=
          match t with
          | _ _ => t
          | ?t => eval unfold t in t
          | _ => t
          end in
        only_do_if_ok_direct t ltac:(fun _ =>
          let x' :=
            let rec get_name x :=
              match x with
              | ?f _ => get_name f
              | _ => fresh x
              | _ => fresh "x"
              end in
            get_name x in
          move: H;
          set_eq x' x;
          let E := fresh "E" x' in
          move=> E H));
      aux f
    | _ => idtac
    end in
  let Ht := type of H in
  aux Ht.

(** Then, each of the associated parameters can be generalised. **)
Ltac gen_ind_gen H :=
  let rec try_generalize t :=
    lazymatch t with
    | ?f ?x => try_generalize f; try_generalize x
    | ?x => is_variable x ltac:(generalize dependent x) ltac:(idtac)
    | _ => fail "unable to generalize" t
    end in
  let rec aux v :=
    lazymatch v with
    | ?f ?x => 
    lazymatch goal with
      | _ : x = ?y |- _ => try_generalize y
      | _ => fail "unexpected term" v
      end;
      aux f
    | _ => idtac
    end in
  let Ht := type of H in
  aux Ht.

(** After the induction, one can inverse them again (and do some cleaning). **)
Ltac gen_ind_post :=
  repeat lazymatch goal with
  | |- _ = _ -> _ => inversion 1
  | |- _ -> _ => intro
  end;
  repeat lazymatch goal with
  | H: True |- _ => clear H
  | H: ?x = ?x |- _ => clear H
  end.

(** Wrapping every part of the generalised induction together. **)
Ltac gen_ind H :=
  gen_ind_pre H;
  gen_ind_gen H;
  induction H;
  gen_ind_post.

(** Similar to [gen_ind H; subst], but cleaning just a little bit more. **)
Ltac gen_ind_subst H :=
  gen_ind H;
  subst;
  gen_ind_post.

(** Calls the continuation on [v] or, if it failed, on [v] whose root has been unfolded.
  This is useful for tactics with pattern mtaching recognising a predicate which is
  frequently folded in a section, like [be_typing]. **)
Ltac call_unfold v cont :=
  let rec unfold_root :=
    lazymatch v with
    | ?f ?x =>
      let f := unfold_root f in
      constr:(f x)
    | ?x => eval unfold x in x
    end in
  first [
      cont v
    | let v := unfold_root v in
      cont v ].

(** Perform basic simplifications of [es_is_basic]. **)
Ltac basic_inversion :=
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


(** Rewrite hypotheses on the form [_ ++ [:: _] = _] as some easier to use equalities. **)
Ltac extract_listn :=
  repeat lazymatch goal with
  | H: (?es ++ [::?e])%list = [::_] |- _ =>
    apply extract_list1 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_] |- _ =>
    apply extract_list1 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _] |- _ =>
    apply extract_list2 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_; _] |- _ =>
    apply extract_list2 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_; _; _] |- _ =>
    apply extract_list3 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _; _] |- _ =>
    apply extract_list3 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _; _; _] |- _ =>
    apply extract_list4 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_; _; _; _] |- _ =>
    apply extract_list4 in H; destruct H; subst
  | H: _ :: _ = (_ ++ _)%list |- _ => symmetry in H
  | H: _ :: _ = _ ++ _ |- _ => symmetry in H
         end.

Ltac fold_upd_context :=
  lazymatch goal with
  | |- context [upd_local (upd_return ?C ?ret) ?loc] =>
    replace (upd_local (upd_return C ret) loc) with
        (upd_local_return C ret loc); try by destruct C
  | |- context [upd_return (upd_local ?C ?ret) ?loc] =>
    replace (upd_return (upd_local C ret) loc) with
        (upd_local_return C ret loc); try by destruct C
  end.



(** * More Advanced Lemmas **)



Lemma lfilled_swap : forall i lh es LI es', 
  lfilled i lh es LI ->
  exists LI', lfilled i lh es' LI'.
Proof.
  intros i lh. generalize dependent i.
  induction lh;intros i es LI es' Hfill%lfilled_Ind_Equivalent.
  - inversion Hfill; subst.
    exists (l ++ es' ++ l0).
    apply lfilled_Ind_Equivalent. by constructor. 
  - inversion Hfill;subst.
    apply lfilled_Ind_Equivalent in H8.
    apply IHlh with (es':=es') in H8 as [LI' HLI'].
    exists (l ++ [::AI_label n l0 LI'] ++ l1).
    apply lfilled_Ind_Equivalent. constructor;auto.
    by apply lfilled_Ind_Equivalent.
  - inversion Hfill;subst.
    apply lfilled_Ind_Equivalent in H7.
    apply IHlh with (es':=es') in H7 as [LI' HLI'].
    exists (l ++ [::AI_handler l0 LI'] ++ l1).
    apply lfilled_Ind_Equivalent. constructor;auto.
    by apply lfilled_Ind_Equivalent.
  - inversion Hfill;subst.
    apply lfilled_Ind_Equivalent in H8.
    apply IHlh with (es':=es') in H8 as [LI' HLI'].
    exists (l ++ [::AI_prompt l0 l1 LI'] ++ l2).
    apply lfilled_Ind_Equivalent. constructor;auto.
    by apply lfilled_Ind_Equivalent.
Qed.

Lemma lfilled_inj : forall i lh es LI LI',
  lfilled i lh es LI ->
  lfilled i lh es LI' ->
  LI = LI'.
Proof.
  intros i lh. generalize dependent i.
  induction lh; intros i es LI LI'
                      Hfill1%lfilled_Ind_Equivalent
                      Hfill2%lfilled_Ind_Equivalent.
  - inversion Hfill1; subst.
    inversion Hfill2; subst. done. 
  - inversion Hfill1; subst.
    inversion Hfill2; subst.
    rewrite (IHlh k es LI0 LI);auto;by apply lfilled_Ind_Equivalent.
  - inversion Hfill1; subst.
    inversion Hfill2; subst.
    rewrite (IHlh i es LI0 LI);auto; by apply lfilled_Ind_Equivalent.
  - inversion Hfill1; subst.
    inversion Hfill2; subst.
    rewrite (IHlh i es LI0 LI);auto; by apply lfilled_Ind_Equivalent.
Qed.


Lemma hfilled_inj : forall i i' lh es LI LI',
    hfilled i lh es LI ->
    hfilled i' lh es LI' ->
  LI = LI'.
Proof.
  intros i i' lh. 
  induction lh; intros es LI LI'
                      Hfill1%hfilled_Ind_Equivalent
                      Hfill2%hfilled_Ind_Equivalent.
  - inversion Hfill1; subst.
    inversion Hfill2; subst. done. 
  - inversion Hfill1; subst.
    inversion Hfill2; subst.
    rewrite (IHlh es LI0 LI);auto;by apply hfilled_Ind_Equivalent.
  - inversion Hfill1; subst.
    inversion Hfill2; subst.
    rewrite (IHlh es LI0 LI);auto; by apply hfilled_Ind_Equivalent.
  - inversion Hfill1; subst.
    inversion Hfill2; subst.
    rewrite (IHlh es LI0 LI);auto; by apply hfilled_Ind_Equivalent.
  - inversion Hfill1; subst.
    inversion Hfill2; subst.
    rewrite (IHlh es LI0 LI);auto; by apply hfilled_Ind_Equivalent.
Qed.

Lemma map_Some_inj {A} (l1 l2: list A) :
  map Some l1 = map Some l2 -> l1 = l2.
Proof.
  generalize dependent l2.
  induction l1 => //=.
  all: destruct l2 => //=.
  intros H; inversion H; subst.
  f_equal.
  by apply IHl1.
Qed. 

Lemma lfilled_collapse1: forall n lh vs es LI l,
    lfilledInd n lh (vs++es) LI ->
    const_list vs ->
    length vs >= l ->
    exists lh', lfilledInd n lh' ((drop (length vs-l) vs) ++ es) LI.
Proof.
  move => n lh vs es LI l HLF HConst HLen.
  remember (vs++es) as es'. induction HLF; subst.
  - exists (LH_base (vs0 ++ (take (length vs - l) vs)) es').
    replace (vs0++(vs++es)++es') with ((vs0++take (length vs - l) vs) ++ (drop (length vs - l) vs ++ es) ++ es').
    { apply LfilledBase. apply const_list_concat => //=.
      by apply const_list_take. }
    repeat rewrite -catA. f_equal.
    repeat rewrite catA. do 2 f_equal.
    by apply cat_take_drop. 
  - destruct IHHLF => //. eexists (LH_rec _ _ _ _ _). apply LfilledRec => //. by apply H0.
  - destruct IHHLF => //. eexists (LH_handler _ _ _ _). apply LfilledHandler => //. exact H0.
  - destruct IHHLF => //. eexists (LH_prompt _ _ _ _ _). apply LfilledPrompt => //. exact H0.
Qed.

Lemma lfilled_collapse2: forall n lh es es' LI,
    lfilledInd n lh (es++es') LI ->
    exists lh', lfilledInd n lh' es LI.
Proof.
  move => n lh es es' LI HLF. remember (es ++ es') as Ees. induction HLF; subst.
  - eexists (LH_base _ _). rewrite <- catA. by apply LfilledBase.
  - destruct IHHLF => //. eexists (LH_rec _ _ _ _ _). apply LfilledRec => //. by apply H0.
  - destruct IHHLF => //. eexists (LH_handler _ _ _ _). apply LfilledHandler => //. exact H0.
  - destruct IHHLF => //. eexists (LH_prompt _ _ _ _ _). apply LfilledPrompt => //. exact H0.
Qed.

Lemma lfilled_collapse3: forall k lh n les es LI,
    lfilledInd k lh [:: AI_label n les es] LI ->
    exists lh', lfilledInd (k+1) lh' es LI.
Proof.
  move => k lh n les es LI HLF. remember [:: AI_label n les es] as E.  induction HLF; subst.
  - eexists (LH_rec _ _ _ _ _). apply LfilledRec. auto.
    assert (lfilledInd 0 (LH_base nil nil) es ([::] ++ es ++ [::])). { by apply LfilledBase. }
    simpl in H0. rewrite cats0 in H0. by apply H0.
  - destruct IHHLF => //. eexists (LH_rec _ _ _ _ _). apply LfilledRec => //. by apply H0.
  - destruct IHHLF => //. eexists (LH_handler _ _ _ _). apply LfilledHandler => //. exact H0.
  - destruct IHHLF => //. eexists (LH_prompt _ _ _ _ _). apply LfilledPrompt => //. exact H0.
Qed.

Lemma lfilled_deterministic: forall k lh es les les',
    lfilledInd k lh es les ->
    lfilledInd k lh es les' ->
    les = les'.
Proof.
  move => k lh es les les' HLF HLF'.
  apply lfilled_Ind_Equivalent in HLF. unfold operations.lfilled in HLF.
  apply lfilled_Ind_Equivalent in HLF'. unfold operations.lfilled in HLF'.
  destruct (lfill k lh es) => //.
  replace les' with l.
  { move: HLF. by apply/eqseqP. }
  symmetry. move: HLF'. by apply/eqseqP. 
Qed.  

Lemma all_projection: forall {X:Type} f (l:seq X) n x,
    all f l ->
    List.nth_error l n = Some x ->
    f x.
Proof.
  move => X f l n x.
  generalize dependent l.
  induction n => //; destruct l => //=; move => HF HS; remove_bools_options => //.
  eapply IHn; by eauto.
Qed.

Lemma all2_projection: forall {X Y:Type} f (l1:seq X) (l2:seq Y) n x1 x2,
    all2 f l1 l2 ->
    List.nth_error l1 n = Some x1 ->
    List.nth_error l2 n = Some x2 ->
    f x1 x2.
Proof.
  move => X Y f l1 l2 n.
  generalize dependent l1.
  generalize dependent l2.
  induction n => //=; move => l2 l1 x1 x2 HALL HN1 HN2.
  - destruct l1 => //=. destruct l2 => //=.
    inversion HN1. inversion HN2. subst. clear HN1. clear HN2.
    simpl in HALL. move/andP in HALL. by destruct HALL.
  - destruct l1 => //=. destruct l2 => //=.
    simpl in HALL. move/andP in HALL. destruct HALL.
    eapply IHn; by eauto.
Qed.

Lemma all2_Forall2 {T1 T2: Type} r (l1: list T1) (l2: list T2):
  all2 r l1 l2 <-> List.Forall2 r l1 l2.
Proof.
  move: l2.
  elim: l1 => //=.
  - move => l2; destruct l2 => //=.
    split => //.
    move => Hcontra.
    by inversion Hcontra.
  - move => e l1 IH l2.
    destruct l2 => //=.
    + split => //.
      move => Hcontra.
      by inversion Hcontra.
    + split; move => H.
      * move/andP in H.
        destruct H.
        constructor => //.
        by apply IH.
      * apply/andP.
        inversion H; subst; clear H.
        split => //.
        by apply IH.
Qed.


Definition function {X Y:Type} (f: X -> Y -> Prop) : Prop :=
  forall x y1 y2, ((f x y1 /\ f x y2) -> y1 = y2).

Lemma all2_function_unique: forall {X Y:Type} f (l1:seq X) (l2 l3:seq Y),
    all2 f l1 l2 ->
    all2 f l1 l3 ->
    function f ->
    l2 = l3.
Proof.
  move => X Y f l1.
  induction l1 => //=; move => l2 l3 HA1 HA2 HF.
  - destruct l2 => //. by destruct l3 => //.
  - destruct l2 => //=; destruct l3 => //=.
    simpl in HA1. simpl in HA2.
    move/andP in HA1. move/andP in HA2.
    destruct HA1. destruct HA2.
    unfold function in HF.
    assert (y = y0); first by eapply HF; eauto.
    rewrite H3. f_equal.
    by apply IHl1.
Qed.


(** The decreasing measure used in the definition of [lfilled_pickable_rec_gen]. **)
(* Definition lfilled_pickable_rec_gen_measure (LI : seq administrative_instruction) :=
  TProp.max
    (seq_administrative_instruction_rect'
       (fun _ => 0)
       0
       (fun _ => 0)
       (fun _ LI1 LI2 m1 m2 => 1 + TProp.max m2)
       (fun _ _ LI' m => 0)
       (fun _ _ _ => 0)
       LI). *)

Fixpoint lfilled_pickable_rec_gen_measure_single (e : administrative_instruction) :=
  match e with
  | AI_handler _ es1
  | AI_prompt _ _ es1
  | AI_label _ _ es1 =>
      1 + List.fold_left (fun a b => max a (lfilled_pickable_rec_gen_measure_single b)) es1 0
  | _ => 0
  end.
     
                

Definition lfilled_pickable_rec_gen_measure (LI : seq administrative_instruction) :=
  List.fold_left (fun a b => max a (lfilled_pickable_rec_gen_measure_single b)) LI 0.


Lemma fold_left_max_rem {A} n (l : seq A) f:
  List.fold_left (fun a b => max a (f b)) l n = max n (List.fold_left (fun a b => max a (f b)) l 0).
Proof.
  generalize dependent n. induction l; intros n => //=. lias.
  rewrite (IHl (max n (f a))). rewrite (IHl (f a)).
  lias.
Qed. 

Lemma fold_left_max_app_cons {A} x (l : seq A) f n:
  List.fold_left (fun a b => max a (f b)) (x :: l) n =
    max (f x) (List.fold_left (fun a b => max a (f b)) l n).
Proof.
  simpl. rewrite (fold_left_max_rem (max n (f x))).
  rewrite (fold_left_max_rem n).
  lias.
Qed. 



Lemma lfilled_pickable_rec_gen_measure_cons : forall I LI,
  lfilled_pickable_rec_gen_measure LI <= lfilled_pickable_rec_gen_measure (I :: LI).
Proof.
  move=> I LI. unfold lfilled_pickable_rec_gen_measure.
  rewrite fold_left_max_app_cons. lias.
Qed.

Lemma lfilled_pickable_rec_gen_measure_concat_l : forall LI1 LI2,
  lfilled_pickable_rec_gen_measure LI1 <= lfilled_pickable_rec_gen_measure (LI1 ++ LI2).
Proof.
  move => LI1 LI2. induction LI1 => /=.
  - rewrite {1} /lfilled_pickable_rec_gen_measure /=. by lias.
  - rewrite /lfilled_pickable_rec_gen_measure /=.
    do 2 rewrite (fold_left_max_rem (_ a)).
    unfold lfilled_pickable_rec_gen_measure in IHLI1. lias.
Qed.

Lemma lfilled_pickable_rec_gen_measure_concat_r : forall LI1 LI2,
  lfilled_pickable_rec_gen_measure LI2 <= lfilled_pickable_rec_gen_measure (LI1 ++ LI2).
Proof.
  move => LI1 LI2. induction LI1 => /=.
  - rewrite {1} /lfilled_pickable_rec_gen_measure /=. by lias.
  - rewrite /lfilled_pickable_rec_gen_measure /=.
    rewrite (fold_left_max_rem (_ a)).
    unfold lfilled_pickable_rec_gen_measure in IHLI1. lias.
Qed.

Lemma lfilled_pickable_rec_gen_measure_label_r : forall n es LI LI',
  lfilled_pickable_rec_gen_measure LI < lfilled_pickable_rec_gen_measure (AI_label n es LI :: LI').
Proof.
  move=> n es LI LI'. rewrite /lfilled_pickable_rec_gen_measure /=.
  rewrite (fold_left_max_rem (S _)). lias. 
Qed.

Lemma lfilled_pickable_rec_gen_measure_handler_r : forall hs LI LI',
  lfilled_pickable_rec_gen_measure LI < lfilled_pickable_rec_gen_measure (AI_handler hs LI :: LI').
Proof.
  move=> hs LI LI'. rewrite /lfilled_pickable_rec_gen_measure /=.
  rewrite (fold_left_max_rem (S _)). lias. 
Qed.
Lemma lfilled_pickable_rec_gen_measure_prompt_r : forall ts hs LI LI',
  lfilled_pickable_rec_gen_measure LI < lfilled_pickable_rec_gen_measure (AI_prompt ts hs LI :: LI').
Proof.
  move=> ts hs LI LI'. rewrite /lfilled_pickable_rec_gen_measure /=.
  rewrite (fold_left_max_rem (S _)). lias. 
Qed.

(** A helper definition for [lfilled_decidable_rec]. **)
Definition lfilledInd_pickable_rec_gen : forall fes,
  (forall es' lh lh' n0, decidable (lfilledInd 0 lh (fes n0 lh') es')) ->
  forall es', pickable2 (fun n lh => lfilledInd n lh (fes n lh) es').
Proof.
  move=> fes D0 es'.
  apply: (@pickable2_equiv _ _ (fun n lh => lfilledInd n lh (fes (0+n) lh) es')); first by [].
  move: 0 => k.
  have [m E]: { m | lfilled_pickable_rec_gen_measure es' = m }; first by eexists.
  move: fes D0 es' E k.
  assert (forall m' m, m <= m' ->
                  forall fes : nat -> lholed -> seq administrative_instruction,
                    (forall (es' : seq administrative_instruction) (lh lh' : lholed) (n0 : nat),
                        decidable (lfilledInd 0 lh (fes n0 lh') es')) ->
                    forall es' : seq administrative_instruction,
                      lfilled_pickable_rec_gen_measure es' = m ->
                      forall k : nat,
                        pickable2 (fun (n : nat) (lh : lholed) => lfilledInd n lh (fes (k + n) lh) es')) as H.
  2:{ apply (H (S m) m). lias. }
  clear m. induction m'.

  { move=> m Hm fes D0 es' E k.
    destruct m; last lias.
    have Dcl: forall vs, decidable (const_list vs).
    { move=> vs. by apply: is_true_decidable. }
    (** First, we check whether we can set [n = 0]. **)
    have P0: pickable2 (fun vs es'' =>
                       let lh := LH_base vs es'' in
                       let es := fes k lh in
                       es' = vs ++ es ++ es'' /\ const_list vs /\ lfilledInd 0 lh es es').
    - have: pickable3 (fun vs es es'' =>
                         es' = vs ++ es ++ es'' /\ let lh := LH_base vs es'' in
                                                  es = fes k lh /\ const_list vs /\ lfilledInd 0 lh es es').
      + apply: list_split_pickable3_gen. move=> vs es es'' Ees /=.
        case E': (es == fes k (LH_base vs es'')); move/eqP: E' => E'.
        * rewrite E'. repeat apply: decidable_and => //. by apply: eq_comparable.
        * right. by move=> [Ees2 [Cl I]].
      + case.
        * move=> [[[vs es] es''] [E1 [E2 [Cl I]]]]. left. exists (vs, es''). by subst.
        * move=> Ex. right. move=> [vs [es'' [E' [Cl I]]]]. apply: Ex.
          by repeat eexists; eassumption.
    - case P0.
      + move=> [[vs es''] [E' [Cvs I]]]. left. exists (0, LH_base vs es'').
        subst. rewrite_by (k + 0 = k). by apply: LfilledBase.
      + move=> nE.
        (** Otherwise, we have to apply [LfilledRec]. **)
        have Dparse: forall es' : seq administrative_instruction,
        decidable (exists n es1 LI es2, es' = [:: AI_label n es1 LI] ++ es2).
        * clear. move=> es'.
          have Pparse: pickable4 (fun n es1 LI es2 => es' = [:: AI_label n es1 LI] ++ es2).
          -- let no := by intros; right; intros (?&?&?&?&?) in
             (case es'; first by no); case; try by no.
             move=> n l1 l2 l3. left. by eexists (n, l1, l2, l3).
          -- convert_pickable Pparse.
        * case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse es)) es').
          -- move=> [[vs es''] [E1 [C Ex]]].
             destruct es'' as [| [| | | | | | | | | | | n es1 LI | |] es2];
               try solve [ exfalso; move: Ex => [? [? [? [? E']]]]; inversion E' ].
             clear Ex. rewrite E1.
             exfalso. subst es'.
             specialize (lfilled_pickable_rec_gen_measure_concat_r vs (AI_label n es1 LI :: es2)) as H.
             specialize (lfilled_pickable_rec_gen_measure_label_r n es1 LI es2) as H'.
             lias. 
          -- move=> nE'.
             (** If we get here, we have to apply [LfilledHandler]. **)
             have Dparse': forall es': seq administrative_instruction,
                 decidable (exists hs LI es2, es' = [:: AI_handler hs LI] ++ es2).
             ++ clear. move => es'.
                have Pparse: pickable3 (fun hs LI es2 => es' = [:: AI_handler hs LI] ++ es2).
                ** let no := by intros; right; intros (?&?&?&?) in
                   (case es'; first by no); case; try by no.
                   move => hs l0 l1. left. by eexists (hs, l0, l1).
                ** convert_pickable Pparse.
             ++ case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse' es)) es').
                ** move => [[vs es''] [E1 [C Ex]]].
                   destruct es'' as [| [| | | | | | | | hs LI| | | | |] es2];
                     try solve [ exfalso; move: Ex => [? [? [? E']]]; inversion E' ].
                   clear Ex. rewrite E1.
                   exfalso. subst es'.
                   specialize (lfilled_pickable_rec_gen_measure_concat_r vs (AI_handler hs LI :: es2)) as H.
                   specialize (lfilled_pickable_rec_gen_measure_handler_r hs LI es2) as H'.
                   lias.
                ** move => nE''.
                     (** If we get here, we have to apply [LfilledPrompt]. **)
             have Dparse'': forall es': seq administrative_instruction,
                 decidable (exists ts hs LI es2, es' = [:: AI_prompt ts hs LI] ++ es2).
                   --- clear. move => es'.
                       have Pparse: pickable4 (fun ts hs LI es2 => es' = [:: AI_prompt ts hs LI] ++ es2).
                       +++ let no := by intros; right; intros (?&?&?&?&?) in
                           (case es'; first by no); case; try by no.
                           move => ts hs l0 l1. left. by eexists (ts, hs, l0, l1).
                       +++ convert_pickable Pparse.
                   --- case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse'' es)) es').
                       +++ move => [[vs es''] [E1 [C Ex]]].
                           destruct es'' as [| [| | | | | | | | | ts hs LI | | | |] es2];
                             try solve [ exfalso; move: Ex => [? [? [? [? E']]]]; inversion E' ].
                           clear Ex. rewrite E1.
                           exfalso. subst es'.
                           specialize (lfilled_pickable_rec_gen_measure_concat_r vs (AI_prompt ts hs LI :: es2)) as H.
                           specialize (lfilled_pickable_rec_gen_measure_prompt_r ts hs LI es2) as H'.
                           lias.
                       +++ move => nE'''.
                           right. move=> [n [lh I]]. inversion I; subst.
                           *** apply: nE. do 2 eexists. rewrite_by (k + 0 = k). repeat split; try eassumption.
                               by apply: LfilledBase.
                           *** apply: nE'. by repeat eexists.
                           *** apply: nE''. by repeat eexists.
                           *** apply: nE'''. by repeat eexists.
  } 

   move=> m Hm fes D0 es' E k.
  have Dcl: forall vs, decidable (const_list vs).
  { move=> vs. by apply: is_true_decidable. }
  (** First, we check whether we can set [n = 0]. **)
  have P0: pickable2 (fun vs es'' =>
                       let lh := LH_base vs es'' in
                       let es := fes k lh in
                       es' = vs ++ es ++ es'' /\ const_list vs /\ lfilledInd 0 lh es es').
  {
    have: pickable3 (fun vs es es'' =>
      es' = vs ++ es ++ es'' /\ let lh := LH_base vs es'' in
      es = fes k lh /\ const_list vs /\ lfilledInd 0 lh es es').
    {
      apply: list_split_pickable3_gen. move=> vs es es'' Ees /=.
      case E': (es == fes k (LH_base vs es'')); move/eqP: E' => E'.
      - rewrite E'. repeat apply: decidable_and => //. by apply: eq_comparable.
      - right. by move=> [Ees2 [Cl I]].
    }
    case.
    - move=> [[[vs es] es''] [E1 [E2 [Cl I]]]]. left. exists (vs, es''). by subst.
    - move=> Ex. right. move=> [vs [es'' [E' [Cl I]]]]. apply: Ex.
      by repeat eexists; eassumption.
  }
  case P0.
  {
    move=> [[vs es''] [E' [Cvs I]]]. left. exists (0, LH_base vs es'').
    subst. rewrite_by (k + 0 = k). by apply: LfilledBase.
  }
  move=> nE.
  (** Otherwise, we have to apply [LfilledRec]. **)
  have Dparse: forall es' : seq administrative_instruction,
    decidable (exists n es1 LI es2, es' = [:: AI_label n es1 LI] ++ es2).
  {
    clear. move=> es'.
    have Pparse: pickable4 (fun n es1 LI es2 => es' = [:: AI_label n es1 LI] ++ es2).
    {
      let no := by intros; right; intros (?&?&?&?&?) in
      (case es'; first by no); case; try by no.
      move=> n l1 l2 l3. left. by exists (n, l1, l2, l3).
    }
    convert_pickable Pparse.
  }
  case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse es)) es').
  - move=> [[vs es''] [E1 [C Ex]]].
    destruct es'' as [| [| | | | | | | | | | | n es1 LI | |] es2];
      try solve [ exfalso; move: Ex => [? [? [? [? E']]]]; inversion E' ].
    clear Ex. rewrite E1.
    destruct m.
    { exfalso. subst es'.
      specialize (lfilled_pickable_rec_gen_measure_concat_r vs (AI_label n es1 LI :: es2)) as H.
      specialize (lfilled_pickable_rec_gen_measure_label_r n es1 LI es2) as H'.
      lias. 
    } 
    have I_LI: (lfilled_pickable_rec_gen_measure LI <= m').
    {
      assert (lfilled_pickable_rec_gen_measure LI < S m); last lias.
      rewrite -E E1. eapply leq_trans.
      - by eapply lfilled_pickable_rec_gen_measure_label_r.
      - by apply: lfilled_pickable_rec_gen_measure_concat_r.
    }
    set fes' := fun k lh => fes (k + 1) (LH_rec vs n es1 lh es2).
    have D1: forall es' lh lh' n0, decidable (lfilledInd 0 lh (fes' n0 lh') es').
    { move=> ? ? ? ?. by apply: D0. }
    specialize (IHm' (lfilled_pickable_rec_gen_measure LI) I_LI fes' D1 LI (erefl _) k) as [[[n' lh] LF]|NP].
    + eapply LfilledRec with (vs := vs) in LF => //.
      left. exists (n'.+1, LH_rec vs n es1 lh es2).
      move: LF. rewrite /fes'. rewrite_by (k + n' + 1 = k + n'.+1) => /= LF. by apply: LF.
    + right. move=> [n' [lh FI]]. apply: NP. inversion FI; subst.
      * exfalso. apply: nE. exists vs0. exists es'0. repeat split => //.
        -- rewrite -H. by rewrite_by (k + 0 = k).
        -- by rewrite_by (k = k + 0).
      * apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
        exists k0. eexists. rewrite /fes'. rewrite_by (k + k0 + 1 = k + k0.+1). by apply: H4.
      * apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
      * apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
        
  - move=> nE'.
    (** If we get here, we have to apply [LfilledHandler]. **)
    have Dparse': forall es': seq administrative_instruction,
        decidable (exists hs LI es2, es' = [:: AI_handler hs LI] ++ es2).
    + clear. move => es'.
      have Pparse: pickable3 (fun hs LI es2 => es' = [:: AI_handler hs LI] ++ es2).
      * let no := by intros; right; intros (?&?&?&?) in
                   (case es'; first by no); case; try by no.
        move => hs l0 l1. left. by eexists (hs, l0, l1).
      * convert_pickable Pparse.
    + case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse' es)) es').
      * move => [[vs es''] [E1 [C Ex]]].
        destruct es'' as [| [| | | | | | | | hs LI| | | | |] es2];
          try solve [ exfalso; move: Ex => [? [? [? E']]]; inversion E' ].
        clear Ex. rewrite E1.
        destruct m.
        { exfalso. subst es'.
          specialize (lfilled_pickable_rec_gen_measure_concat_r vs (AI_handler hs LI :: es2)) as H.
          specialize (lfilled_pickable_rec_gen_measure_handler_r hs LI es2) as H'.
          lias. 
        } 
        have I_LI: (lfilled_pickable_rec_gen_measure LI <= m').
        {
          assert (lfilled_pickable_rec_gen_measure LI < S m); last lias.
          rewrite -E E1. eapply leq_trans.
          - by eapply lfilled_pickable_rec_gen_measure_handler_r.
          - by apply: lfilled_pickable_rec_gen_measure_concat_r.
        }
        set fes' := fun k lh => fes k (LH_handler vs hs lh es2).
        have D1: forall es' lh lh' n0, decidable (lfilledInd 0 lh (fes' n0 lh') es').
        { move=> ? ? ? ?. by apply: D0. }
        specialize (IHm' (lfilled_pickable_rec_gen_measure LI) I_LI fes' D1 LI (erefl _) k) as [[[n' lh] LF]|NP].
        -- eapply LfilledHandler with (bef := vs) in LF => //.
           left. exists (n', LH_handler vs hs lh es2). 
           move: LF. rewrite /fes'. intros H. exact H. 
        -- right. move=> [n' [lh FI]]. apply: NP. inversion FI; subst.
           ++ exfalso. apply: nE. exists vs0. exists es'0. repeat split => //.
              ** rewrite -H. by rewrite_by (k + 0 = k).
              ** by rewrite_by (k = k + 0).
           ++ apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
           ++ apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
              eexists. eexists. rewrite /fes'. exact H4.
           ++ apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.


      * move=> nE''.
    (** If we get here, we have to apply [LfilledPrompt]. **)
    have Dparse'': forall es': seq administrative_instruction,
        decidable (exists ts hs LI es2, es' = [:: AI_prompt ts hs LI] ++ es2).
        --  clear. move => es'.
            have Pparse: pickable4 (fun ts hs LI es2 => es' = [:: AI_prompt ts hs LI] ++ es2).
            ++ let no := by intros; right; intros (?&?&?&?&?) in
                   (case es'; first by no); case; try by no.
               move => ts hs l0 l1. left. by eexists (ts, hs, l0, l1).
            ++ convert_pickable Pparse.
        -- case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse'' es)) es').
           ++ move => [[vs es''] [E1 [C Ex]]].
              destruct es'' as [| [| | | | | | | | |ts hs LI | | | |] es2];
          try solve [ exfalso; move: Ex => [? [? [? [? E']]]]; inversion E' ].
        clear Ex. rewrite E1.
        destruct m.
        { exfalso. subst es'.
          specialize (lfilled_pickable_rec_gen_measure_concat_r vs (AI_prompt ts hs LI :: es2)) as H.
          specialize (lfilled_pickable_rec_gen_measure_prompt_r ts hs LI es2) as H'.
          lias. 
        } 
        have I_LI: (lfilled_pickable_rec_gen_measure LI <= m').
        {
          assert (lfilled_pickable_rec_gen_measure LI < S m); last lias.
          rewrite -E E1. eapply leq_trans.
          - by eapply lfilled_pickable_rec_gen_measure_prompt_r.
          - by apply: lfilled_pickable_rec_gen_measure_concat_r.
        }
        set fes' := fun k lh => fes k (LH_prompt vs ts hs lh es2).
        have D1: forall es' lh lh' n0, decidable (lfilledInd 0 lh (fes' n0 lh') es').
        { move=> ? ? ? ?. by apply: D0. }
        specialize (IHm' (lfilled_pickable_rec_gen_measure LI) I_LI fes' D1 LI (erefl _) k) as [[[n' lh] LF]|NP].
              ** eapply LfilledPrompt with (bef := vs) in LF => //.
                 left. exists (n', LH_prompt vs ts hs lh es2). 
                 move: LF. rewrite /fes'. intros H. exact H. 
              ** right. move=> [n' [lh FI]]. apply: NP. inversion FI; subst.
                 --- exfalso. apply: nE. exists vs0. exists es'0. repeat split => //.
                     +++ rewrite -H. by rewrite_by (k + 0 = k).
                     +++ by rewrite_by (k = k + 0).
                 --- apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
                 --- apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
                 --- apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
                     eexists. eexists. rewrite /fes'. exact H4.
              
           ++ intros nE'''.
              right. move=> [n [lh I]]. inversion I; subst.
              ** apply: nE. do 2 eexists. rewrite_by (k + 0 = k). repeat split; try eassumption.
                 by apply: LfilledBase.
              ** apply: nE'. by repeat eexists.
              ** apply: nE''. by repeat eexists.
              ** apply: nE'''. by repeat eexists.
Defined.

Definition lfilled_pickable_rec_gen : forall fes,
  (forall es' lh lh' n0, decidable (lfilled 0 lh (fes n0 lh') es')) ->
  forall es', pickable2 (fun n lh => lfilled n lh (fes n lh) es').
Proof.
  move=> fes D0 es'.
  apply: (@pickable2_equiv _ _ (fun n lh => lfilledInd n lh (fes (0+n) lh) es')).
  { move=> n lh. by split; apply lfilled_Ind_Equivalent. }
  apply: lfilledInd_pickable_rec_gen => es'' lh lh' n0.
  by apply: decidable_equiv; first by apply: lfilled_Ind_Equivalent.
Defined.


(** We can always decide [lfilled 0]. **)
Lemma lfilled_decidable_base : forall es es' lh,
  decidable (lfilled 0 lh es es').
Proof.
  move=> es es' lh. apply: (@decidable_equiv (lfilledInd 0 lh es es')).
  { by split; apply lfilled_Ind_Equivalent. }
(*  assert (pickable (fun LI => lfilledInd 0 lh es LI)).
  2:{ destruct X.
      - destruct s as [LI HLI].
        assert (decidable (es' = LI)).
        { decidable_equality. }
        destruct H; first by subst; left.
        right. intros Habs. 
        apply n.
        eapply lfilled_deterministic. exact Habs. exact HLI.
      - right. intros Habs. apply n. exists es'. done. } 
  clear es'. *)
  generalize dependent es'; induction lh; intros es'.
  - have: pickable2 (fun vs es'' => es' = vs ++ es ++ es'' /\ const_list vs /\ vs = l /\ es'' = l0).
    {
      apply: list_search_split_pickable2.
      - by apply: administrative_instruction_eq_dec.
      - move=> ? ?. by repeat apply: decidable_and; apply: eq_comparable.
    }
    case.
    + move=> [[vs es''] [E [C [E1 E2]]]]. left. subst. by constructor.
    + move=> nE. right. move=> I. apply: nE. inversion I. subst. by repeat eexists.
  - right. move=> I. by inversion I. 
  - have: pickable3 (fun vs esh aft => es' = vs ++ esh ++ aft /\ const_list vs /\ vs = l /\ aft = l1 /\ match esh with [:: AI_handler hs _] => hs = l0 | _ => False end).
    {
      apply: list_split_pickable3.
      intros bef esh aft.
      repeat apply: decidable_and ; try by apply: eq_comparable.
      destruct esh; first by right.
      destruct a; try by right.
      destruct esh; last by right.
      decidable_equality.
    }
    case.
    + intros [[[bef esh] aft] (E & C & E1 & E2 & E3)].
      destruct esh => //. destruct a => //. destruct esh => //.
      subst.
      destruct (IHlh l3).
      * left. by constructor.
      * right. intros Habs. inversion Habs; subst.
        apply app_app in H6 => //. inversion H6; subst. by apply n.
    + intros nE. right. intros Habs. apply nE. inversion Habs; subst. by repeat eexists.
  - have: pickable3 (fun vs esh aft => es' = vs ++ esh ++ aft /\ const_list vs /\ vs = l /\ aft = l2 /\ match esh with [:: AI_prompt ts hs _] => ts = l0 /\ hs = l1 | _ => False end).
    {
      apply: list_split_pickable3.
      intros bef esh aft.
      repeat apply: decidable_and ; try by apply: eq_comparable.
      destruct esh; first by right.
      destruct a; try by right.
      destruct esh; last by right.
      apply decidable_and;
      decidable_equality.
    }
    case.
    + intros [[[bef esh] aft] (E & C & E1 & E2 & E3)].
      destruct esh => //. destruct a => //. destruct esh => //.
      destruct E3 as [-> ->]. subst.
      destruct (IHlh l5).
      * left. by constructor.
      * right. intros Habs. inversion Habs; subst.
        apply app_app in H7 => //. inversion H7; subst. by apply n.
    + intros nE. right. intros Habs. apply nE. inversion Habs; subst. by repeat eexists. 

Defined.

(** We can furthermore rebuild the stack [lh] for any [lfilled 0] predicate. **)
Lemma lfilled_pickable_base : forall es es',
  pickable (fun lh => lfilled 0 lh es es').
Proof.
  move=> es es'. apply: (@pickable_equiv _ (fun lh => lfilledInd 0 lh es es')).
  { move=> lh. by split; apply lfilled_Ind_Equivalent. }

  remember (lfilled_pickable_rec_gen_measure es') as m.
  assert (lfilled_pickable_rec_gen_measure es' <= m); first lias.
  clear Heqm.
  generalize dependent es'; induction m; intros es' Hm.
  {  have: pickable2 (fun vs es'' => es' = vs ++ es ++ es'' /\ const_list vs /\ True).
     {
       apply: list_search_split_pickable2.
       - by apply: administrative_instruction_eq_dec.
       - move=> ? ?. apply: decidable_and.
         + by apply: is_true_decidable.
         + by left.
     }
     case.
     - move=> [[vs es''] [E [C _]]]. left. eexists. subst. by constructor.
     - move=> nE. right.  intros [lh Habs].
       inversion Habs; subst => //.
       + apply nE. repeat eexists => //.
       + specialize (lfilled_pickable_rec_gen_measure_concat_r bef (AI_handler hs LI :: aft)) as ?.
         specialize (lfilled_pickable_rec_gen_measure_handler_r hs LI aft) as ?.
         simpl in Hm. lias.
       + specialize (lfilled_pickable_rec_gen_measure_concat_r bef (AI_prompt ts hs LI :: aft)) as ?.
         specialize (lfilled_pickable_rec_gen_measure_prompt_r ts hs LI aft) as ?.
         simpl in Hm. lias.
  } 

  
  have: pickable2 (fun vs es'' => es' = vs ++ es ++ es'' /\ const_list vs /\ True).
  {
    apply: list_search_split_pickable2.
    - by apply: administrative_instruction_eq_dec.
    - move=> ? ?. apply: decidable_and.
      + by apply: is_true_decidable.
      + by left.
  }
  case.
  - move=> [[vs es''] [E [C _]]]. left. eexists. subst. by constructor.
  - move=> nE.
    have: pickable3 (fun bef esh aft => es' = bef ++ esh ++ aft /\ const_list bef /\
                                       match esh with
                                       | [:: AI_handler _ _] => True
                                       | _ => False
                                       end).
    {
      apply: list_split_pickable3.
      intros bef esh aft.
      repeat apply: decidable_and ; try by apply: eq_comparable.
      destruct esh; first by right.
      destruct a; try by right.
      destruct esh; last by right.
      by left.
    }
    case.
    + intros [[[bef esh] aft] (-> & Hbef & Hesh)].
      destruct esh => //. destruct a => //. destruct esh => //.
      destruct (IHm l0).
      * specialize (lfilled_pickable_rec_gen_measure_concat_r bef (AI_handler l l0 :: aft)) as H.
        specialize (lfilled_pickable_rec_gen_measure_handler_r l l0 aft) as H'.
        simpl in Hm. lias. 
      * destruct s as [lh Hl0].
        left. exists (LH_handler bef l lh aft).
        constructor => //.
      * right. intros [lh Habs]. inversion Habs.
        -- apply nE. repeat eexists => //=. rewrite - H. done. done.
        -- apply first_values in H as (-> & H & ->) => //.
           inversion H; subst. apply n. exists lh'. done.
        -- apply first_values in H as (-> & H & ->) => //.

           
    + intros nE'.
      have: pickable3 (fun bef esh aft => es' = bef ++ esh ++ aft /\ const_list bef /\
                                       match esh with
                                       | [:: AI_prompt _ _ _] => True
                                       | _ => False
                                       end).
    {
      apply: list_split_pickable3.
      intros bef esh aft.
      repeat apply: decidable_and ; try by apply: eq_comparable.
      destruct esh; first by right.
      destruct a; try by right.
      destruct esh; last by right.
      by left.
    }
    case.
    * intros [[[bef esh] aft] (-> & Hbef & Hesh)].
      destruct esh => //. destruct a => //. destruct esh => //.
      destruct (IHm l1).
      -- specialize (lfilled_pickable_rec_gen_measure_concat_r bef (AI_prompt l l0 l1:: aft)) as H.
        specialize (lfilled_pickable_rec_gen_measure_prompt_r l l0 l1 aft) as H'.
        simpl in Hm. lias. 
      -- destruct s as [lh Hl0].
        left. exists (LH_prompt bef l l0 lh aft).
        constructor => //.
      -- right. intros [lh Habs]. inversion Habs.
         ++ apply nE. repeat eexists => //=. rewrite - H. done. done.
         ++ apply first_values in H as (-> & H & ->) => //.
         ++ apply first_values in H as (-> & H & ->) => //.
           inversion H; subst. apply n. exists lh'. done.

           
    * intros nE''. right. intros [lh Habs].
      inversion Habs.
      -- apply nE. repeat eexists => //=. rewrite - H3. done. done.
      -- apply nE'. repeat eexists => //=. rewrite - H4. done. done. done.
      -- apply nE''. repeat eexists => //=. rewrite - H4. done. done. done.
Defined.

Definition lfilled_pickable_rec : forall es,
  (forall es' lh, decidable (lfilled 0 lh es es')) ->
  forall es', pickable2 (fun n lh => lfilled n lh es es').
Proof.
  move=> es D. by apply: lfilled_pickable_rec_gen.
Defined.

(*
(** Same with hfilled *)

Fixpoint hfilled_pickable_rec_gen_measure_single (e : administrative_instruction) :=
  match e with
  | AI_handler _ es1
  | AI_prompt _ _ es1
  | AI_local _ _ es1 
  | AI_label _ _ es1 =>
      1 + List.fold_left (fun a b => max a (hfilled_pickable_rec_gen_measure_single b)) es1 0
  | _ => 0
  end.
     
                

Definition hfilled_pickable_rec_gen_measure (LI : seq administrative_instruction) :=
  List.fold_left (fun a b => max a (hfilled_pickable_rec_gen_measure_single b)) LI 0.



Lemma hfilled_pickable_rec_gen_measure_cons : forall I LI,
  hfilled_pickable_rec_gen_measure LI <= hfilled_pickable_rec_gen_measure (I :: LI).
Proof.
  move=> I LI. unfold hfilled_pickable_rec_gen_measure.
  rewrite fold_left_max_app_cons. lias.
Qed.

Lemma hfilled_pickable_rec_gen_measure_concat_l : forall LI1 LI2,
  hfilled_pickable_rec_gen_measure LI1 <= hfilled_pickable_rec_gen_measure (LI1 ++ LI2).
Proof.
  move => LI1 LI2. induction LI1 => /=.
  - rewrite {1} /hfilled_pickable_rec_gen_measure /=. by lias.
  - rewrite /hfilled_pickable_rec_gen_measure /=.
    do 2 rewrite (fold_left_max_rem (_ a)).
    unfold hfilled_pickable_rec_gen_measure in IHLI1. lias.
Qed.

Lemma hfilled_pickable_rec_gen_measure_concat_r : forall LI1 LI2,
  hfilled_pickable_rec_gen_measure LI2 <= hfilled_pickable_rec_gen_measure (LI1 ++ LI2).
Proof.
  move => LI1 LI2. induction LI1 => /=.
  - rewrite {1} /hfilled_pickable_rec_gen_measure /=. by lias.
  - rewrite /hfilled_pickable_rec_gen_measure /=.
    rewrite (fold_left_max_rem (_ a)).
    unfold hfilled_pickable_rec_gen_measure in IHLI1. lias.
Qed.

Lemma hfilled_pickable_rec_gen_measure_label_r : forall n es LI LI',
  hfilled_pickable_rec_gen_measure LI < hfilled_pickable_rec_gen_measure (AI_label n es LI :: LI').
Proof.
  move=> n es LI LI'. rewrite /hfilled_pickable_rec_gen_measure /=.
  rewrite (fold_left_max_rem (S _)). lias. 
Qed.

Lemma hfilled_pickable_rec_gen_measure_handler_r : forall hs LI LI',
  hfilled_pickable_rec_gen_measure LI < hfilled_pickable_rec_gen_measure (AI_handler hs LI :: LI').
Proof.
  move=> hs LI LI'. rewrite /hfilled_pickable_rec_gen_measure /=.
  rewrite (fold_left_max_rem (S _)). lias. 
Qed.
Lemma hfilled_pickable_rec_gen_measure_prompt_r : forall ts hs LI LI',
  hfilled_pickable_rec_gen_measure LI < hfilled_pickable_rec_gen_measure (AI_prompt ts hs LI :: LI').
Proof.
  move=> ts hs LI LI'. rewrite /hfilled_pickable_rec_gen_measure /=.
  rewrite (fold_left_max_rem (S _)). lias. 
Qed.
Lemma hfilled_pickable_rec_gen_measure_local_r : forall ts hs LI LI',
  hfilled_pickable_rec_gen_measure LI < hfilled_pickable_rec_gen_measure (AI_local ts hs LI :: LI').
Proof.
  move=> ts hs LI LI'. rewrite /hfilled_pickable_rec_gen_measure /=.
  rewrite (fold_left_max_rem (S _)). lias. 
Qed.

(** A helper definition for [hfilled_decidable_rec]. **)
Definition hfilledInd_pickable_rec_gen : forall fes x,
  (forall es' bef aft lh', decidable (hfilledInd x (HH_base bef aft) (fes lh') es')) ->
  forall es', pickable (fun lh => hfilledInd x lh (fes lh) es').
Proof.
  move=> fes x D0 es'.
  move: No_var => k. 
  have [m E]: { m | hfilled_pickable_rec_gen_measure es' = m }; first by eexists.
  move: fes D0 es' E k.
  assert (forall m' m, m <= m' ->
                  forall fes : hholed -> seq administrative_instruction,
                    (forall (es' : seq administrative_instruction) bef aft (lh' : hholed),
                        decidable (hfilledInd x (HH_base bef aft) (fes lh') es')) ->
                    forall es' : seq administrative_instruction,
                      hfilled_pickable_rec_gen_measure es' = m ->
                      forall k : avoiding,
                        pickable (fun (lh : hholed) => hfilledInd x lh (fes lh) es')) as H.
  2:{ apply (H (S m) m). lias. }
  clear m. induction m'.

  { move=> m Hm fes D0 es' E k.
    destruct m; last lias.
    have Dcl: forall vs, decidable (const_list vs).
    { move=> vs. by apply: is_true_decidable. }
    (** First, we check whether we can use HH_base. **)
    have P0: pickable2 (fun vs es'' =>
                       let lh := HH_base vs es'' in
                       let es := fes lh in
                       es' = vs ++ es ++ es'' /\ const_list vs /\ hfilledInd x lh es es').
    - have: pickable3 (fun vs es es'' => 
                         es' = vs ++ es ++ es'' /\ let lh := HH_base vs es'' in
                                                  es = fes lh /\ const_list vs /\ hfilledInd x lh es es').
      + apply: list_split_pickable3_gen. move=> vs es es'' Ees /=.
        case E': (es == fes (HH_base vs es'')); move/eqP: E' => E'.
        * rewrite E'. 
          repeat apply: decidable_and => //.
          by apply: eq_comparable.
        * right. by move=> [Ees2 [Cl I]].
      + case.
        * move=> [[[vs es] es''] [E1 [E2 [Cl I]]]].
          left. exists (vs, es''). by subst.
        * move=> Ex. right. move=> [vs [es'' [E' [Cl I]]]].
          apply: Ex.
          by repeat eexists; eassumption.
    - case P0.
      + move=> [[vs es''] [E' [Cvs I]]]. left.
        exists (HH_base vs es'').
        subst. by apply: HfilledBase.
      + move=> nE.
        (** Otherwise, we have to apply [HfilledRec]. **)
        have Dparse: forall es' : seq administrative_instruction,
        decidable (exists n es1 LI es2, es' = [:: AI_label n es1 LI] ++ es2).
        * clear. move=> es'.
          have Pparse: pickable4 (fun n es1 LI es2 => es' = [:: AI_label n es1 LI] ++ es2).
          -- let no := by intros; right; intros (?&?&?&?&?) in
             (case es'; first by no); case; try by no.
             move=> n l1 l2 l3. left. by eexists (n, l1, l2, l3).
          -- convert_pickable Pparse.
        * case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse es)) es').
          -- move=> [[vs es''] [E1 [C Ex]]].
             destruct es'' as [| [| | | | | | | | n es1 LI | |] es2];
               try solve [ exfalso; move: Ex => [? [? [? [? E']]]]; inversion E' ].
             clear Ex. rewrite E1.
             exfalso. subst es'.
             specialize (hfilled_pickable_rec_gen_measure_concat_r vs (AI_label n es1 LI :: es2)) as H.
             specialize (hfilled_pickable_rec_gen_measure_label_r n es1 LI es2) as H'.
             lias. 
          -- move=> nE'.
             (** If we get here, we have to apply [HfilledHandler]. **)
             have Dparse': forall es': seq administrative_instruction,
                 decidable (exists hs LI es2, es' = [:: AI_handler hs LI] ++ es2).
             ++ clear. move => es'.
                have Pparse: pickable3 (fun hs LI es2 => es' = [:: AI_handler hs LI] ++ es2).
                ** let no := by intros; right; intros (?&?&?&?) in
                   (case es'; first by no); case; try by no.
                   move => hs l0 l1. left. by eexists (hs, l0, l1).
                ** convert_pickable Pparse.
             ++ case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse' es)) es').
                ** move => [[vs es''] [E1 [C Ex]]].
                   destruct es'' as [| [| | | | |  hs LI| | | | |] es2];
                     try solve [ exfalso; move: Ex => [? [? [? E']]]; inversion E' ].
                   clear Ex. rewrite E1.
                   exfalso. subst es'.
                   specialize (hfilled_pickable_rec_gen_measure_concat_r vs (AI_handler hs LI :: es2)) as H.
                   specialize (hfilled_pickable_rec_gen_measure_handler_r hs LI es2) as H'.
                   lias.
                ** move => nE''.
                     (** If we get here, we have to apply [HfilledPrompt]. **)
             have Dparse'': forall es': seq administrative_instruction,
                 decidable (exists ts hs LI es2, es' = [:: AI_prompt ts hs LI] ++ es2).
                   --- clear. move => es'.
                       have Pparse: pickable4 (fun ts hs LI es2 => es' = [:: AI_prompt ts hs LI] ++ es2).
                       +++ let no := by intros; right; intros (?&?&?&?&?) in
                           (case es'; first by no); case; try by no.
                           move => ts hs l0 l1. left. by eexists (ts, hs, l0, l1).
                       +++ convert_pickable Pparse.
                   --- case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse'' es)) es').
                       +++ move => [[vs es''] [E1 [C Ex]]].
                           destruct es'' as [| [| | | | | | ts hs LI | | | |] es2];
                             try solve [ exfalso; move: Ex => [? [? [? [? E']]]]; inversion E' ].
                           clear Ex. rewrite E1.
                           exfalso. subst es'.
                           specialize (hfilled_pickable_rec_gen_measure_concat_r vs (AI_prompt ts hs LI :: es2)) as H.
                           specialize (hfilled_pickable_rec_gen_measure_prompt_r ts hs LI es2) as H'.
                           lias.
                       +++ move => nE'''.
                           (** If we get here then local *)
                            have Dparse''': forall es': seq administrative_instruction,
                 decidable (exists ts hs LI es2, es' = [:: AI_local ts hs LI] ++ es2).
                           *** clear. move => es'.
                               have Pparse: pickable4 (fun ts hs LI es2 => es' = [:: AI_local ts hs LI] ++ es2).
                               ---- let no := by intros; right; intros (?&?&?&?&?) in
                           (case es'; first by no); case; try by no.
                           move => ts hs l0 l1. left. by eexists (ts, hs, l0, l1).
                               ---- convert_pickable Pparse.
                           *** case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse''' es)) es').
                               ---- move => [[vs es''] [E1 [C Ex]]].
                                    destruct es'' as [| [| | | | | | | | | ts hs LI | ] es2];
                             try solve [ exfalso; move: Ex => [? [? [? [? E']]]]; inversion E' ].
                           clear Ex. rewrite E1.
                           exfalso. subst es'.
                           specialize (hfilled_pickable_rec_gen_measure_concat_r vs (AI_local ts hs LI :: es2)) as H.
                           specialize (hfilled_pickable_rec_gen_measure_local_r ts hs LI es2) as H'.
                           lias.
                               ---- move => nE''''.
                           right. move=> [lh I]. inversion I; subst.
                                    ++++ apply: nE. do 2 eexists.
                                         repeat split; try eassumption.
                                    ++++ apply: nE'. by repeat eexists.
                                    ++++ apply: nE''''. by repeat eexists.
                                    ++++ apply: nE'''. by repeat eexists.
                                    ++++ apply: nE''. by repeat eexists.
  } 

   move=> m Hm fes D0 es' E k.
  have Dcl: forall vs, decidable (const_list vs).
  { move=> vs. by apply: is_true_decidable. }
  (** First, we check whether we can set [n = 0]. **)
  have P0: pickable2 (fun vs es'' =>
                       let lh := HH_base vs es'' in
                       let es := fes lh in
                       es' = vs ++ es ++ es'' /\ const_list vs /\ hfilledInd x lh es es').
  {
    have: pickable3 (fun vs es es'' =>
      es' = vs ++ es ++ es'' /\ let lh := HH_base vs es'' in
      es = fes lh /\ const_list vs /\ hfilledInd x lh es es').
    {
      apply: list_split_pickable3_gen. move=> vs es es'' Ees /=.
      case E': (es == fes (HH_base vs es'')); move/eqP: E' => E'.
      - rewrite E'. repeat apply: decidable_and => //. by apply: eq_comparable.
      - right. by move=> [Ees2 [Cl I]].
    }
    case.
    - move=> [[[vs es] es''] [E1 [E2 [Cl I]]]]. left. exists (vs, es''). by subst.
    - move=> Ex. right. move=> [vs [es'' [E' [Cl I]]]]. apply: Ex.
      by repeat eexists; eassumption.
  }
  case P0.
  {
    move=> [[vs es''] [E' [Cvs I]]]. left. exists (HH_base vs es'').
    subst. by apply: HfilledBase.
  }
  move=> nE.
  (** Otherwise, we have to apply [LfilledRec]. **)
  have Dparse: forall es' : seq administrative_instruction,
    decidable (exists n es1 LI es2, es' = [:: AI_label n es1 LI] ++ es2).
  {
    clear. move=> es'.
    have Pparse: pickable4 (fun n es1 LI es2 => es' = [:: AI_label n es1 LI] ++ es2).
    {
      let no := by intros; right; intros (?&?&?&?&?) in
      (case es'; first by no); case; try by no.
      move=> n l1 l2 l3. left. by exists (n, l1, l2, l3).
    }
    convert_pickable Pparse.
  }
  case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse es)) es').
  - move=> [[vs es''] [E1 [C Ex]]].
    destruct es'' as [| [| | | | | | | | n es1 LI | |] es2];
      try solve [ exfalso; move: Ex => [? [? [? [? E']]]]; inversion E' ].
    clear Ex. rewrite E1.
    destruct m.
    { exfalso. subst es'.
      specialize (hfilled_pickable_rec_gen_measure_concat_r vs (AI_label n es1 LI :: es2)) as H.
      specialize (hfilled_pickable_rec_gen_measure_label_r n es1 LI es2) as H'.
      lias. 
    } 
    have I_LI: (hfilled_pickable_rec_gen_measure LI <= m').
    {
      assert (hfilled_pickable_rec_gen_measure LI < S m); last lias.
      rewrite -E E1. eapply leq_trans.
      - by eapply hfilled_pickable_rec_gen_measure_label_r.
      - by apply: hfilled_pickable_rec_gen_measure_concat_r.
    }
    set fes' := fun lh => fes (HH_label vs n es1 lh es2).
    have D1: forall es' bef aft lh', decidable (hfilledInd x (HH_base bef aft) (fes' lh') es').
    { move=> ? ? ? ?. by apply: D0. }
    specialize (IHm' (hfilled_pickable_rec_gen_measure LI) I_LI fes' D1 LI (erefl _) k) as [[ lh LF]|NP].
    + eapply HfilledLabel with (vs := vs) in LF => //.
      left. exists (HH_label vs n es1 lh es2). exact LF.
(*      move: LF. rewrite /fes'. rewrite_by (k + n' + 1 = k + n'.+1) => /= LF. by apply: LF. *)
    + right. move=> [lh FI]. apply: NP. inversion FI; subst.
      * exfalso. apply: nE. exists vs0. exists es'0. repeat split => //.
        (* rewrite -H. by apply HfilledBase. *)
      * apply const_list_concat_inv in H => //.
        move: H => [? [E' ?]]. inversion E'; subst.
        eexists. rewrite /fes'.
        by apply: H4.
      * apply const_list_concat_inv in H => //.
        move: H => [? [E' ?]]. inversion E'; subst.
      * apply const_list_concat_inv in H => //.
        move: H => [? [E' ?]]. inversion E'; subst.
      * apply const_list_concat_inv in H => //.
        move: H => [? [E' ?]]. inversion E'; subst.

        
  - move=> nE'.
    (** If we get here, we have to apply [LfilledHandler]. **)
    have Dparse': forall es': seq administrative_instruction,
        decidable (exists hs LI es2, es' = [:: AI_handler hs LI] ++ es2).
    + clear. move => es'.
      have Pparse: pickable3 (fun hs LI es2 => es' = [:: AI_handler hs LI] ++ es2).
      * let no := by intros; right; intros (?&?&?&?) in
                   (case es'; first by no); case; try by no.
        move => hs l0 l1. left. by eexists (hs, l0, l1).
      * convert_pickable Pparse.
    + case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse' es)) es').
      * move => [[vs es''] [E1 [C Ex]]].
        destruct es'' as [| [| | | | | hs LI| | | | |] es2];
          try solve [ exfalso; move: Ex => [? [? [? E']]]; inversion E' ].
        clear Ex. rewrite E1.
        destruct m.
        { exfalso. subst es'.
          specialize (hfilled_pickable_rec_gen_measure_concat_r vs (AI_handler hs LI :: es2)) as H.
          specialize (hfilled_pickable_rec_gen_measure_handler_r hs LI es2) as H'.
          lias. 
        } 
        have I_LI: (hfilled_pickable_rec_gen_measure LI <= m').
        {
          assert (hfilled_pickable_rec_gen_measure LI < S m); last lias.
          rewrite -E E1. eapply leq_trans.
          - by eapply hfilled_pickable_rec_gen_measure_handler_r.
          - by apply: hfilled_pickable_rec_gen_measure_concat_r.
        }
        set fes' := fun lh => fes (HH_handler vs hs lh es2).
        have D1: forall es' bef aft lh', decidable (hfilledInd x (HH_base bef aft) (fes' lh') es').
        { move=>  ? ? ? ?. by apply: D0. }
        specialize (IHm' (hfilled_pickable_rec_gen_measure LI) I_LI fes' D1 LI (erefl _) k) as [[ lh LF]|NP].
        -- assert (decidable
                     (match x with
                      | Var_handler x0 inst => firstx_exception hs inst x0 = No_label
                      | _ => True
                      end)).
           { destruct x; try by left.
             decidable_equality. }
           destruct H. 
           ++ eapply HfilledHandler with (bef := vs) in LF => //.
              left. exists (HH_handler vs hs lh es2).
              move: LF. rewrite /fes'. intros H. exact H.
              exact y.
           ++ right. intros [hh Habs].
              apply n. inversion Habs; subst.
              ** exfalso. apply: nE. exists vs0. exists es'0.
                 repeat split => //.
              ** apply const_list_concat_inv in H => //.
                 move: H => [? [E' ?]]. inversion E'; subst.
              ** apply const_list_concat_inv in H => //.
                 move: H => [? [E' ?]]. inversion E'; subst.
              ** apply const_list_concat_inv in H => //.
                 move: H => [? [E' ?]]. inversion E'; subst.
              ** apply const_list_concat_inv in H => //.
                 move: H => [? [E' ?]]. inversion E'; subst.
                 exact H1.
        -- right. move=> [lh FI]. apply: NP. inversion FI; subst.
           ++ exfalso. apply: nE. exists vs0. exists es'0. repeat split => //.
           ++ apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
           ++ apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
           ++ apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
           ++ apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
              eexists. rewrite /fes'. exact H5.


      * move=> nE''.
    (** If we get here, we have to apply [LfilledPrompt]. **)
    have Dparse'': forall es': seq administrative_instruction,
        decidable (exists ts hs LI es2, es' = [:: AI_prompt ts hs LI] ++ es2).
        --  clear. move => es'.
            have Pparse: pickable4 (fun ts hs LI es2 => es' = [:: AI_prompt ts hs LI] ++ es2).
            ++ let no := by intros; right; intros (?&?&?&?&?) in
                   (case es'; first by no); case; try by no.
               move => ts hs l0 l1. left. by eexists (ts, hs, l0, l1).
            ++ convert_pickable Pparse.
        -- case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse'' es)) es').
           ++ move => [[vs es''] [E1 [C Ex]]].
              destruct es'' as [| [| | | | | |ts hs LI | | | |] es2];
          try solve [ exfalso; move: Ex => [? [? [? [? E']]]]; inversion E' ].
        clear Ex. rewrite E1.
        destruct m.
        { exfalso. subst es'.
          specialize (hfilled_pickable_rec_gen_measure_concat_r vs (AI_prompt ts hs LI :: es2)) as H.
          specialize (hfilled_pickable_rec_gen_measure_prompt_r ts hs LI es2) as H'.
          lias. 
        } 
        have I_LI: (hfilled_pickable_rec_gen_measure LI <= m').
        {
          assert (hfilled_pickable_rec_gen_measure LI < S m); last lias.
          rewrite -E E1. eapply leq_trans.
          - by eapply hfilled_pickable_rec_gen_measure_prompt_r.
          - by apply: hfilled_pickable_rec_gen_measure_concat_r.
        }
        set fes' := fun lh => fes (HH_prompt vs ts hs lh es2).
        have D1: forall es' bef aft lh' , decidable (hfilledInd x (HH_base bef aft) (fes' lh') es').
        { move=> ? ? ? ?. by apply: D0. }
        specialize (IHm' (hfilled_pickable_rec_gen_measure LI) I_LI fes' D1 LI (erefl _) k) as [[ lh LF]|NP].
              **  assert (decidable
                     (match x with
                      | Var_prompt x0 inst => firstx_continuation hs inst x0 = None
                      | _ => True
                      end)).
           { destruct x; try by left.
             decidable_equality. }
           destruct H. 
                  --- eapply HfilledPrompt with (bef := vs) in LF => //.
                      left. exists (HH_prompt vs ts hs lh es2). 
                      move: LF. rewrite /fes'. intros H. exact H.
                      exact y.
                  --- right. intros [hh Habs].
                      apply n. inversion Habs; subst.
                      +++ exfalso. apply :nE. exists vs0. exists es'0. repeat split => //.
                      +++ apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
                      +++ apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
                      +++ apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
                          exact H1.
                      +++ apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
                          
              ** right. move=> [lh FI]. apply: NP. inversion FI; subst.
                 --- exfalso. apply: nE. exists vs0. exists es'0. repeat split => //.
                 --- apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
                 --- apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
                 --- apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
                     eexists. rewrite /fes'. exact H5.
                 --- apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
           ++ intros nE'''.
              (** If we get here, we have to apply [HfilledLocal]. **)
             have Dparse''': forall es': seq administrative_instruction,
                 decidable (exists ts hs LI es2, es' = [:: AI_local ts hs LI] ++ es2).
             **  clear. move => es'.
                 have Pparse: pickable4 (fun ts hs LI es2 => es' = [:: AI_local ts hs LI] ++ es2).
                 --- let no := by intros; right; intros (?&?&?&?&?) in
                   (case es'; first by no); case; try by no.
                     move => ts hs l0 l1. left. by eexists (ts, hs, l0, l1).
                 --- convert_pickable Pparse.
             ** case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse''' es)) es').
                --- move => [[vs es''] [E1 [C Ex]]].
              destruct es'' as [| [| | | | | | | | | ts hs LI |] es2];
          try solve [ exfalso; move: Ex => [? [? [? [? E']]]]; inversion E' ].
        clear Ex. rewrite E1.
        destruct m.
        { exfalso. subst es'.
          specialize (hfilled_pickable_rec_gen_measure_concat_r vs (AI_local ts hs LI :: es2)) as H.
          specialize (hfilled_pickable_rec_gen_measure_local_r ts hs LI es2) as H'.
          lias. 
        } 
        have I_LI: (hfilled_pickable_rec_gen_measure LI <= m').
        {
          assert (hfilled_pickable_rec_gen_measure LI < S m); last lias.
          rewrite -E E1. eapply leq_trans.
          - by eapply hfilled_pickable_rec_gen_measure_local_r.
          - by apply: hfilled_pickable_rec_gen_measure_concat_r.
        }
        set fes' := fun lh => fes (HH_local vs ts hs lh es2).
        have D1: forall es' bef aft lh' , decidable (hfilledInd x (HH_base bef aft) (fes' lh') es').
        { move=> ? ? ? ?. by apply: D0. }
        specialize (IHm' (hfilled_pickable_rec_gen_measure LI) I_LI fes' D1 LI (erefl _) k) as [[ lh LF]|NP].
                    +++ eapply HfilledLocal in LF => //.
                        left. exists (HH_local vs ts hs lh es2). 
                        move: LF. rewrite /fes'. intros H. exact H.
                        done. 
                    +++ right. move=> [lh FI]. apply: NP. inversion FI; subst.
                        *** exfalso. apply: nE. exists vs0. exists es'0. repeat split => //.
                        *** apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
                        *** apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
                            eexists. rewrite /fes'. exact H4.
                        *** apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
                        *** apply const_list_concat_inv in H => //. move: H => [? [E' ?]]. inversion E'; subst.
                --- intros nE''''.
              right. move=> [lh I]. inversion I; subst.
                    +++ apply: nE. do 2 eexists. repeat split; try eassumption.
                    +++ apply: nE'. by repeat eexists.
                    +++ apply: nE''''. by repeat eexists.
           +++ apply: nE'''. by repeat eexists.
              +++ apply: nE''. by repeat eexists.
Defined.

Definition hfilled_pickable_rec_gen : forall fes x,
  (forall es' bef aft lh', decidable (hfilled x (HH_base bef aft) (fes lh') es')) ->
  forall es', pickable (fun lh => hfilled x lh (fes lh) es').
Proof.
  move=> fes x D0 es'.
  apply: (@pickable_equiv _ (fun lh => hfilledInd x lh (fes lh) es')).
  { move=> lh. by split; apply hfilled_Ind_Equivalent. }
  apply: hfilledInd_pickable_rec_gen => es'' bef aft lh'.
  by apply: decidable_equiv; first by apply: hfilled_Ind_Equivalent.
Defined.



(** We can always decide [hfilled hhbase]. **)
Lemma hfilled_decidable_base : forall es es' bef aft x,
  decidable (hfilled x (HH_base bef aft) es es').
Proof.
  move=> es es' bef aft x.
  apply: (@decidable_equiv (hfilledInd x (HH_base bef aft) es es')).
  { by split; apply hfilled_Ind_Equivalent. }
 have: pickable2 (fun vs es'' => es' = vs ++ es ++ es'' /\ const_list vs /\ vs = bef /\ es'' = aft).
    {
      apply: list_search_split_pickable2.
      - by apply: administrative_instruction_eq_dec.
      - move=> ? ?. by repeat apply: decidable_and; apply: eq_comparable.
    }
    case.
    + move=> [[vs es''] [E [C [E1 E2]]]]. left. subst. by constructor.
    + move=> nE. right. move=> I. apply: nE. inversion I. subst. by repeat eexists.
Defined. 

(** We can furthermore rebuild the stack [lh] for any [lfilled 0] predicate. **)
Lemma hfilled_pickable_base : forall es es' x,
  pickable2 (fun bef aft => hfilled x (HH_base bef aft) es es').
Proof.
  move=> es es' x. 
  apply: (@pickable2_equiv _ _ (fun bef aft => hfilledInd x (HH_base bef aft) es es')).
  { move=> lh. by split; apply hfilled_Ind_Equivalent. }
  have: pickable2 (fun vs es'' => es' = vs ++ es ++ es'' /\ const_list vs /\ True).
     {
       apply: list_search_split_pickable2.
       - by apply: administrative_instruction_eq_dec.
       - move=> ? ?. apply: decidable_and.
         + by apply: is_true_decidable.
         + by left.
     }
     case.
  - move=> [[vs es''] [E [C _]]]. left. eexists (_,_).
    subst. by constructor.
  - move=> nE. right.  intros (bef & aft & Habs).
    inversion Habs; subst => //.
    apply nE. repeat eexists => //.
Defined. 

Definition hfilled_pickable_rec : forall es x,
  (forall es' bef aft, decidable (hfilled x (HH_base bef aft) es es')) -> 
  forall es', pickable (fun lh => hfilled x lh es es').
Proof.
  move=> es x D. by apply: hfilled_pickable_rec_gen.
Defined.
*)

(** The lemmas [r_eliml] and [r_elimr] are the fundamental framing lemmas.
  They enable to focus on parts of the stack, ignoring the context. **)

Lemma r_eliml: forall s f es s' f' es' lconst,
    const_list lconst ->
    reduce s f es s' f' es' ->
    reduce s f (lconst ++ es) s' f' (lconst ++ es').
Proof.
  move => s f es s' f' es' lconst HConst H.
  apply: r_label; try apply/lfilledP.
  - by apply: H.
  - replace (lconst++es) with (lconst++es++[::]); first by apply: LfilledBase.
    f_equal. by apply: cats0.
  - replace (lconst++es') with (lconst++es'++[::]); first by apply: LfilledBase.
    f_equal. by apply: cats0.
Qed. 

Lemma r_elimr: forall s f es s' f' es' les,
    reduce s f es s' f' es' ->
    reduce s f (es ++ les) s' f' (es' ++ les).
Proof.
  move => s f es s' f' es' les H.
  apply: r_label; try apply/lfilledP.
  - apply: H.
  - replace (es++les) with ([::]++es++les) => //. by apply: LfilledBase.
  - replace (es'++les) with ([::]++es'++les) => //. by apply: LfilledBase.
Qed.

(** [r_eliml_empty] and [r_elimr_empty] are useful instantiations on empty stacks. **)

Lemma r_eliml_empty: forall s f es s' f' lconst,
    const_list lconst ->
    reduce s f es s' f' [::] ->
    reduce s f (lconst ++ es) s' f' lconst.
Proof.
  move => s f es s' f' lconst HConst H.
  assert (reduce s f (lconst++es) s' f' (lconst++[::])); first by apply: r_eliml.
  by rewrite cats0 in H0.
Qed.

Lemma r_elimr_empty: forall s f es s' f' les,
    reduce s f es s' f' [::] ->
    reduce s f (es ++ les) s' f' les.
Proof.
  move => s f es s' f' les H.
  assert (reduce s f (es++les) s' f' ([::] ++les)); first by apply: r_elimr.
  by rewrite cat0s in H0.
Qed.

(* A reformulation of [ety_a] that is easier to be used. *)
Lemma ety_a': forall s C es ts,
    es_is_basic es ->
    be_typing C (to_b_list es) ts ->
    e_typing s C es ts.
Proof.
  move => s C es ts HBasic HType.
  replace es with (to_e_list (to_b_list es)).
  - by apply ety_a.
  - symmetry. by apply e_b_elim.
Qed.

(*
Lemma ety_const: forall s C v,
    e_typing s C [::AI_const v] (Tf [::] [::typeof s v]).
Proof.
  destruct v => /=.
  - apply ety_a'; constructor => //. 
  - destruct v => //=.
    + apply ety_a'; constructor => //.
    + constructor.

 Lemma ety_const': forall v t s C,
    typeof C v = t -> e_typing s C [:: AI_const v] (Tf [::] [::t]).
Proof.
  intros v t s C <-. destruct v => //=.
  - apply ety_a' => //=. by repeat eexists.
    constructor.
  - destruct v => //=. apply ety_a' => //=. by repeat eexists.
    constructor. destruct (List.nth_error (tc_func_t C) f) eqn:Hf.
    eapply ety_ref.  *)

(* Some quality of life lemmas *)
Lemma bet_weakening_empty_1: forall C es ts t2s,
    be_typing C es (Tf [::] t2s) ->
    be_typing C es (Tf ts (ts ++ t2s)).
Proof.
  move => C es ts t2s HType.
  assert (be_typing C es (Tf (ts ++ [::]) (ts ++ t2s))); first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

Lemma et_weakening_empty_1: forall s C es ts t2s,
    e_typing s C es (Tf [::] t2s) ->
    e_typing s C es (Tf ts (ts ++ t2s)).
Proof.
  move => s C es ts t2s HType.
  assert (e_typing s C es (Tf (ts ++ [::]) (ts ++ t2s))); first by apply ety_weakening.
  by rewrite cats0 in H.
Qed.

Lemma bet_weakening_empty_2: forall C es ts t1s,
    be_typing C es (Tf t1s [::]) ->
    be_typing C es (Tf (ts ++ t1s) ts).
Proof.
  move => C es ts t1s HType.
  assert (be_typing C es (Tf (ts ++ t1s) (ts ++ [::]))); first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

Lemma et_weakening_empty_2: forall s C es ts t1s,
    e_typing s C es (Tf t1s [::]) ->
    e_typing s C es (Tf (ts ++ t1s) ts).
Proof.
  move => s C es ts t1s HType.
  assert (e_typing s C es (Tf (ts ++ t1s) (ts ++ [::]))); first by apply ety_weakening.
  by rewrite cats0 in H.
Qed.

Lemma bet_weakening_empty_both: forall C es ts,
    be_typing C es (Tf [::] [::]) ->
    be_typing C es (Tf ts ts).
Proof.
  move => C es ts HType.
  assert (be_typing C es (Tf (ts ++ [::]) (ts ++ [::]))); first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

Lemma et_weakening_empty_both: forall s C es ts,
    e_typing s C es (Tf [::] [::]) ->
    e_typing s C es (Tf ts ts).
Proof.
  move => s C es ts HType.
  assert (e_typing s C es (Tf (ts ++ [::]) (ts ++ [::]))); first by apply ety_weakening.
  by rewrite cats0 in H.
Qed.

Lemma empty_btyping: forall C t1s t2s,
    be_typing C [::] (Tf t1s t2s) ->
    t1s = t2s.
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //.
  - by destruct es.
  - f_equal. by eapply IHHType.
Qed.

Lemma empty_typing: forall s C t1s t2s,
    e_typing s C [::] (Tf t1s t2s) ->
    t1s = t2s.
Proof.
  move => s C t1s t2s HType.
  gen_ind_subst HType => //.
  - destruct bes => //. by apply empty_btyping in H.
  - by destruct es.
  - f_equal. by eapply IHHType.
Qed. 

(* A convenient lemma to invert e_typing back to be_typing. *)
Lemma et_to_bet: forall s C es ts,
    es_is_basic es ->
    e_typing s C es ts ->
    be_typing C (to_b_list es) ts.
Proof.
  move => s C es ts HBasic HType.
  dependent induction HType; basic_inversion; try by inversion HBasic; inversion H1.
  + replace (to_b_list (to_e_list bes)) with bes => //.
    by apply b_e_elim.
  + rewrite to_b_list_concat.
    eapply bet_composition.
    * by eapply IHHType1 => //.
    * by eapply IHHType2 => //.
  + apply bet_weakening. by eapply IHHType => //.
Qed.


Section composition_typing_proofs.

Hint Constructors be_typing : core.

(** A helper tactic for proving [composition_typing_single]. **)
Ltac auto_prove_bet:=
  repeat lazymatch goal with
  | H: _ |- exists ts t1s t2s t3s, ?tn = ts ++ t1s /\ ?tm = ts ++ t2s /\
                                   be_typing _ [::] (Tf _ _) /\ _ =>
    try exists [::], tn, tm, tn; try eauto
  | H: _ |- _ /\ _ =>
    split => //=; try eauto
  | H: _ |- be_typing _ [::] (Tf ?es ?es) =>
    apply bet_weakening_empty_both; try by []
  end.

Lemma composition_typing_single: forall C es1 e t1s t2s,
    be_typing C (es1 ++ [::e]) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             be_typing C es1 (Tf t1s' t3s) /\
                             be_typing C [::e] (Tf t3s t2s').
Proof.
  move => C es1 e t1s t2s HType.
  gen_ind_subst HType; extract_listn; auto_prove_bet.
  + by apply bet_block.
  + by destruct es1 => //=.
  + apply concat_cancel_last in H1. destruct H1. subst.
    by exists [::], t1s0, t2s0, t2s.
  + edestruct IHHType; eauto.
    destruct H as [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]. subst.
    exists (ts ++ x), t1s', t2s', t3s'.
    by repeat split => //=; rewrite -catA.
Qed.

Lemma composition_typing: forall C es1 es2 t1s t2s,
    be_typing C (es1 ++ es2) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             be_typing C es1 (Tf t1s' t3s) /\
                             be_typing C es2 (Tf t3s t2s').
Proof.
  move => C es1 es2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1.
  clear Heqes2'. subst.
  induction es2' => //=; move => es1 t1s t2s HType.
  - unfold rev in HType; simpl in HType. subst.
    rewrite cats0 in HType.
    exists [::], t1s, t2s, t2s.
    repeat split => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite rev_cons in HType.
    rewrite -cats1 in HType. subst.
    rewrite catA in HType.
    apply composition_typing_single in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]]. subst.
    apply IHes2' in H3.
    destruct H3 as [ts2 [t1s2 [t2s2 [t3s2 [H5 [H6 [H7 H8]]]]]]]. subst.
    exists ts', (ts2 ++ t1s2), t2s', (ts2 ++ t3s2).
    repeat split => //.
    + by apply bet_weakening.
    + rewrite rev_cons. rewrite -cats1.
      eapply bet_composition; eauto.
Qed.

Lemma e_composition_typing_single: forall s C es1 e t1s t2s,
    e_typing s C (es1 ++ [::e]) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             e_typing s C es1 (Tf t1s' t3s) /\
                             e_typing s C [::e] (Tf t3s t2s').
Proof.
  move => s C es1 es2 t1s t2s HType.
  gen_ind_subst HType; extract_listn.
  - (* basic *)
    apply b_e_elim in H3. destruct H3. subst.
    rewrite to_b_list_concat in H.
    apply composition_typing in H.
    apply basic_concat in H1. destruct H1.
    destruct H as [ts' [t1s' [t2s' [t3s' [H2 [H3 [H4 H5]]]]]]]. subst.
    exists ts', t1s', t2s', t3s'.
    by repeat split => //=; apply ety_a' => //=.
  - (* composition *)
    apply concat_cancel_last in H2. destruct H2. subst.
    by exists [::], t1s0, t2s0, t2s.
  - (* weakening *)
    edestruct IHHType; eauto.
    destruct H as [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]. subst.
    exists (ts ++ x), t1s', t2s', t3s'.
    by repeat split => //; rewrite catA.
  - (* Trap *)
    exists [::], t1s, t2s, t1s.
    repeat split => //=.
    + apply ety_a' => //. apply bet_weakening_empty_both. by apply bet_empty.
    + by apply ety_trap.
  - (* Local *)
    exists [::], [::], t2s, [::]. repeat split => //=.
    + by apply ety_a' => //.
    + by apply ety_local.
  - (* Reference *)
    exists [::], [::], [::T_ref (T_funcref (cl_type cl))], [::].
    repeat split => //.
    + apply ety_a' => //.
    + econstructor => //. exact H. (* exact H0. *)
  - (* Continuation *)
     exists [::], [::], [::T_ref (T_contref (typeof_cont cont))], [::].
    repeat split => //.
    + apply ety_a' => //.
    + econstructor; try done; try done.
  - (* Exception *)
    exists [::], [::], [:: T_ref T_exnref], [::].
    repeat split => //.
    + apply ety_a' => //.
    + econstructor; eauto.
  - (* Suspend_desugared *)
    eexists [::], _,_,_. 
    repeat split => //.
    + apply et_weakening_empty_both.
      apply ety_a' => //.
    + econstructor => //.
      exact H. done.
  - (* Switch_desugared *)
    exists [::], [::], t2s0, [::].
    repeat split => //.
    + apply et_weakening_empty_both.
      apply ety_a' => //.
    + econstructor => //.
      exact H. exact H1. exact H2. 
  - (* Throw_ref_desugared *)
    exists [::], t1s, t2s, t1s.
    repeat split => //.
    + apply et_weakening_empty_both.
      apply ety_a' => //.
    + econstructor => //. done.
  - (* Prompt *)
    exists [::], [::], t2s, [::]. repeat split => //=.
    + apply ety_a' => //.
    + econstructor => //.
  - (* Handler *)
    exists [::], [::], t2s, [::]. repeat split => //=.
    + apply ety_a' => //.
    + econstructor => //. 
  - (* Invoke *)
    exists [::], t1s, t2s, t1s. repeat split => //=.
    + apply ety_a' => //. apply bet_weakening_empty_both. by apply bet_empty.
    + by eapply ety_invoke; eauto.
  - (* Label *)
    exists [::], [::], t2s0, [::]. repeat split => //=.
    + by apply ety_a' => //.
    + by eapply ety_label; eauto.
  - (* Call host *)
    exists [::], [::], t2s0, [::]. repeat split => //=.
    + by apply ety_a' => //.
    + by eapply ety_call_host ; eauto.
Qed.

Lemma e_composition_typing: forall s C es1 es2 t1s t2s,
    e_typing s C (es1 ++ es2) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             e_typing s C es1 (Tf t1s' t3s) /\
                             e_typing s C es2 (Tf t3s t2s').
Proof.
  move => s C es1 es2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1.
  clear Heqes2'. subst.
  induction es2' => //=; move => es1 t1s t2s HType.
  - unfold rev in HType; simpl in HType. subst.
    rewrite cats0 in HType.
    exists [::], t1s, t2s, t2s.
    repeat split => //=.
    apply ety_a' => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite rev_cons in HType.
    rewrite -cats1 in HType. subst.
    rewrite catA in HType.
    apply e_composition_typing_single in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]]. subst.
    apply IHes2' in H3.
    destruct H3 as [ts2 [t1s2 [t2s2 [t3s2 [H5 [H6 [H7 H8]]]]]]]. subst.
    exists ts', (ts2 ++ t1s2), t2s', (ts2 ++ t3s2).
    repeat split => //.
    + by apply ety_weakening.
    + rewrite rev_cons. rewrite -cats1.
      eapply ety_composition; eauto.
      by apply ety_weakening.
Qed.

Lemma bet_composition': forall C es1 es2 t1s t2s t3s,
    be_typing C es1 (Tf t1s t2s) ->
    be_typing C es2 (Tf t2s t3s) ->
    be_typing C (es1 ++ es2) (Tf t1s t3s).
Proof.
  move => C es1 es2 t1s t2s t3s HType1 HType2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1. generalize dependent es2.
  generalize dependent t1s. generalize dependent t2s.
  generalize dependent t3s.
  induction es2' => //=.
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1. destruct es2 => //=. rewrite cats0.
    apply empty_btyping in HType2. by subst.
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1.
    rewrite rev_cons in H2. rewrite -cats1 in H2.
    rewrite H2 in HType2.
    apply composition_typing in HType2.
    destruct HType2 as [ts [t1s' [t2s' [t3s' [H3 [H4 [H5 H6]]]]]]]. subst.
    rewrite catA. eapply bet_composition => //=.
    instantiate (1 := (ts ++ t3s')).
    eapply IHes2' => //.
    instantiate (1 := (ts ++ t1s')); first by apply bet_weakening.
    symmetry. by apply revK.
    by apply HType1.
    by apply bet_weakening.
Qed.

Lemma bet_composition_front: forall C e es t1s t2s t3s,
    be_typing C [::e] (Tf t1s t2s) ->
    be_typing C es (Tf t2s t3s) ->
    be_typing C (e :: es) (Tf t1s t3s).
Proof.
  intros.
  rewrite - cat1s.
  by eapply bet_composition'; eauto.
Qed.

Lemma et_composition': forall s C es1 es2 t1s t2s t3s,
    e_typing s C es1 (Tf t1s t2s) ->
    e_typing s C es2 (Tf t2s t3s) ->
    e_typing s C (es1 ++ es2) (Tf t1s t3s).
Proof.
  move => s C es1 es2 t1s t2s t3s HType1 HType2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1. generalize dependent es2.
  generalize dependent t1s. generalize dependent t2s.
  generalize dependent t3s.
  induction es2' => //=.
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1. destruct es2 => //=. rewrite cats0.
    apply et_to_bet in HType2 => //. apply empty_btyping in HType2. by subst.
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1.
    rewrite rev_cons in H2. rewrite -cats1 in H2.
    rewrite H2 in HType2.
    apply e_composition_typing in HType2.
    destruct HType2 as [ts [t1s' [t2s' [t3s' [H3 [H4 [H5 H6]]]]]]]. subst.
    rewrite catA. eapply ety_composition => //=.
    instantiate (1 := (ts ++ t3s')).
    eapply IHes2' => //.
    instantiate (1 := (ts ++ t1s')); first by apply ety_weakening.
    symmetry. by apply revK.
    by apply HType1.
    by apply ety_weakening.
Qed.

End composition_typing_proofs.

Lemma cat_cons_not_nil : forall T (xs : list T) y ys,
  xs ++ (y :: ys) <> [::].
Proof. move => T xs y ys E. by move: (List.app_eq_nil _ _ E) => [? ?]. Qed.

Lemma not_reduce_simple_nil : forall es', ~ reduce_simple [::] es'.
Proof.
  assert (forall es es', reduce_simple es es' -> es = [::] -> False) as H.
  - move => es es' H.
    elim: {es es'} H => //=.
    + move => vs es _ _ t1s t2s _ _ _ _ H.
      apply: cat_cons_not_nil. exact H. 
    + move => vs es _ _ t1s t2s _ _ _ _ H.
      apply: cat_cons_not_nil. exact H. 
    + move => es lh _ H Hes.
      rewrite Hes {es Hes} /lfilled /operations.lfilled /= in H.
      case: lh H => //=.
      * move => es es2.
        case_eq (const_list es) => //=.
        move=> _ /eqP H.
        symmetry in H.
        by move: (List.app_eq_nil _ _ H) => [? ?].
      * intros bef hs lh aft. destruct (const_list bef) => //.
        destruct (lfill _ _ _) => //. destruct bef => //.
      * intros bef hs lh aft. destruct (const_list bef) => //.
        destruct (lfill _ _ _) => //. destruct bef => //. 
  - move => es' H2.
    apply: H. exact H2. done. 
Qed.


Lemma lfill_cons_not_Some_nil : forall i lh es es' e es0,
  lfill i lh es = es' -> es = e :: es0 -> es' <> Some [::].
Proof.
  elim.
  - elim; try by intros; subst.
    + move=> l l0 es es' /=.
      case: (const_list l).
      * move => Hfill H1 H2 H3 H4.
        rewrite H4 in H2.
        injection H2 => H5 {H2}.
        rewrite H3 in H5.
        apply: cat_cons_not_nil.
        exact H5.
      * intros; subst; discriminate.
    + intros bef hs lh aft bef' ts' hs' lh' aft' LI Hfill Heq.
      simpl in LI.
      destruct (const_list bef) => //.
      * destruct (lfill _ _ _) => //.
        -- by subst; destruct bef.
        -- by subst.
      * by subst.
    + intros bef ts hs lh aft bef' ts' hs' lh' aft' LI Hfill Heq.
      simpl in LI.
      destruct (const_list bef) => //.
      * destruct (lfill _ _ _) => //.
        -- by subst; destruct bef.
        -- by subst.
      * by subst.
  - move=> n IH.
    elim; first by intros; subst.
    intros.
    rewrite /= in H0.
    move: H0.
    case: (const_list l).
    + rewrite H1 {H1}.
      case_eq (lfill n l1 (e :: es0)).
      * move=> l3 H1 H2 H3.
        rewrite H3 in H2.
        injection H2.
        move=> {} H2.
        apply: cat_cons_not_nil.
        exact H2. 
      * intros; subst; discriminate. 
    + intros; subst; discriminate.
    + intros; subst. simpl.
      destruct (const_list l) => //.
      destruct (lfill _ _ _) => //.
      destruct l => //.
          + intros; subst. simpl.
      destruct (const_list l) => //.
      destruct (lfill _ _ _) => //.
      destruct l => //.
Qed.

Lemma lfilled_not_nil : forall i lh es es', lfilled i lh es es' -> es <> [::] -> es' <> [::].
Proof.
  move => i lh es es' H Hes Hes'.
  move: (List.exists_last Hes) => [e [e0 H']].
  rewrite H' in H.
  move: H.
  rewrite /lfilled /operations.lfilled.
  case_eq (operations.lfill i lh es).
  { intros; subst.
    rewrite H in H0.
    assert ([::] = l) as H0'.
    { apply/eqP.
      apply H0. }
    { rewrite H0' in H.
      rewrite /= in H.
      case E: (e ++ (e0 :: l)%SEQ)%list; first by move: (List.app_eq_nil _ _ E) => [? ?].
      apply: lfill_cons_not_Some_nil.
      apply: H.
      apply: E.
      by rewrite H0'. } }
  { intros; subst.
    rewrite H in H0.
    done. }
Qed.

Lemma reduce_not_nil : forall σ1 f es σ2 f' es',
  reduce σ1 f es σ2 f' es' -> es <> [::].
Proof.
  move => σ1 f es σ2 f' es' Hred.
  elim: {σ1 f es f' σ2} Hred => // ;
    try by intros; (destruct vs + destruct ves).
  - move => e e' _ _ Hreds He.
    rewrite He in Hreds.
    apply: not_reduce_simple_nil.
    apply: Hreds. 
  - intros. apply: lfilled_not_nil. exact H1. exact H0. 
Qed.


 Lemma typeof_extension: forall s s' v,
    store_extension s s' ->
    typeof s v = typeof s' v \/ typeof s v = None /\ (exists tf, typeof s' v = Some (T_ref (T_contref tf))) \/ typeof s v = None /\ typeof s' v = Some (T_ref T_exnref).
Proof.
  intros s s' v HSF. unfold store_extension in HSF. remove_bools_options.
  induction v => //=; try by left.
  induction v => //=; try by left.
  - left; by rewrite H.
  - remember (s_conts s) as l. remember (s_conts s') as l'.
    clear - H4.
    generalize dependent l'. generalize dependent f.
    induction l; intros f l' Hextension.
    + destruct (List.nth_error l' f).
      * right. left. split; first by destruct f.
        exists (typeof_cont c). done.
      * left. by destruct f.
    + destruct l' => //. simpl in Hextension.
      unfold cont_extension in Hextension. remove_bools_options.
      destruct c => //.
      * move/eqP in H. subst a. destruct f => //=.
        -- by left.
        -- apply IHl. done.
      * move/eqP in H. destruct f => //=.
        -- rewrite H. by left.
        -- apply IHl. done.
  - remember (s_exns s) as l. remember (s_exns s') as l'.
    clear - H0.
    generalize dependent l'. generalize dependent e.
    induction l; intros e l' Hextension.
    + destruct (List.nth_error l' e).
      * destruct (e_tag e0 == t).
        -- right. right. split; first by destruct e. done.
        -- left. by destruct e.
      * left. by destruct e.
    + destruct l' => //. simpl in Hextension.
      inversion Hextension.
      subst e0. rewrite - H1.
      destruct e => //=.
      * by left.
      * apply IHl. exact H1.
Qed. 

