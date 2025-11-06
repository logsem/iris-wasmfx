From mathcomp Require Import ssreflect eqtype seq ssrbool.
From Stdlib Require Import List.
From stdpp Require Import base list.
From Wasm Require Export stdpp_aux datatypes operations properties opsem.
From Wasm.iris.helpers.lfill_prelude Require Export lfill_prelude.

Set Bullet Behavior "Strict Subproofs".

(* Ltac false_assumption := exfalso ; apply ssrbool.not_false_is_true ; assumption. *)

Lemma found_intruse l1 l2 (x : administrative_instruction) :
  l1 = l2 -> (In x l1 -> False) -> In x l2 -> False.
Proof.
  intros. rewrite H in H0. apply H0 ; exact H1.
Qed.

(* If H is a hypothesis that states the equality between 2 lists, attempts to prove
   False by showing object x is in the rhs of H, but not in the lhs.
   If attempt fails, user is given a hypothesis Hxl1 to end proof manually *)
Ltac found_intruse x H Hxl1 :=
  exfalso ; 
  apply (found_intruse _ _ x H) ;
  [intro Hxl1 ; repeat ((destruct Hxl1 as [Hxl1 | Hxl1] ; [ inversion Hxl1 |]) +
                          assumption  ) |
    try by (apply in_or_app ; right ; left ; trivial) ].

(*

(* Attempts to prove False from hypothesis H, which states that an lholed is filled
   with AI_trap. If attempt fails, user is given a hypothesis Hxl1 to end proof manually *)
Ltac filled_trap H Hxl1 :=
  exfalso ;
  unfold lfilled, lfill in H ; 
  destruct (_:lholed) in H => //;
                               fold lfill in H;
                               destruct (const_list _) in H => //;
                               (try destruct (lfill _ _ _) eqn:Hfill => //);
  move/eqP in H ; found_intruse AI_trap H Hxl1.

(* Given hypothesis H, which states that an lholed lh is filled at level k, 
   unfolds the definition of lfilled. Attempts to prove a contradiction when k > 0.
   If attempts fail, user is given that filled expression is 
   vs ++ (AI_label n l1 l3) :: l0 *)
Ltac simple_filled H k lh l0 n l1 l3 :=
  let l2 := fresh "l" in
  let lh' := fresh "lh" in
  let Hxl1 := fresh "Hxl1" in
  let les := fresh "les" in
  let Hvs := fresh "Hvs" in
  unfold lfilled, lfill in H ;
  destruct lh ;
  [ destruct k => //;
                   destruct (const_list _) eqn:Hvs => //; move/eqP in H
  | destruct k => //;
    fold lfill in H ; 
                 destruct (const_list _) eqn:Hvs => //;
                                                     destruct (lfill _ _ _) eqn:Hfill => //;
                                                                                          move/eqP in H ; found_intruse (AI_label n l1 l3) H Hxl1
  | fold lfill in H ; 
    destruct (const_list _) eqn:Hvs => //;
                                        destruct (lfill _ _ _) eqn:Hfill => //;
                                                                             move/eqP in H ; found_intruse (AI_label n l1 l3) H Hxl1
  | fold lfill in H ; 
    destruct (const_list _) eqn:Hvs => //;
                                        destruct (lfill _ _ _) eqn:Hfill => //;
                                                                             move/eqP in H ; found_intruse (AI_label n l1 l3) H Hxl1

  ].

(* Like simple_filled, but does not attempt to solve case k > 0 *)
Ltac simple_filled2 H k lh vs l0 n l1 l3 :=
  let l2 := fresh "l" in
  let lh' := fresh "lh" in
  let Hxl1 := fresh "Hxl1" in
  let les := fresh "les" in
  let Hvs := fresh "Hvs" in
  unfold lfilled, lfill in H ;
   destruct lh ;
  [ destruct k => //;
                   destruct (const_list vs) eqn:Hvs => //; move/eqP in H
  | destruct k => //;
    fold lfill in H ; destruct lh => //;
                                      destruct (const_list vs) eqn:Hvs => //;
                                                                           destruct (lfill _ _ _) eqn:Hfill => //;
                                                                                                                move/eqP in H ; try by found_intruse (AI_label n l1 l3) H Hxl1
  | fold lfill in H ; destruct lh => //;
                                      destruct (const_list vs) eqn:Hvs => //;
                                                                           destruct (lfill _ _ _) eqn:Hfill => //;
                                                                                                                move/eqP in H ; try by found_intruse (AI_label n l1 l3) H Hxl1
  | fold lfill in H ; destruct lh => //;
                                      destruct (const_list vs) eqn:Hvs => //;
                                                                           destruct (lfill _ _ _) eqn:Hfill => //;
                                                                                                                move/eqP in H ; try by found_intruse (AI_label n l1 l3) H Hxl1

  ].
*)

Global Instance ai_eq_dec: EqDecision (administrative_instruction).
Proof.
  by decidable_equality.
Defined.
Global Instance ai_list_eq_dec: EqDecision (seq.seq administrative_instruction).
Proof.
  by decidable_equality.
Defined.

Lemma ai_eq_true a a0 : administrative_instruction_eqb a a0 = true <-> a = a0.
Proof.
  split; by move/eqP.
Qed.

Lemma ai_eqseq_true (l1 l2 : seq.seq administrative_instruction) :
  l1 = l2 <-> (l1 == l2) = true.
Proof.
  split; by move/eqP.
Qed.


Section lfilled_properties.

  Fixpoint base_is_empty lh :=
    match lh with
    | LH_base bef aft => bef = [] /\ aft = []
    | LH_rec _ _ _ lh _
    | LH_prompt _ _ _ lh _
    | LH_handler _ _ lh _
      => base_is_empty lh
    end.

  Fixpoint empty_base lh :=
    match lh with
    | LH_base bef aft => (LH_base [] [], bef, aft)
    | LH_rec a b c lh d => let '( lh', bef, aft) := empty_base lh in
                          (LH_rec a b c lh' d, bef, aft)
    | LH_prompt a b c lh d => let '( lh', bef, aft) := empty_base lh in
                             (LH_prompt a b c lh' d, bef, aft)
    | LH_handler a b lh c => let '( lh', bef, aft) := empty_base lh in
                            (LH_handler a b lh' c, bef, aft)
    end.

  Fixpoint get_layer lh i :=
    match lh,i with
    | LH_base vs es, _ => None
    | LH_rec vs' n es lh' es', 0 => Some (vs',n,es,lh',es')
    | LH_rec _ _ _ lh' _, S n => get_layer lh' n
    | LH_prompt _ _ _ lh' _, n => get_layer lh' n
    | LH_handler _ _ lh' _, n => get_layer lh' n
    end.

  Definition delete_outer lh :=
    match lh with
    | LH_base _ _ => lh
    | LH_rec vs n es lh es' => lh
    | LH_prompt _ _ _ lh _ => lh
    | LH_handler _ _ lh _ => lh
    end.

  Definition lh_delete_inner lh :=
    let '(lh',_,_) := empty_base lh in lh'.

  Fixpoint sh_pull_const_r sh vs :=
    match sh with
    | SH_base bef aft  => SH_base (bef ++ vs) aft 
    | SH_rec bef n es sh aft => SH_rec bef n es (sh_pull_const_r sh vs) aft
    | SH_prompt bef ts hs sh aft => SH_prompt bef ts hs (sh_pull_const_r sh vs) aft
    | SH_handler bef hs sh aft => SH_handler bef hs (sh_pull_const_r sh vs) aft
    end.

  Fixpoint lh_pull_const_r lh vs :=
    match lh with
    | LH_base bef aft  => LH_base (bef ++ vs) aft 
    | LH_rec bef n es sh aft => LH_rec bef n es (lh_pull_const_r sh vs) aft
    | LH_prompt bef ts hs sh aft => LH_prompt bef ts hs (lh_pull_const_r sh vs) aft
    | LH_handler bef hs sh aft => LH_handler bef hs (lh_pull_const_r sh vs) aft
    end.
  
  Inductive lh_minus_Ind : lholed -> lholed -> lholed -> Prop :=
  | lh_minus_base lh : lh_minus_Ind lh (LH_base [] []) lh
  | lh_minus_ind lh lh' lh'' vs n es es' :
    lh_minus_Ind lh lh' lh'' ->
    lh_minus_Ind (LH_rec vs n es lh es') (LH_rec vs n es lh' es') lh''
  | lh_minus_prompt lh lh' lh'' bef ts hs aft :
    lh_minus_Ind lh lh' lh'' ->
    lh_minus_Ind (LH_prompt bef ts hs lh aft) (LH_prompt bef ts hs lh' aft) lh''
  | lh_minus_handler lh lh' lh'' bef hs aft :
    lh_minus_Ind lh lh' lh'' ->
    lh_minus_Ind (LH_handler bef hs lh aft) (LH_handler bef hs lh' aft) lh''
  .

  Lemma to_e_list_fmap l :
    fmap (fun v => AI_const v) l = v_to_e_list l.
  Proof.
    induction l;auto.
  Qed.

  Lemma can_empty_base k lh es LI lh' bef aft :
    empty_base lh = (lh', bef, aft) -> 
    lfilled k lh es LI ->
    exists es', lfilled 0 (LH_base bef aft) es es' /\ lfilled k lh' es' LI /\ base_is_empty lh'.
  Proof.
    intros.
    generalize dependent lh'.
    generalize dependent bef. generalize dependent aft.
    generalize dependent LI. generalize dependent k. 
    induction lh ; intros k LI Hfill aft beft lh' Hempty.
    all: unfold lfilled, lfill in Hfill; fold lfill in Hfill.
    1,2: destruct k => //.
    all: try specialize (IHlh k).
    all: try unfold lfilled in IHlh.
    all: destruct (const_list l) eqn:Hl => //.
    all: try (destruct (lfill _ _ _) eqn:Hfill'; last done).
    all: move/eqP in Hfill; subst LI.
    all: simpl in Hempty.
    2-4: destruct (empty_base lh) as [[??]?] eqn:Hlh.
    all: inversion Hempty; subst.
    all: try edestruct IHlh as (es' & Hres0 & Hres' & Hbase) => //=.
    exists (beft ++ es ++ aft).
    all: try eexists es'.
    all: repeat split => //=.
    all: unfold lfilled, lfill; fold lfill => //=.
    2: by rewrite app_nil_r.
    all: rewrite Hl => //.
    all: destruct (lfill k _ es') => //.
    all: move/eqP in Hres'; subst => //.
  Qed.
  

  Lemma can_fill_base k lh es es' LI lh' bef aft:
    empty_base lh = (lh', bef, aft) ->
    lfilled 0 (LH_base bef aft) es es' -> lfilled k lh' es' LI -> lfilled k lh es LI.
  Proof.
    generalize dependent LI ; generalize dependent k.
    generalize dependent lh' ; generalize dependent aft; generalize dependent bef.
    induction lh ; intros bef aft lh' k LI Hempty ; simpl.
    all: simpl in Hempty.
    2-4: destruct (empty_base lh) as [[??]?] eqn:Hlh.
    all: inversion Hempty; subst.
    all: intros Hfill0 Hfill.
    all: apply/lfilledP.
    all: move/lfilledP in Hfill0.
    all: move/lfilledP in Hfill.
    all: inversion Hfill; subst.
    { inversion Hfill0; subst.
      rewrite cats0 /=.
      constructor.
      done. } 
    all: constructor => //.
    all: apply/lfilledP.
    all: eapply IHlh => //.
    all: apply/lfilledP => //.
  Qed.


  Fixpoint lh_minus lh1 lh2 :=
    match lh2 with
    | LH_base [] [] => Some lh1
    | LH_base _ _ => None
    | LH_rec bef2 n2 es2 lh2 aft2 =>
        match lh1 with
        | LH_rec bef1 n1 es1 lh1 aft1 =>
            if (bef1 == bef2) && (n1 =? n2) && (es1 == es2) && (aft1 == aft2)
            then lh_minus lh1 lh2
            else None
        | _ => None
        end
    | LH_prompt bef2 ts2 hs2 lh2 aft2 =>
        match lh1 with
        | LH_prompt bef1 ts1 hs1 lh1 aft1 =>
            if (bef1 == bef2) && (ts1 == ts2) && (hs1 == hs2) && (aft1 == aft2)
            then lh_minus lh1 lh2
            else None
        | _ => None
        end
    | LH_handler bef2 hs2 lh2 aft2 =>
        match lh1 with
        | LH_handler bef1 hs1 lh1 aft1 =>
            if (bef1 == bef2) && (hs1 == hs2) && (aft1 == aft2)
            then lh_minus lh1 lh2
            else None
        | _ => None                 
        end
        end .


  Lemma lh_minus_LH_base lh1 bef aft :
    lh_minus lh1 (LH_base bef aft) =
      match bef with
        [::] => match aft with
                [::] => Some lh1
              | _ => None
              end
      | _ => None
      end.
  Proof.
    destruct lh1 => //=.
  Qed. 

  Lemma lh_minus_plus k0 k1 lh0 lh1 lh2 es0 es1 es2 :
    lh_minus lh0 lh1 = Some lh2 ->
    k0 >= k1 -> 
    lfilled (k0 - k1) lh2 es0 es1 ->
    lfilled k1 lh1 es1 es2 ->
    lfilled k0 lh0 es0 es2.
  Proof.
    generalize dependent k0 ; generalize dependent es2 ;
      generalize dependent lh0 ; generalize dependent k1.
    induction lh1 ; intros k1 lh0 es2 k0 Hminus Hk Hfill2 Hfill1.
    all: unfold lfilled, lfill in Hfill1; fold lfill in Hfill1.
    1-2: destruct k1 => //.
(*    all: try specialize (IHlh1 k1). *)
(*    all: try unfold lfilled in IHlh1. *)
    all: destruct (const_list l) eqn:Hl => //.
    all: try destruct (lfill k1 _ _) eqn:Hfill' => //.
    all: move/eqP in Hfill1; subst es2.
    { rewrite lh_minus_LH_base in Hminus.
      destruct l => //.
      destruct l0 => //.
      inversion Hminus; subst.
      rewrite Nat.sub_0_r in Hfill2.
      rewrite app_nil_r /=.
      done. } 
    all: destruct lh0; simpl in Hminus; try by inversion Hminus.
    all: destruct (_ && _) eqn:Heqs => //.
    all: remove_bools_options; subst.
    apply Nat.eqb_eq in H2; subst n0.
    destruct k0; first lias.
    all: apply/lfilledP.
    all: constructor => //.
    all: apply/lfilledP.
    all: eapply IHlh1 => //.
    lias.
    all: unfold lfilled; rewrite Hfill' => //. 
  Qed.
  
  Lemma lh_minus_minus k0 k1 lh0 lh1 lh2 es0 es1 es2 :
    lh_minus lh0 lh1 = Some lh2 ->
    lfilled k0 lh0 es0 es2 ->
    lfilled k1 lh1 es1 es2 ->
    lfilled (k0 - k1) lh2 es0 es1.
  Proof.
    generalize dependent k1 ; generalize dependent es2 ;
      generalize dependent lh0 ; generalize dependent k0.
    induction lh1 ; intros k0 lh0 es2 k1 Hminus Hfill0 Hfill1.
    all: unfold lfilled, lfill in Hfill1; fold lfill in Hfill1.
    1-2: destruct k1 => //.
    all: destruct (const_list l) eqn:Hl => //.
    all: try (destruct (lfill _ _ _) eqn:Hfill'; last done).
    all: move/eqP in Hfill1; subst es2.
    { rewrite lh_minus_LH_base in Hminus.
      destruct l => //. destruct l0 => //.
      rewrite Nat.sub_0_r. rewrite app_nil_r /= in Hfill0.
      inversion Hminus; subst.
      done. }
    all: destruct lh0; simpl in Hminus; try by inversion Hminus.
    all: destruct (_ && _) eqn:Heqs => //.
    all: remove_bools_options; subst.
    apply Nat.eqb_eq in H2; subst n0.
    all: move/lfilledP in Hfill0.
    all: inversion Hfill0; subst.
    2: apply app_app in H6 => //. 
    1,3: apply app_app in H7 => //.
    1,2: inversion H7; subst.
    3: inversion H6; subst.
    replace (S k - S k1) with (k - k1); last lias.
    all: eapply IHlh1; eauto.
    all: try by apply/lfilledP; eauto.
    all: unfold lfilled; rewrite Hfill' => //. 
  Qed. 


  Lemma lfilled_depth k lh es LI :
    lfilled k lh es LI ->
    lh_depth lh = k.
  Proof.
    generalize dependent k ; generalize dependent LI.
    induction lh ; intros LI k Hfill ;
      unfold lh_depth ;
      unfold lfilled, lfill in Hfill ;
      fold lfill in Hfill.
    1-2: destruct k => //=. 
    all: fold lh_depth.
    all: destruct (const_list l) => //. 
    all: destruct (lfill k lh es) eqn:Hfill' => //.
    all: move/eqP in Hfill; subst.
    f_equal.
    all: eapply IHlh.
    all: unfold lfilled; rewrite Hfill' => //.
  Qed.
  
  Lemma lfilled_same_index k0 k1 lh es0 es1 LI0 LI1 :
    lfilled k0 lh es0 LI0 ->
    lfilled k1 lh es1 LI1 ->
    k0 = k1.
  Proof.
    move => Hlf1 Hlf2.
    by apply lfilled_depth in Hlf1, Hlf2; subst.
  Qed.

  Fixpoint lh_true_depth lh :=
    match lh with
    | LH_base _ _ => 0
    | LH_rec _ _ _ lh _
    | LH_handler _ _ lh _
    | LH_prompt _ _ _ lh _ => S (lh_true_depth lh)
    end.

  Lemma true_depth_leq_filled lh1 lh2 k1 k2 es1 es2 LI:
    lh_true_depth lh1 <= lh_true_depth lh2 ->
    lfilled k1 lh1 es1 LI ->
    lfilled k2 lh2 es2 LI ->
    k1 <= k2.
  Proof.
    intros Hleq Hfill1.
    generalize dependent lh2. generalize dependent k2.
    move/lfilledP in Hfill1.
    induction Hfill1 => //=.
    { lia. } 
    all: intros k2 lh2 Hleq Hfill2.
    all: move/lfilledP in Hfill2.
    all: inversion Hfill2; subst.
    all: try lazymatch goal with
           | H : (_ ++ _ :: _)%SEQ = (_ ++ _ :: _)%SEQ |- _ =>
               apply first_values in H as (? & ? & ?) => //
           end. 
    all: simpl in Hleq; try lia.
    all: inversion H2; subst.
    all: move/lfilledP in H5.
    all: apply IHHfill1 in H5 => //.
    all: lia.
  Qed.

   Lemma true_depth_lt_minus lh1 lh2 lh1' bef1 aft1 bef2 aft2:
     lh_true_depth lh1 < lh_true_depth lh2 ->
     empty_base lh1 = (lh1', bef1, aft1) ->
     lh_minus lh2 lh1' = Some (LH_base bef2 aft2) ->
     False.
  Proof.
    intros Hleq Hempty Hminus.
    generalize dependent lh2. generalize dependent lh1'.
    induction lh1; intros lh'1 Hempty lh2 Hleq Hminus.
    - inversion Hempty; subst.
      destruct lh2 => //.
      simpl in Hleq. lia.
    - simpl in Hempty.
      destruct (empty_base lh1) as [[??]?].
      inversion Hempty; subst.
      destruct lh2 => //.
      simpl in Hminus.
      destruct (_ && _) eqn:Heq => //.
      remove_bools_options.
      apply Nat.eqb_eq in H2. subst.
      simpl in Hleq.
      eapply IHlh1. done.
      2: exact Hminus.
      lia.
    - simpl in Hempty.
      destruct (empty_base lh1) as [[??]?].
      inversion Hempty; subst.
      destruct lh2 => //.
      simpl in Hminus.
      destruct (_ && _) eqn:Heq => //.
      remove_bools_options.
      subst.
      simpl in Hleq.
      eapply IHlh1. done.
      2: exact Hminus.
      lia.
    - simpl in Hempty.
      destruct (empty_base lh1) as [[??]?].
      inversion Hempty; subst.
      destruct lh2 => //.
      simpl in Hminus.
      destruct (_ && _) eqn:Heq => //.
      remove_bools_options.
      subst.
      simpl in Hleq.
      eapply IHlh1. done.
      2: exact Hminus.
      lia.
  Qed. 

    

  Lemma empty_base_same_true_depth lh lh' x y :
    empty_base lh = (lh', x, y) -> lh_true_depth lh = lh_true_depth lh'.
  Proof.
    generalize dependent lh'.
    induction lh => //=.
    all: intros lh' Heq.
    by inversion Heq; subst => //=.
    all: destruct (empty_base lh) as [[??]?] eqn:Hlh.
    all: inversion Heq; subst => //=.
    all: by erewrite IHlh.
  Qed. 
    
    

  
  Lemma lh_minus_depth lh0 lh1 lh2 :
    lh_minus lh0 lh1 = Some lh2 ->
    lh_depth lh2 = lh_depth lh0 - lh_depth lh1.
  Proof.
    generalize dependent lh0.
    induction lh1 ; intros lh0 Hminus.
    { rewrite lh_minus_LH_base in Hminus.
      destruct l => //.
      destruct l0 => //.
      inversion Hminus; subst.
      simpl. lias. }
    all: destruct lh0; simpl in Hminus; try inversion Hminus.
    all: destruct (_ && _) eqn:Heq => //.
    all: simpl.
    all: apply IHlh1 => //.
  Qed.

    Lemma lh_minus_true_depth lh0 lh1 lh2 :
    lh_minus lh0 lh1 = Some lh2 ->
    lh_true_depth lh2 = lh_true_depth lh0 - lh_true_depth lh1.
  Proof.
    generalize dependent lh0.
    induction lh1 ; intros lh0 Hminus.
    { rewrite lh_minus_LH_base in Hminus.
      destruct l => //.
      destruct l0 => //.
      inversion Hminus; subst.
      simpl. lias. }
    all: destruct lh0; simpl in Hminus; try inversion Hminus.
    all: destruct (_ && _) eqn:Heq => //.
    all: simpl.
    all: apply IHlh1 => //.
  Qed.


  Lemma lh_minus_minus2 k0 k1 k2 lh0 lh1 lh2 es0 es1 es2 :
    lh_minus lh0 lh1 = Some lh2 ->
    lfilled k0 lh0 es0 es2 ->
    lfilled k1 lh2 es0 es1 ->
    k2 = k0 - k1 ->
    lfilled k2 lh1 es1 es2.
  Proof.
    intros ??? ->.
    generalize dependent lh0. generalize dependent es2.
    generalize dependent k0. generalize dependent k1.
    induction lh1 ; intros k1 Hfill2 k0 es2 lh0 Hminus Hfill0.
    
    { rewrite lh_minus_LH_base in Hminus.
      destruct l => //. 
      destruct l0 => //.
      inversion Hminus; subst.
      specialize (lfilled_same_index _ _ _ _ _ _ _  Hfill0 Hfill2) ; intro.
      rewrite H in Hfill0.
      eapply lfilled_inj in Hfill0 ; last exact Hfill2.
      rewrite Hfill0.
      rewrite H Nat.sub_diag.
      by unfold lfilled, lfill => //= ; rewrite app_nil_r. }
    all: destruct lh0; simpl in Hminus; try by inversion Hminus.
    all: destruct (_ && _) eqn:Heq => //.
    all: remove_bools_options; subst.
    apply Nat.eqb_eq in H2; subst n0.
    all: move/lfilledP in Hfill0.
    all: inversion Hfill0; subst.
    all: apply/lfilledP.
    destruct (S k - k1) eqn:Hk.
    { move/lfilledP in H8.
      apply lfilled_depth in Hfill2, H8.
      apply lh_minus_depth in Hminus.
      rewrite H8 Hfill2 in Hminus.
      lia. } 

    all: constructor => //.
    all: apply/lfilledP.
    replace n0 with (k - k1); last lia.
    all: eapply IHlh1 => //.
    all: by apply/lfilledP.
  Qed.

  (* Old version *)
  (*
  Lemma lh_minus_minus2 k0 k1 lh0 lh1 lh2 es0 es1 es2 :
    lh_minus lh0 lh1 = Some lh2 ->
    k0 >= k1 ->
    lfilled k0 lh0 es0 es2 ->
    lfilled (k0 - k1) lh2 es0 es1 ->
    lfilled k1 lh1 es1 es2.
  Proof.
    generalize dependent lh0. generalize dependent es2.
    generalize dependent k0. generalize dependent k1.
    induction lh1 ; intros k1 k0 es2 lh0 Hminus Hk Hfill0 Hfill2.
    
    { rewrite lh_minus_LH_base in Hminus.
      destruct l => //. 
      destruct l0 => //.
      inversion Hminus; subst.
      specialize (lfilled_same_index _ _ _ _ _ _ _  Hfill0 Hfill2) ; intro.
      rewrite H in Hfill0.
      eapply lfilled_inj in Hfill0 ; last exact Hfill2.
      rewrite Hfill0.
      assert (k1 = 0) ; first lia.
      rewrite H0.
      by unfold lfilled, lfill => //= ; rewrite app_nil_r. }
    all: destruct lh0; simpl in Hminus; try by inversion Hminus.
    all: destruct (_ && _) eqn:Heq => //.
    all: remove_bools_options; subst.
    apply Nat.eqb_eq in H2; subst n0.
    all: move/lfilledP in Hfill0.
    all: inversion Hfill0; subst.
    all: apply/lfilledP.
    destruct k1.
    { replace (S k - 0) with (S k) in Hfill2 ; last lia.
      move/lfilledP in H8.
      apply lfilled_depth in Hfill2, H8.
      apply lh_minus_depth in Hminus.
      rewrite H8 Hfill2 in Hminus.
      lia. }
    all: constructor => //.
    all: apply/lfilledP.
    all: eapply IHlh1 => //.
    lias.
    all: by apply/lfilledP.
  Qed. *)


  

  Lemma filled_twice k0 k1 lh0 lh1 es0 es1 LI :
    lfilled k0 lh0 es0 LI ->
    lfilled k1 lh1 es1 LI ->
    (*    k0 >= k1 -> *)
    lh_true_depth lh0 >= lh_true_depth lh1 ->
    base_is_empty lh1 ->
    exists lh2, lh_minus lh0 lh1 = Some lh2.
  Proof.
    generalize dependent k1 ; generalize dependent LI ;
      generalize dependent lh0 ; generalize dependent k0.
    induction lh1 ; intros k0 lh0 LI k1 Hfill0 Hfill1 Hk Hempty.
    all: unfold lfilled, lfill in Hfill1; fold lfill in Hfill1.
    1-2: destruct k1 => //.
    all: destruct (const_list l) eqn:Hl => //.
    all: try (destruct (lfill _ _ _) eqn:Hfill'; last done).
    all: move/eqP in Hfill1; subst LI.
    all: simpl in Hempty.
    { destruct Hempty as [-> ->].
      exists lh0. destruct lh0 => //. }
    all: move/lfilledP in Hfill0.
    all: destruct lh0; inversion Hfill0; subst.
    all: try by simpl in Hk; lia.
    all: lazymatch goal with
         | H4 : (_ ++ _ :: _)%SEQ = (_ ++ _ :: _)%SEQ |- _ =>
             apply first_values in H4 as (? & ? & ?)
         | H4 : (_ ++ _ :: _)%SEQ = _ ++ (_ :: _)%SEQ |- _ =>
             apply first_values in H4 as (? & ? & ?)
         end => //.
    all: inversion H0; subst.
    all: repeat rewrite /= eq_refl.
    rewrite Nat.eqb_refl /=.
    all: eapply IHlh1 in Hempty => //.
    all: try by apply/lfilledP.
    all: try by unfold lfilled; erewrite Hfill'.
    all: simpl in Hk; lia.
  Qed.


  
  Lemma length_lfilled_rec_or_same k lh es LI :
    lfilled k lh es LI -> length_rec es < length_rec LI \/ es = LI /\ k = 0 /\ lh = LH_base [::] [::].
  Proof.
    move => Hlf; move/lfilledP in Hlf.
    induction Hlf.
    { repeat rewrite length_app_rec.
      destruct vs, es' => /=; try by left; unfold length_rec; destruct a; lias.
      right. by rewrite cats0.
    }
    all: destruct IHHlf as [? | (? & ? & ?)]; last subst.
    all: rewrite length_app_rec cat_app length_app_rec;
        unfold length_rec in * => /=; lia.
  Qed.
  
  
  Lemma filled_trivial k lh es :
    lfilled k lh es es -> k = 0 /\ lh = LH_base [] [].
  Proof.
    intros Hfill.
    apply length_lfilled_rec_or_same in Hfill as [?|(? & ? & ?)] => //.
    lias.
  Qed.     


  Lemma lfilled_const k lh es LI :
    lfilled k lh es LI ->
    const_list LI ->
    k = 0 /\ const_list es.
  Proof.
    intros.
    destruct lh; 
      unfold lfilled, lfill in H; fold lfill in H.
    1-2: destruct k.
    all: destruct (const_list l) eqn:Hl => //.
    all: try (destruct (lfill _ _ _); last done).
    all: move/eqP in H; subst LI.
    all: apply const_list_split in H0 as [_ H].
    all: try rewrite separate1 in H.
    all: apply const_list_split in H as [H _].
    all: done.
  Qed.

  Lemma hfilled_const x lh es LI :
    hfilled x lh es LI ->
    const_list LI ->
    const_list es.
  Proof.
    intros Hfill HLI.
    move/hfilledP in Hfill.
    inversion Hfill; subst.
    all: apply const_list_split in HLI as [_ HLI].
    all: apply const_list_split in HLI as [? _] => //.
  Qed. 

  Lemma filled_singleton k lh es e :
    lfilled k lh es [e] ->
    (forall a b c, e = AI_label a b c -> False) ->
    (forall a b c, e = AI_prompt a b c -> False) ->
    (forall a b, e = AI_handler a b -> False) ->
    es <> [] ->
    k = 0 /\ lh = LH_base [] [] /\ es = [e].
  Proof.
    intros.
    destruct lh; unfold lfilled, lfill in H; fold lfill in H.
    1-2: destruct k => //.
    all: destruct (const_list l) eqn:Hl => //.
    2-4: destruct (lfill _ _ _) eqn:Hfill' => //.
    all: move/eqP in H.
    all: destruct l; last by destruct l => //; inversion H => //; destruct es => //.
    all: destruct es => //.
    all: inversion H => //.
    { destruct es, l0 => //. }
    all: exfalso; subst.
    by eapply H0.
    by eapply H2.
    by eapply H1.
  Qed.

  Lemma hfilled_singleton x lh es e :
    hfilled x lh es [e] ->
    (forall a b c, e = AI_label a b c -> False) ->
    (forall a b c, e = AI_frame a b c -> False) ->
    (forall a b c, e = AI_prompt a b c -> False) ->
    (forall a b, e = AI_handler a b -> False) ->
    es <> [] ->
    lh = HH_base [] [] /\ es = [e].
  Proof.
    intros.
    move/hfilledP in H; inversion H; subst.
    all: try (destruct vs; last by destruct vs; try destruct es).
    all: try (destruct bef; last by destruct bef; try destruct es).
    2-5: inversion H5; subst; exfalso.
    2: by eapply H0.
    2: by eapply H1.
    2: by eapply H2.
    2: by eapply H3.
    destruct es => //.
    inversion H5; destruct es, es' => //.
  Qed. 

  Definition lh_prepend lh v :=
    match lh with
    | LH_base bef aft => LH_base (AI_const v :: bef) aft
    | LH_rec bef n es lh aft => LH_rec (AI_const v :: bef) n es lh aft
    | LH_prompt bef ts hs lh aft => LH_prompt (AI_const v :: bef) ts hs lh aft
    | LH_handler bef hs lh aft => LH_handler (AI_const v :: bef) hs lh aft
    end.

  Lemma lfilled_prepend i lh es v LI :
    lfilled i lh es LI -> lfilled i (lh_prepend lh v) es (AI_const v :: LI).
  Proof.
    destruct lh ; unfold lfilled, lfill ; fold lfill.
    1-2: destruct i => //.
    all: destruct (const_list l) eqn:Hl => //=.
    2-4: destruct (lfill _ _ _) eqn:Hfill => //.
    all: intros H; move/eqP in H; subst LI.
    all: rewrite const_const Hl //=.
  Qed.
  
  Lemma lfilled_vLI i lh e es v LI :
    lfilled i lh (e :: es) (AI_const v :: LI) ->
    (exists lh', lh_prepend lh' v = lh /\ lfilled i lh' (e :: es) LI) \/
      i = 0 /\ e = AI_const v /\ exists aft, lh = LH_base [] aft /\ es ++ aft = LI.
  Proof.
    intros Hfilled.
    destruct lh; 
      unfold lfilled, lfill in Hfilled ; fold lfill in Hfilled.
    1-2: destruct i => //.
    all: destruct (const_list l) eqn:Hl => //.
    2-4: destruct (lfill _ _ _) eqn:Hfill' => //.
    all: move/eqP in Hfilled.
    all: destruct l; try by destruct v; try destruct v; inversion Hfilled.
    { right. inversion Hfilled; subst. repeat split => //.
      eexists. split => //. }
    all: inversion Hfilled; subst.
    all: left.
    exists (LH_base l l0).
    2: eexists (LH_rec l n l0 lh l1).
    3: eexists (LH_handler l l0 lh l1).
    4: eexists (LH_prompt l l0 l1 lh l2).
    all: split => //.
    all: apply/lfilledP.
    all: simpl in Hl; remove_bools_options.
    all: constructor => //.
    all: apply/lfilledP; unfold lfilled; rewrite Hfill' => //. 
  Qed.

  Lemma lh_minus_Ind_Equivalent lh lh' lh'' :
    lh_minus lh lh' = Some lh'' <->
      lh_minus_Ind lh lh' lh''.
  Proof.
    revert lh lh''.
    induction lh';intros lh lh''.
    { rewrite lh_minus_LH_base.
      split; intros Hlh.
      + destruct l,l0 => //.
        inversion Hlh; subst lh''.
        constructor.
      + inversion Hlh; subst. done. } 
    all: split; intros Hlh.
    1,3,5: destruct lh; inversion Hlh.
    1-3: destruct (_ && _) eqn:Heq => //.
    1-3: remove_bools_options; subst.
    apply Nat.eqb_eq in H3; subst n0.
    1-3: constructor.
    1-3: by apply IHlh'.
    all: inversion Hlh; subst.
    all: simpl.
    all: repeat rewrite eq_refl.
    rewrite Nat.eqb_refl.
    all: simpl.
    all: by apply IHlh'.
  Qed.

  Lemma lh_delete_inner_eq lh :
    base_is_empty lh ->
    lh_delete_inner lh = lh.
  Proof.
    intros Hbase.
    induction lh.
    { inversion Hbase; subst; auto. }
    all: simpl in Hbase.
    all: apply IHlh in Hbase.
    all: unfold lh_delete_inner in Hbase.
    all: destruct (empty_base lh) as [[??]?] eqn:Hlh.
    all: simplify_eq.
    all: unfold lh_delete_inner.
    all: rewrite /= Hlh.
    all: auto. 
  Qed.

  Lemma base_is_empty_delete_inner lh :
    base_is_empty (lh_delete_inner lh).
  Proof.
    induction lh.
    { simpl. auto. }
    all: unfold lh_delete_inner.
    all: destruct (empty_base _) as [[??]?] eqn:Hl.
    all: inversion Hl.
    all: destruct (empty_base lh) as [[??]?] eqn:Hlh.
    all: simplify_eq.
    all: simpl.
    all: unfold lh_delete_inner in IHlh.
    all: rewrite Hlh in IHlh.
    all: auto. 
  Qed.

  Lemma lh_minus_eq lh :
    lh_minus lh (LH_base [] []) = Some lh.
  Proof.
    induction lh;simpl;auto.
  Qed.
  
  Lemma get_layer_lh_minus lh i vs' n es lh' es' :
    get_layer lh i = Some (vs', n, es, lh', es') ->
    ∃ lh'', lh_minus lh lh'' = Some lh'.
  Proof.
    revert i vs' n es lh' es'.
    induction lh;intros i vs' m es lh' es' Hl;[done| | |].
    - destruct i.  
      + inversion Hl;simplify_eq.
        exists (LH_rec vs' m es (LH_base [] []) es'). simpl.
        cbn. rewrite !eqseqE !eq_refl PeanoNat.Nat.eqb_refl.
        cbn.
        apply lh_minus_eq. 
      + inversion Hl.
        apply IHlh in H0. destruct H0 as [hl'' Hlh''].
        exists (LH_rec l n l0 hl'' l1).
        simpl. rewrite Hlh''.
        cbn.
        rewrite !eqseqE !eq_refl PeanoNat.Nat.eqb_refl.
        cbn. auto.
    - simpl. simpl in Hl.
      apply IHlh in Hl as [lh'' Hlh''].
      exists (LH_handler l l0 lh'' l1).
      repeat rewrite eq_refl.
      done.
    - apply IHlh in Hl as [lh'' Hlh''].
      exists (LH_prompt l l0 l1 lh'' l2).
      simpl. repeat rewrite eq_refl. done.
  Qed.

  Lemma LH_rec_circular vs' m es lh es' :
    LH_rec vs' m es lh es' = lh -> False.
  Proof.
    revert vs' m es es'.
    induction lh;intros vs' m es es' Hcontr;[done| | done | done].
    inversion Hcontr;subst.
    apply IHlh in H3. auto.
  Qed.

  Lemma lminus_base_inv lh lh' :
    lh_minus_Ind lh lh' lh ->
    lh' = LH_base [] [].
  Proof.
    intros Hlh.
    inversion Hlh;auto.
    all: exfalso.
    all: simplify_eq.
    all: apply lh_minus_Ind_Equivalent in H.
    all: apply lh_minus_true_depth in H.
    all: simpl in H.
    all: lia.
  Qed.
  
  Lemma lminus_rec_inv vs' m es lh es' lh'' :
    lh_minus (LH_rec vs' m es lh es') lh'' = Some lh ->
    lh'' = LH_rec vs' m es (LH_base [] []) es'.
  Proof.
    intros Hmin%lh_minus_Ind_Equivalent.
    inversion Hmin;subst.
    exfalso. eapply LH_rec_circular. eauto.
    f_equiv. eapply lminus_base_inv;eauto.
  Qed.

  Lemma get_layer_depth i lh x :
    get_layer lh i = Some x ->
    i < lh_depth lh.
  Proof.
    revert i x;induction lh;intros i x Hlayer; first done.
    - destruct x,p,p,p.
      cbn in Hlayer.
      destruct i;simplify_eq.
      + simpl. lia. 
      + apply IHlh in Hlayer.
        simpl. lia.
    - by eapply IHlh.
    - by eapply IHlh. 
  Qed.

  Lemma get_layer_depth_lt i lh vs' n es lh' es' :
    get_layer lh i = Some (vs',n,es,lh',es') ->
    lh_depth lh' < lh_depth lh.
  Proof.
    revert i vs' n es lh' es';induction lh;intros i vs' m es lh' es' Hlayer; first done.
    2-3: by eapply IHlh.
    cbn in Hlayer.
    destruct i;simplify_eq.
    { simpl. lia. }
    { apply IHlh in Hlayer.
      simpl. lia. }
  Qed.

  Lemma get_layer_circular lh i vs' m es es' :
    get_layer lh i = Some (vs', m, es, lh, es') ->
    False.
  Proof.
    assert (forall lh lh' i vs' m es es',
               lh_true_depth lh <= lh_true_depth lh' ->
               get_layer lh i = Some (vs', m, es, lh', es') ->
               False).
    2:{ apply H. lias. }
    clear.
    induction lh;intros lh' i vs' m es es' Hlh Hlayer => //.
    destruct i => //.
    { simpl in Hlayer. simplify_eq.
      simpl in Hlh. lias. }
    all: apply IHlh in Hlayer => //.
    all: simpl in Hlh.
    all: lias.
  Qed.

  (* Is this lemma even true with Handler and Prompt? *)
  (*
  Lemma get_layer_find i lh' :
    S i < (lh_depth lh') ->
    ∃ vs0' n0 es0 vs' n es lh es' es0' lh'',
      get_layer lh' (lh_depth lh' - (S (S i))) = Some (vs0', n0, es0, (LH_rec vs' n es lh es'), es0') ∧
        lh_minus lh' lh'' = Some (LH_rec vs' n es lh es') ∧ lh_depth lh = i.
  Proof.
    revert i.
    induction lh';intros i Hlt.
    - simpl in Hlt. lia. 
    - simpl in Hlt.
      destruct lh'; first by simpl in Hlt; lia.
      + simpl in Hlt. destruct lh'.
        * simpl in Hlt. destruct i;[|lia]. simpl.
          do 9 eexists.
          eexists (LH_rec l n l0 (LH_base [] []) l1).
          split;eauto.
          rewrite !eq_refl PeanoNat.Nat.eqb_refl.
          cbn. auto. 
        * simpl. simpl in Hlt.
          destruct (decide (i = S (lh_depth lh'))).
          -- subst i.
             rewrite PeanoNat.Nat.sub_diag.
             clear IHlh'.
             do 9 eexists.
             eexists (LH_rec l n l0 (LH_base [] []) l1).
             split;eauto.
             rewrite !eq_refl PeanoNat.Nat.eqb_refl.
             cbn. auto. 
          -- assert (S i < S (S (lh_depth lh'))) as Hlt';[lia|].
             apply IHlh' in Hlt'.
             destruct Hlt' as [vs0' [n3 [es0 [vs' [m [es [lh [es' [es0' [lh'' [Heq Hmin]]]]]]]]]]].
             simpl in Heq.
             destruct (lh_depth lh' - i) eqn:Hi1.
             ++ rewrite Nat.sub_succ_l;[|lia]. rewrite Hi1.
                do 9 eexists.
                eexists (LH_rec l n l0 lh'' l1).
                split;[eauto|].
                rewrite !eq_refl PeanoNat.Nat.eqb_refl. cbn.
                auto. 
             ++ rewrite Nat.sub_succ_l;[|lia]. rewrite Hi1.
                destruct n4.
                ** inversion Heq;subst. do 9 eexists.
                   eexists (LH_rec l n l0 lh'' l1).
                   split;eauto.
                   rewrite !eq_refl !PeanoNat.Nat.eqb_refl.
                   cbn. auto. 
                ** do 9 eexists.
                   eexists (LH_rec l n l0 lh'' l1).
                   split;eauto.
                   rewrite !eq_refl !PeanoNat.Nat.eqb_refl.
                   cbn. auto. 
        * simpl. simpl in Hlt. simpl in IHlh'.
          destruct (decide (i = lh_depth lh')).
          -- subst i.
             rewrite PeanoNat.Nat.sub_diag.
             do 9 eexists.
             eexists (LH_rec l n l0 (LH_handler l5 l6 lh' l7) l1).
             split;eauto.
             rewrite !eq_refl PeanoNat.Nat.eqb_refl.
             cbn. auto. 
          -- assert (S i < S (S (lh_depth lh'))) as Hlt';[lia|].
             apply IHlh' in Hlt'.
             destruct Hlt' as [vs0' [n3 [es0 [vs' [m [es [lh [es' [es0' [lh'' [Heq Hmin]]]]]]]]]]].
             simpl in Heq.
             destruct (lh_depth lh' - i) eqn:Hi1.
             ++ rewrite Nat.sub_succ_l;[|lia]. rewrite Hi1.
                do 9 eexists.
                eexists (LH_rec l n l0 lh'' l1).
                split;[eauto|].
                rewrite !eq_refl PeanoNat.Nat.eqb_refl. cbn.
                auto. 
             ++ rewrite Nat.sub_succ_l;[|lia]. rewrite Hi1.
                destruct n4.
                ** inversion Heq;subst. do 9 eexists.
                   eexists (LH_rec l n l0 lh'' l1).
                   split;eauto.
                   rewrite !eq_refl !PeanoNat.Nat.eqb_refl.
                   cbn. auto. 
                ** do 9 eexists.
                   eexists (LH_rec l n l0 lh'' l1).
                   split;eauto.
                   rewrite !eq_refl !PeanoNat.Nat.eqb_refl.
                   cbn. auto. 

          Check Hlt.
          apply IHlh'1. in Hlt.
  Qed. *)
  
  Lemma lfilled_minus lh' i vs' n es lh es' e LI j lh'' :
    lh_minus lh' lh'' = Some lh ->
    i < lh_depth lh' ->
    get_layer lh' (lh_depth lh' - S i) = Some (vs', n, es, lh, es') ->
    lfilled j lh' e LI ->
    ∃ LI', lfilled i lh e LI' ∧ lfilled (j - i) lh'' LI' LI.
  Proof.
    intros Hlh%lh_minus_Ind_Equivalent.
    revert vs' n es es' i j e LI.
    induction Hlh;intros vs' m es2 es2' i j e LI Hle Hlayer Hfill.
    - apply get_layer_circular in Hlayer. done. 
    - simpl in *.
      destruct (lh_depth lh - i) eqn:Hi.
      + simplify_eq.
        assert (lh_depth lh'' = i);[lia|simplify_eq].
        apply lfilled_depth in Hfill as Heq. simpl in *;subst.
        apply lfilled_Ind_Equivalent in Hfill.
        inversion Hfill;simplify_eq.
        apply lfilled_Ind_Equivalent in H8.
        eexists. split;eauto.
        apply lfilled_Ind_Equivalent.
        assert (S (lh_depth lh'') - (lh_depth lh'') = S 0) as ->;[lia|].
        constructor;auto.
        apply lminus_base_inv in Hlh as ->.
        apply lfilled_Ind_Equivalent. cbn.
        erewrite app_nil_r. by apply/eqP.
      + assert (lh_depth lh - S i = n0);[lia|simplify_eq].
        apply lfilled_Ind_Equivalent in Hfill.
        inversion Hfill;simplify_eq.
        apply lfilled_Ind_Equivalent in H8.
        eapply IHHlh in Hlayer as HLI';[|lia|eauto].
        destruct HLI' as [LI' [Hfill1 Hfill2]].
        assert (i <= k) as Hlei.
        { apply lh_minus_Ind_Equivalent in Hlh.
          apply lh_minus_depth in Hlh as Hd.
          apply lfilled_depth in Hfill1 as Hieq.
          apply lfilled_depth in Hfill2 as Hkeq.
          rewrite Hieq in Hd.
          rewrite Hkeq in Hd.
          simpl in *. lia. }
        exists LI'.
        split;auto. rewrite Nat.sub_succ_l;auto.
        apply lfilled_Ind_Equivalent. constructor;auto.
        apply lfilled_Ind_Equivalent. auto.
    - simpl in *.
      move/lfilledP in Hfill.
      inversion Hfill; subst.
      move/lfilledP in H8.
      eapply IHHlh in Hle as (LI' & HLI' & HLI).
      2: exact Hlayer.
      2: exact H8.
      exists LI'. split => //.
      apply/lfilledP. constructor => //. apply/lfilledP => //. 

    - simpl in *.
      move/lfilledP in Hfill.
      inversion Hfill; subst.
      move/lfilledP in H7.
      eapply IHHlh in Hle as (LI' & HLI' & HLI).
      2: exact Hlayer.
      2: exact H7.
      exists LI'. split => //.
      apply/lfilledP. constructor => //. apply/lfilledP => //. 

  Qed.

  Lemma lfilled_split i j lh e LI :
    i <= j ->
    lfilled j lh e LI ->
    ∃ lh' lh'' LI',
      lfilled i lh' e LI' ∧ lfilled (j - i) lh'' LI' LI.
  Proof.
    revert i j e LI.
    induction lh;intros i j e LI Hle Hfill%lfilled_Ind_Equivalent.
    all: inversion Hfill; simplify_eq.
    - destruct i;[|lia].
      simpl.
      eexists; eexists; eexists.
      split.
      + apply lfilled_Ind_Equivalent.
        constructor. eauto. 
      + instantiate (2:=LH_base [] []). cbn. apply/eqP.
        rewrite app_nil_r. eauto. 
    - destruct (decide (i = S k)).
      + simplify_eq. rewrite PeanoNat.Nat.sub_diag.
        eexists; eexists; eexists.
        split.
        * apply lfilled_Ind_Equivalent.
          constructor;eauto. 
        * instantiate (4:=LH_base [] []). cbn. apply/eqP.
          rewrite app_nil_r. eauto. 
      + assert (i <= k) as Hle';[lia|].
        apply lfilled_Ind_Equivalent in H8.
        eapply IHlh in Hle' as Hres;eauto.
        destruct Hres as [lh2 [lh'' [LI' [Hfill1 Hfill2]]]].
        repeat eexists;eauto.
        apply lfilled_Ind_Equivalent.
        rewrite Nat.sub_succ_l;eauto.
        constructor;auto. apply lfilled_Ind_Equivalent.
        eauto.
    - eapply IHlh in Hle as (lh2 & lh'' & LI' & Hfill1 & Hfill2).
      2:{ apply/lfilledP. exact H7. }
      repeat eexists.
      exact Hfill1.
      instantiate (1 := LH_handler _ _ _ _).
      apply/lfilledP.
      constructor => //.
      apply/lfilledP.
      exact Hfill2.
    - eapply IHlh in Hle as (lh2 & lh'' & LI' & Hfill1 & Hfill2).
      2:{ apply/lfilledP. exact H8. }
      repeat eexists.
      exact Hfill1.
      instantiate (1 := LH_prompt _ _ _ _ _).
      apply/lfilledP.
      constructor => //.
      apply/lfilledP.
      exact Hfill2.
  Qed.

  Lemma lfilled_to_sfill i lh es LI :
    lfilled i lh es LI ->
    ∃ sh, LI = sfill sh es.
  Proof.
    revert i es LI.
    induction lh;intros i es LI Hfill%lfilled_Ind_Equivalent.
    - inversion Hfill;simplify_eq.
      apply const_es_exists in H4 as [vs Hvs].
      exists (SH_base vs l0);rewrite Hvs;simpl;auto. 
    - inversion Hfill;simplify_eq.
      apply lfilled_Ind_Equivalent in H8.
      apply IHlh in H8 as [sh Hsh]. simplify_eq.
      apply const_es_exists in H7 as [vs Hvs].
      exists (SH_rec vs n l0 sh l1).
      rewrite Hvs;simpl;auto.
    - inversion Hfill; simplify_eq.
      move/lfilledP in H7.
      apply IHlh in H7 as [sh Hsh]. simplify_eq.
      apply const_es_exists in H6 as [vs ->].
      exists (SH_handler vs l0 sh l1).
      done.
    - inversion Hfill; simplify_eq.
      move/lfilledP in H8.
      apply IHlh in H8 as [sh Hsh]. simplify_eq.
      apply const_es_exists in H7 as [vs ->].
      exists (SH_prompt vs l0 l1 sh l2).
      done.
  Qed.

  Lemma sfill_sh_pull_const_r sh :
    ∀ e x, sfill (sh_pull_const_r sh x) e = sfill sh (v_to_e_list x ++ e).
  Proof.
    induction sh;intros e x.
    { cbn. rewrite -to_e_list_fmap. rewrite !fmap_app.
      repeat rewrite app_assoc. repeat f_equiv. }
    all: cbn.
    all: rewrite IHsh.
    all: auto. 
  Qed.

  Lemma const_list_app v1 v2 :
    const_list (v1 ++ v2) <-> const_list v1 ∧ const_list v2.
  Proof.
    split; intros; [ by apply const_list_split | apply const_list_concat; by inversion H ].
  Qed.
  
  Lemma lh_pull_const_r_app i lh x es es1 :
    lfilled i lh (v_to_e_list x ++ es) es1 ->
    ∃ lh', lfilled i lh' es es1.
  Proof.
    revert i es1.
    induction lh;intros i es1 Hfill%lfilled_Ind_Equivalent.
    { inversion Hfill;simplify_eq.
      exists (LH_base (l ++ (v_to_e_list) x) l0).
      apply lfilled_Ind_Equivalent. repeat erewrite app_assoc.
      erewrite <- (app_assoc _ _ l0). constructor.
      apply const_list_app. split;auto. apply v_to_e_is_const_list. }
    all: inversion Hfill;simplify_eq.
    all: try apply lfilled_Ind_Equivalent in H8.
    all: try apply lfilled_Ind_Equivalent in H7.
    all: try apply IHlh in H8 as [lh' Hlh'%lfilled_Ind_Equivalent].
    all: try apply IHlh in H7 as [lh' Hlh'%lfilled_Ind_Equivalent].
    all: eexists.
    all: apply lfilled_Ind_Equivalent.
    all: constructor;eauto. 
  Qed.

  Lemma lfilled_flatten i lh e LI l1 n es l2 :
    lfilled (S i) (LH_rec l1 n es lh l2) e LI ->
    ∃ LI', lfilled i lh e LI' ∧ lfilled 1 (LH_rec l1 n es (LH_base [] []) l2) LI' LI.
  Proof.
    intros Hfill.
    move/lfilledP in Hfill.
    inversion Hfill; subst.
    exists LI0. split; apply/lfilledP => //.
    constructor => //.
    apply/lfilledP. unfold lfilled, lfill => //=.
    by rewrite app_nil_r.
  Qed.

      
  Lemma hfilled_forget_avoiding x h es LI :
    hfilled x h es LI -> hfilled No_var h es LI.
  Proof.
    intros H.
    move/hfilledP in H.
    induction H.
    all: apply/hfilledP.
    all: constructor => //.
    all: by apply/hfilledP.
  Qed. 



Fixpoint constant_hholed hh :=
  match hh with
  | HH_base bef _ => const_list bef
  | HH_label bef _ _ hh _ => const_list bef && constant_hholed hh
  | HH_local bef _ _ hh _ => const_list bef && constant_hholed hh
  | HH_prompt bef _ _ hh _ => const_list bef && constant_hholed hh 
  | HH_handler bef _ hh _ => const_list bef && constant_hholed hh
  end.

Lemma fillable_constant_hholed hh es :
  constant_hholed hh -> exists LI, hfilled No_var hh es LI.
Proof.
  induction hh.
  { intros Hl. eexists. apply/hfilledP. 
    constructor. exact Hl. } 
  all: intros H.
  all: simpl in H. 
  all: remove_bools_options.
  all: apply IHhh in H0 as [LI HLI].
  all: eexists.
  all: apply/hfilledP.
  all: constructor.
  all: try done.
  all: apply/hfilledP.
  all: done.
Qed. 


  
End lfilled_properties.
