From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import tactics.
From iris.base_logic Require Export gen_heap proph_map.
Require Export iris iris_locations.
From Wasm.iris.helpers Require Export iris_properties.
From Wasm Require Export datatypes operations properties opsem.

Set Bullet Behavior "Strict Subproofs".

Local Definition reducible := @reducible wasm_lang.

Local Definition expr := iris.expr.
Local Definition val := iris.val.
Local Definition to_val := iris.to_val.


(* The following atomicity definition will be useful for opening invariants *)
Definition is_atomic (e : expr) : Prop :=
  match e with
  | [::AI_basic (BI_const (VAL_int32 _)); AI_basic (BI_load _ _ _ _)] => True
  | [::AI_basic (BI_const (VAL_int32 _)); v; AI_basic (BI_store _ _ _ _)] => is_const v
  | [::v; AI_basic (BI_set_global _)] => is_const v
  | [::AI_basic (BI_get_global _)] => True
  | [::AI_trap] => True
  | _ => False
  end.

Ltac destruct_match_goal :=
  let x := fresh "x" in 
  match goal with
                | _ : _ |- (match ?x with | _ => _ end -> _) => case: x => x //=
  end.
Lemma is_atomic_eq (e : expr) :
  is_atomic e ->
  (∃ k x1 x2 x3 x4, e = [::AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load x1 x2 x3 x4)]) ∨
  (∃ k v x1 x2 x3 x4, e = [::AI_basic (BI_const (VAL_int32 k)); AI_const v; AI_basic (BI_store x1 x2 x3 x4)]) ∨
  (∃ v g, e = [::AI_const v; AI_basic (BI_set_global g)]) ∨
  (∃ g, e = [::AI_basic (BI_get_global g)]) ∨
  (e = [::AI_trap]).
Proof.
  intros He.
  do 2 (destruct e;try done).
  - destruct a;try done.
    + destruct b;try done.
      * right. right. right. left. eauto.
      * destruct v;try done.
    + right. right. right. by right. 
  - do 1 (destruct e;try done).
    + revert He. cbn.
      destruct a => //=.
      destruct b => //=.
      all: destruct a0 => //=.
      all: try destruct b => //=.
      all: try destruct v => //=.
      all: try destruct b0 => //=.
      all: intros _.
      5: left; repeat eexists.
      all: right; right; left; eexists _,_.
      1-4: instantiate (2 := VAL_num _) => //.
      all: instantiate (2 := VAL_ref _) => //=.
      instantiate (2 := VAL_ref_null _) => //.
      instantiate (2 := VAL_ref_func _) => //.
      instantiate (2 := VAL_ref_exn _ _) => //.
      instantiate (2 := VAL_ref_cont _) => //.
    + destruct e.
      2: { exfalso. cbn in He. revert He.
           repeat destruct_match_goal. all: try destruct a0 => //.
           all: try destruct b => //.
           all: try destruct a1 => //.
           all: try destruct b => //. 
      }
      revert He. cbn. repeat destruct_match_goal.
      all: try destruct a0 => //.
      all: try destruct b => //.
      all: try destruct a1 => //.
      all: try destruct b => //.
      all: try destruct b0 => //. 
      all: move => *.
      all: right;left.
      all: repeat eexists.
      all: try by instantiate (5 := VAL_num _).
      all: instantiate (5 := VAL_ref _).
      all: try by instantiate (5 := VAL_ref_null _).
      all: try by instantiate (5 := VAL_ref_func _).
      all: try by instantiate (5 := VAL_ref_cont _).
      all: try by instantiate (5 := VAL_ref_exn _ _).
Qed.

Lemma atomic_no_hole_load s0 f es s' f' es' k lh k0 x0 x1 x2 x3 :
  reduce s0 f es s' f' es' -> 
  lfilled k lh es [::AI_basic (BI_const (VAL_int32 k0)); AI_basic (BI_load x0 x1 x2 x3)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.  
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  inversion Hfill; subst.
  all: try by repeat destruct vs => //.
  all: try by repeat destruct bef => //. 

  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 2 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
  - inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. 
  - inversion H;subst. exfalso.
     clear -Hred.
  lazymatch goal with
  | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
  end.
  exfalso. 
  induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
        first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
        try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by do 4 destruct vs => //);
          do 4 destruct bef => //
        | move/lfilledP in H02; inversion H02; subst;
          try (by do 4 destruct vs => //);
          try (by do 4 destruct bef => //);
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
              inversion H3; subst;
              destruct es => //; apply IHHred => //
              )
        ].
  inversion H3; subst => //.
Qed.
    
Lemma atomic_no_hole_store s0 f es s' f' es' k lh k0 v x0 x1 x2 x3 :
  reduce s0 f es s' f' es' -> 
  lfilled k lh es [::AI_basic (BI_const (VAL_int32 k0)); AI_const v; AI_basic (BI_store x0 x1 x2 x3)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  inversion Hfill; subst.
  all: try by destruct v; destruct v; repeat destruct vs => //.
  all: try by destruct v; destruct v; repeat destruct bef => //. 
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 3 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
  - inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. eauto. 
  - inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. destruct v; destruct v => //.  
  - inversion H;subst. exfalso.
         clear -Hred.
  lazymatch goal with
  | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
  end.
  exfalso. 
  induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
        first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
    try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves)  ;
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by destruct v; destruct v; do 4 destruct vs => //);
          destruct v; destruct v; do 4 destruct bef => //
        | move/lfilledP in H02; inversion H02; subst;
          try (by destruct v; destruct v; do 4 destruct vs => //);
          try (by destruct v; destruct v; do 4 destruct bef => //);
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred; try rewrite /= const_const);
              inversion H3; subst;
              destruct es => //; apply IHHred => //
              )
        ].
  inversion H3; subst => //.
  destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
  destruct es; first empty_list_no_reduce.
  destruct es => //.
  inversion H2; subst.
       clear -Hred.
  lazymatch goal with
  | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
  end.
  exfalso. 
  induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
        first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
        try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by do 4 destruct vs => //);
          do 4 destruct bef => //
        | move/lfilledP in H02; inversion H02; subst;
          try (by do 4 destruct vs => //);
          try (by do 4 destruct bef => //);
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
              inversion H3; subst;
              destruct es => //; apply IHHred => //
              )
        ].
  inversion H3; subst => //.
  - inversion H;subst. exfalso.
           clear -Hred.
  lazymatch goal with
  | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
  end.
  exfalso. 
  induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
        first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
        try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by do 4 destruct vs => //);
          do 4 destruct bef => //
        | move/lfilledP in H02; inversion H02; subst;
          try (by do 4 destruct vs => //);
          try (by do 4 destruct bef => //);
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
              inversion H3; subst;
              destruct es => //; apply IHHred => //
              )
        ].
  inversion H3; subst => //.
  - inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. destruct v; destruct v => //. 
Qed.

Lemma atomic_no_hole_trap s0 f es s' f' es' k lh :
  reduce s0 f es s' f' es' -> 
  lfilled k lh es [::AI_trap] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  inversion Hfill; subst.
  all: try by repeat destruct vs => //.
  all: try by repeat destruct bef => //.
  destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
  destruct es; first empty_list_no_reduce.
  destruct es => //.
  inversion H; subst.
  exfalso.
  eapply AI_trap_irreducible => //. 
Qed.

Lemma reduce_set_global_false s0 f s' f' es es' g :
  es = [AI_basic (BI_set_global g)] ->
  reduce s0 f es s' f' es' -> False.
Proof.
  intros Heq Hred.
  subst.
          clear -Hred.
  lazymatch goal with
  | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
  end.
  exfalso. 
  induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
        first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
        try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by do 4 destruct vs => //);
          do 4 destruct bef => //
        | move/lfilledP in H02; inversion H02; subst;
          try (by do 4 destruct vs => //);
          try (by do 4 destruct bef => //);
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
              inversion H3; subst;
              destruct es => //; apply IHHred => //
              )
        ].
  inversion H3; subst => //.
Qed.

Lemma atomic_no_hole_set_global s0 f es s' f' es' k lh v g :
  reduce s0 f es s' f' es' ->
  lfilled k lh es [::AI_const v; AI_basic (BI_set_global g)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  inversion Hfill; subst.
  all: try by destruct v; destruct v; repeat destruct vs => //.
  all: try by destruct v; destruct v; repeat destruct bef => //.
  pose proof (reduce_not_nil Hred) as Hnil.
  destruct vs,es,es'0 => //=.
  all: do 3 (try destruct vs; try destruct es; try destruct es'0 => //=;simplify_eq).
  - inversion H;subst. exfalso.
    eapply reduce_val_false;eauto. destruct v; destruct v => //. 
  - inversion H;subst. exfalso.
         clear -Hred.
  lazymatch goal with
  | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
  end.
  exfalso. 
  induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
        first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
        try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by do 4 destruct vs => //);
          do 4 destruct bef => //
        | move/lfilledP in H02; inversion H02; subst;
          try (by do 4 destruct vs => //);
          try (by do 4 destruct bef => //);
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
              inversion H3; subst;
              destruct es => //; apply IHHred => //
              )
        ].
  inversion H3; subst => //.
Qed.

Lemma atomic_no_hole_get_global s0 f es s' f' es' k lh g:
  reduce s0 f es s' f' es' -> 
  lfilled k lh es [::AI_basic (BI_get_global g)] ->
  lh = LH_base [] [] ∧ k = 0.
Proof.
  intros Hred Hfill.
  apply lfilled_Ind_Equivalent in Hfill.
  inversion Hfill; subst.
  all: try by repeat destruct vs => //.
  all: try by repeat destruct bef => //.
  destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
  destruct es; first empty_list_no_reduce.
  destruct es => //.
  inversion H; subst.
  done.
Qed. 

  

Global Instance is_atomic_correct s e : is_atomic e → @Atomic wasm_lang s e.
Proof.
  intros Ha; apply strongly_atomic_atomic.
  move => σ e' K σ' e'' /= Hstep.
  unfold iris.prim_step in Hstep.
  destruct σ as [[[hs ws] locs] inst].
  destruct σ' as [[[hs' ws'] locs'] inst'].
  destruct Hstep as [Hstep [-> ->]].
  induction Hstep using reduce_ind.
  all: apply is_atomic_eq in Ha as Heq.
  all: destruct Heq as [(?&?&?&?&?&?)|[(?&?&?&?&?&?&?)|[(?&?&?)|[(?&?)|?]]]];simplify_eq; eauto.
  all: try by (do 2 (destruct vcs;try done)).
  all: try by (do 4 (destruct vcs;try done)).
  all: try by (do 4 (destruct vs; try done)).
  - inversion H;subst;eauto.
    1,2: do 3 (destruct vs;try done). 
  - inversion H;subst;eauto.
    1,2: do 4 (destruct vs;try done). 
  - inversion H;subst;eauto.
    1,2: do 4 (destruct vs;try done). 
  - inversion H;subst;eauto.
    1,2: do 4 (destruct vs;try done). 
  - inversion H;simpl;eauto; subst; exfalso.
    + do 2 (destruct vs;inversion H0;try done).
    + do 2 (destruct vs;inversion H0;try done). 
  - destruct v; destruct v => //. 
  - eapply atomic_no_hole_load in Hstep as HH;eauto.
    destruct HH as [Hlh Hk];eauto. subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. 
  - edestruct atomic_no_hole_store as [Hlh Hk];eauto.
    subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. 
  - edestruct atomic_no_hole_set_global as [Hlh Hk];eauto.
    subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. 
  - edestruct atomic_no_hole_get_global as [Hlh Hk];eauto.
    subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. 
  - edestruct atomic_no_hole_trap as [Hlh Hk];eauto.
    subst k. subst lh.
    apply lfilled_Ind_Equivalent in H.
    apply lfilled_Ind_Equivalent in H0.
    inversion H;inversion H0; subst. erewrite app_nil_r in H3. subst.
    erewrite app_nil_r. erewrite app_nil_l. apply IHHstep. auto. 
Qed.



Ltac solve_atomic :=
  apply is_atomic_correct; simpl; repeat split;
    rewrite ?to_of_val; eapply mk_is_Some; fast_done.

Global Hint Extern 0 (Atomic _ _) => solve_atomic : core.
Global Hint Extern 0 (Atomic _ _) => solve_atomic : typeclass_instances.
