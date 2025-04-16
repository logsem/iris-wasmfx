From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Set Bullet Behavior "Strict Subproofs".

Lemma throw_ref_null_det tf s f s' f' es:
  reduce s f [AI_basic (BI_ref_null tf); AI_basic BI_throw_ref] s' f' es ->
  reduce_det_goal s f [AI_trap] s' f' es [AI_basic (BI_ref_null tf); AI_basic BI_throw_ref]. 
Proof.
  move => Hred.
  only_one.
  inversion H3; subst.
    destruct vs; inversion H4; subst => //.
    destruct esnewest; first empty_list_no_reduce.
    inversion H1; subst.
    destruct esnewest => //. 
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


Lemma throw_ref_desugar_det vs a exn i s f s' f' es:
  nth_error (s_exns s) a = Some exn ->
  vs = e_fields exn ->
  reduce s f [AI_ref_exn a i; AI_basic BI_throw_ref] s' f' es ->
  reduce_det_goal s f [AI_throw_ref_desugared vs a i] s' f' es [AI_ref_exn a i; AI_basic BI_throw_ref]. 
Proof.
  move => Hexn -> Hred.
  only_one.
  inversion Heqesnew; subst.
  rewrite Hexn in H; inversion H; subst.
  by left.
  inversion H3; subst.
    destruct vs0; inversion H4; subst => //.
    destruct esnewest; first empty_list_no_reduce.
    inversion H1; subst.
    destruct esnewest => //. 
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

Lemma throw_ref_det i hh vs a LI l hs s f s' f' es':
  hfilled (Var_handler i) hh [AI_throw_ref_desugared vs a i] LI ->
  firstx_exception hs i = Clause_label l ->
  reduce s f [AI_handler hs LI] s' f' es' ->
  reduce_det_goal s f (v_to_e_list vs ++ [AI_basic (BI_br l)]) s' f' es' [AI_handler hs LI]. 
Proof.
  intros Hfill Hfirst Hred.
   lazymatch goal with
  | _ : reduce _ _ ?es _ _ _ |- _ => remember es as ves
  end.
  induction Hred.
  inversion H.
  all: remember Heqves as Heqves'; clear HeqHeqves' Heqves.
  all: subst.
  all: try by inversion Heqves'.
  all: try by do 4 destruct vs0 => //.
  all: try by do 4 destruct vcs => //.
  - inversion Heqves'; subst.
    apply hfilled_const in Hfill => //.
  - inversion Heqves'; subst.
    apply hfilled_singleton in Hfill as ( _ & ?) => //.
  - move/lfilledP in H1; inversion H1; subst.
    all: try by do 2 destruct vs0 => //.
    all: try by do 2 destruct bef => //.
    destruct bef; last by destruct bef.
    inversion H2; subst.
    move/lfilledP in H7.
    apply hfilled_to_llfill in Hfill as [llh Hllh].
    edestruct lfilled_llfill_first_values as (? & ?).
    instantiate (3 := []). exact H7. instantiate (2 := []). exact Hllh.
    all: try done.
  - inversion Heqves'; subst.
    edestruct hfilled_first_values as (? & ?).
    instantiate (3 := []).
    exact H.
    instantiate (2 := []).
    exact Hfill.
    all: try done.
    destruct H2 as [_ ->] => //.
    inversion H1; subst.
    rewrite H0 in Hfirst; inversion Hfirst; subst. by left.
  - inversion Heqves'; subst.
    edestruct hfilled_first_values as (? & ?).
    instantiate (3 := []).
    exact H.
    instantiate (2 := []).
    exact Hfill.
    all: try done.
    inversion H1; subst.
    rewrite H0 in Hfirst; inversion Hfirst; subst. 

  - move/lfilledP in H; inversion H; subst.
    all: try by do 2 destruct vs0 => //. 
    all: try by do 2 destruct bef => //. 
    all: move/lfilledP in H0; inversion H0; subst.
    + destruct vs0; last by destruct vs0, es => //; empty_list_no_reduce.
      destruct es; first empty_list_no_reduce.
      inversion H1; destruct es, es'0 => //.
      simpl in *. subst. rewrite cats0.
      apply IHHred => //.
    + destruct bef; last by destruct bef.
      inversion H1; subst.
      exfalso; eapply hfilled_throw_ref_and_reduce.
      exact Hred.
      exact Hfill.
      apply/lfilledP => //.
Qed. 


Lemma throw_ref_ref_det i hh vs a LI l hs s f s' f' es':
  hfilled (Var_handler i) hh [AI_throw_ref_desugared vs a i] LI ->
  firstx_exception hs i = Clause_label_ref l ->
  reduce s f [AI_handler hs LI] s' f' es' ->
  reduce_det_goal s f (v_to_e_list vs ++ [AI_ref_exn a i; AI_basic (BI_br l)]) s' f' es' [AI_handler hs LI]. 
Proof.
  intros Hfill Hfirst Hred.
   lazymatch goal with
  | _ : reduce _ _ ?es _ _ _ |- _ => remember es as ves
  end.
  induction Hred.
  inversion H.
  all: remember Heqves as Heqves'; clear HeqHeqves' Heqves.
  all: subst.
  all: try by inversion Heqves'.
  all: try by do 4 destruct vs0 => //.
  all: try by do 4 destruct vcs => //.
  - inversion Heqves'; subst.
    apply hfilled_const in Hfill => //.
  - inversion Heqves'; subst.
    apply hfilled_singleton in Hfill as ( _ & ?) => //.
  - move/lfilledP in H1; inversion H1; subst.
    all: try by do 2 destruct vs0 => //.
    all: try by do 2 destruct bef => //.
    destruct bef; last by destruct bef.
    inversion H2; subst.
    move/lfilledP in H7.
    apply hfilled_to_llfill in Hfill as [llh Hllh].
    edestruct lfilled_llfill_first_values as (? & ?).
    instantiate (3 := []). exact H7. instantiate (2 := []). exact Hllh.
    all: try done.
  - inversion Heqves'; subst.
    edestruct hfilled_first_values as (? & ?).
    instantiate (3 := []).
    exact H.
    instantiate (2 := []).
    exact Hfill.
    all: try done.
    inversion H1; subst.
    rewrite H0 in Hfirst; inversion Hfirst; subst. 
  - inversion Heqves'; subst.
    edestruct hfilled_first_values as (? & ?).
    instantiate (3 := []).
    exact H.
    instantiate (2 := []).
    exact Hfill.
    all: try done.
    destruct H2 as [_ ->] => //.
    inversion H1; subst.
    rewrite H0 in Hfirst; inversion Hfirst; subst. by left.


  - move/lfilledP in H; inversion H; subst.
    all: try by do 2 destruct vs0 => //. 
    all: try by do 2 destruct bef => //. 
    all: move/lfilledP in H0; inversion H0; subst.
    + destruct vs0; last by destruct vs0, es => //; empty_list_no_reduce.
      destruct es; first empty_list_no_reduce.
      inversion H1; destruct es, es'0 => //.
      simpl in *. subst. rewrite cats0.
      apply IHHred => //.
    + destruct bef; last by destruct bef.
      inversion H1; subst.
      exfalso; eapply hfilled_throw_ref_and_reduce.
      exact Hred.
      exact Hfill.
      apply/lfilledP => //.
Qed. 
