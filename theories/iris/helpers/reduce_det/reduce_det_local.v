From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude iris_split_reduce.

Set Bullet Behavior "Strict Subproofs".

Lemma local_det s f es s' f' es' ws2 n f0 f2 es2 nnn:
  (∀ (f f2 f1 : frame) (es2 es1 es : seq.seq administrative_instruction),
    reduce s f es s' f1 es1
    → reduce s f es ws2 f2 es2 → length_rec es < nnn → reduce_det_goal s' f1 es1 ws2 f2 es2 es) ->
  reduce s f es s' f' es' ->
  reduce s f0 [AI_local n f es] ws2 f2 es2 ->
  length_rec [AI_local n f es] < S nnn ->
  ((∀ (f f2 f1 : frame) (es2 es1 es : seq.seq administrative_instruction),
      reduce s f es s' f1 es1
      → reduce s f es ws2 f2 es2 → length_rec es < nnn → reduce_det_goal s' f1 es1 ws2 f2 es2 es)
   → reduce s f es ws2 f2 es2 → length_rec es < S nnn → reduce_det_goal s' f' es' ws2 f2 es2 es) ->
  reduce_det_goal s' f0 [AI_local n f' es'] ws2 f2 es2 [AI_local n f es].
Proof.
  move => IHnnn Hred1 Hred2 Hlen IHHred1.
  (* final case : the r_local case. We perform the case analysis on Hred2 by hand *)
  clear IHHred1. remember [AI_local n f es] as es0.
  rewrite <- (app_nil_l [AI_local n f es]) in Heqes0.
  induction Hred2 ; (try by inversion Heqes0) ;
    try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
  destruct H ; (try by inversion Heqes0) ;
    try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
  all: try by do 2 destruct vs => //.
  all: try by do 2 destruct ves => //. 
  - inversion Heqes0 ; subst. exfalso ; values_no_reduce.
  - inversion Heqes0 ; subst.
    exfalso; by eapply AI_trap_irreducible.
  - inversion Heqes0 ; subst.
    induction Hred1.
    inversion H0.
    all: subst.
    all: try by try destruct ref; move/lfilledP in H1; inversion H1; subst;
      lazymatch goal with
      | H : (_)%SEQ = [_;_] |- _ =>
          symmetry in H; try rewrite catA catA -catA in H;
          rewrite separate1 in H;
          apply first_values in H as (? & ? & ?);
          try apply const_list_concat;
          try rewrite /= const_const;
          try rewrite /= H2
      end.
    all: try by move/lfilledP in H1; inversion H1; subst;
      lazymatch goal with
      | H : (_)%SEQ = [_;_;_] |- _ =>
          symmetry in H; try rewrite catA catA -catA in H;
          rewrite separate2 in H;
          apply first_values in H as (? & ? & ?);
          try apply const_list_concat
      end.
    all: try by move/lfilledP in H1; inversion H1; subst;
      lazymatch goal with
      | H : (_)%SEQ = [?e] |- _ =>
          symmetry in H; try rewrite catA catA -catA in H;
          rewrite -(app_nil_l [e]) in H;
          apply first_values in H as (? & ? & ?);
          try apply const_list_concat
      end.
    all: try by move/lfilledP in H1; inversion H1; subst;
      lazymatch goal with
      | H : (_)%SEQ = (_ ++ [_])%SEQ |- _ =>
          symmetry in H; try rewrite catA catA -catA in H;
          apply first_values in H as (? & ? & ?);
          try apply const_list_concat;
          subst; try apply v_to_e_is_const_list
      end.
    all: try by move/lfilledP in H1; inversion H1; subst;
      lazymatch goal with
      | H : (_)%SEQ = (_ ++ [_;_])%SEQ |- _ =>
          symmetry in H; try rewrite catA catA -catA in H;
          rewrite separate1 -cat_app catA in H;
          apply first_values in H as (? & ? & ?);
          try apply const_list_concat;
          subst; try apply v_to_e_is_const_list
      end.
    all: try by move/lfilledP in H1; inversion H1; subst;
        try (by lazymatch goal with
      | H : (_)%SEQ = [?e] |- _ =>
          symmetry in H; try rewrite catA catA -catA in H;
          rewrite -(app_nil_l [e]) in H;
          apply first_values in H as (? & ? & ?);
          try apply const_list_concat
                  end);
      try (destruct bef; last (by destruct bef));
      try (destruct vs0; last (by destruct vs0));
      inversion H3; subst;
      move/lfilledP in H8;
      apply lfilled_const in H8 as [_ Habs] => //;
      apply const_list_split in Habs as [??] => //.
    all: try by move/lfilledP in H1; inversion H1; subst;
      try (by lazymatch goal with
      | H : (_)%SEQ = [?e] |- _ =>
          symmetry in H; try rewrite catA catA -catA in H;
          rewrite -(app_nil_l [e]) in H;
          apply first_values in H as (? & ? & ?);
          try apply const_list_concat
                  end);
      try (destruct bef; last (by destruct bef));
      try (destruct vs0; last (by destruct vs0));
      inversion H2; subst;
      move/lfilledP in H7;
      eapply filled_singleton in H7 as (_ & _ & Habs) => //;
                                                          do 2 destruct vs => //.
    all: try by move/lfilledP in H1; inversion H1; subst;
      lazymatch goal with
      | H : (_)%SEQ = [_;_;_;_] |- _ =>
          symmetry in H; try rewrite catA catA -catA in H;
          rewrite separate3 in H;
          apply first_values in H as (? & ? & ?);
          try apply const_list_concat;
          repeat rewrite /= const_const
      end.
    all: try by move/lfilledP in H1; inversion H1; subst;
      try (by lazymatch goal with
      | H : (_)%SEQ = [?e] |- _ =>
          symmetry in H; try rewrite catA catA -catA in H;
          rewrite -(app_nil_l [e]) in H;
          apply first_values in H as (? & ? & ?);
          try apply const_list_concat
              end);
      destruct bef; last (by destruct bef);
      inversion H3; subst;
      apply hfilled_to_llfill in H0 as [llh Hllh];
      edestruct lfilled_llfill_first_values as [??];
      try (apply/lfilledP; exact H8);
      try (instantiate (2 := []); exact Hllh).
     all: try by move/lfilledP in H1; inversion H1; subst;
      try (by lazymatch goal with
      | H : (_)%SEQ = [?e] |- _ =>
          symmetry in H; try rewrite catA catA -catA in H;
          rewrite -(app_nil_l [e]) in H;
          apply first_values in H as (? & ? & ?);
          try apply const_list_concat
              end);
      destruct bef; last (by destruct bef);
      inversion H0; subst;
      apply hfilled_to_llfill in H4 as [llh Hllh];
      edestruct lfilled_llfill_first_values as [??];
      try (apply/lfilledP; exact H9);
        try (instantiate (2 := []); exact Hllh). 
    + move/lfilledP in H1; inversion H1; subst;
      try (by lazymatch goal with
      | H : (_)%SEQ = [?e] |- _ =>
          symmetry in H; try rewrite catA catA -catA in H;
          rewrite -(app_nil_l [e]) in H;
          apply first_values in H as (? & ? & ?);
          try apply const_list_concat
              end).
      destruct vs1; last by destruct vs1.
      inversion H3; subst.
      edestruct lfilled_first_values as [??].
      exact H4. apply/lfilledP; exact H9. all: try done.
    + edestruct lfilled_first_values as [??].
      exact H1. instantiate (2 := []). exact H3. all: try done.
    + move/lfilledP in H1; inversion H1; subst;
      try (by lazymatch goal with
      | H : (_)%SEQ = [?e] |- _ =>
          symmetry in H; try rewrite catA catA -catA in H;
          rewrite -(app_nil_l [e]) in H;
          apply first_values in H as (? & ? & ?);
          try apply const_list_concat
              end);
      destruct bef; last (by destruct bef);
      inversion H2; subst.
      apply hfilled_to_llfill in H4 as [llh Hllh];
      edestruct lfilled_llfill_first_values as [??];
      try (apply/lfilledP; exact H10);
        try (instantiate (2 := []); exact Hllh).
      all: try done.
    + exfalso. eapply lfilled_return_and_reduce => //=.
  - rewrite Heqes0 in H0.
    move/lfilledP in H0; inversion H0.
    all: try by do 2 destruct vs => //.
    all: by do 2 destruct bef => //.
  - rewrite Heqes0 in H.
    move/lfilledP in H; inversion H; subst.
    all: try by do 2 destruct bef => //.
    all: try by do 2 destruct vs => //.
    destruct vs; last by destruct vs, es0 => //; empty_list_no_reduce.
    destruct es0; first by empty_list_no_reduce.
    inversion H1; subst.
    destruct es0, es'1 => //.
    move/lfilledP in H0; inversion H0; subst.
    simpl in *.
    rewrite cats0.
    apply IHHred2 => //. 
  - (* In case Hred2 was also proved using r_local, we make use of the induction
         hypothesis IHnnn *)
    inversion Heqes0 ; subst. clear IHHred2.
    assert (length_rec es < nnn).
    unfold length_rec in Hlen ; simpl in Hlen.
    unfold length_rec ; lia.
    destruct (IHnnn _ _ _ _ _ _ Hred1 Hred2 H)
      as [Hσ | [ [i Hstart] | (i1 & i2 & i3 & Hstart1 & Hstart2 & Hstart3 & Hσ) (* ] *)]].
    * left. by inversion Hσ ; subst.
    * right ; left. exists (i + 1). unfold first_instr => //=. unfold first_instr in Hstart.
      rewrite Hstart => //=. repeat f_equiv. lia.
    * repeat right. exists (i1 + 1),(i2 + 1),(i3 + 1). repeat split => //=.
      unfold first_instr => //= ; unfold first_instr in Hstart1 ;
                             rewrite Hstart1 => //=; repeat f_equiv; lia.
      unfold first_instr => //= ; unfold first_instr in Hstart2 ;
                             rewrite Hstart2 => //=; repeat f_equiv; lia.
      unfold first_instr => //= ; unfold first_instr in Hstart3 ;
                             rewrite Hstart3 => //=; repeat f_equiv; lia.
        by inversion Hσ ; subst.
Qed.
