From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Set Bullet Behavior "Strict Subproofs".

Lemma br_det es vs i lh LI s n f s' f' es':
  const_list vs ->
  n = length vs ->
  lfilled i lh (vs ++ [AI_basic (BI_br i)]) LI ->
  reduce s f [AI_label n es LI] s' f' es' ->
  reduce_det_strong_goal s f (vs ++ es) s' f' es'. 
Proof.
  intros Hvs Hn Hfill Hred.
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
    apply lfilled_const in Hfill as [_ ?] => //.
    apply const_list_split in H1 as [??] => //.
  - inversion Heqves'; subst.
    apply filled_singleton in Hfill as (_ & _ & ?) => //.
    all: do 2 destruct vs => //.
  - inversion Heqves'; subst.
    edestruct lfilled_first_values as (? & ? & ?).
    exact H2. exact Hfill.
    all: try done.
    destruct H5 as [-> ->] => //.
  - move/lfilledP in H1; inversion H1; subst.
    all: try by do 2 destruct vs0 => //.
    all: try by do 2 destruct bef => //.
  - move/lfilledP in H; inversion H; subst.
    all: try by do 2 destruct bef => //. 
    all: move/lfilledP in H0; inversion H0; subst.
    + destruct vs0; last by destruct vs0, es0 => //; empty_list_no_reduce.
      destruct es0; first empty_list_no_reduce.
      inversion H1; destruct es0, es'0 => //.
      simpl in *. subst. rewrite cats0.
      apply IHHred => //.
    + destruct vs0; last by destruct vs0.
      inversion H1; subst.
      exfalso; eapply lfilled_br_and_reduce.
      exact Hred.
      3: exact Hfill.
      done. done. apply/lfilledP => //.
Qed. 


Lemma br_if_false_det n i s f s' f' es:
  n = Wasm_int.int_zero i32m ->
  reduce s f [AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] s' f' es ->
  reduce_det_strong_goal s f [] s' f' es. 
Proof.
  move => -> Hred.
  (* example of a usage of [ only_one ] : in this subgoal, we know that Hred2 is
         the hypothesis [ [AI_basic (BI_const v) ; AI_basic (BI_unop t op) ] -> es2 ].
         [ only_one ] selects the left disjunct in the conclusion, meaning we wish
         to show that in this case, there was indeed determinism. Then it performs a 
         case analysis on Hred2. Most cases have a left-hand-side very different from
         [AI_basic (BI_const v) ; AI_basic (BI_unop t op)] and can thus be exfalsoed.
         Some cases, like the r_label case, require a little more effort, but the tactic
         can handle most difficulties. See the next comment for an example of when 
         [ only_one ] cannot exfalso all irrelevant cases *)
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



Lemma br_if_true_det n i s f s' f' es:
  n <> Wasm_int.int_zero i32m ->
  reduce s f [AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] s' f' es ->
  reduce_det_strong_goal s f [AI_basic (BI_br i)] s' f' es.
Proof.
  move => Hn Hred.
  (* example of a usage of [ only_one ] : in this subgoal, we know that Hred2 is
         the hypothesis [ [AI_basic (BI_const v) ; AI_basic (BI_unop t op) ] -> es2 ].
         [ only_one ] selects the left disjunct in the conclusion, meaning we wish
         to show that in this case, there was indeed determinism. Then it performs a 
         case analysis on Hred2. Most cases have a left-hand-side very different from
         [AI_basic (BI_const v) ; AI_basic (BI_unop t op)] and can thus be exfalsoed.
         Some cases, like the r_label case, require a little more effort, but the tactic
         can handle most difficulties. See the next comment for an example of when 
         [ only_one ] cannot exfalso all irrelevant cases *)
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


Lemma br_if_table_det c iss i j s f s' f' es:
  ssrnat.leq (S (Wasm_int.nat_of_uint i32m c)) (length iss) -> 
  nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
  reduce s f [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] s' f' es ->
  reduce_det_strong_goal s f [AI_basic (BI_br j)] s' f' es.
Proof.
  move => Hlim Hj Hred.
  (* example of a usage of [ only_one ] : in this subgoal, we know that Hred2 is
         the hypothesis [ [AI_basic (BI_const v) ; AI_basic (BI_unop t op) ] -> es2 ].
         [ only_one ] selects the left disjunct in the conclusion, meaning we wish
         to show that in this case, there was indeed determinism. Then it performs a 
         case analysis on Hred2. Most cases have a left-hand-side very different from
         [AI_basic (BI_const v) ; AI_basic (BI_unop t op)] and can thus be exfalsoed.
         Some cases, like the r_label case, require a little more effort, but the tactic
         can handle most difficulties. See the next comment for an example of when 
         [ only_one ] cannot exfalso all irrelevant cases *)
  only_one.
  inversion Heqesnew; subst.
  rewrite H0 in Hj; inversion Hj; subst. repeat split => //. 
  inversion Heqesnew; subst. 
  move: (ssrnat.leq_trans Hlim H).
  rewrite ssrnat.ltnn. done.
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


Lemma br_if_table_over_det c iss i s f s' f' es:
  ssrnat.leq (length iss) (Wasm_int.nat_of_uint i32m c) ->
  reduce s f [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] s' f' es ->
  reduce_det_strong_goal s f [AI_basic (BI_br i)] s' f' es.
Proof.
  move => Hlim Hred.
  (* example of a usage of [ only_one ] : in this subgoal, we know that Hred2 is
         the hypothesis [ [AI_basic (BI_const v) ; AI_basic (BI_unop t op) ] -> es2 ].
         [ only_one ] selects the left disjunct in the conclusion, meaning we wish
         to show that in this case, there was indeed determinism. Then it performs a 
         case analysis on Hred2. Most cases have a left-hand-side very different from
         [AI_basic (BI_const v) ; AI_basic (BI_unop t op)] and can thus be exfalsoed.
         Some cases, like the r_label case, require a little more effort, but the tactic
         can handle most difficulties. See the next comment for an example of when 
         [ only_one ] cannot exfalso all irrelevant cases *)
  only_one.
  inversion Heqesnew; subst.
  move: (ssrnat.leq_trans H Hlim).
  rewrite ssrnat.ltnn. done.
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
