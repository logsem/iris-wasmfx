From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Lemma ref_is_null_det t s f s' f' es:
  reduce s f [AI_const (VAL_ref (VAL_ref_null t)); AI_basic BI_ref_is_null] s' f' es ->
  reduce_det_goal s f [AI_const (VAL_num (VAL_int32 Wasm_int.Int32.one))] s' f' es [AI_const (VAL_ref (VAL_ref_null t)); AI_basic BI_ref_is_null].
Proof.
  move => Hred.
  - (* example of a usage of [ only_one ] : in this subgoal, we know that Hred2 is
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
    destruct ref; inversion H1; subst.
    by exfalso; eapply H.
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


Lemma ref_is_not_null_det ref s f s' f' es:
  (forall t, ref <> VAL_ref_null t) ->
  reduce s f [AI_const (VAL_ref ref); AI_basic BI_ref_is_null] s' f' es ->
  reduce_det_goal s f [AI_const (VAL_num (VAL_int32 Wasm_int.Int32.zero))] s' f' es [AI_const (VAL_ref ref); AI_basic BI_ref_is_null].
Proof.
  move => Href Hred.
  - (* example of a usage of [ only_one ] : in this subgoal, we know that Hred2 is
         the hypothesis [ [AI_basic (BI_const v) ; AI_basic (BI_unop t op) ] -> es2 ].
         [ only_one ] selects the left disjunct in the conclusion, meaning we wish
         to show that in this case, there was indeed determinism. Then it performs a 
         case analysis on Hred2. Most cases have a left-hand-side very different from
         [AI_basic (BI_const v) ; AI_basic (BI_unop t op)] and can thus be exfalsoed.
         Some cases, like the r_label case, require a little more effort, but the tactic
         can handle most difficulties. See the next comment for an example of when 
         [ only_one ] cannot exfalso all irrelevant cases *)
    destruct ref.
    all: only_one.
    exfalso; by eapply Href.
    all: inversion H3; subst.
    all: destruct vs; inversion H4; subst => //.
    all: destruct esnewest; first empty_list_no_reduce.
    all: inversion H1; subst.
    all: destruct esnewest => //. 
    all: clear -Hred.
    all: lazymatch goal with
    | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
    end.
    all: exfalso. 
    all: induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
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
    all: inversion H3; subst => //.
Qed.
