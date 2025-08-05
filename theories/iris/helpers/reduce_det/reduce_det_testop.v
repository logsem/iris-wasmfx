From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Lemma testop_i32_det c s f s' f' es testop:
  reduce s f [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_testop T_i32 testop)] s' f' es ->
  reduce_det_strong_goal s f [AI_basic (BI_const (VAL_int32 (wasm_bool (app_testop_i (e:=i32t) testop c))))]
    s' f' es .
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

Lemma testop_i64_det c s f s' f' es testop:
  reduce s f [AI_basic (BI_const (VAL_int64 c)); AI_basic (BI_testop T_i64 testop)] s' f' es ->
  reduce_det_strong_goal s f [AI_basic (BI_const (VAL_int32 (wasm_bool (app_testop_i (e:=i64t) testop c))))]
    s' f' es .
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
