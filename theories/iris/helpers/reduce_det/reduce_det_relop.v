From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.



Lemma relop_det v1 v2 op t s f s' f' es:
  reduce s f [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] s' f' es ->
  reduce_det_strong_goal s f [AI_basic (BI_const (VAL_int32 (wasm_bool (app_relop op v1 v2))))] s' f' es .
Proof.
  move => Hred.
  only_one.
  simpl in H2; remove_bools_options.
  inversion H3; subst.
  destruct vs.
  { repeat (destruct esnewest; first by inversion H5; subst; apply values_no_reduce in Hred).
    inversion H5; subst.
    destruct esnewest, es'0 => //.
    lazymatch goal with
    | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
    end.
    exfalso. clear IHHred.
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
              repeat (destruct es; first by inversion H9; subst; apply values_no_reduce in Hred);
              inversion H9; subst;
              destruct es => //; apply IHHred => //
              )
        ].
    constructor => //.
    inversion H9; subst. 
    destruct vs; last by inversion H8; subst.
    destruct es; first empty_list_no_reduce.
    inversion H8; subst.
    destruct es, es'0 => //.
    clear - Hred.
    lazymatch goal with
    | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
    end.
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
          try (by do 4 destruct bef => //) ;
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
              inversion H3; subst; 
              destruct es => //; apply IHHred => //
              )
        ].
    inversion H3; subst. destruct vs, es, es'0 => //.  }
  destruct vs; last by inversion H5; subst.
  inversion H5; subst.
  destruct esnewest; first empty_list_no_reduce.
  inversion H6; subst.
  destruct esnewest => //.
  clear - Hred.
  exfalso.
  lazymatch goal with
    | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
    end.
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
          try (by do 4 destruct bef => //) ;
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
              inversion H3; subst; 
              destruct es => //; apply IHHred => //
              )
        ].
    inversion H3; subst.
    done.
Qed. 

