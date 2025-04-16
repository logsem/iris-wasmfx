From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Lemma tee_local_det v i s f s' f' es:
  is_const v ->
  reduce s f [v; AI_basic (BI_tee_local i)] s' f' es ->
  reduce_det_goal s f [v; v; AI_basic (BI_set_local i)] s' f' es [v; AI_basic (BI_tee_local i)]. 
Proof.
  move => H Hred.
  destruct v => //; first destruct b => //. 
  all: only_one.
  all: simpl in H3; remove_bools_options.
  all: inversion H4; subst.
  all: destruct vs.
  1,3,5,7,9: repeat (destruct esnewest; first by inversion H6; subst; apply values_no_reduce in Hred).
  1-5: inversion H6; subst.
  1-5: destruct esnewest, es'0 => //.
  1-5: clear -Hred.
  1-5: lazymatch goal with
    | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
    end.
  1-5: exfalso. 
  1-5: induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
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
  1-5: inversion H3; subst. 
  1-5: destruct vs; last by inversion H2; subst.
  1-5: destruct es; first empty_list_no_reduce.
  1-5: inversion H2; subst.
  all: destruct vs; last by inversion H6; subst.
  all: inversion H6; subst.
  all: destruct esnewest; first empty_list_no_reduce.
  all: inversion H7; subst.
Qed. 
