From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Lemma drop_det v s f s' f' es:
  reduce s f [AI_const v; AI_basic BI_drop] s' f' es ->
  reduce_det_goal s f [] s' f' es [AI_const v; AI_basic BI_drop]. 
Proof.
  move => Hred.
   destruct v; destruct v;
  only_one.
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
