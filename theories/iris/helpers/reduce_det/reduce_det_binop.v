From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Lemma binop_det v1 v2 v op t s f s' f' es:
  app_binop op v1 v2 = Some v ->
  reduce s f [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] s' f' es ->
  reduce_det_strong_goal s f [AI_basic (BI_const v)] s' f' es.
Proof.
  move => H Hred.
  only_one.
  1-2: inversion Heqesnew; subst; repeat split => //; rewrite H in H0; inversion H0; subst => //. 
  simpl in H3; remove_bools_options.
  inversion H4; subst.
  destruct vs.
  { repeat (destruct esnewest; first by inversion H6; subst; apply values_no_reduce in Hred).
    inversion H6; subst.
    destruct esnewest, es'0 => //.
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
    inversion H3; subst. 
    destruct vs; last by inversion H2; subst.
    destruct es; first empty_list_no_reduce.
    inversion H2; subst.
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
  destruct vs; last by inversion H6; subst.
  inversion H6; subst.
  destruct esnewest; first empty_list_no_reduce.
  inversion H7; subst.
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


Lemma binop_none_det v1 v2 op t s f s' f' es:
  app_binop op v1 v2 = None ->
  reduce s f [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] s' f' es ->
  reduce_det_strong_goal s f [AI_trap] s' f' es.
Proof.
  move => H Hred.
  only_one.
  inversion Heqesnew; subst; repeat split => //; rewrite H in H0; inversion H0; subst => //. 
  simpl in H3; remove_bools_options.
  inversion H4; subst.
  destruct vs.
  { repeat (destruct esnewest; first by inversion H6; subst; apply values_no_reduce in Hred).
    inversion H6; subst.
    destruct esnewest, es'0 => //.
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
    inversion H3; subst. 
    destruct vs; last by inversion H2; subst.
    destruct es; first empty_list_no_reduce.
    inversion H2; subst.
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
  destruct vs; last by inversion H6; subst.
  inversion H6; subst.
  destruct esnewest; first empty_list_no_reduce.
  inversion H7; subst.
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

