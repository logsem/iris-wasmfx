From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Lemma cvtop_convert_det v v' t1 t2 sx s f s' f' es:
  types_num_agree t1 v ->
  cvt t2 sx v = Some v' ->
  reduce s f [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] s' f' es ->
  reduce_det_goal s f [AI_basic (BI_const v')] s' f' es [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)].
Proof.
  move => H H0 Hred.
  only_one.
  1-2: inversion Heqesnew; left; subst;
  rewrite H0 in H2; inversion H2; subst => //.
  inversion H5; subst.
  destruct vs; inversion H6; subst => //.
  destruct esnewest; first empty_list_no_reduce.
  inversion H3; subst.
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

Lemma cvtop_convert_none_det v t1 t2 sx s f s' f' es:
  types_num_agree t1 v ->
  cvt t2 sx v = None ->
  reduce s f [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] s' f' es ->
  reduce_det_goal s f [AI_trap] s' f' es [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)].
Proof.
    move => H H0 Hred.
  only_one.
  inversion Heqesnew; left; subst;
  rewrite H0 in H2; inversion H2; subst => //.
  inversion H5; subst.
  destruct vs; inversion H6; subst => //.
  destruct esnewest; first empty_list_no_reduce.
  inversion H3; subst.
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
  

Lemma cvtop_reinterpret_det v t1 t2 s f s' f' es:
  types_num_agree t1 v ->
  reduce s f [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] s' f' es ->
  reduce_det_goal s f [AI_basic (BI_const (wasm_deserialise (bits v) t2))] s' f' es
    [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)].
Proof.
  move => H Hred.
  only_one.
  inversion H4; subst.
  destruct vs; inversion H5; subst => //.
  destruct esnewest; first empty_list_no_reduce.
  inversion H2; subst.
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

