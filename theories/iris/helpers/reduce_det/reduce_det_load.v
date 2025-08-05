From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Set Bullet Behavior "Strict Subproofs".

Lemma load_det i m k off t bs a s f s' f' es:
  smem_ind s (f_inst f) = Some i ->
  nth_error (s_mems s) i = Some m ->
  load m (Wasm_int.N_of_uint i32m k) off (length_tnum t) = Some bs ->
  reduce s f [AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load t None a off)] s' f' es ->
  reduce_det_strong_goal s f [AI_basic (BI_const (wasm_deserialise bs t))] s' f' es.
Proof.
  move => Hmem Hi Hload Hred.
  only_one.
  1-2: inversion Heqesnew; subst.
  1-2: rewrite H in Hmem; inversion Hmem; subst.
  1-2: rewrite H0 in Hi; inversion Hi; subst.
  1-2: rewrite H1 in Hload; inversion Hload; subst.
  repeat split => //. 
  
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


Lemma load_failure_det i m k off t a s f s' f' es:
  smem_ind s (f_inst f) = Some i ->
  nth_error (s_mems s) i = Some m ->
  load m (Wasm_int.N_of_uint i32m k) off (length_tnum t) = None ->
  reduce s f [AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load t None a off)] s' f' es ->
  reduce_det_strong_goal s f [AI_trap] s' f' es .
Proof.
  move => Hmem Hi Hload Hred.
  only_one.
  inversion Heqesnew; subst.
  rewrite H in Hmem; inversion Hmem; subst.
  rewrite H0 in Hi; inversion Hi; subst.
  rewrite H1 in Hload; inversion Hload; subst.

  
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


Lemma load_packed_det i m k off t bs sx tp a s f s' f' es:
  smem_ind s (f_inst f) = Some i ->
  nth_error (s_mems s) i = Some m ->
  load_packed sx m (Wasm_int.N_of_uint i32m k) off (length_tp tp) (length_tnum t) = Some bs ->
  reduce s f [AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load t (Some (tp, sx)) a off)] s' f' es ->
  reduce_det_strong_goal s f [AI_basic (BI_const (wasm_deserialise bs t))] s' f' es.
Proof.
  move => Hmem Hi Hload Hred.
  only_one.
  1-2: inversion Heqesnew; subst.
  1-2: rewrite H in Hmem; inversion Hmem; subst.
  1-2: rewrite H0 in Hi; inversion Hi; subst.
  1-2: rewrite H1 in Hload; inversion Hload; subst.
  repeat split => //. 
  
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


Lemma load_packed_failure_det i m k off tp sx t a s f s' f' es:
  smem_ind s (f_inst f) = Some i ->
  nth_error (s_mems s) i = Some m ->
  load_packed sx m (Wasm_int.N_of_uint i32m k) off (length_tp tp) (length_tnum t) = None ->
  reduce s f [AI_basic (BI_const (VAL_int32 k)); AI_basic (BI_load t (Some (tp, sx)) a off)] s' f' es ->
  reduce_det_strong_goal s f [AI_trap] s' f' es .
Proof.
  move => Hmem Hi Hload Hred.
  only_one.
  inversion Heqesnew; subst.
  rewrite H in Hmem; inversion Hmem; subst.
  rewrite H0 in Hi; inversion Hi; subst.
  rewrite H1 in Hload; inversion Hload; subst.

  
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
