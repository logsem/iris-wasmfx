From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.



Lemma store_det i m k off a v t mem' s f s' f' es:
  smem_ind s (f_inst f) = Some i ->
  nth_error (s_mems s) i = Some m ->
  store m (Wasm_int.N_of_uint i32m k) off (bits v) (length_tnum t) = Some mem' ->
  reduce s f [AI_basic (BI_const $ VAL_int32 k); AI_basic (BI_const v); AI_basic (BI_store t None a off)] s' f' es ->
  reduce_det_goal (upd_s_mem s (update_list_at (s_mems s) i mem')) f [] s' f' es [AI_basic (BI_const $ VAL_int32 k); AI_basic (BI_const v); AI_basic (BI_store t None a off)]. 
Proof.
  move => H Hm Hstore Hred.
  only_one.
  1-2: inversion Heqesnew; subst.
  1-2: rewrite H1 in H; inversion H; subst.
  1-2: rewrite H2 in Hm; inversion Hm; subst.
  1-2: rewrite H3 in Hstore; inversion Hstore; subst.
  by left.
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

Lemma store_failure_det i m k off a v t s f s' f' es:
  smem_ind s (f_inst f) = Some i ->
  nth_error (s_mems s) i = Some m ->
  store m (Wasm_int.N_of_uint i32m k) off (bits v) (length_tnum t) = None ->
  reduce s f [AI_basic (BI_const $ VAL_int32 k); AI_basic (BI_const v); AI_basic (BI_store t None a off)] s' f' es ->
  reduce_det_goal s f [AI_trap] s' f' es [AI_basic (BI_const $ VAL_int32 k); AI_basic (BI_const v); AI_basic (BI_store t None a off)]. 
Proof.
  move => H Hm Hstore Hred.
  only_one.
  inversion Heqesnew; subst.
  rewrite H1 in H; inversion H; subst.
  rewrite H2 in Hm; inversion Hm; subst.
  rewrite H3 in Hstore; inversion Hstore; subst.
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


Lemma store_packed_det i m k off a v t mem' tp s f s' f' es:
  smem_ind s (f_inst f) = Some i ->
  nth_error (s_mems s) i = Some m ->
  store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (length_tp tp) = Some mem' ->
  reduce s f [AI_basic (BI_const $ VAL_int32 k); AI_basic (BI_const v); AI_basic (BI_store t (Some tp) a off)] s' f' es ->
  reduce_det_goal (upd_s_mem s (update_list_at (s_mems s) i mem')) f [] s' f' es [AI_basic (BI_const $ VAL_int32 k); AI_basic (BI_const v); AI_basic (BI_store t (Some tp) a off)]. 
Proof.
  move => H Hm Hstore Hred.
  only_one.
  1-2: inversion Heqesnew; subst.
  1-2: rewrite H1 in H; inversion H; subst.
  1-2: rewrite H2 in Hm; inversion Hm; subst.
  1-2: rewrite H3 in Hstore; inversion Hstore; subst.
  by left.
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


Lemma store_packed_failure_det i m k off a v t tp s f s' f' es:
  smem_ind s (f_inst f) = Some i ->
  nth_error (s_mems s) i = Some m ->
  store_packed m (Wasm_int.N_of_uint i32m k) off (bits v) (length_tp tp) = None ->
  reduce s f [AI_basic (BI_const $ VAL_int32 k); AI_basic (BI_const v); AI_basic (BI_store t (Some tp) a off)] s' f' es ->
  reduce_det_goal s f [AI_trap] s' f' es [AI_basic (BI_const $ VAL_int32 k); AI_basic (BI_const v); AI_basic (BI_store t (Some tp) a off)]. 
Proof.
  move => H Hm Hstore Hred.
  only_one.
  inversion Heqesnew; subst.
  rewrite H1 in H; inversion H; subst.
  rewrite H2 in Hm; inversion Hm; subst.
  rewrite H3 in Hstore; inversion Hstore; subst.
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
