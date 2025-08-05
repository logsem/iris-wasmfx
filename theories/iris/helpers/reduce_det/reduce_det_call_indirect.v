From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Lemma call_indirect_det c i cl a s f s' f' es:
  stab_addr s f (Wasm_int.nat_of_uint i32m c) = Some a ->
   nth_error (s_funcs s) a = Some cl ->
  stypes (f_inst f) i = Some (cl_type cl) ->
  reduce s f [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] s' f' es ->
  reduce_det_strong_goal s f [AI_invoke a]
    s' f' es.
Proof.
  move => Ha Hcl Hclt Hred.
  only_one.
  1-3: inversion Heqesnew; subst.
  1-3: rewrite H in Ha; inversion Ha; subst.
  repeat split => //. rewrite H0 in Hcl. inversion Hcl; subst.
  apply H1 in Hclt => //. 
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


Lemma call_indirect_failure1_det c i cl a s f s' f' es:
  stab_addr s f (Wasm_int.nat_of_uint i32m c) = Some a ->
   nth_error (s_funcs s) a = Some cl ->
  stypes (f_inst f) i <> Some (cl_type cl) ->
  reduce s f [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] s' f' es ->
  reduce_det_strong_goal s f [AI_trap]
    s' f' es.
Proof.
  move => Ha Hcl Hclt Hred.
  only_one.
  inversion Heqesnew; subst.
  rewrite H in Ha; inversion Ha; subst.
  rewrite H0 in Hcl. inversion Hcl; subst.
  apply Hclt in H1 => //. 
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


Lemma call_indirect_failure2_det c i s f s' f' es:
  stab_addr s f (Wasm_int.nat_of_uint i32m c) = None ->
  reduce s f [AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_call_indirect i)] s' f' es ->
  reduce_det_strong_goal s f [AI_trap]
    s' f' es.
Proof.
  move => Ha Hred.
  only_one.
  inversion Heqesnew; subst.
  rewrite H in Ha; inversion Ha; subst.
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
