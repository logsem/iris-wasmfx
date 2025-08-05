From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Set Bullet Behavior "Strict Subproofs".

Lemma select_false_det v1 v2 n s f s' f' es:
  n = Wasm_int.int_zero i32m ->
  reduce s f [AI_const v1; AI_const v2; AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select] s' f' es ->
  reduce_det_strong_goal s f [AI_const v2] s' f' es .
Proof.
  move => H Hred.
    
  let Hfill := fresh "Hfill" in
  let Hfill' := fresh "Hfill" in
  let IHHred := fresh "IHHred" in
    lazymatch goal with
      Hred : reduce _ _ ?es _ _ _ |- _ =>
      remember es as esnew eqn:Heqesnew;
      induction Hred as [? ? ? ? Hred | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?? esnewest ??????? Hred IHHred Hfill Hfill' | ];
      first destruct Hred as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? Hfill];
      try (by inversion Heqesnew) ;
      try (by lazymatch goal with
                _ : (v_to_e_list ?vs ++ _)%SEQ = _ |- _ => do 5 destruct vs => //
              end);
      try (by lazymatch goal with
                _ : (?vs ++ _)%SEQ = _ |- _ => do 5 destruct vs => //
              end);
      try (by inversion Heqesnew; subst; repeat split => //);
      try (move/lfilledP in Hfill; inversion Hfill; subst;
            try (by lazymatch goal with
                _ : (?vs ++ _)%SEQ = _ |- _ => do 5 (destruct vs => //; try by destruct v1, v2; try destruct v; try destruct v0)
                    end))  ;
      last (move/lfilledP in Hfill'; inversion Hfill'; subst ;
      lazymatch goal with
        _ : (?vs ++ ?esnewest ++ ?es'0)%SEQ = _ |- _ =>
          destruct vs;
          first (
              destruct es'0 ;
              [ repeat rewrite cats0 /=;
                  lazymatch goal with H : ([] ++ _ ++ [])%SEQ = _ |- _ => rewrite cats0 /= in H; subst end;
                try apply IHHred => //
              | lazymatch goal with
                  H : ([] ++ _ ++ _ :: _)%SEQ = _ |- _ =>
                    do 4 try (destruct esnewest; first by inversion H; subst;
                              apply values_no_reduce in Hred; repeat rewrite /= const_const);
                    try (destruct esnewest; last by inversion H);
                    inversion H
                end] ) 
      end)
    end.
  inversion H4; subst.
  destruct vs.
  - destruct esnewest; first empty_list_no_reduce.
    inversion H3; subst.
    destruct esnewest; first by apply values_no_reduce in Hred; try rewrite /= const_const.
    inversion H5; subst.
    destruct esnewest; first by apply values_no_reduce in Hred; repeat rewrite /= const_const.
    inversion H6; subst. destruct esnewest, es'0 => //.
    clear -Hred.
      lazymatch goal with
    | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
    end.
    exfalso. 
    induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
        first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by do 5 destruct vs => //);
      try (by do 5 destruct ves => //);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by do 4 (destruct vs => //; try by destruct v2; try destruct v));
          do 4 (destruct bef => //; try by destruct v2; try destruct v)
        | move/lfilledP in H02; inversion H02; subst;
          try (by do 4 (destruct vs => //; try by destruct v2; try destruct v));
          try (by do 4 (destruct bef => //; try by destruct v2; try destruct v)) ;
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred; repeat rewrite /= const_const);
              inversion H3; subst;
              destruct es => //; apply IHHred => //
              )
        ].
    inversion H3; subst.
    destruct vs.
    + destruct es; first empty_list_no_reduce.
      inversion H2; subst.
      destruct es; first by apply values_no_reduce in Hred.
      inversion H4; subst. destruct es, es'0 => //.
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
    inversion H3; subst. destruct vs, es, es'0 => //.
    + destruct vs.
      2:{ inversion H2; subst. simpl in H. destruct v2; try destruct v => //. }   inversion H2; subst.
      destruct es; first empty_list_no_reduce.
      inversion H4; subst.
      destruct es => //.
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
  - inversion H3; subst.
     destruct vs.
    + destruct esnewest; first empty_list_no_reduce.
      inversion H5; subst.
      destruct esnewest; first by apply values_no_reduce in Hred.
      inversion H6; subst. destruct esnewest, es'0 => //.
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
    inversion H3; subst. destruct vs, es, es'0 => //.
    + destruct vs.
      2:{ inversion H5; subst. simpl in H0. repeat rewrite const_const in H0. done. }
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

Lemma select_true_det v1 v2 n s f s' f' es:
  n <> Wasm_int.int_zero i32m ->
  reduce s f [AI_const v1; AI_const v2; AI_basic (BI_const (VAL_int32 n)); AI_basic BI_select] s' f' es ->
  reduce_det_strong_goal s f [AI_const v1] s' f' es .
Proof.
  move => H Hred.
    
  let Hfill := fresh "Hfill" in
  let Hfill' := fresh "Hfill" in
  let IHHred := fresh "IHHred" in
    lazymatch goal with
      Hred : reduce _ _ ?es _ _ _ |- _ =>
      remember es as esnew eqn:Heqesnew;
      induction Hred as [? ? ? ? Hred | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?? esnewest ??????? Hred IHHred Hfill Hfill' | ];
      first destruct Hred as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? Hfill];
      try (by inversion Heqesnew) ;
      try (by lazymatch goal with
                _ : (v_to_e_list ?vs ++ _)%SEQ = _ |- _ => do 5 destruct vs => //
              end);
      try (by lazymatch goal with
                _ : (?vs ++ _)%SEQ = _ |- _ => do 5 destruct vs => //
              end);
      try (by inversion Heqesnew; subst; repeat split => //);
      try (move/lfilledP in Hfill; inversion Hfill; subst;
            try (by lazymatch goal with
                _ : (?vs ++ _)%SEQ = _ |- _ => do 5 (destruct vs => //; try by destruct v1, v2; try destruct v; try destruct v0)
                    end))  ;
      last (move/lfilledP in Hfill'; inversion Hfill'; subst ;
      lazymatch goal with
        _ : (?vs ++ ?esnewest ++ ?es'0)%SEQ = _ |- _ =>
          destruct vs;
          first (
              destruct es'0 ;
              [ repeat rewrite cats0 /=;
                  lazymatch goal with H : ([] ++ _ ++ [])%SEQ = _ |- _ => rewrite cats0 /= in H; subst end;
                try apply IHHred => //
              | lazymatch goal with
                  H : ([] ++ _ ++ _ :: _)%SEQ = _ |- _ =>
                    do 4 try (destruct esnewest; first by inversion H; subst;
                              apply values_no_reduce in Hred; repeat rewrite /= const_const);
                    try (destruct esnewest; last by inversion H);
                    inversion H
                end] ) 
      end)
    end.
  inversion H4; subst.
  destruct vs.
  - destruct esnewest; first empty_list_no_reduce.
    inversion H5; subst.
    destruct esnewest; first by apply values_no_reduce in Hred; try rewrite /= const_const.
    inversion H6; subst.
    destruct esnewest; first by apply values_no_reduce in Hred; repeat rewrite /= const_const.
    inversion H7; subst. destruct esnewest, es'0 => //.
    clear -Hred.
      lazymatch goal with
    | _ : reduce _ _ ?esn _ _ _ |- _ => remember esn as ves
    end.
    exfalso. 
    induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ???????????? H02 H03 | ];
        first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
        try (by inversion Heqves);
        try (by do 5 destruct vs => //);
      try (by do 5 destruct ves => //);
        [ by move/lfilledP in H01; inversion H01; subst;
          try (by do 4 (destruct vs => //; try by destruct v2; try destruct v));
          do 4 (destruct bef => //; try by destruct v2; try destruct v)
        | move/lfilledP in H02; inversion H02; subst;
          try (by do 4 (destruct vs => //; try by destruct v2; try destruct v));
          try (by do 4 (destruct bef => //; try by destruct v2; try destruct v)) ;
          destruct vs;
          first (
              do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred; repeat rewrite /= const_const);
              inversion H3; subst;
              destruct es => //; apply IHHred => //
              )
        ].
    inversion H3; subst.
    destruct vs.
    + destruct es; first empty_list_no_reduce.
      inversion H2; subst.
      destruct es; first by apply values_no_reduce in Hred.
      inversion H4; subst. destruct es, es'0 => //.
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
    inversion H3; subst. destruct vs, es, es'0 => //.
    + destruct vs.
      2:{ inversion H2; subst. rewrite /= const_const in H. done. }
      destruct es; first empty_list_no_reduce.
      inversion H2; subst.
      destruct es => //.
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
  - inversion H3; subst.
     destruct vs.
    + destruct esnewest; first empty_list_no_reduce.
      inversion H5; subst.
      destruct esnewest; first by apply values_no_reduce in Hred.
      inversion H8; subst. destruct esnewest, es'0 => //.
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
    inversion H3; subst. destruct vs, es, es'0 => //.
    + destruct vs.
      2:{ inversion H5; subst. simpl in H0. repeat rewrite const_const in H0. done. }
      inversion H5; subst.
      destruct esnewest; first empty_list_no_reduce.
      inversion H8; subst.
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

