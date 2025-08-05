From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Set Bullet Behavior "Strict Subproofs".

Lemma set_global_det v s2 i s f s' f' es:
  supdate_glob s (f_inst f) i v = Some s2 ->
  reduce s f [AI_basic (BI_const v); AI_basic $ BI_set_global i] s' f' es ->
  reduce_det_strong_goal s2 f [] s' f' es.
Proof.
  move => Hs2 Hred.
  only_one.
  - inversion Heqesnew; subst.
    rewrite Hs2 in H; inversion H; subst.
    repeat split => //.
  - inversion H3; subst.
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
