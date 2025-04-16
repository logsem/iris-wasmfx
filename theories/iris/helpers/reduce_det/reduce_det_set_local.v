From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Set Bullet Behavior "Strict Subproofs".

Lemma set_local_det v f2 vd i s f s' f' es:
  f_inst f2 = f_inst f ->
  ssrnat.leq (S i) (length (f_locs f)) ->
  f_locs f2 = set_nth vd (f_locs f) i v ->
  reduce s f [AI_const v; AI_basic $ BI_set_local i] s' f' es ->
  reduce_det_goal s f2 [] s' f' es [AI_const v; AI_basic $ BI_set_local i]. 
Proof.
  move => Hf2 Hlenf Hf2' Hred.
   assert (forall l i (v:value) vd vd', ssrnat.leq (S i) (length l) ->
                                      set_nth vd l i v = set_nth vd' l i v) as Hign.
   { intro. induction l ; intros i' v' vd1 vd2 Hlen. inversion Hlen.
     destruct i' => //=. simpl in Hlen ; apply ssrnat.ltnSE in Hlen.
     by rewrite (IHl i' v' vd1 vd2 Hlen). }
  destruct v; destruct v;
    only_one.
   all: try by inversion Heqesnew; subst;
     destruct v; destruct v => //;
     inversion H3; subst;
     destruct f2, f, f';
     simpl in Hf2, Hf2', H, H1, Hlenf, H0;
     subst;
     erewrite Hign; [left |].

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
