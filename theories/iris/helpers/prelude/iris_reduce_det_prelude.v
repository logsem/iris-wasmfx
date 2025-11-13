From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
Require Export iris_reduce_properties first_instr.

(* Knowing hypothesis "Hred : objs -> _" (with frames (locs, inst) and (locs', inst')),
   attempts to exfalso away most of the possible ways Hred could hold, leaving the user
   with only the one possible desired case. Tactic will also attempt to trivially solve
   this one case, but may give it to user if attempt fails. *)

Ltac only_one :=
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
                _ : (v_to_e_list ?vs ++ _)%SEQ = _ |- _ => do 4 destruct vs => //
              end);
      try (by lazymatch goal with
                _ : (?vs ++ _)%SEQ = _ |- _ => do 4 destruct vs => //
              end);
      try (by inversion Heqesnew; subst; repeat split => //; left);
      try (move/lfilledP in Hfill; inversion Hfill; subst;
            try (by lazymatch goal with
                _ : (?vs ++ _)%SEQ = _ |- _ => do 4 destruct vs => //
              end));
      last (move/lfilledP in Hfill'; inversion Hfill'; subst ;
      lazymatch goal with
        _ : (?vs ++ ?esnewest ++ ?es'0)%SEQ = _ |- _ =>
          destruct vs;
          first (
              destruct es'0 ;
              [ repeat rewrite cats0 /=;
                  lazymatch goal with H : ([] ++ _ ++ [])%SEQ = _ |- _ => rewrite cats0 /= in H; subst end;
                apply IHHred => //
              | lazymatch goal with
                  H : ([] ++ _ ++ _ :: _)%SEQ = _ |- _ =>
                    do 3 try (destruct esnewest; first by inversion H; subst;
                              apply values_no_reduce in Hred);
                    try (destruct esnewest; last by inversion H);
                    inversion H
                end] ) 
      end)
    end.



Definition reduce_det_strong_goal (ws1: store_record) (f1: frame) (es1: list administrative_instruction) ws2 f2 es2 :=
  f1 = f2 /\ es1 = es2 /\ ws1 = ws2. 


Definition reduce_det_goal (ws1: store_record) (f1: frame) es1 ws2 f2 es2 es :=
  f1 = f2 /\ (es1 = es2 /\ ws1 = ws2 \/
          (exists i, first_instr es = Some (AI_basic (BI_grow_memory),i)) \/
          (exists i1 i2 i3, first_instr es = Some (AI_trap,i1) /\ first_instr es1 = Some (AI_trap,i2) /\
                         first_instr es2 = Some (AI_trap,i3) /\ ws1 = ws2)).

Lemma reduce_det_strong_implies_goal a b c d e f g :
  reduce_det_strong_goal a b c d e f -> reduce_det_goal a b c d e f g.
Proof.
  intros (-> & -> & ->).
  split => //. by left.
Qed. 
