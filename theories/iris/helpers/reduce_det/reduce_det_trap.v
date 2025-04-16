From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.helpers.prelude Require Export iris_reduce_det_prelude.

Set Bullet Behavior "Strict Subproofs".

Lemma filled_trap_det LI lh s f s' f' es:
(*  LI <> [AI_trap] -> *)
  lfilled 0 lh [AI_trap] LI ->
  reduce s f LI s' f' es ->
  reduce_det_goal s f [AI_trap] s' f' es LI.
Proof.
  intros (* HLI *) Hfill Hred.
  induction Hred.
  destruct H.
  84:{ clear IHHred.
       right. right. exists 0, 0, 0.
       generalize dependent les. generalize dependent lh0. generalize dependent les'.
       induction lh; intros les' lh0 H0 les (* Hntrap *) Hfill H.
       all: move/lfilledP in Hfill; inversion Hfill; subst.
       - move/lfilledP in H; inversion H; subst.
         all: try by apply first_values in H1 as (? & ? & ?).
         edestruct first_non_value_reduce as (vs' & e & es'' & Hvs & He & Hes).
         exact Hred.
         subst.
         rewrite separate1 -cat_app -cat_app in H1.
         do 3 rewrite catA in H1.
         do 2 rewrite -catA in H1.
         apply first_values in H1 as (<- & -> & <-) => //.
         3: apply const_list_concat => //.
         2:{ destruct He as [? | ->] => //.
             destruct e => //.
             destruct b => //. }
         assert (lfilled 0 (LH_base vs' es'') [AI_trap] (vs' ++ (AI_trap :: es'')%SEQ)%list).
         { apply/lfilledP; constructor => //. }
         edestruct trap_reduce as (lh' & Hlh' & Hσ).
         exact H1. exact Hred.
         repeat split => //.
         rewrite first_instr_const //.
         edestruct lfilled_trans.
         exact Hlh'. exact H0.
         eapply lfilled_implies_starts => //.
       - move/lfilledP in H; inversion H; subst.
         all: try by apply first_values in H1 as (? & ? & ?).
         + edestruct first_non_value_reduce as (vs' & e & es''' & Hvs & He & Hes).
           exact Hred. subst.
           rewrite separate1 -cat_app -cat_app in H1.
           do 3 rewrite catA in H1.
           do 2 rewrite -catA in H1.
           apply first_values in H1 as (<- & -> & <-) => //.
           3: apply const_list_concat => //.
           2: destruct He as [? | ->] => //; destruct e => //; destruct b => //.
           assert (lfilled 0 (LH_handler vs' l0 lh es''') [AI_trap] (vs' ++ (AI_handler l0 LI :: es''')%SEQ)%list).
           { apply/lfilledP; constructor => //. }
           edestruct trap_reduce as (lh'' & Hlh' & Hσ).
           exact H1. exact Hred.
           repeat split => //.
           rewrite first_instr_const.
           apply first_instr_app.
           unfold first_instr. simpl.
           move/lfilledP in H9.
           apply lfilled_implies_starts in H9 => //.
           unfold first_instr in H9.
           rewrite H9. done.
           apply const_list_concat => //.
           edestruct lfilled_trans.
           exact Hlh'. exact H0.
           eapply lfilled_implies_starts => //.
         + apply first_values in H1 as (-> & Hh & ->) => //.
           inversion Hh; subst.
           move/lfilledP in H0; inversion H0; subst.
           edestruct IHlh as (Hres1 & Hres2 & Hres3 & Hres4).
           apply/lfilledP; exact H13.
           apply/lfilledP; exact H9.
           apply/lfilledP; exact H6.
           repeat split => //.
           rewrite first_instr_const => //.
           apply first_instr_app.
           rewrite /first_instr /=.
           move/lfilledP in H9.
           apply lfilled_implies_starts in H9 => //.
           unfold first_instr in H9.
           rewrite H9. done.
           rewrite first_instr_const //.
           apply first_instr_app.
           rewrite /first_instr /=.
           unfold first_instr in Hres3.
           rewrite Hres3. done.
       - move/lfilledP in H; inversion H; subst.
         all: try by apply first_values in H1 as (? & ? & ?).
         + edestruct first_non_value_reduce as (vs' & e & es''' & Hvs & He & Hes).
           exact Hred. subst.
           rewrite separate1 -cat_app -cat_app in H1.
           do 3 rewrite catA in H1.
           do 2 rewrite -catA in H1.
           apply first_values in H1 as (<- & -> & <-) => //.
           3: apply const_list_concat => //.
           2: destruct He as [? | ->] => //; destruct e => //; destruct b => //.
           assert (lfilled 0 (LH_prompt vs' l0 l1 lh es''') [AI_trap] (vs' ++ (AI_prompt l0 l1 LI :: es''')%SEQ)%list).
           { apply/lfilledP; constructor => //. }
           edestruct trap_reduce as (lh'' & Hlh' & Hσ).
           exact H1. exact Hred.
           repeat split => //.
           rewrite first_instr_const.
           apply first_instr_app.
           unfold first_instr. simpl.
           move/lfilledP in H10.
           apply lfilled_implies_starts in H10 => //.
           unfold first_instr in H10.
           rewrite H10. done.
           apply const_list_concat => //.
           edestruct lfilled_trans.
           exact Hlh'. exact H0.
           eapply lfilled_implies_starts => //.
         + apply first_values in H1 as (-> & Hh & ->) => //.
           inversion Hh; subst.
           move/lfilledP in H0; inversion H0; subst.
           edestruct IHlh as (Hres1 & Hres2 & Hres3 & Hres4).
           apply/lfilledP; exact H14.
           apply/lfilledP; exact H10.
           apply/lfilledP; exact H6.
           repeat split => //.
           rewrite first_instr_const => //.
           apply first_instr_app.
           rewrite /first_instr /=.
           move/lfilledP in H10.
           apply lfilled_implies_starts in H10 => //.
           unfold first_instr in H10.
           rewrite H10. done.
           rewrite first_instr_const //.
           apply first_instr_app.
           rewrite /first_instr /=.
           unfold first_instr in Hres3.
           rewrite Hres3. done.
           

         } 
  all: move/lfilledP in Hfill; inversion Hfill; subst.
  all: try destruct ref.
  all: try by
    lazymatch goal with
    | HH : _ = [_;_] |- _ => symmetry in HH; rewrite separate1 in HH; apply first_values in HH as (? & ? & ?); try rewrite /= const_const; try rewrite /= H
    end.
  all: try by
    lazymatch goal with
    | H : _ = [_;_;_] |- _ => symmetry in H; rewrite separate2 in H; apply first_values in H as (? & ? & ?); repeat rewrite /= const_const
    end.
    all: try by
    lazymatch goal with
    | H : _ = [_;_;_;_] |- _ => symmetry in H; rewrite separate3 in H; apply first_values in H as (? & ? & ?); repeat rewrite /= const_const
    end.
   all: try by
    lazymatch goal with
    | H : _ = [_] |- _ => symmetry in H; rewrite -(app_nil_l [_]) in H; apply first_values in H as (? & ? & ?)
    end.
   all: try by
    lazymatch goal with
    | H : _ = (_ ++ [_])%SEQ |- _ => apply first_values in H as (? & ? & ?); try apply v_to_e_is_const_list
    end.
    all: try by
    lazymatch goal with
    | H : _ = (_ ++ [_;_])%SEQ |- _ =>
        symmetry in H; rewrite separate1 -cat_app catA in H; apply first_values in H as (? & ? & ?); try apply const_list_concat; try apply v_to_e_is_const_list
    end.
    all: try lazymatch goal with
           | H : (?vs ++ _ :: _)%SEQ = [_] |- _ => destruct vs; last (by destruct vs); inversion H; subst
           end.
    all: try by
      lazymatch goal with
      | H : lfilledInd _ _ _ _ |- _ => move/lfilledP in H; apply lfilled_const in H as [??]
      end .
    all: try by left.
    all: try by
      apply hfilled_to_llfill in H as [llh Hllh];
    move/lfilledP in H6;
    edestruct lfilled_llfill_first_values as (? & ?);
      try (instantiate (3 := []); exact H6);
      try (instantiate (2 := []); exact Hllh).
    all: try by
      apply hfilled_to_llfill in H2 as [llh Hllh];
    move/lfilledP in H8;
    edestruct lfilled_llfill_first_values as (? & ?);
      try (instantiate (3 := []); exact H8);
      try (instantiate (2 := []); exact Hllh).
    all: try by
      apply hfilled_to_llfill in H2 as [llh Hllh];
    move/lfilledP in H9;
    edestruct lfilled_llfill_first_values as (? & ?);
      try (instantiate (3 := []); exact H9);
      try (instantiate (2 := []); exact Hllh).
Qed. 

