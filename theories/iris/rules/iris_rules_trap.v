From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export iris_rules_control.

Set Bullet Behavior "Strict Subproofs".

Section trap_rules.
  Context `{!wasmG Σ}.

  Lemma ewp_trap (E : coPset) Ψ (Φ : iris.val0 -> frame -> iProp Σ) (vs1 es2 : expr0) f:
    const_list vs1 ->
    Φ trapV f -∗
    EWP vs1 ++ [AI_trap] ++ es2 UNDER f @ E <| Ψ |> {{ v ; f, Φ v f }}.
  Proof.
    iLöb as "IH" forall (E vs1 es2 f). 
    iIntros (Hconst) "HΦ".
    destruct (iris.to_val0 (vs1 ++ [AI_trap] ++ es2)) eqn:Hsome.
    { destruct vs1,es2 => //;[|by erewrite to_val_not_trap_interweave in Hsome;auto..].
      rewrite app_nil_l app_nil_r.
      iApply ewp_value;[|iFrame]. done. }
    assert (to_eff0 (vs1 ++ [AI_trap] ++ es2) = None) as Hsome'.
    { apply to_eff_cat_None2 => //.
      apply to_eff_cat_None1 => //. } 
    iApply ewp_unfold.
    repeat rewrite /ewp_pre /=.
    rewrite Hsome Hsome'.
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplit.
    { iPureIntro.
      eexists _,([AI_trap], _),_,_.
      repeat split;eauto.
      eapply r_simple,rs_trap.
      2: instantiate (1 := LH_base vs1 es2);apply lfilled_Ind_Equivalent;by constructor.
      destruct vs1,es2 => //; destruct vs1 => //. }
    { iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls".
      iIntros ([e2 ?] σ2 Hstep).
      iModIntro. iNext. iModIntro.
      iMod "Hcls". iModIntro.
      assert (lfilled 0 (LH_base vs1 es2) [AI_trap] (vs1 ++ (AI_trap :: es2))) as Hfill.
      { apply lfilled_Ind_Equivalent. constructor. done. } 

      simpl in *. destruct Hstep as [Hstep _].

      eapply trap_reduce_length in Hstep as Hred;[|apply Hfill].
      destruct Hred as (? & ? & _ & Hfill' & Heq).
      simplify_eq.
      iFrame. 
      apply lfilled_Ind_Equivalent in Hfill';inversion Hfill';subst.
      iApply ("IH" with "[] HΦ"). auto.
    }
  Qed.

 

End trap_rules.
