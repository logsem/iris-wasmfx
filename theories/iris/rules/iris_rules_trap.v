From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export iris_rules_control.

Set Bullet Behavior "Strict Subproofs".

Section trap_rules.
  Context `{!wasmG Σ}.

  Lemma ewp_trap (E : coPset) Ψ (Φ : iris.val -> frame -> iProp Σ) (vs1 es2 : iris.expr) f:
    const_list vs1 ->
    Φ trapV f -∗
    EWP vs1 ++ [AI_trap] ++ es2 UNDER f @ E <| Ψ |> {{ v ; f, Φ v f }}.
  Proof.
    iLöb as "IH" forall (E vs1 es2 f). 
    iIntros (Hconst) "HΦ".
    destruct (iris.to_val (vs1 ++ [AI_trap] ++ es2)) eqn:Hsome.
    { destruct vs1,es2 => //;[|by erewrite to_val_not_trap_interweave in Hsome;auto..].
      rewrite app_nil_l app_nil_r.
      iApply ewp_value;[|iFrame]. done. }
    assert (to_eff (vs1 ++ [AI_trap] ++ es2) = None) as Hsome'.
    { apply to_eff_cat_None2 => //.
      apply to_eff_cat_None1 => //. } 
    iApply ewp_unfold.
    repeat rewrite /ewp_pre /=.
    rewrite Hsome Hsome'.
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplit.
    { iPureIntro.
      eexists _,[AI_trap],(_,_,_),_.
      repeat split;eauto.
      eapply r_simple,rs_trap.
      2: instantiate (1 := LH_base vs1 es2);apply lfilled_Ind_Equivalent;by constructor.
      destruct vs1,es2 => //; destruct vs1 => //. }
    { iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls".
      iIntros (e2 σ2 ?? Hstep).
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
      destruct f; iApply ("IH" with "[] HΦ"). auto.
    }
  Qed.

(* Cannot seem to prove this: problem with the frame resource in the to_eff=Some case
 UPD: try again with fram baked in? *)
(*
  Lemma ewp_seq_trap (E : coPset) (es1 es2 : language.expr wasm_lang) f Φf Ψ :
(*    to_eff es2 = None -> *)
     EWP es1 UNDER f @ E <| Ψ |> {{ w, ⌜w = trapV⌝ ; Φf }}
     ⊢ EWP (es1 ++ es2) UNDER f @ E <| Ψ |> {{ w, ⌜w = trapV⌝ ; Φf }}.
  Proof.
    iLöb as "IH" forall (E es1 es2 f Φf ).
    iIntros (* Hes2 *) "Hes1". 
    repeat rewrite ewp_unfold /ewp_pre.
    destruct (iris.to_val (es1 ++ es2)) as [vs|] eqn:Hetov.
    { eapply lfilled_to_val_app with (i:=0) (lh:=LH_base [] []) in Hetov as HH.
      2: cbn;erewrite app_nil_r;by apply/eqP. 
      destruct HH as [vs' [Hvs' Hfilled']].
      rewrite Hvs'.
      iMod "Hes1" as "[-> Hf]". iFrame. 
      apply to_val_trap_is_singleton in Hvs' as ->.
      apply to_val_AI_trap_Some_nil in Hetov as Heq. subst es2.
      rewrite app_nil_r in Hetov.
      destruct vs => //.
    }
    destruct (to_eff (es1 ++ es2)) as [e|] eqn:Hetof.
    { destruct e => //=.
      - eapply lfilled_to_eff_app_sus in Hetof as HH; last first.
        2:{ instantiate (3 := LH_base [] []).
            instantiate (3 := 0).
            rewrite /lfilled /lfill /= app_nil_r //. }
        constructor.
        destruct HH as [[Hes1 Hes2'] | [(esv & shin & shout & -> & Hes2' & Hout & Htrans) | (shin & shout & Hin & Hout & Htrans)]].
        + edestruct const_list_to_val as (vsn & Htv & Hvsn).
          apply const_list_concat. exact Hes1. exact Hes2'.
          rewrite Htv in Hetov => //.
        + edestruct const_list_to_val as (?&?&?); first apply v_to_e_is_const_list.
          erewrite H.
          waaaat
          iDestruct "Hes1" as "[% ?]".
          rewrite Hes2' in Hes2 => //. 
        + destruct (to_val es1) eqn:Habs; first by exfalso; eapply to_val_to_eff.
          rewrite Hin.
          iDestruct "Hes1" as (Ξ) "[HΞ H]".
          iFrame. iIntros (w) "Hw".
          iSpecialize ("H" with "Hw").
          iNext.
          simpl in Hout. inversion Hout; subst.
          iSimpl. rewrite sus_push_const_nil.
          rewrite sus_append_nil.
          rewrite sus_push_const_nil.
          rewrite susfill_sus_append.
          iApply "IH". done. iExact "H".
      - eapply lfilled_to_eff_app_sw in Hetof as HH; last first.
        2:{ instantiate (3 := LH_base [] []).
            instantiate (3 := 0).
            rewrite /lfilled /lfill /= app_nil_r //. }
        constructor.
        destruct HH as [[Hes1 Hes2'] | [(esv & shin & shout & -> & Hes2' & Hout & Htrans) | (shin & shout & Hin & Hout & Htrans)]].
        + edestruct const_list_to_val as (vsn & Htv & Hvsn).
          apply const_list_concat. exact Hes1. exact Hes2'.
          rewrite Htv in Hetov => //.
        + rewrite Hes2' in Hes2 => //. 
        + destruct (to_val es1) eqn:Habs; first by exfalso; eapply to_val_to_eff.
          rewrite Hin.
          iDestruct "Hes1" as (Ξ) "[HΞ H]".
          iFrame. iIntros (w) "Hw".
          iSpecialize ("H" with "Hw").
          iNext.
          simpl in Hout. inversion Hout; subst.
          iSimpl. rewrite sw_push_const_nil.
          rewrite sw_append_nil.
          rewrite sw_push_const_nil.
          rewrite swfill_sw_append.
          iApply "IH". done. iExact "H".
      - eapply lfilled_to_eff_app_thr in Hetof as HH; last first.
        2:{ instantiate (3 := LH_base [] []).
            instantiate (3 := 0).
            rewrite /lfilled /lfill /= app_nil_r //. }
        constructor.
        destruct HH as [[Hes1 Hes2'] | [(esv & shin & shout & -> & Hes2' & Hout & Htrans) | (shin & shout & Hin & Hout & Htrans)]].
        + edestruct const_list_to_val as (vsn & Htv & Hvsn).
          apply const_list_concat. exact Hes1. exact Hes2'.
          rewrite Htv in Hetov => //.
        + rewrite Hes2' in Hes2 => //. 
        + destruct (to_val es1) eqn:Habs; first by exfalso; eapply to_val_to_eff.
          rewrite Hin.
          iDestruct "Hes1" as (Ξ) "[HΞ H]".
          iFrame. 
    } 
    
    (* Ind *)
    iIntros (σ) "Hσ".
    destruct (iris.to_val es1) as [vs|] eqn:Hes.
    { apply of_to_val in Hes as <-.
      iMod "Hes1" as "[-> Hf]".
(*      iMod ("Hes1" with "Hf") as "[%Heq Hf]". subst. *)
      iApply fupd_frame_l.
      iSplit.
      - iPureIntro.
        unfold reducible, reducible.
        eexists _,[AI_trap],(_,_,_),_.
        repeat split;eauto.
        eapply r_simple,rs_trap.
        2: instantiate (1 := LH_base [] es2);apply lfilled_Ind_Equivalent;by constructor.
        destruct es2 => //. 
      - iApply fupd_mask_intro;[solve_ndisj|].
        iIntros "Hcls".
        iIntros (e2 σ2 ?? Hstep).
        iModIntro. iNext. iModIntro.
        iMod "Hcls". iModIntro.
        assert (lfilled 0 (LH_base [] es2) [AI_trap] (of_val trapV ++ es2)) as Hfill.
        { apply lfilled_Ind_Equivalent. constructor. done. }
        simpl in *. destruct Hstep as [Hstep _].
        eapply trap_reduce_length in Hstep as Hred;[|apply Hfill].
        destruct Hred as (? & ? & _ & Hfill' & Heq). simplify_eq.
        apply lfilled_Ind_Equivalent in Hfill'. inversion Hfill';subst.
        iFrame. 
        erewrite app_assoc.
        iApply "IH".
        admit.
        iApply ewp_trap;eauto. by destruct f. }

    destruct (iris.to_eff es1) as [eff|] eqn:Hes'.
    { apply of_to_eff in Hes' as <-.
      destruct eff.
      all: simpl in Hetof.
      rewrite -susfill_sus_append in Hetof.
      fold (of_eff (susE vs i (sus_append sh es2))) in Hetof.
      rewrite to_of_eff in Hetof => //.
      rewrite -swfill_sw_append in Hetof.
      fold (of_eff (swE vs k tf i (sw_append sh es2))) in Hetof.
      rewrite to_of_eff in Hetof => //.
      rewrite -exnfill_exn_append in Hetof.
      fold (of_eff (thrE vs a i (exn_append sh es2))) in Hetof.
      rewrite to_of_eff in Hetof => //. } 

    iSpecialize ("Hes1" with "[$]").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      by apply append_reducible.
    - iIntros (e2 σ2 ?? HStep).
      apply prim_step_split_reduce_r in HStep ; last by [].
      destruct HStep as [[es'' [-> HStep]] | [n [m [lh [Hlf1 [Hlf2 Hσ]]]]]]; last (inversion Hσ; subst).
      + iSpecialize ("H2" $! es'' σ2 _ _ HStep).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        iModIntro.

        iDestruct "H2" as "[Hσ H]".
        iFrame. (* iSplit => //. *)
        iSpecialize "IH".
        iApply "IH".
        done.
        done.
      + move/lfilledP in Hlf1.
        inversion Hlf1; subst; clear Hlf1.
        assert (iris.prim_step es1 (σ,f_locs f, f_inst f) [] [AI_trap] (σ, f_locs f, f_inst f) []) as HStep2.
        { unfold iris.prim_step.
          repeat split => //.
          apply r_simple; eapply rs_trap => //.
          move => HContra; subst.
          by destruct n.
        }
        iSpecialize ("H2" $! [AI_trap] σ _ _ HStep2).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        iDestruct "H2" as "[Hσ H]".
        rewrite ewp_unfold /ewp_pre /=.
        iMod "H" as "[_ Hf1]".
        iFrame. 
        iModIntro. 
        erewrite cons_middle.
        erewrite app_assoc.
        iApply "IH" .
        admit.
        iApply ewp_trap;auto. }
  Qed. 

  Lemma ewp_val_trap (E : coPset) v0 (es1 : language.expr wasm_lang) f f' Ψ :
    ↪[frame] f ∗
     (↪[frame] f -∗ EWP es1 @ E <| Ψ |> {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }})
     ⊢ EWP ((AI_const v0) :: es1) @ E <| Ψ |> {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }}.
  Proof.
  iLöb as "IH" forall (v0 es1 f f').
  iIntros "(Hntrap & H)".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { repeat rewrite ewp_unfold /ewp_pre /= Hes.
    iApply fupd_ewp.
    unfold to_val in Hes; unfold to_eff => //=.
    rewrite merge_prepend to_val_instr_AI_const.
    destruct (merge_values _) => //.
    inversion Hes; subst => //.
    destruct vs => //. 
    iMod ("H" with "Hntrap") as "[%Hcontr Hf]". subst.
    apply to_val_trap_is_singleton in Hes as ->.
    rewrite -(app_nil_r [AI_trap]). rewrite separate1.
    iApply (ewp_trap with "[] [Hf]");auto.
    rewrite /= const_const //.
  }
  destruct (to_eff es1) as [e|] eqn:Hes'.
  { rewrite ewp_unfold /ewp_pre /= Hes Hes'.
    rewrite ewp_unfold /ewp_pre.
    unfold to_val, to_eff.
    rewrite merge_prepend to_val_instr_AI_const.
    unfold to_eff in Hes'.
    destruct (merge_values _) => //.
    inversion Hes'; subst.
    destruct e => //=.
    - iDestruct ("H" with "Hntrap") as (?) "[Hf H]".
      iFrame.
      iIntros "?"; iDestruct ("H" with "[$]") as (Ξ) "[HΞ H]".
      iFrame.
      iIntros (w) "Hw".
      iSpecialize ("H" with "Hw").
      iNext.
      rewrite susfill_sus_push_const.
      iSimpl.
      iApply "IH".

  }
  repeat rewrite ewp_unfold /ewp_pre /= Hes.
    iApply ewp_unfold. rewrite /ewp_pre /=.
    rewrite to_val_cons_None//.
    iIntros (?????) "?".
    iDestruct ("H" with "[$]") as "H".
    iSpecialize ("H" $! σ1 ns κ κs nt with "[$]").
    iMod "H" as "[%Hred H]".
    iModIntro.
    iSplit.
    { iPureIntro.
      destruct s => //. rewrite separate1.
      eapply prepend_reducible;intros;eauto. all: done. }
    iIntros (es2 σ2 HStep).
    rewrite separate1 in HStep.
    apply prim_step_obs_efs_empty in HStep as Heq. simplify_eq.
    apply reduce_ves in HStep as [[-> Hstep] | [lh [lh' [Hfill1 [Hfill2 ->]]]]].
    { iSpecialize ("H" $! _ _ _ Hstep).
      repeat (iMod "H"; iModIntro; try iNext).
      iDestruct "H" as "[$ Ha]".
      iDestruct "Ha" as (a) "[Hf [Ha _]]".
      iExists _. iFrame. simpl.
      iSplit => //. iIntros "Hf".
      iApply "IH". iFrame. }
    { apply lfilled_Ind_Equivalent in Hfill1.
      apply lfilled_Ind_Equivalent in Hfill2.
      inversion Hfill1;inversion Hfill2;simplify_eq.
      assert (iris.prim_step (vs0 ++ [AI_trap] ++ es'0)%SEQ σ2 [] [AI_trap] σ2 []) as Hstep'.
      { destruct σ2 as [[? ?]?]. split => //.
        apply r_simple; eapply rs_trap => //.
        2: apply lfilled_Ind_Equivalent;constructor=> //.
        destruct vs0;[|destruct vs0 => //].
        destruct es'0;[|destruct es'0 => //].
        erewrite app_nil_l, app_nil_r in Hes. done.
      }
      iSpecialize ("H" $! _ _ _ Hstep').
      repeat (iMod "H"; iModIntro; try iNext).
      iDestruct "H" as "[$ Ha]".
      iDestruct "Ha" as (a) "[Hf [Ha _]]".
      iExists _. iFrame. simpl.
      iSplit => //. iIntros "Hf".
      iDestruct ("Ha" with "Hf") as "Ha".
      rewrite ewp_unfold /ewp_pre /=.
      iMod "Ha" as "[_ Hf]".
      erewrite cons_middle.
      iApply ewp_trap;auto. } 
    auto.
  }
  Qed. 
      
  Lemma ewp_val_app_trap' (E : coPset) vs (es : language.expr wasm_lang) f f' :
    ↪[frame] f ∗
     (↪[frame] f -∗ EWP es @ NotStuck ; E {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }}%I)
     ⊢ EWP ((v_to_e_list vs) ++ es) @ E <| Ψ |> {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }}%I.
  Proof.
    iInduction vs as [|c vs] "IH" forall (s E es).
    { simpl.
      iIntros "[Hf HWP]".
      destruct s.
      2: iApply ewp_stuck_weaken.
      all: iDestruct ("HWP" with "Hf") as "HWP".
      all: iApply (ewp_wand with "HWP").
      all: iIntros (v).
      all: destruct v => /=.
      all: iIntros "HΦ" => //.
    }
    { iIntros "[Hf HWP]".
      iSimpl.
      iApply ewp_val_trap.
      iFrame. iIntros "Hf".
      iApply ("IH" $! _ _ _ with "[Hf HWP]") => //=.
      iFrame.
    }
  Qed. 
  
  Lemma ewp_val_app_trap (E : coPset) vs v' (es : language.expr wasm_lang) f f' :
    iris.to_val vs = Some (immV v') ->
    ↪[frame] f ∗
     (↪[frame] f -∗ EWP es @ NotStuck ; E {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f'}}%I)
     ⊢ EWP (vs ++ es) @ E <| Ψ |> {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }}%I.
  Proof.
    iIntros "%Hves [Hf Hwp]".
    apply iris.of_to_val in Hves; subst.
    iApply ewp_val_app_trap'.
    by iFrame.
  Qed. 

  Lemma ewp_label_trap s E LI vs n es' es'' f f':
    const_list vs ->
    ↪[frame] f -∗
    (↪[frame] f -∗ EWP LI @ E {{ w, ⌜w = trapV⌝ ∗  ↪[frame]f' }}) -∗
    EWP vs ++ [AI_label n es' LI] ++ es'' @ E <| Ψ |> {{ w, ⌜w = trapV⌝ ∗  ↪[frame]f' }}.
  Proof.
    iLöb as "IH" forall (vs LI n es' f f' es'' s).
    iIntros (Hconst) "Hf Hcont".
    destruct (iris.to_val LI) eqn:He.
    { iDestruct ("Hcont" with "Hf") as "Hcont".
      iDestruct (ewp_unfold with "Hcont") as "Hcont".
      rewrite /ewp_pre /= He.
      iMod "Hcont" as "[%Hcontr Hf]". subst.
      apply to_val_trap_is_singleton in He as ->.
      apply const_list_to_val in Hconst as [v Hv].
      iApply ewp_val_app_trap;eauto. iFrame.
      iIntros "Hf".
      rewrite separate1.
      iApply ewp_seq_trap. iFrame. iIntros "Hf".
      iApply (ewp_label_trap with "Hf");auto. }
    { apply const_list_to_val in Hconst as [v Hv].
      iApply ewp_val_app_trap;eauto. iFrame.
      iIntros "Hf".
      iApply ewp_seq_trap. iFrame. iIntros "Hf".
      iDestruct ("Hcont" with "Hf") as "Hcont".
      iDestruct (ewp_unfold with "Hcont") as "Hcont".
      iApply ewp_unfold.
      rewrite /ewp_pre /= He.
      rewrite to_val_None_label//.
      iIntros (σ ns κ κs nt) "Hσ".
      iSpecialize ("Hcont" $! σ 0 [] [] 0).
      iDestruct ("Hcont" with "[$]") as "H".
      iMod "H" as "[%Hred H]".
      iModIntro.
      assert (lfilled 1 (LH_rec [] n es' (LH_base [] []) []) (LI ++ []) [AI_label n es' LI]) as Hfill.
      { apply lfilled_Ind_Equivalent.
        rewrite -(app_nil_l [AI_label n es' LI]) -(app_nil_r [AI_label n es' LI]).
        constructor=> //.
        apply lfilled_Ind_Equivalent. cbn. erewrite app_nil_r, app_nil_r. by rewrite eqseqE. }
      iSplit.
      { iPureIntro.
        unfold reducible, reducible.
        destruct Hred as [? [? [? [? ?]]]].
        exists [], [AI_label n es' x0],x1,[].
        destruct x1 as [[ ? ?] ?].
        destruct σ as [[ ? ?] ?].
        split => //.
        eapply r_label. apply H.
        erewrite app_nil_r in Hfill. apply Hfill.
        apply lfilled_Ind_Equivalent.
        rewrite -(app_nil_l [AI_label n es' x0]) -(app_nil_r [AI_label n es' x0]).
        constructor=> //.
        apply lfilled_Ind_Equivalent. cbn. by rewrite eqseqE app_nil_r. }
      iIntros (e2 σ2 Hstep).
      apply prim_step_obs_efs_empty in Hstep as Heq. simplify_eq.
      
      eapply lfilled_prim_step_split_reduce_r in Hstep as Hstep';[|eauto|auto].
      destruct Hstep' as [[e' [Hstep' Hfill']]|[[lh Hfill'] ->]].
      { apply lfilled_Ind_Equivalent in Hfill'. inversion Hfill';subst.
        inversion H8;simplify_eq.
        apply prim_step_obs_efs_empty in Hstep as Heq;simplify_eq.
        iSpecialize ("H" $! _ _ _ Hstep').
        repeat (iMod "H"; iModIntro; try iNext).
        destruct σ2 as [[ ??]?].
        iDestruct ("H") as "[$ H]".
        iDestruct "H" as (f0) "[Hf [H _]]".
        iExists f0. iFrame.
        iSplit => //. iIntros "Hf".
        repeat erewrite app_nil_r,app_nil_l. erewrite app_nil_r.
        iDestruct ("IH" $! [] _ _ es' _ _ [] with "[] Hf H") as "H";auto. }
      { destruct σ2 as [[ ? ?] ?].
        set (σ2 := (s0,l,i)).
        destruct Hstep as [Hstep _].
        erewrite app_nil_r in Hfill.
        eapply lfilled_trans in Hfill as Hfillf; [|apply Hfill'].
        destruct Hfillf as [lh'' Hlh''].
        eapply trap_reduce_nested in Hlh'' as [Heq _];[|eauto].
        destruct Heq as [lh' [j [Hj Hle]]].
        apply lfilled_Ind_Equivalent in Hfill'.
        inversion Hfill';subst.
        assert (iris.prim_step (vs0 ++ [AI_trap] ++ es'0)%SEQ σ2 [] [AI_trap] σ2 []) as Hstep'.
        { destruct σ2 as [[ ? ?] ?].
          split => //.
          eapply r_simple,rs_trap.
          2: instantiate (1 := LH_base vs0 es'0);apply lfilled_Ind_Equivalent;by constructor.
          destruct vs0,es'0 => //; destruct vs0 => //. }
        iSpecialize ("H" $! _ _ _ Hstep').
        repeat (iMod "H"; iModIntro; try iNext).
        iDestruct "H" as "[$ H]".
        iDestruct "H" as (a) "[Hf [H _]]".
        iExists _. iFrame. iSplit => //.
        iIntros "Hf".
        iDestruct ("H" with "Hf") as "H".
        iDestruct (ewp_unfold with "H") as "H".
        rewrite /ewp_pre /=. iMod "H" as "[_ Hf]".
        assert (j = 0 ∨ j = 1) as [-> | ->];[lia|..].
        { apply lfilled_Ind_Equivalent in Hj;inversion Hj;subst.
          iApply ewp_trap;auto. }
        { apply lfilled_Ind_Equivalent in Hj;inversion Hj;subst. inversion H2;subst.
          iApply ("IH" with "[] Hf []");auto.
          iIntros "Hf".
          iApply ewp_trap;auto.
        }
      }
    }
  Qed.

  Lemma reduce_det_local_trap ws f ws' f' es2 n f0 :
    opsem.reduce ws f [AI_local n f0 [AI_trap]] ws' f' es2 ->
    es2 = [AI_trap] ∧ ws = ws' ∧ f = f'.
  Proof.
    remember [AI_local n f0 [AI_trap]] as es.
    revert es2. induction 1;simplify_eq.
    all: try destruct vcs => //.
    3 : by apply val_head_stuck_reduce in H.
    { remember [AI_local n f0 [AI_trap]] as es.
      revert e' H;induction 1;simplify_eq.
      all: try do 2 destruct vs => //.
      all: auto.
      apply lfilled_Ind_Equivalent in H1.
      inversion H1;simplify_eq.
      destruct vs0,vs => //. destruct vs => //.
      all : do 2 destruct vs0 => //. }
    { apply lfilled_Ind_Equivalent in H0.
      inversion H0;simplify_eq.
      all: apply lfilled_Ind_Equivalent in H1;inversion H1;simplify_eq.
      { destruct vs;inversion H2;simplify_eq;[|done].
        apply val_head_stuck_reduce in H.        
        destruct es;[done|]. inversion H4;simplify_eq.
        destruct es,es'0 => //.
        repeat erewrite app_nil_l + erewrite app_nil_r.
        apply IHreduce;auto. }
      { do 2 destruct vs => //. }
    }
  Qed.
  
  Lemma ewp_frame_trap (E : coPset) Ψ (Φ : iris.val -> frame -> iProp Σ) n f f0 :
    ↪[frame] f0 -∗
     ▷ (Φ trapV) -∗
     EWP [AI_trap] @ E FRAME n; f <| Ψ |> {{ v, Φ v ∗ ↪[frame] f0 }}.
  Proof.
    iIntros "Hframe H".
    rewrite ewp_frame_rewrite.
    iApply (ewp_lift_atomic_step with "[H Hframe]"); simpl ; trivial;eauto.
    iIntros (σ ns κ κs nt) "Hσ !>".
    iSplit.
    - iPureIntro.
      destruct s => //=.
      unfold language.reducible, language.prim_step => /=.
      exists [], [AI_trap], σ, [].
      destruct σ as [[ ws locs] inst].
      unfold iris.prim_step => /=.
      repeat split => //. apply r_simple. apply rs_local_trap; auto.
    - destruct σ as [[ws locs] inst].
      iIntros "!>" (es2 σ2 HStep) "!>".
      destruct σ2 as [[ ws' locs'] inst'].
      destruct HStep as (H & -> & ->). iFrame.
      (* iDestruct ("H" with "Hframe") as "[H Hframe]". iFrame. *)
      apply reduce_det_local_trap in H as [? [? ?]]. simplify_eq. iFrame. done.
  Qed.

  Lemma ewp_frame_trap_nested (E : coPset) n f f0 LI f' :
    iris.to_val [AI_local n f LI] = None ->
      ↪[frame] f0 -∗
     (↪[frame] f -∗ EWP LI @ E <| Ψ |> {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }}) -∗
     EWP LI @ E FRAME n; f <| Ψ |> {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f0 }}.
  Proof.
    iIntros (Hnone) "Hframe H".
    rewrite ewp_frame_rewrite.
    iLöb as "IH"
  forall (s E LI f f' f0 Hnone).
    destruct (iris.to_val (LI)) as [vs|] eqn:Hetov.
    { iApply (ewp_lift_atomic_step with "[H Hframe]"); simpl ; trivial;eauto.
      iIntros (σ ns κ κs nt) "Hσ".
      destruct σ as [[? ?] ?].
      iDestruct "Hσ" as "(?&?&?&?&Hff&?&?)".
      iDestruct (ghost_map_lookup with "Hff Hframe") as %Hlook.
      iMod (ghost_map_update f with "Hff Hframe") as "[Hff Hframe]".
      iDestruct ("H" with "Hframe") as "H".
      iDestruct (ewp_unfold with "H") as "H". rewrite /ewp_pre /= Hetov.
      iMod "H" as "[-> Hf]".
      apply to_val_trap_is_singleton in Hetov as ->.
      iModIntro.
      iSplit.
      - iPureIntro.
        destruct s => //=.
        unfold language.reducible, language.prim_step => /=.
        eexists [], [AI_trap], (_,_,_), [].
        unfold iris.prim_step => /=.
        repeat split => //. apply r_simple. apply rs_local_trap; auto.
      - iIntros "!>" (es2 σ2 HStep). destruct σ2 as [[ ws' locs'] inst'].
        iMod (ghost_map_update f0 with "Hff Hf") as "[Hff Hframe]".
        rewrite !insert_insert. iFrame.
        destruct HStep as (H & -> & ->).
        apply reduce_det_local_trap in H as [? [? ?]]. simplify_eq.
        rewrite lookup_insert in Hlook. inversion Hlook. iFrame.
        iModIntro. iSimpl. done. }
    { iApply ewp_unfold. unfold ewp_pre. simpl. rewrite Hnone.
      iIntros (σ ns κ κs nt) "Hσ".
      destruct σ as [[ ? ?] ?].
      iDestruct "Hσ" as "(H1&H2&H3&H4&Hff&H5&H6)".
      iDestruct (ghost_map_lookup with "Hff Hframe") as %Hlook.
      rewrite lookup_insert in Hlook. inversion Hlook.
      iMod (ghost_map_update f with "Hff Hframe") as "[Hff Hframe]".
      iSpecialize ("H" with "Hframe"). rewrite insert_insert.
      destruct f.
      iDestruct (ewp_unfold with "H") as "H". rewrite /ewp_pre /= Hetov.
      iSpecialize ("H" $! (s0,f_locs,f_inst) 0 [] [] 0).
      iDestruct ("H" with "[$H1 $H2 $H3 $H4 $H5 $H6 $Hff]") as "H".
      iMod "H" as "[%Hred H]".
      iModIntro.

      iSplit.
      { iPureIntro. destruct s => //.
        unfold reducible, reducible.
        destruct Hred as [? [? [? ?]]].
        destruct x1 as [[?  ?] ?].
        destruct H as [? (H & -> & ->)].
        
        eexists [], [AI_local n {| f_locs := l0; f_inst := i0 |} x0],(_,_,_),[].
        split => //. eapply r_local. eauto. }
      iIntros (e2 σ2 Hstep).
      destruct σ2 as [[ws' locs'] inst'].
      destruct Hstep as [H [-> _]].
      apply reduce_det_local in H as [? [? [? [? ?]]]];[|auto]. subst e2.
      destruct x0.
      iSpecialize ("H" $! x (ws',f_locs0,f_inst0) [] with "[]").
      { iPureIntro. split;auto. }
      repeat iMod "H". iModIntro. iNext.
      repeat iMod "H". iDestruct "H" as "[H Hf]".
      iDestruct "Hf" as (f1) "[Hf Hcont]".
      iDestruct "H" as "(H1&H2&H3&H4&Hff&H5&H6)".
      iDestruct (ghost_map_lookup with "Hff Hf") as %Hlook'.
      rewrite lookup_insert in Hlook'. inversion Hlook'.
      iDestruct "Hcont" as "[Hcont _]".

      destruct (iris.to_val [AI_local n {| f_locs := f_locs0; f_inst := f_inst0 |} x]) eqn:Hetov'.
      { 
        iDestruct ("Hcont" with "Hf") as "Hx".
        iDestruct (ewp_unfold with "Hx") as "Hx".
        apply to_val_local_inv in Hetov' as Heq.
        destruct Heq as [tf [h [w [vh Heq]]]]. subst v.
        apply to_val_call_host_rec_local in Hetov' as Heq.
        destruct Heq as [LI' [Heq HLI]].
        simpl in Heq. simplify_eq.
        rewrite /ewp_pre /= HLI.
        iMod "Hx" as "[%Hcontr Hf]". done.
      }
      
      iMod (ghost_map_update {| f_locs := l; f_inst := i |} with "Hff Hf") as "[Hff Hframe]".
      rewrite insert_insert.
      simpl. iApply fupd_mask_intro_subseteq;[solve_ndisj|].
      iFrame "H1 H2 H3 H4 H5 H6". simplify_eq. iFrame "Hff".
      iExists _. iFrame. iSplit => //. iIntros "Hframe".
      iDestruct ("IH" with "[] Hframe Hcont") as "Hcont".
      all: auto.
    }
  Qed.

    
  Lemma ewp_seq_trap_ctx (E : coPset) (es1 es2 : language.expr wasm_lang) f f' i lh :
    ↪[frame] f ∗
     (↪[frame] f -∗ EWP es1 @ NotStuck; E {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }})
     ⊢ EWP (es1 ++ es2) @ E CTX i; lh <| Ψ |> {{ w, ⌜w = trapV⌝ ∗ ↪[frame] f' }}.
  Proof.
    iIntros "[Hf Hes1]".
    iInduction i as [|i] "IH" forall (E es1 es2 lh f f' s).
    { iIntros (LI Hfilled).
      apply lfilled_Ind_Equivalent in Hfilled.
      inversion Hfilled;subst.
      erewrite app_assoc.
      iApply (ewp_seq_trap with "[Hf Hes1]"). iFrame.
      iIntros "Hf".
      apply const_list_to_val in H as Hv.
      destruct Hv as [v Hv].
      iApply (ewp_val_app_trap with "[-]");eauto.
      iFrame. iIntros "Hf".
      iApply (ewp_seq_trap with "[-]");eauto.
      iFrame. }
    { iIntros (LI Hfilled).
      apply lfilled_Ind_Equivalent in Hfilled.
      inversion Hfilled;subst.
      iApply (ewp_label_trap with "Hf");auto.
      iIntros "Hf".
      iDestruct ("IH" $! _ _ _ _ _ _ NotStuck with "Hf Hes1") as "H".
      apply lfilled_Ind_Equivalent in H1.
      iSpecialize ("H" $! _ H1). auto.
    }
  Qed.


  Lemma ewp_trap_ctx (E : coPset) f i lh vs es :
    const_list vs ->
    ↪[frame] f -∗
    EWP vs ++ [AI_trap] ++ es @ E CTX i; lh <| Ψ |> {{ v, ⌜v = trapV⌝ ∗ ↪[frame] f }}.
  Proof.
    iIntros (Hconst) "Hf". rewrite app_assoc.
    iApply ewp_seq_trap_ctx.
    iFrame. iIntros "Hf".
    apply const_list_to_val in Hconst as [v Hvs].
    iApply ewp_val_app_trap;eauto.
    iFrame. iIntros "Hf". iApply ewp_value;eauto. done.
  Qed.

          
(* Sequencing rule which is always allowed to trap *)
(* This rule is useful in particular for semantic type soundness, which allows traps *)
  Lemma ewp_seq_can_trap_ctx (E : coPset) Ψ (Φ Ψ : iris.val -> frame -> iProp Σ) (es1 es2 : language.expr wasm_lang) (i : nat) (lh : lholed) (Φf : frame -> iProp Σ) f :
    (((Ψ trapV ={E}=∗ ⌜False⌝)) ∗ (∀ f, ↪[frame] f ∗ Φf f -∗ Φ trapV) ∗ ↪[frame] f ∗
    (↪[frame] f -∗ EWP es1 @ NotStuck; E {{ w, (⌜w = trapV⌝ ∨ Ψ w) ∗ ∃ f0, ↪[frame] f0 ∗ Φf f0 }}) ∗
    ∀ w f0, Ψ w ∗ ↪[frame] f0 ∗ Φf f0 -∗ EWP (iris.of_val w ++ es2) @ E CTX i; lh <| Ψ |> {{ v, Φ v }})%I
     ⊢ EWP (es1 ++ es2) @ E CTX i; lh <| Ψ |> {{ v, Φ v }}.
  Proof.
    iLöb as "IH" forall (s E es1 es2 Φ Ψ i lh f).
{ iIntros "[Hntrap [Ht [Hf [Hes1 Hes2]]]]".
  iIntros (LI Hfilled).
  repeat rewrite ewp_unfold /ewp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val LI) as [vs|] eqn:Hetov.
  { iApply ewp_unfold. rewrite /ewp_pre /= Hetov.
    eapply lfilled_to_val_app in Hetov as HH;eauto.
    destruct HH as [vs' [Hvs' Hfilled']].
    unfold to_val in Hvs'.
    rewrite Hvs'.
    iMod ("Hes1" with "Hf") as "[Hes1 Hf]".
    iDestruct "Hes1" as "[-> | Hes1]".
    { apply to_val_trap_is_singleton in Hvs' as ->.
      destruct es2;cycle 1.
      { assert (to_val ([AI_trap] ++ a :: es2) = None) as Hnone.
        rewrite -(app_nil_l [AI_trap]) -app_assoc; apply to_val_not_trap_interweave;auto.
        eapply to_val_None_lfilled in Hnone;[|eauto]. congruence. }
      erewrite app_nil_r in Hfilled'.
      eapply lfilled_to_val_0 in Hfilled' as Heq;eauto. subst i.
      apply lfilled_Ind_Equivalent in Hfilled. inversion Hfilled;simplify_eq.
      destruct vs0,es'.
      erewrite app_nil_l, app_nil_r, app_nil_r in Hetov.
      destruct vs;try done. iDestruct "Hf" as (?) "[? ?]". iApply "Ht"; by iFrame. eauto.
      all: rewrite to_val_not_trap_interweave in Hetov;try done;auto.
    }
    iDestruct "Hf" as (f0) "[Hf Hfv]".
    iSpecialize ("Hes2" with "[$Hf $Hfv $Hes1]").
    iSpecialize ("Hes2" $! _ Hfilled').
    iDestruct (ewp_unfold with "Hes2") as "Hes2".
    rewrite /ewp_pre /= Hetov.
    iFrame.
  }
  {
    (* Ind *)
    destruct (iris.to_val es1) as [vs|] eqn:Hes.
    { apply of_to_val in Hes as <-.
      iMod ("Hes1" with "Hf") as "[Hes1 Hf]".
      iDestruct "Hes1" as "[-> | Hes1]".
      { iDestruct "Hf" as (f0) "[Hf Hfv]".
        iPoseProof (ewp_trap_ctx s E f0 i lh [] es2 with "Hf") as "HH";auto.
        iSpecialize ("HH" $! LI with "[]");auto.
        iApply (ewp_wand with "HH").
        iIntros (v) "[-> Hf]". iFrame. iApply "Ht";iFrame. (* iExists _. iFrame.  *)
      }
      { iApply ewp_unfold. rewrite /ewp_pre /= Hetov.
        iIntros (σ ns κ κs nt) "Hσ".
        iDestruct "Hf" as (f0) "[Hf Hfv]".
        iSpecialize ("Hes2" with "[$Hes1 $Hf $Hfv]").
        iSpecialize ("Hes2" $! _ Hfilled).
        iDestruct (ewp_unfold with "Hes2") as "Hes2"; rewrite /ewp_pre /=.
        
        rewrite Hetov.
        iSpecialize ("Hes2" $! σ ns κ κs nt with "[$]").
        iMod "Hes2" as "[%H1 H2]".
        iIntros "!>".
        iSplit.
        - iPureIntro. by apply H1. 
        - by iApply "H2".
      }
    }
    { iApply ewp_unfold. rewrite /ewp_pre /= Hetov.
      iIntros (σ ns κ κs nt) "Hσ".
      iSpecialize ("Hes1" with "[$]").
      iSpecialize ("Hes1" $! σ ns κ κs nt with "[$]").
      iMod "Hes1" as "[%H1 H2]".
      iModIntro.
      iSplit.
      - iPureIntro.
        destruct s => //.
        apply append_reducible with (es2:=es2) in H1;auto.
        eapply lfilled_reducible. apply Hfilled. auto.
      - iIntros (e2 σ2 HStep').
        eapply lfilled_prim_step_split_reduce_r in HStep' as Heq;[|apply Hfilled|apply H1].
        apply prim_step_obs_efs_empty in HStep' as Hemp. inversion Hemp;subst;clear Hemp.
        destruct Heq as [[e' [HStep'' Hlfilled']] | [[lh' Hlf] <-]].
        + apply prim_step_obs_efs_empty in HStep'' as Hemp. inversion Hemp;subst;clear Hemp.
          iSpecialize ("H2" $! e' σ2 [] HStep'').
          iMod "H2".
          repeat iModIntro.
          repeat iMod "H2".
          iModIntro.
          iDestruct "H2" as "(Hσ & Hes)".
          iDestruct "Hes" as (f1) "(Hf & Hes'' & Hefs)".
          iFrame. (* iExists _. iFrame. *) 
          iSplit => //.
          iIntros "Hf".
          iDestruct ("IH" with "[Hf Ht $Hntrap $Hes'' $Hes2 ]") as "Hcont". iFrame. by iApply "Hcont".
          
        + assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
          { unfold iris.prim_step.
            destruct σ as [[??]?].
            repeat split => //.
            apply r_simple; eapply rs_trap => //.
            move => HContra; subst.
            by simpl in Hes.
          }
          iSpecialize ("H2" $! [AI_trap] σ [] HStep2).
          iMod "H2".
          repeat iModIntro.
          repeat iMod "H2".
          destruct σ as [[? ?]?].
          iDestruct "H2" as "[Hσ H]".
          iDestruct "H" as (f') "(Hf1 & Hes'' & Hefs)".
          iModIntro => /=.
          iFrame. (* iExists _. iFrame. *) 
          iIntros "?"; iSpecialize ("Hes''" with "[$]").
          replace [AI_trap] with (iris.of_val trapV) => //=.
          iDestruct (ewp_unfold with "Hes''") as "Hes''".
          rewrite /ewp_pre /=. iMod "Hes''" as "[[_ | Hcontr] Hf]".
          2: { iApply fupd_wp. by iMod ("Hntrap" with "Hcontr") as "?". }
          apply lfilled_Ind_Equivalent in Hlf;inversion Hlf;subst.
          assert ((vs ++ [AI_trap] ++ es')%SEQ ++ es2 =
                    (vs ++ [AI_trap] ++ (es' ++ es2)))%list as Hassoc;[repeat erewrite app_assoc;auto|].
          rewrite Hassoc in Hfilled.
          apply lfilled_Ind_Equivalent in Hfilled.
          eapply lfilledInd_frame in Hfilled;auto.
          apply lfilled_Ind_Equivalent in Hfilled.
          destruct HStep' as [HStep' _].
          eapply trap_reduce_lfilled in HStep';eauto.
          destruct HStep' as [lh2 [j [Hlh' Hle]]].
          iDestruct "Hf" as (f0) "[Hf Hfv]".
          iPoseProof (ewp_trap_ctx s E f0 j _ [] [] with "Hf") as "HH";auto.
          iSpecialize ("HH" $! _ Hlh').
          iApply (ewp_wand with "HH").
          iIntros (v) "[-> Hf]". iApply "Ht"; iFrame.
} } }
  Qed.

  Lemma ewp_val_can_trap (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) (v0 : value) (es : language.expr wasm_lang) f Φf :
    ((Φ trapV ={E}=∗ ⌜False⌝) ∗ ↪[frame] f ∗
       (↪[frame] f -∗ EWP es @ NotStuck ; E {{ v, (⌜v = trapV⌝ ∨ (Φ (val_combine (immV [v0]) v))) ∗ ∃ f, ↪[frame] f ∗ Φf f }})
       ⊢ EWP ((AI_basic (BI_const v0)) :: es) @ E <| Ψ |> {{ v, (⌜v = trapV⌝ ∨ Φ v) ∗ ∃ f, ↪[frame] f ∗ Φf f }})%I.
  Proof.
  iLöb as "IH" forall (v0 es Φ f).
  iIntros "(Hntrap & H & Hf)".
  destruct (iris.to_val es) as [vs|] eqn:Hes.
  { destruct vs.
    { iApply ewp_unfold.
      repeat rewrite ewp_unfold /ewp_pre /=.      
      rewrite Hes. apply of_to_val in Hes as <-. rewrite to_val_cons_immV.
      iMod ("Hf" with "H") as "[[%Heq| HΦ] H]";try done.
      iModIntro. iFrame. }
    { apply to_val_trap_is_singleton in Hes as ->.
      repeat rewrite ewp_unfold /ewp_pre /=.
      iMod ("Hf" with "H") as "[[_|Hcontr] H]";cycle 1.
      { iApply fupd_wp. iMod ("Hntrap" with "Hcontr") as "?". done. }
      iDestruct "H" as (f0) "[Hf0 Hf0v]".
      iApply (ewp_wand  _ _ _ (λ v, ⌜v = trapV⌝ ∗ ↪[frame] f0)%I with "[Hf0]").
      { rewrite -(take_drop 1 [AI_basic (BI_const v0); AI_trap]);simpl take;simpl drop.
        rewrite -(app_nil_r [AI_trap]).
        iApply (ewp_trap with "[] Hf0");auto. }
      iIntros (v) "[-> H]". iSplitR;[|iExists _;iFrame]. by iLeft. }
    { iApply ewp_unfold.
      repeat rewrite ewp_unfold /ewp_pre /=.      
      rewrite Hes. apply of_to_val in Hes as <-; erewrite to_val_cons_brV;[|apply to_of_val].
      iMod ("Hf" with "H") as "[[%Heq| HΦ] H]";try done.
      iModIntro. iFrame. }
    { iApply ewp_unfold.
      repeat rewrite ewp_unfold /ewp_pre /=.      
      rewrite Hes. apply of_to_val in Hes as <-; erewrite to_val_cons_retV;[|apply to_of_val].
      iMod ("Hf" with "H") as "[[%Heq| HΦ] H]";try done.
      iModIntro. iFrame. }
     { iApply ewp_unfold.
      repeat rewrite ewp_unfold /ewp_pre /=.      
      rewrite Hes. apply of_to_val in Hes as <-; erewrite to_val_cons_callHostV;[|apply to_of_val].
      iMod ("Hf" with "H") as "[[%Heq| HΦ] H]";try done.
      iModIntro. iFrame. }
    
  }
  { iApply ewp_unfold.
    repeat rewrite ewp_unfold /ewp_pre /=.
    rewrite Hes to_val_cons_None //.
    iIntros (σ ns κ κs nt) "Hσ".
    iDestruct ("Hf" with "[$]") as "H".
    iSpecialize ("H" $! σ ns κ κs nt with "[$]").
    iMod "H".
    iModIntro.
    iDestruct "H" as "(%H1 & H)".
    iSplit.
    - iPureIntro.
      destruct s => //=.
      rewrite - cat1s.
      by eapply prepend_reducible; eauto.
    - iIntros (es2 σ2 HStep).
      rewrite -cat1s in HStep.
      eapply reduce_ves in H1; last by apply HStep.
      assert (κ = [] /\ efs = []) as [-> ->]; first by apply prim_step_obs_efs_empty in HStep; inversion HStep.
      destruct H1 as [[-> HStep2] | [lh1 [lh2 [Hlf1 [Hlf2 ->]]]]].
      + iSpecialize ("H" $! (drop 1 es2) σ2 [] HStep2).
        iMod "H".
        repeat iModIntro.
        repeat iMod "H".
        iModIntro.
        iDestruct "H" as "[Hσ H]".
        iDestruct "H" as  (f1) "(Hf1 & Hes & Hefs)".
        iSimpl.
        iFrame. (* iExists _. iFrame. *) 
        iSplit => //.
        iIntros "Hf".
        iApply "IH".
        by iFrame.
      + move/lfilledP in Hlf1.
        inversion Hlf1; subst; clear Hlf1.
        move/lfilledP in Hlf2.
        inversion Hlf2; subst; clear Hlf2.
        assert (iris.prim_step (vs0 ++ [AI_trap] ++ es'0) σ2 [] [AI_trap] σ2 []) as HStep2.
        { unfold iris.prim_step.
          destruct σ2 as [[??]?].
          repeat split => //.
          apply r_simple; eapply rs_trap => //.
          - move => HContra.
            by replace (vs0 ++ [AI_trap] ++ es'0)%SEQ with [AI_trap] in Hes.
          - apply/lfilledP.
            by apply LfilledBase.
        }
        iSpecialize ("H" $! [AI_trap] σ2 [] HStep2).
        iMod "H".
        repeat iModIntro.
        repeat iMod "H".
        iDestruct "H" as "[Hσ H]".
        iDestruct "H" as (f1) "(Hf1 & Hes & Hefs)".
        iFrame.
        iModIntro. (* iExists _. iFrame. *) 
        iSplit => //.
        iIntros "Hf".
        iSpecialize ("Hes" with "[$]").
        iDestruct (ewp_unfold with "Hes") as "Hes".
        rewrite /ewp_pre /=.
        iMod "Hes" as "[[_|Hcontr] Hf]";cycle 1.
        { iApply fupd_wp. by iMod ("Hntrap" with "Hcontr"). }
        iDestruct "Hf" as (f0) "[Hf0 Hf0v]".
        iApply (ewp_wand  _ _ _ (λ v, ⌜v = trapV⌝ ∗ ↪[frame] f0)%I with "[Hf0]").
        { rewrite separate1.
          iApply (ewp_trap with "[] Hf0");auto. }
        iIntros (v) "[-> H]". iSplitR;[|iExists _;iFrame]. by iLeft.
  }
  Qed.

  (* Some alternative formulations, useful for soundness proof *)

  Lemma ewp_val_can_trap_app' (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) vs (es : language.expr wasm_lang) f Φf :
    (□ ((Φ trapV ={E}=∗ ⌜False⌝))) ∗ ↪[frame] f ∗
                     (↪[frame] f -∗  EWP es @ NotStuck ; E {{ v, (⌜v = trapV⌝ ∨ (Φ (val_combine (immV vs) v))) ∗ ∃ f, ↪[frame] f ∗ Φf f }}%I)
                     ⊢ EWP ((v_to_e_list vs) ++ es) @ E <| Ψ |> {{ v, (⌜v = trapV⌝ ∨ Φ v) ∗ ∃ f, ↪[frame] f ∗ Φf f }}%I.
  Proof.
    iInduction vs as [|c vs] "IH" forall (Φ s E es).
    { simpl.
      iIntros "(#Hntrap & Hf & HWP)".
      destruct s.
      2: iApply ewp_stuck_weaken.
      all: iDestruct ("HWP" with "Hf") as "HWP".
      all: iApply (ewp_wand with "HWP").
      all: iIntros (v).
      all: destruct v => /=.
      all: iIntros "HΦ" => //.
      all: rewrite vh_push_const_nil + rewrite sh_push_const_nil + rewrite llh_push_const_nil.
      all: auto.
    }
    { iIntros "(#Hntrap & Hf & HWP)".
      iSimpl.
      iApply ewp_val_can_trap.
      iFrame. iSplitR => //. iIntros "Hf".
      iApply "IH" => //=.
      iSplit => //. iFrame. iIntros "Hf".
      iDestruct ("HWP" with "Hf") as "HWP".
      iApply (ewp_mono with "HWP").
      iIntros (vs') "HΦ".
      iSimpl. destruct vs';auto.
      all: rewrite -vh_push_const_app + rewrite -sh_push_const_app + rewrite -llh_push_const_app;auto.
    }
  Qed.

  Lemma ewp_val_return' (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) vs vs' es' es'' n f0 Φf :
    const_list vs ->
    ↪[frame] f0 -∗
     (↪[frame] f0 -∗ EWP vs' ++ vs ++ es'' @ E <| Ψ |> {{ v, Φ v ∗ ∃ f, ↪[frame] f ∗ Φf f }})
     -∗ EWP vs @ s; E CTX 1; LH_rec vs' n es' (LH_base [] []) es'' {{ v, Φ v ∗ ∃ f, ↪[frame] f ∗ Φf f }}.
  Proof.
    iIntros (Hconst) "Hf0 HWP".
    iLöb as "IH".
    iIntros (LI Hfill%lfilled_Ind_Equivalent).
    inversion Hfill;subst.
    inversion H8;subst.
    assert (vs' ++ [AI_label n es' ([] ++ vs ++ [])] ++ es''
            = ((vs' ++ [AI_label n es' ([] ++ vs ++ [])]) ++ es''))%SEQ as ->.
    { erewrite app_assoc. auto. }
    apply const_list_to_val in Hconst as [v1 Hv1].
    apply const_list_to_val in H7 as [v2 Hv2].
    eapply to_val_cat_inv in Hv1 as Hvv;[|apply Hv2].
    iApply (ewp_seq _ _ _ (λ v, (⌜v = immV (v2 ++ v1)⌝ ∗ ↪[frame] f0))%I).
    iSplitR; first by iIntros "(%H & ?)".
    iSplitR "HWP".
    - iApply ewp_val_app; first by apply Hv2.
      iSplit; first by iIntros "!> (%H & ?)".
      iApply (ewp_label_value with "[$]") => //=; first by erewrite app_nil_r; apply Hv1 .
    - iIntros (w) "(-> & Hf0)".
      erewrite iris.of_to_val => //.
      rewrite app_assoc.
      by iApply "HWP".
  Qed.

  Lemma ewp_val_can_trap_app (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) vs v' (es : language.expr wasm_lang) f Φf :
    iris.to_val vs = Some (immV v') ->
    (□ ((Φ trapV ={E}=∗ ⌜False⌝))) ∗ ↪[frame] f ∗
                     (↪[frame] f -∗ EWP es @ NotStuck ; E {{ v, (⌜v = trapV⌝ ∨ Φ (val_combine (immV v') v)) ∗ ∃ f, ↪[frame] f ∗ Φf f }})%I
                     ⊢ EWP (vs ++ es) @ E <| Ψ |> {{ v, (⌜v = trapV⌝ ∨ Φ v) ∗ ∃ f, ↪[frame] f ∗ Φf f }}%I.
  Proof.
    iIntros "%Hves [#Hntrap Hwp]".
    apply iris.of_to_val in Hves; subst.
    iApply ewp_val_can_trap_app'.
    by iFrame.
  Qed.
  

Lemma ewp_seq_can_trap_same_ctx Ψ (Φ Ψ : iris.val -> frame -> iProp Σ) (E : coPset) (es1 es2 : language.expr wasm_lang) f i lh :
    (Ψ trapV ={E}=∗ False) ∗ (Φ trapV) ∗ ↪[frame] f ∗
    (↪[frame] f -∗ EWP es1 @ NotStuck; E {{ w, (⌜w = trapV⌝ ∨ Ψ w) ∗ ↪[frame] f }}) ∗
    (∀ w, Ψ w ∗ ↪[frame] f -∗ EWP (iris.of_val w ++ es2) @ E CTX i; lh <| Ψ |> {{ v, Φ v ∗ ↪[frame] f }})%I
    ⊢ EWP (es1 ++ es2) @ E CTX i; lh <| Ψ |> {{ v, Φ v ∗ ↪[frame] f }}.
  Proof.
    iIntros "(HPsi & Hphi & Hf & Hes1 & Hes2)".
    iApply (ewp_wand_ctx _ _ _ (λ  v, Φ v ∗ ∃ f0, ↪[frame] f0 ∗ ⌜f0 = f⌝) with "[-]")%I;cycle 1.
    { iIntros (v) "[$ Hv]". iDestruct "Hv" as (f0) "[Hv ->]". iFrame. }
    iApply ewp_seq_can_trap_ctx.
    iFrame. iSplitR.
    { iIntros (f') "[Hf Heq]". iExists f';iFrame. iExact "Heq". }
    iSplitL "Hes1".
    { iIntros "Hf". iDestruct ("Hes1" with "Hf") as "Hes1".
      iApply (ewp_wand with "Hes1").
      iIntros (v) "[$ Hv]". iExists _. iFrame. eauto. }
    { iIntros (w f') "[H [Hf ->]]".
      iDestruct ("Hes2" with "[$]") as "Hes2".
      iApply (ewp_wand_ctx with "Hes2").
      iIntros (v) "[$ Hv]". iExists _. iFrame. eauto. }
  Qed.

Lemma ewp_seq_can_trap_same_empty_ctx Ψ (Φ Ψ : iris.val -> frame -> iProp Σ) (E : coPset) (es1 es2 : language.expr wasm_lang) f :
    (Ψ trapV ={E}=∗ False) ∗ (Φ trapV) ∗ ↪[frame] f ∗
    (↪[frame] f -∗ EWP es1 @ NotStuck; E {{ w, (⌜w = trapV⌝ ∨ Ψ w) ∗ ↪[frame] f }}) ∗
    (∀ w, Ψ w ∗ ↪[frame] f -∗ EWP (iris.of_val w ++ es2) @ E <| Ψ |> {{ v, Φ v ∗ ↪[frame] f }})%I
    ⊢ EWP (es1 ++ es2) @ E <| Ψ |> {{ v, Φ v ∗ ↪[frame] f }}.
  Proof.
    iIntros "(HPsi & Hphi & Hf & Hes1 & Hes2)".
    iApply ewp_wasm_empty_ctx.
    iApply ewp_seq_can_trap_same_ctx.
    iFrame.
    iIntros (w) "?".
    iApply ewp_wasm_empty_ctx.
    iApply "Hes2". done.
  Qed. *)

End trap_rules.
