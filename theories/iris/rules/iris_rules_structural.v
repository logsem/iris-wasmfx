From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.language Require Export iris_ewp_ctx iris_ewp.
From Wasm.iris.helpers Require Export iris_properties.

Set Bullet Behavior "Strict Subproofs".

(* empty lists, frame and context rules *)
Close Scope byte_scope.
Section structural_rules.
Context `{!wasmG Σ}.



Lemma ewp_wasm_empty_ctx (E : coPset) (Ψ : effect_identifier -> iProt Σ) (Φ : iris.val -> iProp Σ) e :
  ⊢ EWP e @ E <| Ψ |> {{ Φ }} ∗-∗ EWP e @ E CTX_EMPTY <| Ψ |> {{ Φ }}.
Proof.
  iSplit.
  { iIntros "HWP". iIntros (LI Hfill%lfilled_Ind_Equivalent).
    inversion Hfill. subst. erewrite app_nil_l; erewrite app_nil_r. done. }
  { iIntros "HWP".
    iDestruct ("HWP" $! e with "[]") as "$".
    iPureIntro. cbn. rewrite app_nil_r eqseqE. apply eq_refl. }
Qed.

Lemma ewp_wasm_empty_ctx_frame (E : coPset) Ψ (Φ : iris.val -> iProp Σ) e n f :
  ⊢ EWP e @ E FRAME n; f <| Ψ |> {{ Φ }} ∗-∗ EWP e @ E FRAME n; f CTX_EMPTY <| Ψ |> {{ v, Φ v }}.
Proof.
  iSplit.
  { iIntros "HWP". iIntros (LI Hfill%lfilled_Ind_Equivalent).
    inversion Hfill. subst. erewrite app_nil_l; erewrite app_nil_r. done. }
  { iIntros "HWP".
    iDestruct ("HWP" $! e with "[]") as "$".
    iPureIntro. cbn. rewrite app_nil_r eqseqE. apply eq_refl. }
Qed.

Lemma ewp_nil (E : coPset) Ψ (Φ : iProp Σ) f :
  ↪[frame] f ∗ Φ ⊢ EWP [] @ E CTX_EMPTY <| Ψ |> {{ fun v => Φ }}%I.
Proof.
  iIntros "(Hframe & H)". iApply ewp_wasm_empty_ctx.
  rewrite ewp_unfold /ewp_pre /=. iFrame. eauto.
Qed.

Lemma ewp_val (E : coPset) Ψ (Φ : val -> iProp Σ) (v0 : value) (es : language.expr wasm_lang) :
  ((¬ Φ trapV) ∗
     EWP es @ E <| Ψ |> {{ v, (Φ (val_combine (immV [v0]) v))  }}
     ⊢ EWP (AI_const v0 :: es) @ E <| Ψ |> {{ v, Φ v }})%I.
Proof.
  iLöb as "IH" forall (v0 es Φ).
  iIntros "(Hntrap & H)".
  iApply ewp_unfold.               
  repeat rewrite ewp_unfold /ewp_pre /=.
  destruct (to_val es) as [vs|] eqn:Hes.
  - destruct vs.
    + apply of_to_val in Hes as <-.
      rewrite to_val_cons_immV. auto.
    + apply to_val_trap_is_singleton in Hes as ->.
      unfold to_val, to_eff.
      rewrite (separate1 (AI_const _)).
      rewrite merge_prepend.
      rewrite /= to_val_instr_AI_const.
      simpl.
      iIntros (?????) "?".
      iMod "H".
      by iSpecialize ("Hntrap" with "H").
    + erewrite to_val_cons_brV;eauto.
    + erewrite to_val_cons_retV;eauto.
    + erewrite to_val_cons_callHostV;eauto.
  - rewrite to_val_cons_None => //.
    destruct (iris.to_eff es) as [eff|] eqn:Hesf.
    + destruct eff.
      * erewrite to_eff_cons_susE; last done. 
        iDestruct "H" as (f) "[Hf H]".
        iFrame.
        iIntros "Hf".
        iDestruct ("H" with "Hf") as "(%Φ0 & HΨ & Hallw)".
        iExists Φ0.
        iFrame.
        iIntros (w) "Hw".
        iDestruct ("Hallw" with "Hw") as "Hres".
        rewrite susfill_sus_push_const /=.
        iApply ("IH" with "[$Hntrap $Hres]").
      * erewrite to_eff_cons_swE; last done.
        iDestruct "H" as (f) "[Hf H]".
        iFrame.
        iIntros "Hf".
        iDestruct ("H" with "Hf") as "(%Φ0 & HΨ & Hallw)".
        iExists Φ0.
        iFrame.
        iIntros (w) "Hw".
        iDestruct ("Hallw" with "Hw") as "Hres".
        rewrite swfill_sw_push_const /=.
        iApply "IH".
        iFrame.
      * erewrite to_eff_cons_thrE; eauto.
    + rewrite to_eff_cons_None => //.
      iIntros (σ ns κ κs nt) "Hσ".
      iSpecialize ("H" $! σ ns κ κs nt with "[$]").
      iMod "H".
      iModIntro.
      iDestruct "H" as "(%H1 & H)".
      iSplit.
      * iPureIntro.
        destruct σ => //=.
        rewrite - cat1s.
        eapply prepend_reducible; eauto.
        left. rewrite /= const_const //.
      * iIntros (es2 σ2 HStep).
        rewrite -cat1s in HStep.
        eapply reduce_ves in H1; last by apply HStep.
        assert (κ = []) as ->; first by apply prim_step_obs_efs_empty in HStep; inversion HStep.
        destruct H1 as [[-> HStep2] | [lh1 [lh2 [Hlf1 [Hlf2 ->]]]]].
        -- iSpecialize ("H" $! (drop 1 es2) σ2 HStep2).
           iMod "H".
           repeat iModIntro.
           repeat iMod "H".
           iModIntro.
           iDestruct "H" as "[Hσ H]".
           iSimpl.
           iFrame.
           iDestruct "H" as (f) "[Hf H]".
           iExists f.
           iFrame.
           iIntros "Hf".
           iDestruct ("H" with "Hf") as "H".
           iApply "IH".
           by iFrame.
        -- assert (iris.prim_step es σ2 [] [AI_trap] σ2 []) as HStep2.
           { unfold iris.prim_step.
             destruct σ2 as [[??]?].
             repeat split => //.
             apply r_simple; eapply rs_trap => //.
             intros ->.
             unfold to_val in Hes. simpl in Hes. done. } 
           iSpecialize ("H" $! [AI_trap] σ2 HStep2).
           iMod "H".
           repeat iModIntro.
           repeat iMod "H".
           iDestruct "H" as "(Hσ & %f & Hf & H)".
           iFrame.
           iIntros "!> Hf".
           iDestruct ("H" with "Hf") as "H".
           iApply fupd_ewp.
           { destruct (to_eff es2) eqn:Habs => //.
             apply lfilled_to_eff in Hlf1.
             2: by rewrite Habs.
             destruct Hlf1 as [?|?] => //.
             unfold to_eff in H.
             simpl in H. destruct H => //. }
           repeat rewrite ewp_unfold /ewp_pre /=.
           iMod "H".
           by iSpecialize ("Hntrap" with "H").
Qed.


Lemma ewp_val_app' (E : coPset) Ψ (Φ : val -> iProp Σ) vs (es : language.expr wasm_lang) :
  (□ (¬ Φ trapV )) ∗
    EWP es @ E <| Ψ |> {{ v, (Φ (val_combine (immV vs) v)) }}%I
  ⊢ EWP ((v_to_e_list vs) ++ es) @ E <| Ψ |> {{ v, Φ v }}%I.

Proof.
  iInduction vs as [|c vs] "IH" forall (Ψ Φ E es).
  { simpl.
    iIntros "(#Hntrap & HWP)".
    iApply (ewp_wand with "HWP").
    iIntros (v).
    destruct v => /=.
    all: iIntros "HΦ" => //=.
    all: unfold val_combine; simpl.
    all: by rewrite vh_push_const_nil + rewrite sh_push_const_nil + rewrite llh_push_const_nil.
  }
  { iIntros "(#Hntrap & HWP)".
    iSimpl.
    iApply ewp_val.
    iSplitR => //.
    iApply "IH" => //=.
    iSplit => //.
    iApply (ewp_wand with "HWP").
    iIntros (vs') "HΦ".
    iSimpl. unfold val_combine.
    destruct vs';auto; simpl.
    - iExFalso. iApply ("Hntrap" with "HΦ").
    - by rewrite -vh_push_const_app.
    - by rewrite -sh_push_const_app.
    - by rewrite -llh_push_const_app.
  }
Qed.
  
Lemma ewp_val_app (E : coPset) Ψ (Φ : val -> iProp Σ) vs v' (es : language.expr wasm_lang) :
  to_val vs = Some (immV v') ->
  (□ (¬ Φ trapV )) ∗
    EWP es @ E <| Ψ |> {{ v, (Φ (val_combine (immV v') v)) }}%I
  ⊢ EWP (vs ++ es) @ E <| Ψ |> {{ v, Φ v }}%I.
Proof.
  iIntros "%Hves [#Hntrap Hwp]".
  apply iris.of_to_val in Hves; subst.
  iApply ewp_val_app'.
  by iFrame.
Qed.



Definition lh_eff_None lh :=
  let '(_,_,es) := empty_base lh in
  to_eff es = None.

Lemma lh_eff_None_spec lh :
  lh_eff_None lh -> (forall i vs LI, const_list vs -> lfilled i lh vs LI ->
                               to_eff LI = None).
Proof.
  unfold lh_eff_None. induction lh => //=.
    all: intros Htf i vs LI Hvs Hfill.
    all: move/lfilledP in Hfill.
    all: inversion Hfill; subst.
    all: apply to_eff_cat_None2 => //.
    + apply to_eff_cat_None2 => //.
    + destruct (empty_base lh) as [[??]?] eqn:Hbase.
      unfold to_eff => /=.
      move/lfilledP in H8.
      apply IHlh in H8 => //.
      unfold to_eff in H8.
      destruct (merge_values (map _ LI0)) => //.
      destruct v => //.
      3: destruct i => //.
      4: destruct (vh_decrease _) => //.
      all: try by rewrite merge_notval.
      rewrite merge_br => //.
      rewrite merge_return => //.
      rewrite merge_call_host => //.
    +  destruct (empty_base lh) as [[??]?] eqn:Hbase.
      unfold to_eff => /=.
      move/lfilledP in H7.
      apply IHlh in H7 => //.
      unfold to_eff in H7.
      destruct (merge_values (map _ LI0)) => //.
      destruct v => //.
      all: try by rewrite merge_notval.
      rewrite merge_br => //.
      rewrite merge_return => //.
      rewrite merge_call_host => //.
    + destruct (empty_base lh) as [[??]?] eqn:Hbase.
      unfold to_eff => /=.
      move/lfilledP in H8.
      apply IHlh in H8 => //.
      unfold to_eff in H8.
      destruct (merge_values (map _ LI0)) => //.
      destruct v => //.
      all: try by rewrite merge_notval.
      rewrite merge_br => //.
      rewrite merge_return => //.
      rewrite merge_call_host => //.
Qed. 
      
    
      

Lemma ewp_bind es E Ψ i lh Φ:
  is_pure lh ->
(*  (forall vs LI, const_list vs -> lfilled i lh vs LI -> 
         to_eff LI = None) -> *)
  lh_eff_None lh ->
  EWP es @ E <| Ψ |> {{ w, ⌜ w <> trapV ⌝ ∗
                                   EWP of_val w @ E CTX i; lh <| Ψ |> {{ Φ }} }}
    ⊢ EWP es @ E CTX i; lh <| Ψ |> {{ Φ }}.
Proof.
   iLöb as "IH" forall (lh es Ψ).
 { iIntros (Hpure Hlh) "H".
   specialize (lh_eff_None_spec _ Hlh) as Hlh'.
   iIntros (LI HLI).
   rewrite !(ewp_unfold E es) /ewp_pre.
   rewrite !(ewp_unfold E LI) /ewp_pre.
   destruct (to_val LI) as [ v          |] eqn:He;
     [|destruct (to_eff LI) as [eff|] eqn:He'].
   - apply lfilled_to_val in HLI as HLI'.
     2: by eexists.
     destruct HLI' as [ves Htv].
     rewrite Htv.
     iMod "H".
     rewrite (@of_to_val _ _ Htv).
     iDestruct "H" as "[%Hntrap H]".
     iSpecialize ("H" $! _ HLI).
     rewrite !ewp_unfold /ewp_pre.
     rewrite He. done.
   - destruct eff.
     + eapply lfilled_to_eff_sus in HLI as HLI' => //.
       destruct HLI' as [Hconst | (shin & shout & Hin & Hout & Htrans)].
       * erewrite Hlh' in He' => //.
       * destruct (to_val es) eqn:Htv.
         by exfalso; eapply to_val_to_eff.
         rewrite Hin.
         iDestruct "H" as (f) "[Hf H]".
         iFrame. iIntros "Hf".
         iDestruct ("H" with "Hf") as "H".
         iApply (monotonic_prot with "[] H").
         iIntros (w) "H !>".
         subst sh.
         rewrite susfill_trans.
         eapply susfill_to_lfilled in Hout as Hfilled.
         2:{ instantiate (2 := susfill i0 shin (of_val w)).
             instantiate (2 := i0).
             done. } 
         destruct Hfilled as [k Hfilled].
         apply lfilled_depth in HLI as Hdepth1.
         apply lfilled_depth in Hfilled as Hdepth2.
         rewrite Hdepth1 in Hdepth2; subst i k.

         iSpecialize ("IH" $! lh (susfill i0 shin (of_val w)) Ψ Hpure Hlh).
         iDestruct ("IH" with "H") as "H".

         iSpecialize ("H" $! _ Hfilled).
         iExact "H".
     + eapply lfilled_to_eff_sw in HLI as HLI' => //.
       destruct HLI' as [Hconst | (shin & shout & Hin & Hout & Htrans)].
       * erewrite Hlh' in He' => //.
       * destruct (to_val es) eqn:Htv.
         by exfalso; eapply to_val_to_eff.
         rewrite Hin.
         iDestruct "H" as (f) "[Hf H]".
         iFrame.
         iIntros "Hf".
         iDestruct ("H" with "Hf") as "H".
         iApply (monotonic_prot with "[] H").
         iIntros (w) "H !>".
         subst sh.
         rewrite swfill_trans.
         eapply swfill_to_lfilled in Hout as Hfilled.
         2:{ instantiate (2 := swfill i0 shin (of_val w)).
             instantiate (2 := i0).
             done. } 
         destruct Hfilled as [k' Hfilled].
         apply lfilled_depth in HLI as Hdepth1.
         apply lfilled_depth in Hfilled as Hdepth2.
         rewrite Hdepth1 in Hdepth2; subst i k'.

         iSpecialize ("IH" $! lh (swfill i0 shin (of_val w)) Ψ Hpure Hlh).
         iDestruct ("IH" with "H") as "H".

         iSpecialize ("H" $! _ Hfilled).
         iExact "H".
     + eapply lfilled_to_eff_thr in HLI as HLI' => //.
       destruct HLI' as [Hconst | (shin & shout & Hin & Hout & Htrans)].
       * erewrite Hlh' in He' => //.
       * destruct (to_val es) eqn:Htv.
         by exfalso; eapply to_val_to_eff.
         rewrite Hin.
         done.
   - repeat rewrite ewp_unfold. rewrite /ewp_pre /=.
     (* Ind *)
     iIntros (σ ns κ κs nt) "Hσ".
     destruct (to_val es) as [vs|] eqn:Hes;
       last destruct (iris.to_eff es) as [eff |] eqn:Heff.
     + apply of_to_val in Hes as <-.
       iMod "H".
       iDestruct "H" as "[%Hntrap H]".
       iSpecialize ("H" $! _ HLI).
       iDestruct (ewp_unfold with "H") as "H"; rewrite /ewp_pre /=.
       rewrite He He'.
       iSpecialize ("H" $! σ ns κ κs nt with "[$]").
       iFrame.
     + apply to_eff_None_lfilled_inv in HLI => //.
       rewrite HLI in Heff => //. 
     + iSpecialize ("H" $! σ ns κ κs nt with "[$]").
       iMod "H" as "[%H1 H2]".
       iModIntro.
       iSplit.
       * iPureIntro.
         eapply lfilled_reducible => //.
       * iIntros (e2 σ2 HStep').
         eapply lfilled_reduce in HStep' as Heq.
         2: exact HLI.
         2: done.
         apply prim_step_obs_efs_empty in HStep' as Hemp.
         inversion Hemp;subst;clear Hemp.
         destruct Heq as [(es' & Hstep & Hfill) | (lhtrap & Htrap & ->)].
         -- iSpecialize ("H2" $! es' σ2 Hstep).
            iMod "H2".
            repeat iModIntro.
            repeat iMod "H2".
            iModIntro.
            iDestruct "H2" as "(Hσ & %f & Hf & Hes)".
            iFrame.
            iIntros "Hf"; iDestruct ("Hes" with "Hf") as "Hes".
            iDestruct ("IH" with "[] [] Hes") as "Hcont". done. done.
            by iApply "Hcont".
         -- assert (iris.prim_step es σ2 [] [AI_trap] σ2 []) as HStep2.
            { unfold iris.prim_step.
              destruct σ2 as [[??]?].
              repeat split => //.
              apply r_simple; eapply rs_trap => //.
              move => HContra; subst.
              by simpl in Hes.
            }
            iSpecialize ("H2" $! [AI_trap] σ2 HStep2).
            iMod "H2".
            repeat iModIntro.
            repeat iMod "H2".
            iDestruct "H2" as "(Hσ & %f & Hf & H)".
            iModIntro => /=.
            iFrame.
            iIntros "Hf"; iDestruct ("H" with "Hf") as "H".
            iDestruct (ewp_unfold with "H") as "H";rewrite /ewp_pre /=.
            edestruct lfilled_trans as [lh' Hlh''].
            exact Htrap. exact HLI.
            destruct σ2 as [[??]?].
            destruct HStep' as (HStep' & _ & _).
            edestruct trap_reduce_lfilled as (lh'' & j & Hfilled & Hij).
            exact HStep'.
            exact Hlh''.
            apply to_eff_filled_trap in Hfilled as Hy.
            iApply fupd_ewp.
            rewrite Hy. done.
            iMod "H".
            iDestruct "H" as "[% _]" => //.  } 
  Qed. 

(*
 Lemma ewp_bind es E Ψ i lh Φ:
  is_pure lh ->
  EWP es @ E <| Ψ |> {{ w, ⌜ w <> trapV ⌝ ∗
    EWP of_val w @ E CTX i; lh <| Ψ |> {{ Φ }} }}
    ⊢ EWP es @ E CTX i; lh <| Ψ |> {{ Φ }}.
Proof.
  iLöb as "IH" forall (lh es Ψ).
 { iIntros (Hpure) "H".
   iIntros (LI HLI).
   rewrite !(ewp_unfold E es) /ewp_pre.

   destruct (to_val es) as [v|] eqn:He;
     last destruct (to_eff es) as [eff|] eqn:He'.
   - iApply fupd_ewp. Search "lfilled_to_eff".
   

   
   rewrite !(ewp_unfold E LI) /ewp_pre.
   destruct (to_val LI) as [ v          |] eqn:He;
     [|destruct (to_eff LI) as [eff|] eqn:He'].
   - apply lfilled_to_val in HLI as HLI'.
     2: by eexists.
     destruct HLI' as [ves Htv].
     rewrite Htv.
     iMod "H".
     rewrite (@of_to_val _ _ Htv).
     iDestruct "H" as "[%Hntrap H]".
     iSpecialize ("H" $! _ HLI).
     rewrite !ewp_unfold /ewp_pre.
     rewrite He. done.
   - destruct eff.
     + eapply lfilled_to_eff_sus in HLI as HLI' => //.
       destruct HLI' as [Hconst | (shin & shout & Hin & Hout & Htrans)].
       * apply const_list_to_val in Hconst as (ves & Htv & Hves).
         rewrite Htv. by rewrite Htv in Hetoves.
(*         a dmit. *)
       * destruct (to_val es) eqn:Htv.
         by exfalso; eapply to_val_to_eff.
         rewrite Hin.
         iApply (monotonic_prot with "[] H").
         iIntros (w) "H !>".
         subst sh.
         rewrite susfill_trans.
         eapply susfill_to_lfilled in Hout as Hfilled.
         2:{ instantiate (2 := susfill i0 shin (of_val w)).
             instantiate (2 := i0).
             done. } 
         destruct Hfilled as [k Hfilled].
         apply lfilled_depth in HLI as Hdepth1.
         apply lfilled_depth in Hfilled as Hdepth2.
         rewrite Hdepth1 in Hdepth2; subst i k.
         destruct (to_val (susfill i0 shin (of_val w))) eqn:Hetovfill.
         { iDestruct (ewp_unfold with "H") as "H".
           rewrite /ewp_pre Hetovfill.

         iSpecialize ("IH" $! lh Ψ (susfill i0 shin (of_val w)) _ _ Hpure).
         iDestruct ("IH" with "H") as "H".

         iSpecialize ("H" $! _ Hfilled).
         iExact "H".
     + admit.
     + admit.
   - repeat rewrite ewp_unfold. rewrite /ewp_pre /=.
     (* Ind *)
     iIntros (σ ns κ κs nt) "Hσ".
     destruct (to_val es) as [vs|] eqn:Hes;
       last destruct (iris.to_eff es) as [eff |] eqn:Heff.
     + apply of_to_val in Hes as <-.
       iMod "H".
       iDestruct "H" as "[%Hntrap H]".
       iSpecialize ("H" $! _ HLI).
       iDestruct (ewp_unfold with "H") as "H"; rewrite /ewp_pre /=.
       rewrite He He'.
       iSpecialize ("H" $! σ ns κ κs nt with "[$]").
       iFrame.
     + apply to_eff_None_lfilled_inv in HLI => //.
       rewrite HLI in Heff => //. 
     + iSpecialize ("H" $! σ ns κ κs nt with "[$]").
       iMod "H" as "[%H1 H2]".
       iModIntro.
       iSplit.
       * iPureIntro.
         eapply lfilled_reducible => //.
       * iIntros (e2 σ2 HStep').
         eapply lfilled_reduce in HStep' as Heq.
         2: exact HLI.
         2: done.
         apply prim_step_obs_efs_empty in HStep' as Hemp.
         inversion Hemp;subst;clear Hemp.
         destruct Heq as [(es' & Hstep & Hfill) | (lhtrap & Htrap & ->)].
         -- iSpecialize ("H2" $! es' σ2 Hstep).
            iMod "H2".
            repeat iModIntro.
            repeat iMod "H2".
            iModIntro.
            iDestruct "H2" as "(Hσ & Hes)".
            iFrame.
            iDestruct ("IH" with "[] Hes") as "Hcont". done.
            by iApply "Hcont".
         -- assert (iris.prim_step es σ2 [] [AI_trap] σ2 []) as HStep2.
            { unfold iris.prim_step.
              destruct σ2 as [[??]?].
              repeat split => //.
              apply r_simple; eapply rs_trap => //.
              move => HContra; subst.
              by simpl in Hes.
            }
            iSpecialize ("H2" $! [AI_trap] σ2 HStep2).
            iMod "H2".
            repeat iModIntro.
            repeat iMod "H2".
            iDestruct "H2" as "[Hσ H]".
            iModIntro => /=.
            iFrame. 
            iDestruct (ewp_unfold with "H") as "H";rewrite /ewp_pre /=.
            edestruct lfilled_trans as [lh' Hlh'].
            exact Htrap. exact HLI.
            destruct σ2 as [[??]?].
            destruct HStep' as (HStep' & _ & _).
            edestruct trap_reduce_lfilled as (lh'' & j & Hfilled & Hij).
            exact HStep'.
            exact Hlh'.
            apply to_eff_filled_trap in Hfilled as Hy.
            iApply fupd_ewp.
            rewrite Hy. done.
            iMod "H".
            iDestruct "H" as "[% _]" => //. 
  Qed.  *)


Lemma ewp_seq (E : coPset) P (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) :
  to_eff es2 = None -> 
  ( ¬ Ψ trapV ∗  
     EWP es1 @ E <| P |> {{ w, Ψ w }} ∗
  ∀ w, Ψ w -∗ EWP (iris.of_val w ++ es2) @ E <| P |> {{ v, Φ v }})
  ⊢ EWP (es1 ++ es2) @ E <| P |> {{ v, Φ v }}.
Proof.
(*  destruct (const_list es1) eqn:Hes1.
  { a dmit.  (*apply const_list_to_val in Hes1 as (vs & Htv & <-). 
    iIntros "(Hntrap & Hes1 & Hes2)".
    iApply ewp_val_app.
    exact Htv.
    iDestruct ewp_value_fupd as "[H1 _]"; last first.
    iDestruct ("H1" with "Hes1") as "H".
    2: unfold IntoVal.
    2: apply of_to_val => //.
    
    iDestruct (ewp_value_fupd with "Hes1") as "H". *)}
    generalize dependent es1. *)
  iLöb as "IH" forall (E es1 es2 P Φ Ψ).
  iIntros (*es1 Hes1*) (Hes2) "(Hntrap & Hes1 & Hes2)".
  (* Base case, when both es1 and es2 are values *)
  iApply ewp_unfold. repeat rewrite ewp_unfold /ewp_pre /=.
(*  rewrite Hes1. *)
  (*  rewrite to_val_cat_None1 => //. *)
  destruct (to_val (es1 ++ es2)) as [v|] eqn:Hetov; last
  destruct (iris.to_eff (es1 ++ es2)) as [eff|] eqn:Hetof.
  - assert (lfilled 0 (LH_base [] []) (es1 ++ es2) (es1 ++ es2)) as Hfilled.
    { cbn. erewrite app_nil_r. by apply/eqP. }
    eapply lfilled_to_val_app in Hfilled as Hv;eauto.
    destruct Hv as [vs' [Hvs' Hfilled']].
    rewrite Hvs'.
    iSpecialize ("Hes2" with "Hes1").
    iMod "Hes2".
    apply lfilled_Ind_Equivalent in Hfilled';inversion Hfilled';simplify_eq.
    erewrite app_nil_r in H1.
    assert (iris.of_val vs' ++ es2 = es1 ++ es2) as ->;auto.
    iDestruct (ewp_unfold with "Hes2") as "Hes2". rewrite /ewp_pre /= Hetov.
    done. 
  - assert (lfilled 0 (LH_base [] []) (es1 ++ es2) (es1 ++ es2)) as Hfilled.
    { cbn. erewrite app_nil_r. by apply/eqP. }
    destruct eff.
    + eapply lfilled_to_eff_app_sus in Hfilled as Hv;eauto.
      destruct Hv as [[Hconst1 Hconst2] | [(esv & shin & shout & -> & Hin & Hout & Htrans) | (shin & shout & Hin & Hout & Htrans)]].
      * destruct (@const_list_to_val (es1 ++ es2)) as (vs' & Htv & Hvs').
        apply const_list_concat => //.
        rewrite Htv in Hetov => //. 
      * rewrite Hin // in Hes2.  
        (* destruct (@const_list_to_val (v_to_e_list esv)) as (vs' & Htv & Hvs').
        apply v_to_e_is_const_list.
        apply v_to_e_inj in Hvs' as ->.
        rewrite Htv.
        simpl in Hout.
        inversion Hout; subst.
        iSimpl. rewrite sus_push_const_nil.
        rewrite sus_append_nil.
        rewrite sus_append_nil.
        a dmit. *)
      * destruct (to_val es1) eqn:Habs; first by exfalso; eapply to_val_to_eff.
        rewrite Hin.
        iDestruct "Hes1" as (f) "[Hf Hes1]".
        iFrame. iIntros "Hf".
        iDestruct ("Hes1" with "Hf") as (Ξ) "[HΞ Hnext]".
        iExists Ξ.
        iFrame.
        iIntros (w) "Hw".
        simpl in Hout.
        inversion Hout; subst.
        iSimpl.
        rewrite sus_push_const_nil.
        rewrite sus_append_nil.
        rewrite sus_push_const_nil.
        rewrite susfill_sus_append.
        iDestruct ("Hnext" with "Hw") as "Hwp".
        iNext.
        iApply "IH".
        done.
        iFrame.
      * constructor.
    + eapply lfilled_to_eff_app_sw in Hfilled as Hv;eauto.
      destruct Hv as [[Hconst1 Hconst2] | [(esv & shin & shout & -> & Hin & Hout & Htrans) | (shin & shout & Hin & Hout & Htrans)]].
      * destruct (@const_list_to_val (es1 ++ es2)) as (vs' & Htv & Hvs').
        apply const_list_concat => //.
        rewrite Htv in Hetov => //. 
      * rewrite Hin // in Hes2.  
      * destruct (to_val es1) eqn:Habs; first by exfalso; eapply to_val_to_eff.
        rewrite Hin.
        iDestruct "Hes1" as (f) "[Hf Hes1]".
        iFrame. iIntros "Hf".
        iDestruct ("Hes1" with "Hf") as (Ξ) "[HΞ Hnext]".
        iExists Ξ.
        iFrame.
        iIntros (w) "Hw".
        simpl in Hout.
        inversion Hout; subst.
        iSimpl.
        rewrite sw_push_const_nil.
        rewrite sw_append_nil.
        rewrite sw_push_const_nil.
        rewrite swfill_sw_append.
        iDestruct ("Hnext" with "Hw") as "Hwp".
        iNext.
        iApply "IH".
        done.
        iFrame.
      * constructor.
    + eapply lfilled_to_eff_app_thr in Hfilled as Hv;eauto.
      destruct Hv as [[Hconst1 Hconst2] | [(esv & shin & shout & -> & Hin & Hout & Htrans) | (shin & shout & Hin & Hout & Htrans)]].
      * destruct (@const_list_to_val (es1 ++ es2)) as (vs' & Htv & Hvs').
        apply const_list_concat => //.
        rewrite Htv in Hetov => //. 
      * rewrite Hin // in Hes2.  
      * destruct (to_val es1) eqn:Habs; first by exfalso; eapply to_val_to_eff.
        rewrite Hin.
        iDestruct "Hes1" as (Ξ) "[HΞ Hnext]".
        iExists Ξ.
        iFrame.
      * constructor.
  - (* Ind *)
    iIntros (σ ns κ κs nt) "Hσ".
    apply to_eff_cat_None_inv in Hetof as Hetof'.
    rewrite Hetof'.
    destruct (to_val es1) as [vs|] eqn:Hes.
    + apply of_to_val in Hes as <-.
      iMod "Hes1".
      iSpecialize ("Hes2" with "Hes1").
      iDestruct (ewp_unfold with "Hes2") as "Hes2"; rewrite /ewp_pre /=.
      rewrite Hetov Hetof.
      iSpecialize ("Hes2" $! σ ns κ κs nt with "[$]").
      iMod "Hes2" as "[%H1 H2]".
      iIntros "!>".
      iSplit.
      * iPureIntro. by apply H1. 
      * by iApply "H2".
    + iSpecialize ("Hes1" $! σ ns κ κs nt with "[$]").
      iMod "Hes1" as "[%H1 H2]".
      iModIntro.
      iSplit.
      * iPureIntro.
        by apply append_reducible.
      * iIntros (e2 σ2 HStep).
        assert (κ = []) as ->; first by apply prim_step_obs_efs_empty in HStep; inversion HStep.
        apply prim_step_split_reduce_r in HStep; last by [].
        destruct HStep as [[es'' [-> HStep]] | [n [m [lh [Hlf1 [Hlf2 ->]]]]]].
        -- iSpecialize ("H2" $! es'' σ2 HStep).
           iMod "H2".
           repeat iModIntro.
           repeat iMod "H2".
           iModIntro.
           destruct σ2 as [[??]?].
           iDestruct "H2" as "[Hσ H]".
           iDestruct "H" as (f1) "(Hf1 & Hes'')". 
           iFrame. 
           iIntros "?"; iSpecialize ("Hes''" with "[$]"). 
           iApply "IH".
           done.
           by iFrame. 
        -- move/lfilledP in Hlf1.
           inversion Hlf1; subst; clear Hlf1.
           assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
           { unfold iris.prim_step.
             destruct σ as [[??]?].
             repeat split => //.
             apply r_simple; eapply rs_trap => //.
             move => HContra; subst.
             by destruct n.
           }
           iSpecialize ("H2" $! [AI_trap] σ HStep2).
           iMod "H2".
           repeat iModIntro.
           repeat iMod "H2".
           destruct σ as [[??]?].
           iDestruct "H2" as "[Hσ H]".
           iDestruct "H" as (f1) "(Hf1 & Hes'')". 
           iFrame. 
           iModIntro.
           iIntros "?"; iSpecialize ("Hes''" with "[$]"). 
           replace [AI_trap] with (iris.of_val trapV) => //.
           iApply fupd_ewp.
           { simpl. destruct (iris.to_eff (take n es1 ++ AI_trap :: drop m (es1 ++ es2))%SEQ) eqn:Hy => //.
             unfold to_eff in Hy.
             rewrite map_app merge_app /= in Hy.
              rewrite merge_trap in Hy.
              rewrite val_not_val_combine_assoc in Hy.
              apply const_list_to_val in H2 as (? & ? & ?).
              unfold to_val in H.
              destruct (merge_values _) => //.
              inversion H; subst.
              destruct x => //=.
              simpl in Hy.
              destruct (flatten _) => //.  } 
           repeat rewrite ewp_unfold /ewp_pre /=.
           iMod "Hes''".
           by iSpecialize ("Hntrap" with "Hes''").
Qed.

Lemma ewp_wand_ctx E e P Φ Ψ i lh :
  EWP e @ E CTX i; lh <| P |> {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ EWP e @ E CTX i; lh <| P |> {{ Ψ }}.
Proof.
  iIntros "Hwp H". iIntros (LI HLI).
  iSpecialize ("Hwp" $! LI HLI).
  iApply (ewp_wand with "Hwp"). auto.
Qed.

Lemma ewp_seq_ctx (E : coPset) Ψ (Φ Φ' : iris.val -> iProp Σ) (es1 es2 : language.expr wasm_lang) (i : nat) (lh : lholed) :
  to_eff es2 = None ->
  is_pure lh ->
  lh_eff_None lh ->
  ((¬ (Φ' trapV)) ∗
     EWP es1 @ E <| Ψ |> {{ w, Φ' w }} ∗
  ∀ w, (Φ' w -∗ EWP (iris.of_val w ++ es2) @ E CTX i; lh <| Ψ |> {{ v, Φ v }}))%I
  ⊢ EWP (es1 ++ es2) @ E CTX i; lh <| Ψ |> {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (E es1 es2 Φ Φ' Ψ i lh).
  iIntros (Hes2 Hpure Hlh) "[Hntrap [Hes1 Hes2]]".
  specialize (lh_eff_None_spec _ Hlh) as Hlh'.
  iIntros (LI Hfilled).
  iApply ewp_unfold. rewrite /ewp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (to_val LI) as [vs|] eqn:Hetov;
    last destruct (iris.to_eff LI) as [eff|] eqn:Hetof.
   - iDestruct (ewp_unfold with "Hes1") as "Hes1".
     rewrite /ewp_pre /=.
     eapply lfilled_to_val_app in Hfilled as Hv;eauto.
     destruct Hv as [vs' [Hvs' Hfilled']].
     rewrite Hvs'.
     iSpecialize ("Hes2" with "Hes1").
     iMod "Hes2".
     iSpecialize ("Hes2" $! _ Hfilled').
     iDestruct (ewp_unfold with "Hes2") as "Hes2".
     rewrite /ewp_pre /= Hetov.
     done.
   - iDestruct (ewp_unfold with "Hes1") as "Hes1".
     rewrite /ewp_pre /=.
     destruct eff.
     + eapply lfilled_to_eff_app_sus in Hfilled as Hv;eauto.
       destruct Hv as [[Hconst1 Hconst2] | [(esv & shin & shout & -> & Hin & Hout & Htrans) | (shin & shout & Hin & Hout & Htrans)]].
       * apply Hlh' in Hfilled.
         by rewrite Hfilled in Hetof.
         by apply const_list_concat.
       * rewrite Hin in Hes2 => //.  
       * destruct (to_val es1) eqn:Habs.
         eapply to_val_to_eff in Habs => //.
         rewrite Hin.
         iDestruct "Hes1" as (f) "[Hf Hes1]".
         iFrame; iIntros "Hf".
         iDestruct ("Hes1" with "Hf") as (Ξ) "[HΞ Hnext]".
         iExists Ξ.
         iFrame.
         iIntros (w) "Hw".
         iDestruct ("Hnext" with "Hw") as "H".
         iNext.
         subst sh.
         rewrite susfill_trans.
         eapply susfill_to_lfilled in Hout as Hfill'.
         2: done.
         destruct Hfill' as [k Hfill'].
         iDestruct ("IH" with "[] [] [] [$Hntrap $H $Hes2]") as "H".
         done. done. done.
         apply lfilled_depth in Hfilled as Hdepth1.
         apply lfilled_depth in Hfill' as Hdepth2.
         subst i k. 
         iDestruct ("H" $! _ Hfill') as "H".
         unfold sus_trans.
         rewrite sus_push_const_nil.
         rewrite susfill_sus_append.
         iExact "H".
     + eapply lfilled_to_eff_app_sw in Hfilled as Hv;eauto.
       destruct Hv as [[Hconst1 Hconst2] | [(esv & shin & shout & -> & Hin & Hout & Htrans) | (shin & shout & Hin & Hout & Htrans)]].
       * apply Hlh' in Hfilled.
         by rewrite Hfilled in Hetof.
         by apply const_list_concat.
       * rewrite Hin in Hes2 => //.  
       * destruct (to_val es1) eqn:Habs.
         eapply to_val_to_eff in Habs => //.
         rewrite Hin.
         iDestruct "Hes1" as (f) "[Hf Hes1]".
         iFrame; iIntros "Hf".
         iDestruct ("Hes1" with "Hf") as (Ξ) "[HΞ Hnext]".
         iExists Ξ.
         iFrame.
         iIntros (w) "Hw".
         iDestruct ("Hnext" with "Hw") as "H".
         iNext.
         subst sh.
         rewrite swfill_trans.
         eapply swfill_to_lfilled in Hout as Hfill'.
         2: done.
         destruct Hfill' as [k' Hfill'].
         iDestruct ("IH" with "[] [] [] [$Hntrap $H $Hes2]") as "H".
         done. done. done.
         apply lfilled_depth in Hfilled as Hdepth1.
         apply lfilled_depth in Hfill' as Hdepth2.
         subst i k'. 
         iDestruct ("H" $! _ Hfill') as "H".
         unfold sw_trans.
         rewrite sw_push_const_nil.
         rewrite swfill_sw_append.
         iExact "H".
     + eapply lfilled_to_eff_app_thr in Hfilled as Hv;eauto.
       destruct Hv as [[Hconst1 Hconst2] | [(esv & shin & shout & -> & Hin & Hout & Htrans) | (shin & shout & Hin & Hout & Htrans)]].
       * apply Hlh' in Hfilled.
         by rewrite Hfilled in Hetof.
         by apply const_list_concat.
       * rewrite Hin in Hes2 => //.  
       * destruct (to_val es1) eqn:Habs.
         eapply to_val_to_eff in Habs => //.
         rewrite Hin.
         iDestruct "Hes1" as (Ξ) "[HΞ Hnext]".
         iExists Ξ.
         iFrame.

   - repeat rewrite ewp_unfold. rewrite /ewp_pre /=.
     (* Ind *)
     iIntros (σ ns κ κs nt) "Hσ".
     destruct (to_val es1) as [vs|] eqn:Hes;
       last destruct (iris.to_eff es1) as [eff |] eqn:Heff.
     + apply of_to_val in Hes as <-.
       iMod "Hes1".
       iSpecialize ("Hes2" with "Hes1").
       iSpecialize ("Hes2" $! _ Hfilled).
       iDestruct (ewp_unfold with "Hes2") as "Hes2"; rewrite /ewp_pre /=.
       rewrite Hetov Hetof.
       iSpecialize ("Hes2" $! σ ns κ κs nt with "[$]").
       iMod "Hes2" as "[%H1 H2]".
       iIntros "!>".
       iSplit.
       * iPureIntro. by apply H1. 
       * by iApply "H2".
     + apply to_eff_None_lfilled_inv in Hfilled => //.
       apply to_eff_cat_None_inv in Hfilled.
       rewrite Hfilled in Heff => //. 
     + iSpecialize ("Hes1" $! σ ns κ κs nt with "[$]").
       iMod "Hes1" as "[%H1 H2]".
       iModIntro.
       iSplit.
       * iPureIntro.
         destruct σ => //.
         apply append_reducible with (es2:=es2) in H1;auto.
         eapply lfilled_reducible. apply Hfilled. auto.
       * iIntros (e2 σ2 HStep').
         eapply lfilled_prim_step_split_reduce_r in HStep' as Heq;[|apply Hfilled|apply H1].
         apply prim_step_obs_efs_empty in HStep' as Hemp.
         inversion Hemp;subst;clear Hemp.
         destruct Heq as [[e' [HStep'' Hlfilled']] | [[lh' Hlf] <-]].
         -- iSpecialize ("H2" $! e' σ2 HStep'').
            iMod "H2".
            repeat iModIntro.
            repeat iMod "H2".
            iModIntro.
            iDestruct "H2" as "(Hσ & %f & Hf & Hes)".
            iFrame.
            iIntros "?"; iDestruct ("Hes" with "[$]") as "Hes".
            iDestruct ("IH" with "[] [] [] [$Hntrap $Hes $Hes2]") as "Hcont"; try done; by iApply "Hcont".
         -- assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
            { unfold iris.prim_step.
              destruct σ as [[??]?].
              repeat split => //.
              apply r_simple; eapply rs_trap => //.
              move => HContra; subst.
              by simpl in Hes.
            }

            iSpecialize ("H2" $! [AI_trap] σ HStep2).
            iMod "H2".
            repeat iModIntro.
            repeat iMod "H2".
            destruct σ as [[? ?]?].
            iDestruct "H2" as "(Hσ & %f & Hf & H)".
            iModIntro => /=.
            iFrame.
            iIntros "Hf".
            iDestruct ("H" with "Hf") as "H".
            iDestruct (ewp_unfold with "H") as "H";rewrite /ewp_pre /=.
            assert (lfilled 0 (LH_base [] es2) es1 (es1 ++ es2)) as Hfilltr.
            { rewrite /lfilled /lfill /= //. } 
            edestruct lfilled_trans as [lhi Hlhi].
            exact Hlf. exact Hfilltr.
            edestruct lfilled_trans as [lh'' Hlh''].
            exact Hlhi. exact Hfilled.
            destruct HStep' as (HStep' & _ & _).
            edestruct trap_reduce_lfilled as (lh''' & j & Hfilled' & Hij).
            exact HStep'.
            exact Hlh''.
            apply to_eff_filled_trap in Hfilled' as Hy.
            iApply fupd_ewp.
            rewrite Hy. done.
            iMod "H".
            by iSpecialize ("Hntrap" with "H"). 
Qed. 



(* Contextual rules for Local computation *)


Lemma ewp_frame_rewrite (E: coPset) Ψ (Φ: val -> iProp Σ) es n f:
  EWP es @ E FRAME n; f <| Ψ |> {{ v, Φ v }} ⊣⊢
                        EWP [AI_local n f es] @ E <| Ψ |> {{ v, Φ v }}.
Proof.
  trivial.
Qed.

Lemma ewp_frame_value (E : coPset) Ψ (Φ : val -> iProp Σ) es n f f0 vs :
  to_val es = Some (immV vs) ->
  length es = n ->
  ↪[frame] f0 -∗
  ▷ (Φ (immV vs)) -∗
                     EWP es @ E FRAME n; f <| Ψ |> {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hv Hlen) "Hframe H".
  rewrite ewp_frame_rewrite.
  apply to_val_const_list in Hv as Hconst.
  iApply (ewp_lift_atomic_step with "[H Hframe]"); simpl ; trivial;eauto.
  unfold to_val => /=.
  apply const_list_to_val in Hconst as (? & ? & ?).
  unfold to_val in H.
  destruct (merge_values $ map _ _) => //.
  by inversion H.
  unfold to_eff => /=.
  apply const_list_to_val in Hconst as (? & ? & ?).
  unfold to_val in H.
  destruct (merge_values $ map _ _) => //.
  by inversion H.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold language.reducible, language.prim_step => /=.
    exists [], es, σ, [].
    destruct σ as [[ ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. apply r_simple. apply rs_local_const; auto.
  - destruct σ as [[ws locs] inst].
    iIntros "!>" (es2 σ2 HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'].
    destruct HStep as (H & -> & _). iFrame.
    iris_ewp_ctx.only_one_reduction H. all:simplify_eq;iFrame. rewrite Hv. iFrame.
    1,2:rewrite find_first_const// in Hstart.
Qed.

(*
Lemma ewp_bind_frame Ψ f0 f1 f es E P Φ n:
  to_val es = None ->
  to_eff es = None ->
  (¬ (Ψ trapV) ∗
  ↪[frame] f0 ∗
    (↪[frame] f -∗ EWP es @ E <| P |> {{ w, Ψ w ∗ ↪[frame] f1 }}) ∗
    ∀ w, Ψ w ∗ ↪[frame] f0 -∗ EWP [AI_local n f (of_val w)] @ E <| P |> {{ v, Φ v }})%I
    ⊢ EWP [AI_local n f es] @ E <| P |> {{ v, Φ v }} .
Proof.
  iLöb as "IH" forall (E es P Φ Ψ n f f0 f1).
{ iIntros (Htv Htf) "(Htrap & Hf0 & Hes1 & Hes2)".
  iApply ewp_unfold.
  rewrite /ewp_pre.
  rewrite to_val_local_none_none //.
  rewrite to_eff_local_none_none //.
  iIntros (σ ns κ κs nt) "Hσ".
  destruct σ as [[s1 locs] inst].
  iDestruct "Hσ" as "(Hfuncs & Hconts & Htags & Htables & Hmems & Hglobals & Hframe & Hlen)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as %Hlook;rewrite lookup_insert in Hlook;inversion Hlook.
  iMod (ghost_map_update f with "Hframe Hf0") as "[Hframe Hf]"; rewrite insert_insert.
  iDestruct ("Hes1" with "Hf") as "Hes1".
  destruct f. 
  iDestruct (ewp_unfold with "Hes1") as "Hes1".
  rewrite /ewp_pre Htv Htf.
  iSpecialize ("Hes1" $! (s1,f_locs,f_inst) ns κ κs nt with "[$]").
  iMod "Hes1" as "[%H1 H2]".
  iModIntro.
  iSplit; first by iPureIntro; apply local_frame_reducible.
  iIntros (es2 σ2 Hstep).
  rewrite -(cats0 es) in Hstep.
  destruct σ2 as [[s2 locs2] inst2].
  apply prim_step_obs_efs_empty in Hstep as Hobs.
  inversion Hobs; subst.
  apply local_frame_prim_step_split_reduce_r in Hstep.
  destruct Hstep as [(ees' & vs' & inst' & Hstep & <- & <- & ->) | (lh' & Htrap & Hσ)].
  - iDestruct ("H2" $! _ _ Hstep) as "H2".
    simpl.
    iMod "H2".
    repeat iModIntro.
    repeat iMod "H2".
    
    iDestruct "H2" as "(Hσ & %f & Hf & H2)".
    iDestruct "Hσ" as "(Hfuncs & Hconts & Htags & Htables & Hmems & Hglobals & Hframe & Hrest)".
    iDestruct (ghost_map_lookup with "Hframe Hf") as %Hlook';rewrite lookup_insert in Hlook';inversion Hlook'.
    iMod (ghost_map_update (Build_frame locs inst) with "Hframe Hf") as "[Hframe Hf]"; rewrite insert_insert.
    iModIntro. iFrame.
    iIntros "Hf".
    iApply "IH".
    admit.
    admit.
    iFrame "Htrap". iFrame "Hf". rewrite cats0. iFrame "H2".
    iIntros (w) "[Hw Hf]".
    iDestruct ("Hes2" with "[$]") as "Hes2".
    admit.
  - assert (prim_step es (s1, f_locs, f_inst) [] [AI_trap] (s1, f_locs, f_inst) []).
    { repeat split => //.
      constructor. econstructor. 2: exact Htrap. intros ->.
      unfold to_val in Htv. done. }
    iDestruct ("H2" $! _ _ H) as "H2".
    inversion Hσ; subst.
    simpl.
    repeat iMod "H2".
    repeat iModIntro.
    repeat iMod "H2".
    iDestruct "H2" as "(Hσ & %f & Hf & H2)".
    iDestruct "Hσ" as "(Hfuncs & Hconst & Htags & Htables & Hmems & Hglobals & Hframe & Hrest)".
    iMod (gen_heap_update with "Hframe Hf") as H
    
    
    
    
    iApply ("IH" with "[] [] [] [$]");auto.
      iPureIntro. intros LI HLI.
      eapply lfilled_inj in Hfill;eauto.
      subst LI. auto.
      iPureIntro. intros LI HLI.
      eapply lfilled_inj in Hfill; eauto.
      subst LI.


    
    iMod (ghost_map_update f with "Hframe Hf") as "[Hframe Hf]"; rewrite insert_insert.
    
    iFrame.
  
  
  
  unfold to_eff. unfold to_eff in Htf.
  simpl. destruct (merge_values (map _ es)) => //.
  destruct v => //. 
  Search (to_eff [AI_local _ _ _]). *)

(* Lemma ewp_seq_ctx_frame (E : coPset) P (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) (i : nat) (lh : lholed) (n : nat) (f : frame) (f0 : frame) (f1 : frame) :
  to_eff es2 = None ->
  is_pure lh ->
  lh_eff_None lh ->
  (forall LI, lfilled i lh (es1 ++ es2) LI -> to_val [AI_local n f LI] = None) ->
  (forall LI, lfilled i lh (es1 ++ es2) LI -> iris.to_eff [AI_local n f LI] = None) ->
  ((¬ (Ψ trapV)) ∗ ↪[frame] f0 ∗
   (↪[frame] f -∗ EWP es1 @ E <| P |> {{ w, Ψ w ∗ ↪[frame] f1 }}) ∗
   ∀ w, Ψ w ∗ ↪[frame] f0 -∗ EWP (iris.of_val w ++ es2) @ E FRAME n ; f1 CTX i; lh <| P |> {{ v, Φ v }})%I
  ⊢ EWP (es1 ++ es2) @ E FRAME n ; f CTX i; lh <| P |> {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (E es1 es2 P Φ Ψ i lh n f f0 f1).
{ iIntros (Hes2 Hpure Hlh Hnonev Hnonef) "[Htrap [Hf0 [Hes1 Hes2]]]".
  iIntros (LI Hfilled).
  specialize (lh_eff_None_spec _ Hlh) as Hlh'.
  
  iApply ewp_unfold.
  (* Base case, when both es1 and es2 are values *)

  destruct (to_val [AI_local n f LI]) as [vs|] eqn:Hetov.
  { rewrite Hnonev in Hetov => //. } 
  destruct (iris.to_eff [AI_local n f LI]) as [eff|] eqn:Hetof.
  { rewrite Hnonef in Hetof => //. }
 (* clear Hnonef.
    destruct eff.
    + eapply lfilled_to_eff_app_sus in Hfilled as Hv;eauto.
      destruct Hv as [[Hconst1 Hconst2] | [(esv & shin & shout & -> & Hin & Hout & Htrans) | (shin & shout & Hin & Hout & Htrans)]].
      * apply Hlh' in Hfilled.
        unfold to_eff in Hetof, Hfilled.
        simpl in Hetof.
        destruct (merge_values (map _ LI)) => //.
        destruct v => //. 
        by apply const_list_concat.
      * rewrite Hin in Hes2 => //.  
      * destruct (to_val es1) eqn:Habs.
        eapply to_val_to_eff in Habs => //.
        rewrite Hin.
         iDestruct "Hes1" as (Ξ) "[HΞ Hnext]".
         iExists Ξ.
         iFrame.
         iIntros (w) "Hw".
         iDestruct ("Hnext" with "Hw") as "H".
         iNext.
         subst sh.
         rewrite susfill_trans.
         eapply susfill_to_lfilled in Hout as Hfill'.
         2: done.
         destruct Hfill' as [k Hfill'].
         iDestruct ("IH" with "[] [] [] [$Hntrap $H $Hes2]") as "H".
         done. done. done.
         apply lfilled_depth in Hfilled as Hdepth1.
         apply lfilled_depth in Hfill' as Hdepth2.
         subst i k. 
         iDestruct ("H" $! _ Hfill') as "H".
         unfold sus_trans.
         rewrite sus_push_const_nil.
         rewrite susfill_sus_append.
         iExact "H".
  { rewrite Hnonef in Hetof => //. } *)

  repeat rewrite ewp_unfold /ewp_pre /=. rewrite Hetov Hetof.
  unfold to_val in Hetov.
  unfold iris.to_eff in Hetof.
  destruct (merge_values _) eqn:Hmerge => //.
  apply Hnonev in Hfilled as Hnone'.
  apply Hnonef in Hfilled as Hnone''.
  apply lfilled_to_sfill in Hfilled as Hsfill.
  destruct Hsfill as [sh Hsh].
  rewrite Hsh in Hnone'. rewrite sfill_to_llfill in Hnone'.
  rewrite Hsh in Hnone''. rewrite sfill_to_llfill in Hnone''.
  apply to_val_local_none in Hnone' as Hnone2.
(*    apply to_eff_local_none in Hnone'' as Hnone2'. *)

  iIntros (σ ns κ κs nt) "Hσ".
  destruct σ as [[s1 locs] inst].
  iDestruct "Hσ" as "(Hfuncs & Hconts & Htags & Htables & Hmems & Hglobals & Hframe & Hlen)".
  iDestruct (ghost_map_lookup with "Hframe Hf0") as %Hlook;rewrite lookup_insert in Hlook;inversion Hlook.
  iMod (ghost_map_update f with "Hframe Hf0") as "[Hframe Hf]"; rewrite insert_insert.
  iDestruct ("Hes1" with "Hf") as "Hes1".
  destruct f.
    
  destruct (to_val es1) eqn:Hetov'.
  { iMod "Hes1" as "[HPsi Hf]".
    iDestruct (ghost_map_lookup with "Hframe Hf") as %Hlook';rewrite lookup_insert in Hlook';inversion Hlook'.
    subst f1 f0.
    iMod (ghost_map_update {| f_locs := locs; f_inst := inst |}
           with "Hframe Hf") as "[Hframe Hf]"; rewrite insert_insert.
    iDestruct ("Hes2" with "[$]") as "Hes2".
    erewrite of_to_val;[|eauto].
    iDestruct ("Hes2" with "[]") as "Hes2".
    { iPureIntro. eauto. }
    iDestruct (ewp_frame_rewrite with "Hes2") as "Hes2".
    iDestruct (ewp_unfold with "Hes2") as "Hes2".
    rewrite /ewp_pre /= Hsh sfill_to_llfill Hnone' Hnone''.
    iSpecialize ("Hes2" $! (s1,locs,inst) ns κ κs nt with "[$]").
    iFrame. }

  destruct (iris.to_eff es1) eqn:Hetof'.
  { apply to_eff_None_lfilled_inv in Hfilled => //.
    apply to_eff_cat_None_inv in Hfilled.
    rewrite Hfilled in Hetof' => //.
    simpl in Hmerge.
    unfold to_eff.
    destruct (merge_values (map _ LI)) => //.
    destruct e1 => //. } 

  iSpecialize ("Hes1" $! (s1,f_locs,f_inst) ns κ κs nt with "[$]").
  iMod "Hes1" as "[%H1 H2]".
  iModIntro.
  iSplit.
  { iPureIntro.
    apply append_reducible with (es2:=es2) in H1;auto.
    eapply local_frame_lfilled_reducible. apply Hfilled. auto. }
  iIntros (e2 σ2 HStep').
  destruct σ2 as [[s3 locs2] inst2].
  eapply local_frame_lfilled_prim_step_split_reduce_r in HStep' as Heq;[|apply Hfilled|apply H1].
  destruct Heq as [[e' [v'' [i'' [LI' [HStep'' [-> [-> [-> Hfill]]]]]]]]|[lh' [Hlh'' HH]]].
  - apply prim_step_obs_efs_empty in HStep'' as Hemp.
    inversion Hemp;subst;clear Hemp.
    iSpecialize ("H2" $! e' (s3,v'',i'') HStep'').
    iMod "H2".
    repeat iModIntro.
    repeat iMod "H2".
    iDestruct "H2" as "(Hσ & H)".
    iDestruct "H" as (f) "(Hf1 & Hes'')". 
    iDestruct "Hσ" as "(Hfuncs& Hconts & Htags & Htables&Hmems&Hglobals&Hframe&Hlen)".
    iDestruct (ghost_map_lookup with "Hframe Hf1") as %Hlook';rewrite lookup_insert in Hlook';inversion Hlook'.
    subst f.
    apply lfilled_to_sfill in Hfill as Hsh.
    destruct Hsh as [sh' Hsh'].
    destruct (to_val [AI_local n {| f_locs := v''; f_inst := i'' |} e']) eqn:Hetov2.
    { apply to_val_local_inv in Hetov2 as Heq.
      destruct Heq as [tf [h [w [vh Heq]]]]. subst v.
      apply to_val_call_host_rec_local in Hetov2 as HH.
      destruct HH as [LI2 [HeqLI HLI]].
      rewrite app_nil_l app_nil_r in HeqLI. simplify_eq.
        
      iDestruct ("Hes''" with "[$]") as "Hes''".
      iDestruct (ewp_unfold with "Hes''") as "Hes''".
      rewrite /ewp_pre /= HLI.
      iMod "Hes''" as "[HPsi Hf]".
      iDestruct (ghost_map_lookup with "Hframe Hf") as %Hlook';rewrite lookup_insert in Hlook';inversion Hlook'.
      subst f1.
      iMod (ghost_map_update (Build_frame locs2 inst2) with "Hframe Hf") as "[Hframe Hf]"; rewrite insert_insert.
      iModIntro. iFrame.
      iIntros "Hf".
      iDestruct ("Hes2" with "[$]") as "Hes2".
      iDestruct ("Hes2" with "[]") as "Hes2".
      + iPureIntro. apply of_to_val in HLI. rewrite HLI. eauto. 
      + iFrame.
    } 
    destruct (to_eff [AI_local n {| f_locs := v''; f_inst := i'' |} e']) eqn:Hetof2.
    { apply to_eff_local_inv in Hetof2 as Heq.
      destruct Heq as [( vs & i' & she & ->) | [(vs & i' & k & tf & she) | (vs & i' & k & she)]].
      - apply to_eff_sus_local in Hetof2 as HH.
        destruct HH as [LI2 [HeqLI HLI]].
        rewrite app_nil_l app_nil_r in HeqLI. simplify_eq.
        iDestruct ("Hes''" with "[$]") as "Hes''".
        iDestruct (ewp_unfold with "Hes''") as "Hes''".
        rewrite /ewp_pre /= HLI.
        destruct (to_val LI2) eqn:Habs; first by exfalso; eapply to_val_to_eff.
        iDestruct "Hes''" as (f) "[Hf Hes'']".
        iDestruct (ghost_map_lookup with "Hframe Hf") as %Hlook';rewrite lookup_insert in Hlook';inversion Hlook'.
        subst.  
        iMod (ghost_map_update (Build_frame locs2 inst2) with "Hframe Hf") as "[Hframe Hf]"; rewrite insert_insert. 

        iModIntro. iFrame.
        iIntros "Hf".
        iDestruct ("Hes''" with "Hf") as (Ξ) "[Hprot Hcont]".
        (* iMod "Hes''" as "[HPsi Hf]". *)

        iApply ewp_unfold.
        rewrite /ewp_pre.
        destruct (to_val [AI_local _ _ (sfill _ _)]).
        { admit. }
        destruct (to_eff [AI_local _ _ (sfill _ _)]).
        2: admit.
        destruct e0.
        { iSimpl.
          iExists Ξ.
          iSplitL "Hprot".
          admit.
          iIntros (w) "Hw".
          iDestruct ("Hcont" with "Hw") as "Hcont".
        iDestruct ("Hes2" with "[$]") as "Hes2".
        iDestruct ("Hes2" with "[]") as "Hes2".
        { iPureIntro. apply of_to_val in HLI. rewrite HLI. eauto. }
        iFrame.
      }

      destruct (to_val e') eqn:Hetov3.
      { iDestruct ("Hes''" with "[$]") as "Hes''".
        iDestruct (ewp_unfold with "Hes''") as "Hes''".
        rewrite /ewp_pre /= Hetov3.
        iMod "Hes''" as "[HPsi Hf]".
        iDestruct (ghost_map_lookup with "Hframe Hf") as %Hlook'';rewrite lookup_insert in Hlook'';inversion Hlook''.
        subst f1.
        iMod (ghost_map_update (Build_frame locs2 inst2) with "Hframe Hf") as "[Hframe Hf]"; rewrite insert_insert.
        iModIntro. iFrame.
        (* iExists _. iFrame. *) iIntros "Hf".
        iDestruct ("Hes2" with "[$]") as "Hes2".
        iDestruct ("Hes2" with "[]") as "Hes2".
        { iPureIntro. erewrite of_to_val;eauto. }
        iFrame.
      } 
      
      assert (e' ++ es2 = sfill (SH_base [] es2) e') as Hsh'';[auto|].
      pose proof (sfill_nested sh' (SH_base [] es2) e') as [vh' Hvh'].
      
      apply to_val_local_none_inv with (vh:=ll_of_sh vh') in Hetov2 as Hetov4;[|auto].
      rewrite - sfill_to_llfill in Hetov4.
      rewrite -Hvh' -Hsh'' - Hsh' in Hetov4.

(*       iFrame. *)
      iMod (ghost_map_update (Build_frame locs2 inst2) with "Hframe Hf1") as "[Hframe Hf]"; rewrite insert_insert.
      iModIntro. iFrame.
      
(*      iExists _. iFrame. *)
      (*      iSplit => //. *)
      iIntros "Hf".
      iApply ("IH" with "[] [] [] [] [] [$] []");auto.
      iPureIntro. intros LI HLI.
      eapply lfilled_inj in Hfill;eauto.
      subst LI. auto.
      iPureIntro. intros LI HLI.
      eapply lfilled_inj in Hfill; eauto.
      subst LI. admit.
    } *)

  - (* trap case *)
    simplify_eq.
    set (σ:=(s3, f_locs, f_inst)).
    assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
    { unfold iris.prim_step.
      destruct σ as [[??]?].
      repeat split => //.
      apply r_simple; eapply rs_trap => //.
      move => HContra; subst. done.
    }
    destruct HStep' as [HStep' [-> _]].
    simplify_eq.
    iSpecialize ("H2" $! [AI_trap] σ HStep2).
    iMod "H2".
    repeat iModIntro.
    repeat iMod "H2".
    iDestruct "H2" as "(Hσ & H )".
    iDestruct "H" as (f2) "(Hf1 & Hes'')".
    iDestruct "Hσ" as "(Hfuncs&?&?&Htables&Hmems&Hglobals&Hframe&Hlen)".
    iDestruct (ghost_map_lookup with "Hframe Hf1") as %Hlook';rewrite lookup_insert in Hlook';inversion Hlook'.
    iSpecialize ("Hes''" with "[$]").
    replace [AI_trap] with (iris.of_val trapV); last done.
    rewrite ewp_unfold /ewp_pre /=.
    iMod "Hes''" as "[H _]".
    by iSpecialize ("Htrap" with "H").
Qed.  *)




(*
Lemma ewp_frame_seq es1 es2 n (f0 f f': frame) E P Ψ Φ :
  (to_val [AI_local n f (es1 ++ es2)] = None) ->
  ¬ Ψ trapV -∗ ↪[frame] f0 -∗
  ((↪[frame] f) -∗ EWP es1 @ E <| P |> {{ v, Ψ v ∗ ↪[frame] f'}}) -∗
  (∀ w, ↪[frame] f0 -∗ (Ψ w) -∗ EWP (iris.of_val w ++ es2) @ E FRAME n; f' <| P |> {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
  (EWP (es1 ++ es2) @ E FRAME n ; f <| P |> {{ v, Φ v ∗ ↪[frame]f0 }}).
Proof.
  iIntros (Hnone) "Htrap Hf Hes1 Hcont".
  iApply ewp_wasm_empty_ctx_frame.
  iApply (ewp_seq_ctx_frame with "[$Htrap $Hf $Hes1 Hcont]").
  { intros LI HLI%lfilled_Ind_Equivalent. inversion HLI. erewrite app_nil_l, app_nil_r. auto. } 
  iIntros (w) "[H1 H2]".
  iApply wp_wasm_empty_ctx_frame.
  iApply ("Hcont" with "[$] [$]").
Qed.
*)
  
End structural_rules.
