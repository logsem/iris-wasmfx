From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.language Require Export iris_ewp_def iris_ewp.
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
  destruct (iris.to_val es) as [vs|] eqn:Hes.
  - destruct vs.
    + apply of_to_val in Hes as <-. rewrite to_val_cons_immV. auto. 
    + apply to_val_trap_is_singleton in Hes as ->.
      unfold to_val, to_eff.
      rewrite (separate1 (AI_const _)).
      rewrite merge_prepend.
      rewrite to_val_instr_AI_const.
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
      * erewrite to_eff_cons_susE; eauto.
        iDestruct "H" as "(%Φ0 & HΨ & Hallw)".
        iExists Φ0.
        iFrame.
        iIntros (w) "Hw".
        iDestruct ("Hallw" with "Hw") as "Hres".
        rewrite susfill_sus_push_const /=.
        iApply ("IH" with "[$Hntrap $Hres]").
      * erewrite to_eff_cons_swE; eauto.
        iDestruct "H" as "(%Φ0 & HΨ & Hallw)".
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
              iDestruct "H" as "[Hσ H]".
              iFrame.
              iModIntro. 
              repeat rewrite ewp_unfold /ewp_pre /=.
              destruct (iris.to_val es2) eqn:Hx.
           ++ iMod "H".
              by iSpecialize ("Hntrap" with "H").
           ++ destruct (iris.to_eff es2) eqn:Habs.
              ** apply lfilled_to_eff in Hlf1.
                 2: by rewrite Habs.
                 destruct Hlf1 as [?|?] => //.
                 unfold to_eff in H.
                 simpl in H. destruct H => //.
              ** iIntros (?????) "?".
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
  iris.to_val vs = Some (immV v') ->
  (□ (¬ Φ trapV )) ∗
    EWP es @ E <| Ψ |> {{ v, (Φ (val_combine (immV v') v)) }}%I
  ⊢ EWP (vs ++ es) @ E <| Ψ |> {{ v, Φ v }}%I.
Proof.
  iIntros "%Hves [#Hntrap Hwp]".
  apply iris.of_to_val in Hves; subst.
  iApply ewp_val_app'.
  by iFrame.
Qed.

(* ctx must be restricted? *)
(*
Lemma wp_seq_ctx (E : coPset) Ψ (Φ Φ' : iris.val -> iProp Σ) (es1 es2 : language.expr wasm_lang) (i : nat) (lh : lholed) :
  ((¬ (Φ' trapV)) ∗
     EWP es1 @ E <| Ψ |> {{ w, Φ' w }} ∗
  ∀ w, (Φ' w -∗ EWP (iris.of_val w ++ es2) @ E CTX i; lh <| Ψ |> {{ v, Φ v }}))%I
  ⊢ EWP (es1 ++ es2) @ E CTX i; lh <| Ψ |> {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (E es1 es2 Φ Φ' Ψ i lh).
  iIntros "[Hntrap [Hes1 Hes2]]".
  iIntros (LI Hfilled).
  iApply ewp_unfold. rewrite /ewp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (iris.to_val LI) as [vs|] eqn:Hetov;
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
     eapply lfilled_to_eff_app in Hfilled as Hv;eauto.
     destruct Hv as [Hconst | [vs' [Hvs' Hfilled']]].
     + apply const_list_to_val in Hconst as (vs & Htv & <-).
       rewrite Htv.
       
       admit.
     + rewrite Hvs'.
       destruct (to_val es1) eqn:Habs.
       eapply to_val_to_eff in Habs => //.
       admit.
(*     iSpecialize ("Hes2" with "Hes1").
     iMod "Hes2".
     iSpecialize ("Hes2" $! _ Hfilled').
     iDestruct (ewp_unfold with "Hes2") as "Hes2".
     rewrite /ewp_pre /= Hetov.
     done. *)
   - repeat rewrite ewp_unfold. rewrite /ewp_pre /=.
     (* Ind *)
     iIntros (σ ns κ κs nt) "Hσ".
     destruct (iris.to_val es1) as [vs|] eqn:Hes;
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
     + admit.
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
         -- apply prim_step_obs_efs_empty in HStep'' as Hemp. inversion Hemp;subst;clear Hemp.
            iSpecialize ("H2" $! e' σ2 HStep'').
            iMod "H2".
            repeat iModIntro.
            repeat iMod "H2".
            iModIntro.
            iDestruct "H2" as "(Hσ & Hes)".
(*            iDestruct "Hes" as (f1) "(Hf & Hes'' & Hefs)". *)
            iFrame. (* iExists _. iFrame. *) 
(*            iSplit => //.
            iIntros "?"; iSpecialize ("Hes''" with "[$]"). *)
            iDestruct ("IH" with "[$Hntrap $Hes $Hes2]") as "Hcont"; by iApply "Hcont".
         -- assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
            { unfold iris.prim_step.
              destruct σ as [[??]?].
              repeat split => //.
              apply r_simple; eapply rs_trap => //.
              move => HContra; subst.
              by simpl in Hes.
            }
            clear Hlf.
            iSpecialize ("H2" $! [AI_trap] σ HStep2).
            iMod "H2".
            repeat iModIntro.
            repeat iMod "H2".
            destruct σ as [[? ?]?].
            iDestruct "H2" as "[Hσ H]".
            (* iDestruct "H" as (f) "(Hf1 & Hes'' & Hefs)". *)
            iModIntro => /=.
            iFrame. (* iExists _. iFrame. *) 
            (* iIntros "?"; iSpecialize ("Hes''" with "[$]"). *)
            replace [AI_trap] with (iris.of_val trapV) => //=.
            iDestruct (ewp_unfold with "H") as "H";rewrite /ewp_pre /=.
            destruct (iris.to_val e2) eqn:Hx;
              last destruct (iris.to_eff e2) eqn:Hy.
            ++ iApply ewp_unfold.  rewrite /ewp_pre /= Hx /=.
               iMod "H". 
               by iSpecialize ("Hntrap" with "H"). 
            ++ iApply ewp_unfold. rewrite /ewp_pre /= Hx Hy /=.
               admit.
            ++ iApply ewp_unfold. rewrite /ewp_pre /= Hx Hy /=.
               iIntros (?????) "?".
               iMod "H".
               by iSpecialize ("Hntrap" with "H").
Qed. *)



(* Contextual rules for Local computation *)


Lemma ewp_frame_rewrite (E: coPset) Ψ (Φ: val -> iProp Σ) es n f:
  EWP es @ E FRAME n; f <| Ψ |> {{ v, Φ v }} ⊣⊢
                        EWP [AI_local n f es] @ E <| Ψ |> {{ v, Φ v }}.
Proof.
  trivial.
Qed.

Lemma ewp_frame_value (E : coPset) Ψ (Φ : val -> iProp Σ) es n f f0 vs :
  iris.to_val es = Some (immV vs) ->
  length es = n ->
  ↪[frame] f0 -∗
  ▷ (Φ (immV vs)) -∗
                     EWP es @ E FRAME n; f <| Ψ |> {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hv Hlen) "Hframe H".
  rewrite ewp_frame_rewrite.
  apply to_val_const_list in Hv as Hconst.
  iApply (ewp_lift_atomic_step with "[H Hframe]"); simpl ; trivial;eauto.
  unfold iris.to_val => /=.
  apply const_list_to_val in Hconst as (? & ? & ?).
  unfold iris.to_val in H.
  destruct (merge_values $ map _ _) => //.
  by inversion H.
  unfold to_eff => /=.
  apply const_list_to_val in Hconst as (? & ? & ?).
  unfold iris.to_val in H.
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
    iris_ewp_def.only_one_reduction H. all:simplify_eq;iFrame. rewrite Hv. iFrame.
    1,2:rewrite find_first_const// in Hstart.
Qed.

(*
Lemma ewp_seq_ctx_frame (E : coPset) P (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) (i : nat) (lh : lholed) (n : nat) (f : frame) (f0 : frame) (f1 : frame) :
  (forall LI, lfilled i lh (es1 ++ es2) LI -> iris.to_val [AI_local n f LI] = None) ->
  ((¬ (Ψ trapV)) ∗ ↪[frame] f0 ∗
   (↪[frame] f -∗ EWP es1 @ E <| P |> {{ w, Ψ w ∗ ↪[frame] f1 }}) ∗
  ∀ w, Ψ w ∗ ↪[frame] f0 -∗ EWP (iris.of_val w ++ es2) @ E FRAME n ; f1 CTX i; lh <| P |> {{ v, Φ v }})%I
  ⊢ EWP (es1 ++ es2) @ E FRAME n ; f CTX i; lh <| P |> {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (E es1 es2 P Φ Ψ i lh n f f0 f1).
{ iIntros (Hnone) "[Htrap [Hf0 [Hes1 Hes2]]]".
  iIntros (LI Hfilled).
  iApply ewp_unfold.
  (* Base case, when both es1 and es2 are values *)

  destruct (iris.to_val [AI_local n f LI]) as [vs|] eqn:Hetov.
  { assert (iris.to_val [AI_local n f LI] = Some vs) as Hetov' => //.
    unfold iris.to_val in Hetov ; simpl in Hetov.
    destruct (merge_values $ map _ _) eqn:Hmerge => //.
    2: destruct e => //. 
    destruct v => //.
    eapply lfilled_to_val_app in Hfilled as Heq;[|eauto] ; last first.
    unfold to_val ; rewrite Hmerge => //. 
    destruct Heq as [vs' [Heq Hfilled']].
    repeat rewrite ewp_unfold /ewp_pre /=.
    rewrite Heq. apply Hnone in Hfilled. congruence.
    
  }
  destruct (iris.to_eff [AI_local n f LI]) as [eff|] eqn:Hetof.
  { assert (iris.to_eff [AI_local n f LI] = Some eff) as Hetof' => //.
    unfold iris.to_eff in Hetof; simpl in Hetof.
    destruct (merge_values $ map _ _) eqn:Hmerge => //.
    destruct v => //.
    eapply lfilled_to_eff_app in Hfilled as Heq; last first.
    unfold to_eff; rewrite Hmerge => //.
    destruct Heq as [Hconst | (vs' & Heq & Hfilled')].
    - admit.
    - repeat rewrite ewp_unfold /ewp_pre /=.
      rewrite Heq. apply Hnone in Hfilled. congruence.
    2: destruct e => //.

  { repeat rewrite ewp_unfold /ewp_pre /=. rewrite Hetov.
    unfold iris.to_val in Hetov.
    destruct (merge_values _) eqn:Hmerge => //.
    apply Hnone in Hfilled as Hnone'.
    apply lfilled_to_sfill in Hfilled as Hsfill.
    destruct Hsfill as [sh Hsh].
    rewrite Hsh in Hnone'. rewrite sfill_to_llfill in Hnone'.
    apply to_val_local_none in Hnone' as Hnone2.

    iIntros (σ ns κ κs nt) "Hσ".
    destruct σ as [[s1 locs] inst].
    iDestruct "Hσ" as "(Hfuncs&Htables&Hmems&Hglobals&Hframe&Hlen)".
    iDestruct (ghost_map_lookup with "Hframe Hf0") as %Hlook;rewrite lookup_insert in Hlook;inversion Hlook.
    iMod (ghost_map_update f with "Hframe Hf0") as "[Hframe Hf]"; rewrite insert_insert.
    iDestruct ("Hes1" with "Hf") as "Hes1".
    destruct f.

    
    destruct (iris.to_val es1) eqn:Hetov'.
    { iMod "Hes1" as "[HPsi Hf]".
      iDestruct (ghost_map_lookup with "Hframe Hf") as %Hlook';rewrite lookup_insert in Hlook';inversion Hlook'.
      subst f1 f0.
      iMod (ghost_map_update {| f_locs := locs; f_inst := inst |}
             with "Hframe Hf") as "[Hframe Hf]"; rewrite insert_insert.
      iDestruct ("Hes2" with "[$]") as "Hes2".
      erewrite of_to_val;[|eauto].
      iDestruct ("Hes2" with "[]") as "Hes2".
      { iPureIntro. eauto. }
      iDestruct (wp_frame_rewrite with "Hes2") as "Hes2".
      iDestruct (wp_unfold with "Hes2") as "Hes2".
      rewrite /wp_pre /= Hsh sfill_to_llfill Hnone'.
      iSpecialize ("Hes2" $! (s1,locs,inst) ns κ κs nt with "[$]").
      iFrame. }

    

    iSpecialize ("Hes1" $! (s1,f_locs,f_inst) ns κ κs nt with "[$]").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    { iPureIntro.
      destruct s => //.
      apply append_reducible with (es2:=es2) in H1;auto.
      eapply local_frame_lfilled_reducible. apply Hfilled. auto. }
    iIntros (e2 σ2 efs HStep').
    destruct σ2 as [[s3 locs2] inst2].
    eapply local_frame_lfilled_prim_step_split_reduce_r in HStep' as Heq;[|apply Hfilled|apply H1].
    destruct Heq as [[e' [v'' [i'' [LI' [HStep'' [-> [-> [-> Hfill]]]]]]]]|[lh' [Hlh HH]]].
    { apply prim_step_obs_efs_empty in HStep'' as Hemp. inversion Hemp;subst;clear Hemp.
      iSpecialize ("H2" $! e' (s3,v'',i'') [] HStep'').
      iMod "H2".
      repeat iModIntro.
      repeat iMod "H2".
      iDestruct "H2" as "(Hσ & H)".
      iDestruct "H" as (f) "(Hf1 & Hes'' & Hefs)".
      iDestruct "Hσ" as "(Hfuncs&Htables&Hmems&Hglobals&Hframe&Hlen)".
      iDestruct (ghost_map_lookup with "Hframe Hf1") as %Hlook';rewrite lookup_insert in Hlook';inversion Hlook'.
      subst f.
      apply lfilled_to_sfill in Hfill as Hsh.
      destruct Hsh as [sh' Hsh'].
      destruct (iris.to_val [AI_local n {| f_locs := v''; f_inst := i'' |} e']) eqn:Hetov2.
      { apply to_val_local_inv in Hetov2 as Heq.
        destruct Heq as [tf [h [w [vh Heq]]]]. subst v.
        
        apply to_val_call_host_rec_local in Hetov2 as HH.
        destruct HH as [LI2 [HeqLI HLI]].
        rewrite app_nil_l app_nil_r in HeqLI. simplify_eq.
        
        iDestruct ("Hes''" with "[$]") as "Hes''".
        iDestruct (wp_unfold with "Hes''") as "Hes''".
        rewrite /wp_pre /= HLI.
        iMod "Hes''" as "[HPsi Hf]".
        iDestruct (ghost_map_lookup with "Hframe Hf") as %Hlook';rewrite lookup_insert in Hlook';inversion Hlook'.
        subst f1.
        iMod (ghost_map_update (Build_frame locs2 inst2) with "Hframe Hf") as "[Hframe Hf]"; rewrite insert_insert.
        iModIntro. iFrame.
        (* iExists _. iFrame. *)  iIntros "Hf".
        iDestruct ("Hes2" with "[$]") as "Hes2".
        iDestruct ("Hes2" with "[]") as "Hes2".
        { iPureIntro. apply of_to_val in HLI. rewrite HLI. eauto. }
        iFrame.
      }

      destruct (iris.to_val e') eqn:Hetov3.
      { iDestruct ("Hes''" with "[$]") as "Hes''".
        iDestruct (wp_unfold with "Hes''") as "Hes''".
        rewrite /wp_pre /= Hetov3.
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
      iSplit => //. iIntros "Hf".
      iApply ("IH" with "[] [$] []");auto.
      iPureIntro. intros LI HLI.
      eapply lfilled_inj in Hfill;eauto.
      subst LI. auto.
    }

    (* trap case *)
    simplify_eq.
    set (σ:=(s3, f_locs, f_inst)).
    assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
    { unfold iris.prim_step.
      destruct σ as [[??]?].
      repeat split => //.
      apply r_simple; eapply rs_trap => //.
      move => HContra; subst. done.
    }
    destruct HStep' as [HStep' [-> ->]].
    simplify_eq.
    iSpecialize ("H2" $! [AI_trap] σ [] HStep2).
    iMod "H2".
    repeat iModIntro.
    repeat iMod "H2".
    iDestruct "H2" as "(Hσ & H )".
    iDestruct "H" as (f2) "(Hf1 & Hes'' & Hefs)".
    iDestruct "Hσ" as "(Hfuncs&Htables&Hmems&Hglobals&Hframe&Hlen)".
    iDestruct (ghost_map_lookup with "Hframe Hf1") as %Hlook';rewrite lookup_insert in Hlook';inversion Hlook'.
    iSpecialize ("Hes''" with "[$]").
    replace [AI_trap] with (iris.of_val trapV) => //=.
    
    destruct (iris.to_val e2) eqn:Hx.
    * rewrite wp_unfold /wp_pre /=. iMod "Hes''" as "[Hes'' _]".
      by iSpecialize ("Htrap" with "Hes''").
    * rewrite wp_unfold /wp_pre /=. iMod "Hes''" as "[Hes'' _]".
      by iSpecialize ("Htrap" with "Hes''").
      Unshelve. all: try apply 0. all: apply [].
  } }
Qed. *)

Lemma ewp_seq (E : coPset) P (Φ Ψ : val -> iProp Σ) (es1 es2 : language.expr wasm_lang) :
  to_val es1 = None ->
  ((* ¬ Ψ trapV ∗  *)
     EWP es1 @ E <| P |> {{ w, Ψ w }} ∗
  ∀ w, Ψ w -∗ EWP (iris.of_val w ++ es2) @ E <| P |> {{ v, Φ v }})
  ⊢ EWP (es1 ++ es2) @ E <| P |> {{ v, Φ v }}.
Proof.
  iLöb as "IH" forall (E es1 es2 P Φ Ψ).
  iIntros (Hes1) "(Hes1 & Hes2)".
  (* Base case, when both es1 and es2 are values *)
  iApply ewp_unfold. repeat rewrite ewp_unfold /ewp_pre /=.
  rewrite Hes1.
  rewrite to_val_cat_None1 => //.
  destruct (iris.to_eff (es1 ++ es2)) as [eff|] eqn:Hetof.
(*  - assert (lfilled 0 (LH_base [] []) (es1 ++ es2) (es1 ++ es2)) as Hfilled.
    { cbn. erewrite app_nil_r. by apply/eqP. }
    eapply lfilled_to_val_app in Hfilled as Hv;eauto.
    destruct Hv as [vs' [Hvs' Hfilled']].
    unfold iris_ewp_def.to_val in Hvs'.
    rewrite Hvs'.
    iSpecialize ("Hes2" with "Hes1").
    iMod "Hes2".
    apply lfilled_Ind_Equivalent in Hfilled';inversion Hfilled';simplify_eq.
    erewrite app_nil_r in H1.
    assert (iris.of_val vs' ++ es2 = es1 ++ es2) as ->;auto.
    iDestruct (ewp_unfold with "Hes2") as "Hes2". rewrite /ewp_pre /= Hetov.
    done. *)
  - assert (lfilled 0 (LH_base [] []) (es1 ++ es2) (es1 ++ es2)) as Hfilled.
    { cbn. erewrite app_nil_r. by apply/eqP. }
    eapply lfilled_to_eff_app in Hfilled as Hv;eauto.
    destruct Hv as [Hconst | [vs' [Hvs' Hfilled']]].
    + apply const_list_to_val in Hconst as (vs & Htv & Hvs).
      rewrite Hes1 in Htv. done.
    + rewrite Hvs'.
    iSpecialize ("Hes2" with "Hes1").
    iMod "Hes2".
    apply lfilled_Ind_Equivalent in Hfilled';inversion Hfilled';simplify_eq.
    erewrite app_nil_r in H1.
    assert (iris.of_val vs' ++ es2 = es1 ++ es2) as ->;auto.
    iDestruct (ewp_unfold with "Hes2") as "Hes2". rewrite /ewp_pre /= Hetov.
    done.
  - (* Ind *)
  iIntros (σ ns κ κs nt) "Hσ".
  destruct (iris.to_val es1) as [vs|] eqn:Hes.
  { apply of_to_val in Hes as <-.
    iMod "Hes1".
    iSpecialize ("Hes2" with "Hes1").
    iDestruct (wp_unfold with "Hes2") as "Hes2"; rewrite /wp_pre /=.
    rewrite Hetov.
    iSpecialize ("Hes2" $! σ ns κ κs nt with "[$]").
    iMod "Hes2" as "[%H1 H2]".
    iIntros "!>".
    iSplit.
    - iPureIntro. by apply H1. 
    - by iApply "H2".
  }
  {
    iSpecialize ("Hes1" $! σ ns κ κs nt with "[$]").
    iMod "Hes1" as "[%H1 H2]".
    iModIntro.
    iSplit.
    - iPureIntro.
      destruct s => //.
      by apply append_reducible.
    - iIntros (e2 σ2 efs HStep).
      assert (κ = [] /\ efs = []) as [-> ->]; first by apply prim_step_obs_efs_empty in HStep; inversion HStep.
      apply prim_step_split_reduce_r in HStep; last by [].
      destruct HStep as [[es'' [-> HStep]] | [n [m [lh [Hlf1 [Hlf2 ->]]]]]].
      + iSpecialize ("H2" $! es'' σ2 [] HStep).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        iModIntro.
        destruct σ2 as [[??]?].
        iDestruct "H2" as "[Hσ H]".
        iDestruct "H" as (f1) "(Hf1 & Hes'' & Hefs)".
        iFrame. (* iExists _. iFrame. *) 
        iIntros "?"; iSpecialize ("Hes''" with "[$]").
        iApply "IH".
        by iFrame. 
      + move/lfilledP in Hlf1.
        inversion Hlf1; subst; clear Hlf1.
        assert (iris.prim_step es1 σ [] [AI_trap] σ []) as HStep2.
        { unfold iris.prim_step.
          destruct σ as [[??]?].
          repeat split => //.
          apply r_simple; eapply rs_trap => //.
          move => HContra; subst.
          by destruct n.
        }
        iSpecialize ("H2" $! [AI_trap] σ [] HStep2).
        iMod "H2".
        repeat iModIntro.
        repeat iMod "H2".
        destruct σ as [[??]?].
        iDestruct "H2" as "[Hσ H]".
        iDestruct "H" as (f1) "(Hf1 & Hes'' & Hefs)".
        iFrame. (* iExists _. iFrame. *) 
        iModIntro.
        iFrame.
        iIntros "?"; iSpecialize ("Hes''" with "[$]").
        replace [AI_trap] with (iris.of_val trapV) => //.
        repeat rewrite wp_unfold /wp_pre /=.
        destruct (iris.to_val (take n es1 ++ AI_trap :: drop m (es1 ++ es2))%SEQ) eqn:Hx.
        * iMod "Hes''".
          by iSpecialize ("Hntrap" with "Hes''").
        * iIntros (?????) "?".
          iMod "Hes''".
          by iSpecialize ("Hntrap" with "Hes''").
  }
Qed.

Lemma wp_wand_ctx s E e Φ Ψ i lh :
  WP e @ s; E CTX i; lh {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WP e @ s; E CTX i; lh {{ Ψ }}.
Proof.
  iIntros "Hwp H". iIntros (LI HLI).
  iSpecialize ("Hwp" $! LI HLI).
  iApply (wp_wand with "Hwp"). auto.
Qed.


Lemma wp_frame_seq es1 es2 n (f0 f f': frame) E s Ψ Φ :
  (iris.to_val [AI_local n f (es1 ++ es2)] = None) ->
  ¬ Ψ trapV -∗ ↪[frame] f0 -∗
  ((↪[frame] f) -∗ WP es1 @ NotStuck; E {{ v, Ψ v ∗ ↪[frame] f'}}) -∗
  (∀ w, ↪[frame] f0 -∗ (Ψ w) -∗ WP (iris.of_val w ++ es2) @ s; E FRAME n; f' {{ v, Φ v ∗ ↪[frame] f0 }}) -∗
  (WP (es1 ++ es2) @ s; E FRAME n ; f {{ v, Φ v ∗ ↪[frame]f0 }}).
Proof.
  iIntros (Hnone) "Htrap Hf Hes1 Hcont".
  iApply wp_wasm_empty_ctx_frame.
  iApply (wp_seq_ctx_frame with "[$Htrap $Hf $Hes1 Hcont]").
  { intros LI HLI%lfilled_Ind_Equivalent. inversion HLI. erewrite app_nil_l, app_nil_r. auto. } 
  iIntros (w) "[H1 H2]".
  iApply wp_wasm_empty_ctx_frame.
  iApply ("Hcont" with "[$] [$]").
Qed.
  
End structural_rules.
