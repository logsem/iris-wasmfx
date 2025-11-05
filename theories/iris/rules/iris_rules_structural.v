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



Lemma ewp_wasm_empty_ctx (E : coPset) (f: frame) (Ψ : meta_protocol) (Φ : val0 -> frame -> iProp Σ) (e: expr0) :
  ⊢ EWP e UNDER f @ E <| Ψ |> {{ Φ }} ∗-∗ EWP e UNDER f @ E CTX_EMPTY <| Ψ |> {{ Φ }}.
Proof.
  iSplit.
  { iIntros "HWP". iIntros (LI Hfill%lfilled_Ind_Equivalent).
    inversion Hfill. subst. erewrite app_nil_l; erewrite app_nil_r. done. }
  { iIntros "HWP".
    iDestruct ("HWP" $! e with "[]") as "$".
    iPureIntro. cbn. rewrite app_nil_r eqseqE. apply eq_refl. }
Qed.

Lemma ewp_wasm_empty_ctx_frame (E : coPset) f Ψ (Φ : val0 -> frame -> iProp Σ) e n f' :
  ⊢ EWP e UNDER f @ E FRAME n; f' <| Ψ |> {{ Φ }} ∗-∗ EWP e UNDER f @ E FRAME n; f' CTX_EMPTY <| Ψ |> {{ v ; h , Φ v h }}.
Proof.
  iSplit.
  { iIntros "HWP". iIntros (LI Hfill%lfilled_Ind_Equivalent).
    inversion Hfill. subst. erewrite app_nil_l; erewrite app_nil_r. done. }
  { iIntros "HWP".
    iDestruct ("HWP" $! e with "[]") as "$".
    iPureIntro. cbn. rewrite app_nil_r eqseqE. apply eq_refl. }
Qed.

Lemma ewp_nil (E : coPset) f Ψ (Φ : iProp Σ):
  Φ ⊢ EWP [] UNDER f @ E CTX_EMPTY <| Ψ |> {{ fun v f => Φ }}%I.
Proof.
  iIntros "H". iApply ewp_wasm_empty_ctx.
  rewrite ewp_unfold /ewp_pre /=. iFrame. eauto.
Qed.

Lemma ewp_val (E : coPset) f Ψ (Φ : val0 -> frame -> iProp Σ) (v0 : value) (es : expr0) :
  ((∀ f, ¬ Φ trapV f) ∗
     EWP es UNDER f @ E <| Ψ |> {{ v ; h , (Φ (val_combine (immV [v0]) v) h)  }}
     ⊢ EWP (AI_const v0 :: es) UNDER f @ E <| Ψ |> {{ v ; h , Φ v h }})%I.
Proof.
  iLöb as "IH" forall (v0 es f Φ).
  iIntros "(Hntrap & H)".
  iApply ewp_unfold.               
  repeat rewrite ewp_unfold /ewp_pre /=.
  destruct (to_val0 es) as [vs|] eqn:Hes.
  - destruct vs.
    + apply of_to_val0 in Hes as <-.
      rewrite to_val_cons_immV. auto.
    + apply to_val_trap_is_singleton in Hes as ->.
      unfold to_val0, to_eff0.
      rewrite (separate1 (AI_const _)).
      rewrite merge_prepend.
      rewrite /= to_val_instr_AI_const.
      simpl.
      iIntros (?) "?".
      iMod "H" as "H".
      by iSpecialize ("Hntrap" with "H").
    + erewrite to_val_cons_brV;eauto.
    + erewrite to_val_cons_retV;eauto.
    + erewrite to_val_cons_callHostV;eauto.
  - rewrite to_val_cons_None => //.
    destruct (iris.to_eff0 es) as [eff|] eqn:Hesf.
    + destruct eff.
      * erewrite to_eff_cons_susE; last done.
        iDestruct "H" as "(%Φ0 & HΨ & Hallw)".
        iFrame. 
        iIntros (w) "Hw".
        iDestruct ("Hallw" with "Hw") as "Hres".
        rewrite susfill_sus_push_const /=.
        iApply ("IH" with "[$Hntrap $Hres]"). 
      * erewrite to_eff_cons_swE; last done.
        destruct i.
        iDestruct "H" as "(%cont & %t1s & %t2s & %tf' & %ts & #Htag & Hk & -> & -> & Hcont & %Φ0 & HΨ & Hallw)".
        iFrame "#".
        iFrame.
        iExists _,_,_.
        iSplit; first done. iSplit; first done.
        iIntros (w) "Hw".
        iDestruct ("Hallw" with "Hw") as "Hres".
        rewrite swfill_sw_push_const /=.
        iApply "IH".
        iFrame.
      * erewrite to_eff_cons_thrE; eauto.
    + rewrite to_eff_cons_None => //.
      iIntros (σ) "Hσ".
      iSpecialize ("H" $! σ with "[$]").
      iMod "H".
      iModIntro.
      iDestruct "H" as "(%H1 & H)".
      iSplit.
      * iPureIntro.
        destruct σ => //=.
        rewrite - cat1s.
        eapply prepend_reducible; eauto.
        left. rewrite /= const_const //.
      * iIntros ([es2 f2] s2 HStep).
        rewrite -cat1s in HStep.
        eapply reduce_ves in H1.
        2:{ exact HStep. }
        destruct H1 as [[-> HStep2] | [lh1 [lh2 [Hlf1 [Hlf2 Hσ]]]]].
        -- iSpecialize ("H" $! (drop 1 es2, _) s2 HStep2).
           iMod "H".
           repeat iModIntro.
           repeat iMod "H".
           iModIntro.
           iDestruct "H" as "[Hσ H]".
           iSimpl.
           iFrame.
           iApply "IH".
           by iFrame.
        -- eassert (iris.prim_step (es, _) _ [] ([AI_trap], _) _ []) as HStep2.
           { unfold iris.prim_step.
             repeat split => //.
             apply r_simple; eapply rs_trap => //.
             intros ->.
             unfold to_val0 in Hes. simpl in Hes. done. } 
           iSpecialize ("H" $! ([AI_trap], _) _ HStep2).
           iMod "H".
           repeat iModIntro.
           repeat iMod "H".
           iDestruct "H" as "(Hσ & H)".
           inversion Hσ; subst.
           iFrame.
           iIntros "!>".
           iApply fupd_ewp.
           { destruct (to_eff0 es2) eqn:Habs => //.
             apply lfilled_to_eff in Hlf1.
             2: by rewrite Habs.
             destruct Hlf1 as [?|?] => //.
             unfold to_eff0 in H.
             simpl in H. destruct H => //. }
           repeat rewrite ewp_unfold /ewp_pre /=.
           iMod "H" as "H".
           by iSpecialize ("Hntrap" with "H").
Qed.


Lemma ewp_val_app' (E : coPset) f Ψ (Φ : val0 -> frame -> iProp Σ) vs (es : expr0) :
  (□ (∀ f, ¬ Φ trapV f)) ∗
    EWP es UNDER f @ E <| Ψ |> {{ v ; h , (Φ (val_combine (immV vs) v) h) }}%I
  ⊢ EWP ((v_to_e_list vs) ++ es) UNDER f @ E <| Ψ |> {{ v ; h, Φ v h }}%I.

Proof.
  iInduction vs as [|c vs] "IH" forall (Ψ  Φ E es).
  { simpl.
    iIntros "(#Hntrap & HWP)".
    iApply (ewp_wand with "HWP").
    iIntros (v ?).
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
    iIntros (vs' ?) "HΦ".
    iSimpl. unfold val_combine.
    destruct vs';auto; simpl.
    - iExFalso. iApply ("Hntrap" with "HΦ").
    - by rewrite -vh_push_const_app.
    - by rewrite -sh_push_const_app.
    - by rewrite -llh_push_const_app.
  }
Qed.
  
Lemma ewp_val_app (E : coPset) f Ψ (Φ : val0 -> frame -> iProp Σ) vs v' (es : expr0) :
  to_val0 vs = Some (immV v') ->
  (□ (∀ f, ¬ Φ trapV f)) ∗
    EWP es UNDER f @ E <| Ψ |> {{ v ; h, (Φ (val_combine (immV v') v) h) }}%I
  ⊢ EWP (vs ++ es) UNDER f @ E <| Ψ |> {{ v ; h, Φ v h }}%I.
Proof.
  iIntros "%Hves [#Hntrap Hwp]".
  apply iris.of_to_val0 in Hves; subst.
  iApply ewp_val_app'.
  by iFrame.
Qed.



Definition lh_eff_None lh :=
  let '(_,_,es) := empty_base lh in
  to_eff0 es = None.

Lemma lh_eff_None_spec lh :
  lh_eff_None lh -> (forall i vs LI, const_list vs -> lfilled i lh vs LI ->
                               to_eff0 LI = None).
Proof.
  unfold lh_eff_None. induction lh => //=.
    all: intros Htf i vs LI Hvs Hfill.
    all: move/lfilledP in Hfill.
    all: inversion Hfill; subst.
    all: apply to_eff_cat_None2 => //.
    + apply to_eff_cat_None2 => //.
    + destruct (empty_base lh) as [[??]?] eqn:Hbase.
      unfold to_eff0 => /=.
      move/lfilledP in H8.
      apply IHlh in H8 => //.
      unfold to_eff0 in H8.
      destruct (merge_values (map _ LI0)) => //.
      destruct v => //.
      3: destruct i => //.
      4: destruct (vh_decrease _) => //.
      all: try by rewrite merge_notval.
      rewrite merge_br => //.
      rewrite merge_return => //.
      rewrite merge_call_host => //.
    +  destruct (empty_base lh) as [[??]?] eqn:Hbase.
      unfold to_eff0 => /=.
      move/lfilledP in H7.
      apply IHlh in H7 => //.
      unfold to_eff0 in H7.
      destruct (merge_values (map _ LI0)) => //.
      destruct v => //.
      all: try by rewrite merge_notval.
      rewrite merge_br => //.
      rewrite merge_return => //.
      rewrite merge_call_host => //.
    + destruct (empty_base lh) as [[??]?] eqn:Hbase.
      unfold to_eff0 => /=.
      move/lfilledP in H8.
      apply IHlh in H8 => //.
      unfold to_eff0 in H8.
      destruct (merge_values (map _ LI0)) => //.
      destruct v => //.
      all: try by rewrite merge_notval.
      rewrite merge_br => //.
      rewrite merge_return => //.
      rewrite merge_call_host => //.
Qed. 
      
    
      

(*
 Lemma ewp_bind es E Ψ i lh Φ:
  is_pure lh ->
  EWP es UNDER f @ E <| Ψ |> {{ w, ⌜ w <> trapV ⌝ ∗
    EWP of_val w UNDER f @ E CTX i; lh <| Ψ |> {{ Φ }} }}
    ⊢ EWP es UNDER f @ E CTX i; lh <| Ψ |> {{ Φ }}.
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

         iSpecialize ("IH" $! lh f h Ψ (susfill i0 shin (of_val w)) _ _ Hpure).
         iDestruct ("IH" with "H") as "H".

         iSpecialize ("H" $! _ Hfilled).
         iExact "H".
     + admit.
     + admit.
   - repeat rewrite ewp_unfold. rewrite /ewp_pre /=.
     (* Ind *)
     iIntros (σ) "Hσ".
     destruct (to_val es) as [vs|] eqn:Hes;
       last destruct (iris.to_eff es) as [eff |] eqn:Heff.
     + apply of_to_val in Hes as <-.
       iMod "H".
       iDestruct "H" as "[%Hntrap H]".
       iSpecialize ("H" $! _ HLI).
       iDestruct (ewp_unfold with "H") as "H"; rewrite /ewp_pre /=.
       rewrite He He'.
       iSpecialize ("H" $! σ with "[$]").
       iFrame.
     + apply to_eff_None_lfilled_inv in HLI => //.
       rewrite HLI in Heff => //. 
     + iSpecialize ("H" $! σ with "[$]").
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


Lemma ewp_seq (E : coPset) f P (Φ Ψ : val0 -> frame -> iProp Σ) (es1 es2 : expr0) :
  to_eff0 es2 = None ->
  ( (∀ f, ¬ Ψ trapV f) ∗  
     EWP es1 UNDER f @ E <| P |> {{ w ; h , Ψ w h}} ∗
  ∀ w f', Ψ w f' -∗ EWP (iris.of_val0 w ++ es2) UNDER f' @ E <| P |> {{ v ; h , Φ v h }})
  ⊢ EWP (es1 ++ es2) UNDER f @ E <| P |> {{ v ; h , Φ v h }}.
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
  iLöb as "IH" forall (E es1 es2 f P  Φ Ψ).
  iIntros (*es1 Hes1*) (Hes2)  "(Hntrap & Hes1 & Hes2)".
  (* Base case, when both es1 and es2 are values *)
  iApply ewp_unfold. repeat rewrite ewp_unfold /ewp_pre /=.
(*  rewrite Hes1. *)
  (*  rewrite to_val_cat_None1 => //. *)
  destruct (to_val0 (es1 ++ es2)) as [v|] eqn:Hetov; last
  destruct (iris.to_eff0 (es1 ++ es2)) as [eff|] eqn:Hetof.
  - assert (lfilled 0 (LH_base [] []) (es1 ++ es2) (es1 ++ es2)) as Hfilled.
    { cbn. erewrite app_nil_r. by apply/eqP. }
    eapply lfilled_to_val_app in Hfilled as Hv;eauto.
    destruct Hv as [vs' [Hvs' Hfilled']].
    rewrite Hvs'.
    iMod "Hes1" as "Hes1".
    iSpecialize ("Hes2" with "Hes1").
    apply lfilled_Ind_Equivalent in Hfilled';inversion Hfilled';simplify_eq.
    erewrite app_nil_r in H1.
    assert (iris.of_val0 vs' ++ es2 = es1 ++ es2) as ->;auto.
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
(*         
        destruct (@const_list_to_val (v_to_e_list esv)) as (vs' & Htv & Hvs').
        apply v_to_e_is_const_list.
        apply v_to_e_inj in Hvs' as ->.
        rewrite Htv.
        simpl in Hout.
        inversion Hout; subst.
        iSimpl. rewrite sus_push_const_nil.
        rewrite sus_append_nil.
        rewrite sus_append_nil.
        a dmit. *)
      * destruct (to_val0 es1) eqn:Habs; first by exfalso; eapply to_val_to_eff.
        rewrite Hin.
        iDestruct "Hes1" as (Ξ) "[HΞ Hnext]".
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
      * destruct (to_val0 es1) eqn:Habs; first by exfalso; eapply to_val_to_eff.
        rewrite Hin.
        destruct i.
        iDestruct "Hes1" as (cont t1s t2s tf' ts) "(#Htag & Hk & -> & -> & Hcont & Hes1)".
        iDestruct "Hes1" as (Ξ) "[HΞ Hnext]".
        iFrame.
        iFrame "#".
        iExists _,_,_. iSplit; first done. iSplit; first done.
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
      * destruct (to_val0 es1) eqn:Habs; first by exfalso; eapply to_val_to_eff.
        rewrite Hin.
        iFrame. 
      * constructor.
  - (* Ind *)
    iIntros (σ) "Hσ".
    apply to_eff_cat_None_inv in Hetof as Hetof'.
    rewrite Hetof'.
    destruct (to_val0 es1) as [vs|] eqn:Hes.
    + apply of_to_val0 in Hes as <-.
      iMod "Hes1" as "Hes1".
      iSpecialize ("Hes2" with "Hes1").
      iDestruct (ewp_unfold with "Hes2") as "Hes2"; rewrite /ewp_pre /=.
      rewrite Hetov Hetof.
      iSpecialize ("Hes2" $! σ with "[$]").
      iMod "Hes2" as "[%H1 H2]".
      iIntros "!>".
      iSplit.
      * iPureIntro. by apply H1. 
      * by iApply "H2".
    + iSpecialize ("Hes1" $! σ with "[$]").
      iMod "Hes1" as "[%H1 H2]".
      iModIntro.
      iSplit.
      * iPureIntro.
        by apply append_reducible.
      * iIntros ([e2 f2] s2 HStep).
        apply (prim_step_split_reduce_r es1 es2 e2 σ s2) in HStep ; last by [].
        destruct HStep as [[es'' [-> HStep]] | [n [m [lh [Hlf1 [Hlf2 Hσ]]]]]]; last inversion Hσ; subst.
        -- iSpecialize ("H2" $! (es'', f2) s2 HStep).
           iMod "H2".
           repeat iModIntro.
           repeat iMod "H2".
           iModIntro.
           iDestruct "H2" as "[Hσ H]".
           iFrame.
           iApply "IH".
           done.
           iFrame.
           
        -- move/lfilledP in Hlf1.
           inversion Hlf1; subst; clear Hlf1.
           eassert (iris.prim_step (es1, _) σ [] ([AI_trap], _) σ []) as HStep2.
           { unfold iris.prim_step.
             repeat split => //.
             apply r_simple; eapply rs_trap => //.
             move => HContra; subst.
             by destruct n.
           }
           iSpecialize ("H2" $! ([AI_trap], _) _ HStep2).
           iMod "H2".
           repeat iModIntro.
           repeat iMod "H2".
           iDestruct "H2" as "[Hσ H]".
           
           iModIntro.
           replace [AI_trap] with (iris.of_val0 trapV) => //.
           iFrame.
           iApply fupd_ewp.
           { simpl. destruct (iris.to_eff0 (take n es1 ++ AI_trap :: drop m (es1 ++ es2))%SEQ) eqn:Hy => //.
             unfold to_eff0 in Hy.
             rewrite map_app merge_app /= in Hy.
              rewrite merge_trap in Hy.
              rewrite val_not_val_combine_assoc in Hy.
              apply const_list_to_val in H2 as (? & ? & ?).
              unfold to_val0 in H.
              destruct (merge_values _) => //.
              inversion H; subst.
              destruct x => //=.
              simpl in Hy.
              destruct (flatten _) => //.  } 
           repeat rewrite ewp_unfold /ewp_pre /=.
           iMod "H" as "H".
           by iSpecialize ("Hntrap" with "H").
Qed.

Lemma ewp_wand_ctx E e f P Φ Ψ i lh :
  EWP e UNDER f @ E CTX i; lh <| P |> {{ Φ }} -∗ (∀ v f, Φ v f -∗ Ψ v f) -∗ EWP e UNDER f @ E CTX i; lh <| P |> {{ Ψ }}.
Proof.
  iIntros "Hwp H". iIntros (LI HLI).
  iSpecialize ("Hwp" $! LI HLI).
  iApply (ewp_wand with "Hwp"). auto.
Qed.

Lemma ewp_seq_ctx (E : coPset) f Ψ (Φ Φ' : val0 -> frame -> iProp Σ) (es1 es2 : expr0) (i : nat) (lh : lholed) :
  to_eff0 es2 = None ->
  is_pure lh ->
  lh_eff_None lh ->
  (((∀ f, ¬ Φ' trapV f )) ∗
     EWP es1 UNDER f @ E <| Ψ |> {{ w ; h , Φ' w h  }} ∗
  ∀ w f', (Φ' w f' -∗ EWP (iris.of_val0 w ++ es2) UNDER f' @ E CTX i; lh <| Ψ |> {{ v ; h , Φ v h }}))%I
  ⊢ EWP (es1 ++ es2) UNDER f @ E CTX i; lh <| Ψ |> {{ v ; h , Φ v h }}.
Proof.
  iLöb as "IH" forall (E es1 es2 f Φ Φ' Ψ i lh).
  iIntros (Hes2 Hpure Hlh) "[Hntrap [Hes1 Hes2]]".
  specialize (lh_eff_None_spec _ Hlh) as Hlh'. 
  iIntros (LI Hfilled).
  iApply ewp_unfold. rewrite /ewp_pre /=.
  (* Base case, when both es1 and es2 are values *)
  destruct (to_val0 LI) as [vs|] eqn:Hetov;
    last destruct (iris.to_eff0 LI) as [eff|] eqn:Hetof.
   - iDestruct (ewp_unfold with "Hes1") as "Hes1".
     rewrite /ewp_pre /=.
     eapply lfilled_to_val_app in Hfilled as Hv;eauto.
     destruct Hv as [vs' [Hvs' Hfilled']].
     rewrite Hvs'.
     iMod "Hes1" as "Hes1".
     
     iSpecialize ("Hes2" with "Hes1").
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
       * destruct (to_val0 es1) eqn:Habs.
         eapply to_val_to_eff in Habs => //.
         rewrite Hin.
         destruct i0.
         iDestruct "Hes1" as (Ξ) "[HΞ Hnext]".
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
       * destruct (to_val0 es1) eqn:Habs.
         eapply to_val_to_eff in Habs => //.
         rewrite Hin.
         destruct i0.
         iDestruct "Hes1" as (cont t1s t2s tf' ts) "(#Htag & Hk & -> & -> & Hcont & Hes1)".
         iDestruct "Hes1" as (Ξ) "[HΞ Hnext]".
         iFrame. iFrame "#".
         iExists _,_,_. 
         iSplit; first done. iSplit; first done.
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
       * destruct (to_val0 es1) eqn:Habs.
         eapply to_val_to_eff in Habs => //.
         rewrite Hin.
         iFrame.

   - repeat rewrite ewp_unfold. rewrite /ewp_pre /=.
     (* Ind *)
     iIntros (σ) "Hσ".
     destruct (to_val0 es1) as [vs|] eqn:Hes;
       last destruct (iris.to_eff0 es1) as [eff |] eqn:Heff.
     + apply of_to_val0 in Hes as <-.
       iMod "Hes1" as "Hes1".
       iSpecialize ("Hes2" with "Hes1").
       iSpecialize ("Hes2" $! _ Hfilled).
       iDestruct (ewp_unfold with "Hes2") as "Hes2"; rewrite /ewp_pre /=.
       rewrite Hetov Hetof.
       iSpecialize ("Hes2" $! σ with "[$]").
       iMod "Hes2" as "[%H1 H2]".
       iIntros "!>".
       iSplit.
       * iPureIntro. by apply H1. 
       * by iApply "H2".
     + apply to_eff_None_lfilled_inv in Hfilled => //.
       apply to_eff_cat_None_inv in Hfilled.
       rewrite Hfilled in Heff => //. 
     + iSpecialize ("Hes1" $! σ with "[$]").
       iMod "Hes1" as "[%H1 H2]".
       iModIntro.
       iSplit.
       * iPureIntro.
         destruct σ => //.
         apply append_reducible with (es2:=es2) in H1;auto.
         eapply lfilled_reducible. apply Hfilled. auto.
       * iIntros ([e2 f2] σ2 HStep').
         eapply (lfilled_prim_step_split_reduce_r _ _ _ _ _ _ _ _) in HStep' as Heq;[|apply Hfilled|apply H1].
         destruct Heq as [[e' [HStep'' Hlfilled']] | [[lh' Hlf] Hσ]]; last inversion Hσ; subst.
         -- iSpecialize ("H2" $! (e', f2) σ2 HStep'').
            iMod "H2".
            repeat iModIntro.
            repeat iMod "H2".
            iModIntro.
            iDestruct "H2" as "(Hσ & Hes)".
            iFrame.
            iDestruct ("IH" with "[] [] [] [$Hntrap $Hes $Hes2]") as "Hcont"; try done; by iApply "Hcont".
         -- eassert (iris.prim_step (es1, _) _ [] ([AI_trap], _) _ []) as HStep2.
            { unfold iris.prim_step.
              repeat split => //.
              apply r_simple; eapply rs_trap => //.
              move => HContra; subst.
              by simpl in Hes.
            }

            iSpecialize ("H2" $! ([AI_trap], _) _ HStep2).
            iMod "H2".
            repeat iModIntro.
            repeat iMod "H2".
            iDestruct "H2" as "(Hσ & H)".
            iModIntro => /=.
            iFrame.
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
            iMod "H" as "H".
            by iSpecialize ("Hntrap" with "H").
Qed. 



(* Contextual rules for Local computation *)


Lemma ewp_frame_rewrite (E: coPset) f Ψ (Φ: val0 -> frame -> iProp Σ) es n f':
  EWP es UNDER f @ E FRAME n; f' <| Ψ |> {{ v ; h , Φ v h }} ⊣⊢
                        EWP [AI_frame n f' es] UNDER f @ E <| Ψ |> {{ v;h, Φ v h }}.
Proof.
  trivial.
Qed.

Lemma ewp_frame_value (E : coPset) f Ψ (Φ : val0 -> frame -> iProp Σ) es n f' vs :
  to_val0 es = Some (immV vs) ->
  length es = n ->
  ▷ (Φ (immV vs) f) -∗
                     EWP es UNDER f @ E FRAME n; f' <| Ψ |> {{ v;h, Φ v h }}.
Proof.
  iIntros (Hv Hlen) "H".
  rewrite ewp_frame_rewrite.
  apply to_val_const_list in Hv as Hconst.
  iApply (ewp_lift_atomic_step with "[-]"); simpl ; trivial;eauto.
  unfold to_val0 => /=.
  apply const_list_to_val in Hconst as (? & ? & ?).
  unfold to_val0 in H.
  destruct (merge_values $ map _ _) => //.
  by inversion H.
  unfold to_eff0 => /=.
  apply const_list_to_val in Hconst as (? & ? & ?).
  unfold to_val0 in H.
  destruct (merge_values $ map _ _) => //.
  by inversion H.
  iIntros (σ) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold language.reducible, language.prim_step => /=.
    eexists [], (es, _), _, [].
    unfold iris.prim_step => /=.
    repeat split => //. apply r_simple. apply rs_local_const; auto.
  - iIntros "!>" (es2 s2 f2 HStep) "!>".
    destruct HStep as (H & _ & _).
    iris_ewp_ctx.only_one_reduction H. all:simplify_eq;iFrame. rewrite Hv.
    iFrame.
    1,2:rewrite find_first_const// in Hstart.
Qed.


 Lemma ewp_seq_ctx_frame (E : coPset) P (Φ Ψ : val0 -> frame -> iProp Σ) (es1 es2 : expr0) (i : nat) (lh : lholed) (n : nat) (f : frame) (f0 : frame)  :
  to_eff0 es2 = None ->
  is_pure lh ->
  lh_eff_None lh ->
  ((∀ f, ¬ (Ψ trapV f)) ∗ 
   (EWP es1 UNDER f @ E <| P |> {{ w ; h , Ψ w h }}) ∗
   ∀ w f1, Ψ w f1 -∗ EWP (iris.of_val0 w ++ es2) UNDER f0 @ E FRAME n ; f1 CTX i; lh <| P |> {{ v ; h , Φ v h }})%I
  ⊢ EWP (es1 ++ es2) UNDER f0 @ E FRAME n ; f CTX i; lh <| P |> {{ v ; h , Φ v h }}.
Proof.
  iLöb as "IH" forall (E es1 es2 P Φ Ψ i lh n f f0).
{ iIntros (Hes2 Hpure Hlh) "(Htrap & Hes1 & Hes2)".
  iIntros (LI Hfilled).
  specialize (lh_eff_None_spec _ Hlh) as Hlh'.
  
  iApply ewp_unfold.
  (* Base case, when both es1 and es2 are values *)

  destruct (to_val0 [AI_frame n f LI]) as [vs|] eqn:Hetov.
  { unfold ewp_pre.
    rewrite /= Hetov.
    apply to_val_local_inv in Hetov as Heq.
    destruct Heq as [tf [h' [w [vh Heq]]]]. subst vs.
    apply to_val_call_host_rec_local in Hetov as HH.
    destruct HH as [LI2 [HeqLI HLI]].
    rewrite app_nil_l app_nil_r in HeqLI. simplify_eq.

    edestruct lfilled_to_val_app as (vs' & Hes1 & Hfillval).
    exact Hfilled. exact HLI.
    rewrite ewp_unfold /ewp_pre.
    rewrite /= Hes1.
    iMod "Hes1" as "Hvs'".
    iSpecialize ("Hes2" with "[$]").
    iSpecialize ("Hes2" $! LI2 Hfillval).
    rewrite ewp_unfold /ewp_pre.
    rewrite /= Hetov.
    done. } 
    
  destruct (iris.to_eff0 [AI_frame n f LI]) as [eff|] eqn:Hetof.
  { apply to_eff_local_inv in Hetof as Heq.
    destruct Heq as [( vs & i' & she & ->) | [(vs & i' & k & tf & she & ->) | (vs & i' & k & she & -> )]].
    - apply to_eff_sus_local in Hetof as HH.
      destruct HH as [LI2 [HeqLI HLI]].
      inversion HeqLI; subst.
      eapply lfilled_to_eff_app_sus in Hfilled as Hv;eauto.
      destruct Hv as [[Hconst1 Hconst2] | [(esv & shin & shout & -> & Hin & Hout & Htrans) | (shin & shout & Hin & Hout & Htrans)]].
      * apply Hlh' in Hfilled.
        unfold to_eff0 in Hetof, Hfilled.
        simpl in Hetof.
        destruct (merge_values (map _ LI2)) => //.
        destruct v => //. 
        by apply const_list_concat.
      * rewrite Hin in Hes2 => //.  
      * destruct (to_val0 es1) eqn:Habs.
        eapply to_val_to_eff in Habs => //.
        rewrite ewp_unfold /ewp_pre /= Habs Hin Hetov Hetof.
        destruct i'.
        iDestruct "Hes1" as (Ξ) "[HΞ Hnext]".
        iFrame.
        iIntros (w) "Hw".
        iDestruct ("Hnext" with "Hw") as "H".
        iNext.
        subst she.
        iSimpl.
        rewrite susfill_trans.
        eapply susfill_to_lfilled in Hout as Hfill'.
        2: done.
        destruct Hfill' as [k Hfill'].
        iDestruct ("IH" with "[] [] [] [$Htrap $H $Hes2]") as "H".
        done. done. done.
        apply lfilled_depth in Hfilled as Hdepth1.
        apply lfilled_depth in Hfill' as Hdepth2.
        subst i k. 
        iDestruct ("H" $! _ Hfill') as "H".
        unfold sus_trans.
        rewrite sus_push_const_nil.
        rewrite susfill_sus_append.
        iExact "H".
    - apply to_eff_sw_local in Hetof as HH.
      destruct HH as [LI2 [HeqLI HLI]].
      inversion HeqLI; subst.
      eapply lfilled_to_eff_app_sw in Hfilled as Hv;eauto.
      destruct Hv as [[Hconst1 Hconst2] | [(esv & shin & shout & -> & Hin & Hout & Htrans) | (shin & shout & Hin & Hout & Htrans)]].
      * apply Hlh' in Hfilled.
        unfold to_eff0 in Hetof, Hfilled.
        simpl in Hetof.
        destruct (merge_values (map _ LI2)) => //.
        destruct v => //. 
        by apply const_list_concat.
      * rewrite Hin in Hes2 => //.  
      * destruct (to_val0 es1) eqn:Habs.
        eapply to_val_to_eff in Habs => //.
        rewrite ewp_unfold /ewp_pre /= Habs Hin Hetov Hetof.
        destruct tf. 
        iDestruct "Hes1" as (cont t1s t2s tf' ts) "(#Htag & Hk & -> & -> & Hcont & Hes1)".
        iDestruct "Hes1" as (Ξ) "[HΞ Hnext]".
        iFrame. iFrame "#". iExists _,_,_.
        iSplit; first done. iSplit; first done.
        iIntros (w) "Hw".
        iDestruct ("Hnext" with "Hw") as "H".
        iNext.
        subst she.
        iSimpl.
        rewrite swfill_trans.
        eapply swfill_to_lfilled in Hout as Hfill'.
        2: done.
        destruct Hfill' as [k' Hfill'].
        iDestruct ("IH" with "[] [] [] [$Htrap $H $Hes2]") as "H".
        done. done. done.
        apply lfilled_depth in Hfilled as Hdepth1.
        apply lfilled_depth in Hfill' as Hdepth2.
        subst i k'. 
        iDestruct ("H" $! _ Hfill') as "H".
        unfold sus_trans.
        rewrite sw_push_const_nil.
        rewrite swfill_sw_append.
        iExact "H".
    - apply to_eff_thr_local in Hetof as HH.
      destruct HH as [LI2 [HeqLI HLI]].
      inversion HeqLI; subst.
      eapply lfilled_to_eff_app_thr in Hfilled as Hv;eauto.
      destruct Hv as [[Hconst1 Hconst2] | [(esv & shin & shout & -> & Hin & Hout & Htrans) | (shin & shout & Hin & Hout & Htrans)]].
      * apply Hlh' in Hfilled.
        unfold to_eff0 in Hetof, Hfilled.
        simpl in Hetof.
        destruct (merge_values (map _ LI2)) => //.
        destruct v => //. 
        by apply const_list_concat.
      * rewrite Hin in Hes2 => //.  
      * destruct (to_val0 es1) eqn:Habs.
        eapply to_val_to_eff in Habs => //.
        rewrite ewp_unfold /ewp_pre /= Habs Hin Hetov Hetof.
        iFrame. } 

  repeat rewrite ewp_unfold /ewp_pre /=. rewrite Hetov Hetof.
  apply lfilled_to_sfill in Hfilled as Hsfill.
  destruct Hsfill as [sh Hsh].
  rewrite Hsh sfill_to_llfill in Hetov.
  rewrite Hsh sfill_to_llfill in Hetof.

  iIntros (σ) "Hσ".
    
  destruct (to_val0 es1) eqn:Hetov'.
  { iMod "Hes1" as "HPsi".

    iDestruct ("Hes2" with "[$]") as "Hes2".
    erewrite of_to_val0;[|eauto].
    iDestruct ("Hes2" with "[]") as "Hes2".
    { iPureIntro. eauto. }
    iDestruct (ewp_frame_rewrite with "Hes2") as "Hes2".
    iDestruct (ewp_unfold with "Hes2") as "Hes2".
    rewrite /ewp_pre /= Hsh sfill_to_llfill Hetov Hetof.
    iSpecialize ("Hes2" with "[$]").
    iFrame. }

  destruct (iris.to_eff0 es1) eqn:Hetof'.
  { apply to_eff_None_lfilled_inv in Hfilled => //.
    apply to_eff_cat_None_inv in Hfilled.
    rewrite Hfilled in Hetof' => //.
    rewrite Hsh sfill_to_llfill.
    unfold to_eff0.
    unfold to_eff0 in Hetof.
    simpl in Hetof.
    destruct (merge_values (map _ (llfill _ _))) => //.
    destruct e0 => //. } 

  iSpecialize ("Hes1" with "[$]").
  iMod "Hes1" as "[%H1 H2]".
  iModIntro.
  iSplit.
  { iPureIntro.
    apply append_reducible with (es2:=es2) in H1;auto.
    destruct f.
    eapply local_frame_lfilled_reducible. apply Hfilled. auto. }
  iIntros ([e2 f2] s2 HStep').
  destruct f.
  eapply local_frame_lfilled_prim_step_split_reduce_r in HStep' as Heq;[|apply Hfilled|apply H1].
  destruct Heq as [(e' & f'' & LI' & HStep'' & <- & -> & Hfill) | (lh' & Hlh'' & HH)]. 
  - iSpecialize ("H2" $! (e', _) _ HStep'').
    iMod "H2".
    repeat iModIntro.
    repeat iMod "H2".
    iDestruct "H2" as "(Hσ & H)".
    iFrame.
    iModIntro.
    destruct f0.
    iApply ("IH" with "[] [] [] [$Htrap $H $Hes2]"). done. done. done.
    done.

  - (* trap case *)
    simplify_eq.
    eassert (iris.prim_step (es1, _) _ [] ([AI_trap], _) _ []) as HStep2.
    { unfold iris.prim_step.
      repeat split => //.
      apply r_simple; eapply rs_trap => //.
      move => HContra; subst. done.
    }
    destruct HStep' as [HStep' [_ _]].
    simplify_eq.
    iSpecialize ("H2" $! ([AI_trap], _) _ HStep2).
    iMod "H2".
    repeat iModIntro.
    repeat iMod "H2".
    iDestruct "H2" as "(Hσ & H )".
    replace [AI_trap] with (iris.of_val0 trapV); last done.
    iFrame.
    rewrite ewp_unfold /ewp_pre /=.
    iMod "H" as "H".
    by iSpecialize ("Htrap" with "H"). } 
Qed.  





Lemma ewp_frame_seq es1 es2 n f0 (f: frame) E P Ψ Φ :
  (*  (to_val [AI_frame n f (es1 ++ es2)] = None) -> *)
  to_eff0 es2 = None ->
  (∀ f, ¬ Ψ trapV f) -∗ 
  EWP es1 UNDER f @ E <| P |> {{ v ; h , Ψ v h }} -∗
                                                   (∀ w f', Ψ w f' -∗ EWP (iris.of_val0 w ++ es2) UNDER f0 @ E FRAME n; f' <| P |> {{ v ; h , Φ v h }}) -∗
                                                                                         (*                                                                      Φf0 f0 -∗ *)
  (EWP (es1 ++ es2) UNDER f0 @ E FRAME n ; f <| P |> {{ v ; h , Φ v h }}).
Proof.
  iIntros (Hes2) "Htrap Hes1 Hcont".
  iApply ewp_wasm_empty_ctx_frame.
  iApply (ewp_seq_ctx_frame with "[$Htrap $Hes1 Hcont]").
  done. constructor. done.
  iIntros (w f1) "H".
  iApply ewp_wasm_empty_ctx_frame.
  iApply ("Hcont" with "[$]").
Qed.

  
End structural_rules.

