From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export iris_rules_control.

Set Bullet Behavior "Strict Subproofs".
Section bind_rules.
  
Context `{!wasmG Σ}.


Lemma ewp_frame_bind Ψ f0 f es E P Φ n:
  to_val0 es = None ->
  to_eff0 es = None ->
  ((∀ f, ¬ (Ψ trapV f)) ∗
    (EWP es UNDER f @ E <| P |> {{ w ; f , Ψ w f }}) ∗
    ∀ w f1, Ψ w f1 -∗ EWP [AI_frame n f1 (of_val0 w)] UNDER f0 @ E <| P |> {{ v ; f, Φ v f }})%I
    ⊢ EWP [AI_frame n f es] UNDER f0 @ E <| P |> {{ v ; f , Φ v f }} .
Proof.
  iIntros (Htv Htf) "(Htrap & Hes1 & Hes2)".
  iDestruct (ewp_frame_seq es [] with "Htrap Hes1") as "H".
  done.
  repeat rewrite app_nil_r.
  iApply ("H" with "[Hes2]").
  iIntros (??) "?".
  iSpecialize ("Hes2" with "[$]").
  iApply ewp_frame_rewrite.
  rewrite app_nil_r.
  iFrame.
Qed. 



Lemma ewp_bind es E Ψ i lh Φ f:
  is_pure lh ->
  lh_eff_None lh ->
  EWP es UNDER f @ E <| Ψ |> {{ w ; f, ⌜ w <> trapV ⌝ ∗
                                           EWP of_val0 w UNDER f @ E CTX i; lh <| Ψ |> {{ Φ }} }}
    ⊢ EWP es UNDER f @ E CTX i; lh <| Ψ |> {{ Φ }}.
Proof.
   iLöb as "IH" forall (lh es Ψ f).
 { iIntros (Hpure Hlh) "H".
   specialize (lh_eff_None_spec _ Hlh) as Hlh'.
   iIntros (LI HLI).
   rewrite !(ewp_unfold E) /ewp_pre.
   destruct (to_val0 LI) as [ v          |] eqn:He;
     [|destruct (to_eff0 LI) as [eff|] eqn:He'].
   - apply lfilled_to_val in HLI as HLI'.
     2: by eexists.
     destruct HLI' as [ves Htv].
     rewrite /= Htv He.
     iMod "H".
     rewrite (@of_to_val0 _ _ Htv).
     iDestruct "H" as "(%Hntrap & H)".
     iSpecialize ("H" $! _ HLI).
     rewrite !ewp_unfold /ewp_pre.
     rewrite /= He. done.
   - destruct eff.
     + eapply lfilled_to_eff_sus in HLI as HLI' => //.
       destruct HLI' as [Hconst | (shin & shout & Hin & Hout & Htrans)].
       * erewrite Hlh' in He' => //.
       * destruct (to_val0 es) eqn:Htv.
         by exfalso; eapply to_val_to_eff.
         Opaque upcl.
         rewrite /= Hin He He' Htv.
         iApply (monotonic_prot with "[] H").
         iIntros (w) "H !>".
         subst sh.
         rewrite susfill_trans.
         eapply susfill_to_lfilled in Hout as Hfilled.
         2:{ instantiate (2 := susfill i0 shin (v_to_e_list w)).
             instantiate (2 := i0).
             done. } 
         destruct Hfilled as [k Hfilled].
         apply lfilled_depth in HLI as Hdepth1.
         apply lfilled_depth in Hfilled as Hdepth2.
         rewrite Hdepth1 in Hdepth2; subst i k.

         iSpecialize ("IH" $! lh (susfill i0 shin (v_to_e_list w)) Ψ _ Hpure Hlh).
         iDestruct ("IH" with "H") as "H".

         iSpecialize ("H" $! _ Hfilled).
         iExact "H".
     + eapply lfilled_to_eff_sw in HLI as HLI' => //.
       destruct HLI' as [Hconst | (shin & shout & Hin & Hout & Htrans)].
       * erewrite Hlh' in He' => //.
       * destruct (to_val0 es) eqn:Htv.
         by exfalso; eapply to_val_to_eff.
         rewrite /= Hin He He' Htv.
         destruct i0. 
         iDestruct "H" as (cont t1s t2s tf' ts q) "(? & Htag & Hk & -> & -> & Hcont & H)".
         iFrame. iFrame "#".
         iExists _,_,_.
         iSplit; first done. iSplit; first done.
         iIntros "Htag".
         iPoseProof ("H" with "Htag") as "H".
         iApply (monotonic_prot with "[] H").
         iIntros (w) "H !>".
         subst sh.
         rewrite swfill_trans.
         eapply swfill_to_lfilled in Hout as Hfilled.
         2:{ instantiate (2 := swfill (Mk_tagidx n) shin (v_to_e_list w)).
             instantiate (2 := Mk_tagidx n).
             done. } 
         destruct Hfilled as [k' Hfilled].
         apply lfilled_depth in HLI as Hdepth1.
         apply lfilled_depth in Hfilled as Hdepth2.
         rewrite Hdepth1 in Hdepth2; subst i k'.

         iSpecialize ("IH" $! lh (swfill (Mk_tagidx n) shin (v_to_e_list w)) Ψ _ Hpure Hlh).
         iDestruct ("IH" with "H") as "H".

         iSpecialize ("H" $! _ Hfilled).
         iExact "H".
     + eapply lfilled_to_eff_thr in HLI as HLI' => //.
       destruct HLI' as [Hconst | (shin & shout & Hin & Hout & Htrans)].
       * erewrite Hlh' in He' => //.
       * destruct (to_val0 es) eqn:Htv.
         by exfalso; eapply to_val_to_eff.
         rewrite /= Hin He He' Htv.
         done.
   - repeat rewrite ewp_unfold. rewrite /ewp_pre /= He He'.
     (* Ind *)
     iIntros (σ) "Hσ".
     destruct (to_val0 es) as [vs|] eqn:Hes;
       last destruct (iris.to_eff0 es) as [eff |] eqn:Heff.
     + apply of_to_val0 in Hes as <-.
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
       * iIntros ([e2 f2] σ2 HStep').
         eapply lfilled_reduce in HStep' as Heq.
         2: exact HLI.
         2: done.
         destruct Heq as [(es' & Hstep & Hfill) | (lhtrap & Htrap & -> & ->)].
         -- iSpecialize ("H2" $! (es', f2) σ2 Hstep).
            iMod "H2".
            repeat iModIntro.
            repeat iMod "H2".
            iModIntro.
            iDestruct "H2" as "(Hσ & Hes)".
            iFrame.
            iDestruct ("IH" with "[] [] Hes") as "Hcont". done. done.
            by iApply "Hcont".
         -- eassert (iris.prim_step (es,_) _ [] ([AI_trap], _) _ []) as HStep2.
            { unfold iris.prim_step.
              repeat split => //.
              apply r_simple; eapply rs_trap => //.
              move => HContra; subst.
              by simpl in Hes.
            }
            iSpecialize ("H2" $! ([AI_trap],_) _ HStep2).
            iMod "H2".
            repeat iModIntro.
            repeat iMod "H2".
            iDestruct "H2" as "(Hσ & H)".
            iModIntro => /=.
            iFrame.
            iDestruct (ewp_unfold with "H") as "H";rewrite /ewp_pre /=.
            edestruct lfilled_trans as [lh' Hlh''].
            exact Htrap. exact HLI.
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



  Lemma ewp_label_bind (E : coPset) Ψ (Φ : iris.val0 -> frame -> iProp Σ) e n es l1 l2 f :
    EWP e UNDER f @ E <| Ψ |> {{ w ; f', EWP of_val0 w UNDER f' @ E CTX 1; LH_rec l1 n es (LH_base [] []) l2 <| Ψ |> {{ w ; f , Φ w f }} }} -∗
    EWP e UNDER f @ E CTX 1; LH_rec l1 n es (LH_base [] []) l2 <| Ψ |> {{ w ; f , Φ w f }}.
  Proof.
    iIntros "H". iIntros (LI HLI).
    iLöb as "IH" forall (E e LI HLI f).
    repeat rewrite ewp_unfold /ewp_pre /=.
    destruct (iris.to_val0 (LI)) as [vs|] eqn:Hetov;
      last destruct (to_eff0 LI) as [eff|] eqn:Hetof.
    - assert (is_Some (iris.to_val0 LI)) as Hsome;[eauto|].
      eapply lfilled_to_val in Hsome as [v Hv];[|eauto].
      rewrite Hv. erewrite of_to_val0;eauto.
      iMod "H" as "H".
      iDestruct ("H" $! _ HLI) as "H".
      iDestruct (ewp_unfold with "H") as "H".
      rewrite /ewp_pre /= Hetov. done.
    - move/lfilledP in HLI; inversion HLI; subst.
      inversion H8; subst.
      rewrite cats0 /= in Hetof.
      unfold to_eff0 in Hetof.
      rewrite map_app merge_app in Hetof.
      apply const_list_to_val in H7 as (vs1 & Htv1 & Hvs1).
      unfold to_val0 in Htv1.
      destruct (merge_values (map _ l1)) => //.
      inversion Htv1; subst.
      simpl in Hetof.
      unfold to_val0, to_eff0.
      destruct (merge_values (map _ e)) => //.
      + destruct v => //.
        all: try rewrite merge_notval in Hetof => //.
        destruct i => //.
        2: destruct (vh_decrease _) => //.
        all: try rewrite merge_notval in Hetof => //.
        rewrite merge_br in Hetof => //.
        rewrite merge_return in Hetof => //.
        rewrite merge_call_host in Hetof => //.
      + destruct e0 => //.
        * rewrite merge_suspend in Hetof.
          inversion Hetof; subst.
          iDestruct "H" as (Ξ) "[HΞ H]".
          iFrame. iIntros (w) "Hw".
          iDestruct ("H" with "Hw") as "H".
          iNext.
          iApply "IH"; last first.
          iExact "H".
          iPureIntro.
          unfold lfilled, lfill => //=.
          rewrite v_to_e_is_const_list.
          rewrite cats0. rewrite app_nil_r.
          rewrite flatten_simplify. done.
        * rewrite merge_switch in Hetof.
          inversion Hetof; subst.
          destruct i. 
          iDestruct "H" as (cont t1s t2s tf' ts q) "(? & Htag & Hk & -> & -> & Hcont & H)".
          iFrame. iExists _,_,_. 
          iSplit; first done.
          iSplit; first done.
          iIntros "Htag".
          iDestruct ("H" with "Htag") as (Ξ) "[HΞ H]".
          iFrame.
          iIntros (w) "Hw".
          iDestruct ("H" with "Hw") as "H".
          iNext.
          iApply "IH"; last first.
          iExact "H".
          iPureIntro.
          unfold lfilled, lfill => //=.
          rewrite v_to_e_is_const_list.
          rewrite cats0. rewrite app_nil_r.
          rewrite flatten_simplify. done.
        * rewrite merge_throw in Hetof.
          inversion Hetof; subst.
          iFrame. 
      + rewrite merge_notval in Hetof => //. 
          
    - destruct (iris.to_val0 e) eqn:Hetov'.
      { erewrite of_to_val0;[|eauto].
        iIntros (σ) "Hσ".
        iMod "H" as "H".
        iDestruct ("H" $! _ HLI) as "H".
        
        iDestruct (ewp_unfold with "H") as "H".
        rewrite /ewp_pre /= Hetov Hetof.
        iDestruct ("H" with "Hσ") as "H".
        iFrame. }
      destruct (to_eff0 e) eqn:Hetof'.
      { move/lfilledP in HLI.
        inversion HLI; subst. inversion H8; subst.
        unfold to_eff0 in Hetof, Hetof'.
        rewrite cats0 map_app merge_app /= in Hetof.
        apply const_list_to_val in H7 as (vs1 & Htv1 & Hvs1).
        unfold to_val0 in Htv1.
        destruct (merge_values (map _ l1)) => //.
        inversion Htv1; subst.
        destruct (merge_values (map _ e)) => //.
        inversion Hetof'; subst.
        destruct e0 => //.
        rewrite merge_suspend in Hetof => //.
        rewrite merge_switch in Hetof => //.
        rewrite merge_throw in Hetof => //.
      }

      iIntros (σ) "Hσ".
        iDestruct ("H" with "Hσ") as "H".
        iMod "H" as "[%Hred H]". iModIntro.
        iSplit.
        { iPureIntro.
          eapply lfilled_reducible;eauto. }
        apply lfilled_Ind_Equivalent in HLI.
        inversion HLI;simplify_eq. inversion H8;simplify_eq.
        repeat erewrite app_nil_l, app_nil_r.
        iIntros ([e2 f2] σ2 Hprim).
        destruct Hprim as [Hprim _].
        eapply reduce_det_label in Hprim as Hprim';[|auto..].
        destruct Hprim' as [es2' [-> Hstep]].
        iDestruct ("H" with "[]") as "H".
        { iPureIntro. instantiate (2 := (_,_)). split;eauto. }
        iMod "H". iModIntro. iNext.
        repeat iMod "H". iApply fupd_mask_intro_subseteq;[solve_ndisj|].
        iDestruct "H" as "(Hσ & H)".
        
        iFrame. 
        iDestruct ("IH" with "[] H") as "H".
        { iPureIntro. apply lfilled_Ind_Equivalent. constructor;auto. constructor;auto. }
        repeat erewrite app_nil_l, app_nil_r.
        iFrame.
  Qed.



    
End bind_rules.
