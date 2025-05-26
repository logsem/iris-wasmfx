From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export iris_rules_control.

Set Bullet Behavior "Strict Subproofs".
Section bind_rules.
  
Context `{!wasmG Σ}.


Lemma ewp_frame_bind Ψ f0 f1 f es E P Φ n:
  to_val es = None ->
  to_eff es = None ->
  (¬ (Ψ trapV) ∗
  ↪[frame] f0 ∗
    (↪[frame] f -∗ EWP es @ E <| P |> {{ w, Ψ w ∗ ↪[frame] f1 }}) ∗
    ∀ w, Ψ w ∗ ↪[frame] f0 -∗ EWP [AI_local n f (of_val w)] @ E <| P |> {{ v, Φ v }})%I
    ⊢ EWP [AI_local n f es] @ E <| P |> {{ v, Φ v }} .
Proof.
Admitted. (*
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

(*
  Lemma wp_frame_bind (s : stuckness) (E : coPset) (Φ : iris.val -> iProp Σ) n f f0 LI :
    iris.to_val [AI_local n f LI] = None ->
    ↪[frame] f0 -∗
     (↪[frame] f -∗ WP LI @ s; E {{ w, ∃ f', (↪[frame] f0 -∗ WP of_val w @ s; E FRAME n; f' {{ w, Φ w }}) ∗ ↪[frame] f' }})-∗
     WP LI @ s; E FRAME n; f {{ w, Φ w }}.
  Proof.
    iIntros (Hetov') "Hframe H".
    rewrite wp_frame_rewrite.
    iLöb as "IH" forall (s E LI f f0 Hetov').
    destruct (iris.to_val (LI)) as [vs|] eqn:Hetov.
    { iApply wp_unfold.
      unfold wp_pre. simpl language.to_val. rewrite Hetov'; simpl.
      iIntros (σ ns κ κs nt) "Hσ".
      destruct σ as [[ ? ?] ?].
      iDestruct "Hσ" as "(H1&H2&H3&H4&Hff&H5&H6)".
      iDestruct (ghost_map_lookup with "Hff Hframe") as %Hlook.
      iMod (ghost_map_update f with "Hff Hframe") as "[Hff Hframe]".
      iDestruct ("H" with "Hframe") as "H".
      iDestruct (wp_unfold with "H") as "H".
      rewrite /wp_pre /= Hetov.
      iMod ("H") as "Hf".
      iDestruct "Hf" as (f') "[H Hf]".
      rewrite wp_frame_rewrite.
      iDestruct (ghost_map_lookup with "Hff Hf") as %Hlook'.
      iMod (ghost_map_update f0 with "Hff Hf") as "[Hff Hf]".
      rewrite !insert_insert. rewrite lookup_insert in Hlook'. inversion Hlook'.
      iDestruct ("H" with "Hf") as "H".
      iDestruct (wp_unfold with "H") as "H".
      rewrite /wp_pre /=.
      apply of_to_val in Hetov as Heq. rewrite Heq.
      subst f. rewrite Hetov'.
      rewrite lookup_insert in Hlook;inversion Hlook.
      iSpecialize ("H" $! (_,_,_) 0 κ [] 0 with "[$H1 $H2 $H3 $H4 $H5 $H6 $Hff]").
      iMod "H" as "[? H]". iModIntro. iFrame. }
    { iApply wp_unfold. unfold wp_pre. simpl. rewrite Hetov'.
      iIntros (σ ns κ κs nt) "Hσ".
      destruct σ as [[ ? ?] ?].
      iDestruct "Hσ" as "(H1&H2&H3&H4&Hff&H5&H6)".
      iDestruct (ghost_map_lookup with "Hff Hframe") as %Hlook.
      rewrite lookup_insert in Hlook;inversion Hlook.
      
      iMod (ghost_map_update f with "Hff Hframe") as "[Hff Hframe]".
      rewrite insert_insert.
      iDestruct ("H" with "Hframe") as "H". destruct f.
      iDestruct (wp_unfold with "H") as "H". rewrite /wp_pre /= Hetov.
      iSpecialize ("H" $! (_,_,_) 0 κ [] 0). 
      iDestruct ("H" with "[$H1 $H2 $H3 $H4 $H5 $H6 $Hff]") as "H".

      iMod "H" as "[%Hred H]".
      iModIntro. iSplit.
      { iPureIntro. destruct s =>//.
        destruct Hred as [x [e' [σ' [efs Hstep]]]].
        destruct σ' as [[ ? ?] ?].
        eexists x,[AI_local n {| f_locs := l0; f_inst := i0 |} e'],(_,l,i),efs.
        simpl. destruct Hstep as [Hstep [-> ->]]. split;auto.
        apply r_local. eauto. }

      iIntros (e2 σ2 efs Hstep).
      destruct σ2 as [[ ? ?] ?].
      destruct Hstep as [Hstep [-> ->]].
      apply reduce_det_local in Hstep as Hstep';[|auto].
      destruct Hstep' as [es2' [f1 [Heq1 [Heq2 Hstep']]]].
      simplify_eq. destruct f1.
      iSpecialize ("H" $! _ (_,_,_) _ with "[]").
      { iPureIntro. split;eauto. }

      repeat iMod "H". iModIntro. iNext.
      repeat iMod "H". simpl.
      iDestruct "H" as "[H Hf]".
      iDestruct "Hf" as (f1) "[Hf Hcont]".
      iDestruct "H" as "(H1&H2&H3&H4&Hff&H5&H6)".
      iDestruct (ghost_map_lookup with "Hff Hf") as %Hlook'.
      rewrite lookup_insert in Hlook'. inversion Hlook'.
      iDestruct "Hcont" as "[Hcont _]".
      subst f1.

      destruct (iris.to_val [AI_local n {| f_locs := f_locs0; f_inst := f_inst0 |} es2']) eqn:Hsome.
      { apply to_val_local_inv in Hsome as Hsome'.
        destruct Hsome' as [tf [h [w [vh Heq]]]]. subst v.
        apply to_val_call_host_rec_local in Hsome as Heq.
        destruct Heq as [LI' [Heq HLI]].
        erewrite app_nil_l, app_nil_r in Heq. inversion Heq;subst.
        iDestruct ("Hcont" with "Hf") as "Hcont".
        iDestruct (wp_unfold with "Hcont") as "Hcont".
        rewrite /wp_pre /= HLI.
        iMod "Hcont" as "Hf".
        iDestruct "Hf" as (f) "[Hcont Hf]".
(*        iFrame. *)
        iDestruct (ghost_map_lookup with "Hff Hf") as %Hlook2.
        rewrite lookup_insert in Hlook2. inversion Hlook2. simplify_eq.
        iMod (ghost_map_update {| f_locs := l0; f_inst := i0 |} with "Hff Hf") as "[Hff Hframe]".
        rewrite insert_insert. iFrame.

        iApply fupd_mask_intro_subseteq;[solve_ndisj|].
        (* iExists _. iFrame. *)  iSplit =>//. iIntros "Hf". iApply wp_fupd.
        iApply wp_value;[unfold IntoVal;eapply of_to_val;eauto|].
        iDestruct ("Hcont" with "Hf") as "Hcont".
        iDestruct (wp_unfold with "Hcont") as "Hcont".
        eassert (iris.to_val [AI_local n {| f_locs := f_locs0; f_inst := f_inst0 |}
                                       (iris.of_val (callHostV tf h w vh))]
                = Some (callHostV tf h w (LL_local [] n {| f_locs := f_locs0; f_inst := f_inst0 |} vh []))) as Hetov2.
        { erewrite of_to_val;[|eauto].
          apply to_val_local_add_frame. auto. }
        rewrite /wp_pre /= Hetov2. iFrame. }
      
      iMod (ghost_map_update {| f_locs := l0; f_inst := i0 |} with "Hff Hf") as "[Hff Hframe]".
      rewrite insert_insert.
      simpl. iApply fupd_mask_intro_subseteq;[solve_ndisj|]. iFrame.
      (* iExists _. iFrame. *) iSplit =>//. iIntros "Hf".
      iApply ("IH" with "[] Hf Hcont");[auto|..].
    }
  Qed. *)


Lemma ewp_bind es E Ψ i lh Φ:
  is_pure lh ->
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
         iFrame. iIntros (?) "Hf".
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
         iIntros (?) "Hf".
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



  Lemma ewp_label_bind (E : coPset) Ψ (Φ : iris.val -> iProp Σ) e n es l1 l2 :
    EWP e @ E <| Ψ |> {{ w, EWP of_val w @ E CTX 1; LH_rec l1 n es (LH_base [] []) l2 <| Ψ |> {{ w, Φ w }} }} -∗
    EWP e @ E CTX 1; LH_rec l1 n es (LH_base [] []) l2 <| Ψ |> {{ w, Φ w }}.
  Proof.
    iIntros "H". iIntros (LI HLI).
    iLöb as "IH" forall (E e LI HLI).
    repeat rewrite ewp_unfold /ewp_pre /=.
    destruct (iris.to_val (LI)) as [vs|] eqn:Hetov;
      last destruct (to_eff LI) as [eff|] eqn:Hetof.
    - assert (is_Some (iris.to_val LI)) as Hsome;[eauto|].
      eapply lfilled_to_val in Hsome as [v Hv];[|eauto].
      rewrite Hv. erewrite of_to_val;eauto.
      iMod "H". iDestruct ("H" $! _ HLI) as "H".
      iDestruct (ewp_unfold with "H") as "H".
      rewrite /ewp_pre /= Hetov. done.
    - move/lfilledP in HLI; inversion HLI; subst.
      inversion H8; subst.
      rewrite cats0 /= in Hetof.
      unfold to_eff in Hetof.
      rewrite map_app merge_app in Hetof.
      apply const_list_to_val in H7 as (vs1 & Htv1 & Hvs1).
      unfold to_val in Htv1.
      destruct (merge_values (map _ l1)) => //.
      inversion Htv1; subst.
      simpl in Hetof.
      unfold to_val, to_eff.
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
          iDestruct "H" as (f) "[Hf H]".
          iFrame. iIntros (?) "Hf".
          iDestruct ("H" with "Hf") as (Ξ) "[HΞ H]".
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
          iDestruct "H" as (f) "[Hf H]".
          iFrame. iIntros (?) "Hf".
          iDestruct ("H" with "Hf") as (Ξ) "[HΞ H]".
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
        * rewrite merge_throw in Hetof.
          inversion Hetof; subst.
          iDestruct "H" as (f) "[Hf H]".
          iFrame. 
      + rewrite merge_notval in Hetof => //. 
          
    - destruct (iris.to_val e) eqn:Hetov'.
      { erewrite of_to_val;[|eauto].
        iDestruct ("H" $! _ HLI) as "H".
        iIntros (σ ns κ κs nt) "Hσ".
        destruct σ as [[ ? ?] ?].
        iMod "H".
        iDestruct (ewp_unfold with "H") as "H".
        rewrite /ewp_pre /= Hetov Hetof.
        iDestruct ("H" $! (_,_,_) 0 _ [] 0 with "Hσ") as "H".
        iFrame. }
      destruct (to_eff e) eqn:Hetof'.
      { move/lfilledP in HLI.
        inversion HLI; subst. inversion H8; subst.
        unfold to_eff in Hetof, Hetof'.
        rewrite cats0 map_app merge_app /= in Hetof.
        apply const_list_to_val in H7 as (vs1 & Htv1 & Hvs1).
        unfold to_val in Htv1.
        destruct (merge_values (map _ l1)) => //.
        inversion Htv1; subst.
        destruct (merge_values (map _ e)) => //.
        inversion Hetof'; subst.
        destruct e0 => //.
        rewrite merge_suspend in Hetof => //.
        rewrite merge_switch in Hetof => //.
        rewrite merge_throw in Hetof => //.
      }

      iIntros (σ ns κ κs nt) "Hσ".
        destruct σ as [[ ? ?] ?].
        iDestruct ("H" $! (_,_,_) 0 [] [] 0 with "Hσ") as "H".
        iMod "H" as "[%Hred H]". iModIntro.
        iSplit.
        { iPureIntro.
          destruct s => //.
          eapply lfilled_reducible;eauto. }
        apply lfilled_Ind_Equivalent in HLI.
        inversion HLI;simplify_eq. inversion H8;simplify_eq.
        repeat erewrite app_nil_l, app_nil_r.
        iIntros (e2 σ2 Hprim).
        destruct σ2 as [[ ? ?] ?].
        destruct Hprim as [Hprim [-> _]].
        eapply reduce_det_label in Hprim as Hprim';[|auto..]. destruct Hprim' as [es2' [-> Hstep]].
        iDestruct ("H" $! _ (_,_,_) with "[]") as "H".
        { iPureIntro. split;eauto. }
        iMod "H". iModIntro. iNext.
        repeat iMod "H". iApply fupd_mask_intro_subseteq;[solve_ndisj|].
        iDestruct "H" as "(Hσ & %f & Hf & H)".
        
        iFrame. 
        iIntros "Hf".
        iDestruct ("H" with "Hf") as "H".
        iDestruct ("IH" with "[] H") as "H".
        { iPureIntro. apply lfilled_Ind_Equivalent. constructor;auto. constructor;auto. }
        repeat erewrite app_nil_l, app_nil_r.
        iFrame.
  Qed.


  Lemma ewp_label_bind_inv (E : coPset) Ψ (Φ : iris.val -> iProp Σ) e n es l1 l2 :
    const_list l1 ->
    EWP e @ E CTX 1; LH_rec l1 n es (LH_base [] []) l2 <| Ψ |> {{ w, Φ w }} -∗
    EWP e @ E <| Ψ |> {{ w, EWP of_val w @ E CTX 1; LH_rec l1 n es (LH_base [] []) l2 <| Ψ |> {{ w, Φ w }} }}.
  Proof.
    iIntros (Hconst) "H".
    iLöb as "IH" forall (E e).
    eassert (lfilled 1 (LH_rec l1 n es (LH_base [] []) l2) e _) as Hfill.
    { apply lfilled_Ind_Equivalent. constructor;eauto. constructor;eauto. }
    repeat rewrite ewp_unfold /ewp_pre /=.
    destruct (iris.to_val e) eqn:Hetov.
    { iDestruct ("H" with "[]") as "H".
      { iPureIntro. eauto. }
      iModIntro.
      iIntros (LI HLI%lfilled_Ind_Equivalent).
      inversion HLI;simplify_eq.
      inversion H8;simplify_eq.
      repeat erewrite app_nil_l, app_nil_r.
      erewrite of_to_val;eauto. }
    destruct (to_eff e) eqn:Hetof.
    { iDestruct ("H" with "[]") as "H".
      { iPureIntro. done. }
      destruct e0.
      - apply of_to_eff in Hetof as <-.
        apply const_list_to_val in Hconst as (vs1 & Htv & Hvs).
        iDestruct (ewp_effect_sus with "H") as "H".
        unfold to_eff.
        rewrite map_app.
        rewrite merge_app.

        unfold to_val in Htv.
        destruct (merge_values (map _ l1)) => //.
        inversion Htv; subst v. simpl.
        rewrite cats0.
        specialize (to_of_eff (susE vs i sh)) as Hsus.
        unfold to_eff, of_eff in Hsus.
        destruct (merge_values (map _ (susfill _ _ _))) => //.
        inversion Hsus; subst => //.
        rewrite merge_suspend //.

        iDestruct "H" as (f) "[Hf H]".
        iFrame.
        iIntros (?) "Hf".
        iDestruct ("H" with "Hf") as (Ξ) "[HΞ H]".
        iFrame.
        iIntros (w) "Hw".
        iDestruct ("H" with "Hw") as "H".
        iNext.
        iApply "IH".
        iIntros (LI HLI).
        move/lfilledP in HLI; inversion HLI; subst.
        simpl.
        rewrite cats0.
        rewrite flatten_simplify.
        inversion H8; subst.
        rewrite cats0. done.
      - apply of_to_eff in Hetof as <-.
        apply const_list_to_val in Hconst as (vs1 & Htv & Hvs).
        iDestruct (ewp_effect_sw with "H") as "H".
        unfold to_eff.
        rewrite map_app.
        rewrite merge_app.

        unfold to_val in Htv.
        destruct (merge_values (map _ l1)) => //.
        inversion Htv; subst v. simpl.
        rewrite cats0.
        specialize (to_of_eff (swE vs k tf i sh)) as Hsus.
        unfold to_eff, of_eff in Hsus.
        destruct (merge_values (map _ (swfill _ _ _))) => //.
        inversion Hsus; subst => //.
        rewrite merge_switch //.

        iDestruct "H" as (f) "[Hf H]".
        iFrame.
        iIntros (?) "Hf".
        iDestruct ("H" with "Hf") as (Ξ) "[HΞ H]".
        iFrame.
        iIntros (w) "Hw".
        iDestruct ("H" with "Hw") as "H".
        iNext.
        iApply "IH".
        iIntros (LI HLI).
        move/lfilledP in HLI; inversion HLI; subst.
        simpl.
        rewrite cats0.
        rewrite flatten_simplify.
        inversion H8; subst.
        rewrite cats0. done.
      - apply of_to_eff in Hetof as <-.
        apply const_list_to_val in Hconst as (vs1 & Htv & Hvs).
        iDestruct (ewp_effect_thr with "H") as "H".
        unfold to_eff.
        rewrite map_app.
        rewrite merge_app.

        unfold to_val in Htv.
        destruct (merge_values (map _ l1)) => //.
        inversion Htv; subst v. simpl.
        rewrite cats0.
        specialize (to_of_eff (thrE vs a i sh)) as Hsus.
        unfold to_eff, of_eff in Hsus.
        destruct (merge_values (map _ (exnfill _ _ _))) => //.
        inversion Hsus; subst => //.
        rewrite merge_throw //.
        
        iFrame.
        
    } 

    iDestruct ("H" with "[]") as "H".
    { iPureIntro. eauto. }
    repeat erewrite app_nil_l, app_nil_r.
    erewrite app_nil_l, app_nil_r in Hfill.
    assert (iris.to_val (l1 ++ [AI_label n es e] ++ l2) = None).
    { eapply to_val_None_lfilled with (k:=1);eauto. }
    assert (to_eff (l1 ++ [AI_label n es e] ++ l2) = None).
    { eapply to_eff_None_lfilled => //.
      intros He. apply const_list_to_val in He as (? & ? & ?).
      rewrite H0 in Hetov => //. } 
    iDestruct (ewp_unfold with "H") as "H".
    rewrite /ewp_pre/= H H0.
    iIntros (σ ns κ κs nt) "Hσ".
    destruct σ as [[ ? ?] ?].
    iDestruct ("H" $! (_,_,_) 0 [] [] 0 with "Hσ") as "H".
    iMod "H" as "[%Hred H]". iModIntro.
    erewrite (separate1 (AI_label _ _ _)) in Hred.
    iSplit.
    { iPureIntro. 
      destruct Hred as (?&?&?&?&?).
      destruct x1 as [[ ??]?].
      destruct H1 as [Hred [-> _]].
      eapply reduce_det_label in Hred as Hred';eauto.
      destruct Hred' as [es2 [Heq Hred']].
      eexists _,_,(_,_,_),_. split;eauto. }
    iIntros (e2 σ2 Hprim).
    destruct σ2 as [[ ??]?].
    destruct Hprim as [Hprim [-> _]].
    iDestruct ("H" $! _ (_,_,_) with "[]") as "H".
    { iPureIntro. split;eauto.
      eapply r_label;eauto.
      apply lfilled_Ind_Equivalent.
      constructor;auto. apply lfilled_Ind_Equivalent.
      cbn. apply/eqP. done. }
    iMod "H". iModIntro. iNext.
    repeat iMod "H". iApply fupd_mask_intro_subseteq;[solve_ndisj|].
    iDestruct "H" as "[Hσ H]". iFrame.
    iDestruct "H" as (a) "[Hf H]".
    iFrame. 
    iIntros "Hf". iDestruct ("H" with "Hf") as "H".
    rewrite app_nil_r.
    iApply "IH".
    iIntros (LI HLI%lfilled_Ind_Equivalent).
    inversion HLI;simplify_eq.
    inversion H10;simplify_eq.
    erewrite app_nil_l, app_nil_r. done.      
  Qed.

  Lemma ewp_label_bind_next (E : coPset) Ψ (Φ : iris.val -> iProp Σ) e n es l1 l2 i lh :
    is_pure lh ->
  (*  lh_eff_None lh -> *)
    base_is_empty lh ->
    EWP e @ E <| Ψ |> {{ w, EWP of_val w @ E CTX (S i); LH_rec l1 n es lh l2 <| Ψ |> {{ w, Φ w }} }} -∗
      EWP e @ E CTX (S i); LH_rec l1 n es lh l2 <| Ψ |> {{ w, Φ w }}.
Proof.
  intros Hpure (* Hlh *) Hbase.
  generalize dependent e. generalize dependent i. generalize dependent Φ.
  generalize dependent l1. generalize dependent l2. generalize dependent n.
  generalize dependent es.
  induction Hpure.
  all: iIntros (esc nn l2 l1 Φ i e) "He".
(*    iInduction (lh) as [|l1' m es' lh l2'] "IH" forall (i Φ e l1 l2 n es). *)
  - inversion Hbase;subst.
    destruct i;[|iIntros (LI HLI%lfilled_Ind_Equivalent);inversion HLI;inversion H8].
    iApply ewp_label_bind => //.
  - iIntros (LI HLI).
    apply lfilled_flatten in HLI as HLI'.
    destruct HLI' as [LI' [Hfill1 Hfill2]].
    iApply (ewp_label_bind with "[He]").
    2:{ iPureIntro. exact Hfill2. } 
    apply lfilled_Ind_Equivalent in Hfill2.
    inversion Hfill2;simplify_eq.
    inversion H8;simplify_eq.
    apply lfilled_Ind_Equivalent in Hfill1.
    inversion Hfill1;simplify_eq.
    iApply (IHHpure with "[He]"); cycle 2.
    + iPureIntro. apply lfilled_Ind_Equivalent.
      constructor;eauto.
    + done.
    + iApply (ewp_wand with "He").
      iIntros (v) "He".
      iIntros (LI0 HLI0%lfilled_Ind_Equivalent).
      inversion HLI0;simplify_eq.
      iDestruct ("He" with "[]") as "He".
      { iPureIntro. apply lfilled_Ind_Equivalent. constructor;eauto. }
      iApply ewp_label_bind_inv;auto.
      iIntros (LI' HLI'%lfilled_Ind_Equivalent).
      inversion HLI';simplify_eq.
      inversion H15;simplify_eq.
      erewrite app_nil_l,app_nil_r. eauto. 
  Qed.
  
Lemma ewp_ctx_bind (E : coPset) Ψ (Φ : iris.val -> iProp Σ) e i lh :
  is_pure lh ->
    base_is_empty lh ->
    EWP e @ E <| Ψ |> {{ w, EWP of_val w @ E CTX i; lh <| Ψ |> {{ w, Φ w }} }} -∗
    EWP e @ E CTX i; lh <| Ψ |> {{ w, Φ w }}.
  Proof.
    iIntros (Hpure Hbase) "He".
    iInduction (Hpure) as [] "IH" forall (i Φ).
    - iIntros (LI Hfill%lfilled_Ind_Equivalent).
      inversion Hfill;simplify_eq.
      inversion Hbase;simplify_eq.
      erewrite app_nil_r, app_nil_l.
      iApply ewp_fupd.
      iApply (ewp_wand with "He").
      iIntros (v) "Hv".
      iSpecialize ("Hv" $! (of_val v) with "[]");[iPureIntro;cbn;apply/eqP;by rewrite app_nil_r|].
      iDestruct (ewp_unfold with "Hv") as "Hv".
      rewrite /ewp_pre/=. rewrite to_of_val. done. 
    - simpl in Hbase.
      iSpecialize ("IH" $! Hbase).
      destruct i.
      { iIntros (LI HLI%lfilled_Ind_Equivalent);inversion HLI;inversion H8. }
      iApply ewp_label_bind_next;eauto. 
  Qed.


    
End bind_rules.
