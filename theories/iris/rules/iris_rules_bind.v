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
    ∀ w f1, Ψ w f1 -∗ EWP [AI_local n f1 (of_val0 w)] UNDER f0 @ E <| P |> {{ v ; f, Φ v f }})%I
    ⊢ EWP [AI_local n f es] UNDER f0 @ E <| P |> {{ v ; f , Φ v f }} .
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
   (* rewrite !(ewp_unfold E) /ewp_pre. *)
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
         iApply (monotonic_prot with "[] H").
         iIntros (w) "H !>".
         subst sh.
         rewrite swfill_trans.
         eapply swfill_to_lfilled in Hout as Hfilled.
         2:{ instantiate (2 := swfill i0 shin (v_to_e_list w)).
             instantiate (2 := i0).
             done. } 
         destruct Hfilled as [k' Hfilled].
         apply lfilled_depth in HLI as Hdepth1.
         apply lfilled_depth in Hfilled as Hdepth2.
         rewrite Hdepth1 in Hdepth2; subst i k'.

         iSpecialize ("IH" $! lh (swfill i0 shin (v_to_e_list w)) Ψ _ Hpure Hlh).
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
        * rewrite merge_throw in Hetof.
          inversion Hetof; subst.
          iDestruct "H" as (Ξ) "[? H]".
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

(* not sure if this is still true with frame baked in ewp *)
(*  Lemma ewp_label_bind_inv (E : coPset) Ψ (Φ : iris.val -> frame -> iProp Σ) e n es l1 l2 f Φf Φf0:
    const_list l1 ->
    EWP e UNDER f @ E CTX 1; LH_rec l1 n es (LH_base [] []) l2 <| Ψ |> {{ w, Φ w ; Φf}} -∗
    EWP e UNDER f @ E <| Ψ |> {{ w, ∀ f', Φf0 f' -∗ EWP of_val0 w UNDER f' @ E CTX 1; LH_rec l1 n es (LH_base [] []) l2 <| Ψ |> {{ w, Φ w ; Φf0 }} ; Φf }}.
  Proof.
    iIntros (Hconst) "H".
    iLöb as "IH" forall (E e f).
    eassert (lfilled 1 (LH_rec l1 n es (LH_base [] []) l2) e _) as Hfill.
    { apply lfilled_Ind_Equivalent. constructor;eauto. constructor;eauto. }
    repeat rewrite ewp_unfold /ewp_pre /=.
    destruct (iris.to_val e) eqn:Hetov.
    { iDestruct ("H" with "[]") as "H".
      { iPureIntro. eauto. }
      iModIntro.
(*      rewrite /= cats0.
      iDestruct (ewp_unfold with "H") as "H".
      rewrite /ewp_pre.
      rewrite /to_val /to_eff /=.
      rewrite /to_val in Hetov.
      rewrite map_app /= merge_app.
      destruct (merge_values _) => //.
      inversion Hetov; subst.
      apply const_list_to_val in Hconst as (vs' & Htvl1 & Hvte).
      rewrite /to_val in Htvl1.
      destruct (merge_values _) => //.
      inversion Htvl1; subst.
      destruct v.
      - rewrite merge_notval /=. *)

        
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

  Lemma ewp_label_bind_next (E : coPset) Ψ (Φ : iris.val -> frame -> iProp Σ) e n es l1 l2 i lh :
    is_pure lh ->
  (*  lh_eff_None lh -> *)
    base_is_empty lh ->
    EWP e @ E <| Ψ |> {{ w, EWP of_val0 w @ E CTX (S i); LH_rec l1 n es lh l2 <| Ψ |> {{ w, Φ w }} }} -∗
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
  
Lemma ewp_ctx_bind (E : coPset) Ψ (Φ : iris.val -> frame -> iProp Σ) e i lh f Φf Φf0:
  is_pure lh ->
    base_is_empty lh ->
    EWP e UNDER f @ E <| Ψ |> {{ w, ∀ f', Φf0 f' -∗ EWP of_val0 w UNDER f' @ E CTX i; lh <| Ψ |> {{ w, Φ w ; Φf }} ; Φf0 }} -∗
    EWP e UNDER f @ E CTX i; lh <| Ψ |> {{ w, Φ w ; Φf }}.
  Proof.
    iIntros (Hpure Hbase) "He".
    iInduction (Hpure) as [] "IH" forall (i Φ f).
    - iIntros (LI Hfill%lfilled_Ind_Equivalent).
      inversion Hfill;simplify_eq.
      inversion Hbase;simplify_eq.
      erewrite app_nil_r, app_nil_l.
      iApply ewp_fupd.

      clear Hfill.
      iLöb as "IH" forall (e f).
      rewrite !ewp_unfold /ewp_pre.
      destruct (to_val e) eqn:Hte; last destruct (to_eff e) eqn:Htf.
      + iMod "He" as "[H Hf]".
        iSpecialize ("H" with "Hf").
        iDestruct (ewp_wasm_empty_ctx with "H") as "H".
        iDestruct (ewp_value_fupd with "H") as "H".
        unfold IntoVal. done.
        iMod "H" as "[??]".
        iFrame.
        done.
      + destruct e0.
        all: iApply (monotonic_prot with "[] He").
        all: iIntros (w) "H".
        3: done.
        all: iNext.
        all: iApply ("IH" with "H").
      + iIntros (σ) "Hσ".
        iMod ("He" with "Hσ") as "[%Hred H]".
        iModIntro.
        iSplit; first done.
        iIntros (e2 s2 i2 l2 Hstep).
        iSpecialize ("H" $! e2 s2 i2 l2 Hstep).
        iMod "H". iModIntro. iNext. iMod "H".
        iModIntro. iMod "H" as "[Hs H]".
        iModIntro. iFrame.
        iApply ("IH" with "H").
(*      
      iApply (ewp_wand with "He").
      iIntros (v) "Hv".
      iSpecialize ("Hv" $! (of_val0 v) with "[]");[iPureIntro;cbn;apply/eqP;by rewrite app_nil_r|].
      iDestruct (ewp_unfold with "Hv") as "Hv".
      rewrite /ewp_pre/=. rewrite to_of_val. done.  *)
    - simpl in Hbase.
      iSpecialize ("IH" $! Hbase).
      destruct i.
      { iIntros (LI HLI%lfilled_Ind_Equivalent);inversion HLI;inversion H8. }
      iApply ewp_label_bind_next;eauto. 
  Qed. *)


    
End bind_rules.
