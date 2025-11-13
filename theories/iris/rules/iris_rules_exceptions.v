
From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.
From Wasm.iris.language Require Import iris_ewp_ctx.
From Wasm.iris.helpers Require Import iris_properties.
From stdpp Require Import base list.
From mathcomp Require Import ssreflect eqtype seq ssrbool.





Set Bullet Behavior "Strict Subproofs".
Close Scope byte_scope.


(* ========================================================================== *)
(** * Reasoning Rules. *)

Section reasoning_rules.
  Context `{!wasmG Σ}.

   Lemma tag_valid gm a q tf:
    gen_heap_interp gm -∗ a ↦[tag]{q} tf -∗ ⌜ gm !! a = Some tf ⌝.
  Proof.
    iIntros "Htags Htag".
    iDestruct (gen_heap_valid with "Htags Htag") as "%Htag".
    done.
  Qed.

  Lemma ewp_throw f x a ves vcs ts E Ψ Φ:
    List.nth_error (inst_tags (f_inst f)) x = Some a ->
    ves = v_to_e_list vcs ->
    length ves = length ts ->
    N.of_nat a ↦[tag] (Tf ts []) ∗
      ▷ (∀ i, N.of_nat i ↦[we] {| e_tag := Mk_tagidx a ; e_fields := vcs |} -∗
             EWP [AI_ref_exn i (Mk_tagidx a); AI_basic BI_throw_ref] UNDER f @ E <| Ψ |> {{ Φ }})
      ⊢ EWP ves ++ [AI_basic (BI_throw x)] UNDER f @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hx -> Hlen) "[Htag Hwp]".
    iApply ewp_lift_step.
    { rewrite to_val_cat_None2 => //.
      apply v_to_e_is_const_list. }
    { rewrite to_eff_cat_None2 => //.
      apply v_to_e_is_const_list. }
    iIntros (σ) "Hσ".
    iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hclose".

    iDestruct "Hσ" as "(Hfuncs & Hconts & Hexns & Htags & Hrest)".
    iDestruct (tag_valid with "Htags Htag") as "%Htag".
    rewrite gmap_of_list_lookup in Htag.
    rewrite Nat2N.id in Htag.
    iSplit.
    { iPureIntro.
      eexists _,(_,_),_,_.
      repeat split => //.
      eapply r_throw => //.
      exact Hx.
      rewrite nth_error_lookup //.
      exact Htag.
      done.
    }
    iIntros "!>" (e2 ?? HStep).
    iMod (gen_heap_alloc with "Hexns") as "(Hexns & Hexn & Htok)"; last first. 
    iMod "Hclose".
    iModIntro.

    destruct HStep as (Hred & _).
    edestruct reduce_det.
    exact Hred.
    eapply r_throw => //; eauto.
    rewrite nth_error_lookup //.
    destruct H0.
    - destruct H0 as [-> ->].
      subst f. 
      iFrame "Hfuncs Hconts Htags Hrest".
      iSplitR "Hwp Hexn"; last first.
      + iApply ("Hwp" with "Hexn").
      + unfold add_exn. simpl.
        rewrite -gmap_of_list_append.
        iFrame. 
    - destruct H0 as [[? H'] | (? & ? & ? & H' & _)].
      all: rewrite first_instr_const in H' => //.
      all: apply v_to_e_is_const_list.
    - rewrite gmap_of_list_lookup.
      rewrite Nat2N.id.
      apply lookup_ge_None_2.
      lia.
  Qed. 

  Lemma ewp_throw_ref a exn i Ψ f E Φ:
    i = e_tag exn ->
    N.of_nat a ↦[we] exn ∗ get_throw i Ψ (e_fields exn) a
      ⊢ EWP [AI_ref_exn a i; AI_basic BI_throw_ref] UNDER f @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (->) "[Hexn HΨ]".
    iApply ewp_lift_step => //.
    iIntros (σ) "Hσ".
    iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hclose".

    iDestruct "Hσ" as "(Hfuncs & Hconts & Hexns & Hrest)".
    iDestruct (gen_heap_valid with "Hexns Hexn") as %Hexn.
    rewrite gmap_of_list_lookup in Hexn.
    rewrite Nat2N.id in Hexn.
    iSplit.
    { iPureIntro.
      eexists _,(_,_),_,_.
      repeat split => //.
      eapply r_throw_ref_desugar => //.
      rewrite nth_error_lookup //.
    }
    iIntros "!>" (e2 ?? HStep).
    iMod "Hclose".
    iModIntro.

    destruct HStep as (Hred & _).
    edestruct reduce_det.
    exact Hred.
    eapply r_throw_ref_desugar => //; eauto.
    rewrite nth_error_lookup //.
    destruct H0.
    - destruct H0 as [-> ->].
      subst f. 
      iFrame.
      iApply ewp_effect_thr => //. 
    - destruct H0 as [[? H'] | (? & ? & ? & H' & _)].
      done. done.
  Qed.

  Definition agree_on_uncaptured decs (Ψ Ψ' : meta_protocol) : Prop :=
    (forall i, get_suspend i Ψ = get_suspend i Ψ') /\
      (forall i, get_switch i Ψ = get_switch i Ψ') /\
      (forall i, firstx_exception decs i = No_label ->
            get_throw i Ψ = get_throw i Ψ')
  .


  Definition safe_clause Ψ' dec E Ψ Φ : iProp Σ :=
     match dec with
    | DE_catch y l =>
        ∀ vs i f,
          get_throw y Ψ' vs i -∗
          EWP v_to_e_list vs ++ [AI_basic (BI_br l)] UNDER f @ E <| Ψ |> {{ Φ }}
    | DE_catch_ref y l =>
        ∀ vs i f,
          get_throw y Ψ' vs i -∗
          EWP v_to_e_list vs ++ [AI_ref_exn i y; AI_basic (BI_br l)] UNDER f @ E <| Ψ |> {{ Φ }}
    | DE_catch_all l =>
        ∀ y vs i f,
          get_throw y Ψ' vs i -∗
          EWP v_to_e_list vs ++ [AI_basic (BI_br l)] UNDER f @ E <| Ψ |> {{ Φ }}
    | DE_catch_all_ref l =>
        ∀ y vs i f,
          get_throw y Ψ' vs i -∗
          EWP v_to_e_list vs ++ [AI_ref_exn i y; AI_basic (BI_br l)] UNDER f @ E <| Ψ |> {{ Φ }}
    end.

  Lemma firstx_throw_lookup dccs i l:
    firstx_exception dccs i = Clause_label l ->
    exists k, dccs !! k = Some (DE_catch i l) \/ dccs !! k = Some (DE_catch_all l).
  Proof.
    induction dccs => //=.
    destruct a => //=.
    - destruct (eqtype.eq_op i t) eqn:Hit => //.
      + intros H; inversion H; subst; clear H.
        apply b2p in Hit as ->.
        exists 0; by left. 
      + intros H; apply IHdccs in H as [k Hres].
        exists (S k) => //.
    - destruct (eqtype.eq_op i t) eqn:Hit => //.
      intros H; apply IHdccs in H as [k Hres].
      exists (S k) => //.
    - intros H; inversion H; subst. exists 0. by right. 
  Qed.

   Lemma firstx_throw_lookup_ref dccs i l:
    firstx_exception dccs i = Clause_label_ref l ->
    exists k, dccs !! k = Some (DE_catch_ref i l) \/ dccs !! k = Some (DE_catch_all_ref l).
  Proof.
    induction dccs => //=.
    destruct a => //=.
    - destruct (eqtype.eq_op i t) eqn:Hit => //.
      intros H; apply IHdccs in H as [k Hres].
      exists (S k) => //.
    - destruct (eqtype.eq_op i t) eqn:Hit => //.
      + intros H; inversion H; subst; clear H.
        apply b2p in Hit as ->.
        exists 0; by left. 
      + intros H; apply IHdccs in H as [k Hres].
        exists (S k) => //.
    - intros H; inversion H; subst. exists 0. by right. 
  Qed.
   


  Lemma thrE_first_instr es vs a i sh :
    to_eff0 es = Some (thrE vs a i sh) ->
    exists k, first_instr es = Some (AI_throw_ref_desugared vs a i, k).
  Proof.
    remember (S (length_rec es)) as m.
    assert (length_rec es < m); first by subst; lia.
    clear Heqm.
    generalize dependent sh.
    generalize dependent es.
    induction m => //.
    { intros es Hlen; lia. } 
    intros es Hlen sh.
    destruct es => //. 
    unfold to_eff0 => //=.
    rewrite merge_prepend.
    destruct (to_val_instr a0) eqn:Ha => //.
    - destruct v => //=.
      + unfold to_eff0 in IHm.
        specialize (IHm es).
        destruct (merge_values _) => //.
        * destruct v => //. destruct l => //.
        * destruct e => //.
          intros H; inversion H; subst; clear H.
          edestruct IHm as [k Hes] => //.
          specialize (length_cons_rec a0 es). lia.
          unfold first_instr.
          simpl.
          unfold first_instr in Hes.
          rewrite Hes.
          destruct a0 => //=.
          destruct b => //=.
          all: try by eexists.
          all: simpl in Ha.
          all: destruct (merge_values _) => //.
          all: try by destruct v => //.
          all: try destruct e => //.
          destruct (exnelts_of_exception_clauses _ _) => //.
          destruct (suselts_of_continuation_clauses _ _) => //.
          destruct (swelts_of_continuation_clauses _ _) => //.
          destruct v => //.
          destruct i0 => //.
          destruct (vh_decrease _) => //.
      + destruct (expr_of_val_not_val _) => //.
    - destruct e => //.
      simpl.
      intros H; inversion H; subst; clear H.
      destruct a0 => //=.
      + destruct b => //=.
      + simpl in Ha. inversion Ha; subst. by eexists.
      + simpl in Ha.
        specialize (Logic.eq_refl (to_eff0 l0)) as Heq.
        unfold to_eff0 in Heq at 2.
        destruct (merge_values _) => //.
        destruct v => //.
        destruct e => //.
        destruct (exnelts_of_exception_clauses _ _) => //.
        inversion Ha; subst.
        apply IHm in Heq as [k Hk].
        unfold first_instr.
        unfold first_instr in Hk.
        simpl.
        rewrite Hk.
        by eexists.
        unfold length_rec in Hlen.
        unfold length_rec.
        simpl in Hlen. lia.
      + simpl in Ha.
        specialize (Logic.eq_refl (to_eff0 l1)) as Heq.
        unfold to_eff0 in Heq at 2.
        destruct (merge_values _) => //.
        destruct v => //.
        destruct e => //.
        destruct suselts_of_continuation_clauses => //.
        destruct (swelts_of_continuation_clauses _ _) => //.
        inversion Ha; subst.
        apply IHm in Heq as [k Hk].
        unfold first_instr.
        unfold first_instr in Hk.
        simpl.
        rewrite Hk.
        by eexists.
        unfold length_rec in Hlen.
        unfold length_rec.
        simpl in Hlen. lia.
      + simpl in Ha.
        specialize (Logic.eq_refl (to_eff0 l0)) as Heq.
        unfold to_eff0 in Heq at 2.
        destruct (merge_values _) => //.
        destruct v => //.
        2: destruct e => //.
        destruct i0 => //.
        destruct (vh_decrease _) => //. 
        inversion Ha; subst.
        apply IHm in Heq as [k Hk].
        unfold first_instr.
        unfold first_instr in Hk.
        simpl.
        rewrite Hk.
        by eexists.
        unfold length_rec in Hlen.
        unfold length_rec.
        simpl in Hlen. lia.
      + simpl in Ha.
        specialize (Logic.eq_refl (to_eff0 l)) as Heq.
        unfold to_eff0 in Heq at 2.
        destruct (merge_values _) => //.
        destruct v => //.
        destruct e => //.
        inversion Ha; subst.
        apply IHm in Heq as [k Hk].
        unfold first_instr.
        unfold first_instr in Hk.
        simpl.
        rewrite Hk.
        by eexists.
        unfold length_rec in Hlen.
        unfold length_rec.
        simpl in Hlen. lia.
  Qed.

  
  
  Lemma ewp_handler hs Ψ Ψ' es f E Φ' Φ:
    agree_on_uncaptured hs Ψ Ψ' ->
    ((∀ f, ¬ Φ' trapV f) ∗ EWP es UNDER f @ E <| Ψ' |> {{ Φ' }} ∗
      (∀ v' f', Φ' v' f' -∗ EWP [AI_handler hs (of_val0 v')] UNDER f' @ E <| Ψ |> {{ Φ }}) ∗
      ([∗ list] dec ∈ hs, safe_clause Ψ' dec E Ψ Φ)
      ⊢ EWP [AI_handler hs es] UNDER f @ E <| Ψ |> {{ Φ }})%I.
  Proof.
    iLöb as "IH" forall (hs es E Ψ Ψ' Φ Φ' f).
    iIntros (HΨ) "(Hntrap & Hes & HΦ & Hclauses)".
    destruct (to_val0 es) eqn:Htv.
    { iDestruct ewp_value_fupd as "[H _]";
        last iDestruct ("H" with "Hes") as "Hes".
      exact Htv. 

      iApply fupd_ewp.
      unfold to_eff0. simpl.
      unfold to_val0 in Htv.
      destruct (merge_values _) => //.
      destruct v0 => //.
      iMod "Hes" as "Hes".
      iDestruct ("HΦ" with "Hes") as "Hres".
      iModIntro.
      erewrite of_to_val0 => //.
    }
    destruct (to_eff0 es) eqn:Htf.
    { 
      destruct e.
      - iDestruct (ewp_effect_sus with "Hes") as "Hes" ; eauto.
        remember (Logic.eq_refl (to_eff0 [AI_handler hs es])) as Htf'; clear HeqHtf'.
        unfold to_eff0 in Htf' at 2.
        simpl in Htf'.
        remember Htf as Htf0; clear HeqHtf0.
        unfold to_eff0 in Htf.
        destruct (merge_values _) => //.
        inversion Htf; subst e.
        simpl in Htf'.
        iApply ewp_effect_sus; eauto.
        remember HΨ as HΨ'; clear HeqHΨ'.
        destruct HΨ as [HΨ _].
        rewrite -HΨ.
        iApply (monotonic_prot with "[-Hes] Hes").
        iIntros (w) "Hw".
        iNext. iSimpl.
        unfold to_eff0 in Htf'.
        simpl in Htf'.
        destruct (merge_values (List.map _ es)) eqn:HLI => //.
        destruct v => //.
        destruct e => //.
        2:{ destruct (exnelts_of_exception_clauses _ _) => //. } 
        simpl in Htf' => //.
        inversion Htf'; subst.
        iApply "IH".
        done.
        iFrame.
      - destruct i. iDestruct (ewp_effect_sw with "Hes") as "Hes" ; eauto.
        remember (Logic.eq_refl (to_eff0 [AI_handler hs es])) as Htf'; clear HeqHtf'.
        unfold to_eff0 in Htf' at 2.
        simpl in Htf'.
        remember Htf as Htf0; clear HeqHtf0.
        unfold to_eff0 in Htf.
        destruct (merge_values _) => //.
        inversion Htf; subst e.
        simpl in Htf'.
        iApply ewp_effect_sw; eauto.
        remember HΨ as HΨ'; clear HeqHΨ'.
        destruct HΨ as (_ & HΨ & _).
        unfold get_switch2, get_switch1.
        rewrite -HΨ.
        iDestruct "Hes" as (??????) "(? & ? & ? & Htf' & Htf & ? & Hes)".
        iFrame "Htf'".
        iFrame.
        iIntros "Htag".
        iPoseProof ("Hes" with "Htag") as "Hes".
        iApply (monotonic_prot with "[-Hes] Hes").
        iIntros (w) "Hw".
        iNext. iSimpl.
        unfold to_eff0 in Htf'.
        simpl in Htf'.
        destruct (merge_values (List.map _ es)) eqn:HLI => //.
        destruct v => //.
        destruct e => //.
        2:{ destruct (exnelts_of_exception_clauses _ _) => //. } 
        simpl in Htf' => //.
        inversion Htf'; subst.
        iApply "IH".
        done.
        iFrame.
      - iDestruct (ewp_effect_thr with "Hes") as "Hes" ; eauto.
        remember (Logic.eq_refl (to_eff0 [AI_handler hs es])) as Htf'; clear HeqHtf'.
        unfold to_eff0 in Htf' at 2.
        simpl in Htf'.
        remember Htf as Htf0; clear HeqHtf0.
        unfold to_eff0 in Htf.
        destruct (merge_values _) => //.
        inversion Htf; subst e.
        destruct (exnelts_of_exception_clauses hs i) eqn:Helts.
        + simpl in Htf'.
          iApply ewp_effect_thr; eauto.
          remember HΨ as HΨ'; clear HeqHΨ'.
          destruct HΨ as (_ & _ & HΨ).
          rewrite -HΨ. done.
          eapply exnelts_firstx. exact Helts. 
        + simpl in Htf'.
          apply exnelts_of_exception_clauses_None in Helts as Hfirst.
          iApply ewp_lift_step => //.
          apply to_val_None_handler => //.
          iIntros (σ) "Hσ".
          iApply fupd_mask_intro; first solve_ndisj.
          iIntros "Hclose".
          destruct i.
          destruct (firstx_exception hs (Mk_tagidx n)) eqn:Hfirst' => //. 
          * apply firstx_throw_lookup in Hfirst' as Hfirst''.
            destruct Hfirst'' as [k [Hk | Hk]].
            -- iDestruct (big_sepL_lookup with "Hclauses") as "Hclause".
               exact Hk.
               eassert (reduce σ _ [AI_handler hs es] _ _ _).
               { eapply r_throw_ref.
                 2: exact Hfirst'. 
                 apply of_to_eff0 in Htf0.
                 unfold of_eff0 in Htf0.
                 rewrite -Htf0.
                 apply exnfill_to_hfilled. }
               iSplit.
               { iPureIntro.
                 unfold reducible.
                 eexists _, (_, _) , _, _.
                 repeat split => //. eauto. }
               iIntros (es2 σ2 ? Hstep).
               destruct Hstep as (Hstep & _ & _).
               edestruct reduce_det. 
               exact Hstep. exact H.
               subst.
               destruct H1 as [(-> & ->) | Habs].
               ++ iFrame.
                  iNext. iMod "Hclose". iModIntro.
                  iApply ("Hclause" with "Hes").
               ++ apply thrE_first_instr in Htf0 as [k' Htf0].
                  rewrite first_instr_const in Habs; last by apply v_to_e_is_const_list.
                  unfold first_instr in Habs.
                  unfold first_instr in Htf0.
                  simpl in Habs.
                  simpl in Htf0.
                  rewrite Htf0 in Habs.
                  exfalso.
                  destruct Habs as [(? & Habs) | (? & ? & ? & Habs & _)] => //.
            -- iDestruct (big_sepL_lookup with "Hclauses") as "Hclause".
               exact Hk.
               eassert (reduce σ _ [AI_handler hs es] _ _ _).
               { eapply r_throw_ref.
                 2: exact Hfirst'. 
                 apply of_to_eff0 in Htf0.
                 unfold of_eff0 in Htf0.
                 rewrite -Htf0.
                 apply exnfill_to_hfilled. }
               iSplit.
               { iPureIntro.
                 unfold reducible.
                 eexists _, (_, _) , _, _.
                 repeat split => //. eauto. }
               iIntros (es2 σ2 ? Hstep).
               destruct Hstep as (Hstep & _ & _).
               edestruct reduce_det. 
               exact Hstep. exact H.
               subst.
               destruct H1 as [(-> & ->) | Habs].
               ++ iFrame.
                  iNext. iMod "Hclose". iModIntro.
                  iApply ("Hclause" with "Hes").
               ++ apply thrE_first_instr in Htf0 as [k' Htf0].
                  rewrite first_instr_const in Habs; last by apply v_to_e_is_const_list.
                  unfold first_instr in Habs.
                  unfold first_instr in Htf0.
                  simpl in Habs.
                  simpl in Htf0.
                  rewrite Htf0 in Habs.
                  exfalso.
                  destruct Habs as [(? & Habs) | (? & ? & ? & Habs & _)] => //.
          * apply firstx_throw_lookup_ref in Hfirst' as Hfirst''.
            destruct Hfirst'' as [k [Hk | Hk]].
            -- iDestruct (big_sepL_lookup with "Hclauses") as "Hclause".
               exact Hk.
               eassert (reduce σ _ [AI_handler hs es] _ _ _).
               { eapply r_throw_ref_ref.
                 2: exact Hfirst'. 
                 apply of_to_eff0 in Htf0.
                 unfold of_eff0 in Htf0.
                 rewrite -Htf0.
                 apply exnfill_to_hfilled. }
               iSplit.
               { iPureIntro.
                 unfold reducible.
                 eexists _, (_, _) , _, _.
                 repeat split => //. eauto. }
               iIntros (es2 σ2 ? Hstep).
               destruct Hstep as (Hstep & _ & _).
               edestruct reduce_det. 
               exact Hstep. exact H.
               subst.
               destruct H1 as [(-> & ->) | Habs].
               ++ iFrame.
                  iNext. iMod "Hclose". iModIntro.
                  iApply ("Hclause" with "Hes").
               ++ apply thrE_first_instr in Htf0 as [k' Htf0].
                  rewrite first_instr_const in Habs; last by apply v_to_e_is_const_list.
                  unfold first_instr in Habs.
                  unfold first_instr in Htf0.
                  simpl in Habs.
                  simpl in Htf0.
                  rewrite Htf0 in Habs.
                  exfalso.
                  destruct Habs as [(? & Habs) | (? & ? & ? & Habs & _)] => //.
            -- iDestruct (big_sepL_lookup with "Hclauses") as "Hclause".
               exact Hk.
               eassert (reduce σ _ [AI_handler hs es] _ _ _).
               { eapply r_throw_ref_ref.
                 2: exact Hfirst'. 
                 apply of_to_eff0 in Htf0.
                 unfold of_eff0 in Htf0.
                 rewrite -Htf0.
                 apply exnfill_to_hfilled. }
               iSplit.
               { iPureIntro.
                 unfold reducible.
                 eexists _, (_, _) , _, _.
                 repeat split => //. eauto. }
               iIntros (es2 σ2 ? Hstep).
               destruct Hstep as (Hstep & _ & _).
               edestruct reduce_det. 
               exact Hstep. exact H.
               subst.
               destruct H1 as [(-> & ->) | Habs].
               ++ iFrame.
                  iNext. iMod "Hclose". iModIntro.
                  iApply ("Hclause" with "Hes").
               ++ apply thrE_first_instr in Htf0 as [k' Htf0].
                  rewrite first_instr_const in Habs; last by apply v_to_e_is_const_list.
                  unfold first_instr in Habs.
                  unfold first_instr in Htf0.
                  simpl in Habs.
                  simpl in Htf0.
                  rewrite Htf0 in Habs.
                  exfalso.
                  destruct Habs as [(? & Habs) | (? & ? & ? & Habs & _)] => //. } 

    iApply ewp_unfold.
    rewrite /ewp_pre /= to_val_None_handler // to_eff_None_handler //.
    iIntros (σ) "Hσ".

    
    rewrite ewp_unfold /ewp_pre.
    rewrite /= Htv Htf.
    iMod ("Hes" with "Hσ") as "[%Hred Hes]".
    iModIntro.
    iSplit.
    { iPureIntro.
      destruct Hred as (obs & [es' f'] & σ' & efs & Hred & -> & ->).
      eassert _ as Hred'.
      { eapply r_label.
        exact Hred.
        instantiate (2 := LH_handler [] hs (LH_base [] []) []).
        instantiate (2 := 0).
        rewrite /lfilled /lfill /= app_nil_r //.
        rewrite /lfilled /lfill /= app_nil_r //. } 
      eexists [], (_,_), _, [].
      split; last done.
      exact Hred'. } 
    iIntros ([es2 f2] σ2 Hstep).
    eapply lfilled_prim_step_split_reduce_r in Hstep as Hstep0.
    2:{ instantiate (1 := []).
        instantiate (1 := es).
        instantiate (1 := LH_handler [] hs (LH_base [] []) []).
        instantiate (1 := 0).
        unfold lfilled, lfill => //=.
        repeat rewrite app_nil_r.
        rewrite eqtype.eq_refl => //. }
    2:{ destruct Hred as (obs & [es' f'] & σ' & efs & Hred & -> & ->).
        eexists [], (_,_), _, [].
        split; last done.
        exact Hred. } 

    destruct Hstep as [Hstep _].
    destruct Hstep0 as [(e' & Hstep' & Hfill') | ([lh Htrap] & Hσ)].
    - iDestruct ("Hes" $! (_,_) _ Hstep') as "Hes".
      iSimpl.
      iMod "Hes".
      repeat iModIntro.
      repeat iMod "Hes".
      iModIntro.
      iDestruct "Hes" as "(Hσ & He')".

      iFrame.
      unfold lfilled, lfill in Hfill'.
      simpl in Hfill'.
      rewrite app_nil_r in Hfill'.
      rewrite cat_app app_nil_r in Hfill'.
      apply b2p in Hfill' as ->.
      iApply ("IH"). done.
      iFrame. 
    - inversion Hσ; subst σ.
      assert (prim_step (es, f) σ2 [] ([AI_trap], f) σ2 []).
      { repeat split => //.
        constructor. econstructor. 2: exact Htrap.
        intros ->; by simpl in Htv. } 
      iDestruct ("Hes" $! (_,_) _ H) as "Hes". 
      iMod "Hes".
      repeat iModIntro.
      repeat iMod "Hes".
      iDestruct "Hes" as "(Hσ & Hes)".
      iDestruct ewp_value_fupd as "[H _]".
      instantiate (1 := trapV) => //.
      instantiate (1 := [AI_trap]) => //.
      
      iMod ("H" with "Hes") as "Habs".
      iDestruct ("Hntrap" with "Habs") as "Habs" => //.
  Qed. 

  Lemma ewp_try_table f hs hs' es i t1s t2s vs n E Ψ Ψ' Φ Φ':
    map (desugar_exception_clause (f_inst f)) hs = map Some hs' ->
    stypes (f_inst f) i = Some (Tf t1s t2s) ->
    length t1s = length vs ->
    is_true $ const_list vs ->
    n = length t2s ->
    agree_on_uncaptured hs' Ψ Ψ' ->
    ((∀ f, ¬ Φ' trapV f) ∗ ▷ EWP [AI_label n [] (vs ++ to_e_list es)] UNDER f @ E <| Ψ' |> {{ Φ' }} ∗
       ▷ (∀ v' f', Φ' v' f' -∗ EWP [AI_handler hs' (of_val0 v')] UNDER f' @ E <| Ψ |> {{ Φ }}) ∗
       ▷ ([∗ list] dec ∈ hs', safe_clause Ψ' dec E Ψ Φ)
       ⊢ EWP vs ++ [AI_basic (BI_try_table i hs es)] UNDER f @ E <| Ψ |> {{ Φ }})%I.
  Proof.
    iIntros (Hhs Hi Hlen Hvs -> HΨ) "(Hntrap & Hes & HΦ & Hclauses)".
    iApply ewp_lift_step => //.
    { rewrite to_val_cat_None2 => //. } 
    { rewrite to_eff_cat_None2 => //. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    
    eassert (reduce σ f
              (vs ++ [AI_basic (BI_try_table i hs es)])
              σ f
              _
           ) as Hred2.
    { eapply r_try_table => //.
      exact Hi. done. exact Hhs. }
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], (_, _), _, [].
      repeat split => //.
      exact Hred2.

    - iApply fupd_mask_intro; first solve_ndisj.
      iIntros "Hclose !>" (es' σ2 ? HStep).
      destruct HStep as (H & _).
      edestruct reduce_det.
      exact H. exact Hred2.
      subst.
      destruct H1 as [[-> ->] | H0].
      2:{ destruct H0.
          destruct H0 as (? & Habs).
          by rewrite first_instr_const in Habs.
          destruct H0 as (? & ? & ? & Habs & _).
          rewrite first_instr_const in Habs => //.
      }
      iMod "Hclose". iModIntro.
      iFrame.
      iApply ewp_handler.
      exact HΨ.
      iFrame.
  Qed.


End reasoning_rules.
