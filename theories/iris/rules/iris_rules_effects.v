(* basic_reasoning_rules.v *)

(* This theory introduces the basic principles that allow reasoning in terms
   of [EWP]. The most important principles in this theory are the bind rule,
   which endorses modular reasoning about the evaluation context by allowing
   one to compose specifications; and the frame rule, which endorses modular
   reasoning about the state by allowing one to derive specifications with
   a larger footprint than their original statement. *)


From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.
From Wasm.iris.language Require Import iris_ewp_ctx.
From Wasm.iris.helpers Require Import iris_properties.
(* From Wasm.iris.rules Require Import iris_rules_structural. *)

Set Bullet Behavior "Strict Subproofs".
Close Scope byte_scope.

Section clause_triple.
  Context `{!wasmG Σ}.

  Definition clause_triple E Ψ Φ dcc Ψ' Φ' : iProp Σ :=
    match dcc with
    | DC_catch taddr ilab =>
        ∀ vs kaddr tf h,
          N.of_nat kaddr ↦[wcont] Cont_hh tf h -∗
            iProt_car (upcl $ Ψ $ SuspendE taddr) (immV vs) (λ w, ∀ LI, ⌜ hfilled No_var h (of_val w) LI ⌝ -∗ ▷ (* no calling continuations in wasm, so adding this later to symbolise that step *) EWP LI @ E <| Ψ |> {{ Φ }}) -∗
            EWP v_to_e_list vs ++ [AI_ref_cont kaddr; AI_basic (BI_br ilab)] @ E <| Ψ' |> {{ Φ' }}
    | DC_switch _ => False
    end.

  Lemma monotonic_clause_triple E Ψ1 Ψ2 Φ1 Φ2 dcc Ψ'1 Ψ'2 Φ'1 Φ'2 :
    (∀ x, Ψ2 x ⊑ Ψ1 x)%iprot -∗
        (∀ v, Φ2 v ={E}=∗ Φ1 v) -∗
        (∀ x, Ψ'1 x ⊑ Ψ'2 x)%iprot -∗
        (∀ v, Φ'1 v ={E}=∗ Φ'2 v) -∗
    clause_triple E Ψ1 Φ1 dcc Ψ'1 Φ'1 -∗
        clause_triple E Ψ2 Φ2 dcc Ψ'2 Φ'2.
  Proof.
    iIntros "#HΨ HΦ #HΨ' HΦ' Htrip".
    destruct dcc => //.
    iIntros (vs kaddr tf h) "Hcont Hprot".
    iDestruct ("Htrip" $! vs kaddr tf h with "Hcont [HΦ Hprot]") as "Htrip".
    - iApply (monotonic_prot with "[HΦ] [Hprot]"); last first.
      + iDestruct "Hprot" as (Ψ') "[H Hnext]".
        iExists Ψ'.
        iFrame "Hnext".
        iApply ("HΨ" with "H").
      + iIntros (w) "Hw".
        iIntros (LI HLI).
        iDestruct ("Hw" $! _ HLI) as "Hw".
        iNext.
        iApply (ewp_strong_mono with "Hw HΨ HΦ").
        done.
    - iApply (ewp_strong_mono with "Htrip HΨ' HΦ'").
      done.
  Qed.

        
  Definition clause_resources dccs :=
    ([∗ list] dcc ∈ dccs,
      match dcc with
      | DC_catch (Mk_tagidx addr) _
      | DC_switch (Mk_tagidx addr) =>
          ∃ t1s t2s, N.of_nat addr ↪[tag] Tf t1s t2s
  end)%I .
                            
    
  

  Definition agree_on_uncaptured dccs (Ψ Ψ' : effect_identifier -d> iProt Σ) : Prop :=
    (forall i, firstx_continuation_suspend dccs i = None ->
          Ψ (SuspendE i) = Ψ' (SuspendE i)) /\
      (forall i, firstx_continuation_switch dccs i = false ->
            Ψ (SwitchE i) = Ψ' (SwitchE i)) /\
      (forall i, Ψ (ThrowE i) = Ψ' (ThrowE i))
        .

End clause_triple.


(* ========================================================================== *)
(** * Reasoning Rules. *)

Section reasoning_rules.
  Context `{!wasmG Σ}.

  

  Lemma ewp_suspend vs i E Ψ Φ f:
    ↪[frame] f ∗ iProt_car (upcl (Ψ $ SuspendE i)) (immV vs) Φ
      ⊢ EWP [ AI_suspend_desugared vs i ] @ E <| Ψ |> {{ v, Φ v ∗ ↪[frame] f}}.
  Proof.
    iIntros "[Hf HΨ]".
    iApply ewp_effect_sus => //.
    iFrame.
    iIntros "Hf".
    iApply (monotonic_prot with "[Hf] HΨ").
    iIntros (w) "Hw".
    iSimpl.
    rewrite app_nil_r.
    iApply ewp_value'.
    iFrame.
  Qed.

  Lemma suselts_of_continuation_clauses_None cls i:
    suselts_of_continuation_clauses cls i = None ->
    is_Some (firstx_continuation_suspend cls i).
  Proof.
    induction cls => //=.
    destruct (suselt_of_continuation_clause a i) eqn:Helt => //.
    - destruct (suselts_of_continuation_clauses cls i) => //.
      destruct a => //. destruct (eqtype.eq_op i t) => //.
    - unfold suselt_of_continuation_clause in Helt.
      destruct i.
      destruct a => //.
      destruct t => //.
      destruct (n0 <? n) eqn:Hn => //.
      destruct (n0 =? n) eqn:Hn' => //.
      apply Nat.eqb_eq in Hn' as ->.
      rewrite eqtype.eq_refl. done.
  Qed.

  Lemma firstx_suspend_lookup dccs i x :
    firstx_continuation_suspend dccs i = Some x ->
    exists k, dccs !! k = Some (DC_catch i x).
  Proof.
    induction dccs => //=.
    destruct a => //=.
    - destruct (eqtype.eq_op i t) eqn:Hit => //.
      + intros H; inversion H; subst; clear H.
        apply b2p in Hit as ->.
        exists 0 => //.
      + intros H; apply IHdccs in H as [k Hres].
        exists (S k) => //.
    - intros H; apply IHdccs in H as [k Hres].
      exists (S k) => //.
  Qed. 


  Lemma susE_first_instr es vs i sh :
    to_eff es = Some (susE vs i sh) ->
    exists k, first_instr es = Some (AI_suspend_desugared vs i, k).
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
    unfold to_eff => //=.
    rewrite merge_prepend.
    destruct (to_val_instr a) eqn:Ha => //.
    - destruct v => //=.
      + unfold to_eff in IHm.
        specialize (IHm es).
        destruct (merge_values _) => //.
        * destruct v => //. destruct l => //.
        * destruct e => //.
          intros H; inversion H; subst; clear H.
          edestruct IHm as [k Hes] => //.
          specialize (length_cons_rec a es). lia.
          unfold first_instr.
          simpl.
          unfold first_instr in Hes.
          rewrite Hes.
          destruct a => //=.
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
      destruct a => //=.
      + destruct b => //=.
      + simpl in Ha. inversion Ha; subst. by eexists.
      + simpl in Ha.
        specialize (Logic.eq_refl (to_eff l0)) as Heq.
        unfold to_eff in Heq at 2.
        destruct (merge_values _) => //.
        destruct v => //.
        destruct e => //.
        2: destruct (exnelts_of_exception_clauses _ _) => //.
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
        specialize (Logic.eq_refl (to_eff l1)) as Heq.
        unfold to_eff in Heq at 2.
        destruct (merge_values _) => //.
        destruct v => //.
        destruct e => //.
        destruct suselts_of_continuation_clauses => //.
        2: destruct (swelts_of_continuation_clauses _ _) => //.
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
        specialize (Logic.eq_refl (to_eff l0)) as Heq.
        unfold to_eff in Heq at 2.
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
        specialize (Logic.eq_refl (to_eff l)) as Heq.
        unfold to_eff in Heq at 2.
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


  

  Lemma ewp_prompt ts dccs es E Ψ Ψ' Φ Φ':
    agree_on_uncaptured dccs Ψ Ψ' ->
    (¬ Φ trapV ∗ EWP es @ E <| Ψ |> {{ Φ }} ∗
      (∀ w, Φ w -∗ EWP [AI_prompt ts dccs (of_val w)] @ E <| Ψ' |> {{ Φ' }}) ∗
      clause_resources dccs ∗
      [∗ list] dcc ∈ dccs, clause_triple E Ψ Φ dcc Ψ' Φ')%I
      ⊢ EWP [AI_prompt ts dccs es] @ E <| Ψ' |> {{ Φ' }}.
  Proof.
    iLöb as "IH" forall (ts dccs es E Ψ Ψ' Φ Φ').
    iIntros (HΨ) "(Hntrap & Hes & HΦ & Hclres & Hclauses)".
    destruct (to_val es) eqn:Htv.
    { iDestruct ewp_value_fupd as "[H _]";
        last iDestruct ("H" with "Hes") as "Hes".
      apply of_to_val in Htv. exact Htv.
      iApply fupd_ewp.
      unfold to_eff. simpl.
      unfold to_val in Htv.
      destruct (merge_values _) => //.
      destruct v0 => //.
      iMod "Hes".
      iDestruct ("HΦ" with "Hes") as "Hres".
      iModIntro.
      erewrite of_to_val => //. }
    destruct (to_eff es) eqn:Htf.
    { destruct e.
      - iDestruct (ewp_effect_sus with "Hes") as "Hes" => //.
        iDestruct "Hes" as (f) "[Hf Hes]".
        remember (Logic.eq_refl (to_eff [AI_prompt ts dccs es])) as Htf'; clear HeqHtf'.
        unfold to_eff in Htf' at 2.
        simpl in Htf'.
        remember Htf as Htf0; clear HeqHtf0.
        unfold to_eff in Htf.
        destruct (merge_values _) => //.
        inversion Htf; subst.
        destruct (suselts_of_continuation_clauses dccs i) eqn:Helts.
        + simpl in Htf'.
          iApply ewp_effect_sus => //.
          iFrame.
          iIntros "Hf".
          iDestruct ("Hes" with "Hf") as "Hes".
          remember HΨ as HΨ'; clear HeqHΨ'.
          destruct HΨ as [HΨ _].
          rewrite -HΨ.
          2: by eapply suselts_firstx.
          iApply (monotonic_prot with "[-Hes] Hes").
          iIntros (w) "Hw".
          iNext. iSimpl.
          erewrite suselts_of_continuation_clauses_inj => //.
          iApply "IH".
          done.
          iFrame.
        + simpl in Htf'.
          apply suselts_of_continuation_clauses_None in Helts as [x Hfirst].
          iApply ewp_lift_step => //.
          apply to_val_None_prompt => //.
          iIntros (σ ns κ κs nt) "Hσ".
          destruct σ as [[??]?].
          iApply fupd_mask_intro; first solve_ndisj.
          iIntros "Hclose".
          destruct i.
          apply firstx_suspend_lookup in Hfirst as Hfirst'.
          destruct Hfirst' as [k Hk].
          iDestruct (big_sepL_lookup with "Hclauses") as "Hclause".
          exact Hk.
          iDestruct (big_sepL_lookup with "Hclres") as "Hclres".
          exact Hk.
          iDestruct "Hclres" as (t1s t2s q) "Hclres".
          iDestruct "Hσ" as "(Hfuncs & Hconts & Htags & Hrest)".
          iDestruct (gen_heap_valid with "Htags Hclres") as %Htag.
          rewrite gmap_of_list_lookup in Htag.
          rewrite -nth_error_lookup in Htag.
          eassert (reduce s (Build_frame l i0) [AI_prompt ts dccs es] _ _ _).
          { eapply r_suspend.
            done.
            done.
            rewrite Nat2N.id.
            exact Hfirst.
            apply of_to_eff in Htf0.
            unfold of_eff in Htf0.
            subst es.
            rewrite Nat2N.id.
            apply susfill_to_hfilled. }
          iSplit.
          { iPureIntro.
            unfold reducible.
            eexists _, _, (_,_,_), _.
            repeat split => //. } 
            
          iIntros (es2 σ2 Hstep).
          destruct σ2 as [[??]?].
          destruct Hstep as (Hstep & -> & _).
          
          edestruct reduce_det. 
          exact Hstep. exact H.
          * inversion H0; subst.
            iFrame.


            iModIntro.
            iMod "Hclose".
          
            iMod (gen_heap_alloc with "Hconts") as "(Hconts & Hcont & Htok)";
              last first.
            iModIntro.

            iFrame.
            iSplitL "Hconts".
            { unfold new_cont. simpl.
              instantiate (2 := N.of_nat (length (s_conts s))).
              rewrite -gmap_of_list_append.
              iExact "Hconts". }
            2:{ rewrite gmap_of_list_lookup.
                rewrite Nat2N.id.
                apply lookup_ge_None_2.
                lia. }
            iIntros "Hf".

            iApply ("Hclause" with "Hcont").
            iDestruct ("Hes" with "[$]") as "Hes".
(*            iDestruct "Hes" as (Ξ) "[HΞ Hes]".
            iExists Ξ. iFrame.
            iIntros (w) "HΞ".
            iIntros (LI HLI). 
            iDestruct ("Hes" with "HΞ") as "Hes". *)
            iApply (monotonic_prot with "[-Hes] Hes").
            iIntros (w) "Hw".
            iIntros (LI HLI).
            specialize (susfill_to_hfilled (Mk_tagidx n) sh (of_val w)) as Hfilled.
            eapply hfilled_inj in Hfilled.
            2:{ instantiate (1 := LI).
                instantiate (1 := No_var).
                destruct (hfilled No_var _ _) => //. }
            rewrite Hfilled.
            iNext.
            iExact "Hw".
          * apply susE_first_instr in Htf0 as [k' Htf0].
            unfold first_instr in H0.
            unfold first_instr in Htf0.
            simpl in H0.
            rewrite Htf0 in H0.
            exfalso.
            destruct H0 as [(? & Habs) | (? & ? & ? & Habs & _)] => //.
      - admit. (* switch case *)
      - iDestruct (ewp_effect_thr with "Hes") as "Hes" => //. 
        iDestruct "Hes" as (f) "[Hf Hes]". 
        remember (Logic.eq_refl (to_eff [AI_prompt ts dccs es])) as Htf'; clear HeqHtf'.
        unfold to_eff in Htf' at 2.
        simpl in Htf'.
        remember Htf as Htf0; clear HeqHtf0.
        unfold to_eff in Htf.
        destruct (merge_values _) => //.
        inversion Htf; subst.
        simpl in Htf'.
        iApply ewp_effect_thr => //.
        iFrame.
        iIntros "Hf".
        iDestruct ("Hes" with "Hf") as "Hes".
        remember HΨ as HΨ'; clear HeqHΨ'.
        destruct HΨ as (_ & _ & HΨ).
        rewrite -HΨ.
        iExact "Hes".
    }
    iApply ewp_unfold.
    rewrite /ewp_pre to_val_None_prompt // to_eff_None_prompt //.
    iIntros (σ ns κ κs nt) "Hσ".
    
    rewrite ewp_unfold /ewp_pre.
    rewrite Htv Htf.
    iMod ("Hes" with "Hσ") as "[%Hred Hes]".
    iModIntro.
    iSplit.
    { iPureIntro.
      destruct Hred as (obs & es' & σ' & efs & Hred).
      destruct σ as [[??]?].
      destruct σ' as [[??]?].
      destruct Hred as (Hred & -> & ->).
      eexists _, _, (_,_,_), _.
      repeat split => //.
      eapply r_label.
      exact Hred.
      instantiate (1 := LH_prompt [] ts dccs (LH_base [] []) []).
      instantiate (1 := 0).
      all: unfold lfilled, lfill => //=.
      rewrite app_nil_r //. }
    iIntros (es2 σ2 Hstep).
    eapply lfilled_prim_step_split_reduce_r in Hstep as Hstep0.
    2:{ instantiate (1 := []).
        instantiate (1 := es).
        instantiate (1 := LH_prompt [] ts dccs (LH_base [] []) []).
        instantiate (1 := 0).
        unfold lfilled, lfill => //=.
        repeat rewrite app_nil_r.
        rewrite eqtype.eq_refl => //. }
    2: exact Hred.
    apply prim_step_obs_efs_empty in Hstep as Hstep1. inversion Hstep1; subst.
    destruct Hstep0 as [(e' & Hstep' & Hfill) | ([lh Htrap] & ->)].
    - iDestruct ("Hes" $! _ _ Hstep') as "Hes".
      iSimpl.
      unfold num_laters_per_step.
      unfold heapG_irisG.
      iMod "Hes".
      repeat iModIntro.
      repeat iMod "Hes".
      iModIntro.
      iDestruct "Hes" as "(Hσ & %f & Hf & He')".
      iFrame.
      iIntros "Hf".
      iDestruct ("He'" with "Hf") as "He'".
      
      unfold lfilled, lfill in Hfill.
      simpl in Hfill.
      rewrite app_nil_r in Hfill.
      rewrite cat_app app_nil_r in Hfill.
      apply b2p in Hfill as ->.
      iApply ("IH" with "[] [$]"). done. 
    - assert (prim_step es σ2 [] [AI_trap] σ2 []).
      { destruct σ2 as [[??]?]. repeat split => //.
        constructor. econstructor. 2: exact Htrap.
        intros ->; by simpl in Htv. } 
      iDestruct ("Hes" $! _ _ H) as "Hes".
      unfold num_laters_per_step, heapG_irisG.
      iMod "Hes".
      repeat iModIntro.
      repeat iMod "Hes".
      iDestruct "Hes" as "(Hσ & %f & Hf & Hes)".
      iDestruct ("Hes" with "Hf") as "Hes".
      iDestruct ewp_value_fupd as "[H _]".
      unfold IntoVal.
      instantiate (2 := trapV) => //.
      iMod ("H" with "Hes") as "Habs".
      iDestruct ("Hntrap" with "Habs") as "Habs" => //.
Admitted.

  Lemma ewp_resume vs addr i ccs dccs LI E Ψ Ψ' Φ Φ' t1s t2s h f:
    const_list vs ->
    stypes f.(f_inst) i = Some (Tf t1s t2s) ->
    length vs = length t1s ->
    map (desugar_continuation_clause (f_inst f)) ccs = map Some dccs ->
    agree_on_uncaptured dccs Ψ Ψ' ->
    hfilled No_var h vs LI ->
    (N.of_nat addr ↦[wcont] Cont_hh (Tf t1s t2s) h ∗
       ¬ Φ trapV ∗ EWP LI @ E <| Ψ |> {{ Φ }} ∗
       ↪[frame] f ∗ clause_resources dccs ∗
(*       (∀ w, Φ' w -∗ (Ξ w ∗ ↪[frame] f)) ∗ *)
       (↪[frame] f -∗ ∀ w, Φ w -∗ EWP [AI_prompt t2s dccs (of_val w)] @ E <| Ψ' |> {{ Φ' }}) ∗
       [∗ list] dcc ∈ dccs, clause_triple E Ψ Φ dcc Ψ' Φ'
        )%I
      ⊢ EWP vs ++ [AI_ref_cont addr ; AI_basic $ BI_resume i ccs] @ E <| Ψ' |> {{ Φ'}}.
  Proof.
    iIntros (Hvs Hi Hlen Hclauses HLI HΨ) "(Hcont & Hntrap & HLI & Hf & Hclres & HΦ & Hclauses)".
(*    iApply (ewp_wand with "[-]"). *)
    iApply ewp_lift_step => //.
    { rewrite to_val_cat_None2 => //. destruct (const_list vs) => //. }
    { rewrite to_eff_cat_None2 => //. destruct (const_list vs) => //. } 
    iIntros (σ ns κ κs nt) "Hσ".
    iApply fupd_frame_l.
    destruct σ as [[ws locs] inst].
    iDestruct "Hσ" as "(Hfuncs & Hconts & Htags & Htables & Hmems & Hglobals & Hframe & Hrest)".
    iDestruct (ghost_map_lookup with "Hframe Hf") as "%Hlook".
    rewrite lookup_insert in Hlook.
    inversion Hlook; subst f. clear Hlook.
    iDestruct (gen_heap_valid with "Hconts Hcont") as "%Hlook".
    rewrite gmap_of_list_lookup Nat2N.id in Hlook.
    rewrite - nth_error_lookup in Hlook.
    assert (reduce ws (Build_frame locs inst)
              (vs ++ [AI_ref_cont addr; AI_basic (BI_resume i ccs)])
              (upd_s_cont ws addr (Cont_dagger (Tf t1s t2s))) (Build_frame locs inst)
              [AI_prompt t2s dccs LI]
           ) as Hred2.
    { eapply r_resume => //. 
      destruct (const_list vs) => //.
      destruct (hfilled No_var h vs LI) => //. } 
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, (_,_,_), [].
      repeat split => //. 
    - iApply fupd_mask_intro; first solve_ndisj.
      iIntros "Hclose !>" (es σ2 HStep). 
      destruct σ2 as [[ ws' locs'] inst'].
      destruct HStep as (H & -> & _).
      edestruct reduce_det.
      exact H. exact Hred2.
      2:{ destruct H0.
          destruct H0 as (? & Habs).
          rewrite -cat_app in Habs.
          rewrite first_instr_const in Habs.
          done.
          destruct (const_list vs) => //.
          destruct H0 as (? & ? & ? & Habs & _).
          rewrite -cat_app first_instr_const in Habs => //.
          destruct (const_list vs) => //. } 
      inversion H0; subst.
      iMod (gen_heap_update with "Hconts Hcont") as "[Hconts Hcont]".
      iMod "Hclose". iModIntro.
      iFrame.
      iSplitL "Hconts".
      { unfold upd_s_cont. simpl.
        unfold replace_nth_cont.
        rewrite - gmap_of_list_insert.
        rewrite insert_take_drop.
        repeat rewrite cat_app.
        rewrite Nat2N.id. done.
        all: rewrite Nat2N.id.
        all: rewrite nth_error_lookup in Hlook.
        all: apply lookup_lt_Some in Hlook.
        all: done. }
      iIntros "Hf".
      iApply ewp_prompt.
      done.
      iFrame.
      iApply ("HΦ" with "Hf").
  Qed. 


  Lemma ewp_newcont addr i E Ψ ft f:
    stypes (f_inst f) i = Some ft ->
    ↪[frame] f 
      ⊢ EWP [AI_ref addr; AI_basic $ BI_contnew i] @ E <| Ψ |> {{ w, (∃ kaddr, ⌜ w = immV [VAL_ref $ VAL_ref_cont kaddr] ⌝ ∗ N.of_nat kaddr ↦[wcont] Cont_hh ft (HH_base [] [AI_ref addr; AI_basic $ BI_call_reference $ Type_explicit ft])) ∗ ↪[frame] f }}.
  Proof.
    iIntros (Hi) "Hf".
    iApply ewp_lift_atomic_step => //=.
    iIntros (σ n κ κs nt) "Hσ".
    destruct σ as [[??]?].
    iDestruct "Hσ" as "(Hfuncs & Hconts & Htags & Htabs & Hmem & Hglobs & Hframe & Hrest)".
    iDestruct (ghost_map_lookup with "Hframe Hf") as "%Hf".
    rewrite lookup_insert in Hf. inversion Hf; subst; clear Hf.
    eassert (prim_step [AI_ref addr; AI_basic (BI_contnew i)] (s, l, i0) [] _ (_,_,_) []).
    { repeat split => //=.
      apply r_contnew.
      exact Hi. done. }
    iMod (gen_heap_alloc with "Hconts") as "(Hconts & Hcont & Htok)"; last first.
    iModIntro.
    iSplit.
    { iPureIntro. repeat eexists. exact H. }
    iIntros "!>" (e2 σ2 HStep).
    destruct H as [H _].
    apply prim_step_obs_efs_empty in HStep as Heq.
    inversion Heq; subst.
    destruct σ2 as [[??]?].
    destruct HStep as [HStep _].
    edestruct reduce_det.
    exact H. exact HStep.
    - inversion H0; subst.
      iModIntro. iFrame.
      iSplitL.
      unfold new_cont.
      iSimpl.
      erewrite <- gmap_of_list_append.
      iExact "Hconts".
      done.
    - unfold first_instr in H0.
      simpl in H0.
      destruct H0 as [(? & ?) | (? & ? & ? & ? & _)] => //.
    - rewrite gmap_of_list_lookup.
      rewrite Nat2N.id.
      apply lookup_ge_None_2.
      lia.
  Qed. 
      
    
      
    

End reasoning_rules.

