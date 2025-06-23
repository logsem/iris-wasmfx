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

  Definition empty_frame :=
    Build_frame [] (Build_instance [] [] [] [] [] []).

  Definition is_empty_frame : frame -> iProp Σ :=
    λ f, ⌜ f = empty_frame ⌝%I.

  Definition clause_triple E Ψ Φ dcc Ψ' Φ': iProp Σ :=
    match dcc with
    | DC_catch taddr ilab =>
        ∀ vs kaddr tf h,
          N.of_nat kaddr ↦[wcont] Cont_hh tf h -∗
            iProt_car (upcl $ Ψ $ SuspendE taddr) (immV vs) (λ w, ∀ LI, ⌜ hfilled No_var h (of_val w) LI ⌝ -∗ ▷ (* no calling continuations in wasm, so adding this later to symbolise that step *) EWP LI UNDER empty_frame @ E <| Ψ |> {{ Φ ; is_empty_frame }}) -∗
            EWP v_to_e_list vs ++ [AI_ref_cont kaddr; AI_basic (BI_br ilab)] UNDER empty_frame @ E <| Ψ' |> {{ Φ' ; is_empty_frame }}
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
          ∃ t1s t2s, N.of_nat addr ↦□[tag] Tf t1s t2s
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

  

  Lemma ewp_suspend vs i E Ψ Φ f Φf:
    iProt_car (upcl (Ψ $ SuspendE i)) (immV vs) Φ ∗ Φf f 
      ⊢ EWP [ AI_suspend_desugared vs i ] UNDER f @ E <| Ψ |> {{ v, Φ v ; Φf }}.
  Proof.
    iIntros "[HΨ Hf]".
    iApply ewp_effect_sus => //.
    iFrame.
    iApply (monotonic_prot with "[Hf] HΨ").
    iIntros (w) "Hw".
    iSimpl.
    rewrite app_nil_r.
    iApply ewp_value'.
    iFrame.
  Qed.

  Lemma tag_valid gm a tf:
    gen_heap_interp gm -∗ a ↦□[tag] tf -∗ ⌜ gm !! a = Some tf ⌝.
  Proof.
    iIntros "Htags Htag".
    iDestruct (gen_heap_valid with "Htags Htag") as "%Htag".
    done.
  Qed. 

  Lemma ewp_suspend_desugar f f' ves vs i x a t1s t2s E Ψ Φ:
    i = Mk_tagident x ->
    f.(f_inst).(inst_tags) !! x = Some a ->
    length vs = length t1s ->
    ves = v_to_e_list vs ->
    N.of_nat a ↦□[tag] Tf t1s t2s ∗
      (N.of_nat a ↦□[tag] Tf t1s t2s -∗ EWP [AI_suspend_desugared vs (Mk_tagidx a)] UNDER f @ E <| Ψ |> {{ v, Φ v ; f' }})
    ⊢ EWP ves ++ [AI_basic (BI_suspend i)] UNDER f @ E <| Ψ |> {{ v, Φ v ; f' }}.
  Proof.
    iIntros (-> Hx Hlen ->) "(Htag & H)".
    iApply ewp_lift_step.
    { rewrite to_val_cat_None2 => //.
      apply v_to_e_is_const_list. }
    { rewrite to_eff_cat_None2 => //.
      apply v_to_e_is_const_list. }
    iIntros (σ) "Hσ".
    iApply fupd_mask_intro; first solve_ndisj.
    iIntros "Hclose".

    iDestruct "Hσ" as "(Hfuncs & Hconts & Htags & Hmems & Htabs & Hglobs & Hrest)".
    iDestruct (tag_valid with "Htags Htag") as "%Htag".
    rewrite gmap_of_list_lookup in Htag.
    rewrite Nat2N.id in Htag.
    iSplit.
    { iPureIntro.
      eexists _,_,(_,_,_),_.
      repeat split => //.
      eapply r_suspend_desugar => //.
      rewrite nth_error_lookup //.
      rewrite nth_error_lookup //. }
    iIntros "!>" (e2 ??? HStep).
    iMod "Hclose".
    iModIntro.

    destruct HStep as (Hred & _).
    edestruct reduce_det.
    exact Hred.
    eapply r_suspend_desugar => //.
    1-2: rewrite nth_error_lookup //.
    destruct H0.
    - destruct H0 as [-> ->].
      destruct f; simpl in H; inversion H; subst. iFrame.
      iApply ("H" with "Htag").
    - destruct H0 as [[? H'] | (? & ? & ? & H' & _)].
      all: rewrite first_instr_const in H' => //.
      all: apply v_to_e_is_const_list.
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

  Lemma reducible_empty_frame es s f:
    iris_resources.reducible es (s, f_locs empty_frame, f_inst empty_frame) -> reducible es (s, f_locs f, f_inst f).
  Proof.
  Admitted.

  Lemma desugar_exception_clauses_empty_frame cs csd f:
    seq.map (desugar_exception_clause (f_inst empty_frame)) cs = seq.map Some csd ->
    seq.map (desugar_exception_clause (f_inst f)) cs = seq.map Some csd.
  Proof.
    generalize dependent csd.
    induction cs => //=.
    destruct a => //=.
    - destruct t => //=.
      destruct i0, csd => //=.
    - destruct t => //=.
      destruct i0, csd => //.
    - destruct csd => //=.
      intros H; inversion H.
      rewrite H2.
      erewrite IHcs => //. 
    - destruct csd => //=.
      intros H; inversion H.
      rewrite H2.
      erewrite IHcs => //.
  Qed.

    Lemma desugar_continuation_clauses_empty_frame cs csd f:
    seq.map (desugar_continuation_clause (f_inst empty_frame)) cs = seq.map Some csd ->
    seq.map (desugar_continuation_clause (f_inst f)) cs = seq.map Some csd.
  Proof.
    generalize dependent csd.
    induction cs => //=.
    destruct a => //=.
    - destruct t => //=.
      destruct i0, csd => //=.
    - destruct t => //.
      destruct i, csd => //. 
  Qed.

  (*
  Lemma ewp_adequacy_trans s f es s' f' esv vs Φ Φf Ψ E:
    reduce_trans (s, f, es) (s', f', esv) ->
    to_val esv = Some vs ->
    state_interp s ∗ EWP es UNDER f @ E <| Ψ |> {{ Φ; Φf }} ⊢ |={E}=> Φ vs ∗ Φf f ∗ state_interp s'.
  Proof.
    intros Hred Hes.
    remember (s, f, es) as x.
    remember (s', f', esv) as y.
    generalize dependent s. generalize dependent f. generalize dependent es.
    generalize dependent s'. generalize dependent f'. generalize dependent esv.
    induction Hred; intros; subst.
    - iIntros "[Hs Hwp]".
      destruct f, f'.
      rewrite ewp_unfold /ewp_pre.
      erewrite val_head_stuck_reduce => //.
      edestruct eff_head_stuck_reduce.
      exact H.
      2:{ admit. (* weird behaviour of switch *) }
      rewrite H0.
      iMod ("Hwp" with "Hs") as "[%Hred Hes]".
      iMod ("Hes" with "[]") as "Hes".
      
  

  Lemma ewp_trans_trap s f es s' f' Φ Φf Ψ E:
    reduce_trans (s, f, es) (s', f', [AI_trap]) ->
    es <> [AI_trap] ->
    (¬ Φ trapV ∗  ∀ (e₂ : iris.expr) (s0 : store_record) (inst0 : instance) 
            (locs0 : list value),
            ⌜prim_step es (s, f_locs f, f_inst f) [] e₂
               (s0, locs0, inst0) []⌝ ={∅}▷=∗
            |={∅,E}=> state_interp s0 ∗
              EWP e₂
              UNDER {| f_locs := locs0; f_inst := inst0 |} @ E <|Ψ|> {{ v,
                        Φ v ; Φf }})%I  ⊢ |={∅}▷=> |={∅, E}=> False.
  Proof.
    intros Hred Hes.
    remember (s, f, es) as x.
    remember (s', f', [AI_trap]) as y.
    induction Hred; subst.
    - iIntros "[HΦ Hes]".
      destruct f, f'.
      iMod ("Hes" with "[]") as "Hes".
      iPureIntro. repeat split => //.
      iModIntro. iNext.
      iMod "Hes".
      iModIntro.
      iMod "Hes" as "[Hs Hewp]".
      rewrite ewp_unfold /ewp_pre.
      simpl.
      iMod "Hewp" as "[Habs Hf]".
      iSpecialize ("HΦ" with "Habs").
      done.
    - inversion Heqy; subst.
      done.
    - 
      erewrite val_head_stuck_reduce; last done.
      edestruct eff_head_stuck_reduce. exact H.
      + rewrite H0.
      erewrite eff_head_stuck_reduce.
    iLöb as "IH" forall (es). *)



  
  
  Lemma reduce_empty_frame s f es s' f' es' :
    reduce s f es s' f' es' ->
    iris_resources.reducible es (s, f_locs empty_frame, f_inst empty_frame) ->
    f = f' /\ reduce s empty_frame es s' empty_frame es' \/
      reduce_trans (s, empty_frame, es) (s, empty_frame, [AI_trap]).
  Proof.
    intros Hred1 Hred2.
    destruct Hred2 as (l & es'' & [[s'' locs] inst] & l' & Hred2 & -> & ->).
    remember {| f_locs := f_locs empty_frame ; f_inst := f_inst empty_frame |} as f0.
    generalize dependent es'.
    induction Hred2.
    inversion H.
    all: intros.
    all: subst.
    all: try by right; constructor; try econstructor; try constructor.
    all: try by destruct i.
    all: try by destruct x.
    all: try by destruct j.
    all: try (destruct i; first by clear Hred1; destruct i).
    1-40: edestruct reduce_det as [Hf [Hres | Hresabs]] ; first exact Hred1.
    all: try by econstructor.
    all: try destruct Hres as [??] ; subst.
    all: try by left; split => //; try constructor; try constructor. 
    all: try destruct Hresabs as [(? & Habs) | (? & ? & ? & Habs & Hes' & Habs' & Hσ)] => //.
    all: subst.
    all: try by destruct ref.
    all: try by rewrite /first_instr /= in Habs;
      specialize (first_instr_const _ [] H0) as He';
      rewrite seq.cats0 /first_instr in He';
      rewrite He' /= // in Habs.
    all: try by rewrite separate1 -cat_app first_instr_const in Habs;
      [done | rewrite /= const_const //].
    all: try by rewrite separate2 -cat_app first_instr_const in Habs;
      [done | repeat rewrite /= const_const //].
    all: try by rewrite first_instr_const in Habs.
    
    all: try by eapply starts_with_lfilled in H2; last (by rewrite first_instr_const);
      rewrite /first_instr /= in Habs;
      rewrite /first_instr in H2;
      rewrite H2 in Habs.
(*    all: try by eapply starts_with_lfilled in H1; last done;
      rewrite /first_instr /= in Habs;
      rewrite /first_instr in H1;
      rewrite H1 in Habs. *)
    all: try by rewrite separate1 -cat_app first_instr_const in Habs;
      [done | rewrite /= H0 //].
    
(*    all: try by right; try econstructor; try econstructor. *)
  (*  13:{ destruct i.
         2: eapply r_resume => //.
         2: apply desugar_continuation_clauses_empty_frame.
         2: done.
         by destruct i. } *)
    all: try by rewrite first_instr_const in Habs; try rewrite v_to_e_is_const_list.
    all: try by eapply starts_with_hfilled in H; last done;
      destruct H as (i' & Hi' & HLI);
      rewrite /first_instr /= in Habs;
      rewrite /first_instr in HLI;
      rewrite HLI in Habs.
    all: try by eapply starts_with_hfilled in H2; last done;
      destruct H2 as (i' & Hi' & HLI);
      rewrite /first_instr /= in Habs;
      rewrite /first_instr in HLI;
      rewrite HLI in Habs.
    all: try (left; split; first done).
    all: try by econstructor.
    - eapply r_try_table => //.
      apply desugar_exception_clauses_empty_frame.
      done. 
    - subst. 
      eapply r_try_table => //. 
    - eapply r_resume => //.
      apply desugar_continuation_clauses_empty_frame.
      done. 
    - subst. 
      eapply r_resume => //.
    - destruct i'. clear Hred1; destruct i => //.
      eapply r_contbind => //. 
    - subst. 
      eapply r_contbind => //.
    - destruct f'0, f, f'.
      edestruct lfilled_reduce.
      + exact H.
      + apply reducible_empty_frame.
        eexists _,_,(_,_,_),_.
        repeat split => //.
      + instantiate (2 := (_,_,_)).
        repeat split => //.
        instantiate (5 := Build_frame f_locs0 f_inst0).      
        exact Hred1.
      + destruct H1 as (es'' & (Hes & _) & Hes'').
        simpl in Hes.
        apply IHHred2 in Hes as H'=> //.
        destruct H' as [[Hf Hred]| Hred].
        * left; split => //.
          eapply r_label.
          exact Hred.
          exact H.
          exact Hes''.
        * right.
          edestruct lfilled_swap as [LI HLI].
          exact H.
          econstructor 3.
          -- eapply r_label_trans.
             exact Hred.
             exact H.
             exact HLI.
          -- eapply lfilled_trap_reduce.
             exact HLI.
      + destruct H1 as (lh0 & Hest & Hσ).
        inversion Hσ; subst.
        edestruct lfilled_trans.
        exact Hest. exact H.
        right.
        eapply lfilled_trap_reduce.
        exact H1.
    - apply reduce_det_local in Hred1.
      2: by apply val_head_stuck_reduce in Hred2.
      destruct Hred1 as (es2' & f2 & -> & -> & Hred).
      left. split => //.
      constructor. exact Hred. 
  Qed.

  Lemma reduce_stays_empty_frame s es s' f' es':
    reduce s empty_frame es s' f' es' -> f' = empty_frame.
  Proof.
    intros H.
    remember empty_frame as f.
    induction H.
    all: try done.
    all: subst. destruct i => //.
    by apply IHreduce.
  Qed. 
    
(*
  Lemma reduce_empty_frame s f es s' f' es' s'' f'' es'':
    reduce s f es s' f' es' ->
    reduce s empty_frame es s'' f'' es'' ->
    es'' = [AI_trap] \/ s' = s'' /\ f'' = empty_frame /\ f = f' /\ es' = es''.
  Proof.
    intros Hred1 Hred2.
    remember empty_frame as f0.
    induction Hred2.
    inversion H.
    all: try by left; reflexivity.
    1-58, 60: right.
    1-58: subst.
    all: edestruct reduce_det as [Hres | Hres]; first exact Hred1.
    all: try by econstructor.
    all: try by inversion Hres; subst.
    all: try destruct Hres as [(? & Habs) | (? & ? & ? & Habs & _)] => //.
    all: try by destruct ref.
    all: try by rewrite /first_instr /= in Habs;
      specialize (first_instr_const _ [] H0) as He';
      rewrite seq.cats0 /first_instr in He';
      rewrite He' /= // in Habs.
    all: try by rewrite separate1 -cat_app first_instr_const in Habs;
      [done | rewrite /= const_const //].
    all: try by rewrite separate2 -cat_app first_instr_const in Habs;
      [done | repeat rewrite /= const_const //].
    all: try by rewrite first_instr_const in Habs.
    
    all: try by eapply starts_with_lfilled in H2; last (by rewrite first_instr_const);
      rewrite /first_instr /= in Habs;
      rewrite /first_instr in H2;
      rewrite H2 in Habs.
    all: try by rewrite separate1 -cat_app first_instr_const in Habs;
      [done | rewrite /= H0 //].
    all: try by destruct x.
    all: try by destruct i.

    all: try (destruct i; first by destruct i).
    { eapply r_call_reference => //. }
    all: try by rewrite first_instr_const in Habs ; try apply v_to_e_is_const_list.
    { eapply r_try_table => //.
      apply desugar_exception_clauses_empty_frame => //. }
    Search "hfilled_first_instr".
    Search first_instr.

(*     all: try by edestruct reduce_det as [Hres | Hres]; first exact Hred1;
      try (by econstructor);
      try (by inversion Hres; subst);
      try destruct ref;
      try by destruct Hres as [(? & Habs) | (? & ? & ? & Habs & _)]. *)
    
    all: induction Hred1.
    all: subst.


  Lemma reduce_empty_frame s es s' f' es' :
    reduce s empty_frame es s' f' es' ->
    f' = empty_frame /\ (es' = [AI_trap] \/ forall f, reduce s f es s' f es').
  Proof.
  Admitted. 
(*    intros Hred.
    remember empty_frame as f.
    induction Hred; subst.
    inversion H; subst.
    all: try by split; first done; right; intros ?; repeat constructor.
    all: try by destruct x.
    all: try by destruct i.
    all: try by split; last by left.
    { destruct i => //.
      destruct i => //.
      split => //.
      right. intros ?.
      eapply r_call_reference => //. }
    by split; first done; right; intros ?; eapply r_invoke_native.
    by split; first done; right; intros ?; eapply r_invoke_host.
    destruct i; first (by destruct i); split; first done; right; intros ?; eapply r_try_table => //.
    
    unfold stab_addr in H.
    simpl in H. 
 *) 

  Lemma reduce_empty_frame_inv s f es s' f' es' :
    reduce s f es s' f' es' ->
    iris_resources.reducible es (s, f_locs empty_frame, f_inst empty_frame) ->
    reduce s empty_frame es s' empty_frame es' \/ reduce s empty_frame es s' empty_frame [AI_trap].
  Proof.
    intros H Hred.
    induction H.
    inversion H.
    all: try by left; constructor; econstructor.
    all: try by left; econstructor.
    
*)

  Lemma ewp_empty_frame es f E Ψ Φ Φf Φf' :
    ¬ Φ trapV ∗ Φf f ∗ EWP es UNDER empty_frame @ E <| Ψ |> {{ Φ ; Φf' }}
      ⊢ EWP es UNDER f @ E <| Ψ |> {{ Φ ; Φf }}.
  Proof.
    iLöb as "IH" forall (es E Ψ Φ f Φf Φf').
    iIntros "(Htrap & Hf & Hes)".
    do 2 rewrite ewp_unfold /ewp_pre.
    destruct (to_val es) eqn:Htv.
    { iMod "Hes" as "[Hv Hf']".
      iFrame. done. }
    destruct (to_eff es) eqn:Htf.
    { destruct e.
      all: iApply (monotonic_prot with "[-Hes] Hes").
      all: iIntros (w) "H".
      3: done.
      all: iNext.
      all: iApply "IH".
      all: iFrame. }
    iIntros (s) "Hs".
    iSpecialize ("Hes" with "Hs").
    iMod "Hes" as "[%Hred Hes]".
    iModIntro.
    iSplit.
    { iPureIntro. apply reducible_empty_frame. done. }
    iIntros (es2 s2 inst2 locs2 Hstep).
    destruct Hstep as [Hstep _].
    apply reduce_empty_frame in Hstep; last done.
    destruct Hstep as [[Hf Hstep] | Hstep].
    - iMod ("Hes" with "[]") as "Hes".
      iPureIntro.
      repeat split => //.
      iModIntro.
      iNext.
      iMod "Hes".
      iModIntro.
      iMod "Hes" as "[Hs2 Hes2]".
      iModIntro.
      iFrame.
      iApply "IH".
      iFrame.
      destruct f.
      simpl in Hf.
      inversion Hf; subst.
      iFrame.
    - iMod ("Hes" with "[]") as "Hes".
      iPureIntro.
      repeat split => //.
  Admitted. 
(*      iModIntro.
      iNext.
      iMod "Hes".
      iModIntro.
      iMod "Hes" as "[Hs2 Hes2]".
      rewrite -> ewp_unfold at 1.
      rewrite /ewp_pre /=.
      iMod "Hes2" as "[Habs Hf']".
      iSpecialize ("Htrap" with "Habs").
      done.
  Qed.  *)
    
    
  

  Lemma ewp_prompt_empty_frame ts dccs es E Ψ Ψ' Φ Φ' :
    agree_on_uncaptured dccs Ψ Ψ' ->
    ( ¬ Φ trapV ∗ EWP es UNDER empty_frame @ E <| Ψ |> {{ Φ ; is_empty_frame }} ∗
      (∀ w, Φ w -∗ EWP [AI_prompt ts dccs (of_val w)] UNDER empty_frame @ E <| Ψ' |> {{ Φ' ; is_empty_frame }}) ∗
      clause_resources dccs ∗
      [∗ list] dcc ∈ dccs, clause_triple E Ψ Φ dcc Ψ' Φ')%I
      ⊢ EWP [AI_prompt ts dccs es] UNDER empty_frame @ E <| Ψ' |> {{ Φ' ; is_empty_frame }}.
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
      iMod "Hes" as "[Hes Hf]".
      iDestruct ("HΦ" with "Hes") as "Hres".
      iModIntro.
      erewrite of_to_val => //.
    }
    destruct (to_eff es) eqn:Htf.
    { destruct e.
      - iDestruct (ewp_effect_sus with "Hes") as "Hes" => //.
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
          iIntros (σ) "Hσ".
          iApply fupd_mask_intro; first solve_ndisj.
          iIntros "Hclose".
          destruct i.
          apply firstx_suspend_lookup in Hfirst as Hfirst'.
          destruct Hfirst' as [k Hk].
          iDestruct (big_sepL_lookup with "Hclauses") as "Hclause".
          exact Hk.
          iDestruct (big_sepL_lookup with "Hclres") as "Hclres".
          exact Hk.
          iDestruct "Hclres" as (t1s t2s) "Hclres".
          iDestruct "Hσ" as "(Hfuncs & Hconts & Htags & Hrest)".
          iDestruct (gen_heap_valid with "Htags Hclres") as %Htag.
          rewrite gmap_of_list_lookup in Htag.
          rewrite -nth_error_lookup in Htag.
          eassert (reduce σ (Build_frame _ _) [AI_prompt ts dccs es] _ _ _).
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
            
          iIntros (es2 σ2 ?? Hstep).
          destruct Hstep as (Hstep & _ & _).
          
          edestruct reduce_det. 
          exact Hstep. exact H.
          inversion H0; subst.
          destruct H1 as [(-> & ->) | Habs].
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
              instantiate (2 := N.of_nat (length (s_conts σ))).
              rewrite -gmap_of_list_append.
              iExact "Hconts". }
            2:{ rewrite gmap_of_list_lookup.
                rewrite Nat2N.id.
                apply lookup_ge_None_2.
                lia. }
            iApply ("Hclause" with "Hcont").
(*            iDestruct ("Hes" with "[$]") as "Hes". *)
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
            unfold first_instr in Habs.
            unfold first_instr in Htf0.
            simpl in Habs.
            rewrite Htf0 in Habs.
            exfalso.
            destruct Habs as [(? & Habs) | (? & ? & ? & Habs & _)] => //.
      - admit. (* switch case *)
      - iDestruct (ewp_effect_thr with "Hes") as "Hes" => //. 
(*        iDestruct "Hes" as (f) "[Hf Hes]".  *)
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
        (* iIntros (?) "Hf". 
        iDestruct ("Hes" with "Hf") as "Hes". *)
        remember HΨ as HΨ'; clear HeqHΨ'.
        destruct HΨ as (_ & _ & HΨ).
        rewrite -HΨ.
        iExact "Hes".
    }
    iApply ewp_unfold.
    rewrite /ewp_pre to_val_None_prompt // to_eff_None_prompt //.
    iIntros (σ) "Hσ".
    
    rewrite ewp_unfold /ewp_pre.
    rewrite Htv Htf.
    iMod ("Hes" with "Hσ") as "[%Hred Hes]".
    iModIntro.
    iSplit.
    { iPureIntro.
      apply reducible_empty_frame.
      destruct Hred as (obs & es' & σ' & efs & Hred).
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
    iIntros (es2 σ2 ?? Hstep).
    eapply lfilled_prim_step_split_reduce_r in Hstep as Hstep0.
    2:{ instantiate (1 := []).
        instantiate (1 := es).
        instantiate (1 := LH_prompt [] ts dccs (LH_base [] []) []).
        instantiate (1 := 0).
        unfold lfilled, lfill => //=.
        repeat rewrite app_nil_r.
        rewrite eqtype.eq_refl => //. }
    2: apply reducible_empty_frame; exact Hred.
    apply prim_step_obs_efs_empty in Hstep as Hstep1. inversion Hstep1; subst.
    destruct Hstep as [Hstep _].
    apply reduce_stays_empty_frame in Hstep as Hf2.
    inversion Hf2; subst locs2 inst2.
    destruct Hstep0 as [(e' & Hstep' & Hfill) | ([lh Htrap] & Hσ)].
    - iDestruct ("Hes" $! _ _ _ _ Hstep') as "Hes".
      iSimpl.
      unfold num_laters_per_step.
      unfold heapG_irisG.
      iMod "Hes".
      repeat iModIntro.
      repeat iMod "Hes".
      iModIntro.
      iDestruct "Hes" as "(Hσ & He')".
      iFrame.
(*      iIntros "Hf".
      iDestruct ("He'" with "Hf") as "He'". *)
      
      unfold lfilled, lfill in Hfill.
      simpl in Hfill.
      rewrite app_nil_r in Hfill.
      rewrite cat_app app_nil_r in Hfill.
      apply b2p in Hfill as ->.
      iApply ("IH" with "[] [-]"). done.
      iFrame. 
    - inversion Hσ; subst σ.
      assert (prim_step es (σ2, f_locs empty_frame, f_inst empty_frame) [] [AI_trap] (σ2, f_locs empty_frame , f_inst empty_frame) []).
      { repeat split => //.
        constructor. econstructor. 2: exact Htrap.
        intros ->; by simpl in Htv. } 
      iDestruct ("Hes" $! _ _ _ _ H) as "Hes".
      iMod "Hes".
      repeat iModIntro.
      repeat iMod "Hes".
      iDestruct "Hes" as "(Hσ & Hes)".
      (* iDestruct ("Hes" with "Hf") as "Hes". *)
      iDestruct ewp_value_fupd as "[H _]".
      unfold IntoVal.
      instantiate (2 := trapV) => //.
      iMod ("H" with "Hes") as "[Habs <-]".
      iDestruct ("Hntrap" with "Habs") as "Habs" => //.
  Admitted. 


   Lemma ewp_prompt ts dccs es E Ψ Ψ' Φ Φ' f Φf :
    agree_on_uncaptured dccs Ψ Ψ' ->
    (¬ Φ trapV ∗ ¬ Φ' trapV ∗ Φf f ∗ EWP es UNDER empty_frame @ E <| Ψ |> {{ Φ ; is_empty_frame }} ∗
      (∀ w, Φ w -∗ EWP [AI_prompt ts dccs (of_val w)] UNDER empty_frame @ E <| Ψ' |> {{ Φ' ; is_empty_frame }}) ∗
      clause_resources dccs ∗
      [∗ list] dcc ∈ dccs, clause_triple E Ψ Φ dcc Ψ' Φ')%I
      ⊢ EWP [AI_prompt ts dccs es] UNDER f @ E <| Ψ' |> {{ Φ' ; Φf }}.
   Proof.
     iIntros (HΨ) "(HΦ & HΦ' & HΦf & Hes & Hnext & Hdccs & Htriples)".
     iApply ewp_empty_frame.
     instantiate (1 := is_empty_frame).
     iFrame.
     iApply ewp_prompt_empty_frame.
     done.
     iFrame.
   Qed. 

  Lemma ewp_resume vs addr i ccs dccs LI E Ψ Ψ' Φ Φ' t1s t2s h f Φf:
    const_list vs ->
    stypes f.(f_inst) i = Some (Tf t1s t2s) ->
    length vs = length t1s ->
    map (desugar_continuation_clause (f_inst f)) ccs = map Some dccs ->
    agree_on_uncaptured dccs Ψ Ψ' ->
    hfilled No_var h vs LI ->

    
    (N.of_nat addr ↦[wcont] Cont_hh (Tf t1s t2s) h ∗
       ¬ Φ trapV ∗ ¬ Φ' trapV ∗ Φf f ∗
       clause_resources dccs ∗
       EWP LI UNDER empty_frame @ E <| Ψ |> {{ Φ ; is_empty_frame }} ∗
       (∀ w, Φ w -∗ EWP [AI_prompt t2s dccs (of_val w)] UNDER empty_frame @ E <| Ψ' |> {{ Φ' ; is_empty_frame }}) ∗
       [∗ list] dcc ∈ dccs, clause_triple E Ψ Φ dcc Ψ' Φ'
        )%I
      ⊢ EWP vs ++ [AI_ref_cont addr ; AI_basic $ BI_resume i ccs] UNDER f @ E <| Ψ' |> {{ Φ'; Φf }}.
  Proof.
    iIntros (Hvs Hi Hlen Hclauses HLI HΨ) "(Hcont & Hntrap & Hntrap' & HΦf & Hclres & HΦ & Hnext & Hclauses)".
(*    iApply (ewp_wand with "[-]"). *)
    iApply ewp_lift_step => //.
    { rewrite to_val_cat_None2 => //. destruct (const_list vs) => //. }
    { rewrite to_eff_cat_None2 => //. destruct (const_list vs) => //. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iDestruct "Hσ" as "(Hfuncs & Hconts & Htags & Htables & Hmems & Hglobals & Hframe & Hrest)".
    iDestruct (gen_heap_valid with "Hconts Hcont") as "%Hlook".
    rewrite gmap_of_list_lookup Nat2N.id in Hlook.
    rewrite - nth_error_lookup in Hlook.
    assert (reduce σ (Build_frame (f_locs f) (f_inst f))
              (vs ++ [AI_ref_cont addr; AI_basic (BI_resume i ccs)])
              (upd_s_cont σ addr (Cont_dagger (Tf t1s t2s))) (Build_frame (f_locs f) (f_inst f))
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
      iIntros "Hclose !>" (es σ2 ?? HStep). 
      destruct HStep as (H & _).
      edestruct reduce_det.
      exact H. exact Hred2.
      inversion H0; subst; clear H0.
      destruct H1 as [[-> ->] | H0].
      2:{ destruct H0.
          destruct H0 as (? & Habs).
          rewrite -cat_app in Habs.
          rewrite first_instr_const in Habs.
          done.
          destruct (const_list vs) => //.
          destruct H0 as (? & ? & ? & Habs & _).
          rewrite -cat_app first_instr_const in Habs => //.
          destruct (const_list vs) => //. } 
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
      iApply ewp_prompt.
      done.
      iFrame.
      destruct f; iFrame.
  Qed.



  
  Lemma ewp_contnew addr i E Ψ ft f Φf:
    stypes (f_inst f) i = Some ft ->
    Φf f ⊢ EWP [AI_ref addr; AI_basic $ BI_contnew i] UNDER f @ E <| Ψ |> {{ w, ∃ kaddr, ⌜ w = immV [VAL_ref $ VAL_ref_cont kaddr] ⌝ ∗ N.of_nat kaddr ↦[wcont] Cont_hh ft (HH_base [] [AI_ref addr; AI_basic $ BI_call_reference $ Type_explicit ft]) ; Φf }}.
  Proof.
    iIntros (Hi) "Hf".
    iApply ewp_lift_atomic_step => //=.
    iIntros (σ) "Hσ".
    iDestruct "Hσ" as "(Hfuncs & Hconts & Htags & Htabs & Hmem & Hglobs & Hframe & Hrest)".
    eassert (prim_step [AI_ref addr; AI_basic (BI_contnew i)] (_, _,_) [] _ (_,_,_) []).
    { repeat split => //=.
      apply r_contnew.
      exact Hi. done. }
    iMod (gen_heap_alloc with "Hconts") as "(Hconts & Hcont & Htok)"; last first.
    iModIntro.
    iSplit.
    { iPureIntro. repeat eexists. exact H. }
    iIntros "!>" (e2 σ2 ?? HStep).
    destruct H as [H _].
    destruct HStep as [HStep _].
    edestruct reduce_det.
    exact H. exact HStep.
    inversion H0; subst; clear H0.
    destruct H1 as [[<- <-] | H0].
    - iModIntro. iFrame.
      iSplitR "Hf".
      unfold new_cont.
      iSimpl.
      erewrite <- gmap_of_list_append.
      iExact "Hconts".
      destruct f; iFrame.
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

