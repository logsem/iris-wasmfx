From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
Require Export iris_rules_structural.
Require Import Coq.Program.Equality.


Set Bullet Behavior "Strict Subproofs".

Section control_operations.

  Fixpoint push_base (lh : lholed) n es' vs_pre es_post :=
    match lh with
    | LH_base vs_pre' es_post' => LH_rec vs_pre' n es' (LH_base vs_pre es_post) es_post'
    | LH_rec vs m es'' lh' es => LH_rec vs m es'' (push_base lh' n es' vs_pre es_post) es
    | LH_prompt bef ts hs sh es => LH_prompt bef ts hs (push_base sh n es' vs_pre es_post) es
    | LH_handler bef hs sh es => LH_handler bef hs (push_base sh n es' vs_pre es_post) es
    end.

  Fixpoint frame_base (lh : lholed) l1 l2 :=
    match lh with
    | LH_base vs es => LH_base (vs ++ l1) (l2 ++ es)
    | LH_rec vs m es' lh' es => LH_rec vs m es' (frame_base lh' l1 l2) es
    | LH_prompt bef ts hs sh aft => LH_prompt bef ts hs (frame_base sh l1 l2) aft
    | LH_handler bef hs sh aft => LH_handler bef hs (frame_base sh l1 l2) aft 
    end.

  Fixpoint pull_base (lh : lholed) :=
    match lh with
    | LH_base vs es => (LH_base [] [], vs, es)
    | LH_rec vs m es' lh' es => let '(lh'',l1,l2) := pull_base lh' in
                               (LH_rec vs m es' lh'' es,l1,l2)
    | LH_prompt bef ts hs sh aft =>
        let '(lh'', l1, l2) := pull_base sh in
        (LH_prompt bef ts hs lh'' aft, l1, l2)
    | LH_handler bef hs sh aft =>
        let '(lh'', l1, l2) := pull_base sh in
        (LH_handler bef hs lh'' aft, l1, l2)
    end.

  Lemma lfilledInd_push i : ∀ lh n es' es LI l1 l2,
      const_list l1 ->
      lfilledInd i lh ([::AI_label n es' (l1 ++ es ++ l2)]) LI ->
      lfilledInd (S i) (push_base lh n es' l1 l2) es LI.
  Proof.
    intros lh.
    generalize dependent i.
    induction lh.
    all: intros ? ? ? ? ? ? ? Hconst Hfill.
    { inversion Hfill;subst.
      constructor. auto. constructor. auto.
    (* apply lfilled_Ind_Equivalent. cbn. rewrite eqseqE app_nil_r. done.  *)}
    { inversion Hfill;subst. simpl. constructor. auto.
      apply IHlh. auto. auto. }
    { inversion Hfill;subst. simpl. constructor. auto.
      apply IHlh. auto. auto. }
    { inversion Hfill;subst. simpl. constructor. auto.
      apply IHlh. auto. auto. }
  Qed.

  Lemma lfilledInd_push_non_zero i lh n es' l1 l2 es LI:
    lfilledInd i (push_base lh n es' l1 l2) es LI -> i <> 0.
  Proof.
    remember (push_base lh n es' l1 l2) as lh'.
    generalize dependent lh'. generalize dependent LI.
    induction lh => //=.
    all: intros LI lh' -> H; inversion H; subst => //.
    all: eapply IHlh => //.
  Qed. 
  
  Lemma lfilledInd_push_inv i : ∀ lh n es' es LI l1 l2,
      const_list l1 ->
      lfilledInd (S i) (push_base lh n es' l1 l2) es LI ->
      lfilledInd i lh ([::AI_label n es' (l1 ++ es ++ l2)]) LI.
  Proof.
    intros lh.
    generalize dependent i.
    induction lh.
    all: intros i ? es' es LI ? ? Hconst Hfill.
    { inversion Hfill;subst. inversion H8; subst.
      constructor => //. }
    all: inversion Hfill; subst.
    { apply lfilledInd_push_non_zero in H8 as Hz.
      destruct i => //.
      constructor => //.
      apply IHlh => //. }
    all: constructor => //.
    all: apply IHlh => //.
  Qed. 

  Lemma lfilledInd_frame i : ∀ lh l1 es l2 LI,
      const_list l1 ->
      lfilledInd i lh (l1 ++ es ++ l2) LI ->
      lfilledInd i (frame_base lh l1 l2) (es) LI.
  Proof.
    intros lh; generalize dependent i.
    induction lh.
    all: intros i ? es ? LI Hconst Hfill.
    { inversion Hfill;subst.
      assert (l ++ (l1 ++ es ++ l2) ++ l0
              = (l ++ l1) ++ es ++ (l2 ++ l0))%SEQ as ->.
      { repeat erewrite app_assoc. auto. }
      constructor. apply const_list_concat;auto. }
    all: inversion Hfill;subst.
    all: simpl.
    all: constructor.
    all: auto.
  Qed.
  Lemma lfilledInd_pull i : ∀ lh es LI,
      lfilledInd i lh (es) LI ->
      let '(lh',l1,l2) := pull_base lh in lfilledInd i lh' (l1++es++l2) LI.
  Proof.
    intros lh; generalize dependent i.
    induction lh.
    all: intros i es LI Hfill.
    { inversion Hfill;subst.
      simpl. apply lfilled_Ind_Equivalent. cbn.
      rewrite app_nil_r. rewrite eqseqE. apply eq_refl. }
    all: inversion Hfill;subst.
    all: simpl.
    all: try apply IHlh in H8.
    2: apply IHlh in H7.
    all: destruct (pull_base lh) as [[lh'' ?] ?].
    all: constructor;auto.
  Qed.

  Lemma lfilled_push_base_swap i lh n es vs1 es2 es' LI :
    lfilled (S i) (push_base lh n es vs1 es2) es' LI ->
    ∃ LI', lfilled i lh es' LI'.
  Proof.
    generalize dependent LI. generalize dependent i.
    induction lh => //=.
    all: intros i LI H; move/lfilledP in H; inversion H; subst => //.
    - inversion H9; subst.
      eexists. apply/lfilledP. constructor => //. 
    - apply lfilledInd_push_non_zero in H9 as Hz.
      destruct i => //.
      move/lfilledP in H9.
      apply IHlh in H9 as [LI' HLI'].
      eexists. apply/lfilledP. constructor => //.
      apply/lfilledP => //.
    - move/lfilledP in H8. apply IHlh in H8 as [LI' HLI'].
      eexists. apply/lfilledP; constructor => //.
      apply/lfilledP => //.
    - move/lfilledP in H9. apply IHlh in H9 as [LI' HLI'].
      eexists. apply/lfilledP; constructor => //.
      apply/lfilledP => //. 
  Qed.

  Lemma lfilled_push_base_swap_inv i lh n es vs1 es2 es' LI :
    const_list vs1 ->
    lfilled i lh es' LI ->
    ∃ LI', lfilled (S i) (push_base lh n es vs1 es2) es' LI'.
  Proof.
    intros Hconst Hfill%lfilled_Ind_Equivalent.
    revert es' i LI Hfill.
    induction lh;intros es' i LI Hfill.
    - simpl. eexists. inversion Hfill;simplify_eq.
      apply lfilled_Ind_Equivalent. constructor;auto. constructor. auto. 
    - inversion Hfill;simplify_eq. simpl.
      eapply IHlh in H8 as [LI' HLI'].
      eexists. apply lfilled_Ind_Equivalent.
      constructor;eauto.
      apply lfilled_Ind_Equivalent;eauto.
    - inversion Hfill; simplify_eq. simpl.
      eapply IHlh in H7 as [LI' HLI'].
      eexists. apply/lfilledP. constructor; eauto.
      apply/lfilledP => //.
    - inversion Hfill; simplify_eq. simpl.
      eapply IHlh in H8 as [LI' HLI'].
      eexists. apply/lfilledP. constructor; eauto.
      apply/lfilledP => //.
  Qed.
  
End control_operations.

Section control_rules.
  
  Context `{!wasmG Σ}.

  (* Structural lemmas for contexts *)

  Lemma ewp_base  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) vs vs' es'' f :
    EWP vs' ++ vs ++ es'' UNDER f @ E <| Ψ |> {{ Φ }}
                                ⊢ EWP vs UNDER f @ E CTX 0; LH_base vs' es'' <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HWP".
    iIntros (LI Hfill%lfilled_Ind_Equivalent).
    inversion Hfill;subst. iFrame.
  Qed.

  Lemma ewp_base_push  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) es l1 l2 i lh f:
    const_list l1 ->
    EWP es UNDER f @ E CTX i; frame_base lh l1 l2 <| Ψ |> {{ Φ }}
                                   ⊢ EWP l1 ++ es ++ l2 UNDER f @ E CTX i; lh <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hconst) "HWP".
    iIntros (LI Hfill%lfilled_Ind_Equivalent).
    apply lfilledInd_frame in Hfill.
    iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
    iPureIntro. by apply lfilled_Ind_Equivalent. auto.
  Qed.
  Lemma ewp_base_pull  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) es i lh f :
    (let '(lh',l1,l2) := pull_base lh in EWP l1 ++ es ++ l2 UNDER f @ E CTX i; lh' <| Ψ |> {{ Φ }})
      ⊢ EWP es UNDER f @ E CTX i; lh <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HWP".
    iIntros (LI Hfill%lfilled_Ind_Equivalent).
    apply lfilledInd_pull in Hfill.
    destruct (pull_base lh) as [[lh' l1] l2].
    iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
    iPureIntro. by apply lfilled_Ind_Equivalent.
  Qed.
  Lemma ewp_label_push  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) es i lh n es' l1 l2 f :
    const_list l1 ->
    EWP es UNDER f @ E CTX S i; push_base lh n es' l1 l2 <| Ψ |> {{ Φ }}
                                    ⊢ EWP [::AI_label n es' (l1 ++ es ++ l2)] UNDER f @ E CTX i; lh <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hconst) "HWP".
    iIntros (LI Hfill%lfilled_Ind_Equivalent).
    apply lfilledInd_push in Hfill.
    iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
    iPureIntro. by apply lfilled_Ind_Equivalent. auto.
  Qed.
  Lemma ewp_label_push_nil  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) es i lh n es' f:
    EWP es UNDER f @ E CTX S i; push_base lh n es' [] [] <| Ψ |> {{ Φ }}
                                    ⊢ EWP [::AI_label n es' es] UNDER f @ E CTX i; lh <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HWP".
    iDestruct (ewp_label_push with "HWP") as "HWP". auto.
    erewrite app_nil_l. erewrite app_nil_r. done.
  Qed.
  Lemma ewp_label_pull  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) es i lh n es' l1 l2 f :
    const_list l1 ->
    EWP [::AI_label n es' (l1 ++ es ++ l2)] UNDER f @ E CTX i; lh <| Ψ |> {{ Φ }}
    ⊢ EWP es UNDER f @ E CTX S i; push_base lh n es' l1 l2 <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hconst) "HWP".
    iIntros (LI Hfill%lfilled_Ind_Equivalent).
    inversion Hfill;subst.
    all: auto.
    all: iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
    all: iPureIntro.
    all: apply lfilledInd_push_inv in Hfill;auto.
    all: apply lfilled_Ind_Equivalent.
    all: auto.
  Qed.
  Lemma ewp_label_pull_nil  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) es i lh n es' f :
    EWP [::AI_label n es' es] UNDER f @ E CTX i; lh <| Ψ |> {{ Φ }}
    ⊢ EWP es UNDER f @ E CTX S i; push_base lh n es' [] [] <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HWP".
    iApply ewp_label_pull;auto.
    simpl. erewrite app_nil_r. auto.
  Qed.
  

  (* Structural lemmas for contexts within a local scope *)

  Lemma ewp_base_push_local  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) es l1 l2 i lh n f f1:
    const_list l1 ->
    EWP es UNDER f1 @ E FRAME n; f CTX i; frame_base lh l1 l2 <| Ψ |> {{ v ; f , Φ v f }}
                                              ⊢ EWP l1 ++ es ++ l2 UNDER f1 @ E FRAME n; f CTX i; lh <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (Hconst) "HWP".
    iIntros (LI Hfill%lfilled_Ind_Equivalent).
    apply lfilledInd_frame in Hfill.
    iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
    iPureIntro. by apply lfilled_Ind_Equivalent. auto.
  Qed.
  Lemma ewp_label_push_local  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) es i lh n es' l1 l2 m f f1 :
    const_list l1 ->
    EWP es UNDER f1 @ E FRAME m; f CTX S i; push_base lh n es' l1 l2 <| Ψ |> {{ v ; f, Φ v f }}
                                               ⊢ EWP [::AI_label n es' (l1 ++ es ++ l2)] UNDER f1 @ E FRAME m; f CTX i; lh <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (Hconst) "HWP".
    iIntros (LI Hfill%lfilled_Ind_Equivalent).
    apply lfilledInd_push in Hfill.
    iDestruct ("HWP" with "[]") as "HWP";[|iFrame].
    iPureIntro. by apply lfilled_Ind_Equivalent. auto.
  Qed.
  Lemma ewp_label_push_nil_local  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) es i lh n es' m f f1:
    EWP es UNDER f1 @ E FRAME m; f CTX S i; push_base lh n es' [] [] <| Ψ |> {{ v ; f , Φ v f }}
                                               ⊢ EWP [::AI_label n es' es] UNDER f1 @ E FRAME m; f CTX i; lh <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros "HWP".
    iDestruct (ewp_label_push_local with "HWP") as "HWP". auto.
    erewrite app_nil_l. erewrite app_nil_r. done.
  Qed.


  (* Control flow rules *)
  Lemma ewp_return  (E: coPset) Ψ (Φ: val -> frame -> iProp Σ) es vs vs0 n f0 i lh f' :
    iris.to_val vs = Some (immV vs0) ->
    length vs = n ->
    lfilled i lh (vs ++ [AI_basic BI_return]) es ->
    ▷ EWP vs UNDER f' @ E <| Ψ |> {{ v ; f , Φ v f }} -∗
                 EWP [AI_local n f0 es] UNDER f' @ E <| Ψ |> {{ v ; f , Φ v f }}%I.
  Proof.
    iIntros (Hval Hlen Hlf) "HΦ".
    iApply ewp_lift_atomic_step => //=.
    { apply lfilled_to_sfill in Hlf as Hsh.
      destruct Hsh as [sh Hsh].
      assert (vs = v_to_e_list vs0).
      { apply of_to_val in Hval. simpl in Hval. auto. }
      assert (vs ++ [AI_basic BI_return] = sfill (SH_base vs0 []) [AI_basic BI_return])%SEQ as Heq;[cbn;rewrite -H;auto|].
      pose proof (sfill_nested sh (SH_base vs0 []) [AI_basic BI_return]) as [vh' Hsh'].
      apply to_val_local_ret_none with (vh:=vh').
      rewrite Hsh Heq Hsh'.
      rewrite -/(iris.of_val (retV vh')).
      apply iris.to_of_val. }
    { apply to_eff_local_none_none.
      eapply to_eff_None_lfilled => //.
      intros H; apply const_list_split in H as [??] => //.
      apply to_eff_cat_None2 => //.
      apply to_val_const_list in Hval => //. } 
    iDestruct (ewp_unfold with "HΦ") as "HΦ".
    rewrite /ewp_pre /=.
    rewrite Hval. 
    iIntros (σ) "Hσ !>".
    assert (const_list vs) as Hcvs; first by apply to_val_const_list in Hval.
    iSplit.
    - iPureIntro. 
      unfold language.reducible, language.prim_step => /=.
      eexists [], vs, (_,_,_), [].
      unfold iris.prim_step => /=.
      repeat split => //.
      constructor. econstructor =>//.
    - iModIntro.
      iIntros (es1 ??? HStep).
      iMod "HΦ" as "HΦ".
      iModIntro.

      destruct HStep as [H _].  iFrame.
      only_one_reduction H.
      { iFrame.
        rewrite Hval.
        iFrame. by destruct f'. } 
        
        all: assert (lfilled 0 (LH_base vs []) [AI_basic (BI_return)]
                             (vs ++ [AI_basic (BI_return)]));
          first (by unfold lfilled, lfill ; rewrite Hcvs ; rewrite app_nil_r);
          eapply lfilled_trans in Hlf as Hlh';eauto;destruct Hlh' as [lh' Hfill'];
          eapply lfilled_implies_starts in Hfill' => //= ;
                                                    unfold first_instr in Hstart ; simpl in Hstart ;
                                                    unfold first_instr in Hfill' ; rewrite Hfill' in Hstart ;
                                                    inversion Hstart.
  Qed.
  
  Lemma ewp_frame_return  (E: coPset) Ψ (Φ: val -> frame -> iProp Σ) vs vs0 n f0 i lh LI f':
    iris.to_val vs = Some (immV vs0) ->
    length vs = n ->
    lfilled i lh (vs ++ [AI_basic BI_return]) LI ->
    ( ▷ EWP vs UNDER f' @ E <| Ψ |> {{ v ; f, Φ v f }}
                   ⊢ EWP LI UNDER f' @ E FRAME n ; f0 <| Ψ |> {{ v ; f , Φ v f }}).
  Proof.
    iIntros (Hval Hlen Hlf) "HΦ".
    by iApply ewp_return.
  Qed.

  Lemma ewp_ctx_frame_return  (E: coPset) Ψ (Φ: iris.val -> frame -> iProp Σ) vs vs0 n f0 i lh f' :
    iris.to_val vs = Some (immV vs0) ->
    length vs = n ->
    ( ▷ EWP vs UNDER f' @ E <| Ψ |> {{ v ; f , Φ v f }}
                   ⊢ EWP vs ++ [AI_basic BI_return] UNDER f' @ E FRAME n ; f0 CTX i ; lh <| Ψ |> {{ v ; f, Φ v f }}).
  Proof.
    iIntros (Hval Hlen) "HΦ".
    iIntros (LI HLI).
    iApply ewp_return;eauto.
  Qed.

  Lemma ewp_br  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) n vs es i LI lh f :
    const_list vs ->
    length vs = n ->
    lfilled i lh (vs ++ [::AI_basic (BI_br i)]) LI ->
    ▷ (EWP (vs ++ es) UNDER f @ E <| Ψ |> {{ v ; f , Φ v f }})
     -∗ EWP [AI_label n es LI] UNDER f @ E <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (Hvs Hlen Hfill) "HΦ".
    iApply ewp_lift_step => //=.
    { eapply to_val_brV_None;eauto. }
    { eapply to_eff_None_label. eapply to_eff_None_lfilled => //.
      intros H; apply const_list_split in H as [??] => //.
      apply to_eff_cat_None2 => //. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplit.
    - iPureIntro. 
      unfold language.reducible, language.prim_step => /=.
      eexists [], (vs ++ es), (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //.
      constructor. econstructor =>//.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.

      destruct HStep as [H _].
      assert (lfilled 0 (LH_base vs []) [AI_basic (BI_br i)]
                      (vs ++ [AI_basic (BI_br i)])).
      { unfold lfilled. rewrite /= Hvs. done. }
      only_one_reduction H.
      by destruct f; iFrame.
      all:
        eapply lfilled_trans in Hfill as Hfill';eauto;destruct Hfill' as [lh' Hfill'];
        eapply lfilled_implies_starts in Hfill' => //= ;
                                                  unfold first_instr in Hstart ; simpl in Hstart ;
                                                  unfold first_instr in Hfill' ; rewrite Hfill' in Hstart ;
                                                  inversion Hstart.    
  Qed.

  Lemma ewp_br_ctx_nested  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) n vs es i j lh lh' lh'' vs' es' f vs0' n0 es0 es0' :
    S i < j ->
    get_layer lh' (lh_depth lh' - (S (S i))) = Some (vs0', n0, es0, (LH_rec vs' n es lh es'), es0') ->
    lh_minus lh' lh'' = Some (LH_rec vs' n es lh es') ->
    const_list vs ->
    length vs = n ->
    
     ▷ (EWP (vs' ++ (vs ++ es) ++ es') UNDER f @ E CTX j - S i ; lh'' <| Ψ |> {{ Φ }})
     -∗ EWP vs ++ [::AI_basic (BI_br i)] UNDER f @ E CTX j ; lh' <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hlt Hlayer Hminus Hvs Hlen) "HΦ".
    iIntros (LI Hfill).

    eapply lfilled_minus with (i:=S i) in Hfill as Hfill';[|eauto..].
    2: { apply lfilled_depth in Hfill as ->. auto. }
    destruct Hfill' as [LI' [Hfill1 Hfill2]].
    apply lfilled_Ind_Equivalent in Hfill1. inversion Hfill1;simplify_eq.
    apply lfilled_swap with (es':=vs' ++ (vs ++ es) ++ es') in Hfill2 as Hfill2'.
    destruct Hfill2' as [LI_r Hfill2'].
    
    assert (iris.to_val LI = None) as Hnone.
    { apply lfilled_Ind_Equivalent in Hfill.
      inversion Hfill;simplify_eq.
      all: eapply val_head_stuck_reduce.
      all: eapply r_label.
      all: try by apply Hfill2'.
      all: try by eauto.
      all: eapply r_label with (lh:=(LH_base vs' es')).
      all: try by apply lfilled_Ind_Equivalent;
        econstructor;auto. 
      all: apply r_simple.
      all: eapply rs_br => //.
      all: apply lfilled_Ind_Equivalent.
      all: eauto.
      Unshelve. all: try by apply (Build_store_record [] [] [] [] [] [] [] ).
      all: apply (Build_frame [] (Build_instance [] [] [] [] [] [])). }
    assert (to_eff LI = None) as Hnone'.
    { eapply to_eff_None_lfilled.
      3: exact Hfill.
      intros H; apply const_list_split in H as [??] => //.
      apply to_eff_cat_None2 => //. }

    iApply ewp_lift_step => //=.
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    eassert (iris.prim_step LI (_,_,_) [] LI_r (_,_,_) []) as Hstep.
    { simpl.
      repeat split => //.
      eapply r_label. 3: apply Hfill2'. 2: eauto.
      eapply r_label with (lh:=(LH_base vs' es')).
      2: { apply lfilled_Ind_Equivalent.
           econstructor;auto. }
      2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
      apply r_simple. eapply rs_br.
      apply Hvs. auto. apply lfilled_Ind_Equivalent. eauto. }
    
    iSplit.
    { 
      iPureIntro. 
      
      eexists [],LI_r,(_,_,_),[]. eauto. }

    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 ??? HStep).
    iMod "Hcls". iModIntro.

    destruct HStep as [HStep _].

    apply lfilled_Ind_Equivalent in H8.
    assert (first_instr LI = Some (AI_basic (BI_br i),(0 + S i) + (j - S i))).
    { eapply starts_with_lfilled. 2:eauto.
      eapply starts_with_lfilled.
      2: { apply lfilled_Ind_Equivalent. constructor;auto.
           apply lfilled_Ind_Equivalent;eauto. }
      rewrite first_instr_const//.
    }
    destruct Hstep as [Hstep _].
    eapply reduce_det in HStep as [-> [Heq | [[i0 Hstart] |
                                                          (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]] ; try congruence.
    2: destruct f; apply Hstep.
    destruct Heq as [-> ->].

    iFrame. 


    iSpecialize ("HΦ" $! _ Hfill2').
    eauto.
  Qed.

  Lemma ewp_block  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) vs es n m t1s t2s f :
    const_list vs ->
    length vs = n ->
    length t1s = n ->
    length t2s = m ->
    
     ▷ (EWP [::AI_label m [::] (vs ++ to_e_list es)] UNDER f @ E <| Ψ |> {{ v ; f , Φ v f }})
     -∗ EWP (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) UNDER f @ E <| Ψ |> {{ v ; f, Φ v f }}.
  Proof.
    iIntros (Hvs Hlen1 Hlen2 Hlen3) "HΦ".
    iApply ewp_lift_step => //=.
    apply to_val_cat_None2;auto.
    apply to_eff_cat_None2 => //. 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //.
      constructor. econstructor => //.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.
      destruct HStep as [H _].
      eapply reduce_det in H as [-> [H | [[i0 Hstart] | 
                                                      (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ)]]];
        last (destruct f; by eapply r_simple, rs_block) ;
        first (inversion H; subst; clear H ; destruct f; by iFrame) ;
        rewrite first_instr_const in Hstart => //=.
  Qed.
  
  Lemma ewp_label_value  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) es m ces v f:
    iris.to_val es = Some (immV v) -> 
     ▷ Φ (immV v) f -∗ EWP [::AI_label m ces es] UNDER f @ E <| Ψ |> {{ v ; f, Φ v f }}.
  Proof.
    iIntros (Hval) "HP".
    iApply ewp_lift_atomic_step => //=.
    { eapply to_val_immV_label_None;eauto. }
    { eapply to_eff_None_label => //.
      destruct (to_eff es) eqn:Habs => //.
      exfalso; by eapply to_val_to_eff. } 
    iIntros (σ) "Hσ !>".
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], es, (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //.
      apply r_simple.  apply rs_label_const.
      eapply to_val_const_list. apply Hval.
    - iIntros "!>" (es1 ??? HStep) "!>".

      destruct HStep as [H _].
      eapply reduce_det in H as [-> [H | [[i0 Hstart] |
                                                      (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ)]]];
        (try by destruct f; apply r_simple ; apply rs_label_const ;
         eapply to_val_const_list ; apply Hval) .
      { (* The only possible case. *)
        destruct H as [-> ->].
        rewrite Hval.
        iFrame. }
        (* All of the rest are impossible reductions since es is a value. *)
      all: try by unfold first_instr in Hstart ; simpl in Hstart ;
          remember (find_first_some (map first_instr_instr es)) as fes ;
          destruct fes => //= ;
                         apply to_val_const_list in Hval ;
                         eapply starts_implies_not_constant in Hval ; first (by exfalso) ;
                         unfold first_instr ; rewrite <- Heqfes.
  Qed.

   Lemma ewp_prompt_value  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) es m ces v f:
    iris.to_val es = Some (immV v) -> 
     ▷ Φ (immV v) f -∗ EWP [::AI_prompt m ces es] UNDER f @ E <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (Hval) "HP".
    iApply ewp_lift_atomic_step => //=.
    { eapply to_val_immV_prompt_None;eauto. }
    { eapply to_eff_None_prompt => //.
      destruct (to_eff es) eqn:Habs => //.
      exfalso; by eapply to_val_to_eff. } 
    iIntros (σ) "Hσ !>".
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], es, (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //.
      apply r_simple.  apply rs_prompt_const.
      eapply to_val_const_list. apply Hval.
    - iIntros "!>" (es1 ??? HStep) "!>".

      destruct HStep as [H _].
      eapply reduce_det in H as [-> [H | [[i0 Hstart] |
                                                      (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ)]]];
        (try by destruct f; apply r_simple ; apply rs_prompt_const ;
         eapply to_val_const_list ; apply Hval) .
      { (* The only possible case. *)
        destruct H as [-> ->].
        rewrite Hval.
        iFrame. }
        (* All of the rest are impossible reductions since es is a value. *)
      all: try by unfold first_instr in Hstart ; simpl in Hstart ;
          remember (find_first_some (map first_instr_instr es)) as fes ;
          destruct fes => //= ;
                         apply to_val_const_list in Hval ;
                         eapply starts_implies_not_constant in Hval ; first (by exfalso) ;
                         unfold first_instr ; rewrite <- Heqfes.
  Qed.

   Lemma ewp_handler_value  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) es ces v f:
    iris.to_val es = Some (immV v) -> 
     ▷ Φ (immV v) f -∗ EWP [::AI_handler ces es] UNDER f @ E <| Ψ |> {{ v ; f, Φ v f }}.
  Proof.
    iIntros (Hval) "HP".
    iApply ewp_lift_atomic_step => //=.
    { eapply to_val_immV_handler_None;eauto. }
    { eapply to_eff_None_handler => //.
      destruct (to_eff es) eqn:Habs => //.
      exfalso; by eapply to_val_to_eff. } 
    iIntros (σ) "Hσ !>".
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], es, (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //.
      apply r_simple.  apply rs_handler_const.
      eapply to_val_const_list. apply Hval.
    - iIntros "!>" (es1 ??? HStep) "!>".

      destruct HStep as [H _].
      eapply reduce_det in H as [-> [H | [[i0 Hstart] |
                                                      (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ)]]];
        (try by destruct f; apply r_simple ; apply rs_handler_const ;
         eapply to_val_const_list ; apply Hval) .
      { (* The only possible case. *)
        destruct H as [-> ->].
        rewrite Hval.
        iFrame. }
        (* All of the rest are impossible reductions since es is a value. *)
      all: try by unfold first_instr in Hstart ; simpl in Hstart ;
          remember (find_first_some (map first_instr_instr es)) as fes ;
          destruct fes => //= ;
                         apply to_val_const_list in Hval ;
                         eapply starts_implies_not_constant in Hval ; first (by exfalso) ;
                         unfold first_instr ; rewrite <- Heqfes.
  Qed.

  Lemma ewp_label_trap  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) es m ctx f0:
    iris.to_val es = Some trapV -> 
     ▷ Φ trapV f0 -∗ EWP [::AI_label m ctx es] UNDER f0 @ E <| Ψ |> {{ v ; f, Φ v f }}.
  Proof.
    iIntros (Hval) "HP".
    iApply ewp_lift_atomic_step => //=.
    { eapply to_val_trapV_label_None;eauto. }
    { eapply to_eff_None_label => //.
      destruct (to_eff es) eqn:Habs => //.
      exfalso; by eapply to_val_to_eff. } 
    iIntros (σ) "Hσ !>".
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], [AI_trap], (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //.
      apply to_val_trap_is_singleton in Hval as ->.
      apply r_simple.  apply rs_label_trap.
    - apply to_val_trap_is_singleton in Hval as ->.

      iIntros "!>" (es1 ??? HStep) "!>".

      destruct HStep as [H _].
      (* Here, the conclusion of reduce_det is not strong enough, so we re-do the proof
       of this subcase by hand, since in this particular case, we can get a 
       stronger result *)
      remember [AI_label m ctx [AI_trap]] as es0.
      remember {| f_locs := f_locs f0 ; f_inst := f_inst f0 |} as f.
      remember {| f_locs := locs2 ; f_inst := inst2 |} as f'.
      rewrite <- app_nil_l in Heqes0.
      induction H ; (try by inversion Heqes0) ;
        try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
      { destruct H ; (try by inversion Heqes0) ;
          try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
        - inversion Heqes0 ; subst. inversion H.
        - inversion Heqes0 ; subst. inversion Heqf' ; subst.
          iFrame.  destruct f0 => //. 
        - inversion Heqes0 ; subst.
          move/lfilledP in H1; inversion H1; subst.
          repeat rewrite catA in H0.
          remember (vs0 ++ vs)%SEQ as l.
          do 2 destruct l => //.
          do 2 destruct vs0 => //.
          all: do 2 destruct bef => //. 
        - rewrite Heqes0 in H0.
          move/lfilledP in H0; inversion H0; subst.
          do 2 destruct vs => //.
          all: do 2 destruct bef => //. } 
      all: try by do 2 destruct vs => //.
      do 2 destruct ves => //. 
      rewrite Heqes0 in H0.
      move/lfilledP in H0; inversion H0; subst.
      + apply app_eq_unit in H2 as [[ -> H2 ] | [_ Habs]].
        apply app_eq_unit in H2 as [[ -> _] | [-> ->]] => //=.
        apply empty_no_reduce in H. by exfalso.
        unfold lfilled, lfill in H1 ; simpl in H1. move/eqP in H1.
        rewrite app_nil_r in H1 ; subst.
        apply IHreduce => //=.
        destruct es, es'0 => //. 
        by apply empty_no_reduce in H.
      + destruct vs; last by destruct vs => //.
        inversion H2; subst.
        move/lfilledP in H7.
        eapply filled_singleton in H7 as (-> & -> & ->) => //.
        by apply AI_trap_irreducible in H.
        intros ->; empty_list_no_reduce.
      + do 2 destruct bef => //.
      + do 2 destruct bef => //. 
  Qed.


    Lemma ewp_prompt_trap  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) es m ctx f0:
    iris.to_val es = Some trapV -> 
     ▷ Φ trapV f0 -∗ EWP [::AI_prompt m ctx es] UNDER f0 @ E <| Ψ |> {{ v ; f, Φ v f }}.
  Proof.
    iIntros (Hval) "HP".
    iApply ewp_lift_atomic_step => //=.
    { eapply to_val_trapV_prompt_None;eauto. }
    { eapply to_eff_None_prompt => //.
      destruct (to_eff es) eqn:Habs => //.
      exfalso; by eapply to_val_to_eff. } 
    iIntros (σ) "Hσ !>".
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], [AI_trap], (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //.
      apply to_val_trap_is_singleton in Hval as ->.
      apply r_simple.  apply rs_prompt_trap.
    - apply to_val_trap_is_singleton in Hval as ->.

      iIntros "!>" (es1 ??? HStep) "!>".

      destruct HStep as [H _].
      (* Here, the conclusion of reduce_det is not strong enough, so we re-do the proof
       of this subcase by hand, since in this particular case, we can get a 
       stronger result *)
      remember [AI_prompt m ctx [AI_trap]] as es0.
      remember {| f_locs := f_locs f0 ; f_inst := f_inst f0 |} as f.
      remember {| f_locs := locs2 ; f_inst := inst2 |} as f'.
      rewrite <- app_nil_l in Heqes0.
      induction H ; (try by inversion Heqes0) ;
        try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
      { destruct H ; (try by inversion Heqes0) ;
          try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
        - inversion Heqes0 ; subst. inversion H.
        - inversion Heqes0 ; subst. inversion Heqf' ; subst.
          iFrame.  destruct f0 => //.
        - iFrame. subst f; by destruct f0. } 
(*        - inversion Heqes0 ; subst.
          move/lfilledP in H1; inversion H1; subst.
          repeat rewrite catA in H0.
          remember (vs0 ++ vs)%SEQ as l.
          do 2 destruct l => //.
          do 2 destruct vs0 => //.
          all: do 2 destruct bef => //. 
        - rewrite Heqes0 in H0.
          move/lfilledP in H0; inversion H0; subst.
          do 2 destruct vs => //.
          all: do 2 destruct bef => //. }  *)
      all: try by do 2 destruct vs => //.
      + inversion Heqes0; subst.
        move/hfilledP in H2; inversion H2; subst.
        all: try by do 2 destruct vs0 => //.
        all: try by do 2 destruct bef => //.
      + inversion Heqes0; subst.
        move/hfilledP in H2; inversion H2; subst.
        all: try by do 2 destruct vs0 => //.
        all: try by do 2 destruct bef => //.
      + do 2 destruct ves => //. 
      + rewrite Heqes0 in H0.
        move/lfilledP in H0; inversion H0; subst.
        * apply app_eq_unit in H2 as [[ -> H2 ] | [_ Habs]].
          apply app_eq_unit in H2 as [[ -> _] | [-> ->]] => //=.
          apply empty_no_reduce in H. by exfalso.
          unfold lfilled, lfill in H1 ; simpl in H1. move/eqP in H1.
          rewrite app_nil_r in H1 ; subst.
          apply IHreduce => //=.
          destruct es, es'0 => //. 
          by apply empty_no_reduce in H.
        * by do 2 destruct vs => //.
        * by do 2 destruct bef => //.
        * destruct bef; last by destruct bef => //.
          inversion H2; subst.
          move/lfilledP in H7.
          eapply filled_singleton in H7 as (-> & -> & ->) => //.
          by apply AI_trap_irreducible in H.
          intros ->; empty_list_no_reduce.
  Qed.


    Lemma ewp_handler_trap  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) es ctx f0:
    iris.to_val es = Some trapV -> 
     ▷ Φ trapV f0 -∗ EWP [::AI_handler ctx es] UNDER f0 @ E <| Ψ |> {{ v ; f, Φ v f }}.
  Proof.
    iIntros (Hval) "HP".
    iApply ewp_lift_atomic_step => //=.
    { eapply to_val_trapV_handler_None;eauto. }
    { eapply to_eff_None_handler => //.
      destruct (to_eff es) eqn:Habs => //.
      exfalso; by eapply to_val_to_eff. } 
    iIntros (σ) "Hσ !>".
    iSplit.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], [AI_trap], (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //.
      apply to_val_trap_is_singleton in Hval as ->.
      apply r_simple.  apply rs_handler_trap.
    - apply to_val_trap_is_singleton in Hval as ->.

      iIntros "!>" (es1 ??? HStep) "!>".

      destruct HStep as [H _].
      (* Here, the conclusion of reduce_det is not strong enough, so we re-do the proof
       of this subcase by hand, since in this particular case, we can get a 
       stronger result *)
      remember [AI_handler ctx [AI_trap]] as es0.
      remember {| f_locs := f_locs f0 ; f_inst := f_inst f0 |} as f.
      remember {| f_locs := locs2 ; f_inst := inst2 |} as f'.
      rewrite <- app_nil_l in Heqes0.
      induction H ; (try by inversion Heqes0) ;
        try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
      { destruct H ; (try by inversion Heqes0) ;
          try by apply app_inj_tail in Heqes0 as [_ Habs] ; inversion Habs.
        - inversion Heqes0 ; subst. inversion H.
        - inversion Heqes0 ; subst. inversion Heqf' ; subst.
          iFrame.  destruct f0 => //.
        - iFrame. by subst; destruct f0. } 
(*        - inversion Heqes0 ; subst.
          move/lfilledP in H1; inversion H1; subst.
          repeat rewrite catA in H0.
          remember (vs0 ++ vs)%SEQ as l.
          do 2 destruct l => //.
          do 2 destruct vs0 => //.
          all: do 2 destruct bef => //. 
        - rewrite Heqes0 in H0.
          move/lfilledP in H0; inversion H0; subst.
          do 2 destruct vs => //.
          all: do 2 destruct bef => //. }  *)
      all: try by do 2 destruct vs => //.
      + inversion Heqes0; subst.
        move/hfilledP in H; inversion H; subst.
        all: try by do 2 destruct vs0 => //.
        all: try by do 2 destruct bef => //.
      + inversion Heqes0; subst.
        move/hfilledP in H; inversion H; subst.
        all: try by do 2 destruct vs0 => //.
        all: try by do 2 destruct bef => //.
      + do 2 destruct ves => //. 
      + rewrite Heqes0 in H0.
        move/lfilledP in H0; inversion H0; subst.
        * apply app_eq_unit in H2 as [[ -> H2 ] | [_ Habs]].
        apply app_eq_unit in H2 as [[ -> _] | [-> ->]] => //=.
        apply empty_no_reduce in H. by exfalso.
        unfold lfilled, lfill in H1 ; simpl in H1. move/eqP in H1.
        rewrite app_nil_r in H1 ; subst.
        apply IHreduce => //=.
        destruct es, es'0 => //. 
        by apply empty_no_reduce in H.
        * by do 2 destruct vs => //.
        * destruct bef; last by destruct bef => //.
          inversion H2; subst.
          move/lfilledP in H7.
          eapply filled_singleton in H7 as (-> & -> & ->) => //.
          by apply AI_trap_irreducible in H.
          intros ->; empty_list_no_reduce.
        * do 2 destruct bef => //. 
  Qed.

  Lemma ewp_val_return  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) vs vs' es' es'' n f :
    const_list vs ->
    to_eff es'' = None ->
    
     (EWP vs' ++ vs ++ es'' UNDER f @ E <| Ψ |> {{ v ; f, Φ v f }})
     -∗ EWP vs UNDER f @ E CTX 1; LH_rec vs' n es' (LH_base [] []) es'' <| Ψ |> {{ v ; f, Φ v f }}.
  Proof.
    iIntros (Hconst Htf) "HWP".
    iLöb as "IH".
    iIntros (LI Hfill%lfilled_Ind_Equivalent).
    inversion Hfill;subst.
    inversion H8;subst.
    assert (vs' ++ [AI_label n es' ([] ++ vs ++ [])] ++ es''
            = ((vs' ++ [AI_label n es' ([] ++ vs ++ [])]) ++ es''))%SEQ as ->.
    { erewrite app_assoc. auto. }
    apply const_list_to_val in Hconst as (v1 & Hv1 & _).
    apply const_list_to_val in H7 as [v2 Hv2].
    eapply to_val_cat_inv in Hv1 as Hvv;[|apply Hv2].
    iApply ewp_seq.
    done.
    (*    iApply (ewp_seq _ _ _ _ _ _ _ _ (λ v f', (⌜v = immV (v2 ++ v1)⌝ ∗ ⌜ f' = f ⌝))%I) => //.  *)
    iSplitR; last first.
(*    iSplitR; first by iIntros "%H". *)
    iSplitR "HWP".
    - iApply ewp_val_app; first by apply Hv2.
      iSplit; last first.
(*      iSplit; first by iIntros "!> %". *)
      iApply (ewp_label_value with "[]") => //=; first by erewrite app_nil_r; apply Hv1 .
      by instantiate (1 := λ v g, (⌜ v = immV (v2 ++ v1) ⌝ ∗ ⌜ g = f ⌝)%I).
      by iIntros "!>" (?) "[% _ ]".
    - iIntros (w f0) "[-> ->]".
      erewrite iris.of_to_val => //.
      rewrite app_assoc.
      by iApply "HWP".
    - by iIntros (?) "[% _]".
  Qed.

  Lemma ewp_block_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) (i : nat) (lh : lholed) vs t1s t2s es n m f0:
    const_list vs ->
    length vs = n ->
    length t1s = n ->
    length t2s = m ->
    ▷ (EWP [::AI_label m [::] (vs ++ to_e_list es)] UNDER f0 @ E CTX i; lh <| Ψ |> {{ Φ }})
     -∗ EWP (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) UNDER f0 @ E CTX i; lh <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hconst Hn Hn' Hm) "HWP".
    iIntros (LI Hfill).
    destruct (iris.to_val LI) eqn:Hcontr.
    { apply lfilled_to_val in Hfill as [v' Hv];eauto.
      assert (iris.to_val [AI_basic (BI_block (Tf t1s t2s) es)] = None) as Hnone;auto.
      apply (to_val_cat_None2 vs) in Hnone;auto.
      rewrite Hv in Hnone. done. }
    assert (to_eff LI = None) as Htf.
    { eapply to_eff_None_lfilled => //.
      intros H; apply const_list_split in H as [??] => //.
      apply to_eff_cat_None2 => //. } 
    unfold ewp_wasm_ctx.
    iApply ewp_unfold.
    repeat rewrite /ewp_pre/=.
    rewrite Hcontr Htf.
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplit.
    { iPureIntro. 
      apply lfilled_swap with (es':=[::AI_label m [::] (vs ++ to_e_list es)]) in Hfill as Hfill'.
      destruct Hfill' as [LI' Hfill'].
      eexists [],_,(_,_,_),[]. simpl.

      unfold iris.prim_step => /=.
      repeat split => //.
      eapply r_label. apply r_simple. eapply rs_block.
      apply Hconst. apply Hn. apply Hn'. apply Hm. eauto. eauto. }

    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls" (es1 ??? HStep) "!>!>!>".
    iMod "Hcls". iModIntro.

    apply lfilled_swap with (es':=[::AI_label m [::] (vs ++ to_e_list es)]) in Hfill as Hfill'.
    destruct Hfill' as [LI' Hfill'].
    destruct HStep as [H _].

    assert (lfilled 0 (LH_base vs []) [AI_basic (BI_block (Tf t1s t2s) es)]
                    (vs ++ [AI_basic (BI_block (Tf t1s t2s) es)])).
    { unfold lfilled, lfill ; rewrite Hconst ; done. }
    eapply reduce_det in H as [-> [H | [[i0 Hstart] |
                                                    (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
      [..|eapply r_label;[destruct f0; apply r_simple;eapply rs_block|eauto..];eauto].
    all: try (by 
               eapply lfilled_trans in Hfill as Hfill'';eauto;destruct Hfill'' as [lh' Hfill''];
              eapply lfilled_implies_starts in Hfill'' ; (try done) ;
              rewrite Hfill'' in Hstart ; inversion Hstart => //=).
    destruct H as [-> ->].
    iFrame.
    by iSpecialize ("HWP" with "[%]").
  Qed.
  
  Lemma ewp_block_local_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) (i : nat) (lh : lholed) vs t1s t2s es n m n1 f1 f0 :
    const_list vs ->
    length vs = n ->
    length t1s = n ->
    length t2s = m ->
    
     ▷ (EWP [::AI_label m [::] (vs ++ to_e_list es)] UNDER f0 @ E FRAME n1; f1 CTX i; lh <| Ψ |> {{ v ; f , Φ v f }})
     -∗ EWP (vs ++ [::AI_basic (BI_block (Tf t1s t2s) es)]) UNDER f0 @ E FRAME n1; f1 CTX i; lh <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (Hconst Hn Hn' Hm) "HWP".
    iIntros (LI Hfill).
    destruct (iris.to_val LI) eqn:Hcontr.
    { apply lfilled_to_val in Hfill as [v' Hv];eauto.
      assert (iris.to_val [AI_basic (BI_block (Tf t1s t2s) es)] = None) as Hnone;auto.
      apply (to_val_cat_None2 vs) in Hnone;auto.
      rewrite Hv in Hnone. done. }
    unfold ewp_wasm_ctx.
    iApply ewp_unfold.
    repeat rewrite /ewp_pre/=.
    destruct (iris.to_val [AI_local n1 f1 LI]) eqn:Htv.
    { unfold iris.to_val in Htv ; simpl in Htv.
      unfold iris.to_val in Hcontr.
      destruct (merge_values _) => //. destruct e => //. }
    assert (to_eff [AI_local n1 f1 LI] = None) as Htf.
    { apply to_eff_local_none_none.
      eapply to_eff_None_lfilled => //.
      intros H; apply const_list_split in H as [??] => //.
      apply to_eff_cat_None2 => //. }
    rewrite Htf.
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplit.
    { iPureIntro. 
      apply lfilled_swap with (es':=[::AI_label m [::] (vs ++ to_e_list es)]) in Hfill as Hfill'.
      destruct Hfill' as [LI' Hfill'].
      eexists [],_,(_,_,_),[]. simpl.

      unfold iris.prim_step => /=.
      repeat split => //. eapply r_local.
      eapply r_label. apply r_simple. eapply rs_block.
      apply Hconst. apply Hn. apply Hn'. apply Hm. eauto. eauto. }

    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls" (es1 ??? HStep) "!>!>!>".
    iMod "Hcls". iModIntro.

    apply lfilled_swap with (es':=[::AI_label m [::] (vs ++ to_e_list es)]) in Hfill as Hfill'.
    destruct Hfill' as [LI' Hfill'].
    destruct HStep as [H _].
    assert (first_instr [AI_local n1 f1 LI] = Some (AI_basic (BI_block (Tf t1s t2s) es),S (0 + i))) as HH.
    { apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill].
      apply first_instr_const;auto. }
    eapply reduce_det in H as [Hf [H | [[i0 Hstart] |
                                        (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ)  ]]];
      try congruence;
      try by assert (lfilled 0 (LH_base vs []) [AI_basic (BI_block (Tf t1s t2s) es)]
                             (vs ++ [AI_basic (BI_block (Tf t1s t2s) es)])) ;
      first (unfold lfilled, lfill ; rewrite Hconst ; by rewrite app_nil_r) ;
      destruct (@lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfill''] ;
      eapply lfilled_implies_starts in Hfill'' ; (try done) ;
      rewrite /first_instr in Hfill'';
      rewrite /first_instr /= Hfill'' in Hstart ; inversion Hstart => //=.
    2: { eapply r_local. eapply r_label. apply r_simple. eapply rs_block;eauto. all: eauto. }
    inversion Hf; subst. destruct H as [<- <-].
    all: iFrame.
    destruct f0; 
    by iSpecialize ("HWP" with "[%]").
  Qed.

  Lemma ewp_br_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) n vs es i lh vs' es' f0:
    const_list vs ->
    length vs = n ->

     ▷ (EWP (vs' ++ vs ++ es ++ es') UNDER f0 @ E <| Ψ |> {{ Φ }})
     -∗ EWP vs ++ [::AI_basic (BI_br i)] UNDER f0 @ E CTX S i; LH_rec vs' n es lh es' <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hvs Hlen) "HΦ".
    iIntros (LI Hfill).
    assert (iris.to_val LI = None) as Hnone.
    { apply lfilled_Ind_Equivalent in Hfill.
      inversion Hfill;simplify_eq.
      apply to_val_cat_None2;auto.
      apply to_val_cat_None1.
      eapply to_val_brV_None;[|eauto|];auto.
      apply lfilled_Ind_Equivalent. eauto. }
    assert (to_eff LI = None) as Htf.
    { eapply to_eff_None_lfilled => //.
      intros H; apply const_list_split in H as [??] => //.
      apply to_eff_cat_None2 => //. } 

    iApply ewp_lift_step => //=.
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplit.
    { apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;subst.
      iPureIntro. 
      apply lfilled_Ind_Equivalent in H8 as Hfill'.
      apply lfilled_swap with (es':=vs ++ es) in Hfill' as Hfill''.
      destruct Hfill'' as [LI' Hfill''].    
      eexists [],_,(_,_,_),[].

      unfold iris.prim_step => /=.
      repeat split => //.   
      eapply r_label with (lh:=(LH_base vs' es')).
      2: { erewrite cons_middle. apply lfilled_Ind_Equivalent.
           econstructor;auto. }
      2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
      apply r_simple. eapply rs_br.
      apply Hvs. auto. eauto. }

    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 ??? HStep).
    iMod "Hcls". iModIntro.

    apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;subst.
    apply lfilled_Ind_Equivalent in H8 as Hfill'.
    apply lfilled_swap with (es':=vs ++ es) in Hfill' as Hfill''.
    destruct Hfill'' as [LI' Hfill''].    
    destruct HStep as [H _].

    assert (lfilled 0 (LH_base vs []) [AI_basic (BI_br i)]
                    (vs ++ [AI_basic (BI_br i)])) ;
      first (unfold lfilled, lfill ; rewrite Hvs ; by rewrite app_nil_r).
    eapply reduce_det in H as [-> [H | [[i0 Hstart] |
                                                    (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]].
    4: { eapply r_label with (lh:=(LH_base vs' es')).
         2: { apply lfilled_Ind_Equivalent.
              econstructor;auto. }
         2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
         destruct f0; apply r_simple. eapply rs_br. apply Hvs. all:eauto. }
    all: try by apply lfilled_Ind_Equivalent in Hfill ;
      eapply lfilled_trans in Hfill as Hfilln;eauto;destruct Hfilln as [lh' Hfilln];
      eapply lfilled_implies_starts in Hfilln ; (try done) ;
      rewrite Hfilln in Hstart ; inversion Hstart => //=. 
    inversion H; subst; clear H.
    
    iFrame. 

    destruct f0.
    by erewrite !app_assoc.
  Qed.

  Lemma ewp_br_local_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) n vs es i lh vs' es' f0 n1 f1 :
    const_list vs ->
    length vs = n ->
    
     ▷ (EWP (vs' ++ vs ++ es ++ es') UNDER f0 @ E FRAME n1; f1 <| Ψ |> {{ v ; f , Φ v f }})
     -∗ EWP vs ++ [::AI_basic (BI_br i)] UNDER f0 @ E FRAME n1; f1 CTX S i; LH_rec vs' n es lh es' <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (Hvs Hlen) "HΦ".
    iIntros (LI Hfill).
    assert (iris.to_val LI = None) as Hnone.
    { apply lfilled_Ind_Equivalent in Hfill.
      inversion Hfill;simplify_eq.
      apply to_val_cat_None2;auto.
      apply to_val_cat_None1.
      eapply to_val_brV_None;[|eauto|];auto.
      apply lfilled_Ind_Equivalent. eauto. }
    assert (to_eff LI = None) as Htf.
    { eapply to_eff_None_lfilled => //.
      intros H; apply const_list_split in H as [??] => //.
      apply to_eff_cat_None2 => //. } 
    iApply ewp_lift_step => //=.
    apply to_val_local_none_none => //.
    apply to_eff_local_none_none => //. 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplit.
    { apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;subst.
      iPureIntro. 
      apply lfilled_Ind_Equivalent in H8 as Hfill'.
      apply lfilled_swap with (es':=vs ++ es) in Hfill' as Hfill''.
      destruct Hfill'' as [LI' Hfill''].    
      eexists [],_,(_,_,_),[].

      unfold iris.prim_step => /=.
      repeat split => //. eapply r_local.
      eapply r_label with (lh:=(LH_base vs' es')).
      2: { erewrite cons_middle. apply lfilled_Ind_Equivalent.
           econstructor;auto. }
      2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
      apply r_simple. eapply rs_br.
      apply Hvs. auto. eauto. }

    iApply fupd_mask_intro;[solve_ndisj|].
    iIntros "Hcls !>" (es1 ??? HStep).
    iMod "Hcls". iModIntro.

    apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;subst.
    apply lfilled_Ind_Equivalent in H8 as Hfill'.
    apply lfilled_swap with (es':=vs ++ es) in Hfill' as Hfill''.
    destruct Hfill'' as [LI' Hfill''].    
    destruct HStep as [H _].
    assert (first_instr [AI_local n1 f1 (vs' ++ [AI_label (length vs) es LI0] ++ es')] 
            = Some (AI_basic (BI_br i),S (0 + S i))) as HH.
    { apply lfilled_Ind_Equivalent in Hfill.
      apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill].
      apply first_instr_const;auto. }
    
    eapply reduce_det in H as [Hf [H | [[i0 Hstart] |
                                                    (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
      try congruence;
      try by apply lfilled_Ind_Equivalent in Hfill ;
      assert (lfilled 0 (LH_base vs []) [AI_basic (BI_br i)]
                      (vs ++ [AI_basic (BI_br i)])) ;
      first (unfold lfilled, lfill ; rewrite Hvs ; by rewrite app_nil_r) ;
      destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
      eapply lfilled_implies_starts in Hfilln ; (try done) ;
      rewrite Hfilln in Hstart ; inversion Hstart => //=. 
    2: { eapply r_local.
         eapply r_label with (lh:=(LH_base vs' es')).
         2: { apply lfilled_Ind_Equivalent.
              econstructor;auto. }
         2: { apply lfilled_Ind_Equivalent. econstructor;auto. }
         apply r_simple. eapply rs_br. apply Hvs. all:eauto. }
    inversion Hf; subst. destruct H as [<- <-].

    iFrame. 
    destruct f0; 
    by erewrite !app_assoc.
  Qed.

  Lemma ewp_loop_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) vs es n m t1s t2s i lh f0: 
    const_list vs ->
    length vs = n ->
    length t1s = n ->
    length t2s = m ->
    
     ▷ (EWP [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)] UNDER f0 @ E CTX i; lh <| Ψ |> {{ Φ }})
     -∗ EWP vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)] UNDER f0 @ E CTX i; lh <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hvs Hn Hn' Hm) "HP".
    iIntros (LI Hfill).
    eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
    iApply ewp_lift_step => //=.
    { destruct (iris.to_val LI) eqn:Hcontr;auto.
      apply lfilled_to_val in Hfill;eauto.
      destruct Hfill as [? Hfill].
      assert (iris.to_val [AI_basic (BI_loop (Tf t1s t2s) es)] = None) as HH;auto.
      apply (to_val_cat_None2 vs) in HH;auto. rewrite Hfill in HH. done. }
    { eapply to_eff_None_lfilled => //.
      intros H; apply const_list_split in H as [??] => //.
      apply to_eff_cat_None2 => //. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplitR.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], LI', (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //.
      eapply r_label. apply r_simple;eauto. eapply rs_loop;eauto.
      eauto. eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.

      destruct HStep as [H _].
      destruct f0. 
      eapply reduce_det in H as [-> [H | [[i0 Hstart] |
                                                      (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ)]]].
      4: { eapply r_label. apply r_simple;eauto. eapply rs_loop;eauto.
           eauto. eauto. }
      all: try by assert (lfilled 0 (LH_base vs []) [AI_basic (BI_loop (Tf t1s t2s) es)]
                                  (vs ++ [AI_basic (BI_loop (Tf t1s t2s) es)])) ;
        first (unfold lfilled, lfill ; rewrite Hvs ; by rewrite app_nil_r) ;
        eapply lfilled_trans in Hfill as [lh' Hfill''] ;eauto;
        eapply lfilled_implies_starts in Hfill'' ; (try done) ;
        rewrite Hfill'' in Hstart ; inversion Hstart => //=.
      inversion H; subst; clear H.
      
      iFrame. 
      by iSpecialize ("HP" with "[%]").
  Qed.

  Lemma ewp_loop_local_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) vs es n m t1s t2s i lh f0 n1 f1 :
    const_list vs ->
    length vs = n ->
    length t1s = n ->
    length t2s = m ->
    
     ▷ (EWP [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)] UNDER f0 @ E FRAME n1; f1 CTX i; lh <| Ψ |> {{ v ; f, Φ v f }})
     -∗ EWP vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)] UNDER f0 @ E FRAME n1; f1 CTX i; lh <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (Hvs Hn Hn' Hm) "HP".
    iIntros (LI Hfill).
    eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
    iApply ewp_lift_step => //=.
    { apply to_val_local_none_none.
      eapply to_val_None_lfilled;eauto.
      apply to_val_cat_None2;auto. }
    { apply to_eff_local_none_none.
      eapply to_eff_None_lfilled => //.
      intros H; apply const_list_split in H as [??] => //.
      apply to_eff_cat_None2 => //. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplitR.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //. eapply r_local.
      eapply r_label. apply r_simple;eauto. eapply rs_loop;eauto.
      eauto. eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.

      destruct HStep as [H _].

      assert (first_instr [AI_local n1 f1 LI] = Some (AI_basic (BI_loop (Tf t1s t2s) es),S (0 + i))) as HH.
      { apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill].
        apply first_instr_const. auto. }
      eapply reduce_det in H as [Hf [H | [[i0 Hstart] |
                                                      (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
        try congruence;
        try by assert (lfilled 0 (LH_base vs []) [AI_basic (BI_loop (Tf t1s t2s) es)]
                               (vs ++ [AI_basic (BI_loop (Tf t1s t2s) es)])) ;
        first (unfold lfilled, lfill ; rewrite Hvs ; by rewrite app_nil_r) ;
        destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfill''] ;
        eapply lfilled_implies_starts in Hfill'' ; (try done) ;
        rewrite Hfill'' in Hstart ; inversion Hstart => //=.
      2: { eapply r_local. eapply r_label. apply r_simple;eauto. eapply rs_loop;eauto.
           eauto. eauto. }
      inversion Hf; subst. destruct H as [<- <-].

      iFrame. 
      destruct f0; 
      by iSpecialize ("HP" with "[%]").
  Qed.

  Lemma ewp_loop  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) vs es n m t1s t2s f :
    const_list vs ->
    length vs = n ->
    length t1s = n ->
    length t2s = m ->
    
     ▷ (EWP [::AI_label n [::AI_basic (BI_loop (Tf t1s t2s) es)] (vs ++ to_e_list es)] UNDER f @ E <| Ψ |> {{ w ; f , Φ w f }})
     -∗ EWP vs ++ [::AI_basic (BI_loop (Tf t1s t2s) es)] UNDER f @ E <| Ψ |> {{ w ; f , Φ w f }}.
  Proof.
    iIntros (Hvs Hn Hn' Hm) "HP".
    iApply ewp_wasm_empty_ctx. iApply ewp_loop_ctx => //.
    iNext.
    
    by iApply ewp_wasm_empty_ctx. 
  Qed.

  Lemma ewp_if_true_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) n tf e1s e2s i lh f0  :
    n ≠ Wasm_int.int_zero i32m ->
    ▷ (EWP [::AI_basic (BI_block tf e1s)] UNDER f0 @ E CTX i; lh <| Ψ |> {{ Φ }})
     -∗ EWP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] UNDER f0 @ E CTX i; lh <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hn) "HP".
    iIntros (LI Hfill).
    eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
    iApply ewp_lift_step => //=.
    { destruct (iris.to_val LI) eqn:Hcontr;auto.
      apply lfilled_to_val in Hfill;eauto.
      destruct Hfill as [? Hfill]. simpl in Hfill. done. }
    { eapply to_eff_None_lfilled => //.
      done.
      done. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplitR.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], LI', (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //.
      eapply r_label. apply r_simple;eauto. eapply rs_if_true;eauto.
      eauto. eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.

      destruct HStep as [H _].
      rename tf into tf'.
      
      only_one_reduction H.
      { 
        iFrame.
        destruct f0; 
        by iApply "HP". } 
      all: by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                                [AI_basic (BI_if tf' e1s e2s)]
                                [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf' e1s e2s)]) ;
          first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
          eapply lfilled_trans in Hfill as [lh' Hfilln] ; eauto;
          eapply lfilled_implies_starts in Hfilln => //= ;
                                                     rewrite Hfilln in Hstart ; inversion Hstart.
  Qed.

  Lemma ewp_if_true_local_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) n tf e1s e2s i lh f0 n1 f1 :
    n ≠ Wasm_int.int_zero i32m ->
    
     ▷ (EWP [::AI_basic (BI_block tf e1s)] UNDER f0 @ E FRAME n1; f1 CTX i; lh <| Ψ |> {{ v ; f , Φ v f }})
     -∗ EWP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] UNDER f0 @ E FRAME n1; f1 CTX i; lh <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (Hn) "HP".
    iIntros (LI Hfill).
    eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
    iApply ewp_lift_step => //=.
    { apply to_val_local_none_none.
      eapply to_val_None_lfilled;eauto.
      rewrite separate1.
      apply to_val_cat_None2;auto. }
    { apply to_eff_local_none_none.
      eapply to_eff_None_lfilled => //.
      all: done. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplitR.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //. eapply r_local.
      eapply r_label. apply r_simple;eauto. eapply rs_if_true;eauto.
      eauto. eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.

      destruct HStep as [H _].

      assert (first_instr [AI_local n1 f1 LI] = Some (AI_basic (BI_if tf e1s e2s),S (0 + i))) as HH.
      { apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill]. auto. }
      eapply reduce_det in H as [Hf [H | [[i0 Hstart] |
                                                      (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ)  ]]];
        try congruence;
        try by assert (lfilled 0 (LH_base vs []) [AI_basic (BI_loop (Tf t1s t2s) es)]
                               (vs ++ [AI_basic (BI_loop (Tf t1s t2s) es)])) ;
        first (unfold lfilled, lfill ; rewrite Hvs ; by rewrite app_nil_r) ;
        destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfill''] ;
        eapply lfilled_implies_starts in Hfill'' ; (try done) ;
        rewrite Hfill'' in Hstart ; inversion Hstart => //=.
      2: { eapply r_local. eapply r_label. apply r_simple;eauto. eapply rs_if_true;eauto.
           eauto. eauto. }
      inversion Hf; subst; destruct H as [<- <-].

      iFrame. 
      destruct f0;
      by iSpecialize ("HP" with "[%]").
  Qed.

  Lemma ewp_if_true  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) c tf e1s e2s f :
    c ≠ Wasm_int.int_zero i32m ->
    ▷ (EWP [::AI_basic (BI_block tf e1s)] UNDER f @ E <| Ψ |> {{ w ; f , Φ w f }})
     -∗ EWP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_if tf e1s e2s)] UNDER f @ E <| Ψ |> {{ w ; f , Φ w f }}.
  Proof.
    iIntros (?) "HP".
    iApply ewp_wasm_empty_ctx. iApply ewp_if_true_ctx;eauto.
    iNext.
    destruct f;
    by iApply ewp_wasm_empty_ctx.
  Qed.
  
  Lemma ewp_if_false_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) n tf e1s e2s i lh f0 :
    n = Wasm_int.int_zero i32m ->
    ▷ (EWP [::AI_basic (BI_block tf e2s)] UNDER f0 @ E CTX i; lh <| Ψ |> {{ Φ }})
     -∗ EWP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] UNDER f0 @ E CTX i; lh <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hn) "HP".
    iIntros (LI Hfill).
    eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
    iApply ewp_lift_step => //=.
    { destruct (iris.to_val LI) eqn:Hcontr;auto.
      apply lfilled_to_val in Hfill;eauto.
      destruct Hfill as [? Hfill]. simpl in Hfill. done. }
    { eapply to_eff_None_lfilled => //.
      all: done. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplitR.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], LI', (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //.
      eapply r_label. apply r_simple;eauto. eapply rs_if_false;eauto.
      eauto. eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.

      destruct HStep as [H _].
      destruct f0.
      eapply reduce_det in H as [-> [H | [[i0 Hstart] |
                                                      (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]].
      4: { eapply r_label. apply r_simple;eauto. eapply rs_if_false;eauto.
           eauto. eauto. }
      all: try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                                  [AI_basic (BI_if tf e1s e2s)]
                                  [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf e1s e2s)]) ;
        first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
        eapply lfilled_trans in Hfill as [lh' Hfilln] ; eauto;
        eapply lfilled_implies_starts in Hfilln => //= ;
                                                   rewrite Hfilln in Hstart ; inversion Hstart.
      inversion H; subst; clear H.
      
      iFrame.

      by iApply "HP".
  Qed.

  Lemma ewp_if_false_local_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) n tf e1s e2s i lh f0 n1 f1 :
    n = Wasm_int.int_zero i32m ->

     ▷ (EWP [::AI_basic (BI_block tf e2s)] UNDER f0 @ E FRAME n1; f1 CTX i; lh <| Ψ |> {{ v ; f , Φ v f }})
     -∗ EWP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_if tf e1s e2s)] UNDER f0 @ E FRAME n1; f1 CTX i; lh <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (Hn) "HP".
    iIntros (LI Hfill).
    eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
    iApply ewp_lift_step => //=.
    { apply to_val_local_none_none.
      eapply to_val_None_lfilled;eauto.
      rewrite separate1.
      apply to_val_cat_None2;auto. }
    { apply to_eff_local_none_none => //.
      eapply to_eff_None_lfilled => //.
      all: done. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplitR.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //. eapply r_local.
      eapply r_label. apply r_simple;eauto. eapply rs_if_false;eauto.
      eauto. eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.

      destruct HStep as [H _].
      assert (first_instr [AI_local n1 f1 LI] = Some (AI_basic (BI_if tf e1s e2s),S (0 + i))) as HH.
      { apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill];auto. }
      
      eapply reduce_det in H as [Hf [H | [[i0 Hstart] |
                                                      (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
        try congruence;
        try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                               [AI_basic (BI_if tf e1s e2s)]
                               [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf e1s e2s)]) ;
        first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
        destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
        eapply lfilled_implies_starts in Hfilln => //= ;
                                                   rewrite Hfilln in Hstart ; inversion Hstart.
      2: { eapply r_local. eapply r_label. apply r_simple;eauto. eapply rs_if_false;eauto.
           eauto. eauto. }
      inversion Hf; subst; destruct H as [<- <-].

      iFrame.
      by destruct f0; 
      by iApply "HP".
  Qed.

  Lemma ewp_if_false  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) c tf e1s e2s f:
    c = Wasm_int.int_zero i32m ->

     ▷ (EWP [::AI_basic (BI_block tf e2s)] UNDER f @ E <| Ψ |> {{ w ; f , Φ w f }})
     -∗ EWP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_if tf e1s e2s)] UNDER f @ E <| Ψ |> {{ w ; f , Φ w f }}.
  Proof.
    iIntros (?) "HP".
    iApply ewp_wasm_empty_ctx. iApply ewp_if_false_ctx;eauto.
    iNext. iApply ewp_wasm_empty_ctx.
    by iApply "HP".
  Qed.

  Lemma ewp_br_if_true_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) n i j lh f0 :
    n ≠ Wasm_int.int_zero i32m ->
    ▷ (EWP [::AI_basic (BI_br i)] UNDER f0 @ E CTX j; lh <| Ψ |> {{ Φ }})
     -∗ EWP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] UNDER f0 @ E CTX j; lh <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hn) "HP".
    iIntros (LI Hfill).
    eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
    iApply ewp_lift_step => //=.
    { destruct (iris.to_val LI) eqn:Hcontr;auto.
      apply lfilled_to_val in Hfill;eauto.
      destruct Hfill as [? Hfill]. simpl in Hfill. done. }
    { eapply to_eff_None_lfilled => //.
      all: done. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplitR.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], LI', (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //.
      eapply r_label. apply r_simple;eauto. eapply rs_br_if_true;eauto.
      eauto. eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.

      destruct HStep as [H _].
      
      only_one_reduction H ;
        try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                               [AI_basic (BI_br_if i)]
                               [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_br_if i)]) ;
        first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
        eapply lfilled_trans in Hfill as [lh' Hfilln] ; eauto;
        eapply lfilled_implies_starts in Hfilln => //= ;
                                                   rewrite Hfilln in Hstart ; inversion Hstart.
      iFrame.
      destruct f0; by iApply "HP".
  Qed.

  Lemma ewp_br_if_true_local_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) n i j lh f0 n1 f1  :
    n ≠ Wasm_int.int_zero i32m ->
    ▷ (EWP [::AI_basic (BI_br i)] UNDER f0 @ E FRAME n1; f1 CTX j; lh <| Ψ |> {{ v ; f , Φ v f }})
     -∗ EWP [::AI_basic (BI_const (VAL_int32 n)); AI_basic (BI_br_if i)] UNDER f0 @ E FRAME n1; f1 CTX j; lh <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (Hn) "HP".
    iIntros (LI Hfill).
    eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
    iApply ewp_lift_step => //=.
    { apply to_val_local_none_none.
      eapply to_val_None_lfilled;eauto.
      rewrite separate1.
      apply to_val_cat_None2;auto. }
    { apply to_eff_local_none_none.
      eapply to_eff_None_lfilled => //.
      all: done. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplitR.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //. eapply r_local.
      eapply r_label. apply r_simple;eauto. eapply rs_br_if_true;eauto.
      eauto. eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.

      destruct HStep as [H _].
      assert (first_instr [AI_local n1 f1 LI] = Some (AI_basic (BI_br_if i),S (0 + j))) as HH.
      { apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill];auto. }
      
      eapply reduce_det in H as [Hf [H | [[i0 Hstart] | 
                                                      (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
        try congruence;
        try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                               [AI_basic (BI_if tf e1s e2s)]
                               [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf e1s e2s)]) ;
        first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
        destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
        eapply lfilled_implies_starts in Hfilln => //= ;
                                                   rewrite Hfilln in Hstart ; inversion Hstart.
      2: { eapply r_local. eapply r_label. apply r_simple;eauto. eapply rs_br_if_true;eauto.
           eauto. eauto. }
      inversion Hf; subst; destruct H as [<- <-].
      
      iFrame.
      destruct f0; 
      by iApply "HP".
  Qed.

  Lemma ewp_br_if_true  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) c i f :
    c ≠ Wasm_int.int_zero i32m ->
    
     ▷ (EWP [::AI_basic (BI_br i)] UNDER f @ E <| Ψ |> {{ w ; f , Φ w f }})
     -∗ EWP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_if i)] UNDER f @ E <| Ψ |> {{ w ; f , Φ w f }}.
  Proof.
    iIntros (?) "HP".
    iApply ewp_wasm_empty_ctx. iApply ewp_br_if_true_ctx;eauto.
    iNext. iApply ewp_wasm_empty_ctx.
    destruct f; by iApply "HP".
  Qed.

  (* The following expression reduces to a value reguardless of context, 
   and thus does not need a context aware version *)
  Lemma ewp_br_if_false  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) c i f:
    c = Wasm_int.int_zero i32m ->
    
     ▷ Φ (immV []) f 
     -∗ EWP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_if i)] UNDER f @ E <| Ψ |> {{ w ; f , Φ w f }}.
  Proof.
    iIntros (Hn) "HΦ".
    iApply ewp_lift_atomic_step => //=.
    iIntros (σ) "Hσ !>".
    iSplit.
    - iPureIntro.
      unfold reducible, language.prim_step => /=.
      eexists [], [], (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //.
      apply r_simple.
      subst.
      by apply rs_br_if_false.
    - iIntros "!>" (es ??? HStep) "!>".

      destruct HStep as [H _].
      only_one_reduction H. iFrame. by destruct f.
  Qed.


  Lemma ewp_br_table_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) iss c i j k lh f0 :
    ssrnat.leq (S (Wasm_int.nat_of_uint i32m c)) (length iss) ->
    List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
    ▷ (EWP [::AI_basic (BI_br j)] UNDER f0 @ E CTX k; lh <| Ψ |> {{ Φ }})
     -∗ EWP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] UNDER f0 @ E CTX k; lh <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hiss Hj) "HP".
    iIntros (LI Hfill).
    eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
    iApply ewp_lift_step => //=.
    { destruct (iris.to_val LI) eqn:Hcontr;auto.
      apply lfilled_to_val in Hfill;eauto.
      destruct Hfill as [? Hfill]. simpl in Hfill. done. }
    { eapply to_eff_None_lfilled => //=.
      all: done. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplitR.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], LI', (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //.
      eapply r_label. apply r_simple;eauto. apply rs_br_table;eauto.
      eauto. eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.

      destruct HStep as [H _].

      only_one_reduction H ;
        try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 c))] [])
                               [AI_basic (BI_br_table iss i)]
                               [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_br_table iss i)]) ;
        first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
        eapply lfilled_trans in Hfill as [lh' Hfilln] ; eauto;
        eapply lfilled_implies_starts in Hfilln => //= ;
                                                   rewrite Hfilln in Hstart ; inversion Hstart.
      iFrame.
      destruct f0; by iApply "HP".
  Qed.
  
  Lemma ewp_br_table_local_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) iss c i j k lh f0 n1 f1 :
    ssrnat.leq (S (Wasm_int.nat_of_uint i32m c)) (length iss) ->
    List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
    ▷ (EWP [::AI_basic (BI_br j)] UNDER f0 @ E FRAME n1; f1 CTX k; lh <| Ψ |> {{ v ; f, Φ v f }})
     -∗ EWP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] UNDER f0 @ E FRAME n1; f1 CTX k; lh <| Ψ |> {{ v ; f, Φ v f }}.
  Proof.
    iIntros (Hiss Hj) "HP".
    iIntros (LI Hfill).
    eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
    iApply ewp_lift_step => //=.
    { apply to_val_local_none_none.
      eapply to_val_None_lfilled;eauto.
      rewrite separate1.
      apply to_val_cat_None2;auto. }
    { apply to_eff_local_none_none.
      eapply to_eff_None_lfilled => //.
      all: done. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplitR.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //. eapply r_local.
      eapply r_label. apply r_simple;eauto. apply rs_br_table;eauto.
      eauto. eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.

      destruct HStep as [H _].
      assert (first_instr [AI_local n1 f1 LI] = Some (AI_basic (BI_br_table iss i),S (0 + k))) as HH.
      { apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill];auto. }
      
      eapply reduce_det in H as [Hf [H | [[i0 Hstart] |
                                                      (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
        try congruence;
        try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                               [AI_basic (BI_if tf e1s e2s)]
                               [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf e1s e2s)]) ;
        first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
        destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
        eapply lfilled_implies_starts in Hfilln => //= ;
                                                   rewrite Hfilln in Hstart ; inversion Hstart.
      2: { eapply r_local. eapply r_label. apply r_simple;eauto. eapply rs_br_table;eauto.
           eauto. eauto. }
      inversion Hf; subst; destruct H as [<- <-].

      iFrame.
      destruct f0; 
      by iApply "HP".
  Qed.
  
  Lemma ewp_br_table  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) iss c i j f  :
    List.nth_error iss (Wasm_int.nat_of_uint i32m c) = Some j ->
    ▷ (EWP [::AI_basic (BI_br j)] UNDER f @ E <| Ψ |> {{ w ; f, Φ w f }})
     -∗ EWP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] UNDER f @ E <| Ψ |> {{ w ; f , Φ w f }}.
  Proof.
    iIntros (?) "HP".
    iApply ewp_wasm_empty_ctx. iApply ewp_br_table_ctx => //.
    { rewrite nth_error_lookup in H. apply lookup_lt_Some in H. by lias. }
    iNext. iApply ewp_wasm_empty_ctx. done.
  Qed.

  Lemma ewp_br_table_length_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) iss c i j lh f0 :
    ssrnat.leq (length iss) (Wasm_int.nat_of_uint i32m c) ->
     ▷ (EWP [::AI_basic (BI_br i)] UNDER f0 @ E CTX j; lh <| Ψ |> {{ Φ }})
     -∗ EWP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] UNDER f0 @ E CTX j; lh <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hiss) "HP".
    iIntros (LI Hfill).
    eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
    iApply ewp_lift_step => //=.
    { destruct (iris.to_val LI) eqn:Hcontr;auto.
      apply lfilled_to_val in Hfill;eauto.
      destruct Hfill as [? Hfill]. simpl in Hfill. done. }
    { eapply to_eff_None_lfilled => //.
      all: done. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplitR.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], LI', (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //.
      eapply r_label. apply r_simple;eauto. apply rs_br_table_length;eauto.
      eauto. eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.

      destruct HStep as [H _].
      
      only_one_reduction H ;
        try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 c))] [])
                               [AI_basic (BI_br_table iss i)]
                               [AI_basic (BI_const (VAL_int32 c)) ; AI_basic (BI_br_table iss i)]) ;
        first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
        eapply lfilled_trans in Hfill as [lh' Hfilln] ; eauto;
        eapply lfilled_implies_starts in Hfilln => //= ;
                                                   rewrite Hfilln in Hstart ; inversion Hstart.
      iFrame.
      destruct f0;
      by iApply "HP" .
  Qed.
  Lemma ewp_br_table_length_local_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) iss c i j lh f0 n1 f1  :
    ssrnat.leq (length iss) (Wasm_int.nat_of_uint i32m c) ->
     ▷ (EWP [::AI_basic (BI_br i)] UNDER f0 @ E FRAME n1; f1 CTX j; lh <| Ψ |> {{ v ; f, Φ v f }})
     -∗ EWP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] UNDER f0 @ E FRAME n1; f1 CTX j; lh <| Ψ |> {{ v ; f , Φ v f }}.
  Proof.
    iIntros (Hiss) "HP".
    iIntros (LI Hfill).
    eapply lfilled_swap in Hfill as Hfill'; destruct Hfill' as [LI' Hfill'].
    iApply ewp_lift_step => //=.
    { apply to_val_local_none_none.
      eapply to_val_None_lfilled;eauto.
      rewrite separate1.
      apply to_val_cat_None2;auto. }
    { apply to_eff_local_none_none.
      eapply to_eff_None_lfilled => //.
      all: done. } 
    iIntros (σ) "Hσ".
    iApply fupd_frame_l.
    iSplitR.
    - iPureIntro.
      unfold language.reducible, language.prim_step => /=.
      eexists [], _, (_,_,_), [].

      unfold iris.prim_step => /=.
      repeat split => //. eapply r_local.
      eapply r_label. apply r_simple;eauto. apply rs_br_table_length;eauto.
      eauto. eauto.
    - iApply fupd_mask_intro;[solve_ndisj|].
      iIntros "Hcls !>" (es1 ??? HStep).
      iMod "Hcls". iModIntro.

      destruct HStep as [H _].
      assert (first_instr [AI_local n1 f1 LI] = Some (AI_basic (BI_br_table iss i),S (0 + j))) as HH.
      { apply first_instr_local. eapply starts_with_lfilled;[|apply Hfill];auto. }
      
      eapply reduce_det in H as [Hf [H | [[i0 Hstart] |
                                                      (i1 & i2 & i3 & Hstart & Hstart1 & Hstart2 & Hσ) ]]];
        try congruence;
        try by assert (lfilled 0 (LH_base [AI_basic (BI_const (VAL_int32 n))] [])
                               [AI_basic (BI_if tf e1s e2s)]
                               [AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_if tf e1s e2s)]) ;
        first (by unfold lfilled, lfill => //= ; rewrite app_nil_r) ;
        destruct (lfilled_trans _ _ _ _ _ _ _ H Hfill) as [lh' Hfilln] ;
        eapply lfilled_implies_starts in Hfilln => //= ;
                                                   rewrite Hfilln in Hstart ; inversion Hstart.
      2: { eapply r_local. eapply r_label. apply r_simple;eauto. eapply rs_br_table_length;eauto.
           eauto. eauto. }
      inversion Hf; subst; destruct H as [<- <-].
      
      iFrame.
      destruct f0; 
      by iApply "HP".
  Qed.
  
  Lemma ewp_br_table_length  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) iss c i f :
    length iss <= Wasm_int.nat_of_uint i32m c ->
     ▷ (EWP [::AI_basic (BI_br i)] UNDER f @ E <| Ψ |> {{ w ; f , Φ w f }})
     -∗ EWP [::AI_basic (BI_const (VAL_int32 c)); AI_basic (BI_br_table iss i)] UNDER f @ E <| Ψ |> {{ w ; f , Φ w f }}.
  Proof.
    iIntros (?) "HP".
    iApply ewp_wasm_empty_ctx. iApply ewp_br_table_length_ctx ;eauto; first by lias.
    iNext. iApply ewp_wasm_empty_ctx. done. 
  Qed.

  (* --------------------------------------------- *)
  (* Special sifting rules about break and return *)

  Lemma ewp_br_ctx_shift  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) vs i lh n es vs1 es2 l n1 l0 l1 f :
    const_list vs ->
    length vs = n1 ->
    EWP vs ++ [AI_basic (BI_br i)] UNDER f @ E CTX S i; LH_rec l n1 l0 lh l1 <| Ψ |> {{ Φ }} -∗
                                                         EWP vs ++ [AI_basic (BI_br (S i))] UNDER f @ E CTX S (S i); LH_rec l n1 l0 (push_base lh n es vs1 es2) l1 <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hlen Hconst) "Hwp".
    iIntros (LI Hfill%lfilled_Ind_Equivalent).
    inversion Hfill;subst;simplify_eq.
    apply lfilled_Ind_Equivalent in H8 as Hfill'.
    apply lfilled_push_base_swap in Hfill' as Hfill''.
    destruct Hfill'' as [LI' Hfill''].
    apply lfilled_swap with (es' := vs ++ [AI_basic (BI_br i)]) in Hfill'' as Hfilli.
    destruct Hfilli as [LIi Hfilli].
    iSpecialize ("Hwp" with "[]").
    { iPureIntro. apply lfilled_Ind_Equivalent. constructor;auto.
      apply lfilled_Ind_Equivalent. eauto. }

    assert (iris.to_val (l ++ [AI_label (length vs) l0 LIi] ++ l1) = None).
    { apply to_val_cat_None2;auto.
      apply to_val_cat_None1.
      eapply to_val_brV_None;[|eauto|];eauto.
    }
    assert (iris.to_val (l ++ [AI_label (length vs) l0 LI0] ++ l1) = None).
    { apply to_val_cat_None2;auto.
      apply to_val_cat_None1.
      eapply to_val_brV_None;[|eauto|];eauto.
    }

    assert (to_eff (l ++ [AI_label (length vs) l0 LIi] ++ l1) = None).
    { apply to_eff_cat_None2 => //.
      apply to_eff_cat_None1 => //.
      apply to_eff_None_label => //.
      eapply to_eff_None_lfilled => //.
      let H := fresh "H" in intros H; apply const_list_split in H as [??] => //.
      apply to_eff_cat_None2 => //. }

    assert (to_eff (l ++ [AI_label (length vs) l0 LI0] ++ l1) = None).
    { apply to_eff_cat_None2 => //.
      apply to_eff_cat_None1 => //.
      apply to_eff_None_label => //.
      eapply to_eff_None_lfilled .
      3: done.
      intros Hc; apply const_list_split in Hc as [??] => //.
      apply to_eff_cat_None2 => //. } 
      

    iApply ewp_unfold. iDestruct (ewp_unfold with "Hwp") as "Hwp".
    rewrite /ewp_pre /= H H0 H1 H2.

    iIntros (σ1) "Hσ".
    iSpecialize ("Hwp" $! σ1 with "Hσ").

    eassert (reduce _
                   {| f_locs := _; f_inst := _ |}
                   (l ++ [AI_label (length vs) l0 LI0] ++ l1) _
                   {| f_locs := _; f_inst := _ |}
                   (l ++ (vs ++ l0) ++ l1)).
    { eapply r_label with (k:=0) (lh:=LH_base l l1);cycle 1.
      apply lfilled_Ind_Equivalent. by constructor.
      apply lfilled_Ind_Equivalent. by constructor.
      eapply r_simple, rs_br;eauto. }

    eassert (reduce _
                   {| f_locs := _; f_inst := _ |}
                   (l ++ [AI_label (length vs) l0 LIi] ++ l1) _ 
                   {| f_locs := _; f_inst := _ |}
                   (l ++ (vs ++ l0) ++ l1)).
    { eapply r_label with (k:=0) (lh:=LH_base l l1);cycle 1.
      apply lfilled_Ind_Equivalent. by constructor.
      apply lfilled_Ind_Equivalent. by constructor.
      eapply r_simple, rs_br;eauto. }
    
    iMod "Hwp". iModIntro.
    iDestruct "Hwp" as "[_ Hwp]".
    iSplitR.
    { unfold reducible. iPureIntro.
      eexists [],_,(_,_,_),[]. simpl. repeat split;eauto. }
    iIntros (e2 ??? Hprim).

    destruct Hprim as [Hprim _].
    apply lfilled_Ind_Equivalent in Hfill.
    assert (first_instr (l ++ [AI_label (length vs) l0 LI0] ++ l1) = Some (AI_basic (BI_br (S i)),0 + S (S i))) as Hfirst0.
    { eapply starts_with_lfilled;cycle 1.
      apply lfilled_Ind_Equivalent. constructor;eauto.
      apply first_instr_const;auto. }
    eapply reduce_det in Hprim as [? [? | [[? ?]|[? [? [? [? [? [? ?]]]]]]]]];[..|apply H3].
    inversion H5; subst; destruct H6 as [<- <-].
    all: try by (rewrite separate1 Hfirst0 in H6; inversion H6).
    inversion H5;simplify_eq.
    iSpecialize ("Hwp" $! _ _ _ _ with "[]").
    { iPureIntro. unfold prim_step. repeat split;eauto. }
    iFrame.
  Qed.

  Lemma ewp_br_ctx_shift_inv  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) vs i lh n es vs1 es2 l n1 l0 l1 f  :
    const_list vs ->
    const_list vs1 ->
    length vs = n1 ->
    EWP vs ++ [AI_basic (BI_br (S i))] UNDER f @ E CTX S (S i); LH_rec l n1 l0 (push_base lh n es vs1 es2) l1 <| Ψ |> {{ Φ }} -∗
                                                                 EWP vs ++ [AI_basic (BI_br i)] UNDER f @ E CTX (S i); LH_rec l n1 l0 lh l1 <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hconst Hconst' Hlen) "Hwp".
    iIntros (LI Hfill).
    apply lfilled_push_base_swap_inv with (n:=n) (es:=es) (vs1:=vs1) (es2:=es2) in Hfill as Hfill';auto.
    destruct Hfill' as [LI' Hfill'].
    simpl in Hfill'.
    
    apply lfilled_swap with (es' := vs ++ [AI_basic (BI_br (S i))]) in Hfill' as Hfilli.
    destruct Hfilli as [LIi Hfilli].
    apply lfilled_Ind_Equivalent in Hfilli.
    inversion Hfilli. simplify_eq.
    apply lfilled_Ind_Equivalent in H8.
    apply lfilled_Ind_Equivalent in Hfilli.

    assert (const_list l) as Hconst''.
    { apply lfilled_Ind_Equivalent in Hfill. inversion Hfill;auto. }
    
    iSpecialize ("Hwp" with "[]").
    { iPureIntro. eauto. }  
    
    assert (iris.to_val (l ++ [AI_label (length vs) l0 LI0] ++ l1) = None).
    { apply to_val_cat_None2;auto.
      apply to_val_cat_None1.
      eapply to_val_brV_None;[|eauto|];eauto.
    }
    assert (iris.to_val LI = None).
    { apply lfilled_Ind_Equivalent in Hfill.
      inversion Hfill;simplify_eq.
      apply to_val_cat_None2;auto.
      apply to_val_cat_None1.
      eapply to_val_brV_None. apply Hconst.
      auto. apply lfilled_Ind_Equivalent. eauto. }

    assert (to_eff LI = None).
    { eapply to_eff_None_lfilled => //.
      intros Hc; apply const_list_split in Hc as [??] => //.
      apply to_eff_cat_None2 => //. }

    assert (to_eff (l ++ [AI_label (length vs) l0 LI0] ++ l1) = None).
    { apply to_eff_cat_None2 => //.
      apply to_eff_cat_None1 => //.
      apply to_eff_None_label => //.
      eapply to_eff_None_lfilled.
      3: done.
      intros Hc; apply const_list_split in Hc as [??] => //.
      apply to_eff_cat_None2 => //. } 
      

    iApply ewp_unfold. iDestruct (ewp_unfold with "Hwp") as "Hwp".
    rewrite /ewp_pre /= H H0 H1 H2.

    apply lfilled_Ind_Equivalent in Hfill.
    inversion Hfill;simplify_eq.

    iIntros (σ1 ) "Hσ".
    iSpecialize ("Hwp" $! σ1  with "Hσ").


    eassert (reduce  _
                   {| f_locs := _; f_inst := _ |}
                   (l ++ [AI_label (length vs) l0 LI0] ++ l1) _
                   {| f_locs := _; f_inst := _ |}
                   (l ++ (vs ++ l0) ++ l1)).
    { eapply r_label with (k:=0) (lh:=LH_base l l1);cycle 1.
      apply lfilled_Ind_Equivalent. by constructor.
      apply lfilled_Ind_Equivalent. by constructor.
      eapply r_simple, rs_br;eauto. }

    eassert (reduce _ 
                   {| f_locs := _; f_inst := _ |}
                   (l ++ [AI_label (length vs) l0 LI1] ++ l1) _ 
                   {| f_locs := _; f_inst := _ |}
                   (l ++ (vs ++ l0) ++ l1)).
    { eapply r_label with (k:=0) (lh:=LH_base l l1);cycle 1.
      apply lfilled_Ind_Equivalent. by constructor.
      apply lfilled_Ind_Equivalent. by constructor.
      eapply r_simple, rs_br;eauto. apply lfilled_Ind_Equivalent. eauto. }
    
    iMod "Hwp". iModIntro.
    iDestruct "Hwp" as "[_ Hwp]".
    iSplitR.
    { unfold reducible. iPureIntro.
      eexists [],_,(_,_,_),[]. simpl. repeat split;eauto. }
    iIntros (e2 ??? Hprim).

    destruct Hprim as [Hprim _].
    apply lfilled_Ind_Equivalent in Hfill.
    assert (first_instr (l ++ [AI_label (length vs) l0 LI1] ++ l1) = Some (AI_basic (BI_br i),0 + S i)) as Hfirst0.
    { eapply starts_with_lfilled;cycle 1.
      apply lfilled_Ind_Equivalent. constructor;eauto.
      apply first_instr_const;auto. }
    eapply reduce_det in Hprim as [? [? | [[? ?]|[? [? [? [? [? [? ?]]]]] ]]]];[..|apply H4].
    all: try by (rewrite separate1 Hfirst0 in H6; inversion H6).
    inversion H5; subst; destruct H6 as [<- <-].
    iSpecialize ("Hwp" $! _ _ _ _ with "[]").
    { iPureIntro. unfold prim_step. repeat split;eauto. }
    iFrame.
  Qed.

  Lemma ewp_ret_shift  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) n f0 i lh j lh' LI LI' vs f :
    const_list vs ->
    length vs = n ->
    lfilled i lh (vs ++ [AI_basic BI_return]) LI ->
    lfilled j lh' (vs ++ [AI_basic BI_return]) LI' ->
    EWP [AI_local n f LI] UNDER f @ E <| Ψ |> {{ Φ }} -∗
                                EWP [AI_local n f0 LI'] UNDER f @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hconst Hlen Hfill1 Hfill2) "Hwp".

    iApply ewp_unfold. iDestruct (ewp_unfold with "Hwp") as "Hwp".
    rewrite /ewp_pre /=.
    assert (iris.to_val [AI_local n f LI] = None) as ->.
    { apply lfilled_to_sfill in Hfill1 as Hsh.
      destruct Hsh as [sh Hsh].
      apply const_es_exists in Hconst as Hvs0;destruct Hvs0 as [vs0 Hvs0].
      assert (vs ++ [AI_basic BI_return] = sfill (SH_base vs0 []) [AI_basic BI_return])%SEQ as Heq;[cbn;rewrite -Hvs0;auto|].
      pose proof (sfill_nested sh (SH_base vs0 []) [AI_basic BI_return]) as [vh' Hsh'].
      apply to_val_local_ret_none with (vh:=vh').
      rewrite Hsh Heq Hsh'.
      rewrite -/(iris.of_val (retV vh')).
      apply iris.to_of_val. }
    assert (to_val [AI_local n f0 LI'] = None) as ->.
    { apply lfilled_to_sfill in Hfill2 as Hsh.
      destruct Hsh as [sh Hsh].
      apply const_es_exists in Hconst as Hvs0;destruct Hvs0 as [vs0 Hvs0].
      assert (vs ++ [AI_basic BI_return] = sfill (SH_base vs0 []) [AI_basic BI_return])%SEQ as Heq;[cbn;rewrite -Hvs0;auto|].
      pose proof (sfill_nested sh (SH_base vs0 []) [AI_basic BI_return]) as [vh' Hsh'].
      apply to_val_local_ret_none with (vh:=vh').
      rewrite Hsh Heq Hsh'.
      rewrite -/(iris.of_val (retV vh')).
      apply iris.to_of_val. }
    assert (to_eff [AI_local n f LI] = None) as ->.
    { apply to_eff_local_none_none.
      eapply to_eff_None_lfilled => //=.
      intros Hc; apply const_list_split in Hc as [??] => //.
      apply to_eff_cat_None2 => //. }
    assert (to_eff [AI_local n f0 LI'] = None) as ->.
    { apply to_eff_local_none_none.
      eapply to_eff_None_lfilled => //=.
      intros Hc; apply const_list_split in Hc as [??] => //.
      apply to_eff_cat_None2 => //. } 
    
    iIntros (σ1 ) "Hσ".
    iSpecialize ("Hwp" $! σ1  with "Hσ").


    eassert (reduce _ 
                   {| f_locs := _; f_inst := _ |}
                   ([AI_local n f LI]) _
                   {| f_locs := _; f_inst := _ |}
                   vs).
    { eapply r_simple. eapply rs_return;eauto. }
    eassert (reduce _ 
                   {| f_locs := _; f_inst := _ |}
                   ([AI_local n f0 LI']) _ 
                   {| f_locs := _; f_inst := _ |}
                   vs).
    { eapply r_simple. eapply rs_return;eauto. }
    iMod "Hwp". iModIntro.
    iDestruct "Hwp" as "[_ Hwp]".
    iSplitR.
    { unfold reducible. iPureIntro.
      eexists [],_,(_,_,_),[]. simpl. repeat split;eauto. }
    iIntros (e2 ??? Hprim).

    destruct Hprim as [Hprim _].
    assert (first_instr ([AI_local n f0 LI']) = Some (AI_basic (BI_return),S(0 + j))) as Hfirst0.
    { eapply first_instr_local. eapply starts_with_lfilled;eauto.
      apply first_instr_const;auto. }
    eapply reduce_det in Hprim as [? [? | [[? ?]| [? [? [? [? [? [? ?]]]]] ]]]];[..|apply H0].
    all: try by (rewrite separate1 Hfirst0 in H2; inversion H2).
    inversion H1; subst; destruct H2 as [<- <-].
    iSpecialize ("Hwp" with "[]").
    { iPureIntro. unfold prim_step. repeat split;eauto. }
    iFrame. 
  Qed.

End control_rules.

