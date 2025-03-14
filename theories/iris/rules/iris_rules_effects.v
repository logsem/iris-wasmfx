(* basic_reasoning_rules.v *)

(* This theory introduces the basic principles that allow reasoning in terms
   of [EWP]. The most important principles in this theory are the bind rule,
   which endorses modular reasoning about the evaluation context by allowing
   one to compose specifications; and the frame rule, which endorses modular
   reasoning about the state by allowing one to derive specifications with
   a larger footprint than their original statement. *)

From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.
From Wasm.iris.language.iris Require Import weakest_precondition.


(* ========================================================================== *)
(** * Reasoning Rules. *)

Section reasoning_rules.
  Context `{!irisGS eff_lang Σ}.

  (* ------------------------------------------------------------------------ *)
  (** Values and Effects. *)

  Lemma ewp_value E Ψ1 Ψ2 Φ v :
    Φ v -∗ EWP (of_val v) @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.
  Lemma ewp_value_inv E Ψ1 Ψ2 Φ v :
    EWP of_val v @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} ={E}=∗ Φ v.
  Proof. iIntros "HΦ". by rewrite ewp_unfold /ewp_pre. Qed.
  Lemma ewp_value_fupd E Ψ1 Ψ2 Φ v :
    (|={E}=> Φ v)%I ⊢ EWP of_val v @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof. intros. by rewrite !ewp_unfold /ewp_pre. Qed.
  Lemma ewp_eff_os_eq E Ψ1 Ψ2 Φ v k :
    iEff_car (upcl OS Ψ1) v (λ w,
      ▷ EWP fill k (Val w) @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }})
      ⊣⊢
    EWP of_eff OS v k @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof. by rewrite ewp_unfold /ewp_pre /=. Qed.
  Lemma ewp_eff_ms_eq E Ψ1 Ψ2 Φ v k :
    iEff_car (upcl MS Ψ2) v (λ w,
      ▷ EWP fill k (Val w) @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }})
      ⊣⊢
    EWP of_eff MS v k @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof. by rewrite ewp_unfold /ewp_pre /=. Qed.
  Lemma ewp_eff_os E Ψ1 Ψ2 Φ v k :
    iEff_car (upcl OS Ψ1) v (λ w,
      ▷ EWP fill k (Val w) @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}) -∗
    EWP of_eff OS v k @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof. rewrite ewp_eff_os_eq. iIntros "$". Qed.
  Lemma ewp_eff_ms E Ψ1 Ψ2 Φ v k :
    iEff_car (upcl MS Ψ2) v (λ w,
      ▷ EWP fill k (Val w) @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}) -∗
    EWP of_eff MS v k @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof. rewrite ewp_eff_ms_eq. iIntros "$". Qed.

  (* Test. *)
  Goal forall A (P : A → iProp Σ) Φ (Ψ : iEff Σ) (v : val) x,
    (P x -∗
    EWP (Eff MS v [])
      <| >> x >> ! v {{ P x }}; << w << ? w {{ Φ w }} @ OS |>
      {| >> x >> ! v {{ P x }}; << w << ? w {{ Φ w }} @ MS |}
      {{ w, Φ w }})%ieff.
  Proof.
    intros A P Φ Ψ v x.
    iIntros "HP". iApply ewp_eff_ms.
    rewrite (pers_upcl_tele' [tele _] [tele _]) //=.
    iExists x. iFrame.
    iSplit; [done|]. iIntros "!#" (w) "HΦ". iNext.
    by iApply ewp_value.
  Qed.


  (* ------------------------------------------------------------------------ *)
  (** Monotonicity. *)

  (* This principle is only sound if multi-shot effects (and continuations)
     are disallowed. Recall that when a protocol is not specified the default
     one is ⊥. *)
  Lemma ewp_mono E Ψ Φ Φ' e :
    EWP e @ E <| Ψ |> {{ Φ }} -∗
      (∀ v, Φ v ={E}=∗ Φ' v) -∗
        EWP e @ E <| Ψ |> {{ Φ' }}.
  Proof.
    iIntros "He HΦ". iLöb as "IH" forall (e).
      destruct (to_val e) as [ v         |] eqn:?;
    [|destruct (to_eff e) as [((m, v), k)|] eqn:?].
    - rewrite !ewp_unfold /ewp_pre Heqo. iMod "He". by iApply "HΦ".
    - rewrite -(of_to_eff _ _ _ _ Heqo0).
      destruct m; [rewrite -!ewp_eff_os_eq|rewrite -!ewp_eff_ms_eq];[|
      by iDestruct "He" as "[% [HFalse _]]"; simpl].
      iApply (monotonic_prot with "[HΦ] He"). simpl.
      iIntros (w) "Hk". iNext. by iApply ("IH" with "Hk HΦ").
    - rewrite !ewp_unfold /ewp_pre Heqo Heqo0.
      iIntros (σ₁ ns k ks nt) "Hσ".
      iMod (fupd_mask_subseteq E) as "Hclose"; first done.
      iMod ("He" with "[$]") as "[$ H]".
      iModIntro. iIntros (e₂ σ₂ Hstep).
      iMod ("H" with "[//]") as "H". iIntros "!> !>".
      iMod "H". iModIntro.
      iApply (step_fupdN_wand with "[H]"); first by iApply "H".
      iIntros ">($ & H)". iMod "Hclose" as "_". iModIntro.
      iApply ("IH" with "H HΦ").
  Qed.

  Lemma ewp_pers_smono E E' Ψ1 Ψ1' Ψ2 Ψ2' Φ Φ' e :
    E ⊆ E' →
      EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} -∗
        (Ψ1 ⊑ Ψ1')%ieff -∗ (Ψ2 ⊑ Ψ2')%ieff -∗
          □ (∀ v, Φ v ={E'}=∗ Φ' v) -∗
            EWP e @ E' <| Ψ1' |> {| Ψ2' |} {{ Φ' }}.
  Proof.
      iIntros (HE) "He #HΨ1 #HΨ2 #HΦ".
      iLöb as "IH" forall (e).
      destruct (to_val e) as [ v         |] eqn:?;
    [|destruct (to_eff e) as [((m, v), k)|] eqn:?].
    - rewrite !ewp_unfold /ewp_pre Heqo.
      iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E _).
    - rewrite -(of_to_eff _ _ _ _ Heqo0).
      destruct m; [rewrite -!ewp_eff_os_eq|rewrite -!ewp_eff_ms_eq]; [
      iApply (iEff_le_upcl with "HΨ1")|
      iApply (iEff_le_upcl with "HΨ2")]; [
      iApply (monotonic_prot with "[HΦ] He")|
      iApply (pers_monotonic_prot with "[] He"); iModIntro];
      iIntros (w) "Hk"; iNext; by iApply ("IH" with "Hk").
    - rewrite !ewp_unfold /ewp_pre Heqo Heqo0.
      iIntros (σ₁ ns k ks nt) "Hσ".
      iMod (fupd_mask_subseteq E) as "Hclose"; first done.
      iMod ("He" with "[$]") as "[$ H]".
      iModIntro. iIntros (e₂ σ₂ Hstep).
      iMod ("H" with "[//]") as "H". iIntros "!> !>".
      iMod "H". iModIntro.
      iApply (step_fupdN_wand with "[H]"); first by iApply "H".
      iIntros ">($ & H)". iMod "Hclose" as "_". iModIntro.
      iApply ("IH" with "H").
  Qed.

  Corollary ewp_pers_mono E Ψ1 Ψ2 Φ Φ' e :
    EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} -∗
      □ (∀ v, Φ v ={E}=∗ Φ' v) -∗
        EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ' }}.
  Proof.
    iIntros "He #HΦ".
    iApply (ewp_pers_smono with "He"); try auto;
    by iApply iEff_le_refl.
  Qed.

  Corollary ewp_mask_mono E E' Ψ1 Ψ2 Φ e :
    E ⊆ E' →
      EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} -∗
        EWP e @ E' <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof.
    iIntros (HE) "He".
    iApply (ewp_pers_smono with "He"); try auto;
    by iApply iEff_le_refl.
  Qed.

  Corollary ewp_os_prot_mono E Ψ1 Ψ1' Ψ2 Φ e :
    (Ψ1 ⊑ Ψ1')%ieff -∗
      EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} -∗
        EWP e @ E <| Ψ1' |> {| Ψ2 |} {{ Φ }}.
  Proof.
    iIntros "#HΨ1 He".
    iApply (ewp_pers_smono with "He"); try auto;
    by iApply iEff_le_refl.
  Qed.

  Corollary ewp_ms_prot_mono E Ψ1 Ψ2 Ψ2' Φ e :
    (Ψ2 ⊑ Ψ2')%ieff -∗
      EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} -∗
        EWP e @ E <| Ψ1 |> {| Ψ2' |} {{ Φ }}.
  Proof.
    iIntros "#HΨ2 He".
    iApply (ewp_pers_smono with "He"); try auto;
    by iApply iEff_le_refl.
  Qed.


  (* ------------------------------------------------------------------------ *)
  (** Frame Rule. *)

  Lemma ewp_frame_r E R Ψ Φ e :
    EWP e @ E <| Ψ |> {{ v, Φ v }} -∗ R -∗ EWP e @ E <| Ψ |> {{ v, Φ v ∗ R }}.
  Proof. by iIntros "He HR"; iApply (ewp_mono with "He"); iFrame; auto. Qed.

  Lemma ewp_frame_l E R Ψ Φ e :
    R -∗ EWP e @ E <| Ψ |> {{ v, Φ v }} -∗ EWP e @ E <| Ψ |> {{ v, R ∗ Φ v }}.
  Proof. by iIntros "HR He"; iApply (ewp_mono with "He"); iFrame; auto. Qed.


  (* ------------------------------------------------------------------------ *)
  (** Ghost Update. *)

  (* This rule allows updating the _ghost state_. Ghost state is a standard
     technique in formal verification, usually presented under the formalism of
     _history variables_ (cf. "The Existence of Refinement Mappings" by Abadi
     and Lamport). According to the interface exposed by Iris, ghost state can
     be seen as a fictional extension of the heap, within which elements of a
     _camera_ M are stored. A user can reason about the possession of fragments
     of a _ghost cell_ and update these fragments, provided that these updates
     are _frame-preserving_. *)

  Lemma fupd_ewp E e Ψ1 Ψ2 Φ :
    TCEq (to_eff e) None →
      (|={E}=> EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}) -∗
        EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof.
    iIntros (?) "H"; rewrite ewp_unfold /ewp_pre.
      destruct (to_val e) as [ v    |] eqn:?;
    [|destruct (to_eff e) as [(v, k)|] eqn:?].
    { by iMod "H". } { by inversion H. }
    { iIntros (σ1 ns k ks nt) "Hσ1". iMod "H". by iApply "H". }
  Qed.

  (* Eliminate update modality in the postcondition. *)
  Lemma ewp_fupd E e Ψ1 Ψ2 Φ :
    EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ v, |={E}=> Φ v }} -∗
      EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof. by iIntros "He"; iApply (ewp_pers_mono with "He"); auto. Qed.


  (* ------------------------------------------------------------------------ *)
  (** Reasoning about Atomic Steps. *)

  (* This rules allows access to invariant-protected resources during atomic
     steps of execution. *)
  Lemma ewp_atomic E1 E2 e Ψ1 Ψ2 Φ `{!Atomic StronglyAtomic e} :
    TCEq (to_eff e) None →
      (|={E1,E2}=> EWP e @ E2 <| Ψ1 |> {| Ψ2 |} {{ v, |={E2,E1}=> Φ v }}) -∗
        EWP e @ E1 <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof.
    iIntros (?) "H". rewrite !ewp_unfold /ewp_pre.
      destruct (to_val e) as [ v    |] eqn:He;
    [|destruct (to_eff e) as [(v, k)|] eqn:He'].
    - by iDestruct "H" as ">>> $".
    - by inversion H.
    - iIntros (σ1 ns k κs nt) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
      iModIntro. iIntros (e2 σ2 Hstep).
      iApply (step_fupdN_wand with "[H]"); first by iApply "H".
      iIntros ">(Hσ & H)".
      rewrite !ewp_unfold /ewp_pre.
        destruct (to_val e2) as [ v2     |] eqn:He2;
      [|destruct (to_eff e2) as [(v2, k2)|] eqn:He2'].
      + iDestruct "H" as ">> $". by iFrame.
      + have Hstep' : prim_step' e σ1 [] e2 σ2 []. { by destruct k. }
        edestruct (atomic _ _ _ _ _ Hstep'); by naive_solver.
      + iMod ("H" $! _ _ [] with "[$]") as "[H _]".
        iDestruct "H" as %(? & ? & ? & ? & ?).
        have Hstep' : prim_step' e σ1 [] e2 σ2 []. { by destruct k. }
        edestruct (atomic _ _ _ _ _ Hstep'); by naive_solver.
  Qed.


  (* ------------------------------------------------------------------------ *)
  (** Reasoning about Pure Steps. *)

  Lemma ewp_pure_step' E e e' Ψ1 Ψ2 Φ :
    pure_prim_step e e' → 
      ▷ EWP e' @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} -∗
          EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof.
    intros Hstep.
      destruct (to_val e) as [ v         |] eqn:He;
    [|destruct (to_eff e) as [((m, v), k)|] eqn:He'].
    - by specialize (val_not_pure' _ _   e' He).
    - by specialize (eff_not_pure' _ _ e' He').
    - rewrite !(ewp_unfold E e) /ewp_pre He He'.
      iIntros "Hewp" (σ₁ ns k ks nt) "Hs".
      iMod (fupd_mask_subseteq ∅) as "Hclose"; [by apply empty_subseteq|].
      iModIntro. iSplitR;
      [iPureIntro; by apply (pure_prim_step_imp_reducible _ e')|].
      iIntros (e₂ σ₂ Hstep'). destruct k; [|done].
      destruct (pure_prim_step_det _ _ Hstep _ _ _ Hstep') as [-> ->].
      simpl. iIntros "!> !>".
      iMod (state_interp_mono with "Hs") as "Hs". iModIntro.
      induction num_laters_per_step as [|k IH]; simpl;
      [by iFrame|iIntros "!>!>!>"; by apply IH].
  Qed.

  Lemma ewp_pure_step E e e' Ψ1 Ψ2 Φ :
    pure_prim_step e e' → 
      EWP e' @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} -∗
        EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof. iIntros "% Hwp". by iApply (ewp_pure_step' with "Hwp"). Qed.

  Lemma ewp_pure_steps' E e e' Ψ1 Ψ2 Φ :
    tc pure_prim_step e e' → 
      ▷ EWP e' @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} -∗
          EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof.
    intros Hstep; iInduction Hstep as [|] "IH".
    - by iApply ewp_pure_step'.
    - iIntros "Hewp". iApply ewp_pure_step'. apply H. iNext. by iApply "IH".
  Qed.

  Lemma ewp_pure_steps E e e' Ψ1 Ψ2 Φ :
    rtc pure_prim_step e e' → 
      EWP e' @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} -∗
        EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof.
    intros Hstep; iInduction Hstep as [|] "IH".
    - by iIntros "?".  
    - iIntros "Hewp". iApply ewp_pure_step. apply H. by iApply "IH".
  Qed.

  (* Combination of [ewp_eff] and [ewp_pure_step]. *)
  Lemma ewp_do_os E v Ψ1 Ψ2 Φ :
    iEff_car (upcl OS Ψ1) v Φ -∗ EWP do: v @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof.
    iIntros "HΨ". iApply ewp_pure_step. { by apply pure_prim_step_Do. }
    iApply ewp_eff_os. iApply (monotonic_prot with "[] HΨ").
    iIntros (w) "HΦ". by iApply ewp_value.
  Qed.

  Lemma ewp_do_ms E v Ψ1 Ψ2 Φ :
    iEff_car (upcl MS Ψ2) v Φ -∗ EWP doₘ: v @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof.
    iIntros "HΨ". iApply ewp_pure_step. { by apply pure_prim_step_Do. }
    iApply ewp_eff_ms. iApply (pers_monotonic_prot with "[] HΨ").
    iIntros "!#" (w) "HΦ". by iApply ewp_value.
  Qed.


  (* ------------------------------------------------------------------------ *)
  (** Bind Rule. *)

  Lemma ewp_eff_steps k `{NeutralEctx k} E Ψ1 Ψ2 Φ m v k' :
    EWP Eff m v (k ++ k') @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} -∗
      EWP fill k (Eff m v k') @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof. by apply ewp_pure_steps, rtc_pure_prim_step_Eff. Qed.

  Lemma ewp_bind k `{NeutralEctx k} E Ψ1 Ψ2 Φ e e' :
    e' = fill k e  →
      EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ v,
        EWP fill k (of_val v) @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} }} -∗
          EWP e' @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof.
    intros ->. iLöb as "IH" forall (e Ψ1 Ψ2).
    rewrite !(ewp_unfold E e) /ewp_pre.
      destruct (to_val e) as [ v          |] eqn:He;
    [|destruct (to_eff e) as [((m, v), k')|] eqn:He'].
    - rewrite <- (of_to_val _ _ He). iIntros "H".
      by iApply fupd_ewp; first rewrite fill_not_eff.
    - iIntros "H".
      rewrite <- (of_to_eff _ _ _ _ He').
      iApply ewp_eff_steps.
      destruct m; [iApply ewp_eff_os|iApply ewp_eff_ms]; simpl; [
      iDestruct "H" as (Q) "[HP HQ]"|
      iDestruct "H" as (Q) "[HP #HQ]"];
      iExists Q; iFrame; [|iModIntro]; iIntros (w) "HQ'";
      rewrite fill_app; iApply "IH"; by iApply "HQ".
    - rewrite !ewp_unfold /ewp_pre.
      rewrite (fill_not_val _ _ He) (fill_not_eff k _ He').
      iIntros "Hewp" (σ₁ ns k' ks nt) "Hs".
      iMod ("Hewp" $! σ₁ with "Hs") as "[% Hewp]". iModIntro.
      iSplitR; [iPureIntro; by apply reducible_fill|].
      iIntros (e₂ σ₂) "%".
      destruct k'; [|done]. rename H1 into Hstep. simpl in Hstep.
      destruct (Ectx_prim_step_inv k _ _ _ _ He He' Hstep) as [e' [Hstep' ->]].
      iMod ("Hewp" $! e' σ₂ Hstep') as "Hewp". iIntros "!> !>".
      iMod "Hewp". iModIntro.
      iApply (step_fupdN_wand with "[Hewp]"); first by iApply "Hewp".
      iIntros "H". iMod "H" as "[$ Hewp]". iModIntro.
      by iApply "IH".
  Qed.

  Lemma ewp_bind' f `{NeutralFrame f} E Ψ1 Ψ2 Φ e e' :
    e' = fill_frame f e  →
      EWP e  @ E <| Ψ1 |> {| Ψ2 |} {{ v,
        EWP fill_frame f (of_val v) @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} }} -∗
          EWP e' @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof. intros ->. by iApply (ewp_bind [f]). Qed.

  (* If [e] does not perform effects, then it is sound to "bind" [e]
     under an arbitrary evaluation context [k]. *)
  Lemma ewp_pure_bind k E Ψ1 Ψ2 Φ e e' :
    e' = fill k e  →
      EWP e @ E {{ v, EWP fill k (of_val v) @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} }} -∗
        EWP e' @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
  Proof.
    intros ->. iLöb as "IH" forall (e).
    rewrite !(ewp_unfold E e) /ewp_pre.
      destruct (to_val e) as [ v          |] eqn:He;
    [|destruct (to_eff e) as [((m, v), k')|] eqn:He'].
    - rewrite <- (of_to_val _ _ He).
      iIntros "H". by iApply fupd_ewp; first rewrite fill_not_eff.
    - destruct m; rewrite upcl_bottom; by iIntros "HFalse".
    - rewrite !ewp_unfold /ewp_pre.
      rewrite (fill_not_val _ _ He) (fill_not_eff k _ He').
      iIntros "Hewp"  (σ₁ ns k' ks nt) "Hs".
      iMod ("Hewp" $! σ₁ with "Hs") as "[% Hewp]". iModIntro.
      iSplitR; [iPureIntro; by apply reducible_fill|].
      iIntros (e₂ σ₂) "%".
      destruct k';[|done]; rename H0 into Hstep, H into Hred.
      destruct (Ectx_prim_step_inv k _ _ _ _ He He' Hstep) as [e' [Hstep' ->]].
      iMod ("Hewp" $! e' σ₂ Hstep') as "Hewp". iIntros "!> !>".
      iMod "Hewp". iModIntro.
      iApply (step_fupdN_wand with "[Hewp]"); first by iApply "Hewp".
      iIntros "H". iMod "H" as "[$ Hewp]". iModIntro.
      by iApply "IH".
  Qed.

End reasoning_rules.

