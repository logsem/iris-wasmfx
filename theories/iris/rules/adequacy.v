(* adequacy.v *)

(* This theory shows that reasoning in terms of [EWP] is sound: at the end of a
   verification task, the derivation of an [EWP] assertion entails that the
   verified (complete) program is _safe_. This is a non-trivial property
   (not every program is safe); roughly, it says that the verified program
   either diverges or terminates with a value, but it never performs operations
   without meaning, such as calling a function with the wrong number of
   arguments or performing an unhandled effect. *)

From iris.proofmode Require Import base tactics classes.
From iris.base_logic.lib Require Import iprop wsat.
From iris.program_logic Require Import weakestpre adequacy.
From Wasm.iris.rules Require Import iris_rules.


(* ========================================================================== *)
(** * Preliminaries. *)

(* -------------------------------------------------------------------------- *)
(** * Link Between [WP] and [EWP]. *)

(* The adequacy of [EWP] follows from the adequacy of [WP], the standard Iris
   weakest-precondition construction (that becomes available for any
   programming language satisfying the Iris axiomatization [Language]). The
   notion of [WP] is adequate. The idea is thus to prove that [EWP] entails
   [WP] (under the assumption that both protocols are empty). *)

Lemma ewp_imp_wp `{!irisGS eff_lang Σ} E e Φ :
  EWP e @ E <| ⊥ |> {| ⊥ |} {{ Φ }} -∗ WP e @ NotStuck; E {{ Φ }}.
Proof.
  iLöb as "IH" forall (e).
  destruct (to_val e) as [ v         |] eqn:?; [|
  destruct (to_eff e) as [((m, v), k)|] eqn:?  ].
  - rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /= Heqo. by auto.
  - rewrite -(of_to_eff _ _ _ _ Heqo0).
    iIntros "Hewp". by destruct m;
    [rewrite -ewp_eff_os_eq|rewrite -ewp_eff_ms_eq]; rewrite upcl_bottom.
  - rewrite ewp_unfold /ewp_pre wp_unfold /wp_pre /= Heqo Heqo0.
    iIntros "Hewp" (σ ns k ks nt) "Hs".
    iMod ("Hewp" $! σ ns k ks nt with "Hs") as "[$ H]". iModIntro.
    iIntros (e2 σ2 efs Hstep).
    case k   as [|??]; [|done].
    case efs as [|??]; [|done].
    simpl in Hstep.
    iMod ("H" with "[//]") as "H". iIntros "_ !> !>".
    simpl. iMod "H". iModIntro.
    iApply (step_fupdN_wand with "[H]"); first by iApply "H".
    iIntros "H". iMod "H" as "[$ Hewp]". iModIntro.
    by iSplit; [iApply "IH"|].
Qed.


(* ========================================================================== *)
(** * Adequacy. *)

Section adequacy.
  Context `{!heapGpreS Σ}. (* We make assumptions about the cameras available in
                              in the global list [Σ]. In [state_reasoning.v], we
                              show that these assumptions can be satisfied. *)

  (* ------------------------------------------------------------------------ *)
  (** Adequacy Theorem for [WP]. *)

  (* The main reasoning step in this proof is the allocation of ghost cells
     with contents in the cameras specified by [heapGpreS]. In particular,
     it is at this moment that the ghost cell [γ_heap] is fixed. *)

  Theorem eff_lang_wp_adequacy s e σ φ :
    (∀ `{!heapGS Σ}, ⊢ WP e @ s; ⊤ {{ v, ⌜ φ v ⌝ }}) →
      adequate s e σ (λ v _, φ v).
  Proof.
    intros Hwp; eapply (wp_adequacy _ _); iIntros (??) "".
    iMod (gen_heap_init σ.(heap)) as (?) "[Hh _]".
    iMod (inv_heap_init loc val) as (?) ">Hi".
    iModIntro. iExists
      (λ σ κs, gen_heap_interp σ.(heap)),
      (λ _, True%I).
    iFrame. iApply (Hwp (HeapGS _ _ _ _)).
  Qed.


  (* ------------------------------------------------------------------------ *)
  (** Adequacy Theorem for [EWP]. *)

  Theorem ewp_adequacy e σ φ :
    (∀ `{!heapGS Σ}, ⊢ EWP e <| ⊥ |> {| ⊥ |} {{ v, ⌜ φ v ⌝ }}) →
      adequate NotStuck e σ (λ v _, φ v).
  Proof.
    intros Hwp. apply eff_lang_wp_adequacy.
    intros. iApply ewp_imp_wp. iApply Hwp.
  Qed.


  (* ------------------------------------------------------------------------ *)
  (** Corollary: Safety. *)

  Corollary ewp_not_stuck e σ Φ :
    (∀ `{!heapGS Σ}, ⊢ EWP e <| ⊥ |> {| ⊥ |} {{ v, Φ v }}) →
      ∀ e' σ', rtc erased_step ([e], σ) ([e'], σ') → not_stuck e' σ'.
  Proof.
    intros Hewp ?? Hstep.
    assert (adequate NotStuck e σ (λ _ _, True)) as Hadequate.
    { apply ewp_adequacy =>?.
      by iApply ewp_mono; [iApply Hewp|]; iIntros (?) "_". }
    eapply adequate_alt in Hadequate as [_ Hnot_stuck]; eauto.
    apply Hnot_stuck; auto.
    set_solver.
  Qed.

End adequacy.
