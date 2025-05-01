(* shallow_handler_reasoning.v *)

(* This file introduces reasoning rules for shallow effect handlers. *)

From iris.proofmode Require Import base tactics classes.
From Wasm.iris.language Require Import protocols iris_ewp_def.
From Wasm.iris.rules Require Import iris_rules_effects.


(* ========================================================================== *)
(** * Shallow-Handler Judgment. *)

(* A shallow-handler judgment provides the specification of both return and
   effect branches of a (shallow) handler. *)

(* -------------------------------------------------------------------------- *)
(** Definition. *)

Definition shallow_handler `{!heapGS Σ}
  (E : coPset)
  (Ψ1 Ψ2 : iEffO (Σ:=Σ))
  (Φ : val -d> iPropO Σ)
  (h r : expr)
  (Ψ1' Ψ2' : iEffO (Σ:=Σ))
  (Φ' : val -d> iPropO Σ) : iProp Σ :=

  (* Correctness of the return branch. *)
  (∀ (y : val), Φ y -∗ EWP r y @ E <| Ψ1' |> {| Ψ2' |} {{ Φ' }}) ∧

  (* Correctness of the effect branch -- one-shot case. *)
  (∀ (v k : val),
     iEff_car (upcl OS Ψ1) v (λ w, EWP k w @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}) -∗
       EWP h v k @ E <| Ψ1' |> {| Ψ2' |} {{ Φ' }}) ∧

  (* Correctness of the effect branch -- multi-shot case. *)
  (∀ (v k : val),
     iEff_car (upcl MS Ψ2) v (λ w, EWP k w @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}) -∗
       EWP h v k @ E <| Ψ1' |> {| Ψ2' |} {{ Φ' }}).


(* -------------------------------------------------------------------------- *)
(** Non-expansiveness. *)

Global Instance shallow_handler_ne `{!heapGS Σ} E n :
  Proper
    ((dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==>
       (dist n) ==> (dist n) ==> (dist n) ==> (dist n) ==> (dist n))
  (shallow_handler (Σ:=Σ) E).
Proof.
  intros ??? ??? ??? ??-> ??-> ??? ??? ???. rewrite /shallow_handler.
  by repeat (apply iEff_car_ne || solve_proper || f_equiv).
Qed.
Global Instance shallow_handler_proper `{!heapGS Σ} E :
  Proper ((≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡) ==> (≡))
  (shallow_handler (Σ:=Σ) E).
Proof.
  intros ??? ??? ??? ??? ??? ??? ??? ???.
  apply equiv_dist=>n. by apply shallow_handler_ne; apply equiv_dist.
Qed.


(* -------------------------------------------------------------------------- *)
(** Monotonicity. *)

(* The shallow-handler judgment is contravariant
   on the handlee protocols, Ψ1 and Ψ2. *)
Lemma shallow_handler_mono `{!heapGS Σ}
  E Ψ1 Ψ1'' Ψ2 Ψ2'' Φ h r Ψ1' Ψ2' Φ' :
  shallow_handler E Ψ1 Ψ2 Φ h r Ψ1' Ψ2' Φ' -∗
    (Ψ1'' ⊑ Ψ1)%ieff -∗ (Ψ2'' ⊑ Ψ2)%ieff -∗
      shallow_handler E Ψ1'' Ψ2'' Φ h r Ψ1' Ψ2' Φ'.
Proof.
  iIntros "Hhandler #HΨ1 #HΨ2". iSplit; [|iSplit].
  - iIntros (y) "Hy". by iApply "Hhandler".
  - iIntros (v k) "HΨ1''". iDestruct "Hhandler" as "(_&Hh&_)".
    iApply "Hh". iApply (iEff_le_upcl with "HΨ1").
    iApply (monotonic_prot with "[] HΨ1''").
    iIntros (w) "Hkw".
    by iApply (ewp_pers_smono with "Hkw"); auto.
  - iIntros (v k) "HΨ2''". iDestruct "Hhandler" as "(_&_&Hh)".
    iApply "Hh". iApply (iEff_le_upcl with "HΨ2").
    iApply (pers_monotonic_prot with "[] HΨ2''").
    iIntros "!#" (w) "Hkw".
    by iApply (ewp_pers_smono with "Hkw"); auto.
Qed.

(* The shallow-handler judgment is covariant
   on the handler protocols, Ψ1' and Ψ2'. *)
Lemma shallow_handler_mono' `{!heapGS Σ}
  E Ψ1 Ψ1'' Ψ2 Ψ2'' Φ h r Ψ1' Ψ2' Φ' :
  shallow_handler E Ψ1 Ψ2 Φ h r Ψ1' Ψ2' Φ' -∗
    (Ψ1' ⊑ Ψ1'')%ieff -∗ (Ψ2' ⊑ Ψ2'')%ieff -∗
      shallow_handler E Ψ1 Ψ2 Φ h r Ψ1'' Ψ2'' Φ'.
Proof.
  iIntros "Hhandler #HΨ1' #HΨ2'". iSplit; [|iSplit].
  - iIntros (y) "Hy". iDestruct "Hhandler" as "[Hr _]".
    iSpecialize ("Hr" with "Hy").
    by iApply (ewp_pers_smono with "Hr"); auto.
  - iIntros (v k) "HΨ1". iDestruct "Hhandler" as "(_&Hh&_)".
    iSpecialize ("Hh" with "HΨ1").
    by iApply (ewp_pers_smono with "Hh"); auto.
  - iIntros (v k) "HΨ2". iDestruct "Hhandler" as "(_&_&Hh)".
    iSpecialize ("Hh" with "HΨ2").
    by iApply (ewp_pers_smono with "Hh"); auto.
Qed.


(* ========================================================================== *)
(** * Reasoning Rules. *)

(* -------------------------------------------------------------------------- *)
(** Invoking a One-Shot Continuation. *)

(* We prove this reasoning rule as an auxiliary principle in the proof
   of soundness of the reasoning rule for shallow handlers. *)

Lemma ewp_cont `{!heapGS Σ} E Ψ1 Ψ2 Φ k (w : val) l :
  ▷ EWP fill k w @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} -∗ l ↦ #false -∗
      EWP (ContV k l) w @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }}.
Proof.
  iIntros "Hk Hl".
  rewrite !(ewp_unfold _ (App _ _)) /ewp_pre //=.
  iIntros (σ ????) "Hσ".
  iDestruct (gen_heap_valid with "Hσ Hl") as "%".
  rename H into heap_valid.
  iMod (gen_heap_update _ _ _ #true with "Hσ Hl") as "[Hσ Hl]".
  iMod (fupd_mask_subseteq ∅) as "Hclose". by apply empty_subseteq.
  iModIntro. iSplitR.
  - iPureIntro. rewrite /reducible //=.
    exists [], (fill k w), (heap_upd <[l:=#true]> σ), []. simpl.
    apply (Ectx_prim_step _ _ _ _ [] (ContV k l w) (fill k w)); try done.
    apply ContS; by eauto.
  - iIntros (e₂ σ₂ Hstep).
    destruct κ; [|done]. simpl in Hstep.
    specialize (prim_step_inv_Cont _ _ _ _ _ _ Hstep) as [-> ->].
    by iFrame; auto.
Qed.


(* -------------------------------------------------------------------------- *)
(** Reasoning about Shallow Handlers. *)

Lemma ewp_try_with `{!heapGS Σ} E Ψ1 Ψ2 Φ Ψ1' Ψ2' Φ' e h r :
  EWP e @ E <| Ψ1 |> {| Ψ2 |} {{ Φ }} -∗
    shallow_handler E Ψ1 Ψ2 Φ h r Ψ1' Ψ2' Φ' -∗
      EWP (TryWith e h r) @ E <| Ψ1' |> {| Ψ2' |} {{ Φ' }}.
Proof.
  iLöb as "IH" forall (e Ψ1 Ψ2).
  destruct (to_val e) as [ v         |] eqn:He; [|
  destruct (to_eff e) as [((m, v), k)|] eqn:He' ].
  (* Return branch. *)
  - rewrite <-(of_to_val _ _ He).
    iIntros "HΦ [Hr _]".
    iApply fupd_ewp. iMod (ewp_value_inv with "HΦ") as "HΦ". iModIntro.
    iApply ewp_pure_step'. { by apply pure_prim_step_TryWithVal. }
    by iApply ("Hr" with "HΦ").
  (* Effect branch. *)
  - rewrite <-(of_to_eff _ _ _ _ He').
    destruct m; [iIntros "Heff (_&Hh&_)"|iIntros "Heff (_&_&Hh)"].
    (* One-shot. *)
    + rewrite -ewp_eff_os_eq.
      rewrite !ewp_unfold /ewp_pre //=.
      iIntros (σ ????) "Hσ".
      iMod (fupd_mask_subseteq ∅) as "Hclose". by apply empty_subseteq.
      iModIntro. iSplitR.
      * iPureIntro. rewrite /reducible //=.
        set (l := Loc.fresh (dom σ.(heap))).
        exists [], (h v (ContV k l)), (heap_upd <[l:=#false]> σ), []. simpl.
        apply (Ectx_prim_step _ _ _ _ []
              (TryWith (Eff OS v k) h r) (h v (ContV k l))); try done.
        by apply try_with_fresh.
      * iIntros (e₂ σ₂ Hstep). destruct κ; [|done]. simpl in Hstep.
        specialize (prim_step_inv_TryWithOSEff _ _ _ _ _ _ _ Hstep)
          as [l [Hlkp [-> ->]]].
        iMod (gen_heap_alloc _ l #false with "Hσ") as "($ & Hl & Hm)". { done. }
        iSpecialize ("Hh" $! v (ContV k l) with "[Heff Hl]").
        { iDestruct "Heff" as "[%Q [HΨ1 Hk]]". iExists Q. iFrame.
          iIntros (w) "HQ". iApply (ewp_cont with "[HQ Hk] Hl").
          by iApply "Hk".
        }
        iIntros "!> !> !>". by iMod "Hclose".
    (* Multi-shot. *)
    + rewrite -ewp_eff_ms_eq.
      iApply ewp_pure_step. { by apply pure_prim_step_TryWithMSEff. }
      iApply "Hh". iApply (pers_monotonic_prot with "[] Heff").
      iIntros "!#" (w) "Hk".
      iApply ewp_pure_step'. { by apply pure_prim_step_Kont. }
      done.
  (* One execution step. *)
  - iIntros "He Hhandler".
    rewrite !(ewp_unfold _ (TryWith _ _ _))
            !(ewp_unfold _ e) /ewp_pre He He' //=.
    iIntros (σ₁ ns k' ks nt) "Hs".
    iMod ("He" $! σ₁ ns k' ks nt with "Hs") as "[% He]".
    iSplitR.
    + iPureIntro. revert H; unfold reducible. simpl.
      rewrite /prim_step'; simpl.
      destruct 1 as [obs [e₄ [σ₄ [efs Hstep]]]].
      case obs in Hstep; [|done].
      case efs in Hstep; [|done].
      inversion Hstep. simplify_eq.
      exists [], (TryWith (fill k e2') h r), σ₄, [].
      by apply (Ectx_prim_step _ _ _ _ ((TryWithCtx h r) :: k) e1' e2').
    + iModIntro. iIntros (e₄ σ₄) "%".
      destruct k'; [|done]. rename H0 into Hstep. simpl in Hstep.
      assert (Hstep' : ∃ e₅, prim_step e σ₁ e₅ σ₄ ∧ e₄ = TryWith e₅ h r).
      { inversion Hstep. destruct k as [|f k].
        - simpl in H; simplify_eq. inversion H2; naive_solver.
        - destruct f; try naive_solver. simpl in *; simplify_eq.
          exists (fill k e2'). simpl. split;[| done].
          by apply (Ectx_prim_step _ _ _ _ k e1' e2').
      }
      destruct Hstep' as [e₅ [Hstep' ->]].
      iDestruct ("He" $! e₅ σ₄ Hstep') as "> He".
      iIntros "!> !>". iMod "He". iModIntro.
      iMod "He" as "[$ He]". iModIntro.
      by iApply ("IH" with "He Hhandler").
Qed.
