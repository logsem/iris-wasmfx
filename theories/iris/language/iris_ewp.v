(* weakest_precondition.v *)

(* This theory introduces a notion of weakest precondition for reasoning about
   [eff_lang] programs. The key idea is to extend a weakest-precondition
   assertion with a pair of protocols to describe the effects that a program
   (fragment) might perform; the first protocol specifies one-shot effects,
   whereas the second one specifies multi-shot effects. *)

From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.
From Wasm.iris.language.iris Require Export iris.
From Wasm.iris.language Require Export protocols iris_resources.


Set Bullet Behavior "Strict Subproofs".

(* ========================================================================== *)
(** * Weakest Precondition. *)

(* -------------------------------------------------------------------------- *)
(** Definition. *)

 Inductive effect_identifier : Type :=
| SuspendE : tagidx -> effect_identifier
| SwitchE : tagidx -> effect_identifier
| ThrowE : tagidx -> effect_identifier
.


  

Definition ewp_pre `{!wasmG Σ} :
  (coPset -d> expr -d> frame -d> (frame -d> iPropO Σ) -d>
        (effect_identifier -d> iProt Σ) -d> 
     (val -d> iPropO Σ) -d> iPropO Σ) →
  (coPset -d> expr -d> frame -d> (frame -d> iPropO Σ) -d>
     (effect_identifier -d> iProt Σ) -d> 
     (val -d> iPropO Σ) -d> iPropO Σ)
  := λ ewp E e₁ f Φf Ψ Φ,
  match to_val e₁ with
  | Some v =>
      |={E}=> Φ v ∗ Φf f 
  | None =>
      match to_eff e₁ with
      | Some (thrE vs i a sh) =>
      (*    Ψ (ThrowE a) (immV vs)
       (* Hmmm have value instead of val to avoid immV? *) *)
          iProt_car (upcl $ Ψ $ ThrowE a) (immV vs) (λ w, False)%I
      | Some (susE vs i sh) =>
          iProt_car (upcl $ Ψ $ SuspendE i) (immV vs) (λ w, ▷ ewp E (susfill i sh (of_val w)) f Φf Ψ Φ)
      | Some (swE vs k tf i sh) =>
          iProt_car (upcl $ Ψ $ SwitchE i) (immV vs) (λ w, ▷ ewp E (swfill i sh (of_val w)) f Φf Ψ Φ)
      | None =>
          ∀ s1,
            state_interp s1 ={E,∅}=∗
              ⌜ reducible e₁ (s1, f_locs f, f_inst f) ⌝ ∗  
              ∀ e₂ s2 inst2 locs2, ⌜ prim_step e₁ (s1, f_locs f, f_inst f) [] e₂ (s2, locs2, inst2) [] ⌝
                ={∅}▷=∗ |={∅,E}=>
                state_interp s2 ∗ ewp E e₂ (Build_frame locs2 inst2) Φf Ψ Φ
      end
  end%I.

Local Instance ewp_pre_contractive `{!wasmG Σ} : Contractive ewp_pre.
Proof.
  rewrite /ewp_pre=> n ewp ewp' Hwp E e f Φf Ψ  Φ.
  do 4 f_equiv; try by intros => ?; f_contractive; apply Hwp.
  do 17 (f_contractive || f_equiv).
  apply Hwp.
Qed.
Definition ewp_def `{!wasmG Σ} :
  coPset -d> expr -d> frame -d> (frame -d> iPropO Σ) -d> 
    (effect_identifier -d> iProt Σ) -d> 
    (val -d> iPropO Σ) -d> iPropO Σ :=
  fixpoint ewp_pre.
Definition ewp_aux `{!wasmG Σ} : seal ewp_def. Proof. by eexists. Qed.
Definition ewp_eq `{!wasmG Σ} := ewp_aux.(seal_eq).
Definition ewp' `{!wasmG Σ} := ewp_aux.(unseal).



(* -------------------------------------------------------------------------- *)
(** Non-expansiveness. *)

Lemma ewp_unfold `{!wasmG Σ} E e f Φf Ψ Φ :
  ewp_def E e f Φf Ψ Φ ⊣⊢ ewp_pre ewp_def E e f Φf Ψ Φ.
Proof. by rewrite /ewp_def; apply (fixpoint_unfold ewp_pre). Qed.


Global Instance ewp_ne `{!wasmG Σ} E e f Φf n :
  Proper ((dist n) ==> (dist n) ==> (dist n) ) (ewp_def E e f Φf).
Proof.
  revert e f Φf.
  induction (lt_wf n) as [n _ IH]=> e f Φf Ψ1 Ψ1' HΨ1 Φ Φ' HΦ.
  rewrite !ewp_unfold /ewp_pre /upcl. simpl.
  f_equiv. { f_equiv. f_equiv. by f_equiv. }
  f_equiv.
  - f_equiv.
    + do 3 f_equiv. 
      * f_equiv. 
        apply IProt_ne.
        f_equiv.
        apply HΨ1.
      * f_equiv. intros ?. do 2 (f_contractive || f_equiv).
        apply IH; try lia; eapply dist_le; eauto with lia. 
    + do 3 f_equiv. 
      * f_equiv. apply IProt_ne. f_equiv. apply HΨ1.
      * f_equiv. intros ?. do 2 (f_contractive || f_equiv). 
        apply IH; try lia; eapply dist_le; eauto with lia.
    + f_equiv. f_equiv. f_equiv. f_equiv. apply IProt_ne. f_equiv. apply HΨ1.  
  - do 5 f_equiv. do 14 (f_contractive || f_equiv).
    apply IH; try lia; eapply dist_le; eauto with lia. 
Qed.

Global Instance ewp_proper `{!wasmG Σ} E e f Φf:
  Proper ((≡) ==> (≡) ==> (≡)) (ewp_def E e f Φf).
Proof.
  intros Ψ1 Ψ1' ? Φ Φ' ?.
  by apply equiv_dist=>n; apply ewp_ne; apply equiv_dist.
Qed.


(* -------------------------------------------------------------------------- *)
(** Notation. *)

Notation "'EWP' e 'UNDER'  f @ E {{ Φ ; h } }" :=
  (ewp_def E e%E f h (λ _, iProt_bottom) Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' 'UNDER'  f  @  E  {{  Φ  ;  h  } } ']' ']'") : bi_scope.
Notation "'EWP' e 'UNDER'  f @ E <| Ψ |>  {{ Φ ; h } }" :=
  (ewp_def E e%E f h Ψ Φ)
  (at level 20, e, Ψ, Φ at level 200,
    format "'[' 'EWP'  e  '/' '[          ' 'UNDER'  f  @  E  <|  Ψ  |>  {{  Φ  ;  h  } } ']' ']'") : bi_scope. 


(* Postcondition includes binder. *)

Notation "'EWP' e 'UNDER'  f @ E {{ v , Φ ; h } }" :=
  (ewp_def E e%E f h ( λ _, iProt_bottom ) (λ v, Φ))
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' 'UNDER'  f  @  E  {{ v , Φ  ;  h  } } ']' ']'") : bi_scope.
 Notation "'EWP' e 'UNDER'  f @ E <| Ψ |>  {{ v , Φ ; h } }" :=
  (ewp_def E e%E f h Ψ (λ v, Φ))
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' 'UNDER'  f  @  E  <| Ψ |>  {{  v , Φ  ;  h  } } ']' ']'") : bi_scope. 

(* Mask is implicitly specified by ⊤. *)

Notation "'EWP' e 'UNDER'  f {{ v , Φ ; h } }" :=
  (ewp_def ⊤ e%E f h ( λ _, iProt_bottom ) (λ v, Φ))
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' 'UNDER'  f  {{ v , Φ  ;  h  } } ']' ']'") : bi_scope.
 Notation "'EWP' e 'UNDER'  f <| Ψ |>  {{ v , Φ ; h } }" :=
  (ewp_def ⊤ e%E f h Ψ (λ v, Φ))
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  'UNDER'  f  <|  Ψ  |>  {{  v , Φ  ;  h  } } ']' ']'") : bi_scope. 

(* No binder and no mask. *)

Notation "'EWP' e 'UNDER'  f {{ Φ ; h } }" :=
  (ewp_def ⊤ e%E f h ( λ _, iProt_bottom ) Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  'UNDER'  f  {{  Φ  ;  h  } } ']' ']'") : bi_scope.
 Notation "'EWP' e 'UNDER'  f <| Ψ |>  {{ Φ ; h } }" :=
  (ewp_def ⊤ e%E f h Ψ Φ)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  'UNDER'  f  <|  Ψ  |>  {{  Φ  ;  h  } } ']' ']'") : bi_scope. 

(* Tests *)
(* Check (λ Σ es P Q, EWP es <| λ _, iProt_bottom |> {{ λ v, True }})%I.
 Check (λ Σ es P Q, EWP es <| λ i w, λne Φ, ⌜ i = SuspendE (Mk_tagidx 1) ⌝ ∗ ((>> v >> ! v {{ P }} ; << w << ? w {{ Q }})%iprot w Φ) |> {{ λ v, True }})%I. *)


Section wp.
  Context `{!wasmG Σ}.

  Lemma ewp_value_fupd' E f Φf Ψ Φ v : EWP of_val v UNDER f @ E <| Ψ |> {{ Φ ; Φf }} ⊣⊢ |={E}=> Φ v ∗  Φf f .
  Proof. rewrite ewp_unfold /ewp_pre. rewrite to_of_val. auto. Qed.

  Lemma ewp_effect_sus' E f Φf Ψ Φ vs i sh : EWP of_eff (susE vs i sh) UNDER f @ E <| Ψ |> {{ Φ ; Φf }} ⊣⊢ iProt_car (upcl $ Ψ $ SuspendE i) (immV vs) (λ w, ▷ EWP (susfill i sh (of_val w)) UNDER f @ E <| Ψ |> {{ Φ ; Φf }}).
  Proof.
    rewrite ewp_unfold /ewp_pre. rewrite to_of_eff.
    destruct (to_val _) eqn:Habs => //.
    exfalso; eapply to_val_to_eff => //.
    rewrite to_of_eff //.
  Qed.

  Lemma ewp_effect_sw' E f Φf Ψ Φ vs k tf i sh : EWP of_eff (swE vs k tf i sh) UNDER f @ E <| Ψ |> {{ Φ ; Φf }} ⊣⊢ iProt_car (upcl $ Ψ $ SwitchE i) (immV vs) (λ w, ▷ EWP (swfill i sh (of_val w)) UNDER f @ E <| Ψ |> {{ Φ ; Φf }}).
  Proof.
    rewrite ewp_unfold /ewp_pre. rewrite to_of_eff.
    destruct (to_val _) eqn:Habs => //.
    exfalso; eapply to_val_to_eff => //.
    rewrite to_of_eff //.
  Qed.


   Lemma ewp_effect_thr' E f Φf Ψ  Φ vs i a sh : EWP of_eff (thrE vs i a sh) UNDER f @ E <| Ψ |> {{ Φ ; Φf }} ⊣⊢ iProt_car (upcl $ Ψ $ ThrowE a) (immV vs) (λ w, False)%I.
  Proof.
    rewrite ewp_unfold /ewp_pre. rewrite to_of_eff.
    destruct (to_val _) eqn:Habs => //.
    exfalso; eapply to_val_to_eff => //.
    rewrite to_of_eff //.
  Qed.

  
  

  Lemma ewp_strong_mono E1 E2 e f Φf Φ1 Φ2 Ψ1 Ψ2  :
    E1 ⊆ E2 →
    EWP e UNDER f @ E1 <| Ψ1 |> {{ Φ1 ; Φf }} -∗ (∀ x, Ψ1 x ⊑ Ψ2 x)%iprot -∗ (∀ v, Φ1 v ={E2}=∗ Φ2 v) -∗ EWP e UNDER f @ E2 <| Ψ2 |> {{ Φ2 ; Φf }}.
  Proof.
    iIntros (HE) "H #HΨ HΦ". 
    iLöb as "IH" forall (e f Φf E1 E2 HE Φ1 Φ2).
    rewrite !ewp_unfold /ewp_pre /=.
    destruct (to_val e) as [v|] eqn:?.
    { iMod (fupd_mask_mono E1 E2 with "H") as "[H Hf]".
      done.
      iFrame.
      iApply ("HΦ" with "[> -]").
      done. } 
(*      iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). } *)
    destruct (to_eff e) as [eff|] eqn:?.
    { destruct eff.
      all: destruct i.
      all: iDestruct "H" as (Φ) "[HΦ1 H]".
      all: iExists Φ.
      all: iSplitL "HΦ1".
      all: try iApply ("HΨ" with "HΦ1").
      all: iIntros (w) "Hw".
      all: iDestruct ("H" with "Hw") as "H".
      3: done.
      all: iNext.
      all: iApply ("IH" with "[] H"); eauto.
    } 
    iIntros (σ1) "Hσ".
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
    iDestruct ("H" $! σ1) as "H".
    iMod ("H" with "[$]") as "[% H]".
    iModIntro. iSplit; [done|].
    iIntros (e2 ? ? ? Hstep).
    iMod ("H" with "[//]") as "H". iIntros "!> !>".  iMod "H". iModIntro.
    iMod "H" as "[Hσ H]".
    iMod "Hclose".
    (*    iApply (step_fupdN_wand with "[H]"); first by iApply "H". *)
    iModIntro.
    iFrame.
    iApply ("IH" with "[] H"); eauto.
  Qed.

    Lemma fupd_ewp E e f Φf Ψ  Φ :
    TCEq (to_eff e) None ->
    (|={E}=> EWP e UNDER f @ E <| Ψ |>  {{ Φ ; Φf }}) ⊢ EWP e UNDER f @ E <| Ψ |> {{ Φ ; Φf }}.
  Proof.
    rewrite ewp_unfold /ewp_pre. iIntros (He) "H".
    destruct (to_val e) as [v|] eqn:?.
    { by iMod "H". }
    destruct (to_eff e) as [eff|] eqn:?.
    { inversion He. } 
    iIntros (σ1) "Hσ1". iMod "H". by iApply "H".
  Qed. 
  
  Lemma ewp_fupd E e f Φf Ψ Φ : EWP e UNDER f @ E <| Ψ |> {{ v, |={E}=> Φ v ; Φf }} ⊢ EWP e UNDER f @ E <| Ψ |> {{ Φ ; Φf }}.
  Proof. iIntros "H". iApply (ewp_strong_mono E with "H"); auto.
         iIntros (x). iApply iProt_le_refl. 
  Qed.


  (* Is this true anymore? *)
  (*
  Lemma ewp_atomic E1 E2 e Ψ Φ a `{!Atomic (stuckness_to_atomicity NotStuck) e} :
    (|={E1,E2}=> EWP e UNDER f @ E2 <| Ψ |> {{ v, |={E2,E1}=> Φ v ∗ Pred a }}) ⊢ EWP e UNDER f @ E1 <| Ψ |> {{ v, Φ v ∗ Pred a }}.
  Proof.
    iIntros "H". rewrite !ewp_unfold /ewp_pre.
    destruct (to_val e) as [v|] eqn:He.
    { by iDestruct "H" as ">>>$". }
    destruct (to_eff e) as [eff|] eqn:Hf.
    { destruct eff.
      - 
    iIntros (σ1) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
    iModIntro. iIntros (e2 σ2 efs Hstep).
    iApply (step_fupdN_wand with "[H]"); first by iApply "H".
    iIntros ">[Hσ H]". iDestruct "H" as (a') "(H' & H & Hefs)". destruct s.
    - rewrite !wp_unfold /wp_pre. destruct (to_val e2) as [v2|] eqn:He2.
      + iDestruct ("H" with "H'") as ">>[? ?]". iFrame.
        iModIntro. (* iExists _. iFrame. *) iIntros "?".
        iApply wp_unfold. rewrite /wp_pre /= He2. by iFrame.
      + iDestruct ("H" with "H'") as "H".
        iMod ("H" $! _ _ [] with "[$]") as "[H _]". iDestruct "H" as %(? & ? & ? & ? & ?).
        by edestruct (atomic _ _ _ _ _ Hstep).
    - destruct (atomic _ _ _ _ _ Hstep) as [v <-%of_to_val].
      rewrite wp_value_fupd'. iMod ("H" with "[$]") as ">[H H']".
      iModIntro. iFrame "Hσ Hefs". iExists _. iFrame. iIntros "?". iApply wp_value_fupd'. by iFrame.
  Qed. *)

  (** In this stronger version of [wp_step_fupdN], the masks in the
      step-taking fancy update are a bit weird and somewhat difficult to
      use in practice. Hence, we prove it for the sake of completeness,
      but [wp_step_fupdN] is just a little bit weaker, suffices in
      practice and is easier to use.

   See the statement of [wp_step_fupdN] below to understand the use of
   ordinary conjunction here. *)
  Lemma ewp_step_fupdN_strong n f Φf E1 E2 e P Ψ Φ :
    TCEq (to_val e) None → TCEq (to_eff e) None -> E2 ⊆ E1 →
    (∀ σ, state_interp σ
                   ={E1,∅}=∗ ⌜n ≤ 1⌝) ∧
      ((|={E1,E2}=> |={∅}▷=>^n |={E2,E1}=> P) ∗
         EWP e UNDER f @ E2 <| Ψ |> {{ v, P ={E1}=∗ Φ v ; Φf }}) -∗
            EWP e UNDER f @ E1 <| Ψ |>  {{ Φ ; Φf }}.
  Proof.
    destruct n as [|n].
    { iIntros (? ? ?) "/= [_ [HP Hwp]]".
      iApply (ewp_strong_mono with "Hwp") => //.
      iIntros (x); iApply iProt_le_refl. 
      iIntros (v) "H". iFrame. iApply ("H" with "[>HP]"). by do 2 iMod "HP". }
    rewrite !ewp_unfold /ewp_pre /=. iIntros (-> -> ?) "H".
    iIntros (σ1) "Hσ".
    destruct (decide (n ≤ 0)) as [Hn|Hn]; first last.
    { iDestruct "H" as "[Hn _]".
      iDestruct ("Hn" $! σ1) as "Hn".
      iMod ("Hn" with "Hσ") as %?. lia. }
    iDestruct "H" as "[_ [>HP Hwp]]".
    iDestruct ("Hwp" $! σ1) as "Hwp".
    iMod ("Hwp" with "[$]") as "[$ H]".
    iMod "HP".
    iIntros "!>" (e2 s2 l2 i2 Hstep). iMod ("H" $! e2 s2 l2 i2 with "[% //]") as "H".
    iIntros "!>!>". iMod "H". iMod "HP". iModIntro.
    destruct n; last lia.
    simpl.
    iMod "H" as "[H Hwp]".
    iMod "HP".
    iModIntro.
    iFrame.
    iApply (ewp_strong_mono with "Hwp"); [done | set_solver | ].
    iIntros (v) "HΦ". iApply ("HΦ" with "HP").
  Qed.


  (** * Derived rules *)
  Lemma ewp_mono E e f Φf Φ1 Φ2 Ψ1 Ψ2 : (∀ v, Φ1 v ⊢ Φ2 v) →  (∀ v, ⊢ (Ψ1 v ⊑ Ψ2 v)%iprot) -> EWP e UNDER f @ E <| Ψ1 |> {{ Φ1 ; Φf }} ⊢ EWP e UNDER f @ E <| Ψ2 |> {{ Φ2 ; Φf }}.
  Proof.
    iIntros (HΦ HΨ) "H"; iApply (ewp_strong_mono with "H"); auto.
    iIntros (v). iApply HΨ. 
    iIntros (v) "?". iFrame. by iApply HΦ.
  Qed.

   Lemma ewp_mono_post E e f Φf Φ1 Φ2 Ψ : (∀ v, Φ1 v ⊢ Φ2 v) → EWP e UNDER f @ E <| Ψ |> {{ Φ1 ; Φf }} ⊢ EWP e UNDER f @ E <| Ψ |> {{ Φ2 ; Φf }}.
  Proof.
    iIntros (HΦ) "H"; iApply (ewp_strong_mono with "H"); auto.
    iIntros (?); iApply iProt_le_refl. 
    iIntros (v) "?". iFrame. by iApply HΦ.
  Qed.

   Lemma ewp_mono_prot E e f Φf Φ Ψ1 Ψ2 : (∀ v, ⊢ (Ψ1 v ⊑ Ψ2 v)%iprot) -> EWP e UNDER f @ E <| Ψ1 |> {{ Φ ; Φf }} ⊢ EWP e UNDER f @ E <| Ψ2 |> {{ Φ ; Φf }}.
  Proof.
    iIntros (HΨ) "H"; iApply (ewp_strong_mono with "H"); auto.
    iIntros (v). iApply HΨ.
  Qed. 
  
  Lemma ewp_mask_mono E1 E2 e f Φf Ψ  Φ : E1 ⊆ E2 → EWP e UNDER f @ E1 <| Ψ |> {{ Φ ; Φf }} ⊢ EWP e UNDER f @ E2 <| Ψ |> {{ Φ ; Φf }}.
  Proof. iIntros (?) "H"; iApply (ewp_strong_mono with "H"); auto.
         iIntros (?); iApply iProt_le_refl. 
  Qed.

(*
  Global Instance ewp_mono' E e :
    Proper (pointwise_relation _ (⊢) ==> (⊢)) (ewp_def E e).
  Proof. by intros Φ Φ' ?; apply wp_mono. Qed.
  Global Instance wp_flip_mono' s E e :
    Proper (pointwise_relation _ (flip (⊢)) ==> (flip (⊢))) (wp (PROP:=iProp Σ) s E e).
  Proof. by intros Φ Φ' ?; apply wp_mono. Qed. *)

  Lemma ewp_value_fupd E f Φf Ψ  Φ e v : IntoVal e v → EWP e UNDER f @ E <| Ψ |> {{ Φ ; Φf }} ⊣⊢ |={E}=> Φ v ∗ Φf f .
  Proof. intros <-. by apply ewp_value_fupd'. Qed.
  Lemma ewp_value' E f Ψ Φf Φ v : Φ v ∗ Φf f ⊢ EWP (of_val v) UNDER f @ E <| Ψ |> {{ Φ ; Φf }}.
  Proof. rewrite ewp_value_fupd'. auto. Qed.
  Lemma ewp_value E f Ψ Φ Φf e v : IntoVal e v → Φ v ∗ Φf f ⊢ EWP e UNDER f @ E <| Ψ |> {{ Φ ; Φf }}.
  Proof. intros <-. apply ewp_value'. Qed.

  Lemma ewp_effect_sus E f Φf Ψ Φ vs i sh es:
    to_eff es = Some (susE vs i sh) ->
    EWP es UNDER f @ E <| Ψ |> {{ Φ ; Φf }} ⊣⊢ iProt_car (upcl $ Ψ $ SuspendE i) (immV vs) (λ w, ▷ EWP (susfill i sh (of_val w)) UNDER f @ E <| Ψ |> {{ Φ ; Φf }}).
  Proof.
    intros. apply of_to_eff in H. subst. by apply ewp_effect_sus'.
  Qed.

  
  Lemma ewp_effect_sw E f Φf Ψ Φ vs k tf i sh es:
    to_eff es = Some (swE vs k tf i sh) ->
    EWP es UNDER f @ E <| Ψ |> {{ Φ ; Φf }} ⊣⊢ iProt_car (upcl $ Ψ $ SwitchE i) (immV vs)  (λ w, ▷ EWP (swfill i sh (of_val w)) UNDER f @ E <| Ψ |> {{ Φ ; Φf }}).
  Proof.
    intros. apply of_to_eff in H. subst. by apply ewp_effect_sw'.
  Qed.

  Lemma ewp_effect_thr E f Φf Ψ Φ vs i a sh es:
    to_eff es = Some (thrE vs i a sh) ->
    EWP es UNDER f @ E <| Ψ |> {{ Φ ; Φf }} ⊣⊢ iProt_car (upcl $ Ψ $ ThrowE a) (immV vs)  (λ w, False)%I.
  Proof.
    intros. apply of_to_eff in H. subst. by apply ewp_effect_thr'.
  Qed. 

  Lemma ewp_frame_l E e f Φf Ψ Φ R : R ∗ EWP e UNDER f @ E <| Ψ |> {{ Φ ; Φf }} ⊢ EWP e UNDER f @ E <| Ψ |> {{ v, R ∗ Φ v ; Φf }}.
  Proof. iIntros "[? H]". iApply (ewp_strong_mono with "H"); auto with iFrame.
         iIntros (?); iApply iProt_le_refl. 
  Qed.
  Lemma ewp_frame_r E e f Φf Ψ  Φ R : EWP e UNDER f @ E <| Ψ |> {{ Φ ; Φf }} ∗ R ⊢ EWP e UNDER f @ E <| Ψ |> {{ v, Φ v ∗ R ; Φf }}.
  Proof. iIntros "[H ?]". iApply (ewp_strong_mono with "H"); auto with iFrame.
         iIntros (?); iApply iProt_le_refl. 
  Qed.

  (** This lemma states that if we can prove that [n] laters are used in
      the current physical step, then one can perform an n-steps fancy
      update during that physical step. The resources needed to prove the
      bound on [n] are not used up: they can be reused in the proof of
      the WP or in the proof of the n-steps fancy update. In order to
      describe this unusual resource flow, we use ordinary conjunction as
      a premise. *)
  Lemma ewp_step_fupdN n E1 E2 e f Φf P Ψ Φ :
    TCEq (to_val e) None → TCEq (to_eff e) None -> E2 ⊆ E1 →
    (∀ σ, state_interp σ
          ={E1,∅}=∗ ⌜n ≤ 1 ⌝) ∧
      ((|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> P) ∗
      EWP e UNDER f @ E2 <| Ψ |> {{ v, P ={E1}=∗ Φ v ; Φf }}) -∗
                                                    EWP e UNDER f @ E1 <| Ψ |> {{ Φ ; Φf }}.
  Proof.
    iIntros (???) "H". iApply (ewp_step_fupdN_strong with "[H]"); [done|].
    iApply (bi.and_mono_r with "H"). apply bi.sep_mono_l. iIntros "HP".
    iMod fupd_mask_subseteq_emptyset_difference as "H"; [|iMod "HP"]; [set_solver|].
    iMod "H" as "_". replace (E1 ∖ (E1 ∖ E2)) with E2; last first.
    { set_unfold=>x. destruct (decide (x ∈ E2)); naive_solver. }
    iModIntro. iApply (step_fupdN_wand with "HP"). iIntros "H".
    iApply fupd_mask_frame; [|iMod "H"; iModIntro]; [set_solver|].
    by rewrite difference_empty_L (comm_L (∪)) -union_difference_L.
  Qed.
  Lemma ewp_step_fupd E1 E2 e f Φf P Ψ Φ :
    TCEq (to_val e) None → TCEq (to_eff e) None -> E2 ⊆ E1 →
    (|={E1}[E2]▷=> P) -∗ EWP e UNDER f @ E2 <| Ψ |> {{ v, P ={E1}=∗ Φ v ; Φf }} -∗ EWP e UNDER f @ E1 <| Ψ |> {{ Φ ; Φf }}.
  Proof.
    iIntros (???) "HR H".
    iApply (ewp_step_fupdN_strong 1 f Φf E1 E2 with "[-]") => //. iSplit.
    - iIntros (?) "_". iMod (fupd_mask_subseteq ∅) as "_"; [set_solver+|].
      auto with lia.
    - iFrame "H". iMod "HR" as "$". auto.
  Qed.

  Lemma ewp_frame_step_l E1 E2 e f Φf Ψ  Φ R :
    TCEq (to_val e) None → TCEq (to_eff e) None -> E2 ⊆ E1 →
    (|={E1}[E2]▷=> R) ∗ EWP e UNDER f @ E2 <| Ψ |> {{ Φ ; Φf }} ⊢ EWP e UNDER f @ E1 <| Ψ |> {{ v, R ∗ Φ v ; Φf }}.
  Proof.
    iIntros (???) "[Hu Hwp]". iApply (ewp_step_fupd with "Hu"); try done.
    iApply (ewp_mono_post with "Hwp"). by iIntros (?) "$$".
  Qed.
  Lemma ewp_frame_step_r E1 E2 e f Φf Ψ  Φ R :
    TCEq (to_val e) None → TCEq (to_eff e) None -> E2 ⊆ E1 →
    EWP e UNDER f @ E2 <| Ψ |> {{ Φ ; Φf }} ∗ (|={E1}[E2]▷=> R) ⊢ EWP e UNDER f @ E1 <| Ψ |> {{ v, Φ v ∗ R ; Φf }}.
  Proof.
    iIntros (???) "[Hwp Hu]". iApply (ewp_step_fupd with "Hu"); try done.
    iApply (ewp_mono_post with "Hwp"). by iIntros (?) "$$".
  Qed.
  Lemma ewp_frame_step_l' E e f Φf Ψ  Φ R :
    TCEq (to_val e) None → TCEq (to_eff e) None ->  ▷ R ∗ EWP e UNDER f @ E <| Ψ |> {{ Φ ; Φf }} ⊢ EWP e UNDER f @ E <| Ψ |> {{ v, R ∗ Φ v ; Φf }}.
  Proof. iIntros (??) "[??]". iApply (ewp_frame_step_l E E); try iFrame; eauto. Qed.
  Lemma ewp_frame_step_r' E e f Φf Ψ  Φ R :
    TCEq (to_val e) None → TCEq (to_eff e) None -> EWP e UNDER f @ E <| Ψ |> {{ Φ ; Φf }} ∗ ▷ R ⊢ EWP e UNDER f @ E <| Ψ |> {{ v, Φ v ∗ R ; Φf }}.
  Proof. iIntros (??) "[??]". iApply (ewp_frame_step_r E E); try iFrame; eauto. Qed.

  Lemma ewp_wand E e f Φf P Φ Ψ :
    EWP e UNDER f @ E <| P |> {{ Φ ; Φf }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ EWP e UNDER f @ E <| P |>  {{ Ψ ; Φf }}.
  Proof.
    iIntros "Hwp H". iApply (ewp_strong_mono with "Hwp"); auto.
    iIntros (?); iApply iProt_le_refl. 
    iIntros (?) "?". by iApply "H".
  Qed.
  Lemma ewp_wand_l E e f Φf P Φ Ψ :
    (∀ v, Φ v -∗ Ψ v) ∗ EWP e UNDER f @ E <| P |>  {{ Φ ; Φf }} ⊢ EWP e UNDER f @ E <| P |> {{ Ψ ; Φf }}.
  Proof. iIntros "[H Hwp]". iApply (ewp_wand with "Hwp"). done. Qed.
  Lemma ewp_wand_r E e f Φf P Φ Ψ :
    EWP e UNDER f @ E <| P |> {{ Φ ; Φf }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ EWP e UNDER f @ E <| P |> {{ Ψ ; Φf }}.
  Proof. iIntros "[Hwp H]". by iApply (ewp_wand with "Hwp H"). Qed.
  Lemma ewp_frame_wand E e f Φf Ψ Φ R :
    R -∗ EWP e UNDER f @ E <| Ψ |> {{ v, R -∗ Φ v ; Φf }} -∗ EWP e UNDER f @ E <| Ψ |> {{ Φ ; Φf }}.
  Proof.
    iIntros "HR HWP". iApply (ewp_wand with "HWP").
    iIntros (v) "HΦ". iFrame. by iApply "HΦ".
  Qed.

  (* Some lifting lemmas restated and reproved *)
  Local Hint Resolve reducible_no_obs_reducible : core.

     Lemma ewp_lift_step_fupdN E f Φf Ψ Φ e1 :
    to_val e1 = None → to_eff e1 = None ->
    (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜reducible e1 (σ1, f_locs f, f_inst f) ⌝ ∗
    ∀ e2 s2 inst2 locs2, ⌜prim_step e1 (σ1, f_locs f, f_inst f) [] e2 (s2, locs2, inst2) [] ⌝
      ={∅}▷=∗ |={∅,E}=>
      state_interp s2 ∗ EWP e2 UNDER Build_frame locs2 inst2 @ E <| Ψ |> {{ Φ ; Φf }})
      ⊢ EWP e1 UNDER f @ E <| Ψ |> {{ Φ ; Φf }}.
   Proof.
     rewrite ewp_unfold /ewp_pre => -> ->. done. 
   Qed. 
(*     iIntros "H" (σ1) "Hσ".
     iMod ("H" with "Hσ") as "(Hred & H)".
     iFrame.
     done.
     iIntros "!>" (e2 σ2 Hred).
     iSpecialize ("H" $! e2 σ2 Hred).
     iApply (step_fupdN_mono with "H").
     iIntros "H".
     iMod "H" as "[Hσ H]".
     iModIntro. iFrame.
     iDestruct "H" as (a) "[Ha H]".
     iApply ("H" with "Ha").
   Qed. *)

   Lemma ewp_lift_step_fupd E f Φf Ψ Φ e1 :
  to_val e1 = None → to_eff e1 = None ->
  (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜reducible e1 (σ1, f_locs f, f_inst f) ⌝ ∗
    ∀ e2 s2 inst2 locs2, ⌜prim_step e1 (σ1, f_locs f, f_inst f) [] e2 (s2, locs2, inst2) [] ⌝ ={∅}=∗ ▷ |={∅,E}=>
      state_interp s2 ∗ EWP e2 UNDER Build_frame locs2 inst2 @ E <| Ψ |> {{ Φ ; Φf }})
    ⊢ EWP e1 UNDER f @ E <| Ψ |> {{ Φ ; Φf }}.
  Proof.
    intros ? ?. rewrite -ewp_lift_step_fupdN => //. simpl.
    do 16 f_equiv.
    iIntros "H !>". iMod "H". iModIntro. iFrame.
  Qed.


  (** Derived lifting lemmas. *)
  Lemma ewp_lift_step E f Φf Ψ  Φ e1 :
    to_val e1 = None → to_eff e1 = None ->
    (∀ σ1, state_interp σ1 ={E,∅}=∗
    ⌜reducible e1 (σ1, f_locs f, f_inst f) ⌝ ∗
    ▷ ∀ e2 s2 inst2 locs2, ⌜prim_step e1 (σ1, f_locs f, f_inst f) [] e2 (s2, locs2, inst2) []⌝ ={∅,E}=∗
      state_interp s2 ∗ EWP e2 UNDER Build_frame locs2 inst2 @ E <| Ψ |> {{ Φ ; Φf }})
      ⊢ EWP e1 UNDER f @ E <| Ψ |> {{ Φ ; Φf }}.
  Proof.
    iIntros (??) "H". iApply ewp_lift_step_fupd => //. iIntros (?) "Hσ".
    iMod ("H" with "Hσ") as "[$ H]". iIntros "!> * % !> !>". by iApply "H".
  Qed.

  Lemma ewp_lift_pure_step_no_fork (* `{!Inhabited (language.state wasm_lang)} *) E E' Ψ Φ e1 a Φf :
    (∀ σ1, reducible e1 σ1) →
    (∀ κ σ1 e2 σ2, prim_step e1 σ1 κ e2 σ2 [] → κ = [] ∧ σ2 = σ1) →
    (|={E}[E']▷=> ∀ κ e2 σ, ⌜prim_step e1 σ κ e2 σ []⌝ → (EWP e2 UNDER a @ E <| Ψ |> {{ Φ ; Φf }}))
      ⊢ EWP e1 UNDER a @ E <| Ψ |> {{ Φ ; Φf }}.
  Proof.
    iIntros (Hsafe Hstep) "H". iApply ewp_lift_step.
    { specialize (Hsafe (Build_store_record [] [] [] [] [] [] [], [], Build_instance [] [] [] [] [] [])).
      eauto using reducible_not_val. }
    { destruct (to_eff e1) eqn:? => //.
      destruct e.
      1, 3: specialize (Hsafe (Build_store_record [] [] [] [] [] [] [], [], Build_instance [] [] [] [] [] [])).
      1-2: destruct Hsafe as (? & ? & [[??]?] & ? & ? & _).
      1-2: apply eff_head_stuck_reduce in H as [Habs | (? & ? & ? & ? & ? & ? & ? & Habs & _)]; by rewrite Habs in Heqo.
      specialize (Hsafe (Build_store_record [] [] [] [] [] [] (repeat (Cont_hh (Tf [] []) (HH_base [] [])) (S k)), [], Build_instance [] [] [] [] [] [])).
      destruct Hsafe as (? & ? & [[??]?] & ? & ? & _).
      apply eff_head_stuck_reduce in H as [Habs | (? & ? & ? & ? & ? & ? & ? & Habs & Habs' & _)]; rewrite Habs in Heqo => //.
      inversion Heqo; subst.
      rewrite nth_error_repeat in Habs'; last lia.
      done. }
    iIntros (σ1) "Hσ". iMod "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
    { iPureIntro. done. }
    iNext. iIntros (e2 ? ? ? ?).
    destruct (Hstep [] (σ1, f_locs a, f_inst a) e2 (s2, locs2, inst2)) as (_ & Hσ); auto.
    inversion Hσ; subst.
    iMod (state_interp_mono with "Hσ") as "$".
    iMod "Hclose" as "_". iMod "H". iModIntro.
    destruct a.
    iDestruct ("H" with "[//]") as "$". 
  Qed.


  (* Atomic steps don't need any mask-changing business here, one can
     use the generic lemmas here. *)
    Lemma ewp_lift_atomic_step_fupd {E1 E2 Ψ Φ} e1 a b:
    to_val e1 = None → to_eff e1 = None ->
    (∀ σ1, state_interp σ1 ={E1}=∗
    ⌜ reducible e1 (σ1, f_locs a, f_inst a) ⌝ ∗
    ∀ e2 s2 inst2 locs2, ⌜prim_step e1 (σ1, f_locs a, f_inst a) [] e2 (s2, locs2, inst2) []⌝ ={E1}[E2]▷=∗
      state_interp s2  ∗
      from_option Φ False (to_val e2) ∗ b (Build_frame locs2 inst2))
      ⊢ EWP e1 UNDER a @ E1 <| Ψ |> {{ v, Φ v ; b }}.
  Proof.
    iIntros (??) "H".
    iApply (ewp_lift_step_fupd E1 _ _ _ _  e1)=> //; iIntros (σ1) "Hσ1".
    iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose" (e2 ??? ?). iMod "Hclose" as "_".
    iMod ("H" $! e2 s2 with "[#]") as "H"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
    iMod "Hclose" as "_". iMod "H" as "($ & HQ & Hf)".
    destruct (to_val e2) eqn:?; last by iExFalso.
    iApply fupd_mask_intro;[auto|].
    iIntros "Hcls". 
    iApply ewp_value ;[|iFrame]. by apply of_to_val.
  Qed.

  Lemma ewp_lift_atomic_step {E Ψ Φ} e1 a b:
    to_val e1 = None → to_eff e1 = None ->
    (∀ σ1, state_interp σ1 ={E}=∗
    ⌜reducible e1 (σ1, f_locs a, f_inst a) ⌝ ∗
    ▷ ∀ e2 s2 inst2 locs2, ⌜prim_step e1 (σ1, f_locs a, f_inst a) [] e2 (s2, locs2, inst2) []⌝ ={E}=∗
      state_interp s2 ∗
      from_option Φ False (to_val e2) ∗ b (Build_frame locs2 inst2) )
      ⊢ EWP e1 UNDER a @ E <| Ψ |> {{ v, Φ v ; b }}.
  Proof.
    iIntros (??) "H". iApply ewp_lift_atomic_step_fupd. done. done.
    iIntros (?) "?". iMod ("H" with "[$]") as "[$ H]".
    iIntros "!> *". iIntros (Hstep) "!> !>".
    by iApply "H".
  Qed.


  Lemma ewp_lift_pure_det_step_no_fork {E E' Ψ Φ} e1 e2 a Φf :
    (∀ σ1, reducible e1 σ1 ) →
    (∀ σ1 κ e2' σ2, prim_step e1 σ1 κ e2' σ2 []  →
                    κ = [] ∧ σ2 = σ1 ∧ e2' = e2) →
    (|={E}[E']▷=> EWP e2 UNDER a @ E <| Ψ |> {{ Φ ; Φf }}) ⊢ EWP e1 UNDER a @ E <| Ψ |> {{ Φ ; Φf }}.
  Proof.
    iIntros (? Hpuredet) "H". iApply (ewp_lift_pure_step_no_fork E E'); try done.
    { naive_solver. }
    iApply (step_fupd_wand with "H"); iIntros "H".
    iIntros (κ e' σ (_&?&->)%Hpuredet); auto.
  Qed.

  Lemma ewp_pure_step_fupd E E' e1 e2 φ n Ψ  Φ a Φf :
    PureExec φ n e1 e2 →
    φ →
    (|={E}[E']▷=>^n EWP e2 UNDER a @ E <| Ψ |> {{ Φ ; Φf }}) ⊢ EWP e1 UNDER a @ E <| Ψ |> {{ Φ ; Φf }}.
  Proof.
    iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
    iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
    iApply ewp_lift_pure_det_step_no_fork.
    - intros σ. specialize (Hsafe σ). eauto using reducible_not_val.
    - intros.  apply pure_step_det in H as (-> & -> & -> & _).
      done.
    - by iApply (step_fupd_wand with "Hwp").
  Qed.

  Lemma ewp_pure_step_later E e1 e2 φ n Ψ Φ a Φf :
    PureExec φ n e1 e2 →
    φ →
    ▷^n (EWP e2 UNDER a @ E <| Ψ |> {{ Φ ; Φf }}) ⊢ EWP e1 UNDER a @ E <| Ψ |> {{ Φ ; Φf }}.
  Proof.
    intros Hexec ?. rewrite -ewp_pure_step_fupd //. clear Hexec.
    induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
  Qed.

  (* proofmode classes *)
  Global Instance frame_ewp p E e R P f Φf Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (EWP e UNDER f @ E <| P |>  {{ Φ ; Φf }}) (EWP e UNDER f @ E <| P |> {{ Ψ ; Φf }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite ewp_frame_l. apply ewp_mono_post, HR. Qed.

(*  Global Instance is_except_0_ewp E e Ψ Φ : IsExcept0 (EWP e UNDER f @ E <| Ψ |> {{ Φ ; Φf }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_ewp -except_0_fupd -fupd_intro. Qed. *)

(*  Global Instance elim_modal_bupd_ewp p E e P Ψ Φ :
    ElimModal True p false (|==> P) P (EWP e UNDER f @ E <| Ψ |> {{ Φ ; Φf }}) (EWP e UNDER f @ E <| Ψ |> {{ Φ ; Φf }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_ewp.
  Qed. *)

(*  Global Instance elim_modal_fupd_ewp p E e P Ψ Φ :
    ElimModal True p false (|={E}=> P) P (EWP e UNDER f @ E <| Ψ |> {{ Φ ; Φf }}) (EWP e UNDER f @ E <| Ψ |> {{ Φ ; Φf }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_ewp.
  Qed. *)

(*  Global Instance elim_modal_fupd_ewp_atomic p E1 E2 e P Ψ Φ a :
    ElimModal (Atomic (stuckness_to_atomicity NotStuck) e) p false
            (|={E1,E2}=> P) P
            (EWP e UNDER f @ E1 <| Ψ |> {{ v, Φ v ∗ Pred a }})%I (EWP e UNDER f @ E2 <| Ψ |> {{ v, |={E2,E1}=> Φ v ∗ Pred a }})%I | 100.
  Proof.
    intros ?. rewrite bi.intuitionistically_if_elim
                      fupd_frame_r bi.wand_elim_r ewp_atomic. auto.
  Qed. *)

(*  Global Instance add_modal_fupd_ewp E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ ; Φf }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed. *)

(*  Global Instance elim_acc_ewp_atomic {X} E1 E2 α β γ e Ψ Φ a :
    ElimAcc (X:=X) (Atomic (stuckness_to_atomicity NotStuck) e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (EWP e UNDER f @ E1 <| Ψ |> {{ v, Φ v ∗ Pred a }})%I
            (λ x, EWP e UNDER f @ E2 <| Ψ |> {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) ∗ Pred a }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[H [H' $]]". iApply "H'". by iApply "Hclose".
  Qed. 

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ ; Φf }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed. *)


End wp.



