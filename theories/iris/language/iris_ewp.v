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
  
Opaque weakestpre.state_interp.
Opaque num_laters_per_step.

Definition ewp_pre `{!wasmG Σ} :
  (coPset -d> expr -d>
     (effect_identifier -d> iProt Σ) -d>
     (val -d> iPropO Σ) -d> iPropO Σ) →
  (coPset -d> expr -d>
     (effect_identifier -d> iProt Σ) -d>
     (val -d> iPropO Σ) -d> iPropO Σ)
  := λ ewp E e₁ Ψ Φ,
  match to_val e₁ with
  | Some v =>
      |={E}=> Φ v
  | None =>
      match to_eff e₁ with
      | Some (thrE vs i a sh) =>
      (*    Ψ (ThrowE a) (immV vs)
       (* Hmmm have value instead of val to avoid immV? *) *)
          ∃ f, ↪[frame] f ∗ (↪[frame] f -∗ iProt_car (upcl (Ψ $ ThrowE a)) (immV vs) (λ w, False)%I)
      | Some (susE vs i sh) =>
          ∃ f, ↪[frame] f ∗ (↪[frame] f -∗ iProt_car (upcl (Ψ $ SuspendE i)) (immV vs) (λ w, ▷ ewp E (susfill i sh (of_val w)) Ψ Φ))
      | Some (swE vs k tf i sh) =>
          ∃ f, ↪[frame] f ∗ (↪[frame] f -∗ iProt_car (upcl (Ψ $ SwitchE i)) (immV vs) (λ w, ▷ ewp E (swfill i sh (of_val w)) Ψ Φ))
      | None =>
          ∀ σ₁ ns κ κs nt,
            weakestpre.state_interp σ₁ ns (κ ++ κs) nt ={E,∅}=∗
              ⌜ reducible e₁ σ₁ ⌝ ∗  
              ∀ e₂ σ₂, ⌜ prim_step e₁ σ₁ κ e₂ σ₂ [] ⌝
                ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
                weakestpre.state_interp σ₂ (S ns) κs nt ∗ ∃ (f : frame), ↪[frame] f ∗ (↪[frame] f -∗ ewp E e₂ Ψ Φ)
      end
  end%I.

Local Instance ewp_pre_contractive `{!wasmG Σ} : Contractive ewp_pre.
Proof.
  rewrite /ewp_pre=> n ewp ewp' Hwp E e Ψ Φ.
  do 8 f_equiv; try by intros => ?; f_contractive; apply Hwp.
  do 12 (f_contractive || f_equiv).
  induction num_laters_per_step as [|k IH]; simpl.
  - repeat (f_contractive || f_equiv); apply Hwp.
  - do 3 f_equiv. by apply IH.
Qed.
Definition ewp_def `{!wasmG Σ} :
  coPset -d> expr -d>
    (effect_identifier -d> iProt Σ) -d>
    (val -d> iPropO Σ) -d> iPropO Σ :=
  fixpoint ewp_pre.
Definition ewp_aux `{!wasmG Σ} : seal ewp_def. Proof. by eexists. Qed.
Definition ewp_eq `{!wasmG Σ} := ewp_aux.(seal_eq).
Definition ewp' `{!wasmG Σ} := ewp_aux.(unseal).



(* -------------------------------------------------------------------------- *)
(** Non-expansiveness. *)

Lemma ewp_unfold `{!wasmG Σ} E e Ψ Φ :
  ewp_def E e Ψ Φ ⊣⊢ ewp_pre ewp_def E e Ψ Φ.
Proof. by rewrite /ewp_def; apply (fixpoint_unfold ewp_pre). Qed.

Global Instance ewp_ne `{!wasmG Σ} E e n :
  Proper ((dist n) ==> (dist n) ==> (dist n)) (ewp_def E e).
Proof.
  revert e.
  induction (lt_wf n) as [n _ IH]=> e Ψ1 Ψ1' HΨ1 Φ Φ' HΦ.
  rewrite !ewp_unfold /ewp_pre /upcl. simpl.
  f_equiv. { by f_equiv. }
  f_equiv.
  - f_equiv.
    + f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
      * f_equiv.
        apply IProt_ne.
        f_equiv.
        apply HΨ1.
      * f_equiv. intros ?. do 2 (f_contractive || f_equiv).
        apply IH; try lia; eapply dist_le; eauto with lia.
    + f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
      * f_equiv. apply IProt_ne. f_equiv. apply HΨ1.
      * f_equiv. intros ?. do 2 (f_contractive || f_equiv).
        apply IH; try lia; eapply dist_le; eauto with lia.
    + f_equiv. f_equiv. f_equiv. f_equiv. f_equiv. f_equiv.
      f_equiv. apply IProt_ne. f_equiv. apply HΨ1. 
  - do 4 f_equiv. do 14 (f_contractive || f_equiv).
    induction num_laters_per_step as [| k IH']; simpl.
    + do 9 (f_contractive || f_equiv).
      apply IH; try lia; eapply dist_le; eauto with lia.
    + do 3 f_equiv. by apply IH'. 
Qed.

Global Instance ewp_proper `{!wasmG Σ} E e :
  Proper ((≡) ==> (≡) ==> (≡)) (ewp_def E e).
Proof.
  intros Ψ1 Ψ1' ? Φ Φ' ?.
  by apply equiv_dist=>n; apply ewp_ne; apply equiv_dist.
Qed.


(* -------------------------------------------------------------------------- *)
(** Notation. *)

Notation "'EWP' e @ E {{ Φ } }" :=
  (ewp_def E e%E (λ _, iProt_bottom) Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E <| Ψ |>  {{ Φ } }" :=
  (ewp_def E e%E Ψ Φ)
  (at level 20, e, Ψ, Φ at level 200,
    format "'[' 'EWP'  e  '/' '[          ' @  E  <|  Ψ  |>  {{  Φ  } } ']' ']'") : bi_scope.



(*Notation "'EWP' e @ E .{| Ψ '|' '}'  {{ Φ } }" :=
  (ewp_def E e%E (λ _, iProt_bottom) Ψ (λ _ _, False%I) Φ)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  .{|  Ψ  '|' '}'  {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E <| Ψ1 '|' '>' {| Ψ2 '|' '}'  {{ Φ } }" :=
  (ewp_def E e%E Ψ1 Ψ2 (λ _ _, False%I) Φ)
  (at level 20, e, Ψ1, Ψ2, Φ at level 200,
    format "'[' 'EWP'  e  '/' '[          ' @  E  <|  Ψ1  '|' '>'  {|  Ψ2  '|' '}'  {{  Φ  } } ']' ']'") : bi_scope.

Notation "'EWP' e @ E <{ Ψ '}' '>' {{ Φ } }" :=
  (ewp_def E e%E (λ _, iProt_bottom) (λ _, iProt_bottom) Ψ Φ)
  (at level 20, e, Φ, Ψ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  <{ Ψ '}' '>' {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E <| Ψ '|' '>' <{ Ψ2 '}' '>'  {{ Φ } }" :=
  (ewp_def E e%E Ψ (λ _, iProt_bottom) Ψ2 Φ)
  (at level 20, e, Ψ, Ψ2, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  <|  Ψ  '|' '>' <{ Ψ2 '}' '>'  {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E .{| Ψ '|' '}' <{ Ψ2 '}' '>' {{ Φ } }" :=
  (ewp_def E e%E (λ _, iProt_bottom) Ψ Ψ2 Φ)
  (at level 20, e, Ψ, Ψ2, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  .{|  Ψ  '|' '}' <{ Ψ2 '}' '>' {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E <| Ψ1 '|' '>' {| Ψ2 '|' '}' <{ Ψ3 '}' '>'  {{ Φ } }" :=
  (ewp_def E e%E Ψ1 Ψ2 Ψ3 Φ)
  (at level 20, e, Ψ1, Ψ2, Ψ3, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  <|  Ψ1  '|' '>'  {|  Ψ2  '|' '}'  <{ Ψ3 '}' '>' {{  Φ  } } ']' ']'") : bi_scope. *)

(* Postcondition includes binder. *)

Notation "'EWP' e @ E {{ v , Φ } }" :=
  (ewp_def E e%E (λ _, iProt_bottom) (λ v, Φ))
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  {{ v , Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E <| Ψ |>  {{ v , Φ } }" :=
  (ewp_def E e%E Ψ (λ v, Φ))
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  <| Ψ |>  {{  v , Φ  } } ']' ']'") : bi_scope.

(* Notation "'EWP' e @ E .{| Ψ '|' '}'  {{ v , Φ } }" :=
  (ewp_def E e%E (λ _, iProt_bottom) Ψ (λ _ _, False%I) (λ v, Φ))
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  .{|  Ψ  '|' '}'  {{ v , Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E <| Ψ1 '|' '>' {| Ψ2 '|' '}'  {{ v , Φ } }" :=
  (ewp_def E e%E Ψ1 Ψ2 (λ _ _, False%I) (λ v, Φ))
  (at level 20, e, Ψ1, Ψ2, Φ at level 200,
    format "'[' 'EWP'  e  '/' '[          ' @  E  <|  Ψ1  '|' '>'  {|  Ψ2  '|' '}'  {{  v , Φ  } } ']' ']'") : bi_scope.

Notation "'EWP' e @ E <{ Ψ '}' '>' {{ v , Φ } }" :=
  (ewp_def E e%E (λ _, iProt_bottom) (λ _, iProt_bottom) Ψ (λ v, Φ))
  (at level 20, e, Φ, Ψ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  <{ Ψ '}' '>' {{  v , Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E <| Ψ '|' '>' <{ Ψ2 '}' '>'  {{ v , Φ } }" :=
  (ewp_def E e%E Ψ (λ _, iProt_bottom) Ψ2 (λ v, Φ))
  (at level 20, e, Ψ, Ψ2, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  <|  Ψ  '|' '>' <{ Ψ2 '}' '>'  {{  v , Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E .{| Ψ '|' '}' <{ Ψ2 '}' '>' {{ v , Φ } }" :=
  (ewp_def E e%E (λ _, iProt_bottom) Ψ Ψ2 (λ v, Φ))
  (at level 20, e, Ψ, Ψ2, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  .{|  Ψ  '|' '}' <{ Ψ2 '}' '>' {{  v , Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E <| Ψ1 '|' '>' {| Ψ2 '|' '}' <{ Ψ3 '}' '>'  {{ v , Φ } }" :=
  (ewp_def E e%E Ψ1 Ψ2 Ψ3 (λ v, Φ))
  (at level 20, e, Ψ1, Ψ2, Ψ3, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  <|  Ψ1  '|' '>'  {|  Ψ2  '|' '}'  <{ Ψ3 '}' '>' {{  v , Φ  } } ']' ']'") : bi_scope. *)

(* Mask is implicitly specified by ⊤. *)

Notation "'EWP' e {{ v , Φ } }" :=
  (ewp_def ⊤ e%E (λ _, iProt_bottom) (λ v, Φ))
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' {{ v , Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e <| Ψ |>  {{ v , Φ } }" :=
  (ewp_def ⊤ e%E Ψ (λ v, Φ))
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  <|  Ψ  |>  {{  v , Φ  } } ']' ']'") : bi_scope.
(* Notation "'EWP' e  .{| Ψ '|' '}'  {{ v , Φ } }" :=
  (ewp_def ⊤ e%E (λ _, iProt_bottom) Ψ (λ _ _, False%I) (λ v, Φ))
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' .{|  Ψ  '|' '}'  {{ v , Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e <| Ψ1 '|' '>' {| Ψ2 '|' '}'  {{ v , Φ } }" :=
  (ewp_def ⊤ e%E Ψ1 Ψ2 (λ _ _, False%I) (λ v, Φ))
  (at level 20, e, Ψ1, Ψ2, Φ at level 200,
    format "'[' 'EWP'  e  '/' '[          '  <|  Ψ1  '|' '>'  {|  Ψ2  '|' '}'  {{  v , Φ  } } ']' ']'") : bi_scope.

Notation "'EWP' e <{ Ψ '}' '>' {{ v , Φ } }" :=
  (ewp_def ⊤ e%E (λ _, iProt_bottom) (λ _, iProt_bottom) Ψ (λ v, Φ))
  (at level 20, e, Φ, Ψ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  <{ Ψ '}' '>' {{  v , Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e <| Ψ '|' '>' <{ Ψ2 '}' '>'  {{ v , Φ } }" :=
  (ewp_def ⊤ e%E Ψ (λ _, iProt_bottom) Ψ2 (λ v, Φ))
  (at level 20, e, Ψ, Ψ2, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  <|  Ψ  '|' '>' <{ Ψ2 '}' '>'  {{  v , Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e .{| Ψ '|' '}' <{ Ψ2 '}' '>' {{ v , Φ } }" :=
  (ewp_def ⊤ e%E (λ _, iProt_bottom) Ψ Ψ2 (λ v, Φ))
  (at level 20, e, Ψ, Ψ2, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  .{|  Ψ  '|' '}' <{ Ψ2 '}' '>' {{  v , Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e <| Ψ1 '|' '>' {| Ψ2 '|' '}' <{ Ψ3 '}' '>'  {{ v , Φ } }" :=
  (ewp_def ⊤ e%E Ψ1 Ψ2 Ψ3 (λ v, Φ))
  (at level 20, e, Ψ1, Ψ2, Ψ3, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  <|  Ψ1  '|' '>'  {|  Ψ2  '|' '}'  <{ Ψ3 '}' '>' {{  v , Φ  } } ']' ']'") : bi_scope.
*)

(* No binder and no mask. *)
Notation "'EWP' e {{ Φ } }" :=
  (ewp_def ⊤ e%E (λ _, iProt_bottom) Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e <| Ψ |>  {{ Φ } }" :=
  (ewp_def ⊤ e%E Ψ Φ)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  <|  Ψ  |>  {{  Φ  } } ']' ']'") : bi_scope.
(* Notation "'EWP' e .{| Ψ '|' '}'  {{ Φ } }" :=
  (ewp_def ⊤ e%E (λ _, iProt_bottom) Ψ (λ _ _, False%I) Φ)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  .{|  Ψ  '|' '}'  {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e <| Ψ1 '|' '>' {| Ψ2 '|' '}'  {{ Φ } }" :=
  (ewp_def ⊤ e%E Ψ1 Ψ2 (λ _ _, False%I) Φ)
  (at level 20, e, Ψ1, Ψ2, Φ at level 200,
    format "'[' 'EWP'  e  '/' '[          '   <|  Ψ1  '|' '>'  {|  Ψ2  '|' '}'  {{  Φ  } } ']' ']'") : bi_scope.

Notation "'EWP' e <{ Ψ '}' '>' {{ Φ } }" :=
  (ewp_def ⊤ e%E (λ _, iProt_bottom) (λ _, iProt_bottom) Ψ Φ)
  (at level 20, e, Φ, Ψ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  <{ Ψ '}' '>' {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e <| Ψ '|' '>' <{ Ψ2 '}' '>'  {{ Φ } }" :=
  (ewp_def ⊤ e%E Ψ (λ _, iProt_bottom) Ψ2 Φ)
  (at level 20, e, Ψ, Ψ2, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  <|  Ψ  '|' '>' <{ Ψ2 '}' '>'  {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e .{| Ψ '|' '}' <{ Ψ2 '}' '>' {{ Φ } }" :=
  (ewp_def ⊤ e%E (λ _, iProt_bottom) Ψ Ψ2 Φ)
  (at level 20, e, Ψ, Ψ2, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  .{|  Ψ  '|' '}' <{ Ψ2 '}' '>' {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e <| Ψ1 '|' '>' {| Ψ2 '|' '}' <{ Ψ3 '}' '>'  {{ Φ } }" :=
  (ewp_def ⊤ e%E Ψ1 Ψ2 Ψ3 Φ)
  (at level 20, e, Ψ1, Ψ2, Ψ3, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  <|  Ψ1  '|' '>'  {|  Ψ2  '|' '}'  <{ Ψ3 '}' '>' {{  Φ  } } ']' ']'") : bi_scope.

*)
(* Tests *)
(* Check (λ Σ es P Q, EWP es <| λ _, iProt_bottom |> {{ λ v, True }})%I.
 Check (λ Σ es P Q, EWP es <| λ i w, λne Φ, ⌜ i = SuspendE (Mk_tagidx 1) ⌝ ∗ ((>> v >> ! v {{ P }} ; << w << ? w {{ Q }})%iprot w Φ) |> {{ λ v, True }})%I. *)


Section wp.
  Context `{!wasmG Σ}.

  Lemma ewp_value_fupd' E Ψ Φ v : EWP of_val v @  E <| Ψ |> {{ Φ }} ⊣⊢ |={E}=> Φ v.
  Proof. rewrite ewp_unfold /ewp_pre. rewrite to_of_val. auto. Qed.

  Lemma ewp_effect_sus' E Ψ Φ vs i sh : EWP of_eff (susE vs i sh) @ E <| Ψ |> {{ Φ }} ⊣⊢ ∃ f, ↪[frame] f ∗ (↪[frame] f -∗ iProt_car (upcl (Ψ $ SuspendE i)) (immV vs) (λ w, ▷ EWP (susfill i sh (of_val w)) @ E <| Ψ |> {{ Φ }})).
  Proof.
    rewrite ewp_unfold /ewp_pre. rewrite to_of_eff.
    destruct (to_val _) eqn:Habs => //.
    exfalso; eapply to_val_to_eff => //.
    rewrite to_of_eff //.
  Qed.

  Lemma ewp_effect_sw' E Ψ Φ vs k tf i sh : EWP of_eff (swE vs k tf i sh) @ E <| Ψ |> {{ Φ }} ⊣⊢  ∃ f, ↪[frame] f ∗ (↪[frame] f -∗ iProt_car (upcl (Ψ $ SwitchE i)) (immV vs) (λ w, ▷ EWP (swfill i sh (of_val w)) @ E <| Ψ |> {{ Φ }})).
  Proof.
    rewrite ewp_unfold /ewp_pre. rewrite to_of_eff.
    destruct (to_val _) eqn:Habs => //.
    exfalso; eapply to_val_to_eff => //.
    rewrite to_of_eff //.
  Qed.


   Lemma ewp_effect_thr' E Ψ Φ vs i a sh : EWP of_eff (thrE vs i a sh) @ E <| Ψ |> {{ Φ }} ⊣⊢    ∃ f, ↪[frame] f ∗ (↪[frame] f -∗ iProt_car (upcl (Ψ $ ThrowE a)) (immV vs) (λ w, False)%I).
  Proof.
    rewrite ewp_unfold /ewp_pre. rewrite to_of_eff.
    destruct (to_val _) eqn:Habs => //.
    exfalso; eapply to_val_to_eff => //.
    rewrite to_of_eff //.
  Qed.

  
  

  Lemma ewp_strong_mono E1 E2 e Φ1 Φ2 Ψ1 Ψ2 :
    E1 ⊆ E2 →
    EWP e @ E1 <| Ψ1 |> {{ Φ1 }} -∗ (∀ x, Ψ1 x ⊑ Ψ2 x)%iprot -∗ (∀ v, Φ1 v ={E2}=∗ Φ2 v) -∗ EWP e @ E2 <| Ψ2 |> {{ Φ2 }}.
  Proof.
    iIntros (HE) "H #HΨ HΦ".
    iLöb as "IH" forall (e E1 E2 HE Φ1 Φ2).
    rewrite !ewp_unfold /ewp_pre /=.
    destruct (to_val e) as [v|] eqn:?.
    { iApply ("HΦ" with "[> -]"). by iApply (fupd_mask_mono E1 _). }
    destruct (to_eff e) as [eff|] eqn:?.
    { destruct eff.
      all: iDestruct "H" as (f) "[Hf H]".
      all: iFrame.
      all: iIntros "Hf".
      all: iDestruct ("H" with "Hf") as "H".
      all: iDestruct "H" as (Φ) "[HΦ1 H]".
      all: iExists Φ.
      all: iSplitL "HΦ1".
      all: try iApply "HΨ".
      all: try iExact "HΦ1".
      all: iIntros (w) "Hw".
      all: iDestruct ("H" with "Hw") as "H".
      3: done.
      all: iNext.
      all: iApply ("IH" with "[] H"); eauto.
    } 
    iIntros (σ1 ns κ κs nt) "Hσ".
    iMod (fupd_mask_subseteq E1) as "Hclose"; first done.
    iDestruct ("H" $! σ1 ns κ κs nt) as "H".
    iMod ("H" with "[$]") as "[% H]".
    iModIntro. iSplit; [done|].
    iIntros (e2 σ2 Hstep).
    iMod ("H" with "[//]") as "H". iIntros "!> !>".  iMod "H". iModIntro.
    iMod "H" as "[Hσ H]".
    iMod "Hclose".
    (*    iApply (step_fupdN_wand with "[H]"); first by iApply "H". *)
    iModIntro.
    iFrame.
    iDestruct "H" as (f) "[Hf Hnext]".
    iExists f.
    iFrame.
    iIntros "Hf".
    iDestruct ("Hnext" with "Hf") as "H".
    iApply ("IH" with "[] H"); eauto.
  Qed.

    Lemma fupd_ewp E e Ψ Φ :
    TCEq (to_eff e) None ->
    (|={E}=> EWP e @ E <| Ψ |> {{ Φ }}) ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
  Proof.
    rewrite ewp_unfold /ewp_pre. iIntros (He) "H".
    destruct (to_val e) as [v|] eqn:?.
    { by iMod "H". }
    destruct (to_eff e) as [eff|] eqn:?.
    { inversion He. } 
    iIntros (σ1 ns κ κs nt) "Hσ1". iMod "H". by iApply "H".
  Qed. 
  
  Lemma ewp_fupd E e Ψ Φ : EWP e @ E <| Ψ |> {{ v, |={E}=> Φ v }} ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
  Proof. iIntros "H". iApply (ewp_strong_mono E with "H"); auto.
         iIntros (x). iApply iProt_le_refl.
  Qed.


  (* Is this true anymore? *)
  (*
  Lemma ewp_atomic E1 E2 e Ψ Φ a `{!Atomic (stuckness_to_atomicity NotStuck) e} :
    (|={E1,E2}=> EWP e @ E2 <| Ψ |> {{ v, |={E2,E1}=> Φ v ∗ Pred a }}) ⊢ EWP e @ E1 <| Ψ |> {{ v, Φ v ∗ Pred a }}.
  Proof.
    iIntros "H". rewrite !ewp_unfold /ewp_pre.
    destruct (to_val e) as [v|] eqn:He.
    { by iDestruct "H" as ">>>$". }
    destruct (to_eff e) as [eff|] eqn:Hf.
    { destruct eff.
      - 
    iIntros (σ1 ns κ κs nt) "Hσ". iMod "H". iMod ("H" $! σ1 with "Hσ") as "[$ H]".
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
  Lemma ewp_step_fupdN_strong n E1 E2 e P Ψ Φ :
    TCEq (to_val e) None → TCEq (to_eff e) None -> E2 ⊆ E1 →
    (∀ σ ns κs nt, weakestpre.state_interp σ ns κs nt
                   ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
      ((|={E1,E2}=> |={∅}▷=>^n |={E2,E1}=> P) ∗
         EWP e @ E2 <| Ψ |> {{ v, P ={E1}=∗ Φ v }}) -∗
            EWP e @ E1 <| Ψ |> {{ Φ }}.
  Proof.
    destruct n as [|n].
    { iIntros (? ? ?) "/= [_ [HP Hwp]]".
      iApply (ewp_strong_mono with "Hwp") => //.
      iIntros (x); iApply iProt_le_refl.
      iIntros (v) "H". iFrame. iApply ("H" with "[>HP]"). by do 2 iMod "HP". }
    rewrite !ewp_unfold /ewp_pre /=. iIntros (-> -> ?) "H".
    iIntros (σ1 ns κ κs nt) "Hσ".
    destruct (decide (n ≤ num_laters_per_step ns)) as [Hn|Hn]; first last.
    { iDestruct "H" as "[Hn _]".
      iDestruct ("Hn" $! σ1 ns (κ ++ κs) nt) as "Hn".
      iMod ("Hn" with "Hσ") as %?. lia. }
    iDestruct "H" as "[_ [>HP Hwp]]".
    iDestruct ("Hwp" $! σ1 ns κ κs nt) as "Hwp".
    iMod ("Hwp" with "[$]") as "[$ H]".
    iMod "HP".
    iIntros "!>" (e2 σ2 Hstep). iMod ("H" $! e2 σ2 with "[% //]") as "H".
    iIntros "!>!>". iMod "H". iMod "HP". iModIntro.
    revert n Hn. generalize (num_laters_per_step ns)=>n0 n Hn.
    iInduction n as [|n] "IH" forall (n0 Hn).
    - iApply (step_fupdN_wand with "H").
      iIntros "H".
      iMod "H" as "(Hσ & %f & Hf & H)".
      iMod "HP".
      iModIntro. iFrame.
      iIntros "Hf".
      iDestruct ("H" with "Hf") as "H".
      iApply (ewp_strong_mono with "H"); [done|set_solver|].
      iIntros (v) "HΦ".  iApply ("HΦ" with "HP").
    - destruct n0 as [|n0]; [lia|]=> /=. iMod "HP".
      iMod "H". iIntros "!> !>". iMod "HP". iMod "H".
      iModIntro. iApply ("IH" with "[] HP H").
      auto with lia.
  Qed.


  (** * Derived rules *)
  Lemma ewp_mono E e Φ1 Φ2 Ψ1 Ψ2 : (∀ v, Φ1 v ⊢ Φ2 v) → (∀ v, ⊢ (Ψ1 v ⊑ Ψ2 v)%iprot) -> EWP e @ E <| Ψ1 |> {{ Φ1 }} ⊢ EWP e @ E <| Ψ2 |> {{ Φ2 }}.
  Proof.
    iIntros (HΦ HΨ) "H"; iApply (ewp_strong_mono with "H"); auto.
    iIntros (v). iApply HΨ.
    iIntros (v) "?". iFrame. by iApply HΦ.
  Qed.

   Lemma ewp_mono_post E e Φ1 Φ2 Ψ : (∀ v, Φ1 v ⊢ Φ2 v) → EWP e @ E <| Ψ |> {{ Φ1 }} ⊢ EWP e @ E <| Ψ |> {{ Φ2 }}.
  Proof.
    iIntros (HΦ) "H"; iApply (ewp_strong_mono with "H"); auto.
    iIntros (?); iApply iProt_le_refl.
    iIntros (v) "?". iFrame. by iApply HΦ.
  Qed.

   Lemma ewp_mono_prot E e Φ Ψ1 Ψ2 : (∀ v, ⊢ (Ψ1 v ⊑ Ψ2 v)%iprot) -> EWP e @ E <| Ψ1 |> {{ Φ }} ⊢ EWP e @ E <| Ψ2 |> {{ Φ }}.
  Proof.
    iIntros (HΨ) "H"; iApply (ewp_strong_mono with "H"); auto.
    iIntros (v). iApply HΨ.
  Qed.
  
  Lemma ewp_mask_mono E1 E2 e Ψ Φ : E1 ⊆ E2 → EWP e @ E1 <| Ψ |> {{ Φ }} ⊢ EWP e @ E2 <| Ψ |> {{ Φ }}.
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

  Lemma ewp_value_fupd E Ψ Φ e v : IntoVal e v → EWP e @ E <| Ψ |> {{ Φ }} ⊣⊢ |={E}=> Φ v.
  Proof. intros <-. by apply ewp_value_fupd'. Qed.
  Lemma ewp_value' E Ψ Φ v : Φ v ⊢ EWP (of_val v) @ E <| Ψ |> {{ Φ }}.
  Proof. rewrite ewp_value_fupd'. auto. Qed.
  Lemma ewp_value E Ψ Φ e v : IntoVal e v → Φ v ⊢ EWP e @ E <| Ψ |> {{ Φ }}.
  Proof. intros <-. apply ewp_value'. Qed.

  Lemma ewp_effect_sus E Ψ Φ vs i sh es:
    to_eff es = Some (susE vs i sh) ->
    EWP es @ E <| Ψ |> {{ Φ }} ⊣⊢ ∃ f, ↪[frame] f ∗  (↪[frame] f -∗ iProt_car (upcl (Ψ $ SuspendE i)) (immV vs) (λ w, ▷ EWP (susfill i sh (of_val w)) @ E <| Ψ |> {{ Φ }})).
  Proof.
    intros. apply of_to_eff in H. subst. by apply ewp_effect_sus'.
  Qed.

  
  Lemma ewp_effect_sw E Ψ Φ vs k tf i sh es:
    to_eff es = Some (swE vs k tf i sh) ->
    EWP es @ E <| Ψ |> {{ Φ }} ⊣⊢  ∃ f, ↪[frame] f ∗ (↪[frame] f -∗ iProt_car (upcl (Ψ $ SwitchE i)) (immV vs) (λ w, ▷ EWP (swfill i sh (of_val w)) @ E <| Ψ |> {{ Φ }})).
  Proof.
    intros. apply of_to_eff in H. subst. by apply ewp_effect_sw'.
  Qed.

  Lemma ewp_effect_thr E Ψ Φ vs i a sh es:
    to_eff es = Some (thrE vs i a sh) ->
    EWP es @ E <| Ψ |> {{ Φ }} ⊣⊢    ∃ f, ↪[frame] f ∗ (↪[frame] f -∗ iProt_car (upcl (Ψ $ ThrowE a)) (immV vs) (λ w, False)%I).
  Proof.
    intros. apply of_to_eff in H. subst. by apply ewp_effect_thr'.
  Qed. 

  Lemma ewp_frame_l E e Ψ Φ R : R ∗ EWP e @ E <| Ψ |> {{ Φ }} ⊢ EWP e @ E <| Ψ |> {{ v, R ∗ Φ v }}.
  Proof. iIntros "[? H]". iApply (ewp_strong_mono with "H"); auto with iFrame.
         iIntros (?); iApply iProt_le_refl.
  Qed.
  Lemma ewp_frame_r E e Ψ Φ R : EWP e @ E <| Ψ |> {{ Φ }} ∗ R ⊢ EWP e @ E <| Ψ |> {{ v, Φ v ∗ R }}.
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
  Lemma ewp_step_fupdN n E1 E2 e P Ψ Φ :
    TCEq (to_val e) None → TCEq (to_eff e) None -> E2 ⊆ E1 →
    (∀ σ ns κs nt, weakestpre.state_interp σ ns κs nt
                   ={E1,∅}=∗ ⌜n ≤ S (num_laters_per_step ns)⌝) ∧
      ((|={E1∖E2,∅}=> |={∅}▷=>^n |={∅,E1∖E2}=> P) ∗
      EWP e @ E2 <| Ψ |> {{ v, P ={E1}=∗ Φ v }}) -∗
                                                    EWP e @ E1 <| Ψ |> {{ Φ }}.
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
  Lemma ewp_step_fupd E1 E2 e P Ψ Φ :
    TCEq (to_val e) None → TCEq (to_eff e) None -> E2 ⊆ E1 →
    (|={E1}[E2]▷=> P) -∗ EWP e @ E2 <| Ψ |> {{ v, P ={E1}=∗ Φ v }} -∗ EWP e @ E1 <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (???) "HR H".
    iApply (ewp_step_fupdN_strong 1 E1 E2 with "[-]") => //. iSplit.
    - iIntros (????) "_". iMod (fupd_mask_subseteq ∅) as "_"; [set_solver+|].
      auto with lia.
    - iFrame "H". iMod "HR" as "$". auto.
  Qed.

  Lemma ewp_frame_step_l E1 E2 e Ψ Φ R :
    TCEq (to_val e) None → TCEq (to_eff e) None -> E2 ⊆ E1 →
    (|={E1}[E2]▷=> R) ∗ EWP e @ E2 <| Ψ |> {{ Φ }} ⊢ EWP e @ E1 <| Ψ |> {{ v, R ∗ Φ v }}.
  Proof.
    iIntros (???) "[Hu Hwp]". iApply (ewp_step_fupd with "Hu"); try done.
    iApply (ewp_mono_post with "Hwp"). by iIntros (?) "$$".
  Qed.
  Lemma ewp_frame_step_r E1 E2 e Ψ Φ R :
    TCEq (to_val e) None → TCEq (to_eff e) None -> E2 ⊆ E1 →
    EWP e @ E2 <| Ψ |> {{ Φ }} ∗ (|={E1}[E2]▷=> R) ⊢ EWP e @ E1 <| Ψ |> {{ v, Φ v ∗ R }}.
  Proof.
    iIntros (???) "[Hwp Hu]". iApply (ewp_step_fupd with "Hu"); try done.
    iApply (ewp_mono_post with "Hwp"). by iIntros (?) "$$".
  Qed.
  Lemma ewp_frame_step_l' E e Ψ Φ R :
    TCEq (to_val e) None → TCEq (to_eff e) None ->  ▷ R ∗ EWP e @ E <| Ψ |> {{ Φ }} ⊢ EWP e @ E <| Ψ |> {{ v, R ∗ Φ v }}.
  Proof. iIntros (??) "[??]". iApply (ewp_frame_step_l E E); try iFrame; eauto. Qed.
  Lemma ewp_frame_step_r' E e Ψ Φ R :
    TCEq (to_val e) None → TCEq (to_eff e) None -> EWP e @ E <| Ψ |> {{ Φ }} ∗ ▷ R ⊢ EWP e @ E <| Ψ |> {{ v, Φ v ∗ R }}.
  Proof. iIntros (??) "[??]". iApply (ewp_frame_step_r E E); try iFrame; eauto. Qed.

  Lemma ewp_wand E e P Φ Ψ :
    EWP e @ E <| P |> {{ Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ EWP e @ E <| P |> {{ Ψ }}.
  Proof.
    iIntros "Hwp H". iApply (ewp_strong_mono with "Hwp"); auto.
    iIntros (?); iApply iProt_le_refl.
    iIntros (?) "?". by iApply "H".
  Qed.
  Lemma ewp_wand_l E e P Φ Ψ :
    (∀ v, Φ v -∗ Ψ v) ∗ EWP e @ E <| P |> {{ Φ }} ⊢ EWP e @ E <| P |> {{ Ψ }}.
  Proof. iIntros "[H Hwp]". iApply (ewp_wand with "Hwp"). done. Qed.
  Lemma ewp_wand_r E e P Φ Ψ :
    EWP e @ E <| P |> {{ Φ }} ∗ (∀ v, Φ v -∗ Ψ v) ⊢ EWP e @ E <| P |> {{ Ψ }}.
  Proof. iIntros "[Hwp H]". by iApply (ewp_wand with "Hwp H"). Qed.
  Lemma ewp_frame_wand E e Ψ Φ R :
    R -∗ EWP e @ E <| Ψ |> {{ v, R -∗ Φ v }} -∗ EWP e @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros "HR HWP". iApply (ewp_wand with "HWP").
    iIntros (v) "HΦ". iFrame. by iApply "HΦ".
  Qed.

  (* Some lifting lemmas restated and reproved *)
  Local Hint Resolve reducible_no_obs_reducible : core.

     Lemma ewp_lift_step_fupdN E Ψ Φ e1 :
    to_val e1 = None → to_eff e1 = None ->
    (∀ σ1 ns κ κs nt, weakestpre.state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
    ⌜reducible e1 σ1 ⌝ ∗
    ∀ e2 σ2, ⌜prim_step e1 σ1 κ e2 σ2 [] ⌝
      ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
      weakestpre.state_interp σ2 (S ns) κs nt ∗ ∃ f, ↪[frame] f ∗
      (↪[frame] f -∗ EWP e2 @ E <| Ψ |> {{ Φ }}))
      ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
   Proof.
     rewrite ewp_unfold /ewp_pre => -> ->. done.
   Qed. 
(*     iIntros "H" (σ1 ns κ κs nt) "Hσ".
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

   Lemma ewp_lift_step_fupd E Ψ Φ e1 :
  to_val e1 = None → to_eff e1 = None ->
  (∀ σ1 ns κ κs nt, weakestpre.state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
    ⌜reducible e1 σ1 ⌝ ∗
    ∀ e2 σ2, ⌜prim_step e1 σ1 κ e2 σ2 [] ⌝ ={∅}=∗ ▷ |={∅,E}=>
      weakestpre.state_interp σ2 (S ns) κs nt ∗ ∃ f, ↪[frame] f ∗
      (↪[frame] f -∗ EWP e2 @ E <| Ψ |> {{ Φ }}))
    ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
  Proof.
    intros ? ?. rewrite -ewp_lift_step_fupdN => //. simpl.
    do 20 f_equiv.
    rewrite -step_fupdN_intro; [|done]. rewrite -bi.laterN_intro. auto.
  Qed.


  (** Derived lifting lemmas. *)
  Lemma ewp_lift_step E Ψ Φ e1 :
    to_val e1 = None → to_eff e1 = None ->
    (∀ σ1 ns κ κs nt, weakestpre.state_interp σ1 ns (κ ++ κs) nt ={E,∅}=∗
    ⌜reducible e1 σ1 ⌝ ∗
    ▷ ∀ e2 σ2, ⌜prim_step e1 σ1 κ e2 σ2 []⌝ ={∅,E}=∗
      weakestpre.state_interp σ2 (S ns) κs nt ∗ ∃ a, ↪[frame] a ∗
      (↪[frame] a -∗ EWP e2 @ E <| Ψ |> {{ Φ }}))
      ⊢ EWP e1 @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (??) "H". iApply ewp_lift_step_fupd => //. iIntros (?????) "Hσ".
    iMod ("H" with "Hσ") as "[$ H]". iIntros "!> * % !> !>". by iApply "H".
  Qed.

  Lemma ewp_lift_pure_step_no_fork (* `{!Inhabited (language.state wasm_lang)} *) E E' Ψ Φ e1 a :
    (∀ σ1, reducible e1 σ1) →
    (∀ κ σ1 e2 σ2, prim_step e1 σ1 κ e2 σ2 [] → κ = [] ∧ σ2 = σ1) →
    (|={E}[E']▷=> ∀ κ e2 σ, ⌜prim_step e1 σ κ e2 σ []⌝ → (↪[frame] a -∗ EWP e2 @ E <| Ψ |> {{ Φ }}))
      ⊢ ↪[frame] a -∗ EWP e1 @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hsafe Hstep) "H". iIntros "pred". iApply ewp_lift_step.
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
    iIntros (σ1 ns κ κs nt) "Hσ". iMod "H".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose". iSplit.
    { iPureIntro. done. }
    iNext. iIntros (e2 σ2 ?).
    destruct (Hstep κ σ1 e2 σ2) as (-> & <-); auto.
    iMod (state_interp_mono with "Hσ") as "$".
    iMod "Hclose" as "_". iMod "H". iModIntro.
    iExists a. iDestruct ("H" with "[//]") as "$". iFrame. 
  Qed.


  (* Atomic steps don't need any mask-changing business here, one can
     use the generic lemmas here. *)
    Lemma ewp_lift_atomic_step_fupd {E1 E2 Ψ Φ} e1 a :
    to_val e1 = None → to_eff e1 = None ->
    (∀ σ1 ns κ κs nt, weakestpre.state_interp σ1 ns (κ ++ κs) nt ={E1}=∗
    ⌜ reducible e1 σ1 ⌝ ∗
    ∀ e2 σ2, ⌜prim_step e1 σ1 κ e2 σ2 []⌝ ={E1}[E2]▷=∗
      weakestpre.state_interp σ2 (S ns) κs nt ∗
      from_option Φ False (to_val e2) ∗ ↪[frame] a )
      ⊢ EWP e1 @ E1 <| Ψ |> {{ v, Φ v ∗ ↪[frame] a }}.
  Proof.
    iIntros (??) "H".
    iApply (ewp_lift_step_fupd E1 _ _ e1)=> //; iIntros (σ1 ns κ κs nt) "Hσ1".
    iMod ("H" $! σ1 with "Hσ1") as "[$ H]".
    iApply fupd_mask_intro; first set_solver.
    iIntros "Hclose" (e2 σ2 ?). iMod "Hclose" as "_".
    iMod ("H" $! e2 σ2 with "[#]") as "H"; [done|].
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose !>".
    iMod "Hclose" as "_". iMod "H" as "($ & HQ & pred)".
    destruct (to_val e2) eqn:?; last by iExFalso.
    iApply fupd_mask_intro;[auto|].
    iIntros "Hcls". iExists a. iFrame.
    iIntros "Ha". iApply ewp_value;[|iFrame]. by apply of_to_val.
  Qed.

  Lemma ewp_lift_atomic_step {E Ψ Φ} e1 a :
    to_val e1 = None → to_eff e1 = None ->
    (∀ σ1 ns κ κs nt, weakestpre.state_interp σ1 ns (κ ++ κs) nt ={E}=∗
    ⌜reducible e1 σ1 ⌝ ∗
    ▷ ∀ e2 σ2, ⌜prim_step e1 σ1 κ e2 σ2 []⌝ ={E}=∗
      weakestpre.state_interp σ2 (S ns) κs nt ∗
      from_option Φ False (to_val e2) ∗ ↪[frame] a)
      ⊢ EWP e1 @ E <| Ψ |> {{ v, Φ v ∗ ↪[frame] a }}.
  Proof.
    iIntros (??) "H". iApply ewp_lift_atomic_step_fupd. done. done.
    iIntros (?????) "?". iMod ("H" with "[$]") as "[$ H]".
    iIntros "!> *". iIntros (Hstep) "!> !>".
    by iApply "H".
  Qed.


  Lemma ewp_lift_pure_det_step_no_fork {E E' Ψ Φ} e1 e2 a :
    (∀ σ1, reducible e1 σ1 ) →
    (∀ σ1 κ e2' σ2, prim_step e1 σ1 κ e2' σ2 []  →
                         κ = [] ∧ σ2 = σ1 ∧ e2' = e2) →
    (|={E}[E']▷=> ↪[frame] a -∗ EWP e2 @ E <| Ψ |> {{ Φ }}) ⊢ ↪[frame] a -∗ EWP e1 @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (? Hpuredet) "H". iApply (ewp_lift_pure_step_no_fork E E'); try done.
    { naive_solver. }
    iApply (step_fupd_wand with "H"); iIntros "H".
    iIntros (κ e' σ (_&?&->)%Hpuredet); auto.
  Qed.

  Lemma ewp_pure_step_fupd E E' e1 e2 φ n Ψ Φ a :
    PureExec φ n e1 e2 →
    φ →
    (|={E}[E']▷=>^n ↪[frame] a -∗ EWP e2 @ E <| Ψ |> {{ Φ }}) ⊢ ↪[frame] a -∗ EWP e1 @ E <| Ψ |> {{ Φ }}.
  Proof.
    iIntros (Hexec Hφ) "Hwp". specialize (Hexec Hφ).
    iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
    iApply ewp_lift_pure_det_step_no_fork.
    - intros σ. specialize (Hsafe σ). eauto using reducible_not_val.
    - intros.  apply pure_step_det in H as (-> & -> & -> & _).
      done.
    - by iApply (step_fupd_wand with "Hwp").
  Qed.

  Lemma ewp_pure_step_later E e1 e2 φ n Ψ Φ a :
    PureExec φ n e1 e2 →
    φ →
    ▷^n (↪[frame] a -∗ EWP e2 @ E <| Ψ |> {{ Φ }}) ⊢ ↪[frame] a -∗ EWP e1 @ E <| Ψ |> {{ Φ }}.
  Proof.
    intros Hexec ?. rewrite -ewp_pure_step_fupd //. clear Hexec.
    induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
  Qed.

  (* proofmode classes *)
  Global Instance frame_ewp p E e R P Φ Ψ :
    (∀ v, Frame p R (Φ v) (Ψ v)) →
    Frame p R (EWP e @ E <| P |> {{ Φ }}) (EWP e @ E <| P |> {{ Ψ }}) | 2.
  Proof. rewrite /Frame=> HR. rewrite ewp_frame_l. apply ewp_mono_post, HR. Qed.

(*  Global Instance is_except_0_ewp E e Ψ Φ : IsExcept0 (EWP e @ E <| Ψ |> {{ Φ }}).
  Proof. by rewrite /IsExcept0 -{2}fupd_ewp -except_0_fupd -fupd_intro. Qed. *)

(*  Global Instance elim_modal_bupd_ewp p E e P Ψ Φ :
    ElimModal True p false (|==> P) P (EWP e @ E <| Ψ |> {{ Φ }}) (EWP e @ E <| Ψ |> {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      (bupd_fupd E) fupd_frame_r wand_elim_r fupd_ewp.
  Qed. *)

(*  Global Instance elim_modal_fupd_ewp p E e P Ψ Φ :
    ElimModal True p false (|={E}=> P) P (EWP e @ E <| Ψ |> {{ Φ }}) (EWP e @ E <| Ψ |> {{ Φ }}).
  Proof.
    by rewrite /ElimModal intuitionistically_if_elim
      fupd_frame_r wand_elim_r fupd_ewp.
  Qed. *)

(*  Global Instance elim_modal_fupd_ewp_atomic p E1 E2 e P Ψ Φ a :
    ElimModal (Atomic (stuckness_to_atomicity NotStuck) e) p false
            (|={E1,E2}=> P) P
            (EWP e @ E1 <| Ψ |> {{ v, Φ v ∗ Pred a }})%I (EWP e @ E2 <| Ψ |> {{ v, |={E2,E1}=> Φ v ∗ Pred a }})%I | 100.
  Proof.
    intros ?. rewrite bi.intuitionistically_if_elim
                      fupd_frame_r bi.wand_elim_r ewp_atomic. auto.
  Qed. *)

(*  Global Instance add_modal_fupd_ewp E e P Φ :
    AddModal (|={E}=> P) P (WP e @ s; E {{ Φ }}).
  Proof. by rewrite /AddModal fupd_frame_r wand_elim_r fupd_wp. Qed. *)

(*  Global Instance elim_acc_ewp_atomic {X} E1 E2 α β γ e Ψ Φ a :
    ElimAcc (X:=X) (Atomic (stuckness_to_atomicity NotStuck) e)
            (fupd E1 E2) (fupd E2 E1)
            α β γ (EWP e @ E1 <| Ψ |> {{ v, Φ v ∗ Pred a }})%I
            (λ x, EWP e @ E2 <| Ψ |> {{ v, |={E2}=> β x ∗ (γ x -∗? Φ v) ∗ Pred a }})%I | 100.
  Proof.
    iIntros (?) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[H [H' $]]". iApply "H'". by iApply "Hclose".
  Qed. 

  Global Instance elim_acc_wp_nonatomic {X} E α β γ e s Φ :
    ElimAcc (X:=X) True (fupd E E) (fupd E E)
            α β γ (WP e @ s; E {{ Φ }})
            (λ x, WP e @ s; E {{ v, |={E}=> β x ∗ (γ x -∗? Φ v) }})%I.
  Proof.
    iIntros (_) "Hinner >Hacc". iDestruct "Hacc" as (x) "[Hα Hclose]".
    iApply wp_fupd.
    iApply (wp_wand with "(Hinner Hα)").
    iIntros (v) ">[Hβ HΦ]". iApply "HΦ". by iApply "Hclose".
  Qed. *)


End wp.


Transparent weakestpre.state_interp.
Transparent num_laters_per_step.
