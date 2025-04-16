(* weakest_precondition.v *)

(* This theory introduces a notion of weakest precondition for reasoning about
   [eff_lang] programs. The key idea is to extend a weakest-precondition
   assertion with a pair of protocols to describe the effects that a program
   (fragment) might perform; the first protocol specifies one-shot effects,
   whereas the second one specifies multi-shot effects. *)

From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.
From Wasm.iris.language.iris Require Export iris protocols.

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
  

Definition ewp_pre `{!irisGS wasm_lang Σ} :
  (coPset -d> expr -d>
     (* (tagidx -d> iProt Σ) -d> (tagidx -d> iProt Σ) -d> (tagidx -d> val -d> iPropO Σ) -d> *)
     (effect_identifier -d> iProt Σ) -d>
     (val -d> iPropO Σ) -d> iPropO Σ) →
  (coPset -d> expr -d>
     (* (tagidx -d> iProt Σ) -d> (tagidx -d> iProt Σ) -d> (tagidx -d> val -d> iPropO Σ) -d> *)
     (effect_identifier -d> iProt Σ) -d>
     (val -d> iPropO Σ) -d> iPropO Σ)
  := λ ewp E e₁ (* Ψsus Ψsw Ψeff *) Ψ Φ,
  match to_val e₁ with
  | Some v =>
      |={E}=> Φ v
  | None =>
      match to_eff e₁ with
      | Some (thrE vs i a sh) =>
      (*    Ψ (ThrowE a) (immV vs)
       (* Hmmm have value instead of val to avoid immV? *) *)
          iProt_car (upcl (Ψ $ ThrowE a)) (immV vs) (λ w, False)%I
      | Some (susE vs i sh) =>
          iProt_car (upcl (Ψ $ SuspendE i)) (immV vs) (λ w, ▷ ewp E (susfill i sh (of_val w)) Ψ Φ)
      | Some (swE vs k tf i sh) =>
          iProt_car (upcl (Ψ $ SwitchE i)) (immV vs) (λ w, ▷ ewp E (swfill i sh (of_val w)) Ψ Φ)
      | None =>
          ∀ σ₁ ns κ κs nt,
            state_interp σ₁ ns (κ ++ κs) nt ={E,∅}=∗
              ⌜ reducible e₁ σ₁ ⌝ ∗  
              ∀ e₂ σ₂, ⌜ prim_step e₁ σ₁ κ e₂ σ₂ [] ⌝
                ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
                state_interp σ₂ (S ns) κs nt ∗ ewp E e₂ Ψ Φ 
      end
  end%I.

Local Instance ewp_pre_contractive `{!irisGS wasm_lang Σ} : Contractive ewp_pre.
Proof.
  rewrite /ewp_pre=> n ewp ewp' Hwp E e Ψ Φ.
  do 4 f_equiv; try by intros => ?; f_contractive; apply Hwp.
  do 16 (f_contractive || f_equiv). 
  induction num_laters_per_step as [|k IH]; simpl.
  - repeat (f_contractive || f_equiv); apply Hwp.
  - do 3 f_equiv. by apply IH.
Qed.
Definition ewp_def `{!irisGS wasm_lang Σ} :
  coPset -d> expr -d>
    (* (tagidx -d> iProt Σ) -d> (tagidx -d> iProt Σ) -d> (tagidx -d> val -d> iPropO Σ) -d> *)
    (effect_identifier -d> iProt Σ) -d>
    (val -d> iPropO Σ) -d> iPropO Σ :=
  fixpoint ewp_pre.
Definition ewp_aux `{!irisGS wasm_lang Σ} : seal ewp_def. Proof. by eexists. Qed.
Definition ewp_eq `{!irisGS wasm_lang Σ} := ewp_aux.(seal_eq).


(* -------------------------------------------------------------------------- *)
(** Non-expansiveness. *)

Lemma ewp_unfold `{!irisGS wasm_lang Σ} E e Ψ Φ :
  ewp_def E e Ψ Φ ⊣⊢ ewp_pre ewp_def E e Ψ Φ.
Proof. by rewrite /ewp_def; apply (fixpoint_unfold ewp_pre). Qed.

Global Instance ewp_ne `{!irisGS wasm_lang Σ} E e n :
  Proper ((dist n) ==> (dist n) ==> (dist n)) (ewp_def E e).
Proof.
  revert e.
  induction (lt_wf n) as [n _ IH]=> e Ψ1 Ψ1' HΨ1 Φ Φ' HΦ.
  rewrite !ewp_unfold /ewp_pre /upcl. simpl.
  f_equiv. { by f_equiv. }
  f_equiv.
  - f_equiv.
    + f_equiv. f_equiv. f_equiv.
      * f_equiv.
        apply IProt_ne.
        f_equiv.
        apply HΨ1.
      * f_equiv. intros ?. do 2 (f_contractive || f_equiv).
        apply IH; try lia; eapply dist_le; eauto with lia.
    + f_equiv. f_equiv. f_equiv.
      * f_equiv. apply IProt_ne. f_equiv. apply HΨ1.
      * f_equiv. intros ?. do 2 (f_contractive || f_equiv).
        apply IH; try lia; eapply dist_le; eauto with lia.
    + f_equiv. f_equiv. f_equiv. apply IProt_ne. f_equiv. apply HΨ1. 
  - do 4 f_equiv. do 14 (f_contractive || f_equiv).
    induction num_laters_per_step as [| k IH']; simpl.
    + do 5 (f_contractive || f_equiv).
      apply IH; try lia; eapply dist_le; eauto with lia.
    + do 3 f_equiv. by apply IH'.
Qed.

Global Instance ewp_proper `{!irisGS wasm_lang Σ} E e :
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
Notation "'EWP' e @ E <| Ψ '|' '>'  {{ Φ } }" :=
  (ewp_def E e%E Ψ Φ)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  <|  Ψ  '|' '>'  {{  Φ  } } ']' ']'") : bi_scope.

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
Notation "'EWP' e @ E <| Ψ '|' '>'  {{ v , Φ } }" :=
  (ewp_def E e%E Ψ (λ v, Φ))
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  <|  Ψ  '|' '>'  {{  v , Φ  } } ']' ']'") : bi_scope.

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
Notation "'EWP' e <| Ψ '|' '>'  {{ v , Φ } }" :=
  (ewp_def ⊤ e%E Ψ (λ v, Φ))
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  <|  Ψ  '|' '>'  {{  v , Φ  } } ']' ']'") : bi_scope.
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
Notation "'EWP' e <| Ψ '|' '>'  {{ Φ } }" :=
  (ewp_def ⊤ e%E Ψ Φ)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          '  <|  Ψ  '|' '>'  {{  Φ  } } ']' ']'") : bi_scope.
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
