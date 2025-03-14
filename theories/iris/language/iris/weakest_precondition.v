(* weakest_precondition.v *)

(* This theory introduces a notion of weakest precondition for reasoning about
   [eff_lang] programs. The key idea is to extend a weakest-precondition
   assertion with a pair of protocols to describe the effects that a program
   (fragment) might perform; the first protocol specifies one-shot effects,
   whereas the second one specifies multi-shot effects. *)

From iris.proofmode Require Import base tactics classes.
From iris.program_logic Require Import weakestpre.
From Wasm.iris.language.iris Require Export iris protocols.



(* ========================================================================== *)
(** * Weakest Precondition. *)

(* -------------------------------------------------------------------------- *)
(** Definition. *)

Definition ewp_pre `{!irisGS eff_lang Σ} :
  (coPset -d> expr -d> (tagidx -d> iProt Σ) -d> (tagidx -d> iProt Σ) -d> (tagidx -d> iProt Σ) -d> (val -d> iPropO Σ) -d> iPropO Σ) →
  (coPset -d> expr -d> (tagidx -d> iProt Σ) -d> (tagidx -d> iProt Σ) -d> (tagidx -d> iProt Σ) -d> (val -d> iPropO Σ) -d> iPropO Σ)
  := λ ewp E e₁ Ψsus Ψsw Ψeff Φ,
  match to_val e₁ with
  | Some v =>
      |={E}=> Φ v
  | None =>
      match to_eff e₁ with
      | Some (thrE i a sh) =>
          iProt_car (upcl (Ψeff (e_tag a))) (immV (e_fields a)) (λ w, ▷ ewp E (exnfill i (of_val w)) Ψsus Ψsw Ψeff Φ)
      | Some (susE i sh) =>
          True
      | Some (swE k tf i sh) =>
          True
(*                                                                       
      | Some (susE i sh) =>
          iProt_car (upcl (Ψsus i)) v
      | Some (OS, v, k) =>
          iProt_car (upcl OS Ψ₁) v (λ w, ▷ ewp E (fill k (Val w)) Ψ₁ Ψ₂ Φ)
      | Some (MS, v, k) =>
          iProt_car (upcl MS Ψ₂) v (λ w, ▷ ewp E (fill k (Val w)) Ψ₁ Ψ₂ Φ) *)
      | None =>
          ∀ σ₁ ns κ κs nt,
            state_interp σ₁ ns (κ ++ κs) nt ={E,∅}=∗
              ⌜ reducible e₁ σ₁ ⌝ ∗ 
              ∀ e₂ σ₂, ⌜ prim_step e₁ σ₁ κ e₂ σ₂ [] ⌝
                ={∅}▷=∗^(S $ num_laters_per_step ns) |={∅,E}=>
                state_interp σ₂ (S ns) κs nt ∗ ewp E e₂ Ψsus Ψsw Ψeff Φ
      end
  end%I.

Local Instance ewp_pre_contractive `{!irisGS eff_lang Σ} : Contractive ewp_pre.
Proof.
  rewrite /ewp_pre=> n ewp ewp' Hwp E e Ψ1 Ψ2 Φ.
  do 6 f_equiv; try by intros =>?; f_contractive; apply Hwp.
  do 14 (f_contractive || f_equiv). 
  induction num_laters_per_step as [|k IH]; simpl.
  - repeat (f_contractive || f_equiv); apply Hwp.
  - do 3 f_equiv. by apply IH.
Qed.
Definition ewp_def `{!irisGS eff_lang Σ} :
  coPset -d> expr -d> iProt Σ -d> iProt Σ -d> (val -d> iPropO Σ) -d> iPropO Σ :=
  fixpoint ewp_pre.
Definition ewp_aux `{!irisGS eff_lang Σ} : seal ewp_def. Proof. by eexists. Qed.
Definition ewp_eq `{!irisGS eff_lang Σ} := ewp_aux.(seal_eq).


(* -------------------------------------------------------------------------- *)
(** Non-expansiveness. *)

Lemma ewp_unfold `{!irisGS eff_lang Σ} E e Ψ1 Ψ2 Φ :
  ewp_def E e Ψ1 Ψ2 Φ ⊣⊢ ewp_pre ewp_def E e Ψ1 Ψ2 Φ.
Proof. by rewrite /ewp_def; apply (fixpoint_unfold ewp_pre). Qed.

Global Instance ewp_ne `{!irisGS eff_lang Σ} E e n :
  Proper ((dist n) ==> (dist n) ==> (dist n) ==> (dist n)) (ewp_def E e).
Proof.
  revert e.
  induction (lt_wf n) as [n _ IH]=> e Ψ1 Ψ1' HΨ1 Ψ2 Ψ2' HΨ2 Φ Φ' HΦ.
  rewrite !ewp_unfold /ewp_pre /upcl. simpl.
  f_equiv. { by f_equiv. }
  do 8 f_equiv.
  - by apply HΨ1.
  - intros ?. do 2 (f_contractive || f_equiv).
    apply IH; try lia; eapply dist_le; eauto with lia.
  - by apply HΨ2.
  - do 4 (f_contractive || f_equiv).
    apply IH; try lia; eapply dist_le; eauto with lia.
  - do 14 (f_contractive || f_equiv).
    induction num_laters_per_step as [|k IH']; simpl.
    + do 2 (f_contractive || f_equiv).
      apply IH; try lia; eapply dist_le; eauto with lia.
    + do 3 f_equiv. by apply IH'.
Qed.

Global Instance ewp_proper `{!irisGS eff_lang Σ} E e :
  Proper ((≡) ==> (≡) ==> (≡) ==> (≡)) (ewp_def E e).
Proof.
  intros Ψ1 Ψ1' ? Ψ2 Ψ2' ? Φ Φ' ?.
  by apply equiv_dist=>n; apply ewp_ne; apply equiv_dist.
Qed.


(* -------------------------------------------------------------------------- *)
(** Notation. *)

Notation "'EWP' e @ E {{ Φ } }" :=
  (ewp_def E e%E iProt_bottom iProt_bottom Φ)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E <| Ψ '|' '>'  {{ Φ } }" :=
  (ewp_def E e%E Ψ%ieff iProt_bottom Φ)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  <|  Ψ  '|' '>'  {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E .{| Ψ '|' '}'  {{ Φ } }" :=
  (ewp_def E e%E iProt_bottom Ψ%ieff Φ)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  .{|  Ψ  '|' '}'  {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E <| Ψ1 '|' '>' {| Ψ2 '|' '}'  {{ Φ } }" :=
  (ewp_def E e%E Ψ1%ieff Ψ2%ieff Φ)
  (at level 20, e, Ψ1, Ψ2, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  <|  Ψ1  '|' '>'  {|  Ψ2  '|' '}'  {{  Φ  } } ']' ']'") : bi_scope.

(* Postcondition includes binder. *)
Notation "'EWP' e @ E {{ v , Φ } }" :=
  (ewp_def E e%E iProt_bottom iProt_bottom (λ v, Φ)%I)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  {{  v ,  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E <| Ψ '|' '>'  {{ v , Φ } }" :=
  (ewp_def E e%E Ψ%ieff iProt_bottom (λ v, Φ)%I)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  <|  Ψ  '|' '>'  {{  v ,  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E .{| Ψ '|' '}'  {{ v , Φ } }" :=
  (ewp_def E e%E iProt_bottom Ψ%ieff (λ v, Φ)%I)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  .{|  Ψ  '|' '}'  {{  v ,  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e @ E <| Ψ1 '|' '>' {| Ψ2 '|' '}'  {{ v , Φ } }" :=
  (ewp_def E e%E Ψ1%ieff Ψ2%ieff (λ v, Φ)%I)
  (at level 20, e, Ψ1, Ψ2, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' @  E  <|  Ψ1  '|' '>'  {|  Ψ2  '|' '}'  {{  v ,  Φ  } } ']' ']'") : bi_scope.

(* Mask is implicitly specified by ⊤. *)
Notation "'EWP' e  {{ v , Φ } }" :=
  (ewp_def ⊤ e%E iProt_bottom iProt_bottom (λ v, Φ)%I)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' {{  v ,  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e  <| Ψ '|' '>'  {{ v , Φ } }" :=
  (ewp_def ⊤ e%E Ψ%ieff iProt_bottom (λ v, Φ)%I)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' <|  Ψ  '|' '>'  {{  v ,  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e .{| Ψ '|' '}'  {{ v , Φ } }" :=
  (ewp_def ⊤ e%E iProt_bottom Ψ%ieff (λ v, Φ)%I)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' .{|  Ψ  '|' '}'  {{  v ,  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e <| Ψ1 '|' '>' {| Ψ2 '|' '}'  {{ v , Φ } }" :=
  (ewp_def ⊤ e%E Ψ1%ieff Ψ2%ieff (λ v, Φ)%I)
  (at level 20, e, Ψ1, Ψ2, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' <|  Ψ1  '|' '>'  {|  Ψ2  '|' '}'  {{  v ,  Φ  } } ']' ']'") : bi_scope.

(* No binder and no mask. *)
Notation "'EWP' e  {{ Φ } }" :=
  (ewp_def ⊤ e%E iProt_bottom iProt_bottom Φ%I)
  (at level 20, e, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e  <| Ψ '|' '>'  {{ Φ } }" :=
  (ewp_def ⊤ e%E Ψ%ieff iProt_bottom Φ%I)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' <|  Ψ  '|' '>'  {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e .{| Ψ '|' '}'  {{ Φ } }" :=
  (ewp_def ⊤ e%E iProt_bottom Ψ%ieff Φ%I)
  (at level 20, e, Ψ, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' .{|  Ψ  '|' '}'  {{  Φ  } } ']' ']'") : bi_scope.
Notation "'EWP' e <| Ψ1 '|' '>' {| Ψ2 '|' '}'  {{ Φ } }" :=
  (ewp_def ⊤ e%E Ψ1%ieff Ψ2%ieff Φ%I)
  (at level 20, e, Ψ1, Ψ2, Φ at level 200,
   format "'[' 'EWP'  e  '/' '[          ' <|  Ψ1  '|' '>'  {|  Ψ2  '|' '}'  {{  Φ  } } ']' ']'") : bi_scope.
