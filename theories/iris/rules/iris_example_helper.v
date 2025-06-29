From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.language Require Export iris_atomicity.
From Wasm.iris.rules Require Export iris_rules.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* Shorthands for common constructors *)
Definition xx i := (VAL_int32 (Wasm_int.int_of_Z i32m i)).
Definition xb b := (VAL_int32 (wasm_bool b)).
Definition yy i := (Wasm_int.nat_of_uint i32m (Wasm_int.int_of_Z i32m i)).

Section Examples.
  Context `{!wasmG Σ}.
  
  (* Helper lemmas and tactics for necessary list manipulations for expressions *)
  Lemma iRewrite_nil_l  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) (e : iris.expr) f :
    (EWP [] ++ e UNDER f @ E <| Ψ |> {{ Φ }} ⊢ EWP e UNDER f @ E <| Ψ |> {{ Φ }}).
  Proof. rewrite app_nil_l. auto. Qed.
  Lemma iRewrite_nil_r  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) (e : iris.expr) f:
    (EWP e ++ [] UNDER f @ E <| Ψ |> {{ Φ }} ⊢ EWP e UNDER f @ E <| Ψ |> {{ Φ }}).
  Proof. rewrite app_nil_r. auto. Qed.
  Lemma iRewrite_nil_l_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) (e : iris.expr) i lh f:
    (EWP [] ++ e UNDER f @ E CTX i; lh <| Ψ |> {{ Φ }} ⊢ EWP e UNDER f @ E CTX i; lh <| Ψ |> {{ Φ }}).
  Proof. rewrite app_nil_l. auto. Qed.
  Lemma iRewrite_nil_r_ctx  (E : coPset) Ψ (Φ : val -> frame -> iProp Σ) (e : iris.expr) i lh f:
    (EWP e ++ [] UNDER f @ E CTX i; lh <| Ψ |> {{ Φ }} ⊢ EWP e UNDER f @ E CTX i; lh <| Ψ |> {{ Φ }}).
  Proof. rewrite app_nil_r. auto. Qed.

End Examples.

(* Tactics *)
Ltac take_drop_app_rewrite n :=
  match goal with
  | |- context [ EWP ?e UNDER _ @ _ CTX _; _ <| _ |> {{ _  }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ EWP ?e UNDER _ @ _ <| _ |> {{ _  }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ EWP ?e UNDER _ @ _ FRAME _; _ CTX _; _ <| _ |>  {{ _ ; _ , _  }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ EWP ?e UNDER _ @ _ FRAME _; _ <| _ |> {{ _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  end.

Ltac take_drop_app_rewrite_twice n m :=
  take_drop_app_rewrite n;
  match goal with
  | |- context [ EWP _ ++ ?e UNDER _ @ _ CTX _; _ <| _ |> {{ _ }} %I ] =>
      rewrite -(list.take_drop (length e - m) e);simpl take; simpl drop
  | |- context [ EWP _ ++ ?e UNDER _ @ _ <| _ |> {{ _ }} %I ] =>
      rewrite -(list.take_drop (length e - m) e);simpl take; simpl drop
  end.

Ltac auto_instantiate :=
  by instantiate (1 := λ v f, (⌜ v = immV _ ⌝ ∗ ⌜ f = Build_frame _ _ ⌝)%I).
