From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.bi Require Export weakestpre.
Require Import iris_rules iris_example_helper.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Lemma build_llfill_local n f llh es e l1 l2 :
  llfill llh e = es ->
  llfill (LL_local l1 n f llh l2) e = (v_to_e_list l1) ++ [AI_local n f es] ++ l2.
Proof.
  simpl. intros ->. auto.
Qed.
Lemma build_llfill_label n es' llh es e l1 l2 :
  llfill llh e = es ->
  llfill (LL_label l1 n es' llh l2) e = (v_to_e_list l1) ++ [AI_label n es' es] ++ l2.
Proof.
  simpl. intros ->. auto.
Qed.
Lemma build_llfill_base l1 l2 e :
  llfill (LL_base l1 l2) e = (v_to_e_list l1) ++ e ++ l2.
Proof. simpl. auto. Qed.

Class DecomposeLocal (l: list administrative_instruction) l1 n f es l2 :=
  { MkDecomposeLocal: l = (v_to_e_list l1) ++ [AI_local n f es] ++ l2 }.

Global Hint Mode DecomposeLocal ! - - - - - : typeclass_instances.

#[export] Instance DecomposeLocalConsHere : forall n f es l2, DecomposeLocal (AI_local n f es :: l2) [] n f es l2.
Proof. intros. constructor. auto. Qed.

#[export] Instance DecomposeLocalCons : forall n f es l2 l l' e, DecomposeLocal l2 l n f es l' -> DecomposeLocal ((AI_const e) :: l2) (e :: l) n f es l'.
Proof.
  intros. constructor. inversion H. rewrite MkDecomposeLocal0.
  simpl. auto.
Qed.

Lemma decompose_local_list l l1 l2 es n f :
  DecomposeLocal l l1 n f es l2 ->
  l = v_to_e_list l1 ++ [AI_local n f es] ++ l2.
Proof.
  intros D. destruct D. auto.
Qed.

Ltac build_llfill_local :=
  match goal with
  | |- context [ llfill _ _ = ?l ] =>
      erewrite (decompose_local_list);[|once (typeclasses eauto)];
      apply build_llfill_local
  end.

Class DecomposeLabel (l: list administrative_instruction) l1 n f es l2 :=
  { MkDecomposeLabel: l = (v_to_e_list l1) ++ [AI_label n f es] ++ l2 }.

Global Hint Mode DecomposeLabel ! - - - - - : typeclass_instances.

#[export] Instance DecomposeLabelConsHere : forall n f es l2, DecomposeLabel (AI_label n f es :: l2) [] n f es l2.
Proof. intros. constructor. auto. Qed.

#[export] Instance DecomposeLabelCons : forall n f es l2 l l' e, DecomposeLabel l2 l n f es l' -> DecomposeLabel ((AI_const e) :: l2) (e :: l) n f es l'.
Proof.
  intros. constructor. inversion H. rewrite MkDecomposeLabel0.
  simpl. auto.
Qed.

Lemma decompose_label_list l l1 l2 es n f :
  DecomposeLabel l l1 n f es l2 ->
  l = v_to_e_list l1 ++ [AI_label n f es] ++ l2.
Proof.
  intros D. destruct D. auto.
Qed.

Ltac build_llfill_label :=
  match goal with
  | |- context [ llfill _ _ = ?l ] =>
      erewrite (decompose_label_list);[|typeclasses eauto];
      apply build_llfill_label
  end.

Class DecomposeBase l e l1 l2 :=
  { MkDecomposeBase: l = (v_to_e_list l1) ++ e ++ l2 }.

Global Hint Mode DecomposeBase ! ! - - : typeclass_instances.

#[export] Instance DecomposeBaseConsAppNil : forall e, DecomposeBase e e [] [].
Proof. intros. constructor. simpl. rewrite app_nil_r. auto. Qed.

#[export] Instance DecomposeBaseConsSingletonHere : forall e l2, DecomposeBase (e :: l2) [e] [] l2.
Proof. intros. constructor. auto. Qed.

#[export] Instance DecomposeBaseConsHere : forall l e es l2, DecomposeBase l es [] l2 -> DecomposeBase (e :: l) (e :: es) [] l2.
Proof. intros. constructor. inversion H;subst. simpl. auto. Qed.

#[export] Instance DecomposeBaseCons : forall l l1 e l2 e', DecomposeBase l e l1 l2 -> DecomposeBase ((AI_const e') :: l) e (e' :: l1) l2.
Proof. intros. inversion H. constructor. subst. simpl. auto. Qed.

Lemma decompose_base_list l e l1 l2 :
  DecomposeBase l e l1 l2 ->
  l = v_to_e_list l1 ++ e ++ l2.
Proof.
  intros. inversion H. auto.
Qed.

Ltac build_llfill_base :=
  match goal with
  | |- context [ llfill _ _ = ?l ] =>
      erewrite (@decompose_base_list l [AI_call_host _ _ _]);[|once (typeclasses eauto)];
      apply build_llfill_base
  end.

Ltac build_llfill :=
  repeat (build_llfill_local + build_llfill_label + build_llfill_base).

Class BuildCtx i lh es LI :=
  { MkBuildCtx: lfilled i lh es LI }.

Global Hint Mode BuildCtx - - ! ! : typeclass_instances.

Class DeconstructCtx i lh es LI :=
  { MkDeconstruct: lfilled i lh es LI }.

Global Hint Mode DeconstructCtx - - ! - : typeclass_instances.

#[export] Instance DeconstructCtxBaseApp :
  forall es l1 l2,
    DeconstructCtx 0 (LH_base (v_to_e_list l1) l2) es (v_to_e_list l1 ++ es ++ l2).
Proof.
  intros.
  constructor. apply lfilled_Ind_Equivalent. constructor.
  apply v_to_e_is_const_list.
Qed.

#[export] Instance BuildCtxBase :
  forall LI es l1 l2,
    DecomposeBase LI es l1 l2 ->
    BuildCtx 0 (LH_base (v_to_e_list l1) l2) es LI.
Proof.
  intros.
  inversion H as [Heq]. subst.
  constructor. apply lfilled_Ind_Equivalent. constructor.
  apply v_to_e_is_const_list.
Qed.

#[export] Instance DeconstructCtxLabelApp :
  forall l1 n es es' e l2 i lh,
    DeconstructCtx i lh e es ->
    DeconstructCtx (S i) (LH_rec (v_to_e_list l1) n es' lh l2) e ((v_to_e_list l1) ++ [AI_label n es' es] ++ l2).
Proof.
  intros until lh. intros B.
  inversion B as [fill%lfilled_Ind_Equivalent].
  constructor. apply lfilled_Ind_Equivalent.
  constructor;auto.
  apply v_to_e_is_const_list.
Qed.

#[export] Instance BuildCtxLabel :
  forall LI l1 n es es' e l2 i lh,
    DecomposeLabel LI l1 n es' es l2 ->
    BuildCtx i lh e es ->
    BuildCtx (S i) (LH_rec (v_to_e_list l1) n es' lh l2) e LI.
Proof.
  intros until lh. intros D B.
  inversion D as [Heq].
  inversion B as [fill%lfilled_Ind_Equivalent].
  constructor. apply lfilled_Ind_Equivalent.
  rewrite Heq. constructor;auto.
  apply v_to_e_is_const_list.
Qed.

Lemma ewp_build_ctx `{!wasmG Σ} es f i lh LI E P Ψ :
  BuildCtx i lh es LI ->
  EWP es UNDER f @ E CTX i; lh <| Ψ |> {{ P }} -∗ EWP LI UNDER f @ E <| Ψ |> {{ P }}.                                  
Proof.
  iIntros (B) "W".
  inversion B as [fill].
  iDestruct ("W" $! _ fill) as "W".
  iFrame.
Qed.

Lemma ewp_deconstruct_ctx `{!wasmG Σ} es f i lh LI E P Ψ:
  DeconstructCtx i lh es LI ->
  EWP LI UNDER f @ E <| Ψ |> {{ P }} -∗ EWP es UNDER f @ E CTX i; lh <| Ψ |> {{ P }}.
Proof.
  iIntros (B) "W".
  inversion B as [fill].
  iIntros (LI' fill').
  eapply lfilled_inj in fill;eauto. subst.
  iFrame.
Qed.

Ltac build_ctx e :=
  match goal with
  | |- context [ (EWP ?es UNDER ?f @ ?E <| ?Ψ |> {{ ?P }})%I ] =>
      iApply (@ewp_build_ctx _ _ e)
  end.

Ltac deconstruct_ctx :=
  match goal with
  | |- context [ (EWP ?es UNDER ?f @ ?E CTX ?i; ?lh <| ?Ψ |> {{ ?P }})%I ] =>
      iApply (@ewp_deconstruct_ctx _ _ es);
      try (constructor;cbn;rewrite eqseqE;eauto);
      iSimpl
  end.

Lemma bind_seq_base_imm `{!wasmG Σ} es f P LI l1 l2 E Q w Ψ:
  to_eff0 l2 = None ->
  DecomposeBase LI es l1 l2 ->
  EWP es UNDER f @ E <| Ψ |> {{ λ v f, ⌜v = immV w⌝ ∗ P v f }}
  -∗ (∀ v f, ⌜v = immV w⌝ ∗ P v f
                -∗ EWP (v_to_e_list l1) ++ (iris.of_val0 v) ++ l2 UNDER f @ E <| Ψ |> {{ Q }})
  -∗ EWP LI UNDER f @ E <| Ψ |> {{ Q }}.
Proof.
  intros Htf; intros. iIntros "H1 H2".
  build_ctx es.
  rewrite <- (app_nil_r es).
  iApply (ewp_seq_ctx E f Ψ Q (λ v f , ⌜v = immV _⌝ ∗ _)%I es).
  done. constructor. unfold lh_eff_None. simpl. done.
  iSplitR;[by iIntros (?) "[%Hcontr _]"|].
  rewrite app_nil_r. iFrame.
  iIntros (v' f') "H".
  rewrite app_nil_r.
  iApply ewp_base_pull. iApply ewp_wasm_empty_ctx.
  iApply "H2". iFrame.
Qed.

Lemma bind_seq_base_callhost `{!wasmG Σ} es f P LI l1 l2 Ψ E Q a1 a2 a3 a4 :
  to_eff0 l2 = None ->
  DecomposeBase LI es l1 l2 ->
  EWP es UNDER f @ E <| Ψ |> {{ λ v f, ⌜v = callHostV a1 a2 a3 a4⌝ ∗ P v f }}
  -∗ (∀ v f, ⌜v = callHostV a1 a2 a3 a4⌝ ∗ P v f -∗ EWP (v_to_e_list l1) ++ (iris.of_val0 v) ++ l2 UNDER f @ E <| Ψ |> {{ Q }})
  -∗ EWP LI UNDER f @ E <| Ψ |> {{ Q }}.
Proof.
  intros. iIntros "H1 H2".
  build_ctx es.
  rewrite <- (app_nil_r es).
  iApply (ewp_seq_ctx E f Ψ Q (λ v f, ⌜v = callHostV a1 a2 a3 a4⌝ ∗ _)%I es).
  done. constructor. done. 
  iSplitR;[by iIntros (?) "[%Hcontr _]"|].
  rewrite app_nil_r. iFrame.
  iIntros (v' f') "H".
  rewrite app_nil_r.
  iApply ewp_base_pull. iApply ewp_wasm_empty_ctx.
  iApply "H2". iFrame.
Qed.

Ltac bind_seq_base_imm e h :=
  iApply (@bind_seq_base_imm _ _ e with h).

Tactic Notation "bind_seq_base_imm" constr(e) "with" constr(h) :=
  bind_seq_base_imm e h.

Ltac bind_seq_base_callhost e h :=
  iApply (@bind_seq_base_callhost _ _ e with h).

Tactic Notation "bind_seq_base_callhost" constr(e) "with" constr(h) :=
  bind_seq_base_callhost e h.

Ltac take_drop_app_rewrite n :=
  match goal with
  | |- context [ EWP ?e UNDER _ @ _ CTX _; _ <| _ |> {{ _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ EWP ?e UNDER _ @ _ <| _ |> {{ _ }} %I ] =>
      rewrite -(list.take_drop n e);simpl take; simpl drop
  | |- context [ EWP ?e UNDER _ @ _ FRAME _; _ CTX _; _  <| _ |> {{ _ ; _ , _ }} %I ] =>
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
