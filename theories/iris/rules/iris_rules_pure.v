From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From Wasm.iris.language Require Export iris_ewp_ctx.

Set Bullet Behavior "Strict Subproofs".

(* basic instructions with simple(pure) reductions *)
Section iris_rules_pure.

Context `{!wasmG Σ}.

(* numerics *)
Lemma ewp_unop (E : coPset) Ψ (Φ : val0 -> frame -> iProp Σ) v v' t (op: unop) f0:
  app_unop op v = v' ->
  ▷ Φ (immV [VAL_num v']) f0 -∗
                     EWP [AI_basic (BI_const v); AI_basic (BI_unop t op)] UNDER f0 @ E <| Ψ |> {{ v ; h, Φ v h }}.
Proof.
  iIntros (Hunop) "HΦ".
  iApply ewp_lift_atomic_step => //. 
  
  iIntros (σ) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold language.reducible, language.prim_step => /=.
    eexists [], ([AI_basic (BI_const v')], _), _, [].
    unfold iris.prim_step => /=.
    repeat split => //. apply r_simple. rewrite <- Hunop. apply rs_unop.
  - iIntros "!>" (es ?? HStep) "!>".
    destruct HStep as (H & _ & _).
    only_one_reduction H. 
Qed.
 
Lemma ewp_binop (E : coPset) Ψ (Φ : val0 -> frame -> iProp Σ) v1 v2 v t (op: binop) f0:
  app_binop op v1 v2 = Some v ->
  ▷ Φ (immV [VAL_num v]) f0 -∗
                    EWP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] UNDER f0 @ E <| Ψ |> {{ v ; h, Φ v h }}.
Proof.
  iIntros (Hbinop) "HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    eexists [], ([AI_basic (BI_const v)], _), _, [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    by apply rs_binop_success.
  - iIntros "!>" (es ?? HStep) "!>".
    destruct HStep as [H _].
    only_one_reduction H. 
Qed.
                                                                  

Lemma ewp_binop_failure (E : coPset) Ψ (Φ : val0 -> frame -> iProp Σ) v1 v2 t (op: binop) f0:
  app_binop op v1 v2 = None ->
  ▷ Φ trapV f0 -∗
               EWP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] UNDER f0 @ E <| Ψ |> {{ v ; h, Φ v h }}.
Proof.
  iIntros (Hbinop) "HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ".
  iModIntro.
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    eexists [], ([AI_trap], _), _, [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    by apply rs_binop_failure.
  - iIntros "!>" (es ?? HStep) "!>".
    destruct HStep as [H _].
    only_one_reduction H. 
Qed.
    
Lemma ewp_relop (E : coPset) Ψ (Φ : val0 -> frame -> iProp Σ) v1 v2(b: bool) t (op: relop) f0:
  app_relop op v1 v2 = b ->
  ▷ Φ (immV [VAL_num (VAL_int32 (wasm_bool b))]) f0 -∗ 
                                                    EWP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] UNDER f0 @ E <| Ψ |> {{ v ; h , Φ v h }}.
Proof.
  iIntros (Hrelop) "HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    eexists [], ([AI_basic (BI_const (VAL_int32 (wasm_bool b)))], _), _, [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_relop.
  - iIntros "!>" (es ?? HStep) "!>".
    destruct HStep as [H _].
    only_one_reduction H. 
Qed.

Lemma ewp_testop_i32 (E : coPset) Ψ (Φ : val0 -> frame -> iProp Σ) (v : i32) (b: bool) (op: testop) f0:
  app_testop_i (e:=i32t) op v = b ->
  ▷ Φ (immV [VAL_num (VAL_int32 (wasm_bool b))]) f0 -∗
                                                    EWP [AI_basic (BI_const (VAL_int32 v)); AI_basic (BI_testop T_i32 op)] UNDER f0 @ E <| Ψ |> {{ v; h, Φ v h }}.
Proof.
  iIntros (Htestop) "HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    eexists [], ([AI_basic (BI_const (VAL_int32 (wasm_bool b)))], _), _, [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_testop_i32.
  - iIntros "!>" (es ?? HStep) "!>".
    destruct HStep as [H _].
    only_one_reduction H. 
Qed.

Lemma ewp_testop_i64  (E : coPset) Ψ (Φ : val0 -> frame -> iProp Σ) (v : i64) (b: bool) (op: testop) f0:
  app_testop_i (e:=i64t) op v = b ->
  ▷ Φ (immV [VAL_num(VAL_int32 (wasm_bool b))]) f0 -∗
                                                   EWP [AI_basic (BI_const (VAL_int64 v)); AI_basic (BI_testop T_i64 op)] UNDER f0 @ E <| Ψ |> {{ v ; h, Φ v h }}.
Proof.
  iIntros (Htestop) "HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    eexists [], ([AI_basic (BI_const (VAL_int32 (wasm_bool b)))], _), _, [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_testop_i64.
  - iIntros "!>" (es ?? HStep) "!>".
    destruct HStep as [H _].
    only_one_reduction H. 
Qed.

Lemma ewp_cvtop_convert  (E : coPset) Ψ (Φ : val0 -> frame -> iProp Σ) v v' t1 t2 (sx: option sx) f0:
  cvt t2 sx v = Some v' ->
  types_num_agree t1 v ->
  ▷Φ (immV [VAL_num v']) f0 -∗
    EWP [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] UNDER f0 @ E <| Ψ |> {{ v ; h , Φ v h }}.
Proof.
  iIntros (Hcvtop Htype) "HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    eexists [], ([AI_basic (BI_const v')], _), _, [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_convert_success.
  - iIntros "!>" (es ?? HStep) "!>".
    destruct HStep as [H _].
    only_one_reduction H. 
Qed.

Lemma ewp_cvtop_convert_failure  (E : coPset) Ψ (Φ : val0 -> frame -> iProp Σ) v t1 t2 (sx: option sx) f0:
  cvt t2 sx v = None ->
  types_num_agree t1 v ->
  ▷Φ (trapV) f0 -∗
    EWP [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] UNDER f0 @ E <| Ψ |> {{ v ; h , Φ v h }}.
Proof.
  iIntros (Hcvtop Htypes) "HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    eexists [], ([AI_trap], _), _, [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_convert_failure.
  - iIntros "!>" (es ?? HStep) "!>".
    destruct HStep as [H _].
    only_one_reduction H. 
Qed.

Lemma ewp_cvtop_reinterpret  (E : coPset) Ψ (Φ : val0 -> frame -> iProp Σ) v v' t1 t2 f0:
  wasm_deserialise (bits v) t2 = v' ->
  types_num_agree t1 v ->
  ▷Φ (immV [VAL_num v']) f0 -∗
    EWP [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] UNDER f0 @ E <| Ψ |> {{ v ; h , Φ v h }}.
Proof.
  iIntros (Hcvtop Htype) "HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    eexists [], ([AI_basic (BI_const v')],_), _, [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_reinterpret.
  - iIntros "!>" (es ?? HStep) "!>".
    destruct HStep as [H _].
    only_one_reduction H. 
Qed.

(* Non-numerics -- stack operations, control flows *)

Lemma ewp_unreachable  (E : coPset) Ψ (Φ : val0 -> frame -> iProp Σ) f0 :
  ▷Φ (trapV) f0 -∗
  EWP [AI_basic BI_unreachable] UNDER f0 @ E <| Ψ |> {{ v ; h , Φ v h }}.
Proof.
  iIntros "HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    eexists [], ([AI_trap], _), σ, [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_unreachable.
  - iIntros "!>" (es ?? HStep) "!>".
    destruct HStep as [H _].
    only_one_reduction H. 
Qed.

Lemma ewp_nop  (E : coPset) Ψ (Φ : val0 -> frame -> iProp Σ) f0 :
  ▷Φ (immV []) f0 -∗
    EWP [AI_basic (BI_nop)] UNDER f0 @ E <| Ψ |> {{ v ; h , Φ v h }}.
Proof.
  iIntros "HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    exists [], ([], f0), σ, [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_nop.
  - iIntros "!>" (es ?? HStep) "!>".
    destruct HStep as [H _].
    only_one_reduction H. 
Qed.

Lemma ewp_drop (E : coPset) Ψ (Φ : val0 -> frame -> iProp Σ) v f0 :
  ▷Φ (immV []) f0 -∗
    EWP [AI_const v ; AI_basic BI_drop] UNDER f0 @ E <| Ψ |> {{ w ; h , Φ w h }}.
Proof.
  iIntros "HΦ".
  iApply ewp_lift_atomic_step => //=.
  rewrite /to_val0 /= to_val_instr_AI_const //.
  rewrite /to_eff0 /= to_val_instr_AI_const //.
  iIntros (σ) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold language.reducible, language.prim_step => /=.
    exists [], ([], f0), σ, [].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple ; apply rs_drop.
  - iIntros "!>" (es ?? HStep) "!>".
    destruct HStep as (H & _).
    only_one_reduction H.
    destruct v => //. destruct v => //. 
Qed.

Lemma ewp_select_false (E :coPset) Ψ (Φ : val0 -> frame -> iProp Σ) n v1 v2 f0  :
  n = Wasm_int.int_zero i32m ->
  ▷Φ (immV [v2]) f0 -∗ EWP [AI_const v1 ; AI_const v2 ;
                      AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_select) ] UNDER f0 @ E <| Ψ |> {{ w ; h , Φ w h }}.
Proof.
  iIntros (Hn) "HΦ".
  iApply ewp_lift_atomic_step => //=.
  rewrite /to_val0 /= to_val_instr_AI_const /= to_val_instr_AI_const //.
  rewrite /to_eff0 /= to_val_instr_AI_const /= to_val_instr_AI_const //.
  iIntros (σ) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold language.reducible, language.prim_step => /=.
    exists [], ([AI_const v2], f0), σ, [].
    unfold iris.prim_step => /=. repeat split => //.
    apply r_simple ; by apply rs_select_false.
  - iIntros "!>" (es ?? HStep) "!>".
    destruct HStep as (H & _).
    only_one_reduction H.
    iFrame.
    rewrite /to_val0 /= to_val_instr_AI_const.
    iFrame. destruct f0 => //. 
    all: destruct v1, v2 => //=.
    all: try by destruct v, v0 => //=. 
Qed.

Lemma ewp_select_true (E : coPset) Ψ (Φ: val0 -> frame -> iProp Σ) n v1 v2 f0 :
  n <> Wasm_int.int_zero i32m ->
  ▷Φ (immV [v1]) f0 -∗ EWP [AI_const v1 ; AI_const v2 ;
                      AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_select) ] UNDER f0 @
E <| Ψ |> {{ w ; h , Φ w h }}.
Proof.
  iIntros (Hn) "HΦ".
  iApply ewp_lift_atomic_step => //=.
  rewrite /to_val0 /= to_val_instr_AI_const to_val_instr_AI_const //.
  rewrite /to_eff0 /= to_val_instr_AI_const to_val_instr_AI_const //.
  iIntros (σ) "Hσ !>".
  iSplit.
  - iPureIntro. unfold language.reducible, language.prim_step => /=.
    exists [], ([AI_const v1], f0), σ, [].
    unfold iris.prim_step => /=. repeat split => //.
    apply r_simple ; by apply rs_select_true.
  - iIntros "!>" (es ?? HStep) "!>".
    destruct HStep as (H & _).
    only_one_reduction H. iFrame.
    rewrite /to_val0 /= to_val_instr_AI_const //.
    all: destruct v1, v2 => //=.
    all: destruct v, v0 => //. 
Qed.
    
End iris_rules_pure.
