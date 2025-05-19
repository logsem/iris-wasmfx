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
Lemma ewp_unop (E : coPset) Ψ (Φ : iris.val -> iProp Σ) v v' t (op: unop) f0:
  app_unop op v = v' ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [VAL_num v']) -∗
                     EWP [AI_basic (BI_const v); AI_basic (BI_unop t op)] @ E <| Ψ |> {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hunop) "Hf HΦ".
  iApply ewp_lift_atomic_step => //. 
  
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold language.reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v')], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //. apply r_simple. rewrite <- Hunop. apply rs_unop.
  - destruct σ as [[ws locs] inst].
    iIntros "!>" (es σ2 HStep) "!>".
    destruct σ2 as [[ ws' locs'] inst'].
    destruct HStep as (H & -> & _).
    only_one_reduction H. iFrame.
Qed.
 
Lemma ewp_binop (E : coPset) Ψ (Φ : iris.val -> iProp Σ) v1 v2 v t (op: binop) f0:
  app_binop op v1 v2 = Some v ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [VAL_num v]) -∗
                    EWP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] @ E <| Ψ |> {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hbinop) "Hf HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v)], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    by apply rs_binop_success.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    destruct HStep as [H [-> _]].
    only_one_reduction H. iFrame.
Qed.
                                                                  

Lemma ewp_binop_failure (E : coPset) Ψ (Φ : iris.val -> iProp Σ) v1 v2 t (op: binop) f0:
  app_binop op v1 v2 = None ->
  ▷ Φ trapV -∗
  ↪[frame] f0 -∗
                 EWP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_binop t op)] @ E <| Ψ |> {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hbinop) "Hf HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ".
  iModIntro.
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_trap], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    by apply rs_binop_failure.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    destruct HStep as [H [-> _]].
    only_one_reduction H. iFrame.
Qed.
    
Lemma ewp_relop (E : coPset) Ψ (Φ : iris.val -> iProp Σ) v1 v2(b: bool) t (op: relop) f0:
  app_relop op v1 v2 = b ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [VAL_num (VAL_int32 (wasm_bool b))]) -∗
                                            EWP [AI_basic (BI_const v1); AI_basic (BI_const v2); AI_basic (BI_relop t op)] @ E <| Ψ |> {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Hrelop) "Hf HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (wasm_bool b)))], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_relop.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    destruct HStep as [H [-> _]].
    only_one_reduction H. iFrame.
Qed.

Lemma ewp_testop_i32 (E : coPset) Ψ (Φ : iris.val -> iProp Σ) (v : i32) (b: bool) (op: testop) f0:
  app_testop_i (e:=i32t) op v = b ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [VAL_num (VAL_int32 (wasm_bool b))]) -∗
                                                    EWP [AI_basic (BI_const (VAL_int32 v)); AI_basic (BI_testop T_i32 op)] @ E <| Ψ |> {{ v, Φ v ∗ ↪[frame] f0 }}.
Proof.
  iIntros (Htestop) "Hf0 HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (wasm_bool b)))], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_testop_i32.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    destruct HStep as [H [-> _]].
    only_one_reduction H. iFrame.
Qed.

Lemma ewp_testop_i64  (E : coPset) Ψ (Φ : iris.val -> iProp Σ) (v : i64) (b: bool) (op: testop) f0:
  app_testop_i (e:=i64t) op v = b ->
  ↪[frame] f0 -∗
  ▷ Φ (immV [VAL_num(VAL_int32 (wasm_bool b))]) -∗
                                            EWP [AI_basic (BI_const (VAL_int64 v)); AI_basic (BI_testop T_i64 op)] @ E <| Ψ |> {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros (Htestop) "Hf0 HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const (VAL_int32 (wasm_bool b)))], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_testop_i64.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    destruct HStep as [H [-> _]].
    only_one_reduction H. iFrame.
Qed.

Lemma ewp_cvtop_convert  (E : coPset) Ψ (Φ : iris.val -> iProp Σ) v v' t1 t2 (sx: option sx) f0:
  cvt t2 sx v = Some v' ->
  types_num_agree t1 v ->
  ↪[frame] f0 -∗
  ▷Φ (immV [VAL_num v']) -∗
    EWP [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] @ E <| Ψ |> {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hcvtop Htype) "Hf0 HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v')], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_convert_success.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    destruct HStep as [H [-> _]].
    only_one_reduction H. iFrame.
Qed.

Lemma ewp_cvtop_convert_failure  (E : coPset) Ψ (Φ : iris.val -> iProp Σ) v t1 t2 (sx: option sx) f0:
  cvt t2 sx v = None ->
  types_num_agree t1 v ->
  ↪[frame] f0 -∗
  ▷Φ (trapV) -∗
    EWP [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] @ E <| Ψ |> {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hcvtop Htypes) "Hf0 HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_trap], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_convert_failure.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    destruct HStep as [H [-> _]].
    only_one_reduction H. iFrame.
Qed.

Lemma ewp_cvtop_reinterpret  (E : coPset) Ψ (Φ : iris.val -> iProp Σ) v v' t1 t2 f0:
  wasm_deserialise (bits v) t2 = v' ->
  types_num_agree t1 v ->
  ↪[frame] f0 -∗
  ▷Φ (immV [VAL_num v']) -∗
    EWP [AI_basic (BI_const v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] @ E <| Ψ |> {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hcvtop Htype) "Hf0 HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_basic (BI_const v')], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_reinterpret.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    destruct HStep as [H [-> _]].
    only_one_reduction H. iFrame.
Qed.

(* Non-numerics -- stack operations, control flows *)

Lemma ewp_unreachable  (E : coPset) Ψ (Φ : iris.val -> iProp Σ) f0 :
  ↪[frame] f0 -∗
  ▷Φ (trapV) -∗
  EWP [AI_basic BI_unreachable] @ E <| Ψ |> {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf0 HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    exists [], [AI_trap], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_unreachable.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    destruct HStep as [H [-> _]].
    only_one_reduction H. iFrame.
Qed.

Lemma ewp_nop  (E : coPset) Ψ (Φ : iris.val -> iProp Σ) f0:
  ↪[frame] f0 -∗
  ▷Φ (immV []) -∗
    EWP [AI_basic (BI_nop)] @ E <| Ψ |> {{ v, Φ v ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf0 HΦ".
  iApply ewp_lift_atomic_step => //=.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold reducible, language.prim_step => /=.
    exists [], [], σ, [].
    destruct σ as [[ws locs] inst].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple.
    subst.
    by apply rs_nop.
  - destruct σ as [[ws locs] inst] => //=.
    iIntros "!>" (es σ2 HStep) "!>".
    destruct σ2 as [[ws' locs'] inst'] => //=.
    destruct HStep as [H [-> _]].
    only_one_reduction H. iFrame.
Qed.

Lemma ewp_drop (E : coPset) Ψ (Φ : iris.val -> iProp Σ) v f0 :
  ↪[frame] f0 -∗
  ▷Φ (immV []) -∗
    EWP [AI_const v ; AI_basic BI_drop] @ E <| Ψ |> {{ w, Φ w ∗ ↪[frame] f0}}.
Proof.
  iIntros "Hf0 HΦ".
  iApply ewp_lift_atomic_step => //=.
  rewrite /to_val /= to_val_instr_AI_const //.
  rewrite /to_eff /= to_val_instr_AI_const //.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold language.reducible, language.prim_step => /=.
    exists [], [], σ, [].
    destruct σ as [[ws  locs ] inst ].
    unfold iris.prim_step => /=.
    repeat split => //.
    apply r_simple ; apply rs_drop.
  - destruct σ as [[ws  locs ] inst ].
    iIntros "!>" (es σ2 HStep) "!>".
    destruct σ2 as [[ws'  locs' ] inst'].
    destruct HStep as (H & -> & _).
    only_one_reduction H. iFrame.
    destruct v => //. destruct v => //. 
Qed.

Lemma ewp_select_false (E :coPset) Ψ (Φ : iris.val -> iProp Σ) n v1 v2 f0 :
  n = Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷Φ (immV [v2]) -∗ EWP [AI_const v1 ; AI_const v2 ;
                      AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_select) ] @ E <| Ψ |> {{ w, Φ w ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hn) "Hf0 HΦ".
  iApply ewp_lift_atomic_step => //=.
  rewrite /to_val /= to_val_instr_AI_const /= to_val_instr_AI_const //.
  rewrite /to_eff /= to_val_instr_AI_const /= to_val_instr_AI_const //.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro.
    unfold language.reducible, language.prim_step => /=.
    exists [], [AI_const v2], σ, [].
    destruct σ as [[ws  locs ] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply r_simple ; by apply rs_select_false.
  - destruct σ as [[ws  locs ] inst ].
    iIntros "!>" (es σ2 HStep) "!>".
    destruct σ2 as [[ws'  locs' ] inst'].
    destruct HStep as (H & -> & _).
    only_one_reduction H. iFrame.
    rewrite /to_val /= to_val_instr_AI_const //.
    all: destruct v1, v2 => //=.
    all: try by destruct v, v0 => //=. 
Qed.

Lemma ewp_select_true (E : coPset) Ψ (Φ: iris.val -> iProp Σ) n v1 v2 f0 :
  n <> Wasm_int.int_zero i32m ->
  ↪[frame] f0 -∗
  ▷Φ (immV [v1]) -∗ EWP [AI_const v1 ; AI_const v2 ;
                      AI_basic (BI_const (VAL_int32 n)) ; AI_basic (BI_select) ] @
E <| Ψ |> {{ w, Φ w ∗ ↪[frame] f0}}.
Proof.
  iIntros (Hn) "Hf0 HΦ".
  iApply ewp_lift_atomic_step => //=.
  rewrite /to_val /= to_val_instr_AI_const to_val_instr_AI_const //.
  rewrite /to_eff /= to_val_instr_AI_const to_val_instr_AI_const //.
  iIntros (σ ns κ κs nt) "Hσ !>".
  iSplit.
  - iPureIntro. unfold language.reducible, language.prim_step => /=.
    exists [], [AI_const v1], σ, [].
    destruct σ as [[ws  locs ] inst].
    unfold iris.prim_step => /=. repeat split => //.
    apply r_simple ; by apply rs_select_true.
  - destruct σ as [[ ws  locs ] inst].
    iIntros "!>" (es σ2 HStep) "!>".
    destruct σ2 as [[ ws'  locs' ] inst'].
    destruct HStep as (H & -> & _).
    only_one_reduction H. iFrame.
    rewrite /to_val /= to_val_instr_AI_const //.
    all: destruct v1, v2 => //=.
    all: destruct v, v0 => //. 
Qed.
    
End iris_rules_pure.
