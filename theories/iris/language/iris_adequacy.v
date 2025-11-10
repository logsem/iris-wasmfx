From iris.algebra Require Import gmap auth agree gset coPset.
From iris.proofmode Require Import proofmode tactics.
From iris.base_logic.lib Require Import wsat.
From iris.program_logic Require Export weakestpre.
From iris.prelude Require Import options.
From Wasm.iris.language Require Import iris_ewp.
Import uPred.

(** This file contains the adequacy statements of the Iris program logic. First
we prove a number of auxilary results. *)
Set Bullet Behavior "Strict Subproofs".

Section adequacy.
  (* Context `{!irisGS Λ Σ}. *)
  Context `{!wasmG Σ}.
  Implicit Types e : expr0.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : val0 → frame -> iProp Σ.
(* Implicit Types Φs : list (val Λ → iProp Σ). *)

(* Notation wptp s t Φs := ([∗ list] e;Φ ∈ t;Φs, WP e @ s; ⊤ <| Ψ |> {{ Φ }})%I. *)


Lemma ewp_step e1 σ1 f1 e2 σ2 f2 (* Ψ *) Φ κ efs:
  prim_step (e1, f1) σ1 κ (e2, f2) σ2 efs →
  state_interp σ1 -∗ EWP e1 UNDER f1 @ ⊤ (* <| Ψ |> *) {{ Φ }}
    ={⊤,∅}=∗ |={∅}▷=> |={∅,⊤}=>
    state_interp σ2 ∗ EWP e2 UNDER f2 @ ⊤ (* <| Ψ |> *) {{ Φ }} 
  .
Proof.
  rewrite {1}ewp_unfold /ewp_pre. iIntros (?) "Hσ H".
  erewrite val_stuck.
  2: exact H.
  simpl.
  destruct (to_eff0 e1) eqn:Htf.
  { destruct e => //=.
    2: destruct i. 
    - iDestruct "H" as (?) "[? Hrest]" => //.
    - iDestruct "H" as "(% & % & % & % & % & _ & _ & _ & _ & _ & _ & H)".
      iDestruct "H" as (?) "[? Hrest]" => //. 
  } 
(*
    destruct H as (H & -> & ->).
    apply eff_head_stuck_reduce in H as [Habs | (vs & k & tf & tfk & i & sh & hh & Htf' & Hconts & -> & -> & Hfill)];
      first by rewrite Htf in Habs.
    rewrite Htf' in Htf. inversion Htf; subst.
    destruct H as [? _] => //. } *)
  iMod ("H" $! σ1 with "Hσ") as "(_ & H)". iModIntro.
  apply iris_reduce_properties.prim_step_obs_efs_empty in H as H'.
  inversion H'; subst.
  iSpecialize ("H" $! (e2, f2) _ H).
  iExact "H".
Qed.


  
(* Lemma ewp_step' es1 es2 σ1 f1 σ2 f2 Φ :
  reduce σ1 f1 es1 σ2 f2 es2 →
  state_interp σ1 -∗ EWP es1 UNDER f1 @ ⊤ (* <| Ψ |> *) {{ Φ }} -∗
|={⊤,∅}=> |={∅}▷=>^(S $ num_laters_per_step$ ns) |={∅,⊤}=>
         state_interp σ2 (S ns) κs (nt + nt') ∗
         wptp s es2 (Φs ++ replicate nt' fork_post).
Proof.
  iIntros (Hstep) "Hσ Ht".
  destruct Hstep as [e1' σ1' e2' σ2' efs t2' t3 Hstep]; simplify_eq/=.
  iDestruct (big_sepL2_app_inv_l with "Ht") as (Φs1 Φs2 ->) "[? Ht]".
  iDestruct (big_sepL2_cons_inv_l with "Ht") as (Φ Φs3 ->) "[Ht ?]".
  iExists _. iMod (wp_step with "Hσ Ht") as "H"; first done. iModIntro.
  iApply (step_fupdN_wand with "H"). iIntros ">($ & He2 & Hefs) !>".
  rewrite -(assoc_L app) -app_comm_cons. iFrame.
Qed. 

(* The total number of laters used between the physical steps number
   [start] (included) to [start+ns] (excluded). *)
Local Fixpoint steps_sum (num_laters_per_step : nat → nat) (start ns : nat) : nat :=
  match ns with
  | O => 0
  | S ns =>
    S $ num_laters_per_step start + steps_sum num_laters_per_step (S start) ns
  end.
*)

  
Lemma ewp_preservation n es1 es2 σ1 σ2 f1 f2 (* Ψ *) Φ :
  nsteps reduce_tuple n (σ1, f1, es1) (σ2, f2, es2) →
  state_interp σ1 -∗ EWP es1 UNDER f1 @ ⊤ (* <| Ψ |> *) {{ Φ }}
  ={⊤,∅}=∗ |={∅}▷=>^n |={∅,⊤}=> 
    state_interp σ2 ∗
    EWP es2 UNDER f2 @ ⊤ (* <| Ψ |> *) {{ Φ }} .
Proof.
  revert es1 es2 σ1 σ2 f1 f2 (* Ψ *) Φ.
  induction n as [|n IH]=> es1 es2 σ1 σ2 f1 f2 (* Ψ *) Φ /=.
  { inversion_clear 1; iIntros "? ?" => /=. 
    iFrame. by iApply fupd_mask_subseteq. }
  iIntros (Hsteps) "Hσ He". inversion_clear Hsteps as [|?? [[σ1' f1'] es1']].
(*  destruct f1.  *)
  iDestruct (ewp_step with "Hσ He") as ">H".
  { repeat split => //. } 
  iModIntro.
  iApply step_fupd_fupd.
  iApply (step_fupd_wand with "H").
  iIntros ">[Hσ He]".
  iMod (IH with "Hσ He") as "IH"; first done. iModIntro.
  done.
Qed. 

Lemma ewp_not_stuck e f σ (* Ψ *) Φ :
  to_eff0 e = None ->
  state_interp σ -∗ EWP e UNDER f (* <| Ψ |> *) {{ Φ }} ={⊤, ∅}=∗ ⌜not_stuck ((e, f): expr) σ⌝.
Proof.
  rewrite ewp_unfold /ewp_pre /not_stuck. iIntros (Htf) "Hσ H".
  simpl.
  destruct (to_val0 e) as [v|] eqn:?.
  { iMod (fupd_mask_subseteq ∅); first set_solver. iModIntro. eauto. }
  rewrite Htf.
(*  destruct (to_eff0 e) eqn:Htf.
  { destruct e0. all: iDestruct "H" as (?) "[??]". all: done. }  *)
  iSpecialize ("H" $! σ with "Hσ"). rewrite sep_elim_l. 
  iMod "H" as "%". iModIntro. eauto.
Qed.


Lemma ewp_postconditions Φ n es1 es2 σ1 σ2 f1 f2 (* Ψ *):
  nsteps reduce_tuple n (σ1, f1, es1) (σ2, f2, es2) →
  state_interp σ1 -∗ EWP es1 UNDER f1 @ ⊤ (* <| Ψ |> *) {{ Φ }} 
  ={⊤,∅}=∗ |={∅}▷=>^n |={∅,⊤}=> 
      state_interp σ2 ∗
      match (to_val0 es2) with
      | Some v2 => Φ v2 f2
      | None => True
      end. 

Proof.
  iIntros (Hstep) "Hσ He".
  iMod (ewp_preservation with "Hσ He") as "Hwp"; first done.
  iModIntro. iApply (step_fupdN_wand with "Hwp").
  iMod 1 as "(Hσ & Ht)"; simplify_eq/=.
  iFrame "Hσ".
  destruct (to_val0 es2) as [v2|] eqn:He2'; last done.
  apply of_to_val0 in He2' as <-. simpl. iApply ewp_value_fupd'. done.
Qed.

Lemma ewp_progress Φ n es1 es2 σ1 σ2 f1 f2 (* Ψ *):
  to_eff0 es2 = None ->
  nsteps reduce_tuple n (σ1, f1, es1) (σ2, f2, es2) →
  state_interp σ1 -∗
  EWP es1 UNDER f1 @ ⊤ (* <| Ψ |> *) {{ Φ }}
  ={⊤,∅}=∗ |={∅}▷=>^n |={∅}=> ⌜not_stuck ((es2, f2) : expr) σ2⌝.
Proof.
  iIntros (Htf Hstep) "Hσ He".
  iMod (ewp_preservation with "Hσ He") as "Hwp"; first done.
  iModIntro. iApply (step_fupdN_wand with "Hwp").
  iMod 1 as "(Hσ & Ht)"; simplify_eq/=.
  iApply (ewp_not_stuck with "Hσ") => //.
Qed.

End adequacy.

Lemma wp_progress_gen Σ `{!invGpreS Σ} es σ1 es2 σ2 f1 f2 n:
  to_eff0 es2 = None ->
    (∀ `{Hinv : !invGS Σ},
    ⊢ |={⊤}=> ∃  func_heapg cont_heapg exn_heapg tag_heapg tab_heapg
                 tabsize_heapg tablimit_heapg mem_heapg memsize_heapg
                 memlimit_heapg glob_heapg
                 Φ (* Ψ *),
        let _ : wasmG Σ :=
        WasmG Σ Hinv func_heapg cont_heapg exn_heapg tag_heapg tab_heapg
                 tabsize_heapg tablimit_heapg mem_heapg memsize_heapg
                 memlimit_heapg glob_heapg
      in
      state_interp σ1 ∗
      EWP es UNDER f1 @ ⊤ (* <| Ψ |> *) {{ Φ }}) ->
    nsteps reduce_tuple n (σ1, f1, es) (σ2, f2, es2) →
    not_stuck ((es2, f2): expr) σ2.
Proof.
  intros Htf Hwp ?.
  eapply pure_soundness.
  eapply (step_fupdN_soundness_lc _ (S n) n) .
  iIntros (Hinv) "Hcred".
  iMod Hwp as (func_heapg cont_heapg exn_heapg tag_heapg tab_heapg
                 tabsize_heapg tablimit_heapg mem_heapg memsize_heapg
                 memlimit_heapg glob_heapg
                 Φ (* Ψ *) ) "(Hσ & Hwp)".
  iMod (@ewp_progress Σ
       ( WasmG Σ Hinv func_heapg cont_heapg exn_heapg tag_heapg tab_heapg
                 tabsize_heapg tablimit_heapg mem_heapg memsize_heapg
                 memlimit_heapg glob_heapg) 
         with "[Hσ] Hwp") as "H" => //.
  iApply step_fupdN_S_fupd.
  iModIntro.
  iApply (step_fupdN_wand with "H").
  iModIntro. iModIntro. iModIntro. iIntros "$".
Qed.

Theorem ewp_strong_adequacy Σ `{!invGpreS Σ} es f σ1 n es2 f2 σ2 φ:
  to_eff0 es2 = None ->
  ( ∀ `{Hinv : !invGS Σ},
      ⊢ |={⊤}=> ∃
                 func_heapg cont_heapg exn_heapg tag_heapg tab_heapg
                 tabsize_heapg tablimit_heapg mem_heapg memsize_heapg
                 memlimit_heapg glob_heapg
               (Φ : (val0 → frame -> iProp Σ)) (* Ψ *),
      let _ : wasmG Σ :=
        WasmG Σ Hinv func_heapg cont_heapg exn_heapg tag_heapg tab_heapg
                 tabsize_heapg tablimit_heapg mem_heapg memsize_heapg
                 memlimit_heapg glob_heapg
      in
             

     (*let _ : irisGS wasm_lang Σ := IrisG Hinv (λ σ _ _ _, stateI σ) fork_post num_laters_per_step
                                       state_interp_mono
       in *)
       state_interp σ1 ∗
        EWP es UNDER f @ ⊤ (* <| Ψ |> *) {{ Φ }} ∗
       (
         (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
         threads in [t2] are not stuck *)
         ⌜ not_stuck ((es2, f2): expr) σ2 ⌝ -∗
         (* The state interpretation holds for [σ2] *)
         state_interp σ2 -∗
         (* If the initial threads are done, their post-condition [Φ] holds *)
         match to_val0 es2 with
         | Some v2 => Φ v2 f2
         | None => True
         end -∗
         (* Under all these assumptions, and while opening all invariants, we
         can conclude [φ] in the logic. After opening all required invariants,
         one can use [fupd_mask_subseteq] to introduce the fancy update. *)
         |={⊤,∅}=> ⌜ φ ⌝)) →
  nsteps reduce_tuple n (σ1, f, es) (σ2, f2, es2) → 
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  intros Htf Hwp ?.
  eapply pure_soundness.
  eapply (step_fupdN_soundness_lc _ (S n) n).
  iIntros (Hinv) "Hcred".
  iMod Hwp as (func_heapg cont_heapg exn_heapg tag_heapg tab_heapg tabsize_heapg tablimit_heapg mem_heapg memsize_heapg memlimit_heapg glob_heapg Φ (* Ψ *)) "(Hσ & Hwp & Hφ)".
  iMod (@ewp_postconditions Σ ( WasmG Σ Hinv func_heapg cont_heapg exn_heapg tag_heapg tab_heapg
                 tabsize_heapg tablimit_heapg mem_heapg memsize_heapg
                 memlimit_heapg glob_heapg) with "Hσ Hwp") as "H"; first exact H.
  iModIntro.
  iApply step_fupdN_S_fupd.
(*
  iAssert (|={∅}▷=>^n |={∅}=> ⌜φ⌝)%I
    with "[-]" as "H"; last first.
  { Set Printing All. by iApply step_fupdN_S_fupd. } *)
(*  iModIntro. *)
  iApply (step_fupdN_wand with "H").
  iModIntro.
  iModIntro.
  iModIntro.
  iMod 1 as "(Hσ & Hval) /=".
  iApply ("Hφ" with "[%] Hσ Hval").
  (* At this point in the adequacy proof, we use a trick: we effectively run the
    user-provided WP proof again (i.e., instantiate the `invGS_gen` and execute the
    program) by using the lemma [wp_progress_gen]. In doing so, we can obtain
    the progress part of the adequacy theorem.
  *)
  eapply (wp_progress_gen); [done|done | clear Φ  func_heapg cont_heapg exn_heapg tag_heapg tab_heapg
                 tabsize_heapg tablimit_heapg mem_heapg memsize_heapg
                 memlimit_heapg glob_heapg | done]. 
  iIntros (?).
  iMod Hwp as (func_heapg cont_heapg exn_heapg tag_heapg tab_heapg tabsize_heapg tablimit_heapg mem_heapg memsize_heapg memlimit_heapg glob_heapg Φ (* Ψ' *)) "(Hσ & Hwp & Hφ)".
  iModIntro. iFrame.
Qed.


(** Since the full adequacy statement is quite a mouthful, we prove some more
intuitive and simpler corollaries. These lemmas are morover stated in terms of
[rtc erased_step] so one does not have to provide the trace. *)
Record adequate σ1 f1 e1 
    (φ : val0 → frame -> state → Prop) := {
  adequate_result σ2 f2 v2:
   rtc reduce_tuple (σ1, f1, e1) (σ2, f2, of_val0 v2) → φ v2 f2 σ2;
  adequate_not_stuck σ2 f2 e2 :
   rtc reduce_tuple (σ1, f1, e1) (σ2, f2, e2) →
   not_stuck ((e2, f2): expr) σ2
}.

Lemma adequate_alt σ1 f1 e1 (φ : val0 → frame -> state → Prop) :
  adequate σ1 f1 e1 φ ↔ ∀ σ2 f2 e2,
    rtc reduce_tuple (σ1, f1, e1) (σ2, f2, e2) →
      (∀ v2, e2 = of_val0 v2 → φ v2 f2 σ2) ∧
      (not_stuck ((e2, f2): expr) σ2).
Proof.
  split.
  - intros []; naive_solver.
  - constructor; naive_solver.
Qed.

Theorem adequate_tp_safe e1 f1 σ1 e2 f2 σ2 φ :
  adequate σ1 f1 e1 φ →
  rtc reduce_tuple (σ1, f1, e1) (σ2, f2, e2) →
  is_Some (to_val0 e2) ∨ ∃ σ3 f3 e3, reduce_tuple (σ2, f2, e2) (σ3, f3, e3).
Proof.
  intros Had ?.
  destruct (to_val0 e2) eqn:He2; first by left.
  destruct (adequate_not_stuck σ1 f1 e1 φ Had σ2 f2 e2) as [?|(κ&e3&σ3&efs&?)];
    rewrite ?eq_None_not_Some; auto.
  { exfalso. simpl in H0. rewrite He2 in H0. destruct H0 as [??]. done. }
  
  right. destruct e3. exists σ3, f, e.
  destruct H0 as [? _] => //. 
Qed.

(** This simpler form of adequacy requires the [irisGS] instance that you use
everywhere to syntactically be of the form
{|
  iris_invGS := ...;
  state_interp σ _ κs _ := ...;
  fork_post v := ...;
  num_laters_per_step _ := 0;
  state_interp_mono _ _ _ _ := fupd_intro _ _;
|}
In other words, the state interpretation must ignore [ns] and [nt], the number
of laters per step must be 0, and the proof of [state_interp_mono] must have
this specific proof term.
*)
(* Corollary wp_adequacy Σ Λ `{!invGpreS Σ} s e σ φ :
  (∀ `{Hinv : !invGS Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisGS Λ Σ :=
           IrisG _ _ Hinv (λ σ _ κs _, stateI σ κs) fork_post (λ _, 0)
                 (λ _ _ _ _, fupd_intro _ _)
       in
       stateI σ κs ∗ WP e @ s; ⊤ (* <| Ψ |> *) {{ v, ⌜φ v⌝ }}) →
  adequate s e σ (λ v _, φ v).
Proof.
  intros Hwp. apply adequate_alt; intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod Hwp as (stateI fork_post) "[Hσ Hwp]".
  iExists s, (λ σ _ κs _, stateI σ κs), [(λ v, ⌜φ v⌝%I)], fork_post, _ => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> ? ?) "_ H _".
  iApply fupd_mask_intro_discard; [done|]. iSplit; [|done].
  iDestruct (big_sepL2_cons_inv_r with "H") as (e' ? ->) "[Hwp H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed. 

Corollary wp_invariance Σ Λ `{!invGpreS Σ} s e1 σ1 t2 σ2 φ :
  (∀ `{Hinv : !invGS Σ} κs,
     ⊢ |={⊤}=> ∃
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (fork_post : val Λ → iProp Σ),
       let _ : irisGS Λ Σ := IrisG _ _ Hinv (λ σ _, stateI σ) fork_post
              (λ _, 0) (λ _ _ _ _, fupd_intro _ _) in
       stateI σ1 κs 0 ∗ WP e1 @ s; ⊤ (* <| Ψ |> *) {{ _, True }} ∗
       (stateI σ2 [] (pred (length t2)) -∗ ∃ E, |={⊤,E}=> ⌜φ⌝)) →
  rtc erased_step ([e1], σ1) (t2, σ2) →
  φ.
Proof.
  intros Hwp [n [κs ?]]%erased_steps_nsteps.
  eapply (wp_strong_adequacy Σ _); [|done]=> ?.
  iMod (Hwp _ κs) as (stateI fork_post) "(Hσ & Hwp & Hφ)".
  iExists s, (λ σ _, stateI σ), [(λ _, True)%I], fork_post, _ => /=.
  iIntros "{$Hσ $Hwp} !>" (e2 t2' -> _ _) "Hσ H _ /=".
  iDestruct (big_sepL2_cons_inv_r with "H") as (? ? ->) "[_ H]".
  iDestruct (big_sepL2_nil_inv_r with "H") as %->.
  iDestruct ("Hφ" with "Hσ") as (E) ">Hφ".
  by iApply fupd_mask_intro_discard; first set_solver.
Qed.

*)
