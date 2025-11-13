
From mathcomp Require Import ssreflect eqtype seq ssrbool bigop.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.program_logic Require Import adequacy.
From iris.bi Require Export weakestpre.
From iris.algebra Require Import list excl_auth.
From Wasm Require Import type_checker_reflects_typing.
From Wasm.iris.rules Require Export iris_rules iris_example_helper.
From Wasm.iris.host Require Export iris_host.
From Wasm.iris.examples.effects Require Import generator.
From Wasm.iris.examples.effects Require Import generator_module.


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition naturals_type := Tf [] [].
Definition cont_type := T_contref naturals_type.
Definition sum_until_body_type := Tf [] [T_num T_i32].
Definition sum_until_type := Tf [T_num T_i32] [T_num T_i32].
Definition tag_type := Tf [T_num T_i32] [].

Definition gen_tag := Mk_tagident 0.

Definition naturals_locs :=
  [ T_num T_i32 ].

Definition sum_until_locs := [T_num T_i32; T_num T_i32; T_ref cont_type].

Definition sum_until_client_100 :=
  [BI_const $ xx 100; BI_call 0].

Definition sum_until_client_0:=
  [BI_const $ xx 0; BI_call 0].

Definition sum_until_client_neg :=
  [BI_const $ xx (-4294967293); BI_call 0].

Section GeneratorClient.
  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}.
  Context `{!inG Σ (excl_authR (listO (leibnizO i32)))}.

  Definition sum_until_client generator_exp_addr sum_until_exp_addr mod_addr n :=
    [ ID_instantiate [ generator_exp_addr; sum_until_exp_addr ] mod_addr [];
H_invoke sum_until_exp_addr [VAL_int32 n]
    ].

  Notation "{{{{ P }}}} es {{{{ v , Q }}}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).


  Lemma instantiate_client naturals_exp_addr sum_until_exp_addr mod_addr n :
    ⊢ {{{{
        mod_addr ↪[mods] generator_module ∗
        (∃ exp1, naturals_exp_addr ↪[vis] exp1) ∗
        (∃ exp2, sum_until_exp_addr ↪[vis] exp2)
      }}}}
        ((sum_until_client naturals_exp_addr sum_until_exp_addr mod_addr n, [], empty_frame) : host_expr)
      {{{{ w, ⌜w = (immHV [VAL_num (VAL_int32 $ Sum_until_i32 n)], empty_frame)⌝ }}}}.
  Proof.
    iIntros "!>" (Φ) "(Hmod & Hexp1 & Hexp2 ) HΦ".

    (* instantiate generator module *)
    iApply (wp_seq_host_nostart with "[] Hmod [Hexp1 Hexp2]").
    done. done.
    2:{
      iIntros "Hmod".
      iApply (instantiate_generator with "[$Hmod $Hexp1 $Hexp2]").
      iIntros (x) "(-> & Hmod & H)".
      iFrame.
      instantiate (1 := λ v, (⌜ v = (immHV [], empty_frame) ⌝ ∗ _)%I).
      iSplit; first done.
      iExact "H".
    }
    by iIntros (?) "[% _]".
    iIntros (w f) "(%Heq & %addr_naturals & %addr_sum_until & %addr_tag & %name_naturals & %name_sum_until & %cl_naturals & %cl_sum_until & Hexp1 & Hexp2 & %Htypenaturals & %Htypesum_until & Hwfnaturals & Hwfsum_until & Htag & Hnaturals_spec & Hsum_until_spec) Hmod".
    iDestruct (pointsto_ne with "Hwfnaturals Hwfsum_until") as %Hne.
    inversion Heq; subst. clear Heq.

    replace [] with (v_to_e_list []); last done.
    iApply (wp_invoke_host with "[$] [$Hwfsum_until]").
    done.
    done.
    iIntros "!> Hexpsum_until Hwfsum_until".

    iApply wp_lift_wasm.

    (* Prove the specification of sum_until *)
    simpl.
    iApply (ewp_wand with "[-HΦ]").
    iApply ("Hsum_until_spec" with "Htag Hwfsum_until Hwfnaturals").
    iIntros (?? [<- ->]); simpl.
    iApply wp_value; first done.
    by iApply "HΦ".
  Qed.

End GeneratorClient.
