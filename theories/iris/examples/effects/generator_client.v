
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

Definition sum_until_client_100_host generator_exp_addr sum_until_exp_addr mod_addr :=
  [ ID_instantiate [ generator_exp_addr; sum_until_exp_addr ] mod_addr [];
    H_invoke sum_until_exp_addr [xx 100]
  ].

  Notation "{{{{ P }}}} es {{{{ v , Q }}}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).


  Lemma instantiate_client naturals_exp_addr sum_until_exp_addr mod_addr :
    ⊢ {{{{
        mod_addr ↪[mods] generator_module ∗
        (∃ exp1, naturals_exp_addr ↪[vis] exp1) ∗
        (∃ exp2, sum_until_exp_addr ↪[vis] exp2)
      }}}}
      (sum_until_client_100_host naturals_exp_addr sum_until_exp_addr mod_addr : host_expr)
      {{{{ x, ⌜ exists a b, x = (immHV [VAL_num (xx a); VAL_num (xx b)], empty_frame) /\ (a = 1 -> b = 42) ⌝ }}}}.
Section sum_until_clients_spec.

  Context `{!wasmG Σ}.

  Lemma sum_until_100 addr_naturals addr_sum_until cl_sum_until cl_naturals f :
    N.of_nat addr_sum_until ↦[wf] cl_sum_until -∗
    N.of_nat addr_naturals ↦[wf] cl_naturals -∗
    EWP sum_until_client_100 UNDER f
      {{ v ; f', ⌜f = f' ∧ v = immV [VAL_num $ xx 5050]⌝ }}.
  Proof.
    iIntros "Haddr_sum_until Haddr_naturals #Htag".
    iApply (ewp_wand with "[-] []").
    - iApply (sum_until_spec_proof with "[Haddr_sum_until] [Haddr_naturals]"); done.
    - iIntros (?? [-> ->]).
      iPureIntro.
      split; first done.
      unfold Sum_until_i32.
      repeat f_equal.
      replace (xy (yx 100)) with (100); last done.
      repeat rewrite big_nat_recl //=.
      rewrite big_geq; done.
  Qed.

  Lemma sum_until_0 addr_naturals addr_sum_until addr_tag f :
    N.of_nat addr_sum_until ↦[wf] closure_sum_until addr_naturals addr_sum_until addr_tag -∗
    N.of_nat addr_naturals ↦[wf] closure_naturals addr_naturals addr_tag -∗
    N.of_nat addr_tag ↦□[tag] tag_type -∗
    EWP [AI_const $ VAL_num $ VAL_int32 $ yx 0; AI_invoke addr_sum_until] UNDER f
      {{ v ; f', ⌜f = f' ∧ v = immV [VAL_num $ VAL_int32 $ yx 0]⌝ }}.
  Proof.
    iIntros "Haddr_sum_until Haddr_naturals #Htag".
    iApply (ewp_wand with "[-] []").
    - iApply (sum_until_spec_proof with "[Haddr_sum_until] [Haddr_naturals]"); done.
    - iIntros (?? [-> ->]).
      iPureIntro.
      split; first done.
      unfold Sum_until_i32.
      repeat f_equal.
      replace (xy (yx 0)) with (0); last done.
      repeat rewrite big_nat_recl //=.
      rewrite big_geq; done.
  Qed.

  Lemma sum_until_3_neg addr_naturals addr_sum_until addr_tag f :
    N.of_nat addr_sum_until ↦[wf] closure_sum_until addr_naturals addr_sum_until addr_tag -∗
    N.of_nat addr_naturals ↦[wf] closure_naturals addr_naturals addr_tag -∗
    N.of_nat addr_tag ↦□[tag] tag_type -∗
    EWP [AI_const $ VAL_num $ VAL_int32 $ yx (-4294967293); AI_invoke addr_sum_until] UNDER f
      {{ v ; f', ⌜f = f' ∧ v = immV [VAL_num $ VAL_int32 $ yx 6]⌝ }}.
  Proof.
    iIntros "Haddr_sum_until Haddr_naturals #Htag".
    iApply (ewp_wand with "[-] []").
    - iApply (sum_until_spec_proof with "[Haddr_sum_until] [Haddr_naturals]"); done.
    - iIntros (?? [-> ->]).
      iPureIntro.
      split; first done.
      unfold Sum_until_i32.
      repeat f_equal.
      replace (xy (yx (-4294967293))) with (3); last done.
      repeat rewrite big_nat_recl //=.
      rewrite big_geq; done.
  Qed.

End sum_until_spec.
