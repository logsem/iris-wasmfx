From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.rules Require Export iris_rules iris_example_helper.
From Wasm Require Import type_checker_reflects_typing.

Set Bullet Behavior "Strict Subproofs".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Example_Switch.
  Context `{!wasmG Σ}.

  Definition f'_type := Tf [T_num T_i32] [T_num T_i32].
  Definition f'_cont_type := T_contref f'_type.

  Definition g_body_type := Tf [] [T_num T_i32].
  Definition g_type := Tf [T_num T_i32; T_ref f'_cont_type] [T_num T_i32].
  Definition g_cont_type := T_contref g_type.

  Definition f_type := Tf [] [T_num T_i32].
  Definition f_cont_type := T_contref f_type.

  Definition main_type := Tf [] [T_num T_i32].

  Definition swap_tag : tag_identifier := Mk_tagident 0.
  Definition swap_tag_type := Tf [] [T_num T_i32].

  Definition main_body :=
    [ BI_ref_func 1;
      BI_contnew (Type_lookup 2);

      BI_resume (Type_lookup 2) [HC_switch swap_tag]
    ].

  Definition f_body :=
    [ BI_const (xx 42);
      BI_ref_func 2;
      BI_contnew (Type_lookup 1);

      BI_switch (Type_lookup 1) (Mk_tagident 0);
      BI_unreachable
    ].

  Definition g_body :=
    [ BI_get_local 0; BI_return ].

  Definition typing_context : t_context :=
  {|
    tc_types_t := [f'_type; g_type; f_type];
    tc_func_t := [main_type; f_type; g_type];
    tc_global := [];
    tc_table := [];
    tc_memory := [];
    tc_local := [T_num T_i32; T_ref g_cont_type];
    tc_label := [];
    tc_return := Some [T_num T_i32];
    tc_refs := [];
    tc_tags_t := [swap_tag_type]
  |}.

  Lemma g_body_types : be_typing typing_context g_body g_body_type.
  Proof.
    apply /b_e_type_checker_reflects_typing; done.
  Qed.

  Lemma f_body_types : be_typing typing_context f_body f_type.
  Proof.
    unfold f_body.
    rewrite /main_body separate1.
    eapply bet_composition'.
    {
      apply /b_e_type_checker_reflects_typing.
      simpl.
      done.
    }
    rewrite separate1.
    eapply bet_composition'.
    {
      apply /b_e_type_checker_reflects_typing.
      simpl.
      done.
    }
    rewrite separate1.
    eapply bet_composition'.
    {
      eapply (bet_weakening [T_num T_i32]).
      constructor.
      done.
    }
    rewrite separate1.
    eapply bet_composition'; last constructor.
    eapply bet_switch; try done.
    done.
  Qed.


  Definition typing_context_main : t_context :=
  {|
    tc_types_t := [f'_type; g_type; f_type];
    tc_func_t := [main_type; f_type; g_type];
    tc_global := [];
    tc_table := [];
    tc_memory := [];
    tc_local := [];
    tc_label := [];
    tc_return := Some [];
    tc_refs := [];
    tc_tags_t := [Tf [] [T_num T_i32]]
  |}.


  Lemma main_body_type : be_typing typing_context_main main_body main_type.
  Proof.
    rewrite /main_body separate1.
    eapply bet_composition'.
    {
      apply /b_e_type_checker_reflects_typing.
      simpl.
      done.
    }
    rewrite separate1.
    eapply bet_composition'.
    {
      constructor.
      done.
    }
    rewrite separate1.
    eapply bet_composition'.
    {
      rewrite <- (app_nil_l [T_ref _]).
      apply bet_resume.
      done.
      repeat constructor.
    }
    apply /b_e_type_checker_reflects_typing.
    done.
  Qed.


  Definition inst addrg addrf addrmain tag :=
    {|
      inst_types  := [f'_type; g_type; f_type];
      inst_funcs  := [addrmain; addrf; addrg];
      inst_tab    := [];
      inst_memory := [];
      inst_globs  := [];
      inst_tags   := [tag];
    |}.

  Lemma g_spec : ∀ (addrg addrf addrmain tag: nat) f k Ψ x,
    (N.of_nat addrg) ↦[wf] FC_func_native (inst addrg addrf addrmain tag) g_type [] g_body -∗
    EWP [AI_const (VAL_num x); AI_ref_cont k; AI_invoke addrg] UNDER f <| Ψ |> {{ v; f', ⌜v = (immV [VAL_num x])⌝ ∗ ⌜f = f'⌝ }}.
  Proof.
    iIntros (????????) "Hwf_addrg".

    (* Reason about invocation of g function *)
    rewrite separate2.
    iApply (ewp_invoke_native with "Hwf_addrg"); try done.

    (* Reason about g_body in a frame *)
    iIntros "!> Hwf_addrg"; simpl.
    iApply ewp_frame_bind => //.
    repeat iSplitR.

    instantiate (1 := λ v f', ⌜v = retV (SH_rec [] 1 [] (SH_base [VAL_num x] []) [])⌝%I).
    all: simpl.
    2: {
      rewrite <- (app_nil_l _).
      iApply ewp_block; try done.
      iModIntro; simpl.
      rewrite (separate1 (AI_basic _)).
      iApply (ewp_label_bind with "[-]").
      2: {
        iPureIntro.
        instantiate (5 := []).
        unfold lfilled; simpl.
        by rewrite app_nil_r.
      }
      rewrite (separate1 (AI_basic _)).
      iApply ewp_seq; first done.
      repeat iSplitR.
      2: {
        iApply ewp_get_local; first done.
        auto_instantiate.
      }
      by iIntros (? [Hcontra _]).
      iIntros (?? [-> ->]); simpl.
      iApply ewp_value; first done.
      iSimpl.
      iIntros (LI HLI).
      move /lfilledP in HLI.
      inversion HLI; subst.
      inversion H8; subst.
      simpl.
      iApply ewp_value; done.
    }

    (* retV is not a TrapV *)
    { by iIntros (? Hcontra). }

    (* Reason about the retV inside the frame *)
    iIntros (?? ->).
    simpl.
    iApply ewp_return.
    3: {
      instantiate (1 := [AI_basic (BI_const x)]).
      instantiate (1 := LH_rec [] 1 [] (LH_base [] []) []).
      instantiate (1 := 1).
      unfold lfilled, lfill => //=.
    }
    1,2: done.
    by iApply ewp_value.
  Qed.

  Definition fg_prot tag q: iProt Σ :=
    (>> (x : value_num) >> ! ([VAL_num x]) {{⌜x = xx 42⌝ ∗ (N.of_nat tag) ↦[tag]{q} swap_tag_type }} ; ? ( []) {{ False }})%iprot.


  Definition Ξ hh := (∀ k x f Ψ, ∃ LI,
    ⌜hfilled No_var hh [AI_const (VAL_num x); AI_ref_cont k] LI⌝ ∗
    EWP LI UNDER f <| Ψ |> {{ v; f', ⌜v = (immV [VAL_num x])⌝ ∗ ⌜f = f'⌝ }})%I.

  Definition Ψ (addr_tag : nat) q : meta_protocol :=
    (bot_suspend,
    λ t, match t with
          | (Mk_tagidx addr) =>
              if Nat.eqb addr addr_tag then
              (fg_prot addr_tag q, Ξ)
              else
                (iProt_bottom, λ hh, False%I)
          end,
    bot_throw).


  Lemma f_spec : ∀ (addrg addrf addrmain tag: nat) q f Φ,
    (N.of_nat addrg) ↦[wf] FC_func_native (inst addrg addrf addrmain tag) g_type [] g_body -∗
    (N.of_nat addrf) ↦[wf] FC_func_native (inst addrg addrf addrmain tag) f_type [] f_body -∗
    (N.of_nat tag) ↦[tag]{q} swap_tag_type -∗
    EWP [AI_invoke addrf] UNDER f <| Ψ tag q |> {{ Φ }}.
  Proof.
    iIntros (???????) "Hwf_g Hwf_f Htag".

    (* Reason about invocation of f function *)
    rewrite <- (app_nil_l [AI_invoke _]).
    iApply (ewp_invoke_native with "Hwf_f"); try done.

    (* Reason about f_body in a frame *)
    iIntros "!> Hwf_f"; simpl.
    iApply ewp_frame_bind => //.
    iSplitR; last iSplitL "Hwf_g Htag".

    2: {
      unfold f_body.
      rewrite <- (app_nil_l [AI_basic _]).
      iApply ewp_block; try done.
      iModIntro; simpl.
      iApply (ewp_label_bind with "[-]").
      2: {
        iPureIntro.
        instantiate (5 := []).
        unfold lfilled; simpl.
        by rewrite app_nil_r.
      }
      rewrite separate3.
      iApply ewp_seq; first done.
      repeat iSplitR.
      2: {
        rewrite separate1.
        iApply ewp_val_app; first done.
        iSplitR.
        2: {
          (* ref_func 2 *)
          rewrite (separate1 (AI_basic _)).
          instantiate (1 := λ v f, (∃ kaddrg, ⌜ v = immV [_; _] ⌝ ∗ ⌜ f = Build_frame _ _ ⌝ ∗ N.of_nat kaddrg↦[wcont]Live g_type (Initial [] addrg g_type))%I).
          iApply ewp_seq; first done.
          repeat iSplitR.
          2: {
            iApply ewp_ref_func; first done.
            auto_instantiate.
          }
          by iIntros (? [Hcontra _]).
          iIntros (?? [-> ->]); simpl.

          (* create continuation *)
          iApply ewp_wand.
          by iApply ewp_contnew.
          iIntros (??) "(%kaddrg & -> & -> & Hwcont_g)"; simpl.
          by iFrame.
        }
        by iIntros "!>" (?) "(%kaddrg & %Hcontra & _)".
      }
      by iIntros (?) "(%kaddrg & %Hcontra & _)".

      iIntros (??) "(%kaddrg & -> & -> & Hwcont_g)"; simpl.

      (* Reason about switch *)
      rewrite separate3.
      iApply ewp_seq; first done.
      simpl.
      iSplitR; last iSplitL "Hwcont_g Hwf_g Htag".
      2: {
        rewrite separate1.
        iApply ewp_switch.
        done.
        instantiate (3 := f'_type).
        done.
        by instantiate (1 := Initial [] addrg g_type).
        2: done.
        3: by instantiate (1 := [VAL_num (xx 42)]).
        2: done.
        done.
        iFrame "Hwcont_g".
        iFrame.
        iSplitL.
        -
          unfold get_switch2, get_switch; simpl.
          rewrite Nat.eqb_refl.
          iIntros (k x f0 Ψ0).
          iExists _.
          iSplitR; first by unfold hfilled, hfill; simpl.

          iApply (ewp_call_reference_ctx with "[Hwf_g] [-]"); try done.
          3: {
            iPureIntro.
            instantiate (3 := 0).
            instantiate (2 := LH_base [AI_const (VAL_num x); AI_ref_cont _] _).
            instantiate (1 := (Type_explicit g_type)).
            unfold lfilled, lfill; simpl.
            done.
          }
          done.
          iIntros "!> Hwf_g" (LI HLI).
          move /lfilledP in HLI.
          inversion HLI; subst; simpl.
          by iApply g_spec.
        - iIntros "!> Htag".
          eassert (upcl ((get_switch1 (Mk_tagidx tag) (Ψ tag q))) = _ ).
          {
            unfold get_switch1, get_switch.
            simpl.
            rewrite Nat.eqb_refl.
            done.
          }
          rewrite H.
          rewrite (upcl_tele' [tele _] [tele]).
          simpl.
          instantiate (1 := (λ v f , False)%I).
          iFrame.
          eauto.
      }
      by iIntros.
      instantiate (1 := (λ v f , False)%I).
      by iIntros.
    }
    by iIntros.
    by iIntros.
  Qed.


  Lemma main_spec : ∀ (addrg addrf addrmain tag: nat) f,
    (N.of_nat addrg) ↦[wf] FC_func_native (inst addrg addrf addrmain tag) g_type [] g_body -∗
    (N.of_nat addrf) ↦[wf] FC_func_native (inst addrg addrf addrmain tag) f_type [] f_body -∗
    (N.of_nat addrmain) ↦[wf] FC_func_native (inst addrg addrf addrmain tag) main_type [] main_body -∗
    (N.of_nat tag) ↦[tag] swap_tag_type -∗
    EWP [AI_invoke addrmain] UNDER f <| Ψ tag (DfracOwn (1 / 2)) |> {{ v; f', ⌜v = (immV [VAL_num $ xx 42])⌝ ∗ ⌜f = f'⌝}}.
  Proof.
    iIntros (?????) "Hwf_g Hwf_f Hwf_main Htag".
    rewrite <- (app_nil_l [AI_invoke _]).
    iApply (ewp_invoke_native with "Hwf_main"); try done.

    (* Reason about f_body in a frame *)
    iIntros "!> Hwf_main"; simpl.
    iApply ewp_frame_bind => //.
    iSplitR; last iSplitL "Hwf_g Hwf_f Htag".

    2: {
      unfold main_body.
      rewrite <- (app_nil_l [AI_basic _]).
      iApply ewp_block; try done.
      iModIntro; simpl.
      iApply (ewp_label_bind with "[-]").
      2: {
        iPureIntro.
        instantiate (5 := []).
        unfold lfilled; simpl.
        by rewrite app_nil_r.
      }

      rewrite (separate1 (AI_basic _)).
      iApply ewp_seq; first done.
      repeat iSplitR.
      2: {
        iApply ewp_ref_func; first done.
        auto_instantiate.
      }
      by iIntros (? [Hcontra _]).
      iIntros (?? [-> ->]); simpl.

      (* create continuation *)
      rewrite separate2.
      iApply ewp_seq; first done.
      repeat iSplitR.
      2: by iApply ewp_contnew.
      by iIntros (?) "(% & %Hcontra & _)".
      iIntros (??) "(%kaddrf & -> & -> & Hwcont_f)"; simpl.

      rewrite (separate2 (AI_ref_cont _)).
      iApply ewp_seq; first done.
      iSplitR; last iSplitL.
      2: {
        rewrite <- (app_nil_l [AI_ref_cont _; _]).
        iApply ewp_resume; try done.
        simpl. instantiate (1 := [_]) => //.
        2: iFrame "Hwcont_f".
        simpl.
        by unfold hfilled, hfill; simpl.
        iDestruct "Htag" as "[Htag1 Htag2]".
        iSplitR; last iSplitR; last iSplitR "Htag2".
        3: {
          iNext.
          iApply (ewp_call_reference with "Hwf_f [-]"); try done.
          iIntros "!> Hwf_f".
          iApply (f_spec with "Hwf_g Hwf_f Htag1").
        }
        3 :{
          iSplitR; last first.
          - iNext.
            Opaque upcl.
            iSplitL; last done.
            unfold clause_triple.
            iFrame "Htag2".
            (* TODO: Should be able to get tag back here *)
            iIntros "!>" (vs k' h' cont t1s tf') "HΞ Htf' Hcont HΨ".
            unfold get_switch1, get_switch; simpl.
            rewrite Nat.eqb_refl.
            unfold get_switch2, get_switch; simpl.
            rewrite Nat.eqb_refl.
            rewrite (upcl_tele' [tele _] [tele]).
            simpl.
            iDestruct "HΨ" as (w) "(-> & [-> Htag1] & _)"; simpl.
            iDestruct ("HΞ" $! k' (xx 42) empty_frame (Ψ tag (DfracOwn (1 / 2)))) as "(%LI & %Hfill & H)".
            iExists _.
            iFrame "%".
           (* TODO: we lose part of the tag here *)
            instantiate (1 := λ v f, (_ ∗ _ ∗ (N.of_nat tag) ↦[tag]{_} swap_tag_type)%I).
            iFrame.
            iApply "H".
          - iIntros "!>" (?) "(-> & _ & Htag)".
            simpl.
            instantiate (1 := (λ v, ⌜v = (immV [VAL_num $ xx 42])⌝%I)).
            by iApply ewp_prompt_value.
        }
        by iIntros (?) "[%Hcontra _]".
        done.
      }
      by iIntros (? [Hcontra _]).
      iIntros (?? [-> ->]); simpl.
      iApply ewp_value; first done.
      iIntros (LI HLI).
      move /lfilledP in HLI.
      inversion HLI; subst.
      inversion H8; subst.
      simpl.
      iApply ewp_label_value; first done.
      auto_instantiate.
    }
    by iIntros (? [Hcontra _]).
    iIntros (?? [-> ->]); simpl.
    by iApply ewp_frame_value.
  Qed.

End Example_Switch.
