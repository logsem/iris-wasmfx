
From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From iris.algebra Require Import list excl_auth.
From Wasm.iris.rules Require Export iris_rules iris_example_helper.
From Wasm.iris.host Require Export iris_host.
From Wasm.iris.examples.effects Require Import generator.


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section GeneratorModule.
  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}.
  Context `{!inG Σ (excl_authR (listO (leibnizO i32)))}.

  Definition generator_module :=
    {|
      mod_types := [ naturals_type ; sum_until_type ]; (* TODO: why can I only declare function types here? In wat I can give cont types *)
      mod_funcs :=
      [ {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := naturals_locs ;
          modfunc_body := naturals
        |};
        {|
          modfunc_type := Mk_typeidx 1 ;
          modfunc_locals := sum_until_locs ;
          modfunc_body := sum_until
        |}
      ] ;
      mod_tables := [];
      mod_mems := [] ;
      mod_globals := [];
      mod_elem := [] ; (* TODO: any elem declarations? *)
      mod_data := [] ;
      mod_start := None;
      mod_imports := [];
      mod_exports := [
        {| modexp_name := String.list_byte_of_string "generator function" ;
          modexp_desc :=
            MED_func (Mk_funcidx 0) |} ;
        {| modexp_name := String.list_byte_of_string "sum_until function" ;
          modexp_desc :=
            MED_func (Mk_funcidx 1) |}
      ];
      mod_tags := [tag_type]
    |}.

  Definition expts := [ET_func naturals_type ; ET_func sum_until_type].

  Lemma coroutines_module_typing :
    module_typing generator_module [] expts.
  Proof.
    unfold module_typing.
    exists [naturals_type; sum_until_type], []. simpl.
    repeat split;eauto.
    - rewrite ! Forall2_cons. repeat split;auto; cbn;auto.
        apply naturals_typing.
        apply sum_until_typing.
    - constructor => //. constructor => //.
  Qed.

  Definition generator_module_instantiate naturals_exp_addr sum_until_exp_addr mod_addr:=
    [ ID_instantiate [ naturals_exp_addr ; sum_until_exp_addr ] mod_addr [] ].

  Notation "{{{{ P }}}} es {{{{ v , Q }}}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).

  Lemma instantiate_generator naturals_exp_addr sum_until_exp_addr mod_addr:
    ⊢ {{{{
              mod_addr ↪[mods] generator_module ∗
                (∃ exp1, naturals_exp_addr ↪[vis] exp1) ∗
                (∃ exp2, sum_until_exp_addr ↪[vis] exp2)
      }}}}
      ((generator_module_instantiate naturals_exp_addr sum_until_exp_addr mod_addr,
         [], empty_frame) : host_expr) 
        {{{{  x,  ⌜x = (immHV [], empty_frame)⌝ ∗
                          mod_addr ↪[mods] generator_module ∗
                          ∃ addr_naturals addr_sum_until addr_tag name_naturals name_sum_until cl_naturals cl_sum_until,
                            naturals_exp_addr ↪[vis] {| modexp_name := name_naturals;
                                                    modexp_desc := MED_func (Mk_funcidx addr_naturals) |} ∗
                            sum_until_exp_addr ↪[vis] {| modexp_name := name_sum_until;
                                                    modexp_desc := MED_func (Mk_funcidx addr_sum_until) |} ∗
                            ⌜ cl_type cl_naturals = naturals_type ⌝ ∗
                            ⌜ cl_type cl_sum_until = sum_until_type ⌝ ∗
                            N.of_nat addr_naturals ↦[wf] cl_naturals ∗
                            N.of_nat addr_sum_until ↦[wf] cl_sum_until ∗
                            N.of_nat addr_tag ↦[tag] tag_type ∗

                            (∀ I, ∃ Ψ, naturals_spec addr_tag addr_naturals cl_naturals Ψ I) ∗
                            sum_until_spec addr_tag addr_naturals addr_sum_until cl_naturals cl_sum_until
        }}}} .
  Proof.
    iIntros "!>" (Φ) "(Hmod & Hvis1 & Hvis2) HΦ".
    iApply (weakestpre.wp_wand _ _ (_ : host_expr) with "[- HΦ]").
    iApply (instantiation_spec_operational_no_start with "[$Hmod Hvis1 Hvis2]") => //.
    - apply coroutines_module_typing.
    - unfold module_restrictions. cbn. repeat split;exists [];auto.
    - iFrame.
      iSplitR.
      instantiate (1:=[]).
      unfold import_resources_host.
      simpl. done.
      repeat instantiate (1:=∅).
      iSplitR; last by simpl.
      rewrite /instantiation_resources_pre_wasm /import_resources_wasm_typecheck
        /import_func_wasm_check /import_tab_wasm_check /import_glob_wasm_check
        /import_mem_wasm_check /import_tag_wasm_check.
      repeat iSplit.
      all: try by iApply big_sepM_empty.
      all: iPureIntro.
      all: try done.
      all: try constructor.
    - iIntros (v) "(-> & H)".
      iApply "HΦ".
      iSplit; first done.
      unfold instantiation_resources_post.
      iDestruct "H" as "(Hmod & Himports & %inst & Hresources & Hexports)".
      iDestruct "Hexports" as "([%name1 Hexp1] & [%name2 Hexp2] & _)".
      simpl.
      iFrame.
      unfold instantiation_resources_post_wasm.
      iDestruct "Hresources" as (g_inits tab_allocs mem_allocs glob_allocs tag_allocs wts' wms') "(Himport_typecheck & %Hprefixes & -> & -> & %Helembound & -> & -> & %Hdatabound & %Hinit & -> & -> & Hresources)".
      unfold module_inst_resources_wasm.
      iDestruct "Hresources" as "(Hfuncs & Htabs & Hmems & Hglobs & Htags)".
      rewrite /get_import_func_count /get_import_table_count /get_import_mem_count
        /get_import_global_count /get_import_tag_count /= /drop
        /module_inst_resources_func /module_inst_resources_tab /module_inst_resources_mem
        /module_inst_resources_glob /module_inst_resources_tag
      .
      destruct inst.
      simpl.
      destruct inst_globs; last done.
      destruct inst_memory; last done.
      destruct inst_tab; last done.
      iClear "Htabs Hmems Hglobs".
      destruct inst_funcs; first done.
      iDestruct "Hfuncs" as "[Hnaturals Hfuncs]".
      destruct inst_funcs; first done.
      iDestruct "Hfuncs" as "[Hsum_until Hfuncs]".
      destruct inst_funcs; last done.
      iClear "Hfuncs".
      destruct inst_tags; first done.
      iDestruct "Htags" as "[Htag Htags]".
      destruct inst_tags; last done.
      iClear "Htags".
      simpl.
      simpl in Hprefixes.
      destruct Hprefixes as [-> Hprefixes].

      iFrame.
      iSplit; first done.
      iSplit; first done.
      iSplitL.
      2: by iApply sum_until_spec_proof.
      iIntros (I).
      iExists (Ψgen t I).
      iApply naturals_spec_proof.
      by unfold closure_naturals, generator_inst.
  Qed.
    
    
End GeneratorModule.
