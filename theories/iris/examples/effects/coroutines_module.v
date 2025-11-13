
From mathcomp Require Import ssreflect eqtype seq ssrbool.
From iris.program_logic Require Import language.
From iris.proofmode Require Import base tactics classes.
From iris.base_logic Require Export gen_heap ghost_map proph_map.
From iris.base_logic.lib Require Export fancy_updates.
From iris.bi Require Export weakestpre.
From Wasm.iris.rules Require Export iris_rules iris_example_helper.
From Wasm.iris.host Require Export iris_host.
From Wasm.iris.examples.effects Require Import coroutines_implementation_code.


Set Bullet Behavior "Strict Subproofs".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section CoroutinesModule.
  Context `{!wasmG Σ, !hvisG Σ, !hmsG Σ, !hasG Σ}.

  Definition coroutines_module :=
    {|
      mod_types := [ emptyt ; par_type ];
      mod_funcs :=
      [ {|
          modfunc_type := Mk_typeidx 0 ;
          modfunc_locals := [] ;
          modfunc_body := yield
        |};
        {|
          modfunc_type := Mk_typeidx 1 ;
          modfunc_locals := par_locs ;
          modfunc_body := par
        |}
      ] ;
      mod_tables := [];
      mod_mems := [] ;
      mod_globals := [];
      mod_elem := [] ;
      mod_data := [] ;
      mod_start := None; 
      mod_imports := [];
      mod_exports := [
        {| modexp_name := String.list_byte_of_string "yield function" ;
          modexp_desc :=
            MED_func (Mk_funcidx 0) |} ;
        {| modexp_name := String.list_byte_of_string "par function" ;
          modexp_desc :=
            MED_func (Mk_funcidx 1) |}
      ];
      mod_tags := [emptyt]
    |}.

  Definition expts := [ET_func emptyt ; ET_func par_type].

  Lemma coroutines_module_typing :
    module_typing coroutines_module [] expts.
  Proof.
    unfold module_typing.
    exists [emptyt; par_type], []. simpl.
    repeat split;eauto.
    - rewrite ! Forall2_cons. repeat split;auto; cbn;auto.
      + apply yield_typing. 
      + apply par_typing.
    - constructor => //. constructor => //. 
  Qed.

  Definition coroutines_module_instantiate yield_exp_addr par_exp_addr mod_addr:=
    [ ID_instantiate [ yield_exp_addr ; par_exp_addr ] mod_addr [] ].

  Notation "{{{{ P }}}} es {{{{ v , Q }}}}" :=
    (□ ∀ Φ, P -∗ (∀ v, Q -∗ Φ v) -∗ WP (es : host_expr) @ NotStuck ; ⊤ {{ v, Φ v }})%I (at level 50).

  Lemma tag_pointsto_persist n dq v:
    n ↦[tag]{dq} v ==∗ n ↦□[tag] v.
  Proof.
    apply pointsto_persist.
  Qed.

  Lemma instantiate_coroutines yield_exp_addr par_exp_addr mod_addr:

    ⊢ {{{{
              mod_addr ↪[mods] coroutines_module ∗
                (∃ exp1, yield_exp_addr ↪[vis] exp1) ∗
                (∃ exp2, par_exp_addr ↪[vis] exp2)
      }}}}
      ((coroutines_module_instantiate yield_exp_addr par_exp_addr mod_addr,
         [], empty_frame) : host_expr)
        {{{{  x,  ⌜x = (immHV [], empty_frame)⌝ ∗
                          mod_addr ↪[mods] coroutines_module ∗
                          ∃ addr_yield addr_par name_yield name_par cl_yield cl_par,
                            yield_exp_addr ↪[vis] {| modexp_name := name_yield;
                                                    modexp_desc := MED_func (Mk_funcidx addr_yield) |} ∗
                              par_exp_addr ↪[vis] {| modexp_name := name_par;
                                                    modexp_desc := MED_func (Mk_funcidx addr_par) |} ∗
                              ⌜ cl_type cl_yield = emptyt ⌝ ∗
                              ⌜ cl_type cl_par = par_type ⌝ ∗
                              N.of_nat addr_yield ↦[wf] cl_yield ∗
                              N.of_nat addr_par ↦[wf] cl_par ∗
                              yield_par_spec addr_yield addr_par cl_yield cl_par
        }}}} .
  Proof.
    iIntros "!>" (Φ) "(Hmod & Hvis1 & Hvis2) HΦ".
    iApply (weakestpre.wp_wand _ _ (_ : host_expr) with "[- HΦ]").
    {
      iApply (weakestpre.wp_fupd _ _ (_ : host_expr)).
      iApply (weakestpre.wp_wand _ _ (_ : host_expr) with "[Hmod Hvis1 Hvis2]").
      {
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
      }
      iIntros (v) "(-> & H)".
      unfold instantiation_resources_post.
      iDestruct "H" as "(Hmod & Himports & %inst & Hresources & Hexports)".
      iDestruct "Hexports" as "([%name1 Hexp1] & [%name2 Hexp2] & _)".
      simpl.
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
      iDestruct "Hfuncs" as "[Hyield Hfuncs]".
      destruct inst_funcs; first done.
      iDestruct "Hfuncs" as "[Hpar Hfuncs]".
      destruct inst_funcs; last done.
      iClear "Hfuncs".
      destruct inst_tags; first done.
      iDestruct "Htags" as "[Htag Htags]".
      iPoseProof (pointsto_persist with "Htag") as ">Htag".
      iModIntro.
 
      simpl in Hprefixes.
      destruct Hprefixes as [-> Hprefixes].
      destruct inst_tags; last done.

      simpl.
      instantiate (1 := λ v, (
      ∃ _ _ _ _ _ _,
      ⌜v = (_, _)⌝ ∗
      _↪[mods]coroutines_module ∗
      import_resources_host _ _ ∗
      import_resources_wasm_typecheck _ _ _ _ _ _ _ ∗
      N.of_nat _↦[wf]_ ∗
      N.of_nat _↦[wf]_ ∗
      _↪[vis]_ ∗
      _↪[vis]_ ∗
      N.of_nat _↦□[tag]emptyt)%I
      ); iFrame. auto.
    }
    - simpl. iIntros (v) "(%yield_name & %par & %yield & %par_name & %tags & %tag & -> & Hmod & Himports & Himport_typecheck & Hpar & Hyield & Hparvis & Hyieldvis & Htag)".
      iApply "HΦ".
      iFrame.
      rewrite /get_import_func_count /get_import_table_count /get_import_mem_count
        /get_import_global_count /get_import_tag_count /= /drop
        /module_inst_resources_func /module_inst_resources_tab /module_inst_resources_mem
        /module_inst_resources_glob /module_inst_resources_tag
      .
      simpl.

      repeat (iSplit; try done).
      iApply yield_par_spec_proof.
      unfold closure_yield, coroutine_inst.
      done.
      done.
      done.
      Unshelve.
      done.
  Qed.
    
    
End CoroutinesModule.
