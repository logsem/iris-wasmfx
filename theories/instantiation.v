(* Instantiation *)
(* see https://webassembly.github.io/spec/core/exec/modules.html#exec-instantiation *)

From Coq Require Import BinNat.
From mathcomp Require Import ssreflect ssrbool ssrfun ssrnat eqtype seq.
From Wasm Require Import list_extra datatypes datatypes_properties operations
                         typing opsem memory memory_list.


Definition addr := nat.
Definition funaddr := addr.
Definition tableaddr := addr.
Definition memaddr := addr.
Definition globaladdr := addr.

Definition alloc_Xs {A B} f (s : store_record) (xs : list A) : store_record * list B :=
  let '(s', fas) :=
    List.fold_left
      (fun '(s, ys) x =>
        let '(s', y) := f s x in
        (s', y :: ys))
        xs
        (s, nil) in
  (s', List.rev fas).

Inductive externval : Type :=
| ev_func : funaddr -> externval
| ev_table : tableaddr -> externval
| ev_mem : memaddr -> externval
| ev_global : globaladdr -> externval.

Definition funcs_of_externals (evs : list externval) : list addr :=
  seq.pmap (fun ev => match ev with | ev_func fa => Some fa | _ => None end) evs.

Definition tables_of_externals (evs : list externval) : list addr :=
  seq.pmap (fun ev => match ev with | ev_table ta => Some ta | _ => None end) evs.

Definition mems_of_externals (evs : list externval) : list addr :=
  seq.pmap (fun ev => match ev with | ev_mem ta => Some ta | _ => None end) evs.

Definition globals_of_externals (evs : list externval) : list addr :=
  seq.pmap (fun ev => match ev with | ev_global ta => Some ta | _ => None end) evs.

Definition add_func (s : store_record) funcinst :=
  {|
    s_funcs := List.app s.(s_funcs) [::funcinst];
    s_tables := s.(s_tables);
    s_mems := s.(s_mems);
    s_exns := s.(s_exns);
    s_tags := s.(s_tags);
    s_globals := s.(s_globals);
    s_conts := s.(s_conts);
|}.

Definition alloc_func (s : store_record) (m_f : module_func) (mi : instance) : store_record * funcidx :=
  let funcaddr := List.length s.(s_funcs) in
  let functype := List.nth (match m_f.(modfunc_type) with | Mk_typeidx n => n end) mi.(inst_types) (Tf nil nil ) in
  let funcinst := FC_func_native mi functype m_f.(modfunc_locals) m_f.(modfunc_body) in
  let S' := add_func s funcinst in
  (S', Mk_funcidx funcaddr).

Definition alloc_funcs (s : store_record) (m_fs : list module_func) (mi : instance) : store_record * list funcidx :=
  alloc_Xs (fun s m_f => alloc_func s m_f mi) s m_fs.

Definition add_table (s : store_record) (ti : tableinst) : store_record :=
  {|
    s_funcs := s.(s_funcs);
    s_tables := List.app s.(s_tables) [::ti];
    s_mems := s.(s_mems);
    s_globals := s.(s_globals);
    s_tags := s.(s_tags);
    s_conts := s.(s_conts);
    s_exns := s.(s_exns);
|}.

Definition alloc_tab (s : store_record) (tty : table_type) : store_record * tableidx :=
  let '{| tt_limits := {| lim_min := min; lim_max := maxo |} as lim; tt_elem_type := ety |} := tty in
  let tableaddr := Mk_tableidx (List.length s.(s_tables)) in
  let tableinst := {|
    table_data := (List.repeat None min);
    table_max_opt := maxo;
  |} in
  (add_table s tableinst, tableaddr).

Definition alloc_tabs (s : store_record) (ts : list table_type) : store_record * list tableidx :=
  alloc_Xs alloc_tab s ts.

Definition mem_mk (lim : limits) : memory :=
  let len := BinNatDef.N.mul page_size lim.(lim_min) in
  {| mem_data := mem_make Integers.Byte.zero len;
    mem_max_opt := lim.(lim_max);
  |}.

Definition add_mem (s : store_record) (m_m : memory) : store_record :=
  {|
  s_funcs := s.(s_funcs);
  s_tables := s.(s_tables);
  s_mems := List.app s.(s_mems) [::m_m];
    s_globals := s.(s_globals);
    s_conts := s.(s_conts);
    s_exns := s.(s_exns);
    s_tags := s.(s_tags);
|}.

Definition alloc_mem (s : store_record) (m_m : memory_type) : store_record * memidx :=
  let '{| lim_min := min; lim_max := maxo |} := m_m in
  let memaddr := Mk_memidx (List.length s.(s_mems)) in
  let meminst := mem_mk m_m in
  (add_mem s meminst, memaddr).

Definition alloc_mems (s : store_record) (m_ms : list memory_type) : store_record * list memidx :=
  alloc_Xs alloc_mem s m_ms.

Definition add_glob (s : store_record) (m_g : global) : store_record :=
  {|
  s_funcs := s.(s_funcs);
  s_tables := s.(s_tables);
  s_mems := s.(s_mems);
    s_globals := List.app s.(s_globals) [::m_g];
    s_conts := s.(s_conts);
    s_exns := s.(s_exns);
    s_tags := s.(s_tags);
|}.

Definition alloc_glob (s : store_record) (m_g_v : module_glob * value_num) : store_record * globalidx :=
  let '(m_g, v) := m_g_v in
  let globaddr := Mk_globalidx (List.length s.(s_globals)) in
  let globinst := Build_global m_g.(modglob_type).(tg_mut) v in
  (add_glob s globinst, globaddr).

Definition alloc_globs s m_gs (vs : list value_num) :=
  alloc_Xs alloc_glob s (List.combine m_gs vs).

Definition add_tag (s : store_record) m_tg : store_record :=
  {|
  s_funcs := s.(s_funcs);
  s_tables := s.(s_tables);
  s_mems := s.(s_mems);
    s_globals := s.(s_globals);
    s_conts := s.(s_conts);
    s_exns := s.(s_exns);
    s_tags := List.app s.(s_tags) [:: m_tg];
|}.

Definition alloc_tag (s : store_record) m_tg : store_record * tagidx :=
  let tagaddr := Mk_tagidx (List.length s.(s_tags)) in
  (add_tag s m_tg, tagaddr).

Definition alloc_tags s (m_tgs : seq function_type) :=
  alloc_Xs alloc_tag s m_tgs.

Definition v_ext := module_export_desc.

Definition export_get_v_ext (inst : instance) (exp : module_export_desc) : v_ext :=
  (* we circumvent partiality by providing 0 as a default *)
  match exp with
  | MED_func (Mk_funcidx i) => MED_func (Mk_funcidx (List.nth i inst.(inst_funcs) 0))
  | MED_table (Mk_tableidx i) => MED_table (Mk_tableidx (List.nth i inst.(inst_tab) 0))
  | MED_mem (Mk_memidx i) => MED_mem (Mk_memidx (List.nth i inst.(inst_memory) 0))
  | MED_global (Mk_globalidx i) => MED_global (Mk_globalidx (List.nth i inst.(inst_globs) 0))
  | MED_tag (Mk_tagidx i) => MED_tag (Mk_tagidx (List.nth i inst.(inst_tags) 0))
  end.

Definition ext_funcs :=
  seq.pmap
    (fun x =>
      match x with
      | MED_func i => Some i
      | _ => None
      end).

Definition ext_tags :=
  seq.pmap
    (fun x =>
      match x with
      | MED_tag i => Some i
      | _ => None
      end).

Definition ext_tabs :=
  seq.pmap
    (fun x =>
      match x with
      | MED_table i => Some i
      | _ => None
      end).

Definition ext_mems :=
  seq.pmap
    (fun x =>
      match x with
      | MED_mem i => Some i
      | _ => None
      end).

Definition ext_globs :=
  seq.pmap
    (fun x =>
      match x with
      | MED_global i => Some i
      | _ => None
      end).

Definition ext_t_funcs :=
  seq.pmap
    (fun x =>
      match x with
      | ET_func tf => Some tf
      | _ => None
      end).

Definition ext_t_tags :=
  seq.pmap
    (fun x =>
      match x with
      | ET_tag tf => Some tf
      | _ => None
      end).

Definition ext_t_tabs :=
  seq.pmap
    (fun x =>
      match x with
      | ET_tab i => Some i
      | _ => None
      end).

Definition ext_t_mems :=
  seq.pmap
    (fun x =>
      match x with
      | ET_mem i => Some i
      | _ => None
      end).

Definition ext_t_globs :=
  seq.pmap
    (fun x =>
      match x with
      | ET_glob i => Some i
      | _ => None
      end).


Definition alloc_module (s : store_record) (m : module) (imps : list v_ext) (gvs : list value_num)
    (s'_inst_exps : store_record * instance * seq module_export) : bool :=
  let '(s'_goal, inst, exps) := s'_inst_exps in
  let '(s1, i_fs) := alloc_funcs s m.(mod_funcs) inst in
  let '(s2, i_ts) := alloc_tabs s1 (List.map (fun t => t.(modtab_type)) m.(mod_tables)) in
  let '(s3, i_ms) := alloc_mems s2 m.(mod_mems) in
  let '(s4, i_gs) := alloc_globs s3 m.(mod_globals) gvs in
  let '(s', i_tgs) := alloc_tags s4 m.(mod_tags) in
  (s'_goal == s') &&
    (inst.(inst_types) == m.(mod_types)) &&
    (*    (List.map (List.nth_error (inst.(inst_types))) inst.(inst_tags) == List.map Some m.(mod_tags)) && *)
    (inst.(inst_tags) == List.map (fun '(Mk_tagidx i) => i) (List.app (ext_tags imps) i_tgs)) &&
  (inst.(inst_funcs) == List.map (fun '(Mk_funcidx i) => i) (List.app (ext_funcs imps) i_fs)) &&
  (inst.(inst_tab) == List.map (fun '(Mk_tableidx i) => i) (List.app (ext_tabs imps) i_ts)) &&
  (inst.(inst_memory) == List.map (fun '(Mk_memidx i) => i) (List.app (ext_mems imps) i_ms)) &&
  (inst.(inst_globs) == List.map (fun '(Mk_globalidx i) => i) (List.app (ext_globs imps) i_gs)) &&
  (exps == (List.map (fun m_exp => {| modexp_name := m_exp.(modexp_name); modexp_desc := (export_get_v_ext inst m_exp.(modexp_desc)) |}) m.(mod_exports) : seq module_export)).

Definition interp_alloc_module (s : store_record) (m : module) (imps : list v_ext) (gvs : list value_num) : (store_record * instance * list module_export) :=
  let i_fs := List.map (fun i => Mk_funcidx i) (seq.iota (List.length s.(s_funcs)) (List.length m.(mod_funcs))) in
  let i_ts := List.map (fun i => Mk_tableidx i) (seq.iota (List.length s.(s_tables)) (List.length m.(mod_tables))) in
  let i_ms := List.map (fun i => Mk_memidx i) (seq.iota (List.length s.(s_mems)) (List.length m.(mod_mems))) in
  let i_gs := List.map (fun i => Mk_globalidx i) (seq.iota (List.length s.(s_globals)) (min (List.length m.(mod_globals)) (List.length gvs))) in
  let inst := {|
               inst_types := m.(mod_types);
               inst_tags := [::];
    inst_funcs := List.map (fun '(Mk_funcidx i) => i) (List.app (ext_funcs imps) i_fs);
    inst_tab := List.map (fun '(Mk_tableidx i) => i) (List.app (ext_tabs imps) i_ts);
    inst_memory := List.map (fun '(Mk_memidx i) => i) (List.app (ext_mems imps) i_ms);
    inst_globs := List.map (fun '(Mk_globalidx i) => i) (List.app (ext_globs imps) i_gs);
  |} in
  let '(s1, _) := alloc_funcs s m.(mod_funcs) inst in
  let '(s2, _) := alloc_tabs s1 (List.map (fun t => t.(modtab_type)) m.(mod_tables)) in
  let '(s3, _) := alloc_mems s2 m.(mod_mems) in
  let '(s', _) := alloc_globs s3 m.(mod_globals) gvs in
  let exps := List.map (fun m_exp => {| modexp_name := m_exp.(modexp_name); modexp_desc := export_get_v_ext inst m_exp.(modexp_desc) |}) m.(mod_exports) in
  (s', inst, exps).

Definition insert_at {A} (v : A) (n : nat) (l : list A) : list A :=
  List.app (List.firstn n l) (List.app [::v] (List.skipn (n + 1) l)).

Definition dummy_table := {| table_data := nil; table_max_opt := None; |}.

Definition init_tab (s : store_record) (inst : instance) (e_ind : nat) (e : module_element) : store_record :=
  let t_ind := List.nth (match e.(modelem_table) with Mk_tableidx i => i end) inst.(inst_tab) 0 in
  let '{|table_data := tab_e; table_max_opt := maxo |} := List.nth t_ind s.(s_tables) dummy_table in
  let e_pay := List.map (fun i => List.nth_error inst.(inst_funcs) (match i with Mk_funcidx j => j end)) e.(modelem_init) in
  let tab'_e := List.app (List.firstn e_ind tab_e) (List.app e_pay (List.skipn (e_ind + length e_pay) tab_e)) in
  {| s_funcs := s.(s_funcs);
     s_tables := insert_at {| table_data := tab'_e; table_max_opt := maxo |} t_ind s.(s_tables);
     s_mems := s.(s_mems);
    s_globals := s.(s_globals);
    s_exns := s.(s_exns);
    s_conts := s.(s_conts);
    s_tags := s.(s_tags);
  |}.

Definition init_tabs (s : store_record) (inst : instance) (e_inds : list nat) (es : list module_element) : store_record :=
  List.fold_left (fun s' '(e_ind, e) => init_tab s' inst e_ind e) (List.combine e_inds es) s.

Definition dummy_data_vec :=
  mem_make Integers.Byte.zero (N.zero).

Definition dummy_mem := {|
  mem_data := dummy_data_vec;
  mem_max_opt := None
|}.

Definition init_mem (s : store_record) (inst : instance) (d_ind : N) (d : module_data) : store_record :=
  let m_ind := List.nth (match d.(moddata_data) with Mk_memidx i => i end) inst.(inst_memory) 0 in
  let mem := List.nth m_ind s.(s_mems) dummy_mem in
  let d_pay := List.map bytes.compcert_byte_of_byte d.(moddata_init) in
  let mem'_e := List.app (List.firstn d_ind mem.(mem_data).(ml_data)) (List.app d_pay (List.skipn (d_ind + length d_pay) mem.(mem_data).(ml_data))) in
  let mems' := insert_at {| mem_data := {| ml_data := mem'_e |}; mem_max_opt := mem.(mem_max_opt) |} m_ind s.(s_mems) in
  {| s_funcs := s.(s_funcs);
     s_tables := s.(s_tables);
     s_mems := mems';
    s_globals := s.(s_globals);
    s_tags := s.(s_tags);
    s_exns := s.(s_exns);
    s_conts := s.(s_conts);
  |}.

Definition init_mems (s : store_record) (inst : instance) (d_inds : list N) (ds : list module_data) : store_record :=
  List.fold_left (fun s' '(d_ind, d) => init_mem s' inst d_ind d) (List.combine d_inds ds) s.

Definition module_func_typing (c : t_context) (m : module_func) (tf : function_type) : Prop :=
  let '{| modfunc_type := Mk_typeidx i; modfunc_locals := t_locs; modfunc_body := b_es |} := m in
  let '(Tf tn tm) := tf in
  i < List.length c.(tc_types_t) /\
  List.nth i c.(tc_types_t) (Tf nil nil) == tf /\
  let c' := {|
             tc_types_t := c.(tc_types_t);
             tc_tags_t := c.(tc_tags_t);
             tc_refs := c.(tc_refs);
    tc_func_t := c.(tc_func_t);
    tc_global := c.(tc_global);
    tc_table := c.(tc_table);
    tc_memory := c.(tc_memory);
    tc_local := c.(tc_local) ++ tn ++ t_locs;
    tc_label := tm :: c.(tc_label);
    tc_return := Some tm;
  |} in
  typing.be_typing c' b_es (Tf [::] tm).

Definition limit_typing (lim : limits) (k : N) : bool :=
  let '{| lim_min := min; lim_max := maxo |} := lim in
  (N.leb k (N.pow 2 32)) &&
  (match maxo with None => true | Some max => N.leb max k end) &&
  (match maxo with None => true | Some max => N.leb min k end).

Definition module_tab_typing (t : module_table) : bool :=
  limit_typing t.(modtab_type).(tt_limits) (N.pow 2 32).

Definition module_mem_typing (m : memory_type) : bool :=
  limit_typing m (N.pow 2 32).

Definition const_expr (c : t_context) (b_e : basic_instruction) : bool :=
  match b_e with
  | BI_const _ => true
  | BI_get_global k =>
    (k < length c.(tc_global)) &&
    match List.nth_error c.(tc_global) k with
    | None => false
    | Some t => t.(tg_mut) == MUT_immut
    end
  | _ => false
  end.

Definition const_exprs (c : t_context) (es : list basic_instruction) : bool :=
  seq.all (const_expr c) es.

Definition module_glob_typing (c : t_context) (g : module_glob) (tg : global_type) : Prop :=
  let '{| modglob_type := tg'; modglob_init := es |} := g in
  const_exprs c es /\
  tg = tg' /\
  typing.be_typing c es (Tf nil [::T_num tg.(tg_t)]).

Definition module_elem_typing (c : t_context) (e : module_element) : Prop :=
  let '{| modelem_table := Mk_tableidx t; modelem_offset := es; modelem_init := is_ |} := e in
  const_exprs c es /\
  typing.be_typing c es (Tf nil [::T_num T_i32]) /\
  t < List.length c.(tc_table) /\
  seq.all (fun '(Mk_funcidx i) => i < List.length c.(tc_func_t)) is_.

Definition module_data_typing (c : t_context) (m_d : module_data) : Prop :=
  let '{| moddata_data := Mk_memidx d; moddata_offset := es; moddata_init := bs |} := m_d in
  const_exprs c es /\
  typing.be_typing c es (Tf nil [::T_num T_i32]) /\
  d < List.length c.(tc_memory).

Definition module_start_typing (c : t_context) (ms : module_start) : bool :=
  let '(Mk_funcidx i) := ms.(modstart_func) in
  (i < length c.(tc_func_t)) &&
  match List.nth_error c.(tc_func_t) i with
  | None => false
  | Some tf => tf == (Tf nil nil)
  end.

Definition module_import_typing (c : t_context) (d : import_desc) (e : extern_t) : bool :=
  match (d, e) with
  | (ID_func i, ET_func tf) =>
    (i < List.length c.(tc_types_t)) &&
    match List.nth_error c.(tc_types_t) i with
    | None => false
    | Some tf' => tf == tf'
    end
  | (ID_table t_t, ET_tab t_t') =>
    (t_t == t_t') && module_tab_typing {| modtab_type := t_t |}
  | (ID_mem mt, ET_mem mt') =>
    (mt == mt') && module_mem_typing mt
  | (ID_global gt, ET_glob gt') => gt == gt'
  | _ => false
  end.

Definition module_export_typing (c : t_context) (d : module_export_desc) (e : extern_t) : bool :=
  match (d, e) with
  | (MED_func (Mk_funcidx i), ET_func tf) =>
    (i < List.length c.(tc_func_t)) &&
    match List.nth_error c.(tc_func_t) i with
    | None => false
    | Some tf' => tf == tf'
    end
  | (MED_table (Mk_tableidx i), ET_tab t_t) =>
    (i < List.length c.(tc_table)) &&
    match List.nth_error c.(tc_table) i with
    | None => false
    | Some lim' => t_t == lim'
    end
  | (MED_mem (Mk_memidx i), ET_mem t_m) =>
    (i < List.length c.(tc_memory)) &&
    match List.nth_error c.(tc_memory) i with
    | None => false
    | Some lim' => t_m == lim'
    end
  | (MED_global (Mk_globalidx i), ET_glob gt) =>
    (i < List.length c.(tc_global)) &&
    match List.nth_error c.(tc_global) i with
    | None => false
    | Some gt' => gt == gt'
    end
  | (MED_tag (Mk_tagidx i), ET_tag tf) =>
      List.nth_error c.(tc_tags_t) i == Some tf
  | (_, _) => false
  end.

Definition pred_option {A} (p : A -> bool) (a_opt : option A) : bool :=
  match a_opt with
  | None => true
  | Some a => p a
  end.

Definition module_typing (m : module) (impts : list extern_t) (expts : list extern_t) : Prop :=
  exists fts gts,
  let '{| 
    mod_types := tfs;
    mod_funcs := fs;
    mod_tables := ts;
    mod_mems := ms;
    mod_globals := gs;
    mod_elem := els;
          mod_data := ds;
          mod_tags := tags;
    mod_start := i_opt;
    mod_imports := imps;
    mod_exports := exps;
  |} := m in
  let ifts := ext_t_funcs impts in
  let its := ext_t_tabs impts in
  let ims := ext_t_mems impts in
  let igs := ext_t_globs impts in
  let itags := ext_t_tags impts in
  let c := {|
            tc_types_t := tfs;
            tc_tags_t := List.app itags tags;
            tc_refs := nil;
    tc_func_t := List.app ifts fts;
    tc_global := List.app igs gts;
    tc_table := List.app its (List.map (fun t => t.(modtab_type)) ts);
    tc_memory := List.app ims ms; 
    tc_local := nil;
    tc_label := nil;
    tc_return := None;
  |} in
  let c' := {|
             tc_types_t := nil;
             tc_tags_t := nil;
             tc_refs := nil;
    tc_func_t := nil;
    tc_global := igs;
    tc_table := nil;
    tc_memory := nil;
    tc_local := nil;
    tc_label := nil;
    tc_return := None;
  |} in
  List.Forall2 (module_func_typing c) fs fts /\
  seq.all module_tab_typing ts /\
  seq.all module_mem_typing ms /\
  List.Forall2 (module_glob_typing c') gs gts /\
  List.Forall (module_elem_typing c) els /\
  List.Forall (module_data_typing c) ds /\
  pred_option (module_start_typing c) i_opt /\
  List.Forall2 (fun imp => module_import_typing c imp.(imp_desc)) imps impts /\
  List.Forall2 (fun exp => module_export_typing c exp.(modexp_desc)) exps expts.

Inductive external_typing : store_record -> v_ext -> extern_t -> Prop :=
| ETY_func :
  forall (s : store_record) (i : nat) cl (tf : function_type),
  i < List.length s.(s_funcs) ->
  List.nth_error s.(s_funcs) i = Some cl ->
  tf = operations.cl_type cl ->
  external_typing s (MED_func (Mk_funcidx i)) (ET_func tf)
| ETY_tab :
  forall (s : store_record) (i : nat) (ti : tableinst) tt,
  i < List.length s.(s_tables) ->
  List.nth_error s.(s_tables) i = Some ti ->
  typing.tab_typing ti tt ->
  external_typing s (MED_table (Mk_tableidx i)) (ET_tab tt) 
| ETY_mem :
  forall (s : store_record) (i : nat) (m : memory) (mt : memory_type),
  i < List.length s.(s_mems) ->
  List.nth_error s.(s_mems) i = Some m ->
  typing.mem_typing m mt ->
  external_typing s (MED_mem (Mk_memidx i)) (ET_mem mt)
| ETY_glob :
  forall (s : store_record) (i : nat) (g : global) (gt : global_type),
  i < List.length s.(s_globals) ->
  List.nth_error s.(s_globals) i = Some g ->
  typing.global_agree g gt ->
  external_typing s (MED_global (Mk_globalidx i)) (ET_glob gt)
| ETY_tag :
  forall s i tf,
    i < List.length s.(s_tags) ->
    List.nth_error s.(s_tags) i = Some tf ->
  external_typing s (MED_tag (Mk_tagidx i)) (ET_tag tf)
.


Definition instantiate_globals inst (s' : store_record) m (g_inits: list value_num) : Prop :=
  List.Forall2 (fun g (v: value_num) =>
      opsem.reduce_trans (s', (Build_frame nil inst), operations.to_e_list g.(modglob_init))
                         (s', (Build_frame nil inst), [::AI_basic (BI_const v)]))
    m.(mod_globals) g_inits.

Definition instantiate_elem inst (s' : store_record) m e_offs : Prop :=
  List.Forall2 (fun e c =>
      opsem.reduce_trans (s', (Build_frame nil inst), operations.to_e_list e.(modelem_offset))
                         (s', (Build_frame nil inst), [::AI_basic (BI_const (VAL_int32 c))]))
    m.(mod_elem)
    e_offs.

Definition instantiate_data inst (s' : store_record) m d_offs : Prop :=
  List.Forall2 (fun d c =>
      opsem.reduce_trans (s', (Build_frame nil inst), operations.to_e_list d.(moddata_offset))
                         (s', (Build_frame nil inst), [::AI_basic (BI_const (VAL_int32 c))]))
    m.(mod_data)
    d_offs.

Definition nat_of_int (i : i32) : nat :=
  BinInt.Z.to_nat i.(Wasm_int.Int32.intval).

Definition N_of_int (i : i32) : N :=
  BinInt.Z.to_N i.(Wasm_int.Int32.intval).

Definition check_bounds_elem (inst : instance) (s : store_record) (m : module) (e_offs : seq i32) : bool :=
  seq.all2
    (fun e_off e =>
      match List.nth_error inst.(inst_tab) (match e.(modelem_table) with Mk_tableidx i => i end) with
      | None => false
      | Some i =>
        match List.nth_error s.(s_tables) i with
        | None => false
        | Some ti =>
          N.leb (N.add (N_of_int e_off) (N.of_nat (List.length e.(modelem_init)))) (N.of_nat (List.length ti.(table_data)))
        end
      end)
      e_offs
      m.(mod_elem).

Definition length_mem (m : memory) : N :=
  length_mem m.(mem_data).

Definition check_bounds_data (inst : instance) (s : store_record) (m : module) (d_offs : seq i32) : bool :=
  seq.all2
    (fun d_off d =>
      match List.nth_error inst.(inst_memory) (match d.(moddata_data) with Mk_memidx i => i end) with
      | None => false
      | Some i =>
        match List.nth_error s.(s_mems) i with
        | None => false
        | Some mem =>
          N.leb (N.add (N_of_int d_off) (N.of_nat (List.length d.(moddata_init)))) (length_mem mem)
        end
      end)
      d_offs
      m.(mod_data).

Definition check_start m inst start : bool :=
  let start' :=
    operations.option_bind
    (fun i_s =>
      List.nth_error inst.(inst_funcs) (match i_s.(modstart_func) with Mk_funcidx i => i end))
    m.(mod_start) in
  start' == start.

Definition instantiate 
                       (s : store_record) (m : module) (v_imps : list v_ext)
                       (z : (store_record * instance * list module_export) * option nat) : Prop :=
  let '((s_end, inst, v_exps), start) := z in
  exists t_imps t_exps s' (g_inits : list value_num) e_offs d_offs,
    module_typing m t_imps t_exps /\
    List.Forall2 (external_typing s) v_imps t_imps /\
    alloc_module s m v_imps g_inits (s', inst, v_exps) /\
    instantiate_globals inst s' m g_inits /\
    instantiate_elem inst s' m e_offs /\
    instantiate_data inst s' m d_offs /\
    check_bounds_elem inst s' m e_offs /\
    check_bounds_data inst s' m d_offs /\
    check_start m inst start /\
    let s'' := init_tabs s' inst (map (fun o => BinInt.Z.to_nat o.(Wasm_int.Int32.intval)) e_offs) m.(mod_elem) in
    (s_end : store_record_eqType)
      == init_mems s'' inst (map (fun o => BinInt.Z.to_N o.(Wasm_int.Int32.intval)) d_offs) m.(mod_data).
