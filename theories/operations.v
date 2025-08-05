(** Basic operations over Wasm datatypes **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Wasm Require Import common memory_list.
From Coq Require Import BinNat Eqdep_dec.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From compcert Require Floats.
From Wasm Require Export datatypes_properties list_extra.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Bullet Behavior "Strict Subproofs".

Definition AI_const v :=
  match v with
  | VAL_num n => AI_basic (BI_const n)
  | VAL_ref r =>
      match r with
      | VAL_ref_null t => AI_basic (BI_ref_null t)
      | VAL_ref_func x => AI_ref x
      | VAL_ref_cont x => AI_ref_cont x
      | VAL_ref_exn x i => AI_ref_exn x i
      end
  end
  .


Definition empty_frame :=
    Build_frame [::] (Build_instance [::] [::] [::] [::] [::] [::]).

(** read `len` bytes from `m` starting at `start_idx` *)
Definition read_bytes (m : memory) (start_idx : N) (len : nat) : option bytes :=
  those
    (List.map
      (fun off =>
        let idx := BinNatDef.N.add start_idx (N.of_nat off) in
        mem_lookup idx m.(mem_data))
    (iota 0 len)).

(** write bytes `bs` to `m` starting at `start_idx` *)
Definition write_bytes (m : memory) (start_idx : N) (bs : bytes) : option memory :=
  let x :=
    list_extra.fold_lefti
      (fun off dat_o b =>
        match dat_o with
        | None => None
        | Some dat =>
          let idx := BinNatDef.N.add start_idx (N.of_nat off) in
          mem_update idx b dat
        end)
      bs
      (Some m.(mem_data)) in
  match x with
  | Some dat => Some {| mem_data := dat; mem_max_opt := m.(mem_max_opt); |}
  | None => None
  end.

Definition upd_s_mem (s : store_record) (m : list memory) : store_record :=
  {|
    s_funcs := s.(s_funcs);
    s_tables := s.(s_tables);
    s_mems := m;
    s_globals := s.(s_globals);
    s_conts := s.(s_conts);
    s_tags := s.(s_tags);
    s_exns := s.(s_exns);
  |}.

Definition add_exn s e :=
   {|
    s_funcs := s.(s_funcs);
    s_tables := s.(s_tables);
    s_mems := s.(s_mems);
    s_globals := s.(s_globals);
    s_conts := s.(s_conts);
    s_tags := s.(s_tags);
    s_exns := s.(s_exns) ++ [:: e];
  |}.


Definition replace_nth_cont conts n (cont : continuation) :=
  take n conts ++ [:: cont] ++ drop (n + 1) conts.


Definition upd_s_cont (s : store_record) k cont : store_record :=
  {|
    s_funcs := s.(s_funcs);
    s_tables := s.(s_tables);
    s_mems := s.(s_mems);
    s_globals := s.(s_globals);
    s_exns := s.(s_exns);
    s_conts := replace_nth_cont (s_conts s) k cont;
    s_tags := s.(s_tags);
  |}.

Definition new_cont s cont :=
   {|
    s_funcs := s.(s_funcs);
    s_tables := s.(s_tables);
     s_mems := s.(s_mems);
     s_exns := s.(s_exns);
    s_globals := s.(s_globals);
    s_conts := (s_conts s) ++ [:: cont];
    s_tags := s.(s_tags);
  |}.

Definition desugar_tag_identifier inst x :=
  match x with
  | Mk_tagident x =>
      match List.nth_error (inst_tags inst) x with
      | Some a => Some (Mk_tagidx a)
      | None => None
      end
  end.

Definition desugar_continuation_clause inst h :=
  match h with
  | HC_catch x y =>
      match desugar_tag_identifier inst x with
      | Some x => Some (DC_catch x y)
      | None => None
      end
  | HC_switch x =>
      match desugar_tag_identifier inst x with
      | Some x => Some (DC_switch x)
      | None => None
      end
  end.

Definition desugar_exception_clause inst h :=
  match h with
  | HE_catch x y =>
      match desugar_tag_identifier inst x with
      | Some x => Some (DE_catch x y)
      | None => None
      end
  | HE_catch_ref x y =>
      match desugar_tag_identifier inst x with
      | Some x => Some (DE_catch_ref x y)
      | None => None
      end
  | HE_catch_all y => Some (DE_catch_all y)
  | HE_catch_all_ref y => Some (DE_catch_all_ref y)
  end.
                                   

Fixpoint firstx_exception hs (x : tagidx) :=
  match hs with
  | DE_catch y l :: q =>
      if x == y
      then Clause_label l
      else firstx_exception q x
  | DE_catch_ref y l :: q =>
      if x == y
      then Clause_label_ref l
      else firstx_exception q x
  | DE_catch_all l :: _ => Clause_label l
  | DE_catch_all_ref l :: _ => Clause_label_ref l
  | [::] => No_label
  end.

Fixpoint firstx_continuation_suspend hs x :=
  match hs with
  | DC_catch y l :: q =>
      if x == y
      then Some l
      else firstx_continuation_suspend q x
  | DC_switch _ :: q =>
(*      if x == y
      then Clause_switch
      else *) firstx_continuation_suspend q x
  | [::] => None
  end.


Fixpoint firstx_continuation_switch hs x :=
  match hs with
  | DC_catch _ l :: q =>
(*      if x == y
      then Clause_suspend l
      else *) firstx_continuation_switch q x
  | DC_switch y :: q =>
      if x == y
      then true
      else firstx_continuation_switch q x
  | [::] => false
  end.

(*
Definition firstx hs inst x :=
  match hs with
  | H_exception hs => firstx_exception hs inst x
  | H_continuation hs => firstx_continuation hs inst x
  end. 
*)

Fixpoint hhplug vs hh :=
  match hh with
  | HH_base bef aft => HH_base (bef ++ vs) aft
  | HH_label bef n cont hh aft => HH_label bef n cont (hhplug vs hh) aft
  | HH_local bef n f hh aft => HH_local bef n f (hhplug vs hh) aft
  | HH_handler bef hs hh aft => HH_handler bef hs (hhplug vs hh) aft
  | HH_prompt bef ts hs hh aft => HH_prompt bef ts hs (hhplug vs hh) aft
  end. 


Definition page_size : N := (N.of_nat 64) * (N.of_nat 1024).

Definition page_limit : N := N.of_nat 65536.

Definition ml_valid (m: memory_list) : Prop :=
  N.modulo (memory_list.length_mem m) page_size = N.of_nat 0.

Definition length_mem (m : memory) : N :=
  length_mem m.(mem_data).

Definition mem_size (m : memory) : N :=
  N.div (length_mem m) page_size.

(** Grow the memory a given number of pages.
  * @param len_delta: the number of pages to grow the memory by
  *)

Definition mem_grow (m : memory) (len_delta : N) : option memory :=
  let new_size := N.add (mem_size m) len_delta in
  let new_mem_data := mem_grow (N.mul len_delta page_size) m.(mem_data) in
  if N.leb new_size page_limit then
  match m.(mem_max_opt) with
  | Some maxlim =>
    if N.leb new_size maxlim then
        Some {|
          mem_data := new_mem_data;
          mem_max_opt := m.(mem_max_opt);
          |}
    else None
  | None =>
    Some {|
      mem_data := new_mem_data;
      mem_max_opt := m.(mem_max_opt);
      |}
  end
  else None.

(* TODO: We crucially need documentation here. *)

Definition load (m : memory) (n : N) (off : static_offset) (l : nat) : option bytes :=
  if N.leb (N.add n (N.add off (N.of_nat l))) (length_mem m)
  then read_bytes m (N.add n off) l
  else None.

Definition sign_extend (s : sx) (l : nat) (bs : bytes) : bytes :=
  (* TODO: implement sign extension *) bs.
(* TODO
  let: msb := msb (msbyte bytes) in
  let: byte := (match sx with sx_U => O | sx_S => if msb then -1 else 0) in
  bytes_takefill byte l bytes
*)

Definition load_packed (s : sx) (m : memory) (n : N) (off : static_offset) (lp : nat) (l : nat) : option bytes :=
  option_map (sign_extend s l) (load m n off lp).

Definition store (m : memory) (n : N) (off : static_offset) (bs : bytes) (l : nat) : option memory :=
  if N.leb (n + off + N.of_nat l) (length_mem m)
  then write_bytes m (n + off) (bytes_takefill #00 l bs)
  else None.

Definition store_packed := store.

Definition wasm_deserialise (bs : bytes) (vt : number_type) : value_num :=
  match vt with
  | T_i32 => VAL_int32 (Wasm_int.Int32.repr (common.Memdata.decode_int bs))
  | T_i64 => VAL_int64 (Wasm_int.Int64.repr (common.Memdata.decode_int bs))
  | T_f32 => VAL_float32 (Floats.Float32.of_bits (Integers.Int.repr (common.Memdata.decode_int bs)))
  | T_f64 => VAL_float64 (Floats.Float.of_bits (Integers.Int64.repr (common.Memdata.decode_int bs)))
  end.


Definition typeof_num (v : value_num) : number_type :=
  match v with
  | VAL_int32 _ => T_i32
  | VAL_int64 _ => T_i64
  | VAL_float32 _ => T_f32
  | VAL_float64 _ => T_f64
  end.

Definition cl_type (cl : function_closure) : function_type :=
  match cl with
  | FC_func_native _ tf _ _ => tf
  | FC_func_host tf _ => tf
  end.

Definition typeof_cont c :=
  match c with
  | Cont_hh tf _ | Cont_dagger tf => tf
  end.

Definition typeof_ref s (v : value_ref) : option reference_type :=
  match v with
  | VAL_ref_null t => Some t
  | VAL_ref_func i =>
      match List.nth_error (s_funcs s) i with
      | Some cl => Some (T_funcref (cl_type cl))
      | None => None
      end
  | VAL_ref_cont i =>
      match List.nth_error (s_conts s) i with
      | Some cont => Some (T_contref (typeof_cont cont))
      | _ => None
      end
  | VAL_ref_exn i t =>
      match List.nth_error (s_exns s) i with 
      | Some exn =>
          if (e_tag exn == t) then Some T_exnref
          else None
      | _ => None
      end
  end.

Definition typeof C (v : value) : option value_type :=
  match v with
  | VAL_num n => Some (T_num (typeof_num n))
  | VAL_ref r => option_map T_ref (typeof_ref C r)
  end.

Definition option_projl (A B : Type) (x : option (A * B)) : option A :=
  option_map fst x.

Definition option_projr (A B : Type) (x : option (A * B)) : option B :=
  option_map snd x.

Definition length_tnum (t : number_type) : nat :=
  match t with
  | T_i32 => 4
  | T_i64 => 8
  | T_f32 => 4
  | T_f64 => 8
  end.

Definition length_tp (tp : packed_type) : nat :=
  match tp with
  | Tp_i8 => 1
  | Tp_i16 => 2
  | Tp_i32 => 4
  end.

Definition is_int_t (t : number_type) : bool :=
  match t with
  | T_i32 => true
  | T_i64 => true
  | T_f32 => false
  | T_f64 => false
  end.

Definition is_float_t (t : number_type) : bool :=
  match t with
  | T_i32 => false
  | T_i64 => false
  | T_f32 => true
  | T_f64 => true
  end.

Definition is_mut (tg : global_type) : bool :=
  tg_mut tg == MUT_mut.


Definition app_unop_i (e : Wasm_int.type) (iop : unop_i) : Wasm_int.sort e -> Wasm_int.sort e :=
  let: Wasm_int.Pack u (Wasm_int.Class eqmx intmx) as e' := e
    return Wasm_int.sort e' -> Wasm_int.sort e' in
  match iop with
  | UOI_ctz => Wasm_int.int_ctz intmx
  | UOI_clz => Wasm_int.int_clz intmx
  | UOI_popcnt => Wasm_int.int_popcnt intmx
  end.

Definition app_unop_f (e : Wasm_float.type) (fop : unop_f) : Wasm_float.sort e -> Wasm_float.sort e :=
  let: Wasm_float.Pack u (Wasm_float.Class eqmx mx) as e' := e
    return Wasm_float.sort e' -> Wasm_float.sort e' in
  match fop with
  | UOF_neg => Wasm_float.float_neg mx
  | UOF_abs => Wasm_float.float_abs mx
  | UOF_ceil => Wasm_float.float_ceil mx
  | UOF_floor => Wasm_float.float_floor mx
  | UOF_trunc => Wasm_float.float_trunc mx
  | UOF_nearest => Wasm_float.float_nearest mx
  | UOF_sqrt => Wasm_float.float_sqrt mx
  end.

Definition app_unop (op: unop) (v: value_num) :=
  match op with
  | Unop_i iop =>
    match v with
    | VAL_int32 c => VAL_int32 (@app_unop_i i32t iop c)
    | VAL_int64 c => VAL_int64 (@app_unop_i i64t iop c)
    | _ => v
    end
  | Unop_f fop =>
    match v with
    | VAL_float32 c => VAL_float32 (@app_unop_f f32t fop c)
    | VAL_float64 c => VAL_float64 (@app_unop_f f64t fop c)
    | _ => v
    end
  end.

Definition app_binop_i (e : Wasm_int.type) (iop : binop_i)
    : Wasm_int.sort e -> Wasm_int.sort e -> option (Wasm_int.sort e) :=
  let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e
    return Wasm_int.sort e' -> Wasm_int.sort e' -> option (Wasm_int.sort e') in
  let: add_some := fun f c1 c2 => Some (f c1 c2) in
  match iop with
  | BOI_add => add_some (Wasm_int.int_add mx)
  | BOI_sub => add_some (Wasm_int.int_sub mx)
  | BOI_mul => add_some (Wasm_int.int_mul mx)
  | BOI_div SX_U => Wasm_int.int_div_u mx
  | BOI_div SX_S => Wasm_int.int_div_s mx
  | BOI_rem SX_U => Wasm_int.int_rem_u mx
  | BOI_rem SX_S => Wasm_int.int_rem_s mx
  | BOI_and => add_some (Wasm_int.int_and mx)
  | BOI_or => add_some (Wasm_int.int_or mx)
  | BOI_xor => add_some (Wasm_int.int_xor mx)
  | BOI_shl => add_some (Wasm_int.int_shl mx)
  | BOI_shr SX_U => add_some (Wasm_int.int_shr_u mx)
  | BOI_shr SX_S => add_some (Wasm_int.int_shr_s mx)
  | BOI_rotl => add_some (Wasm_int.int_rotl mx)
  | BOI_rotr => add_some (Wasm_int.int_rotr mx)
  end.

Definition app_binop_f (e : Wasm_float.type) (fop : binop_f)
    : Wasm_float.sort e -> Wasm_float.sort e -> option (Wasm_float.sort e) :=
  let: Wasm_float.Pack u (Wasm_float.Class _ mx) as e' := e
    return Wasm_float.sort e' -> Wasm_float.sort e' -> option (Wasm_float.sort e') in
  let: add_some := fun f c1 c2 => Some (f c1 c2) in
  match fop with
  | BOF_add => add_some (Wasm_float.float_add mx)
  | BOF_sub => add_some (Wasm_float.float_sub mx)
  | BOF_mul => add_some (Wasm_float.float_mul mx)
  | BOF_div => add_some (Wasm_float.float_div mx)
  | BOF_min => add_some (Wasm_float.float_min mx)
  | BOF_max => add_some (Wasm_float.float_max mx)
  | BOF_copysign => add_some (Wasm_float.float_copysign mx)
  end.

Definition app_binop (op: binop) (v1: value_num) (v2: value_num) :=
  match op with
  | Binop_i iop =>
    match v1 with
    | VAL_int32 c1 =>
      match v2 with
      | VAL_int32 c2 => option_map (fun v => VAL_int32 v) (@app_binop_i i32t iop c1 c2)
      |  _ => None
      end                              
    | VAL_int64 c1 =>
      match v2 with
      | VAL_int64 c2 => option_map (fun v => VAL_int64 v) (@app_binop_i i64t iop c1 c2)
      |  _ => None
      end                              
    | _ => None
    end
  | Binop_f fop =>
    match v1 with
    | VAL_float32 c1 =>
      match v2 with
      | VAL_float32 c2 => option_map (fun v => VAL_float32 v) (@app_binop_f f32t fop c1 c2)
      |  _ => None
      end                              
    | VAL_float64 c1 =>
      match v2 with
      | VAL_float64 c2 => option_map (fun v => VAL_float64 v) (@app_binop_f f64t fop c1 c2)
      |  _ => None
      end                              
    | _ => None
    end
  end.

Definition app_testop_i (e : Wasm_int.type) (o : testop) : Wasm_int.sort e -> bool :=
  let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e return Wasm_int.sort e' -> bool in
  match o with
  | Eqz => Wasm_int.int_eqz mx
  end.

Definition app_relop_i (e : Wasm_int.type) (rop : relop_i)
    : Wasm_int.sort e -> Wasm_int.sort e -> bool :=
  let: Wasm_int.Pack u (Wasm_int.Class _ mx) as e' := e
    return Wasm_int.sort e' -> Wasm_int.sort e' -> bool in
  match rop with
  | ROI_eq => Wasm_int.int_eq mx
  | ROI_ne => @Wasm_int.int_ne _
  | ROI_lt SX_U => Wasm_int.int_lt_u mx
  | ROI_lt SX_S => Wasm_int.int_lt_s mx
  | ROI_gt SX_U => Wasm_int.int_gt_u mx
  | ROI_gt SX_S => Wasm_int.int_gt_s mx
  | ROI_le SX_U => Wasm_int.int_le_u mx
  | ROI_le SX_S => Wasm_int.int_le_s mx
  | ROI_ge SX_U => Wasm_int.int_ge_u mx
  | ROI_ge SX_S => Wasm_int.int_ge_s mx
  end.

Definition app_relop_f (e : Wasm_float.type) (rop : relop_f)
    : Wasm_float.sort e -> Wasm_float.sort e -> bool :=
  let: Wasm_float.Pack u (Wasm_float.Class _ mx) as e' := e
    return Wasm_float.sort e' -> Wasm_float.sort e' -> bool in
  match rop with
  | ROF_eq => Wasm_float.float_eq mx
  | ROF_ne => @Wasm_float.float_ne _
  | ROF_lt => Wasm_float.float_lt mx
  | ROF_gt => Wasm_float.float_gt mx
  | ROF_le => Wasm_float.float_le mx
  | ROF_ge => Wasm_float.float_ge mx
  end.

Definition app_relop (op: relop) (v1: value_num) (v2: value_num) :=
  match op with
  | Relop_i iop =>
    match v1 with
    | VAL_int32 c1 =>
      match v2 with
      | VAL_int32 c2 => @app_relop_i i32t iop c1 c2
      |  _ => false
      end                              
    | VAL_int64 c1 =>
      match v2 with
      | VAL_int64 c2 => @app_relop_i i64t iop c1 c2
      |  _ => false
      end                              
    | _ => false
    end
  | Relop_f fop =>
    match v1 with
    | VAL_float32 c1 =>
      match v2 with
      | VAL_float32 c2 => @app_relop_f f32t fop c1 c2
      |  _ => false
      end                              
    | VAL_float64 c1 =>
      match v2 with
      | VAL_float64 c2 => @app_relop_f f64t fop c1 c2
      |  _ => false
      end                              
    | _ => false
    end
  end.

Definition types_num_agree (t : number_type) (v : value_num) : bool :=
  (typeof_num v) == t.

Definition types_ref_agree C (t : reference_type) (v : value_ref) : bool :=
  (typeof_ref C v) == Some t.

Definition types_agree C (t: value_type) (v : value) : bool :=
  (typeof C v) == Some t.



Definition rglob_is_mut (g : global) : bool :=
  g_mut g == MUT_mut.

Definition option_bind (A B : Type) (f : A -> option B) (x : option A) :=
  match x with
  | None => None
  | Some y => f y
  end.



Definition empty_instance := Build_instance [::] [::] [::] [::] [::].

Definition stypes (i : instance) j : option function_type :=
  match j with 
  | Type_lookup j => List.nth_error (inst_types i) j
  | Type_explicit t => Some t
  end
.

Definition sfunc_ind (s : store_record) (i : instance) (j : nat) : option nat :=
  List.nth_error (inst_funcs i) j.

Definition sfunc (s : store_record) (i : instance) (j : nat) : option function_closure :=
  option_bind (List.nth_error (s_funcs s)) (sfunc_ind s i j).

Definition sglob_ind (s : store_record) (i : instance) (j : nat) : option nat :=
  List.nth_error (inst_globs i) j.

Definition sglob (s : store_record) (i : instance) (j : nat) : option global :=
  option_bind (List.nth_error (s_globals s))
    (sglob_ind s i j).

Definition sglob_val (s : store_record) (i : instance) (j : nat) : option value_num :=
  option_map g_val (sglob s i j).

Definition smem_ind (s : store_record) (i : instance) : option nat :=
  match i.(inst_memory) with
  | nil => None
  | cons k _ => Some k
  end.

Definition tab_size (t: tableinst) : nat :=
  length (table_data t).

(**
  Get the ith table in the store s, and then get the jth index in the table;
  in the end, retrieve the corresponding function closure from the store.
 **)
(**
  There is the interesting use of option_bind (fun x => x) to convert an element
  of type option (option x) to just option x.
**)
Definition stab_index (s: store_record) (i j: nat) : option nat :=
  let: stabinst := List.nth_error (s_tables s) i in
  option_bind (fun x => x) (
    option_bind
      (fun stab_i => List.nth_error (table_data stab_i) j)
  stabinst).

Definition stab_addr (s: store_record) (f: frame) (c: nat) : option nat :=
  match f.(f_inst).(inst_tab) with
  | nil => None
  | ta :: _ => stab_index s ta c
  end.


Definition stab_s (s : store_record) (i j : nat) : option function_closure :=
  let n := stab_index s i j in
  option_bind
    (fun id => List.nth_error (s_funcs s) id)
  n.

Definition stab (s : store_record) (i : instance) (j : nat) : option function_closure :=
  match i.(inst_tab) with
  | nil => None
  | k :: _ => stab_s s k j
  end.

Definition update_list_at {A : Type} (l : seq A) (k : nat) (a : A) :=
  take k l ++ [::a] ++ List.skipn (k + 1) l.

Definition supdate_glob_s (s : store_record) (k : nat) (v : value_num) : option store_record :=
  option_map
    (fun g =>
      let: g' := Build_global (g_mut g) v in
      let: gs' := update_list_at (s_globals s) k g' in
      Build_store_record (s_funcs s) (s_tables s) (s_mems s) (s_tags s) gs' (s_exns s) (s_conts s))
    (List.nth_error (s_globals s) k).

Definition supdate_glob (s : store_record) (i : instance) (j : nat) (v : value_num) : option store_record :=
  option_bind
    (fun k => supdate_glob_s s k v)
    (sglob_ind s i j).



Definition glob_extension (* (s: store_record) *) (g1 g2: global) : bool.
Proof.
  destruct (g_mut g1) eqn:gmut1.
  - (* Immut *)
    exact ((g_mut g2 == MUT_immut) && (g_val g1 == g_val g2)).
  - (* Mut *)
    destruct (g_mut g2) eqn:gmut2.
    + exact false.
    + exact ((typeof_num (g_val g1) == typeof_num (g_val g2)) (* && (typeof_num (g_val g1) != None) *)).
(*
      destruct (g_val g1) as [n | n] eqn:T1;
        destruct n;
      lazymatch goal with
      | H1: g_val g1 = VAL_num (?T3 _) |- _ =>
          destruct (g_val g2) as [n | n] eqn:T2;
          destruct n;
          lazymatch goal with
          | H2: g_val g2 = VAL_num (T3 _) |- _ => exact true
          | _ => exact false
          end
      | H1: g_val g1 = VAL_ref (?T4 _) |- _ =>
          destruct (g_val g2) as [n | n] eqn:T5;
          destruct n;
          lazymatch goal with
          | H2: g_val g2 = VAL_ref (T4 _) |- _ => exact true
          | _ => exact false
          end
      | _ => exact false
      end. *)
Defined.

Definition tab_extension (t1 t2 : tableinst) :=
  (tab_size t1 <= tab_size t2) &&
  (t1.(table_max_opt) == t2.(table_max_opt)).

Definition mem_extension (m1 m2 : memory) :=
  (N.leb (mem_size m1) (mem_size m2)) && (mem_max_opt m1 == mem_max_opt m2).

Definition cont_extension (cont1 cont2: continuation) :=
  match cont2 with
  | Cont_dagger tf => typeof_cont cont1 == tf
  | _ => cont1 == cont2
  end
.
(*  typeof_cont cont1 == typeof_cont cont2.  *)

 Definition store_extension (s s' : store_record) : bool :=
   (s_funcs s == s_funcs s') &&
     (s_tags s == s_tags s') && 
     (all2 cont_extension s.(s_conts) (take (length s.(s_conts)) s'.(s_conts))) && 
(*     (s_conts s == take (length (s_conts s)) (s_conts s')) && *)
  (all2 tab_extension s.(s_tables) s'.(s_tables)) &&
  (all2 mem_extension s.(s_mems) s'.(s_mems)) &&
     (all2 (glob_extension (* s *) ) s.(s_globals) s'.(s_globals)) &&
     (s_exns s == take (length (s_exns s)) (s_exns s'))
. 

Definition vs_to_vts C (vs : seq value) := map (typeof C) vs.

Definition to_e_list (bes : seq basic_instruction) : seq administrative_instruction :=
  map AI_basic bes.

Definition to_b_single (e: administrative_instruction) : basic_instruction :=
  match e with
  | AI_basic x => x
  | _ => BI_const (VAL_int32 (Wasm_int.Int32.zero))
  end.

Definition to_b_list (es: seq administrative_instruction) : seq basic_instruction :=
  map to_b_single es.

Definition e_is_basic (e: administrative_instruction) :=
  match e with
  | AI_basic _ => True
  | _ => False
  end.
(*  exists be, e = AI_basic be. *) 

Definition es_is_basic (es: seq administrative_instruction) :=
  List.Forall e_is_basic es.
(*  match es with
  | [::] => True
  | e :: es' =>
    e_is_basic e /\ es_is_basic es'
  end. *)

(** [v_to_e_list]: 
    takes a list of [v] and gives back a list where each [v] is mapped to [Basic (EConst v)]. **)

(* Definition vref_to_e (vref: value_ref) : administrative_instruction :=
  match vref with
  | VAL_ref_null t => AI_basic (BI_ref_null t)
  | VAL_ref_func addr => AI_ref addr
  | VAL_ref_cont addr => AI_ref_cont addr
(*  | VAL_ref_extern addr => AI_ref_extern addr *)
  end.
Definition v_to_e (v: value) : administrative_instruction :=
  match v with
  | VAL_num v => AI_basic (BI_const v)
  | VAL_ref v => vref_to_e v
  end. *)
Definition v_to_e_list (ves : seq value) : seq administrative_instruction :=
  map AI_const ves.

(* 
Definition e_to_vref (e: administrative_instruction) : value_ref :=
  match e with
  | AI_basic (BI_ref_null t) => VAL_ref_null t
  | AI_ref addr => VAL_ref_func addr
  | AI_ref_cont addr => VAL_ref_cont addr
(*   | AI_ref_extern addr => VAL_ref_extern addr *) 
  | _ => VAL_ref_null (Tf [::] [::])
  end. 
*)

Definition e_to_vref_opt (e : administrative_instruction) : option value_ref :=
  match e with
  | AI_basic (BI_ref_null t) => Some (VAL_ref_null t)
  | AI_ref addr => Some (VAL_ref_func addr)
  | AI_ref_cont addr => Some (VAL_ref_cont addr)
  | AI_ref_exn addr addr' => Some (VAL_ref_exn addr addr')
(*  | AI_ref_extern addr => Some (VAL_ref_extern addr) *)
  | _ => None
  end.

(*
Definition e_to_v (e: administrative_instruction) : value :=
  match e with
  | AI_basic (BI_const v) => VAL_num v
  | _ => VAL_ref (e_to_vref e)
  end.
*)

(* Definition e_to_v_list (es: seq administrative_instruction) : list value :=
  map e_to_v es. *)

Definition e_to_v_opt (e: administrative_instruction) : option value :=
  match e with
  | AI_basic (BI_const v) => Some (VAL_num v)
  | _ => option_map VAL_ref (e_to_vref_opt e)
  end.

Definition e_to_v_list_opt (es: list administrative_instruction) : option (list value) :=
  those (map e_to_v_opt es).


Definition is_const (e : administrative_instruction) : bool :=
  match e_to_v_opt e with
  | Some _ => true
  | None => false
  end. 

Definition const_list (es : seq administrative_instruction) : bool :=
  List.forallb is_const es.

Definition those_const_list (es : list administrative_instruction) : option (list value) :=
  those (List.map e_to_v_opt es).
  
(* interpreter related *)

Fixpoint split_vals (es : seq basic_instruction) : seq value * seq basic_instruction :=
  match es with
  | e :: es' =>
      match e_to_v_opt (AI_basic e) with
      | Some v =>
          let: (vs', es'') := split_vals es' in
          (v :: vs', es'')
      | None => (nil, es)
      end
  | nil => (nil, nil)
  end.



(** [split_vals_e es]: takes the maximum initial segment of [es] whose elements
    are all of the form [Basic (EConst v)];
    returns a pair of lists [(ves, es')] where [ves] are those [v]'s in that initial
    segment and [es] is the remainder of the original [es]. **)
Fixpoint split_vals_e (es : seq administrative_instruction) : seq value * seq administrative_instruction :=
  match es with
  | e :: es' =>
      match e_to_v_opt e with
      | Some v =>
          let: (vs', es'') := split_vals_e es' in
          (v :: vs', es'')
      | None => (nil, es)
      end
  | nil => (nil, nil)
  end.

Lemma split_vals_not_empty_res : forall es v vs es',
  split_vals_e es = (v :: vs, es') -> es <> [::].
Proof. by case. Qed.

Lemma split_vals_e_not_const es vs e es' :
  split_vals_e es = (vs, e :: es') -> is_const e -> False.
Proof.
  generalize dependent vs ; generalize dependent e ; generalize dependent es'. 
  induction es => //= ; intros.
  destruct a => //= ; try by inversion H ; subst. 
  - destruct b => //= ; try by inversion H ; subst.
    + destruct (split_vals_e es) as [??] eqn:Hes.
      destruct l0 => //=.
      inversion H ; subst.
      by eapply IHes.
    + destruct (split_vals_e es) as [??] eqn:Hes.
      destruct l0 => //=.
      inversion H; subst.
      by eapply IHes.
  - destruct (split_vals_e es) as [??] eqn:Hes.
      destruct l0 => //=.
      inversion H; subst.
      by eapply IHes.
  - destruct (split_vals_e es) as [??] eqn:Hes.
      destruct l0 => //=.
      inversion H; subst.
      by eapply IHes.
  - destruct (split_vals_e es) as [??] eqn:Hes.
    destruct l0 => //=.
    inversion H; subst.
    by eapply IHes.
Qed.




Fixpoint split_n (es : seq value) (n : nat) : seq value * seq value :=
  match (es, n) with
  | ([::], _) => ([::], [::])
  | (_, 0) => ([::], es)
  | (e :: esX, n.+1) =>
    let: (es', es'') := split_n esX n in
    (e :: es', es'')
  end.

Definition expect {A B : Type} (ao : option A) (f : A -> B) (b : B) : B :=
  match ao with
  | Some a => f a
  | None => b
  end.

Definition vs_to_es (vs : seq value) : seq administrative_instruction :=
  v_to_e_list (rev vs).

Definition e_is_trap (e : administrative_instruction) : bool :=
  match e with
  | AI_trap => true
  | _ => false
  end.

(** [es_is_trap es] is equivalent to [es == [:: Trap]]. **)
Definition es_is_trap (es : seq administrative_instruction) : bool :=
  match es with
  | [::e] => e_is_trap e
  | _ => false
  end.



(** Converting a result into a stack. **)
Definition result_to_stack (r : result) :=
  match r with
  | result_values vs => v_to_e_list vs
  | result_trap => [:: AI_trap]
  end.

Fixpoint lfill (k : nat) (lh : lholed) (es : seq administrative_instruction) : option (seq administrative_instruction) :=
  if lh is LH_prompt bef ts hs lh' aft then
    if const_list bef then
      if lfill k lh' es is Some lfilledk then
        Some (bef ++ [:: AI_prompt ts hs lfilledk] ++ aft)
      else None
    else None
  else
  if lh is LH_handler bef hs lh' aft then
    if const_list bef then
      if lfill k lh' es is Some lfilledk then
        Some (bef ++ [:: AI_handler hs lfilledk] ++ aft)
      else None
    else None
  else
  match k with
  | 0 =>
    if lh is LH_base vs es' then
      if const_list vs then Some (app vs (app es es')) else None
    else None
  | k'.+1 =>
    if lh is LH_rec vs n es' lh' es'' then
      if const_list vs then
        if lfill k' lh' es is Some lfilledk then
          Some (app vs (cons (AI_label n es' lfilledk) es''))
        else None
      else None
    else None
  end.

Definition lfilled (k : nat) (lh : lholed) (es : seq administrative_instruction) (es' : seq administrative_instruction) : bool :=
  if lfill k lh es is Some es'' then es' == es'' else false.

Inductive lfilledInd : nat -> lholed -> seq administrative_instruction -> seq administrative_instruction -> Prop :=
| LfilledBase: forall vs es es',
    const_list vs ->
    lfilledInd 0 (LH_base vs es') es (vs ++ es ++ es')
| LfilledRec: forall k vs n es' lh' es'' es LI,
    const_list vs ->
    lfilledInd k lh' es LI ->
    lfilledInd (k.+1) (LH_rec vs n es' lh' es'') es (vs ++ [ :: (AI_label n es' LI) ] ++ es'')
| LfilledHandler: forall bef hs lh' aft k es LI,
    const_list bef ->
    lfilledInd k lh' es LI ->
    lfilledInd k (LH_handler bef hs lh' aft) es (bef ++ [:: AI_handler hs LI] ++ aft)
| LfilledPrompt: forall bef ts hs lh' aft k es LI,
    const_list bef ->
    lfilledInd k lh' es LI ->
    lfilledInd k (LH_prompt bef ts hs lh' aft) es (bef ++ [:: AI_prompt ts hs LI] ++ aft)

.

Lemma lfilled_Ind_Equivalent: forall k lh es LI,
    lfilled k lh es LI <-> lfilledInd k lh es LI.
Proof.
  split.
  - move: k es LI. induction lh; intros k es LI Hfix.
    + destruct k => //. unfold lfilled in Hfix. simpl in Hfix.
      destruct (const_list l) eqn:Hl => //.
      move/eqP in Hfix. subst LI.
      constructor. done.
    + destruct k => //=. unfold lfilled in Hfix. simpl in Hfix.
      destruct (const_list l) eqn:Hl => //.
      destruct (lfill _ _ _) eqn:Hfill => //.
      move/eqP in Hfix. subst LI.
      constructor => //. apply IHlh => //.  unfold lfilled.
      rewrite Hfill => //.
    + unfold lfilled in Hfix. simpl in Hfix.
      destruct (const_list l) eqn:Hl => //.
      destruct (lfill _ _ _) eqn:Hfill => //.
      move/eqP in Hfix. subst LI.
      constructor => //. apply IHlh => //.  unfold lfilled.
      rewrite Hfill => //.
          + unfold lfilled in Hfix. simpl in Hfix.
      destruct (const_list l) eqn:Hl => //.
      destruct (lfill _ _ _) eqn:Hfill => //.
      move/eqP in Hfix. subst LI.
      constructor => //. apply IHlh => //.  unfold lfilled.
      rewrite Hfill => //.
  - intros HLF. induction HLF; unfold lfilled => //=.
    + rewrite H. done.
    + rewrite H. unfold lfilled in IHHLF.
      destruct (lfill _ _ _) => //.
      move/eqP in IHHLF. subst LI. done.
    + rewrite H. unfold lfilled in IHHLF.
      destruct (lfill _ _ _) => //.
      move/eqP in IHHLF. subst LI. done.
          + rewrite H. unfold lfilled in IHHLF.
      destruct (lfill _ _ _) => //.
      move/eqP in IHHLF. subst LI. done.
Qed.

Lemma lfilledP: forall k lh es LI,
    reflect (lfilledInd k lh es LI) (lfilled k lh es LI).
Proof.
  move => k lh es LI. destruct (lfilled k lh es LI) eqn:HLFBool.
  - apply ReflectT. by apply lfilled_Ind_Equivalent.
  - apply ReflectF. move=> HContra. apply lfilled_Ind_Equivalent in HContra.
    by rewrite HLFBool in HContra.
Qed.

Fixpoint lfill_exact (k : nat) (lh : lholed) (es : seq administrative_instruction) : option (seq administrative_instruction) :=
  if lh is LH_prompt bef ts hs lh' aft then
    if const_list bef then
      if lfill k lh' es is Some lfilledk then
        Some (bef ++ [:: AI_prompt ts hs lfilledk] ++ aft)
      else None
    else None
  else
    if lh is LH_handler bef hs lh' aft then
    if const_list bef then
      if lfill k lh' es is Some lfilledk then
        Some (bef ++ [:: AI_handler hs lfilledk] ++ aft)
      else None
    else None
  else
  match k with
  | 0 =>
    if lh is LH_base nil nil then Some es else None
  | k'.+1 =>
    if lh is LH_rec vs n es' lh' es'' then
      if const_list vs then
        if lfill_exact k' lh' es is Some lfilledk then
          Some (app vs (cons (AI_label n es' lfilledk) es''))
        else None
      else None
    else None
  end.




Definition lfilled_exact (k : nat) (lh : lholed) (es : seq administrative_instruction) (es' : seq administrative_instruction) : bool :=
  if lfill_exact k lh es is Some es'' then es' == es'' else false.

Fixpoint lh_depth lh :=
  match lh with
  | LH_base _ _ => 0
  | LH_rec _ _ _ lh _ => S (lh_depth lh)
  | LH_prompt _ _ _ lh _ => lh_depth lh
  | LH_handler _ _ lh _ => lh_depth lh
  end.


(* Definition update_avoiding x f :=
  match x with
  | Var_prompt x _ => Var_prompt x (f_inst f)
  | Var_handler x _ => Var_handler x (f_inst f)
  | No_var => No_var
  end. *)

Fixpoint hfill (x : avoiding) (hh : hholed) (es : seq administrative_instruction) : option (seq administrative_instruction) :=
  match hh with
  | HH_base bef aft =>
      if const_list bef
      then Some (bef ++ es ++ aft)
      else None
  | HH_label bef n cont hh aft =>
      if const_list bef then
      match hfill x hh es with
      | Some LI =>
          Some (bef ++ [:: AI_label n cont LI] ++ aft)
      | None => None
      end
      else None
  | HH_local bef n f hh aft =>
      if const_list bef then
      match hfill x hh es with
      | Some LI => Some (bef ++ [:: AI_local n f LI] ++ aft)
      | None => None
      end
      else None
  | HH_prompt bef ts hs hh aft =>
      if const_list bef then
        if match x with
             Var_prompt_suspend x =>
               firstx_continuation_suspend hs x == None
           | Var_prompt_switch x =>
               firstx_continuation_switch hs x == false
           | _ => true
           end
        then match hfill x hh es with
             | Some LI => Some (bef ++ [:: AI_prompt ts hs LI] ++ aft)
             | None => None
             end
        else None
      else None
  | HH_handler bef hs hh aft =>
      if const_list bef then
        if match x with
             Var_handler x => firstx_exception hs x == No_label
           | _ => true
           end
        then match hfill x hh es with
             | Some LI => Some (bef ++ [:: AI_handler hs LI] ++ aft)
             | None => None
             end
        else None
      else None
  end.


Definition hfilled (x : avoiding) (hh : hholed) (es : seq administrative_instruction) (es' : seq administrative_instruction) : bool :=
  if hfill x hh es is Some es'' then es' == es'' else false.

Inductive hfilledInd : avoiding -> hholed -> seq administrative_instruction -> seq administrative_instruction -> Prop :=
| HfilledBase: forall x vs es es',
    const_list vs ->
    hfilledInd x (HH_base vs es') es (vs ++ es ++ es')
| HfilledLabel: forall x vs n es' hh' es'' es LI,
    const_list vs ->
    hfilledInd x hh' es LI ->
    hfilledInd x (HH_label vs n es' hh' es'') es (vs ++ [ :: (AI_label n es' LI) ] ++ es'')
| HfilledLocal: forall x vs n f hh' es'' es LI,
    const_list vs ->
    hfilledInd x hh' es LI ->
    hfilledInd x (HH_local vs n f hh' es'') es (vs ++ [:: (AI_local n f LI) ] ++ es'')
| HfilledPrompt: forall bef ts hs hh' aft x es LI,
    const_list bef ->
    match x with
      Var_prompt_suspend x => 
        firstx_continuation_suspend hs x = None
    | Var_prompt_switch x =>
        firstx_continuation_switch hs x = false
    | _ => True
    end ->
    hfilledInd x hh' es LI ->
    hfilledInd x (HH_prompt bef ts hs hh' aft) es (bef ++ [:: AI_prompt ts hs LI] ++ aft)
| HfilledHandler: forall bef hs hh' aft x es LI,
    const_list bef ->
    match x with
      Var_handler x => 
        firstx_exception hs x = No_label
    | _ => True
    end ->
    hfilledInd x hh' es LI ->
    hfilledInd x (HH_handler bef hs hh' aft) es (bef ++ [:: AI_handler hs LI] ++ aft)
.

Lemma hfilled_Ind_Equivalent: forall x hh es LI,
    hfilled x hh es LI <-> hfilledInd x hh es LI.
Proof.
  split.
  - move: x es LI. induction hh; intros x es LI Hfix.
    + unfold hfilled in Hfix. simpl in Hfix.
      destruct (const_list l) eqn:Hl => //.
      move/eqP in Hfix. subst LI.
      constructor. done.
    + unfold hfilled in Hfix. simpl in Hfix.
      destruct (const_list l) eqn:Hl => //.
      destruct (hfill _ _ _) eqn:Hfill => //.
      move/eqP in Hfix. subst LI.
      constructor => //. apply IHhh => //.  unfold hfilled.
      rewrite Hfill => //.
    + unfold hfilled in Hfix. simpl in Hfix.
      destruct (const_list l) eqn:Hl => //.
      destruct (hfill _ _ _) eqn:Hfill => //.
      move/eqP in Hfix. subst LI.
      eapply HfilledLocal => //.
      apply IHhh => //.  unfold hfilled.
      rewrite Hfill => //.
    + unfold hfilled in Hfix. simpl in Hfix.
      destruct (const_list l) eqn:Hl => //.
      destruct x as [x | | |] => //.
      destruct (firstx_exception _ _ == _) eqn:Hclauses => //.
      move/eqP in Hclauses.
      all: destruct (hfill _ _ _) eqn:Hfill => //.
      all: move/eqP in Hfix.
      all: subst LI.
      all: constructor => //.
      all: apply IHhh => //.
      all: unfold hfilled => //.
      all: rewrite Hfill => //. 
    + unfold hfilled in Hfix. simpl in Hfix.
      destruct (const_list l) eqn:Hl => //.
      destruct x as [|x |x |] => //.
      2: destruct (firstx_continuation_suspend _ _ == _) eqn:Hclauses => //.
      3: destruct (firstx_continuation_switch _ _ == _) eqn:Hclauses => //. 
      2,3: move/eqP in Hclauses.
      all: destruct (hfill _ _ _) eqn:Hfill => //.
      all: move/eqP in Hfix.
      all: subst LI.
      all: constructor => //.
      all: apply IHhh => //.
      all: unfold hfilled.
      all: rewrite Hfill => //.
  - intros HLF. induction HLF; unfold hfilled => //=.
    + rewrite H. done.
    + rewrite H. unfold hfilled in IHHLF.
      destruct (hfill _ _ _) => //.
      move/eqP in IHHLF. subst LI. done.
    + rewrite H. unfold hfilled in IHHLF.
      destruct (hfill _ _ _) => //.
      move/eqP in IHHLF. subst LI. done.
    + rewrite H.
      destruct x as [|x |x|] => //.
      2,3: rewrite H0 eq_refl.
      all: unfold hfilled in IHHLF.
      all: destruct (hfill _ _ _) => //.
      all: move/eqP in IHHLF.
      all: subst LI.
      all: try done.
    + rewrite H.
      destruct x as [x | | |] => //.
      destruct (firstx_exception _ _ == _) eqn:Hclauses => //. 
      all: unfold hfilled in IHHLF.
      all: destruct (hfill _ _ _) => //.
      all: move/eqP in IHHLF.
      all: subst LI.
      all: try done.
      rewrite H0 in Hclauses. done.
Qed.

Lemma hfilledP: forall x hh es LI,
    reflect (hfilledInd x hh es LI) (hfilled x hh es LI).
Proof.
  move => x hh es LI. destruct (hfilled x hh es LI) eqn:HLFBool.
  - apply ReflectT. by apply hfilled_Ind_Equivalent.
  - apply ReflectF. move=> HContra. apply hfilled_Ind_Equivalent in HContra.
    by rewrite HLFBool in HContra.
Qed.

Definition result_types_agree C (ts : list value_type) r :=
  match r with
  | result_values vs => all2 (types_agree C) ts vs
  | result_trap => true
  end.

Definition load_store_t_bounds (a : alignment_exponent) (tp : option packed_type) (t : number_type) : bool :=
  match tp with
  | None => Nat.pow 2 a <= length_tnum t
  | Some tp' => (Nat.pow 2 a <= length_tp tp') && (length_tp tp' < length_tnum t) && (is_int_t t)
  end.

Definition cvt_i32 (s : option sx) (v : value_num) : option i32 :=
  match v with
  | VAL_int32 _ => None
  | VAL_int64 c => Some (wasm_wrap c)
  | VAL_float32 c =>
    match s with
    | Some SX_U => Wasm_float.float_ui32_trunc f32m c
    | Some SX_S => Wasm_float.float_ui32_trunc f32m c
    | None => None
    end
  | VAL_float64 c =>
    match s with
    | Some SX_U => Wasm_float.float_ui32_trunc f64m c
    | Some SX_S => Wasm_float.float_ui32_trunc f64m c
    | None => None
    end
  end.

Definition cvt_i64 (s : option sx) (v : value_num) : option i64 :=
  match v with
  | VAL_int32 c =>
    match s with
    | Some SX_U => Some (wasm_extend_u c)
    | Some SX_S => Some (wasm_extend_s c)
    | None => None
    end
  | VAL_int64 c => None
  | VAL_float32 c =>
    match s with
    | Some SX_U => Wasm_float.float_ui64_trunc f32m c
    | Some SX_S => Wasm_float.float_si64_trunc f32m c
    | None => None
    end
  | VAL_float64 c =>
    match s with
    | Some SX_U => Wasm_float.float_ui64_trunc f64m c
    | Some SX_S => Wasm_float.float_si64_trunc f64m c
    | None => None
    end
  end.

Definition cvt_f32 (s : option sx) (v : value_num) : option f32 :=
  match v with
  | VAL_int32 c =>
    match s with
    | Some SX_U => Some (Wasm_float.float_convert_ui32 f32m c)
    | Some SX_S => Some (Wasm_float.float_convert_si32 f32m c)
    | None => None
    end
  | VAL_int64 c =>
    match s with
    | Some SX_U => Some (Wasm_float.float_convert_ui64 f32m c)
    | Some SX_S => Some (Wasm_float.float_convert_si64 f32m c)
    | None => None
    end
  | VAL_float32 c => None
  | VAL_float64 c => Some (wasm_demote c)
  end.

Definition cvt_f64 (s : option sx) (v : value_num) : option f64 :=
  match v with
  | VAL_int32 c =>
    match s with
    | Some SX_U => Some (Wasm_float.float_convert_ui32 f64m c)
    | Some SX_S => Some (Wasm_float.float_convert_si32 f64m c)
    | None => None
    end
  | VAL_int64 c =>
    match s with
    | Some SX_U => Some (Wasm_float.float_convert_ui64 f64m c)
    | Some SX_S => Some (Wasm_float.float_convert_si64 f64m c)
    | None => None
    end
  | VAL_float32 c => Some (wasm_promote c)
  | VAL_float64 c => None
  end.


Definition cvt (t : number_type) (s : option sx) (v : value_num) : option value_num :=
  match t with
  | T_i32 => option_map VAL_int32 (cvt_i32 s v)
  | T_i64 => option_map VAL_int64 (cvt_i64 s v)
  | T_f32 => option_map VAL_float32 (cvt_f32 s v)
  | T_f64 => option_map VAL_float64 (cvt_f64 s v)
  end.

Definition bits (v : value_num) : bytes :=
  match v with
  | VAL_int32 c => serialise_i32 c
  | VAL_int64 c => serialise_i64 c
  | VAL_float32 c => serialise_f32 c
  | VAL_float64 c => serialise_f64 c
  end.

Definition bitzero (t : number_type) : value_num :=
  match t with
  | T_i32 => VAL_int32 (Wasm_int.int_zero i32m)
  | T_i64 => VAL_int64 (Wasm_int.int_zero i64m)
  | T_f32 => VAL_float32 (Wasm_float.float_zero f32m)
  | T_f64 => VAL_float64 (Wasm_float.float_zero f64m)
  end.

Definition n_zeros (ts : seq number_type) : seq value_num :=
  map bitzero ts.

Definition default_val (t: value_type) : value :=
  match t with
  | T_num t => VAL_num (bitzero t)
  | T_ref (T_funcref t) => VAL_ref (VAL_ref_null (T_funcref t))
  | T_ref (T_contref t) => VAL_ref (VAL_ref_null (T_contref t))
  | T_ref (T_exnref (* t *)) => VAL_ref (VAL_ref_null (T_exnref (* t *) )) (* placeholder *)
  end.

Definition default_vals (ts: seq value_type) : seq value :=
  map default_val ts.

(* TODO: lots of lemmas *)


Definition is_none_or {A : Type} (p : A -> bool) (x : option A) : bool :=
  match x with
  | None => true
  | Some y => p y
  end.

Lemma b2p: forall {T:eqType} (a b:T), a==b -> a=b.
Proof. move => T a b Hb. by move/eqP in Hb. Qed.


Lemma cat_app {A} (l1 : list A) l2 :
  cat l1 l2 = app l1 l2.
Proof. done. Qed.









Lemma first_values vs1 e1 es1 vs2 e2 es2 :
  (is_const e1 = false) ->
  (is_const e2 = false) ->
  const_list vs1 ->
  const_list vs2 ->
  vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2 ->
  vs1 = vs2 /\ e1 = e2 /\ es1 = es2.
Proof.
  intros He1 He2 Hvs1 Hvs2 Heq.
  generalize dependent vs2; induction vs1 ; intros.
  { destruct vs2 ; inversion Heq => //=. rewrite <- H0 in Hvs2.
    simpl in Hvs2. apply Bool.andb_true_iff in Hvs2 as [ Habs _ ].
    rewrite Habs in He1 => //.
  } 
  destruct vs2 ; inversion Heq.
  { rewrite H0 in Hvs1.
    simpl in Hvs1. apply Bool.andb_true_iff in Hvs1 as [ Habs _ ].
    rewrite Habs in He2 => //.
  }
  assert (vs1 = vs2 /\ e1 = e2 /\ es1 = es2) as H ; last by destruct H ; subst.
  apply IHvs1 => //=.
  - by apply Bool.andb_true_iff in Hvs1 as [ _ Hvs1 ].
  - by apply Bool.andb_true_iff in Hvs2 as [ _ Hvs2 ].  
Qed.


(*
Definition clause_addr_defined inst clause :=
  match clause with
  | HE_catch x _ | HE_catch_ref x _ =>
                    match List.nth_error inst.(inst_tags) x with
                    | Some _ => True
                    | None => False
                    end
  | _ => True
  end
.
*)
