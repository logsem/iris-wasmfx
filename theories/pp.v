(** Pretty-printer **)

Require Import Coq.Strings.String.
From compcert Require Import Floats.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
Require Import Coq.Init.Decimal.
Require Import bytes_pp datatypes interpreter.
Require BinNatDef.
Require Import ansi list_extra.

Open Scope string_scope.


Definition newline_char : Ascii.ascii := Ascii.ascii_of_byte Byte.x0a.

Definition newline : string := String newline_char EmptyString.

(** Describe an indentation level. **)
Definition indentation := nat.

Fixpoint indent (i : indentation) (s : string) : string :=
  match i with
  | 0 => s
  | S i' => "  " ++ indent i' s
  end.

Definition type_style := FG_cyan.

Definition pp_number_type (vt : number_type) : string :=
  let s :=
    match vt with
    | T_i32 => "i32"
    | T_i64 => "i64"
    | T_f32 => "f32"
    | T_f64 => "f64"
    end in
  with_fg type_style s.

Fixpoint pp_reference_type (tr : reference_type) : string :=
  match tr with
  | T_funcref tf => "func " ++ pp_function_type tf
  | T_contref tf => "cont " ++ pp_function_type tf
  | T_exnref => "exn"
  end 

with pp_value_type (vt : value_type) : string :=
       match vt with
       | T_ref rt => pp_reference_type rt
       | T_num t => pp_number_type t
       end

(*with pp_value_types_aux (vts : list value_type) : string :=
       match vts with
       | [::] => "]"
       | [:: v] => pp_value_type v ++ "]"
       | v :: q => pp_value_type v ++ ", " ++ pp_value_types_aux q
       end 
       
with pp_value_types (vts : list value_type) : string :=
       "[" ++ pp_value_types_aux vts
(*       "[" ++ String.concat ", " (List.map pp_value_type vts) ++ "]" *)
*)

with pp_function_type (tf : function_type) : string :=
       let '(Tf ts1 ts2) := tf in
       "[" ++ String.concat ", " (List.map pp_value_type ts1) ++ "]"
           ++ "->" ++ 
           "[" ++ String.concat ", " (List.map pp_value_type ts2) ++ "]" 
           (*  pp_value_types ts1 ++ " -> " ++ pp_value_types ts2. *)
.

Definition pp_value_types ts1 : string :=
  "[" ++ String.concat ", " (List.map pp_value_type ts1) ++ "]".

Definition pp_block_tf (tf : function_type) : string :=
  match tf with
  | Tf nil nil => ""
  | Tf nil (cons vt nil) => " " ++ pp_value_type vt
  | Tf nil _ => " error!"
  | Tf _ _ => " error!"
  end.

Fixpoint string_of_uint (i : uint) : string :=
  match i with
  | Nil => ""
  | D0 i' => "0" ++ string_of_uint i'
  | D1 i' => "1" ++ string_of_uint i'
  | D2 i' => "2" ++ string_of_uint i'
  | D3 i' => "3" ++ string_of_uint i'
  | D4 i' => "4" ++ string_of_uint i'
  | D5 i' => "5" ++ string_of_uint i'
  | D6 i' => "6" ++ string_of_uint i'
  | D7 i' => "7" ++ string_of_uint i'
  | D8 i' => "8" ++ string_of_uint i'
  | D9 i' => "9" ++ string_of_uint i'
  end.

Definition pp_immediate (i : immediate) : string :=
  (* TODO: it's not clear that's the right way to print it, but hey *)
  string_of_uint (Nat.to_uint i).

Definition pp_i32 i :=
  pp_immediate (BinIntDef.Z.to_nat (Wasm_int.Int32.unsigned i)).

Definition pp_i64 i :=
  pp_immediate (BinIntDef.Z.to_nat (Wasm_int.Int64.unsigned i)).

(* TODO: all this printing of floats business is highly dubious,
   and completely untested *)
Fixpoint bool_list_of_pos (acc : list bool) (p : BinNums.positive) :=
  match p with
  | BinNums.xI p' => bool_list_of_pos (true :: acc) p'
  | BinNums.xO p' => bool_list_of_pos (false :: acc) p'
  | BinNums.xH => true :: acc
  end.

Open Scope list.

Fixpoint pp_bools (acc : list Byte.byte) (bools : list bool) : list Byte.byte :=
  (* TODO: I am ashamed I wrote this *)
  match bools with
  | nil => acc
  | b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: bools' =>
    pp_bools (Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, b8))))))) :: acc) bools'
  | b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 ::  nil =>
    Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (b7, false))))))) :: acc
  | b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: nil =>
    Byte.of_bits (b1, (b2, (b3, (b4, (b5, (b6, (false, false))))))) :: acc
  | b1 :: b2 :: b3 :: b4 :: b5 :: nil =>
    Byte.of_bits (b1, (b2, (b3, (b4, (b5, (false, (false, false))))))) :: acc
  | b1 :: b2 :: b3 :: b4 :: nil =>
    Byte.of_bits (b1, (b2, (b3, (b4, (false, (false, (false, false))))))) :: acc
  | b1 :: b2 :: b3 :: nil =>
    Byte.of_bits (b1, (b2, (b3, (false, (false, (false, (false, false))))))) :: acc
  | b1 :: b2 :: nil =>
    Byte.of_bits (b1, (b2, (false, (false, (false, (false, (false, false))))))) :: acc
  | b1 :: nil =>
    Byte.of_bits (b1, (false, (false, (false, (false, (false, (false, false))))))) :: acc
  end.

Definition pp_f32 (f : float32) : string :=
  match BinIntDef.Z.to_N ((Float32.to_bits f).(Integers.Int.intval)) with
  | BinNums.N0 => "0"
  | BinNums.Npos p =>
    bytes_pp.hex_small_no_prefix_of_bytes_compact (pp_bools nil (bool_list_of_pos nil p))
  end.

Definition pp_f64 (f : float) : string :=
  match BinIntDef.Z.to_N ((Float.to_bits f).(Integers.Int64.intval)) with
  | BinNums.N0 => "0"
  | BinNums.Npos p =>
    bytes_pp.hex_small_no_prefix_of_bytes_compact (pp_bools nil (bool_list_of_pos nil p))
  end.

Definition pp_value_num (v : value_num) : string :=
  match v with
  | VAL_int32 i => pp_number_type T_i32 ++ ".const " ++ with_fg FG_green (pp_i32 i) ++ newline
  | VAL_int64 i => pp_number_type T_i64 ++ ".const " ++ with_fg FG_green (pp_i64 i) ++ newline
  | VAL_float32 f => pp_number_type T_f32 ++ ".const " ++ with_fg FG_green (pp_f32 f) ++ newline
  | VAL_float64 f => pp_number_type T_f64 ++ ".const " ++ with_fg FG_green (pp_f64 f) ++ newline
  end.

Definition pp_value_ref (v : value_ref) : string :=
  match v with
  | VAL_ref_null r => "(" ++ pp_reference_type r ++ ").null" ++ newline
  | VAL_ref_func f => "ref.func " ++ pp_immediate f ++ newline
  | VAL_ref_cont f => "ref.cont " ++ pp_immediate f ++ newline
  | VAL_ref_exn e _ => "ref.exn" ++ pp_immediate e ++ newline
  end .

Definition pp_value (v : value) : string :=
  match v with
  | VAL_num v => pp_value_num v
  | VAL_ref v => pp_value_ref v
  end.

Definition pp_values (vs : list value) : string :=
  String.concat " " (List.map pp_value vs).

Definition pp_values_hint_empty (vs : list value) : string :=
  match vs with
  | nil => "(empty)"
  | _ => pp_values vs
  end.

Definition pp_unary_op_i (uoi : unop_i) : string :=
  match uoi with
  | UOI_clz => "clz"
  | UOI_ctz => "ctz"
  | UOI_popcnt => "popcnt"
  end.

Definition pp_unary_op_f (uof : unop_f) : string :=
  match uof with
  | UOF_neg => "neg"
  | UOF_abs => "abs"
  | UOF_ceil => "ceil"
  | UOF_floor => "floor"
  | UOF_trunc => "trunc"
  | UOF_nearest => "nearest"
  | UOF_sqrt => "sqrt"
  end.

Definition pp_sx (s : sx) : string :=
  match s with
  | SX_U => "u"
  | SX_S => "s"
  end.

Definition pp_binary_op_i (boi : binop_i) : string :=
  match boi with
  | BOI_add => "add"
  | BOI_sub => "sub"
  | BOI_mul => "mul"
  | BOI_div s => "div_" ++ pp_sx s
  | BOI_rem s => "rem_" ++ pp_sx s
  | BOI_and => "and"
  | BOI_or => "or"
  | BOI_xor => "xor"
  | BOI_shl => "shl"
  | BOI_shr s => "shr_" ++ pp_sx s
  | BOI_rotl => "rotl"
  | BOI_rotr => "rotr"
  end.

Definition pp_binary_op_f (bof : binop_f) : string :=
  match bof with
  | BOF_add => "add"
  | BOF_sub => "sub"
  | BOF_mul => "mul"
  | BOF_div => "div"
  | BOF_min => "min"
  | BOF_max => "max"
  | BOF_copysign => "copysign"
  end.

Definition pp_rel_op_i (roi : relop_i) : string :=
  match roi with
  | ROI_eq => "eq"
  | ROI_ne => "ne"
  | ROI_lt s => "lt_" ++ pp_sx s
  | ROI_gt s => "gt_" ++ pp_sx s
  | ROI_le s => "le_" ++ pp_sx s
  | ROI_ge s => "ge_" ++ pp_sx s
  end.

Definition pp_rel_op_f (rof : relop_f) : string :=
  match rof with
  | ROF_eq => "eq"
  | ROF_ne => "ne"
  | ROF_lt => "lt"
  | ROF_gt => "gt"
  | ROF_le => "ne"
  | ROF_ge => "ge"
  end.

Definition pp_ao a o : string :=
  pp_immediate a ++ " " ++ pp_immediate o.

Definition pp_packing (p : packed_type) :=
  match p with
  | Tp_i8 => "8"
  | Tp_i16 => "16"
  | Tp_i32 => "32"
  end.

Definition pp_ps (ps : packed_type * sx) : string :=
  let '(p, s) := ps in
  pp_packing p ++ "_" ++ pp_sx s.

Definition be_style := FG_magenta.

Definition pp_type_identifier x :=
  match x with
  | Type_lookup i => pp_immediate i
  | Type_explicit tf => pp_function_type tf
  end.

Definition pp_continuation_clause_identifier h : string :=
  match h with
  | HC_catch (Mk_tagident x) y => "On " ++ pp_immediate x ++ " do " ++ pp_immediate y
  | HC_switch (Mk_tagident x) => "On " ++ pp_immediate x ++ " switch"
  end.

Definition pp_continuation_clauses_identifier hs : string :=
  "(" ++ String.concat ", " (List.map pp_continuation_clause_identifier hs) ++ ")" .

Definition pp_exception_clause_identifier h : string :=
  match h with
  | HE_catch (Mk_tagident x) y => "On " ++ pp_immediate x ++ " do " ++ pp_immediate y
  | HE_catch_ref (Mk_tagident x) y => "On ref " ++ pp_immediate x ++ " do " ++ pp_immediate y
  | HE_catch_all x => "Else do " ++ pp_immediate x
  | HE_catch_all_ref x => "Else ref do " ++ pp_immediate x
  end .

Definition pp_exception_clauses_identifier hs : string :=
  "(" ++ String.concat ", " (List.map pp_exception_clause_identifier hs) ++ ")" .

Definition pp_continuation_clause h : string :=
  match h with
  | DC_catch (Mk_tagidx x) y => "On " ++ pp_immediate x ++ " do " ++ pp_immediate y
  | DC_switch (Mk_tagidx x) => "On " ++ pp_immediate x ++ " switch"
  end.

Definition pp_continuation_clauses hs : string :=
  "(" ++ String.concat ", " (List.map pp_continuation_clause hs) ++ ")" .

Definition pp_exception_clause h : string :=
  match h with
  | DE_catch (Mk_tagidx x) y => "On " ++ pp_immediate x ++ " do " ++ pp_immediate y
  | DE_catch_ref (Mk_tagidx x) y => "On ref " ++ pp_immediate x ++ " do " ++ pp_immediate y
  | DE_catch_all x => "Else do " ++ pp_immediate x
  | DE_catch_all_ref x => "Else ref do " ++ pp_immediate x
  end .

Definition pp_exception_clauses hs : string :=
  "(" ++ String.concat ", " (List.map pp_exception_clause hs) ++ ")" .


Fixpoint pp_basic_instruction (i : indentation) (be : basic_instruction) : string :=
  let pp_basic_instructions bes i :=
    String.concat "" (List.map (pp_basic_instruction (S i)) bes) in
  match be with
  | BI_unreachable => indent i (with_fg be_style "unreachable" ++ newline)
  | BI_nop => indent i (with_fg be_style "nop" ++ newline)
  | BI_drop => indent i (with_fg be_style "drop" ++ newline)
  | BI_select => indent i (with_fg be_style "select" ++ newline)
  | BI_block tf bes =>
    indent i (with_fg be_style "block" ++ with_fg type_style (pp_block_tf tf) ++ newline)
    ++ pp_basic_instructions bes (S i)
    ++ indent i (with_fg be_style "end" ++ newline)
  | BI_loop tf bes =>
    indent i (with_fg be_style "loop" ++ with_fg type_style (pp_block_tf tf) ++ newline)
    ++ pp_basic_instructions bes (S i)
    ++ indent i (with_fg be_style "end" ++ newline)
  | BI_if tf bes nil =>
    indent i (with_fg be_style "if" ++ with_fg type_style (pp_block_tf tf) ++ newline)
    ++ pp_basic_instructions bes (S i)
    ++ indent i (with_fg be_style "end" ++ newline)
  | BI_if tf bes1 bes2 =>
    indent i (with_fg be_style "if" ++ with_fg type_style (pp_block_tf tf) ++ newline)
    ++ pp_basic_instructions bes1 (S i)
    ++ indent i (with_fg be_style "else" ++ newline)
    ++ pp_basic_instructions bes2 (S i)
    ++ indent i (with_fg be_style "end" ++ newline)
  | BI_br x =>
    indent i (with_fg be_style "br " ++ pp_immediate x ++ newline)
  | BI_br_if x =>
    indent i (with_fg be_style "br_if " ++ pp_immediate x ++ newline)
  | BI_br_table is_ i =>
    indent i (with_fg be_style "br_table " ++ String.concat " " (List.map pp_immediate is_) ++ " " ++ pp_immediate i ++ newline)
  | BI_return =>
    indent i (with_fg be_style "return" ++ newline)
  | BI_call x =>
    indent i (with_fg be_style "call " ++ pp_immediate x ++ newline)
  | BI_call_indirect x =>
    indent i (with_fg be_style "call_indirect " ++ pp_type_identifier x ++ newline)
  | BI_get_local x =>
    indent i (with_fg be_style "local.get " ++ pp_immediate x ++ newline)
  | BI_set_local x =>
    indent i (with_fg be_style "local.set " ++ pp_immediate x ++ newline)
  | BI_tee_local x =>
    indent i (with_fg be_style "local.tee " ++ pp_immediate x ++ newline)
  | BI_get_global x =>
    indent i (with_fg be_style "global.get " ++ pp_immediate x ++ newline)
  | BI_set_global x =>
    indent i (with_fg be_style "global.set " ++ pp_immediate x ++ newline)
  | BI_load vt None a o =>
    indent i (pp_number_type vt ++ ".load " ++ pp_ao a o ++ newline)
  | BI_load vt (Some ps) a o =>
    indent i (pp_number_type vt ++ ".load" ++ pp_ps ps ++ " " ++ pp_ao a o ++ newline)
  | BI_store vt None a o =>
    indent i (pp_number_type vt ++ ".store " ++ pp_ao a o ++ newline)
  | BI_store vt (Some p) a o =>
    indent i (pp_number_type vt ++ ".store" ++ pp_packing p ++ " " ++ pp_ao a o ++ newline)
  | BI_current_memory =>
    indent i (with_fg be_style "memory.size" ++ newline ++ newline)
  | BI_grow_memory =>
    indent i (with_fg be_style "memory.grow" ++ newline)
  | BI_const v =>
    indent i (pp_value_num v)
  | BI_unop vt (Unop_i uoi) =>
    indent i (pp_number_type vt ++ "." ++ pp_unary_op_i uoi ++ newline)
  | BI_unop vt (Unop_f uof) =>
    indent i (pp_number_type vt ++ "." ++ pp_unary_op_f uof ++ newline)
  | BI_binop vt (Binop_i boi) =>
    indent i (pp_number_type vt ++ "." ++ pp_binary_op_i boi ++ newline)
  | BI_binop vt (Binop_f bof) =>
    indent i (pp_number_type vt ++ "." ++ pp_binary_op_f bof ++ newline)
  | BI_testop vt Eqz =>
    indent i (pp_number_type vt ++ ".eqz" ++ newline)
  | BI_relop vt (Relop_i roi) =>
    indent i (pp_number_type vt ++ "." ++ pp_rel_op_i roi ++ newline)
  | BI_relop vt (Relop_f rof) =>
    indent i (pp_number_type vt ++ "." ++ pp_rel_op_f rof ++ newline)
  | BI_cvtop vt1 cvtop vt2 sxo => "?" ++ newline (* TODO: ??? *)
                                     
  | BI_ref_null t => indent i (with_fg be_style "ref.null " ++ pp_reference_type t ++ newline)
| BI_ref_is_null => indent i (with_fg be_style "ref.is_null" ++ newline)
| BI_ref_func f => indent i (with_fg be_style "ref.func " ++ pp_immediate f ++ newline) 
| BI_call_reference x => indent i (with_fg be_style "call_reference " ++ pp_type_identifier x ++ newline) 
  | BI_try_table x hs bes =>
      indent i (with_fg be_style "try_table " ++ pp_type_identifier x ++ pp_exception_clauses_identifier hs ++ newline) ++
        pp_basic_instructions bes (S i) ++
        indent i (with_fg be_style "end" ++ newline)
| BI_throw k => indent i (with_fg be_style "throw " ++ pp_immediate k ++ newline)
| BI_throw_ref => indent i (with_fg be_style "throw_ref" ++ newline)

| BI_contnew x => indent i (with_fg be_style "cont.new " ++ pp_type_identifier x ++ newline)
| BI_resume x hs => indent i (with_fg be_style "resume " ++ pp_type_identifier x ++ pp_continuation_clauses_identifier hs ++ newline)
  | BI_suspend (Mk_tagident k) => indent i (with_fg be_style "suspend " ++ pp_immediate k ++ newline)
  | BI_switch j (Mk_tagident k) => indent i (with_fg be_style "switch " ++ pp_type_identifier j ++ pp_immediate k ++ newline)
| BI_contbind x y => indent i (with_fg be_style "cont.bind " ++ pp_type_identifier x ++ ", " ++ pp_type_identifier y ++ newline) 
| BI_resume_throw x k hs => indent i (with_fg be_style "resume_throw " ++ pp_type_identifier x ++ ", " ++ pp_immediate k ++ pp_continuation_clauses_identifier hs ++ newline)
                                     
  end.

Definition pp_basic_instructions n bes :=
  String.concat "" (List.map (pp_basic_instruction n) bes).

Definition pp_hostfuncidx (i : hostfuncidx) : string :=
  match i with
  | Mk_hostfuncidx n => pp_immediate n
  end.

Definition pp_function_closure (n : indentation) (fc : function_closure) : string :=
  match fc with
  | FC_func_native i ft vs bes =>
    (* TODO: show instance? *)
    indent n ("native " ++ pp_function_type ft ++ newline) ++
    indent n ("value types " ++ pp_value_types vs ++ newline) ++
    indent n ("body" ++ newline) ++
    pp_basic_instructions (n.+1) bes ++
    indent n ("end native" ++ newline)
  | FC_func_host ft h =>
    indent n ("host " ++ pp_hostfuncidx h
              ++ " : " ++ pp_function_type ft ++ newline)
  end.

Definition string_of_nat (n : nat) : string :=
  string_of_uint (Nat.to_uint (BinNatDef.N.of_nat n)).

Definition ae_style := FG_blue.

Fixpoint pp_administrative_instruction (n : indentation) (e : administrative_instruction) : string :=
  let pp_administrative_instructions (n : nat) (es : list administrative_instruction) : string :=
    String.concat "" (List.map (pp_administrative_instruction n) es) in
  match e with
  | AI_basic be => pp_basic_instruction n be
  | AI_trap => indent n (with_fg ae_style "trap" ++ newline)
  | AI_invoke a =>
    indent n (with_fg ae_style "invoke" ++ string_of_nat a ++ newline)
  (*    pp_function_closure (n.+1) fc*)
           
  | AI_label k es1 es2 =>
    indent n (with_fg ae_style "label " ++ string_of_nat k ++ newline) ++
    String.concat "" (List.map (pp_administrative_instruction (n.+1)) es1) ++
    indent n (with_fg ae_style "label_cont" ++ newline) ++
    String.concat "" (List.map (pp_administrative_instruction (n.+1)) es2) ++
    indent n (with_fg ae_style "end label" ++ newline)
  | AI_local n f es =>
    indent n (with_fg ae_style "local " ++ string_of_nat n ++ newline) ++
    (* TODO: inst? *)
    indent n (with_fg ae_style "with values " ++ pp_values_hint_empty f.(f_locs) ++ newline) ++
    pp_administrative_instructions (n.+1) es ++
    indent n (with_fg ae_style "end local" ++ newline)
  | AI_call_host tf h cvs =>
      indent n (with_fg ae_style "call host function " ++ pp_hostfuncidx h ++ newline) ++
        indent n (with_fg ae_style "with values " ++ pp_values_hint_empty cvs ++ newline)

  | AI_ref f => indent n (with_fg ae_style "ref " ++ pp_immediate f ++ newline) 
| AI_ref_exn e _ => indent n (with_fg ae_style "ref.exn " ++ pp_immediate e ++ newline)
  | AI_ref_cont f => indent n (with_fg ae_style "ref.cont " ++ pp_immediate f ++ newline)
  | AI_throw_ref_desugared vs a (Mk_tagidx x) => indent n (with_fg ae_style "throw_ref.desugarde " ++ pp_immediate a ++ with_fg ae_style " with tagidx " ++ pp_immediate x ++  with_fg ae_style " with values " ++ pp_values_hint_empty vs)
  | AI_suspend_desugared vs (Mk_tagidx i) => indent n (with_fg ae_style "suspend.desugared " ++ pp_immediate i ++ with_fg ae_style " with values " ++ pp_values_hint_empty vs) 
  | AI_switch_desugared vs k tf (Mk_tagidx i) => indent n (with_fg ae_style "switch.desugared " ++ pp_function_type tf ++ pp_immediate i ++ with_fg ae_style " with continuation " ++ pp_immediate k ++ with_fg ae_style " and values " ++ pp_values_hint_empty vs)
  | AI_handler hs es =>
      indent n (with_fg ae_style "handler " ++ pp_exception_clauses hs) ++
        String.concat "" (List.map (pp_administrative_instruction (n.+1)) es) ++
        indent n (with_fg ae_style "end handler" ++ newline)
  | AI_prompt ts hs es =>
      indent n (with_fg ae_style "prompt " ++ pp_value_types ts ++ pp_continuation_clauses hs) ++
        String.concat "" (List.map (pp_administrative_instruction (n.+1)) es) ++
        indent n (with_fg ae_style "end prompt" ++ newline)
             
  end.

Definition pp_administrative_instructions (n : nat) (es : list administrative_instruction) : string :=
  String.concat "" (List.map (pp_administrative_instruction n) es).

Definition pp_mutability (m : mutability) : string :=
  match m with
  | MUT_immut => "const"
  | MUT_mut => "var"
  end.

Definition pp_global (g : global) : string :=
  pp_mutability g.(g_mut) ++ " " ++ pp_value g.(g_val).

Definition pp_globals (n : indentation) (gs : list global) : string :=
  String.concat "" (mapi (fun i g => indent n (string_of_nat i ++ ": " ++ pp_global g ++ newline)) gs).

Definition pp_memories (n : indentation) (ms : list memory) : string :=
String.concat "" (mapi (fun i g => indent n (string_of_nat i ++ ": " ++ "TODO: memory" ++ newline)) ms).

Definition pp_store (n : indentation) (s : store_record) : string :=
  indent n ("globals" ++ newline) ++
  pp_globals (n.+1) s.(s_globals) ++
  indent n ("memories" ++ newline) ++
  pp_memories (n.+1) s.(s_mems).

Definition pp_config_tuple_except_store (cfg : config_tuple) : string :=
  let '(s, f, es) := cfg in
  pp_administrative_instructions 0 es ++
  "with values " ++ pp_values_hint_empty f.(f_locs) ++ newline.

Definition pp_res_tuple_except_store (res_cfg : res_tuple) : string :=
  let '(s, f, res) := res_cfg in
  match res with
  | RS_crash _ =>
    "crash" ++ newline ++
    "with values " ++ pp_values_hint_empty f.(f_locs) ++ newline
  | RS_break n vs =>
    "break " ++ string_of_nat n ++ "  " ++ pp_values_hint_empty vs ++ newline ++
    "with values " ++ pp_values_hint_empty f.(f_locs) ++ newline
  | RS_return vs_res =>
    "return " ++ pp_values_hint_empty vs_res ++ newline ++
    "with values " ++ pp_values_hint_empty f.(f_locs) ++ newline
  | RS_normal es =>
    "normal" ++ newline ++
    String.concat "" (List.map (pp_administrative_instruction 1) es) ++
    "with values " ++ pp_values_hint_empty f.(f_locs) ++ newline
  | RS_call_host tf h cvs =>
      "call host " ++ pp_hostfuncidx h ++ " with parameters " ++ pp_values_hint_empty cvs
                   ++ newline
  end.



(** As-is, [eqType] tends not to extract well.
  This section provides alternative definitions for better extraction. **)
(* Module PP (EH : Executable_Host).

Module Exec := convert_to_executable_host EH.
Import Exec. 

Section Show.

(*Variable show_host_function : EH.host_function -> string.*)

Definition pp_values : list value -> string := pp_values.

Definition pp_store : nat -> store_record -> string := pp_store _.

Definition pp_res_tuple_except_store : res_tuple -> string :=
  pp_res_tuple_except_store _.

Definition pp_config_tuple_except_store : config_tuple -> string :=
  pp_config_tuple_except_store _.

End Show.

End PP. *)

