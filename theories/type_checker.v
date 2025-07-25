(** Wasm type checker **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)
Require Import common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import operations typing datatypes_properties.




Inductive checker_type_aux : Type :=
| CTA_any : checker_type_aux
| CTA_any_reference : checker_type_aux
| CTA_some : value_type -> checker_type_aux.

Lemma checker_type_aux_eq_dec: forall (x y: checker_type_aux), { x = y } + { x <> y }.
Proof. decidable_equality. Qed.
Definition checker_type_aux_eqb v1 v2 := is_left (checker_type_aux_eq_dec v1 v2).
Definition eqchecker_type_auxP  : Equality.axiom checker_type_aux_eqb :=
  eq_dec_Equality_axiom checker_type_aux_eq_dec.

Canonical Structure checker_type_aux_eqMixin := Equality.Mixin eqchecker_type_auxP.
Canonical Structure checker_type_aux_eqType :=
  Eval hnf in Equality.Pack (sort := checker_type_aux) (Equality.Class checker_type_aux_eqMixin).

Inductive checker_type : Type :=
| CT_top_type : seq checker_type_aux -> checker_type
| CT_type : seq value_type -> checker_type
| CT_bot : checker_type.

Definition checker_type_eq_dec : forall v1 v2 : checker_type, {v1 = v2} + {v1 <> v2}.
Proof. decidable_equality. Defined.

Definition checker_type_eqb v1 v2 : bool := checker_type_eq_dec v1 v2.
Definition eqchecker_typeP : Equality.axiom checker_type_eqb :=
  eq_dec_Equality_axiom checker_type_eq_dec.

Canonical Structure checker_type_eqMixin := Equality.Mixin eqchecker_typeP.
Canonical Structure checker_type_eqType := Eval hnf in Equality.Pack (sort := checker_type) (Equality.Class checker_type_eqMixin).

Definition to_ct_list (ts : seq value_type) : seq checker_type_aux :=
  map CTA_some ts.

(**
Fixpoint ct_suffix (ts ts' : seq checker_type_aux) : bool :=
  (ts == ts')
  ||
  match ts' with
  | [::] => false
  | _ :: ts'' => ct_suffix ts ts''
  end.
**)

Definition ct_compat (t1 t2: checker_type_aux) : bool :=
  match t1 with
  | CTA_any => true
  | CTA_any_reference =>
      match t2 with
      | CTA_any | CTA_any_reference => true
      | CTA_some vt2 =>
          match vt2 with
          | T_ref _ => true
          | _ => false
          end
      end
  | CTA_some vt1 =>
    match t2 with
    | CTA_any => true
    | CTA_any_reference =>
        match vt1 with
        | T_ref _ => true
        | _ => false
        end 
    | CTA_some vt2 => (vt1 == vt2)
    end
  end.

Definition ct_list_compat (l1 l2: list checker_type_aux) : bool :=
  all2 ct_compat l1 l2.

Definition ct_suffix (ts ts' : list checker_type_aux) : bool :=
  (size ts <= size ts') && (ct_list_compat (drop (size ts' - size ts) ts') ts).

(**
  It looks like CT_bot stands for an error in typing.

  CT_top_type xyz means a stack with the top part being xyz??? This is guessed
    by looking at 'produce'... CT_type should refer to the type of the entire stack.

  produce seems to be for the result of a concatenation of two stacks. 
**)

Definition consume (t : checker_type) (cons : seq checker_type_aux) : checker_type :=
  match t with
  | CT_type ts =>
    if ct_suffix cons (to_ct_list ts)
    then CT_type (take (size ts - size cons) ts)
    else CT_bot
  | CT_top_type cts =>
    if ct_suffix cons cts
    then CT_top_type (take (size cts - size cons) cts)
    else
      (if ct_suffix cts cons
       then CT_top_type [::]
       else CT_bot)
  | _ => CT_bot
  end.

Definition produce (t1 t2 : checker_type) : checker_type :=
  match (t1, t2) with
  | (CT_top_type ts, CT_type ts') => CT_top_type (ts ++ (to_ct_list ts'))
  | (CT_type ts, CT_type ts') => CT_type (ts ++ ts')
  | (CT_type ts', CT_top_type ts) => CT_top_type ts
  | (CT_top_type ts', CT_top_type ts) => CT_top_type ts
  | _ => CT_bot
  end.

Definition type_update (curr_type : checker_type) (cons : seq checker_type_aux) (prods : checker_type) : checker_type :=
  produce (consume curr_type cons) prods.

Definition select_return_top (ts : seq checker_type_aux) (cta1 cta2 : checker_type_aux) : checker_type :=
  match (cta1, cta2) with
  | (_, CTA_any) => CT_top_type (take (length ts - 3) ts ++ [::cta1])
  | (CTA_any, _) => CT_top_type (take (length ts - 3) ts ++ [::cta2])
  | (_, CTA_any_reference) =>
      if ct_compat cta1 cta2 then CT_top_type (take (length ts - 3) ts ++ [::cta1])
      else CT_bot
  | (CTA_any_reference, _) =>
      if ct_compat cta1 cta2 then CT_top_type (take (length ts - 3) ts ++ [::cta2])
      else CT_bot
  | (CTA_some t1, CTA_some t2) =>
    if t1 == t2
    then CT_top_type (take (length ts - 3) ts ++ [::CTA_some t1])
    else CT_bot
  end.

Definition type_update_select (t : checker_type) : checker_type :=
  match t with
  | CT_type ts =>
    if (length ts >= 3) && (List.nth_error ts (length ts - 2) == List.nth_error ts (length ts - 3))
    then (consume (CT_type ts) [::CTA_any; CTA_some (T_num T_i32)])
    else CT_bot
  | CT_top_type ts =>
    match length ts with
    | 0 => CT_top_type [::CTA_any]
    | 1 => type_update (CT_top_type ts) [::CTA_some (T_num T_i32)] (CT_top_type [::CTA_any])
    | 2 => consume (CT_top_type ts) [::CTA_some (T_num T_i32)]
    | _ =>
      match List.nth_error ts (length ts - 2), List.nth_error ts (length ts - 3) with
      | Some ts_at_2, Some ts_at_3 =>
        type_update (CT_top_type ts) [::CTA_any; CTA_any; CTA_some (T_num T_i32)]
                    (select_return_top ts ts_at_2 ts_at_3)
                (* UPD: this is now the correct verified version *)
                    
      | _, _ => CT_bot (* TODO: is that OK? *)
      end
    end
  | CT_bot => CT_bot
  end.

Fixpoint same_lab_h (iss : seq nat) (lab_c : seq (seq value_type)) (ts : seq value_type) : option (seq value_type) :=
  match iss with
  | [::] => Some ts
  | i :: iss' =>
    if i >= length lab_c
    then None
    else
      match List.nth_error lab_c i with
      | None => None (* TODO *)
                  (* See comment to the same_lab predicate below in the same place. *)
      | Some xx =>
        if xx == ts then same_lab_h iss' lab_c xx
        else None
      end
  end.

(**
   So Br_table iss i needs to make sure that Br (each element in iss) and Br i would 
     consume the same type. Look at section 3.3.5.8 in the official spec.
**)
Definition same_lab (iss : seq nat) (lab_c : seq (seq value_type)) : option (seq value_type) :=
  match iss with
  | [::] => None
  | i :: iss' =>
    if i >= length lab_c
    then None
    else
      match List.nth_error lab_c i with
      | Some xx => same_lab_h iss' lab_c xx
      | None => None (* TODO: ??? *)
                  (* I think this case will never happen, since we've already
                       checked the length. Or we can remove the previous if. *)
                  (* We have to stick with line-by-line correspondance,
                    even if it means checking things twice. *)
      end
  end.


Definition c_types_agree (ct : checker_type) (ts' : seq value_type) : bool :=
  match ct with
  | CT_type ts => ts == ts'
  | CT_top_type ts => ct_suffix ts (to_ct_list ts')
  | CT_bot => false
  end.

Definition is_int (t: number_type) :=
  match t with
  | T_i32 => true
  | T_i64 => true
  | T_f32 => false
  | T_f64 => false
  end.

Definition is_float (t: number_type) :=
  match t with
  | T_i32 => false
  | T_i64 => false
  | T_f32 => true
  | T_f64 => true
  end.

Definition check_clause C cl t2s :=
  match cl with
  | HC_catch (Mk_tagident x) l =>
      match List.nth_error (tc_tags_t C) x with
      | Some (Tf t1s' t2s') =>
          match List.nth_error (tc_label C) l with
          | Some ts =>
              ts == t1s' ++ [:: T_ref (T_contref (Tf t2s' t2s))]
          | None => false
          end
      | _ => false
      end
  | HC_switch (Mk_tagident x) =>
      match List.nth_error (tc_tags_t C) x with
      | Some (Tf [::] ts) =>
          ts == t2s
      | _ => false
      end
  end.

Definition check_exception_clause C h :=
  match h with
  | HE_catch (Mk_tagident x) y =>
      match List.nth_error (tc_tags_t C) x with
      | Some (Tf ts [::]) =>
          match List.nth_error (tc_label C) y with
          | Some ts' =>
              ts == ts'
          | None => false
          end
      | _ => false
      end
  | HE_catch_ref (Mk_tagident x) y =>
      match List.nth_error (tc_tags_t C) x with
      | Some (Tf ts [::]) =>
          match List.nth_error (tc_label C) y with
          | Some ts' =>
              ts ++ [:: T_ref T_exnref]  == ts'
          | None => false
          end
      | _ => false
      end 
  | HE_catch_all y =>
      match List.nth_error (tc_label C) y with
      | Some [::] => true
      | _ => false
      end
  | HE_catch_all_ref y =>
      match List.nth_error (tc_label C) y with
      | Some [:: T_ref T_exnref] => true
      | _ => false
      end
  end .
  

              

Definition isolate_prefix (full: list value_type) suffix :=
  if length full >= length suffix then
    if drop (length full - length suffix) full == suffix then
      Some (take (length full - length suffix) full)
    else None
  else None.


Fixpoint check_single (C : t_context) (ts : checker_type) (be : basic_instruction) : checker_type :=
  let b_e_type_checker (C : t_context) (es : list basic_instruction) (tf : function_type) : bool :=
    match tf with
    | Tf tn tm =>
        c_types_agree (List.fold_left (check_single C) es (CT_type tn)) tm
    end
in
  if ts == CT_bot then CT_bot
  else
  match be with
  | BI_const v => type_update ts [::] (CT_type [::T_num (typeof_num v)])
  | BI_contnew i =>
      match get_type C i with
      | None => CT_bot (* Isa mismatch *)
      | Some (Tf tn tm) =>
        type_update ts (to_ct_list [::T_ref (T_funcref (Tf tn tm))]) (CT_type [:: T_ref (T_contref (Tf tn tm))])
      end
  | BI_resume_throw i x hs =>
      match get_type C i with
      | Some (Tf t1s t2s) =>
          match List.nth_error (tc_tags_t C) x with
          | Some (Tf ts' [::]) =>
              if List.forallb (fun cl => check_clause C cl t2s) hs
              then type_update ts (to_ct_list (ts' ++ [:: T_ref (T_contref (Tf t1s t2s))])) (CT_type t2s)
              else CT_bot
          | _ => CT_bot
          end
      | _ => CT_bot
      end 
  | BI_contbind i i' =>
      match get_type C i with
      | Some (Tf t1s' t2s') =>
          match get_type C i' with
          | Some (Tf t1s t2s) =>
              match isolate_prefix t1s' t1s with
              | Some ts' =>
                  if t2s == t2s' then
                    type_update ts (to_ct_list (ts' ++ [:: T_ref (T_contref (Tf t1s' t2s'))])) (CT_type [::T_ref (T_contref (Tf t1s t2s))])
                  else CT_bot
              | _ => CT_bot
              end
          | _ => CT_bot
          end
      | _ => CT_bot
      end
  | BI_suspend (Mk_tagident x) =>
      match List.nth_error (tc_tags_t C) x with
      | Some (Tf t1s t2s) => type_update ts (to_ct_list t1s) (CT_type t2s)
      | _ => CT_bot
      end
  | BI_switch i (Mk_tagident x) =>
      match get_type C i with
      | Some (Tf t1s t2s) =>
          match List.nth_error (tc_tags_t C) x with
          | Some (Tf [::] tmatch) =>
              if t2s == tmatch 
              then match separate_last t1s with
                   | Some (t1s', T_ref (T_contref (Tf t2s' tmatch))) =>
                       if t2s == tmatch
                       then type_update ts (to_ct_list (t1s' ++ [:: T_ref (T_contref (Tf t1s t2s))])) (CT_type t2s')
                       else CT_bot
                   | _ => CT_bot
                   end
              else CT_bot
          | _ => CT_bot
          end
      | None => CT_bot
      end
  | BI_resume i hs =>
      match get_type C i with
      | Some (Tf t1s t2s) =>
          if List.forallb (fun cl => check_clause C cl t2s) hs
          then type_update ts (to_ct_list (t1s ++ [:: T_ref (T_contref (Tf t1s t2s))])) (CT_type t2s)
          else CT_bot
      | _ => CT_bot
      end

        
  | BI_ref_null t => type_update ts [::] (CT_type [:: T_ref t])
  | BI_ref_is_null => type_update ts [:: CTA_any_reference ] (CT_type [::T_num T_i32])
  | BI_ref_func f =>
      match List.nth_error (tc_func_t C) f with
      | None => CT_bot (* Isa mismatch *)
      | Some t =>
        type_update ts [::] (CT_type [:: T_ref (T_funcref t)])
      end
  | BI_call_reference i =>
      match get_type C i with
      | None => CT_bot (* Isa mismatch *)
      | Some (Tf tn tm) =>
        type_update ts (to_ct_list (tn ++ [::T_ref (T_funcref (Tf tn tm))])) (CT_type tm)
      end
  | BI_throw i =>
      match List.nth_error (tc_tags_t C) i with
      | Some (Tf ts' [::]) => type_update ts (to_ct_list ts') (CT_top_type [::])
      | _ => CT_bot (* Isa mismatch *)
      end
  | BI_throw_ref =>
      type_update ts (to_ct_list [:: T_ref T_exnref]) (CT_top_type [::])
  | BI_unop t op =>
    match op with
    | Unop_i _ => if is_int t
                  then type_update ts [::CTA_some (T_num t)] (CT_type [::T_num t])
                  else CT_bot
    | Unop_f _ => if is_float t
                  then type_update ts [::CTA_some (T_num t)] (CT_type [::T_num t])
                  else CT_bot
    end
  | BI_binop t op =>
    match op with
    | Binop_i _ => if is_int t
                  then type_update ts [::CTA_some (T_num t); CTA_some (T_num t)] (CT_type [::T_num t])
                  else CT_bot
    | Binop_f _ => if is_float t
                  then type_update ts [::CTA_some (T_num t); CTA_some (T_num t)] (CT_type [::T_num t])
                  else CT_bot
    end
  | BI_testop t _ =>
    if is_int_t t
    then type_update ts [::CTA_some (T_num t)] (CT_type [::T_num T_i32])
    else CT_bot
  | BI_relop t op =>
    match op with
    | Relop_i _ => if is_int t
                  then type_update ts [::CTA_some (T_num t); CTA_some (T_num t)] (CT_type [::T_num T_i32])
                  else CT_bot
    | Relop_f _ => if is_float t
                  then type_update ts [::CTA_some (T_num t); CTA_some (T_num t)] (CT_type [::T_num T_i32])
                  else CT_bot
    end
  | BI_cvtop t1 CVO_convert t2 sx =>
    if typing.convert_cond t1 t2 sx
    then type_update ts [::CTA_some (T_num t2)] (CT_type [::T_num t1])
    else CT_bot
  | BI_cvtop t1 CVO_reinterpret t2 sxo =>
    if (t1 != t2) && (length_tnum t1 == length_tnum t2) && (sxo == None)
    then type_update ts [::CTA_some (T_num t2)] (CT_type [::T_num t1])
    else CT_bot
  | BI_unreachable => type_update ts [::] (CT_top_type [::])
  | BI_nop => ts
  | BI_drop => type_update ts [::CTA_any] (CT_type [::])
  | BI_select => type_update_select ts
  | BI_block (Tf tn tm) es =>
    if b_e_type_checker (upd_label C ([::tm] ++ tc_label C)) es (Tf tn tm)
    then type_update ts (to_ct_list tn) (CT_type tm)
    else CT_bot
  | BI_loop (Tf tn tm) es =>
    if b_e_type_checker (upd_label C ([::tn] ++ tc_label C)) es (Tf tn tm)
    then type_update ts (to_ct_list tn) (CT_type tm)
    else CT_bot
  | BI_if (Tf tn tm) es1 es2 =>
    if b_e_type_checker (upd_label C ([::tm] ++ tc_label C)) es1 (Tf tn tm)
                        && b_e_type_checker (upd_label C ([::tm] ++ tc_label C)) es2 (Tf tn tm)
    then type_update ts (to_ct_list (tn ++ [::T_num T_i32])) (CT_type tm)
    else CT_bot
  | BI_br i =>
    if i < length (tc_label C)
    then
      match List.nth_error (tc_label C) i with
      | Some xx => type_update ts (to_ct_list xx) (CT_top_type [::])
      | None => CT_bot (* Isa mismatch *)
                  (* There are many cases of this 'Isa mismatch'. What does it 
                       mean exactly? I checked and in each of this cases there's a 
                       length comparison immediately before and a call to
                       List.nth_error, which would never give None since we've already
                       checked the length. Maybe this is the reason for the comment? *)
      end
    else CT_bot
  | BI_br_if i =>
    if i < length (tc_label C)
    then
      match List.nth_error (tc_label C) i with
      | Some xx => type_update ts (to_ct_list (xx ++ [::T_num T_i32])) (CT_type xx)
      | None => CT_bot (* Isa mismatch *)
      end
    else CT_bot
  | BI_br_table iss i =>
    match same_lab (iss ++ [::i]) (tc_label C) with
    | None => CT_bot
    | Some tls => type_update ts (to_ct_list (tls ++ [::T_num T_i32])) (CT_top_type [::])
    end
  | BI_return =>
    match tc_return C with
    | None => CT_bot
    | Some tls => type_update ts (to_ct_list tls) (CT_top_type [::])
    end
  | BI_call i =>
    if i < length (tc_func_t C)
    then
      match List.nth_error (tc_func_t C) i with
      | None => CT_bot (* Isa mismatch *)
      | Some (Tf tn tm) =>
        type_update ts (to_ct_list tn) (CT_type tm)
      end
    else CT_bot
  | BI_call_indirect i =>
    if (1 <= length C.(tc_table)) 
    then
      match get_type C i with
      | None => CT_bot (* Isa mismatch *)
      | Some (Tf tn tm) =>
        type_update ts (to_ct_list (tn ++ [::T_num T_i32])) (CT_type tm)
      end
    else CT_bot
  | BI_get_local i =>
    if i < length (tc_local C)
    then
      match List.nth_error (tc_local C) i with
      | None => CT_bot (* Isa mismatch *)
      | Some xx => type_update ts [::] (CT_type [::xx])
      end
    else CT_bot
  | BI_set_local i =>
    if i < length (tc_local C)
    then
      match List.nth_error (tc_local C) i with
      | None => CT_bot (* Isa mismatch *)
      | Some xx => type_update ts [::CTA_some xx] (CT_type [::])
      end
    else CT_bot
  | BI_tee_local i =>
    if i < length (tc_local C)
    then
      match List.nth_error (tc_local C) i with
      | None => CT_bot (* Isa mismatch *)
      | Some xx => type_update ts [::CTA_some xx] (CT_type [::xx])
      end
    else CT_bot
  | BI_get_global i =>
    if i < length (tc_global C)
    then
      match List.nth_error (tc_global C) i with
      | None => CT_bot (* Isa mismatch *)
      | Some xx => type_update ts [::] (CT_type [::T_num (tg_t xx)])
      end
    else CT_bot
  | BI_set_global i =>
    if i < length (tc_global C)
    then
      match List.nth_error (tc_global C) i with
      | None => CT_bot (* Isa mismatch *)
      | Some xx =>
        if is_mut xx
        then type_update ts [::CTA_some (T_num (tg_t xx))] (CT_type [::])
        else CT_bot
      end
    else CT_bot
  | BI_load t tp_sx a off =>
    if (C.(tc_memory) != nil) && load_store_t_bounds a (option_projl tp_sx) t
    then type_update ts [::CTA_some (T_num T_i32)] (CT_type [::T_num t])
    else CT_bot
  | BI_store t tp a off =>
    if (C.(tc_memory) != nil) && load_store_t_bounds a tp t
    then type_update ts [::CTA_some (T_num T_i32); CTA_some (T_num t)] (CT_type [::])
    else CT_bot
  | BI_current_memory =>
    if C.(tc_memory) != nil
    then type_update ts [::] (CT_type [::T_num T_i32])
    else CT_bot
  | BI_grow_memory =>
    if C.(tc_memory) != nil
    then type_update ts [::CTA_some (T_num T_i32)] (CT_type [::T_num T_i32])
    else CT_bot
  | BI_try_table i cs es =>
      match get_type C i with
      | None => CT_bot
      | Some (Tf t1s t2s) =>
          if List.forallb (check_exception_clause C) cs
          then
            if b_e_type_checker (upd_label C ([::t2s] ++ tc_label C)) es (Tf t1s t2s)
            then type_update ts (to_ct_list t1s) (CT_type t2s)
            else CT_bot
          else CT_bot
      end 
  end.

Fixpoint collect_at_inds A (l : seq A) (ns : seq nat) : seq A :=
  match ns with
  | n :: ns' =>
    match (List.nth_error l n) with
    | Some x => x :: collect_at_inds l ns'
    | None => collect_at_inds l ns'
    end
  | [::] => [::]
  end.

Definition check (C : t_context) (es : list basic_instruction) (ts : checker_type): checker_type :=
  List.fold_left (check_single C) es ts.

Definition b_e_type_checker (C : t_context) (es : list basic_instruction) (tf : function_type) : bool :=
  match tf with
  | Tf tn tm => 
      c_types_agree (List.fold_left (check_single C) es (CT_type tn)) tm
  end.

(* TODO: This definition is kind of a duplication of inst_typing, to avoid more dependent definitions becoming Prop downstream *)

(* UPD: This in fact makes the soundness proof extremely tedious and dependent on the type_checker reflecting typing.
  I have edited the later functions to avoid using these. *)
(*
Definition inst_type_check (s : store_record) (i : instance) : t_context := {|
  (* TODO: ported this from option to list, but not too sure it's right *)
  tc_types_t := i_types i;
  tc_func_t := collect_at_inds (map cl_type (s_funcs s)) (i_funcs i);
  tc_global :=
    collect_at_inds
      (map (fun glob => {| tg_mut := glob.(g_mut); tg_t := typeof glob.(g_val) |}) s.(s_globals))
      i.(i_globs);
  tc_table :=
    collect_at_inds
      (map
        (fun t =>
          (* TODO: this is probably wrong? *)
          {| tt_limits := {| lim_min := 0; lim_max := Some (List.length t.(table_data)) |}; tt_elem_type := ELT_funcref |})
          s.(s_tables))
      i.(i_tab);
  tc_memory :=
    collect_at_inds
      (map
        (fun m =>
          (* TODO: this is probably wrong? *)
          {| lim_min := 0; lim_max := Some (List.length m.(mem_data)) |})
        s.(s_mems))
      i.(i_memory);
  tc_local := nil;
  tc_label := nil;
  tc_return := None;
|}.

Definition cl_type_check (s : store_record) (cl : function_closure) : bool :=
  match cl with
  | Func_native i tf ts es =>
    let '(Tf t1s t2s) := tf in
    let C := inst_type_check s i in
    let C' := upd_local_label_return C (app (tc_local C) (app t1s ts)) (app [::t2s] (tc_label  C)) (Some t2s) in
    b_e_type_checker C' es (Tf [::] t2s)
  | Func_host tf h => true
  end.
*)


