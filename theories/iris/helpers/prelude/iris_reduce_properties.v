From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm.iris.language.iris Require Export iris.
From Wasm Require Export stdpp_aux.
Require Export iris_wasm_lang_properties iris_lfilled_properties.

Open Scope list_scope.
Set Bullet Behavior "Strict Subproofs".

Section reduce_properties.
  

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.

  (* wasm opsem related *)

  Lemma values_no_reduce s f vs s' f' es' :
    reduce s f vs s' f' es' -> const_list vs -> False.
  Proof.
    intros H Hvs.
    induction H ; try by inversion Hvs ; unfold const_list in Hvs ;
                    rewrite forallb_app in Hvs ; move/andP in Hvs ;
      destruct Hvs as [_ Hvs] ; inversion Hvs.
    all: try by simpl in Hvs; remove_bools_options.
    { destruct H; try by inversion Hvs ;
        unfold const_list in Hvs ; rewrite forallb_app in Hvs;
        move/andP in Hvs ; destruct Hvs as [_ Hvs] ; 
        inversion Hvs.
      all: try by simpl in Hvs; remove_bools_options.
      apply lfilled_const in H0 as [??] => //.
    }
    apply IHreduce. eapply lfilled_const; eauto.
  Qed.

End reduce_properties.

(* Applies values_no_reduce and attempts to prove that the given arguments were indeed
   values *)
Ltac values_no_reduce :=
  eapply values_no_reduce => //=.
  
(*
(* From hyopthesis "Heqes : [ some explicit list of instructions ] = es" and 
   "Hred : es reduces to es'", attempts to prove False. 
   Defined recursively. Examples below show how compilation time gets noticeably
   longer when there are more instructions.
   To prove lemmas reduce_ves, only length 3 is needed, which is compiled in a few
   seconds *)
Ltac no_reduce Heqes Hred :=
  let a := fresh "a" in
  let aft := fresh "aft" in
  let bef := fresh "bef" in
  let e := fresh "e" in
  let e' := fresh "e" in
  let es := fresh "es" in
  let es' := fresh "es" in
  let es0 := fresh "es" in
  let f := fresh "f" in
  let f' := fresh "f" in
  let g := fresh "g" in
  let k := fresh "k" in
  let l := fresh "l" in
  let l' := fresh "l" in
  let les := fresh "les" in
  let les' := fresh "les'" in
  let lh := fresh "lh" in
  let m := fresh "m" in
  let n := fresh "n" in
  let n' := fresh "n" in
  let s := fresh "s" in
  let s' := fresh "s" in
  let t1s' := fresh "t1s" in
  let t2s := fresh "t2s" in
  let vs := fresh "vs" in
  let H := fresh "H" in
  let H0 := fresh "H" in
  let H1 := fresh "H" in
  let Hconst := fresh "Hconst" in
  let Heqes0 := fresh "Heqes" in
  let Heqg := fresh "Heqg" in
  let Hes := fresh "Hes" in
  let Hles' := fresh "Hles" in
  let Ht1s := fresh "Ht1s" in
  let Ht2s := fresh "Ht2s" in
  let Htrap' := fresh "Htrap" in
  let Hvs := fresh "Hvs" in
  let Hxl1 := fresh "Hxl1" in
  let IHreduce := fresh "IHreduce" in
  (* clear all unimportant hypothesis, in order to make induction hypothesis 
     created at next step as simple as possible *)
  clear - (*host_function host function_closure store_record
                      host_instance*)
                      Hred Heqes ;
  induction Hred as [e e' s f H | | | | | a | a | a | | | | | | | | | | | | | | |
                      s f es les s' f' es' les' k lh  Hred IHreduce H0 _ |
    ]; (try by inversion Heqes) ; (try by found_intruse (AI_invoke a) Heqes Hxl1) ;
  [ destruct H as [ | | | | | | | | | | | | | | 
                    vs es n' m t1s' t2s Hconst Hvs Ht1s Ht2s |
                    vs es n' m t1s' t2s Hconst Hvs Ht1s Ht2s |
                  | | | | | | | | | | | | | | | | | | | | | | | | | | 
                    es' lh Htrap' H0 ]; (try by inversion Heqes) ;
    first found_intruse (AI_basic (BI_block (Tf t1s' t2s) es)) Heqes Hxl1 ;
    first found_intruse (AI_basic (BI_loop (Tf t1s' t2s) es)) Heqes Hxl1 ;
    try rewrite <- Heqes in H0 (* ; filled_trap H0 Hxl1 *)
  | rewrite <- Heqes in H0 ;
    (* The tactic simple_filled will destruct hypothesis "H0 : lfilled es les".
       In this case, it will completely solve the case k > 0, and for the case
       k = 0, it will transform hypothesis H0 into "H0 : objs = bef ++ es ++ aft"
       where objs is the explicit sequence from Heqes *)
    simple_filled H0 k lh bef aft n l l' ;
    apply Logic.eq_sym in H0 ;
    remember ([] : seq.seq administrative_instruction) as g eqn:Heqg in f;
    let rec auxb H0 :=
      ( (* We maintain as an invariant that when auxb H0 is called,
           H0 is the hypothesis "H0 : bef ++ es ++ aft = [some explicit sequence ]" *)
        let b0 := fresh "b" in
        let Hb0 := fresh "Hb0" in
        let H1 := fresh "H" in
        destruct bef as [| b0 bef] ;
        [ (* case bef = [] : our invariant tells us that 
             "H0 : es ++ aft = [some explicit sequence"
             recall g was defined to be [] with "Heqg : g = []" *)
          let rec auxe H0 g Heqg :=
             (* We maintain as an invariant that when auxe H0 g Heqg is called,
                 H0 is the hypothesis "H0 : es ++ aft = [some explicit sequence]"
                 Hred is the hypothesis "Hred : (g ++ es) -> es'"
                 and Heqg is "Heqg : g = [some (other) explicit sequence]" *)
            (  let e0 := fresh "e" in
              let g' := fresh "g" in
              let He0 := fresh "He" in
              let Heqg' := fresh "Heqg" in
              let H1 := fresh "H" in
              destruct es as [| e0 es ] ;
              [ (* case es = [] ; our invariant tells us that
                   "Hred : g -> es'". We can solve this case either … *)
                rewrite <- Heqg in Hred ;
                remember g as es0 eqn:Heqes0 in Hred ;
                apply Logic.eq_sym in Heqes0 ;
                rewrite Heqg in Heqes0 ;
                (* … by induction hypothesis (case where bef = aft = []), or … *)
                ((by subst ; apply IHreduce) +
                   (* … by calling recursively no_reduce (case where bef or aft is
                      nonempty, thus our recursive call is on a shorter list *)
                   no_reduce Heqes0 Hred)
              | (* case es = e0 :: es. Our invariant gives us
                   "H0 : e0 :: es ++ aft = [some explicit sequence]", so we can 
                   try to conclude by inverting H0 in case the explicit sequence is
                   empty *)
                (by inversion H0) +
                  (* else, the explicit sequence is nonempty, so by inverting H0,
                     we get "H1 : es ++ aft = [some shorter explicit sequence]".
                     Our invariant also tells us "Hred : (g ++ e0 :: es) -> es'",
                     so to maintain this invariant, we define g' to be g ++ [e0].
                     We then make sure to have a hypothesis Heqg' which gives an
                     explicit description of g' *)
                  ( inversion H0 as [[ He0 H1 ]] ;
                    rewrite He0 in Hred ;
                    remember (g ++ [e0]) as g' eqn:Heqg' ;
                    rewrite Heqg in Heqg' ;
                    rewrite He0 in Heqg' ;
                    simpl in Heqg' ;
                    (* now we can make a recursive call to auxe. The invariant 
                       is maintained, and the explicit sequence in H1 has diminished
                       in length *)
                    auxe H1 g' Heqg'
                  )
              ]
            ) in auxe H0 g Heqg
        | (* case bef = b0 :: bef. Our invariant gives us
             "H0 : b0 :: bef ++ es ++ aft = [some explicit sequence]", so we can 
             try to conclude by inverting H0 in case that explicit sequence is empty *)
          (by inversion H0) +
            (* else the explicit sequence is nonempty, so by inverting H0, we get 
               "H1 : es ++ aft = [some shorter explicit sequence]" *)
            ( inversion H0 as [[ Hb0 H1 ]] ;
              auxb H1 )
        ]
      ) in auxb H0
  ].  *)

Section reduce_properties_lemmas.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.

  (* examples of usage of no_reduce. This first example is reused in other lemmas,
   the following ones may be removed if wanted *)
  Lemma empty_no_reduce s f s' f' es' :
    reduce s f [] s' f' es' -> False.
  Proof.
    intro Hred.
    remember [] as es in Hred.
    induction Hred => //.
    inversion H => //.
    all: try subst e => //.
    all: try by destruct vs.
    move/lfilledP in H1; inversion H1;
      try by destruct vs + destruct bef.
    all: try by destruct ves.
    apply IHHred.
    move/lfilledP in H; inversion H; subst;
      try by destruct vs + destruct bef.
    destruct vs, es => //.
  Qed.

  Ltac empty_list_no_reduce :=
    exfalso ; eapply empty_no_reduce => //=.

(*  Lemma test_no_reduce1 s f v s' f' es' :
    reduce s f [AI_basic (BI_const v)] s' f' es' -> False.
  Proof.
    intro Hred.
    remember [AI_basic (BI_const v)] as es in Hred.
    apply Logic.eq_sym in Heqes.
    no_reduce Heqes Hred.
  Qed.

  Lemma test_no_reduce_trap s f s' f' es' :
    reduce s f [AI_trap] s' f' es' -> False.
  Proof.
    intro Hred.
    remember [AI_trap] as es.
    apply Logic.eq_sym in Heqes.
    no_reduce Heqes Hred; subst => //.
  Qed.

  Lemma test_no_reduce2 s f v1 v2 s' f' es' :
    reduce s f [AI_basic (BI_const v1) ; AI_basic (BI_const v2)] s' f' es' -> False.
  Proof.
    intro Hred.
    remember [AI_basic (BI_const v1) ; AI_basic (BI_const v2)] as es in Hred.
    apply Logic.eq_sym in Heqes.
    no_reduce Heqes Hred.
  Qed.

  Lemma test_no_reduce3 s f v1 v2 v3 s' f' es' :
    reduce s f [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ; AI_basic (BI_const v3)]
           s' f' es' -> False.
  Proof.
    intro Hred.
    remember [AI_basic (BI_const v1) ; AI_basic (BI_const v2) ; AI_basic (BI_const v3)]
      as es in Hred.
    apply Logic.eq_sym in Heqes.
    no_reduce Heqes Hred.
  Qed.
 *)

  (* Are these still useful? *)
  (*
  
  Lemma reduce_load_false s0 f s' f' es es' x0 x1 x2 x3 :
    es = [AI_basic (BI_load x0 x1 x2 x3)] ->
    reduce s0 f es s' f' es' -> False.
  Proof.
    intros Heq Hred.
    apply Logic.eq_sym in Heq.
    no_reduce Heq Hred.
  Qed.
  
  Lemma reduce_store_false s0 f s' f' es es' x0 x1 x2 x3 :
    es = [AI_basic (BI_store x0 x1 x2 x3)] ->
    reduce s0 f es s' f' es' -> False.
  Proof.
    intros Heq Hred.
    apply Logic.eq_sym in Heq.
    no_reduce Heq Hred.
  Qed.
  
  Lemma reduce_store_false_2 s0 f s' f' es es' x0 x1 x2 x3 v :
    es = [AI_basic (BI_const v); AI_basic (BI_store x0 x1 x2 x3)] ->
    reduce s0 f es s' f' es' -> False.
  Proof.
    intros Heq Hred.
    apply Logic.eq_sym in Heq.
    no_reduce Heq Hred.
  Qed. *)

  Lemma reduce_val_false s0 f s' f' es es' :
    is_Some (iris.to_val es) ->
    reduce s0 f es s' f' es' -> False.
  Proof.
    intros Hsome Hred.
    apply val_head_stuck_reduce in Hred.
    rewrite Hred in Hsome. inversion Hsome.
    done.
  Qed.

  Lemma reduce_br_false s f vs0 j es es0 s' f' es' :
    const_list vs0 ->
    es = vs0 ++ [AI_basic (BI_br j)] ++ es0 ->
    reduce s f es s' f' es' -> False.
  Proof.
    intros Heqes Hred.
    eapply reduce_val_false;eauto.
    subst.
    apply const_es_exists in Heqes as [vs ->].
    rewrite to_val_br_eq. auto.
  Qed.

  Lemma reduce_ret_false s f vs0 es es0 s' f' es' :
    const_list vs0 ->
    es = vs0 ++ [AI_basic BI_return] ++ es0 ->
    reduce s f es s' f' es' -> False.
  Proof.
    intros Heqes Hred.
    eapply reduce_val_false;eauto.
    subst.
    apply const_es_exists in Heqes as [vs ->].
    rewrite to_val_ret_eq. auto.
  Qed.
  
End reduce_properties_lemmas.


Ltac empty_list_no_reduce :=
  exfalso ; eapply empty_no_reduce => //=.

(* Knowing hypothesis "Hin : In obj vs" and "Hvs : const_list vs", tries to prove False *)
Ltac intruse_among_values vs Hin Hvs :=
  try unfold const_list in Hvs ;
  let x := fresh "Hf" in
  destruct (forallb_forall is_const vs) as [x _] ;
  apply (x Hvs) in Hin ; inversion Hin.

(*

(* attempts to prove that vs ++ [obj] entails false when list vs is shorter 
   than list t1s. Some subgoals may be left for user to prove *)
Ltac not_enough_arguments s f vs obj t1s s' f' es' := 
  let Hxl1 := fresh "Hxl1" in
  let n := fresh "n" in
  let H := fresh "H" in
  let Hvs := fresh "Hvs" in
  let es := fresh "es" in
  let Heqes := fresh "Heqes" in
  let e := fresh "e" in
  let e' := fresh "e" in
  let les := fresh "les" in
  let les' := fresh "les" in
  let k := fresh "k" in
  let lh := fresh "lh" in
  let Hred := fresh "Hred" in
  let IHreduce := fresh "IHreduce" in
  let H0 := fresh "H" in
  let Habs := fresh "Habs" in
  let vs' := fresh "vs" in
  let n' := fresh "n" in
  let m := fresh "m" in
  let t1s' := fresh "t1s" in
  let t2s' := fresh "t2s" in
  let Hconst' := fresh "Hconst'" in
  let Hvs' := fresh "Hvs" in
  let Ht1s := fresh "Ht1s" in
  let Ht2s := fresh "Ht2s" in
  let Ht1s' := fresh "Ht1s" in
  let Ht2s' := fresh "Ht2s" in
  let i := fresh "i" in
  let v := fresh "v" in
  let Htrap' := fresh "Htrap" in
  let Hvs0 := fresh "Hvs" in
  let Hbl := fresh "Hbl" in
  let Hes := fresh "Hes" in
  let Hgoal := fresh "Hgoal" in
  let Hxl2 := fresh "Hxl1" in
  let Heq := fresh "Heq" in
  let l := fresh "l" in
  let l0 := fresh "l" in
  let a := fresh "a" in
  let l' := fresh "l" in
  let b := fresh "b" in
  let Htail := fresh "Htail" in
  let IHn := fresh "IHn" in
  let n0 := fresh "n" in
  let l1 := fresh "l" in
  let l3 := fresh "l" in
  cut (forall n, length vs < n ->
            reduce s f (vs ++ [obj]) s' f' es'
            ->  const_list vs -> length vs < length t1s
            ->  False) ;
  [ intro H ; apply (H (S (length vs))) ; apply Nat.lt_succ_diag_r |] ;
  intro n ;
  generalize dependent vs;
  generalize dependent es' ;
  induction n as [| n IHn] ; [ intros es' vs Habs ; inversion Habs |] ;
  intros es' vs Hvs H Hconst Hlen ;
  remember (cat vs [obj]) as es eqn:Heqes ;
  induction H as [e e' s f H | | | | | | | | | | | | | | | | | | | | | | 
                      s f es les s' f' es' les' k lh Hred IHreduce H0 _ |
    ]; (try by found_intruse obj Heqes Hxl1);
  ( try by apply app_inj_tail in Heqes ; destruct Heqes as [ _ Habs ] ;
    inversion Habs ) ;
  (try 
     (destruct H as [ | | | | | | | | | | | | | | 
                      vs' es n' m t1s' t2s' Hconst' Hvs' Ht1s' Ht2s' |
                      vs' es n' m t1s' t2s' Hconst' Hvs' Ht1s' Ht2s' |
                    | | | | | | | | | | | | i v | 
                      es' lh Htrap' H0 ]; try by found_intruse obj Heqes Hxl1 ;
      try by apply app_inj_tail in Heqes ; destruct Heqes as [ _ Habs ] ; inversion Habs ;
      try by apply app_inj_tail in Heqes ; destruct Heqes as [ Hvs0 Hbl ] ;
      inversion Hbl as [[ Ht1s Ht2s Hes ]] ; rewrite Ht1s in Ht1s' ;
      rewrite Ht1s' in Hlen ; rewrite Hvs0 in Hvs' ;
      rewrite Hvs' in Hlen ; apply Nat.lt_neq in Hlen ;
      apply Hlen ; trivial ;
      try by cut ([ v ; AI_basic (BI_tee_local i)] = [v] ++ [AI_basic (BI_tee_local i)]) ;
      [| simpl ; trivial ] ; intro Heq ; rewrite Heq in Heqes ;
      apply app_inj_tail in Heqes ; destruct Heqes as [ _ Habs ] ; inversion Habs ;
      try by rewrite Heqes in H0 ; filled_trap H0 Hxl1 ; apply in_app_or in Hxl1 ;
      destruct Hxl1 as [Hxl1 | Hxl1] ; [ intruse_among_values vs Hxl1 Hconst |] ;
      destruct Hxl1 as [Hxl1 | Hxl1] ; [inversion Hxl1 | exact Hxl1 ] 
  )) ;
  (try (rewrite Heqes in H0 ;
        simple_filled H0 k lh l0 l n0 l1 l3 ;
        [ apply Logic.eq_sym in H0 ;
          destruct l ;
          [ rewrite app_nil_r in H0 ;
            destruct es as [| a es] ;
            [ empty_list_no_reduce |] ;
            get_tail a es l' b Htail ;
            rewrite Htail in H0 ;
            rewrite app_assoc in H0 ;
            apply app_inj_tail in H0 ; destruct H0 as [Hll Hb] ;
            destruct l0 ;
            [ simpl in Hll ; rewrite Htail in IHreduce ;
              rewrite Hll in IHreduce ; rewrite Hb in IHreduce ;
              apply IHreduce; [assumption | trivial]  |] ;
            apply (IHn es' l') ;
            [ rewrite <- Hll in Hvs ;
              rewrite length_app in Hvs ; simpl in Hvs ;
              apply Nat.succ_lt_mono in Hvs ; lia 
            | rewrite Htail in Hred ; rewrite Hb in Hred ;
              exact Hred 
            | rewrite <- Hll in Hconst ; unfold const_list in Hconst ;
              rewrite forallb_app in Hconst ;
              apply andb_true_iff in Hconst ;
              destruct Hconst as [_ Hgoal] ; exact Hgoal 
            | rewrite <- Hll in Hlen ;
              rewrite length_app in Hlen ; lia
            ]
          | get_tail a l l' b Htail;
            rewrite Htail in H0 ;
            rewrite app_assoc in H0 ; rewrite app_assoc in H0 ;
            apply app_inj_tail in H0 ; destruct H0 as [ Hes _ ] ;
            values_no_reduce ;
(*            apply (values_no_reduce _ _ _ _ _ _ _ _ Hred) ; *)
            rewrite <- Hes in Hconst ; unfold const_list in Hconst ;
            rewrite forallb_app in Hconst ;
            apply andb_true_iff in Hconst ;
            destruct Hconst as [Hconst _ ] ;
            rewrite forallb_app in Hconst ;
            apply andb_true_iff in Hconst ;
            destruct Hconst as [ _ Hconst ] ;
            exact Hconst
          ]
        | found_intruse (AI_label n0 l1 l3) H0 Hxl2 ;
          apply in_app_or in Hxl2 ; destruct Hxl2 as [Hxl2 | Hxl2] ;
          [ intruse_among_values vs Hxl2 Hconst 
          | destruct Hxl2 as [Hxl2 | Hxl2] ; [inversion Hxl2 | assumption]
          ]
        ]
  )).
*)
Section reduce_properties_lemmas.
   Let reducible := @iris.program_logic.language.reducible wasm_lang.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.

  Lemma block_not_enough_arguments_no_reduce s f (vs : seq.seq administrative_instruction)
    t1s t2s esb s' f' es'  :
    reduce s f (vs ++ [AI_basic (BI_block (Tf t1s t2s) esb)]) s' f' es' ->
    const_list vs ->
    length vs < length t1s ->
    False.
  Proof.
    intros Hred Hvs Hlen.
    remember (cat vs [AI_basic (BI_block (Tf t1s t2s) esb)]) as es.
    generalize dependent vs.
    induction Hred.
    all: intros vs' Heqes Hvs Hlen.
    inversion H.
    all: remember Heqes as H00; clear HeqH00 Heqes.
    all: subst.
    all: try by rewrite separate1 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate1 in H00;
      rewrite -cat_app catA in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate2 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate3 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by destruct vs' => //; destruct vs'.
    - apply concat_cancel_last in H00 as [??].
      inversion H3; subst. lia.
    - move/lfilledP in H1; inversion H1.
      all: rewrite - (app_nil_r [_]) in H2.
      all: apply first_values in H2 as (? & ? & ?) => //.
    - move/lfilledP in H; inversion H; subst.
      2-4: rewrite - (app_nil_r [_]) in H1.
      2-4: apply first_values in H1 as (? & ? & ?) => //.
      separate_last es'0.
      + rewrite -cat_app in H1.
        repeat rewrite catA in H1.
        apply concat_cancel_last in H1 as [??].
        eapply values_no_reduce.
        exact Hred.
        subst vs'. apply const_list_split in Hvs as [? _].
        apply const_list_split in H1 as [_ ?] => //.
      + separate_last es.
        * rewrite cats0 in H1. rewrite -cat_app catA in H1.
          apply concat_cancel_last in H1 as [<- ->].
          eapply IHHred. done. apply const_list_split in Hvs as [??] => //.
          rewrite length_app in Hlen. lia.
        * empty_list_no_reduce.
  Qed. 

  
  Lemma loop_not_enough_arguments_no_reduce s f (vs : seq.seq administrative_instruction)
        t1s t2s esb s' f' es'  :
    reduce s f (vs ++ [AI_basic (BI_loop (Tf t1s t2s) esb)]) s' f' es' ->
    const_list vs ->
    length vs < length t1s ->
    False.
  Proof.
    intros Hred Hvs Hlen.
    remember (cat vs [AI_basic (BI_loop (Tf t1s t2s) esb)]) as es.
    generalize dependent vs.
    induction Hred.
    all: intros vs' Heqes Hvs Hlen.
    inversion H.
    all: remember Heqes as H00; clear HeqH00 Heqes.
    all: subst.
    all: try by rewrite separate1 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate1 in H00;
      rewrite -cat_app catA in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate2 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate3 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by destruct vs' => //; destruct vs'.
    - apply concat_cancel_last in H00 as [??].
      inversion H3; subst. lia.
    - move/lfilledP in H1; inversion H1.
      all: rewrite - (app_nil_r [_]) in H2.
      all: apply first_values in H2 as (? & ? & ?) => //.
    - move/lfilledP in H; inversion H; subst.
      2-4: rewrite - (app_nil_r [_]) in H1.
      2-4: apply first_values in H1 as (? & ? & ?) => //.
      separate_last es'0.
      + rewrite -cat_app in H1.
        repeat rewrite catA in H1.
        apply concat_cancel_last in H1 as [??].
        eapply values_no_reduce.
        exact Hred.
        subst vs'. apply const_list_split in Hvs as [? _].
        apply const_list_split in H1 as [_ ?] => //. 
      + separate_last es.
        * rewrite cats0 in H1. rewrite -cat_app catA in H1.
          apply concat_cancel_last in H1 as [<- ->].
          eapply IHHred. done. apply const_list_split in Hvs as [??] => //.
          rewrite length_app in Hlen. lia.
        * empty_list_no_reduce.
  Qed.



    Lemma resume_throw_not_enough_arguments_no_reduce s f (vs : seq.seq administrative_instruction)
      x a ts k hs tf hh i s' f' es'  :
      nth_error (inst_tags (f_inst f)) x = Some a ->
      nth_error (datatypes.s_tags s) a = Some (Tf ts []) ->
      nth_error (s_conts s) k = Some (Cont_hh tf hh) ->
    reduce s f (vs ++ [AI_ref_cont k; AI_basic (BI_resume_throw i x hs)]) s' f' es' ->
    const_list vs ->
    length vs < length ts ->
    False.
  Proof.
    intros Hx Ha Hcont Hred Hvs Hlen.
    lazymatch goal with _ : reduce _ _ ?es0 _ _ _ |- _ => remember es0 as es end.
    generalize dependent vs.
    induction Hred.
    all: intros vs' Heqes Hvs Hlen.
    inversion H.
    all: remember Heqes as H00; clear HeqH00 Heqes.
    all: subst.
    all: try (symmetry in H00; rewrite cat_app separate1 app_assoc in H00; symmetry in H00).
    all: try by rewrite separate1 in H00;
      apply concat_cancel_last in H00 as [??]; try apply const_list_concat.
    all: try by rewrite separate1 in H00;
      rewrite -cat_app catA in H00;
      apply concat_cancel_last in H00 as [??]; try apply const_list_concat.
    all: try by rewrite separate2 in H00;
      apply concat_cancel_last in H00 as [??]; try apply const_list_concat.
    all: try by rewrite separate3 in H00;
      apply concat_cancel_last in H00 as [??]; try apply const_list_concat.
    all: try by do 3 destruct vs' => //. 
    - move/lfilledP in H1; inversion H1.
      all: try (symmetry in H2; rewrite cat_app separate1 app_assoc in H2; symmetry in H2).
      all: apply first_values in H2 as (? & ? & ?) => //.
      all: apply const_list_concat => //.
    - rewrite cat_app separate1 app_assoc in H00.
      apply first_values in H00 as (? & ? & ?) => //=.
      inversion H3; subst.
      rewrite H in Hx. inversion Hx; subst a0.
      rewrite H0 in Ha. inversion Ha; subst ts0.
      apply concat_cancel_last in H1 as [<- Heq].
      lia. all: apply const_list_concat => //. apply v_to_e_is_const_list.
    - repeat (destruct vs' => //).
      inversion H00; subst. rewrite H in Hcont. done.
    - move/lfilledP in H; inversion H; subst.
      all: symmetry in H1; rewrite cat_app separate1 app_assoc in H1; symmetry in H1.
      2-4: apply first_values in H1 as (? & ? & ?) => //.
      2-4: apply const_list_concat => //.
      separate_last es'0.
      + rewrite -cat_app in H1.
        repeat rewrite catA in H1.
        apply concat_cancel_last in H1 as [??].
        eapply values_no_reduce.
        exact Hred.
        assert (const_list (app vs' [AI_ref_cont k])); first by apply const_list_concat.
        rewrite -H1 in H3.
        apply const_list_split in H3 as [? _].
        apply const_list_split in H3 as [_ ?] => //. 
      + separate_last es.
        * rewrite cats0 in H1. rewrite -cat_app catA in H1.
          apply concat_cancel_last in H1 as [Hvsl ->].
          separate_last l.
          -- rewrite cat_app app_assoc in Hvsl.
             apply concat_cancel_last in Hvsl as [<- ->].
             eapply IHHred. done. done. done.
             rewrite -app_assoc. done.
             apply const_list_split in Hvs as [??] => //.
             rewrite length_app in Hlen. lia.
          -- simpl in Hred. clear - Hred.
             remember [_] as es0.
             induction Hred.
             destruct H.
             all: try by inversion Heqes0.
             all: try by do 2 destruct vs => //.
             all: try by do 2 destruct ves => //. 
             ++ subst es. move/lfilledP in H0. inversion H0.
                do 2 destruct vs => //.
                all: do 2 destruct bef => //.
             ++ subst. move/lfilledP in H. inversion H; subst.
                all: try by do 2 destruct vs => //.
                all: try by do 2 destruct bef => //.
                destruct vs; last by inversion H1; subst.
                destruct es; first empty_list_no_reduce.
                inversion H1; subst.
                destruct es => //.
        * empty_list_no_reduce.
  Qed.
 
  Lemma contbind_not_enough_arguments_no_reduce s f (vs : seq.seq administrative_instruction)
    t1s t2s ts k tf hh i i' s' f' es'  :
    stypes (f_inst f) i = Some (Tf (ts ++ t1s) t2s) ->
    stypes (f_inst f) i' = Some (Tf t1s t2s) ->
    List.nth_error (s_conts s) k = Some (Cont_hh tf hh) -> 
    reduce s f (vs ++ [AI_ref_cont k; AI_basic (BI_contbind i i')]) s' f' es' ->
    const_list vs ->
    length vs < length ts ->
    False.
  Proof.
    intros Hi Hi' Hcont Hred Hvs Hlen.
    lazymatch goal with _ : reduce _ _ ?es0 _ _ _ |- _ => remember es0 as es end.
    generalize dependent vs.
    induction Hred.
    all: intros vs' Heqes Hvs Hlen.
    inversion H.
    all: remember Heqes as H00; clear HeqH00 Heqes.
    all: subst.
    all: try (symmetry in H00; rewrite cat_app separate1 app_assoc in H00; symmetry in H00).
    all: try by rewrite separate1 in H00;
      apply concat_cancel_last in H00 as [??]; try apply const_list_concat.
    all: try by rewrite separate1 in H00;
      rewrite -cat_app catA in H00;
      apply concat_cancel_last in H00 as [??]; try apply const_list_concat.
    all: try by rewrite separate2 in H00;
      apply concat_cancel_last in H00 as [??]; try apply const_list_concat.
    all: try by rewrite separate3 in H00;
      apply concat_cancel_last in H00 as [??]; try apply const_list_concat.
    all: try by do 3 destruct vs' => //. 
    - move/lfilledP in H1; inversion H1.
      all: try (symmetry in H2; rewrite cat_app separate1 app_assoc in H2; symmetry in H2).
      all: apply first_values in H2 as (? & ? & ?) => //.
      all: apply const_list_concat => //.
    - rewrite cat_app separate1 app_assoc in H00.
      apply first_values in H00 as (? & ? & ?) => //=.
      inversion H5; subst.
      rewrite H1 in Hi'. inversion Hi'; subst.
      rewrite H0 in Hi. inversion Hi; subst.
      apply concat_cancel_last_n in H8 => //.
      remove_bools_options; subst.
      apply concat_cancel_last in H4 as [-> _].
      lia. all: apply const_list_concat => //. 
    - repeat (destruct vs' => //).
      inversion H00; subst. rewrite H in Hcont. done.
    - move/lfilledP in H; inversion H; subst.
      all: symmetry in H1; rewrite cat_app separate1 app_assoc in H1; symmetry in H1.
      2-4: apply first_values in H1 as (? & ? & ?) => //.
      2-4: apply const_list_concat => //.
      separate_last es'0.
      + rewrite -cat_app in H1.
        repeat rewrite catA in H1.
        apply concat_cancel_last in H1 as [??].
        eapply values_no_reduce.
        exact Hred.
        assert (const_list (app vs' [AI_ref_cont k])); first by apply const_list_concat.
        rewrite -H1 in H3.
        apply const_list_split in H3 as [? _].
        apply const_list_split in H3 as [_ ?] => //. 
      + separate_last es.
        * rewrite cats0 in H1. rewrite -cat_app catA in H1.
          apply concat_cancel_last in H1 as [Hvsl ->].
          separate_last l.
          -- rewrite cat_app app_assoc in Hvsl.
             apply concat_cancel_last in Hvsl as [<- ->].
             eapply IHHred. done. done. done.
             rewrite -app_assoc. done.
             apply const_list_split in Hvs as [??] => //.
             rewrite length_app in Hlen. lia.
          -- simpl in Hred. clear - Hred.
             remember [_] as es0.
             induction Hred.
             destruct H.
             all: try by inversion Heqes0.
             all: try by do 2 destruct vs => //.
             all: try by do 2 destruct ves => //. 
             ++ subst es. move/lfilledP in H0. inversion H0.
                do 2 destruct vs => //.
                all: do 2 destruct bef => //.
             ++ subst. move/lfilledP in H. inversion H; subst.
                all: try by do 2 destruct vs => //.
                all: try by do 2 destruct bef => //.
                destruct vs; last by inversion H1; subst.
                destruct es; first empty_list_no_reduce.
                inversion H1; subst.
                destruct es => //.
        * empty_list_no_reduce.
  Qed.

  
 Lemma switch_not_enough_arguments_no_reduce s f (vs : seq.seq administrative_instruction)
   t1s t2s k cont i x s' f' es'  :
   nth_error (datatypes.s_conts s) k = Some cont ->
   typeof_cont cont = Tf t1s t2s ->
    reduce s f (vs ++ [AI_ref_cont k; AI_basic (BI_switch i (Mk_tagident x))]) s' f' es' ->
    const_list vs ->
    S (length vs) < length t1s ->
    False.
 Proof.
    intros Hcont Htcont Hred Hvs Hlen.
    lazymatch goal with _ : reduce _ _ ?es0 _ _ _ |- _ => remember es0 as es end.
    generalize dependent vs.
    induction Hred.
    all: intros vs' Heqes Hvs Hlen.
    inversion H.
    all: remember Heqes as H00; clear HeqH00 Heqes.
    all: subst.
    all: try (symmetry in H00; rewrite cat_app separate1 app_assoc in H00; symmetry in H00).
    all: try by rewrite separate1 in H00;
      apply concat_cancel_last in H00 as [??]; try apply const_list_concat.
    all: try by rewrite separate1 in H00;
      rewrite -cat_app catA in H00;
      apply concat_cancel_last in H00 as [??]; try apply const_list_concat.
    all: try by rewrite separate2 in H00;
      apply concat_cancel_last in H00 as [??]; try apply const_list_concat.
    all: try by rewrite separate3 in H00;
      apply concat_cancel_last in H00 as [??]; try apply const_list_concat.
    all: try by do 3 destruct vs' => //. 
    - move/lfilledP in H1; inversion H1.
      all: try (symmetry in H2; rewrite cat_app separate1 app_assoc in H2; symmetry in H2).
      all: apply first_values in H2 as (? & ? & ?) => //.
      all: apply const_list_concat => //.
    - rewrite cat_app separate1 app_assoc in H00.
      apply first_values in H00 as (? & ? & ?) => //=.
      inversion H6; subst.
      apply concat_cancel_last in H5 as [<- Hk].
      inversion Hk; subst k0.
      rewrite H2 in Hcont. inversion Hcont; subst cont0.
      rewrite H3 in Htcont. inversion Htcont; subst.
      rewrite length_map in Hlen.
      lia. all: apply const_list_concat => //.
      apply v_to_e_is_const_list.
    - move/lfilledP in H; inversion H; subst.
      all: symmetry in H1; rewrite cat_app separate1 app_assoc in H1; symmetry in H1.
      2-4: apply first_values in H1 as (? & ? & ?) => //.
      2-4: apply const_list_concat => //.
      separate_last es'0.
      + rewrite -cat_app in H1.
        repeat rewrite catA in H1.
        apply concat_cancel_last in H1 as [??].
        eapply values_no_reduce.
        exact Hred.
        assert (const_list (app vs' [AI_ref_cont k])); first by apply const_list_concat.
        rewrite -H1 in H3.
        apply const_list_split in H3 as [? _].
        apply const_list_split in H3 as [_ ?] => //. 
      + separate_last es.
        * rewrite cats0 in H1. rewrite -cat_app catA in H1.
          apply concat_cancel_last in H1 as [Hvsl ->].
          separate_last l.
          -- rewrite cat_app app_assoc in Hvsl.
             apply concat_cancel_last in Hvsl as [<- ->].
             eapply IHHred. done. 
             rewrite -app_assoc. done.
             apply const_list_split in Hvs as [??] => //.
             rewrite length_app in Hlen. lia.
          -- simpl in Hred. clear - Hred.
             remember [_] as es0.
             induction Hred.
             destruct H.
             all: try by inversion Heqes0.
             all: try by do 2 destruct vs => //.
             all: try by do 2 destruct ves => //. 
             ++ subst es. move/lfilledP in H0. inversion H0.
                do 2 destruct vs => //.
                all: do 2 destruct bef => //.
             ++ subst. move/lfilledP in H. inversion H; subst.
                all: try by do 2 destruct vs => //.
                all: try by do 2 destruct bef => //.
                destruct vs; last by inversion H1; subst.
                destruct es; first empty_list_no_reduce.
                inversion H1; subst.
                destruct es => //.
        * empty_list_no_reduce.
  Qed.

  
    Lemma resume_not_enough_arguments_no_reduce s f (vs : seq.seq administrative_instruction)
      t1s t2s i k tf hh hs s' f' es'  :
      stypes (f_inst f) i = Some (Tf t1s t2s) ->
      List.nth_error (s_conts s) k = Some (Cont_hh tf hh) ->
    reduce s f (vs ++ [AI_ref_cont k; AI_basic (BI_resume i hs)]) s' f' es' ->
    const_list vs ->
    length vs < length t1s ->
    False.
    Proof.
      intros Hi Hk Hred Hvs Hlen.
    lazymatch goal with _ : reduce _ _ ?es0 _ _ _ |- _ => remember es0 as es end.
    generalize dependent vs.
    induction Hred.
    all: intros vs' Heqes Hvs Hlen.
    inversion H.
    all: remember Heqes as H00; clear HeqH00 Heqes.
    all: subst.
    all: try (symmetry in H00; rewrite cat_app separate1 app_assoc in H00; symmetry in H00).
    all: try by rewrite separate1 in H00;
      apply concat_cancel_last in H00 as [??]; try apply const_list_concat.
    all: try by rewrite separate1 in H00;
      rewrite -cat_app catA in H00;
      apply concat_cancel_last in H00 as [??]; try apply const_list_concat.
    all: try by rewrite separate2 in H00;
      apply concat_cancel_last in H00 as [??]; try apply const_list_concat.
    all: try by rewrite separate3 in H00;
      apply concat_cancel_last in H00 as [??]; try apply const_list_concat.
    all: try by do 3 destruct vs' => //. 
    - move/lfilledP in H1; inversion H1.
      all: try (symmetry in H2; rewrite cat_app separate1 app_assoc in H2; symmetry in H2).
      all: apply first_values in H2 as (? & ? & ?) => //.
      all: apply const_list_concat => //.
    - rewrite cat_app separate1 app_assoc in H00.
      apply first_values in H00 as (? & ? & ?) => //=.
      inversion H6; subst.
      apply concat_cancel_last in H5 as [<- _].
      rewrite H0 in Hi. inversion Hi; subst.
      lia. all: apply const_list_concat => //.
    - repeat destruct vs' => //.
      inversion H00; subst. rewrite H in Hk => //. 
    - move/lfilledP in H; inversion H; subst.
      all: symmetry in H1; rewrite cat_app separate1 app_assoc in H1; symmetry in H1.
      2-4: apply first_values in H1 as (? & ? & ?) => //.
      2-4: apply const_list_concat => //.
      separate_last es'0.
      + rewrite -cat_app in H1.
        repeat rewrite catA in H1.
        apply concat_cancel_last in H1 as [??].
        eapply values_no_reduce.
        exact Hred.
        assert (const_list (app vs' [AI_ref_cont k])); first by apply const_list_concat.
        rewrite -H1 in H3.
        apply const_list_split in H3 as [? _].
        apply const_list_split in H3 as [_ ?] => //. 
      + separate_last es.
        * rewrite cats0 in H1. rewrite -cat_app catA in H1.
          apply concat_cancel_last in H1 as [Hvsl ->].
          separate_last l.
          -- rewrite cat_app app_assoc in Hvsl.
             apply concat_cancel_last in Hvsl as [<- ->].
             eapply IHHred. done. done.
             rewrite -app_assoc. done.
             apply const_list_split in Hvs as [??] => //.
             rewrite length_app in Hlen. lia.
          -- simpl in Hred. clear - Hred.
             remember [_] as es0.
             induction Hred.
             destruct H.
             all: try by inversion Heqes0.
             all: try by do 2 destruct vs => //.
             all: try by do 2 destruct ves => //. 
             ++ subst es. move/lfilledP in H0. inversion H0.
                do 2 destruct vs => //.
                all: do 2 destruct bef => //.
             ++ subst. move/lfilledP in H. inversion H; subst.
                all: try by do 2 destruct vs => //.
                all: try by do 2 destruct bef => //.
                destruct vs; last by inversion H1; subst.
                destruct es; first empty_list_no_reduce.
                inversion H1; subst.
                destruct es => //.
        * empty_list_no_reduce.
  Qed.


    Lemma throw_not_enough_arguments_no_reduce s f (vs : seq.seq administrative_instruction)
      x a ts s' f' es'  :
      nth_error (inst_tags (f_inst f)) x = Some a ->
      nth_error (datatypes.s_tags s) a = Some (Tf ts []) ->
    reduce s f (vs ++ [AI_basic (BI_throw x)]) s' f' es' ->
    const_list vs ->
    length vs < length ts ->
    False.
  Proof.
    intros Hx Ha Hred Hvs Hlen.
    lazymatch goal with _ : reduce _ _ ?es0 _ _ _ |- _ => remember es0 as es end.
    generalize dependent vs.
    induction Hred.
    all: intros vs' Heqes Hvs Hlen.
    inversion H.
    all: remember Heqes as H00; clear HeqH00 Heqes.
    all: subst.
    all: try by rewrite separate1 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate1 in H00;
      rewrite -cat_app catA in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate2 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate3 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by destruct vs' => //; destruct vs'.
    - move/lfilledP in H1; inversion H1.
      all: rewrite - (app_nil_r [_]) in H2.
      all: apply first_values in H2 as (? & ? & ?) => //.

    - apply concat_cancel_last in H00 as [??].
      inversion H3; subst.
      rewrite H in Hx. inversion Hx; subst.
      rewrite H0 in Ha. inversion Ha; subst.
      lia.
    - move/lfilledP in H; inversion H; subst.
      2-4: rewrite - (app_nil_r [_]) in H1.
      2-4: apply first_values in H1 as (? & ? & ?) => //.
      destruct (separate_last es'0) as [[??]|] eqn:Hlast.
      + apply separate_last_spec in Hlast as ->.
        rewrite -cat_app in H1.
        repeat rewrite catA in H1.
        apply concat_cancel_last in H1 as [??].
        eapply values_no_reduce.
        exact Hred.
        subst vs'. apply const_list_split in Hvs as [? _].
        apply const_list_split in H1 as [_ ?] => //. 
      + apply separate_last_None in Hlast as ->.
        destruct (separate_last es) as [[??]|] eqn:Hlast.
        * apply separate_last_spec in Hlast as ->.
          rewrite cats0 in H1. rewrite -cat_app catA in H1.
          apply concat_cancel_last in H1 as [<- ->].
          eapply IHHred. done. done. done.
          apply const_list_split in Hvs as [??] => //.
          rewrite length_app in Hlen. lia.
        * apply separate_last_None in Hlast as ->.
          empty_list_no_reduce.
  Qed.
  
  
   Lemma try_table_not_enough_arguments_no_reduce s f (vs : seq.seq administrative_instruction)
     i cs esb t1s t2s s' f' es'  :
     stypes (f_inst f) i = Some (Tf t1s t2s) ->
    reduce s f (vs ++ [AI_basic (BI_try_table i cs esb)]) s' f' es' ->
    const_list vs ->
    length vs < length t1s ->
    False.
  Proof.
    intros Hi Hred Hvs Hlen.
    lazymatch goal with _ : reduce _ _ ?es0 _ _ _ |- _ => remember es0 as es end.
    generalize dependent vs.
    induction Hred.
    all: intros vs' Heqes Hvs Hlen.
    inversion H.
    all: remember Heqes as H00; clear HeqH00 Heqes.
    all: subst.
    all: try by rewrite separate1 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate1 in H00;
      rewrite -cat_app catA in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate2 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate3 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by destruct vs' => //; destruct vs'.
    - move/lfilledP in H1; inversion H1.
      all: rewrite - (app_nil_r [_]) in H2.
      all: apply first_values in H2 as (? & ? & ?) => //.

    - apply concat_cancel_last in H00 as [??].
      inversion H4; subst. 
      rewrite H in Hi. inversion Hi; subst.
      lia.
    - move/lfilledP in H; inversion H; subst.
      2-4: rewrite - (app_nil_r [_]) in H1.
      2-4: apply first_values in H1 as (? & ? & ?) => //.
      destruct (separate_last es'0) as [[??]|] eqn:Hlast.
      + apply separate_last_spec in Hlast as ->.
        rewrite -cat_app in H1.
        repeat rewrite catA in H1.
        apply concat_cancel_last in H1 as [??].
        eapply values_no_reduce.
        exact Hred.
        subst vs'. apply const_list_split in Hvs as [? _].
        apply const_list_split in H1 as [_ ?] => //. 
      + apply separate_last_None in Hlast as ->.
        destruct (separate_last es) as [[??]|] eqn:Hlast.
        * apply separate_last_spec in Hlast as ->.
          rewrite cats0 in H1. rewrite -cat_app catA in H1.
          apply concat_cancel_last in H1 as [<- ->].
          eapply IHHred. done. done.
          apply const_list_split in Hvs as [??] => //.
          rewrite length_app in Hlen. lia.
        * apply separate_last_None in Hlast as ->.
          empty_list_no_reduce.
  Qed. 

  Lemma v_to_e_length: forall vs,
      length (v_to_e_list vs) = length vs.
  Proof.
    move => vs. elim: vs => //=.
    - move => a l IH. by f_equal.
  Qed.

  Lemma invoke_not_enough_arguments_no_reduce_native
        s f vs a0 s' f' es' i' t1s t2s ts es'' :
    nth_error (s_funcs s) a0 = Some (FC_func_native i' (Tf t1s t2s) ts es'') ->
    reduce s f (vs ++ [AI_invoke a0]) s' f' es' ->
    const_list vs ->
    length vs < length t1s ->
    False.
  Proof.
    intros Hfunc Hred Hvs Hlen.
    
    remember (cat vs [AI_invoke a0]) as es.
    generalize dependent vs.
    induction Hred.
    all: intros vs' Heqes Hvs Hlen.
    inversion H.
    all: remember Heqes as H00; clear HeqH00 Heqes.
    all: subst.
    all: try by rewrite separate1 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate1 in H00;
      rewrite -cat_app catA in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate2 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate3 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by destruct vs' => //; destruct vs'.
    - move/lfilledP in H1; inversion H1.
      all: rewrite - (app_nil_r [_]) in H2.
      all: apply first_values in H2 as (? & ? & ?) => //.
    - apply concat_cancel_last in H00 as [??].
      inversion H1; subst.
      rewrite Hfunc in H; inversion H; subst.
      rewrite v_to_e_length -H4 in Hlen.
      lia.
    - apply concat_cancel_last in H00 as [??].
      inversion H1; subst.
      rewrite Hfunc in H; inversion H; subst.
    - move/lfilledP in H; inversion H; subst.
      2-4: rewrite - (app_nil_r [_]) in H1.
      2-4: apply first_values in H1 as (? & ? & ?) => //.
      destruct (separate_last es'0) as [[??]|] eqn:Hlast.
      + apply separate_last_spec in Hlast as ->.
        rewrite -cat_app in H1.
        repeat rewrite catA in H1.
        apply concat_cancel_last in H1 as [??].
        eapply values_no_reduce.
        exact Hred.
        subst vs'. apply const_list_split in Hvs as [? _].
        apply const_list_split in H1 as [_ ?] => //. 
      + apply separate_last_None in Hlast as ->.
        destruct (separate_last es) as [[??]|] eqn:Hlast.
        * apply separate_last_spec in Hlast as ->.
          rewrite cats0 in H1. rewrite -cat_app catA in H1.
          apply concat_cancel_last in H1 as [<- ->].
          eapply IHHred. done. done.
          apply const_list_split in Hvs as [??] => //.
          rewrite length_app in Hlen. lia.
        * apply separate_last_None in Hlast as ->.
          empty_list_no_reduce.
  Qed.

 Lemma suspend_not_enough_arguments_no_reduce
   s f vs x a s' f' es' t1s t2s :
    nth_error (inst_tags (f_inst f)) x = Some a ->
    nth_error (datatypes.s_tags s) a = Some (Tf t1s t2s) ->
    reduce s f (vs ++ [AI_basic (BI_suspend (Mk_tagident x))]) s' f' es' ->
    const_list vs ->
    length vs < length t1s ->
    False.
  Proof.
    intros Hx Ha Hred Hvs Hlen.
    lazymatch goal with _ : reduce _ _ ?es0 _ _ _ |- _ => remember es0 as es end.
    generalize dependent vs.
    induction Hred.
    all: intros vs' Heqes Hvs Hlen.
    inversion H.
    all: remember Heqes as H00; clear HeqH00 Heqes.
    all: subst.
    all: try by rewrite separate1 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate1 in H00;
      rewrite -cat_app catA in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate2 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate3 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by destruct vs' => //; destruct vs'.
    - move/lfilledP in H1; inversion H1.
      all: rewrite - (app_nil_r [_]) in H2.
      all: apply first_values in H2 as (? & ? & ?) => //.
    - apply concat_cancel_last in H00 as [??].
      inversion H3; subst.
      rewrite H in Hx; inversion Hx; subst.
      rewrite H0 in Ha; inversion Ha; subst.
      rewrite length_map in Hlen.
      lia.
    - move/lfilledP in H; inversion H; subst.
      2-4: rewrite - (app_nil_r [_]) in H1.
      2-4: apply first_values in H1 as (? & ? & ?) => //.
      destruct (separate_last es'0) as [[??]|] eqn:Hlast.
      + apply separate_last_spec in Hlast as ->.
        rewrite -cat_app in H1.
        repeat rewrite catA in H1.
        apply concat_cancel_last in H1 as [??].
        eapply values_no_reduce.
        exact Hred.
        subst vs'. apply const_list_split in Hvs as [? _].
        apply const_list_split in H1 as [_ ?] => //. 
      + apply separate_last_None in Hlast as ->.
        destruct (separate_last es) as [[??]|] eqn:Hlast.
        * apply separate_last_spec in Hlast as ->.
          rewrite cats0 in H1. rewrite -cat_app catA in H1.
          apply concat_cancel_last in H1 as [<- ->].
          eapply IHHred. done. done. done.
          apply const_list_split in Hvs as [??] => //.
          rewrite length_app in Hlen. lia.
        * apply separate_last_None in Hlast as ->.
          empty_list_no_reduce.
  Qed.
  

  Lemma invoke_not_enough_arguments_no_reduce_host
        s f vs a0 s' f' es' t1s t2s h :
    nth_error (s_funcs s) a0 = Some (FC_func_host (Tf t1s t2s) h) ->
    reduce s f (vs ++ [AI_invoke a0]) s' f' es' ->
    const_list vs ->
    length vs < length t1s ->
    False.
  Proof.
       intros Hfunc Hred Hvs Hlen.
    remember (cat vs [AI_invoke a0]) as es.
    generalize dependent vs.
    induction Hred.
    all: intros vs' Heqes Hvs Hlen.
    inversion H.
    all: remember Heqes as H00; clear HeqH00 Heqes.
    all: subst.
    all: try by rewrite separate1 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate1 in H00;
      rewrite -cat_app catA in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate2 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by rewrite separate3 in H00;
      apply concat_cancel_last in H00 as [??].
    all: try by destruct vs' => //; destruct vs'.
    - move/lfilledP in H1; inversion H1.
      all: rewrite - (app_nil_r [_]) in H2.
      all: apply first_values in H2 as (? & ? & ?) => //.
    - apply concat_cancel_last in H00 as [??].
      inversion H1; subst.
      rewrite Hfunc in H; inversion H; subst.
    - apply concat_cancel_last in H00 as [??].
      inversion H1; subst.
      rewrite Hfunc in H; inversion H; subst.
      rewrite v_to_e_length -H3 in Hlen.
      lia.

    - move/lfilledP in H; inversion H; subst.
      2-4: rewrite - (app_nil_r [_]) in H1.
      2-4: apply first_values in H1 as (? & ? & ?) => //.
      destruct (separate_last es'0) as [[??]|] eqn:Hlast.
      + apply separate_last_spec in Hlast as ->.
        rewrite -cat_app in H1.
        repeat rewrite catA in H1.
        apply concat_cancel_last in H1 as [??].
        eapply values_no_reduce.
        exact Hred.
        subst vs'. apply const_list_split in Hvs as [? _].
        apply const_list_split in H1 as [_ ?] => //. 
      + apply separate_last_None in Hlast as ->.
        destruct (separate_last es) as [[??]|] eqn:Hlast.
        * apply separate_last_spec in Hlast as ->.
          rewrite cats0 in H1. rewrite -cat_app catA in H1.
          apply concat_cancel_last in H1 as [<- ->].
          eapply IHHred. done. done.
          apply const_list_split in Hvs as [??] => //.
          rewrite length_app in Hlen. lia.
        * apply separate_last_None in Hlast as ->.
          empty_list_no_reduce.
  Qed.

  Lemma prim_step_obs_efs_empty es es' σ σ' obs efs:
    prim_step es σ obs es' σ' efs ->
    (obs, efs) = ([], []).
  Proof.
    unfold prim_step, iris.prim_step.
    destruct σ as [[[??]?]?].
    destruct σ' as [[[??]?]?].
    by move => [_ [-> ->]].
  Qed.

  Lemma append_reducible (es1 es2: list administrative_instruction) σ:
    iris.to_val es1 = None ->
    reducible es1 σ ->
    reducible (es1 ++ es2) σ.
  Proof.
    unfold reducible => /=.
    move => Htv [κ [es' [σ' [efs HStep]]]].
    exists κ, (es' ++ es2), σ', efs.
    unfold iris.prim_step in * => //=.
    destruct σ as [[[hs ws] locs] inst].
    destruct σ' as [[[hs' ws'] locs'] inst'].
    destruct HStep as [HStep [-> ->]].
    repeat split => //.
    by apply r_elimr.
  Qed.

  Lemma AI_trap_reducible es2 σ :
    es2 ≠ [] -> 
    reducible ([AI_trap] ++ es2) σ.
  Proof.
    elim: es2;[done|].
    move => a l IH _.
    unfold reducible => /=.
    unfold language.reducible.
    exists [],[AI_trap],σ,[].
    simpl. unfold iris.prim_step.
    destruct σ as [[[hs ws] locs] inst].
    repeat split;auto.
    constructor. econstructor. auto.
    instantiate (1:=LH_base [] (a :: l)).
    unfold lfilled, lfill => //=.
  Qed.

  Lemma AI_trap_reducible_2 es1 σ :
    es1 ≠ [] ->
    const_list es1 ->
    reducible (es1 ++ [AI_trap]) σ.
  Proof.
    move => H H'.
    unfold reducible => /=.
    unfold language.reducible.
    exists [],[AI_trap],σ,[].
    simpl. unfold iris.prim_step.
    destruct σ as [[[hs ws] locs] inst].
    repeat split;auto.
    constructor. econstructor.
    destruct es1;auto.
    intros Hcontr. inversion Hcontr.
    destruct es1 => //=.
    instantiate (1:=LH_base (es1) []).
    unfold lfilled, lfill => //=.
    by rewrite H'.
  Qed.

  Lemma AI_trap_irreducible ws f ws' f' es':
    reduce ws f [AI_trap] ws' f' es' ->
    False.
  Proof.
    move => HReduce.
    remember ([AI_trap]) as e.
    induction HReduce => //=; subst; try by do 2 destruct vcs => //=.
    all: try by do 2 destruct vs => //. 
    - subst. inversion H; subst; clear H => //; by do 3 destruct vs => //=.
    - move/lfilledP in H.
      move/lfilledP in H0.
      inversion H => //; subst; clear H.
      all: try by do 3 destruct vs => //=.
      all: try by do 3 destruct bef => //=.
      inversion H0; subst; clear H0.
      destruct vs => /=; last by destruct vs, es, es'0 => //; inversion H1; subst.
      destruct es => /=; first by apply empty_no_reduce in HReduce.
      by destruct es, es'0 => //.
  Qed.
    
  Lemma AI_trap_reduce_det v ws f ws' f' es':
    reduce ws f ([AI_const v; AI_trap]) ws' f' es' ->
    (ws', f', es') = (ws, f, [AI_trap]).
  Proof.
    move => HReduce.
    remember ([AI_const v; AI_trap]) as es0.
    induction HReduce => //=; subst; try by do 3 destruct vcs => //=.
    all: try by do 3 destruct vs => //=.
    - inversion H; subst; clear H => //; by do 3 destruct vs => //=.
    - move/lfilledP in H.
      move/lfilledP in H0.
      inversion H => //; subst; clear H.
      all: try by destruct v; (try destruct v); do 3 destruct vs => //=.
      all: try by destruct v; (try destruct v); do 3 destruct bef => //=.
      inversion H0; subst; clear H0.
      destruct vs => /=.
      + destruct es => /=; first by apply empty_no_reduce in HReduce.
        destruct es => /=; simpl in H1; inversion H1; subst; clear H1; first apply values_no_reduce in HReduce => //.
        simpl; rewrite const_const => //.
        destruct es, es'0 => //=.
        rewrite cats0.
        by apply IHHReduce.
      + destruct vs => /=; last by destruct v; (try destruct v); destruct vs, es, es'0 => //; inversion H1; subst.
        inversion H1; subst; clear H1.
        destruct es => /=; first by apply empty_no_reduce in HReduce.
        destruct es, es'0 => //.
        inversion H2; subst.
        by apply AI_trap_irreducible in HReduce.
  Qed.

  
  Lemma prepend_reducible (es1 es2: list administrative_instruction) σ :
    (const_list es1 \/ es1 = [AI_trap]) ->
    reducible es2 σ ->
    reducible (es1 ++ es2) σ.
  Proof.
    intros [Hes1 | Hes1].
    induction es1 => //.
    intro H.
    simpl in Hes1.
    apply andb_true_iff in Hes1 as [Ha Hes1].
    specialize (IHes1 Hes1 H).
    destruct IHes1 as (? & ? & ? & ? & ?).
    exists x, (a :: x0), x1, x2.
    destruct σ as [[??]?] , x1 as [[??]?].
    destruct H0 as (? & ? & ?).
    repeat split => //=.
    eapply r_label ; last first.
    instantiate (1 := x0).
    instantiate (1 := LH_base [a] []).
    instantiate (1 := 0).
    unfold lfilled, lfill => /=.
    rewrite Ha => /=.
    by rewrite app_nil_r.
    unfold lfilled, lfill => /=.
    rewrite Ha => /=.
    rewrite app_nil_r.
    done.
    done.
    subst.
    intro ; apply AI_trap_reducible.
    destruct H as (? & ?& ? & ? & ?).
    destruct σ as [[??]?], x1 as [[??]?].
    destruct H as (? & ? & ?).
    intro ; subst.
    empty_list_no_reduce.
  Qed.
    
    

  Lemma first_non_value_reduce s f es s' f' es' :
    reduce s f es s' f' es' ->
    exists vs e es'', const_list vs /\ (to_val [e] = None \/ e = AI_trap) /\ es = vs ++ e :: es''.
  Proof.
    intros Hes.
    remember (to_val es) as tv. apply Logic.eq_sym in Heqtv. destruct tv;simplify_eq.
    { destruct v. { apply to_val_const_list in Heqtv.
                    exfalso ; values_no_reduce. }
      apply to_val_trap_is_singleton in Heqtv. subst.
      exfalso ; by apply (AI_trap_irreducible _ _ _ _ _ Hes).
      { apply reduce_val_false in Hes;try done. }
      { apply reduce_val_false in Hes;try done. }
      { apply reduce_val_false in Hes; try  done. } 
    }
      by apply first_non_value.
  Qed.

  Lemma trap_reduce_length s f es s' f' es' vs1 es2 :
    lfilled 0 (LH_base vs1 es2) [AI_trap] es ->
    reduce s f es s' f' es' ->
    exists n1 n2,
      (n1 + (length es2 - n2) < length vs1 + length es2 ∧
         n1 <= length vs1 ∧ n2 <= length es2) ∧
        lfilled 0 (LH_base (take n1 vs1) (drop n2 es2)) [AI_trap] es' /\
        (s, f) = (s', f').
  Proof.
    intros Hfill%lfilled_Ind_Equivalent Hred.
    revert vs1 es2 Hfill.
    generalize dependent es.
    induction 1;intros vs1 es2 Hfill;[|inversion Hfill;simplify_eq..].
    all: try do 2 destruct vs1 => //.
    all: try do 3 destruct vs1 => //.
    2: try by apply first_values in H11 as [?[? ?]];auto;[|apply v_to_e_is_const_list].
    { revert vs1 es2 Hfill.
      generalize dependent e.
      induction 1;intros vs1 es2 Hfill;inversion Hfill;simplify_eq.
      all: try do 2 destruct vs1 => //.
      all: try do 3 destruct vs1 => //.
      all: try by apply first_values in H5 as [?[? ?]];auto.
      all: try by destruct v; (try destruct v); do 3 destruct vs1 => //.
      - destruct ref; do 3 destruct vs1 => //.
      - destruct v1; (try destruct v);
          destruct v2; (try destruct v);
          do 5 destruct vs1 => //.
      - destruct v1; (try destruct v);
          destruct v2; (try destruct v);
          do 5 destruct vs1 => //.
      - apply lfilled_Ind_Equivalent in H0.
        inversion H0;simplify_eq.
        all: apply first_values in H1;auto.
        all: destruct H1 as [-> [? ->]] => //.
        exists 0,(length es2). split.
        + split;try lia. destruct vs1,es2 => //.
          all: simpl;lia. 
        + rewrite take_0 drop_all. split;auto.
    }
    all: try by rewrite -(app_nil_r [_]) in H6;
      apply first_values in H6 as (? & ? & ?) => //; try apply v_to_e_is_const_list.
    all: try by rewrite -(app_nil_r [_]) in H4;
      apply first_values in H4 as (? & ? & ?) => //; try apply v_to_e_is_const_list.
    all: try by rewrite -(app_nil_r [_]) in H7;
      apply first_values in H7 as (? & ? & ?) => //; try apply v_to_e_is_const_list.
    - rewrite (separate1  _ [_]) in H7.
      rewrite -cat_app catA in H7.
      rewrite -(app_nil_r [_]) in H7.
      apply first_values in H7 as (? & ? & ?) => //.
      repeat apply const_list_concat => //.
    - rewrite (separate1  _ [_]) in H7.
      rewrite -cat_app catA in H7.
      rewrite -(app_nil_r [_]) in H7.
      apply first_values in H7 as (? & ? & ?) => //.
      repeat apply const_list_concat => //.
      apply v_to_e_is_const_list.
    - rewrite (separate1  _ [_]) in H6.
      rewrite -cat_app catA in H6.
      rewrite -(app_nil_r [_]) in H6.
      apply first_values in H6 as (? & ? & ?) => //.
      repeat apply const_list_concat => //.
    - rewrite (separate1  _ [_]) in H11.
      rewrite -cat_app catA in H11.
      rewrite -(app_nil_r [_]) in H11.
      apply first_values in H11 as (? & ? & ?) => //.
      repeat apply const_list_concat => //.
      apply v_to_e_is_const_list.
    - destruct v; (try destruct v); do 3 destruct vs1 => //.
(*    - destruct v; (try destruct v); do 3 destruct vs1 => //. *)
    - move/lfilledP in H.
      inversion H; subst.
      all: try by apply first_values in H1 as (? & ? & ?).
      apply lfilled_Ind_Equivalent in H0. inversion H0;simplify_eq.
      apply val_head_stuck_reduce in Hred as Hnv.
      apply const_list_snoc_eq3 in H1;auto.
      2: destruct es => //.
      2:{ destruct (const_list es) eqn:Habs => //.
          apply values_no_reduce in Hred => //. } 
      2: intros ->;done.
      destruct H1 as [? [? [? [? [? ?]]]]];simplify_eq.
      assert (lfilledInd 0 (LH_base x x0) [AI_trap] (x ++ [AI_trap] ++ x0)%list) as HH;[by constructor|].
      apply IHHred in HH as [n1 [n2 [Hlt [Hlh' Heq]]]].
      apply lfilled_Ind_Equivalent in Hlh'.
      inversion Hlh';simplify_eq.
      exists (length vs + n1),n2.
      split. { rewrite !length_app. lia. }
      split;auto.
      rewrite take_app_add//.
      rewrite drop_app_le;[|lia].
      apply lfilled_Ind_Equivalent.
      repeat erewrite app_assoc.
      erewrite <- app_assoc.
      erewrite <- (app_assoc _ _ (drop n2 x0 ++ es'0)).
      constructor. apply const_list_app;auto. 
  Qed.

  Lemma lfilled_prepend_append k lh es LI vs es' :
    const_list vs ->
    lfilled k lh es LI -> exists lh', lfilled k lh' es (vs ++ LI ++ es').
  Proof.
    intros Hvs H; move/lfilledP in H; inversion H; subst.
    - exists (LH_base (vs ++ vs0) (es'0 ++ es')).
      unfold lfilled, lfill.
      rewrite const_list_concat => //.
      repeat rewrite -cat_app. repeat rewrite catA. done.
    - exists (LH_rec (vs ++ vs0) n es'0 lh' (es'' ++ es')).
      unfold lfilled, lfill; fold lfill.
      rewrite const_list_concat => //.
      move/lfilledP in H1. unfold lfilled in H1.
      destruct (lfill _ _ _) => //.  move/eqP in H1; subst l.
      repeat rewrite -cat_app. repeat rewrite -catA. done.
    - exists (LH_handler (vs ++ bef) hs lh' (aft ++ es')).
      unfold lfilled, lfill; fold lfill.
      rewrite const_list_concat => //.
      move/lfilledP in H1. unfold lfilled in H1.
      destruct (lfill _ _ _) => //. move/eqP in H1; subst l.
      repeat rewrite -cat_app. repeat rewrite -catA. done.
    - exists (LH_prompt (vs ++ bef) ts hs lh' (aft ++ es')).
      unfold lfilled, lfill; fold lfill.
      rewrite const_list_concat => //.
      move/lfilledP in H1. unfold lfilled in H1.
      destruct (lfill _ _ _) => //. move/eqP in H1; subst l.
      repeat rewrite -cat_app. repeat rewrite -catA. done.
  Qed. 
      

  
  Lemma trap_reduce s f es s' f' es' lh :
    lfilled 0 lh [AI_trap] es -> reduce s f es s' f' es' ->
    exists lh', lfilled 0 lh' [AI_trap] es' /\ (s, f) = (s', f').
  Proof.
    remember (S (length_rec es)) as m.
    assert (length_rec es < m); first lia.
    clear Heqm.
    generalize dependent es. generalize dependent es'. generalize dependent lh.
    induction m; intros lh es' es Hlen Hfill Hred; first lia.
    move/lfilledP in Hfill; inversion Hfill; subst.
    (*revert es es'.
    induction lh; intros es es' Hfill Hred; try done. *)
    - move/lfilledP in Hfill. eapply trap_reduce_length in Hfill;eauto.
      destruct Hfill as [? [? [? ?]]].
      eexists;eauto.
    - remember (cat bef $ cat [AI_handler hs LI] aft) as es.
      induction Hred.
      inversion H1.
      all: remember Heqes as H00; clear Heqes HeqH00.
      all: subst.
      all: try by rewrite separate1 in H00;
        apply first_values in H00 as (? & ? & ?);
        try rewrite /= const_const.
      all: try by rewrite separate2 in H00;
        apply first_values in H00 as (? & ? & ?).
      all: try by rewrite -(app_nil_l [_]) -(app_nil_r [_]) in H00;
        apply first_values in H00 as (? & ? & ?).
      all: try by rewrite - (app_nil_r [_]) in H00;
        apply first_values in H00 as (? & ? & ?);
        try apply v_to_e_is_const_list.
      all: try by rewrite separate2 separate1 in H00;
        repeat rewrite -cat_app in H00;
        repeat rewrite catA in H00;
        rewrite -catA in H00;
        rewrite -(catA bef) in H00;
        apply first_values in H00 as (? & ? & ?);
        (try apply const_list_concat);
        try apply v_to_e_is_const_list
      .  
      + rewrite separate1 in H00;
          apply first_values in H00 as (? & ? & ?) => //=.
        destruct ref => //.
      + rewrite -(app_nil_l [_]) -(app_nil_r [_]) in H00;
          apply first_values in H00 as (? & ? & ?) => //.
        inversion H4; subst.
        move/lfilledP in H0.
        apply lfilled_const in H0 as [??] => //.
      + exists (LH_base [] []). unfold lfilled, lfill => //=.
      + rewrite separate3 in H00;
          apply first_values in H00 as (? & ? & ?) => //=.
        do 2 rewrite const_const => //.
      + rewrite separate3 in H00;
          apply first_values in H00 as (? & ? & ?) => //=.
        do 2 rewrite const_const => //.
      + rewrite separate1 in H00;
          apply first_values in H00 as (? & ? & ?) => //.
        simpl; rewrite H2 => //.
      + exists (LH_base [] []); unfold lfilled, lfill => //.
      + rewrite -(app_nil_l [_]) -(app_nil_r [_]) in H00;
          apply first_values in H00 as (? & ? & ?) => //.
        inversion H4; subst.
        apply hfilled_to_llfill in H1 as [llh Hllh].
        rewrite -(cat0s [_]) in Hllh.
        rewrite -(cat0s [_]) in H0.
        move/lfilledP in H0.
        edestruct lfilled_llfill_first_values as (? & ?).
        exact H0. exact Hllh. all: try done.
      + rewrite -(app_nil_l [_]) -(app_nil_r [_]) in H00;
          apply first_values in H00 as (? & ? & ?) => //.
        inversion H4; subst.
        apply hfilled_to_llfill in H1 as [llh Hllh].
        rewrite -(cat0s [_]) in Hllh.
        rewrite -(cat0s [_]) in H0.
        move/lfilledP in H0.
        edestruct lfilled_llfill_first_values as (? & ?).
        exact H0. exact Hllh. all: try done.
      + move/lfilledP in H1; inversion H1; subst.
        all: move/lfilledP in H2; inversion H2; subst.
        all: try apply first_values in H3 as (? & ? & ?) => //.
        * specialize (IHHred IHm).
          apply const_list_snoc_eq3 in H3 as (vs2 & es2 & -> & -> & -> & Hvs2).
          all: try done.
          2: intros ->; empty_list_no_reduce.
          2: destruct (const_list es) eqn:Hres => //; by exfalso; eapply values_no_reduce.
          2: intros ->; by eapply AI_trap_irreducible.
          destruct vs.
          -- destruct es'0.
             ++ rewrite app_nil_r in Hfill, Hlen, H1, IHHred.
                rewrite cats0.
                apply IHHred => //.
             ++ eapply IHm in Hred as (lhres & Hfillres & Hσ).
                edestruct lfilled_prepend_append as [lhres' Hfillres'].
                instantiate (1 := []) => //.
                exact Hfillres.
                exists lhres'. split => //.
                repeat rewrite cat_app in Hlen.
                repeat rewrite length_app_rec in Hlen.
                specialize (length_cons_rec a es'0) as Hsol.
                repeat rewrite length_app_rec.
                lia.
                instantiate (1 := LH_handler vs2 hs lh' es2).
                apply/lfilledP; constructor => //.
          -- eapply IHm in Hred as (lhres & Hfillres & Hσ).
             edestruct lfilled_prepend_append as [lhres' Hfillres'].
             exact H6. exact Hfillres.
             exists lhres'. split => //.
             repeat rewrite cat_app in Hlen.
             repeat rewrite length_app_rec in Hlen.
             specialize (length_cons_rec a vs) as Hsol.
             repeat rewrite length_app_rec.
             lia.
             instantiate (1 := LH_handler vs2 hs lh' es2).
             apply/lfilledP; constructor => //.
        * inversion H5; subst. clear IHHred.
          edestruct IHm as (lhres & Hfillres & Hσ).
          3:{ eapply r_label.
              exact Hred.
              apply/lfilledP. exact H8.
              apply/lfilledP. exact H14. }
          repeat rewrite cat_app in Hlen.
          repeat rewrite length_app_rec in Hlen.
          unfold length_rec.
          rewrite /length_rec /= in Hlen.
          lia.
          apply/lfilledP. exact H0.
          exists (LH_handler bef hs lhres aft).
          split => //. apply/lfilledP. constructor => //.
          apply/lfilledP => //.
    - remember (cat bef $ cat [AI_prompt ts hs LI] aft) as es.
      induction Hred.
      inversion H1.
      all: remember Heqes as H00; clear Heqes HeqH00.
      all: subst.
      all: try by rewrite separate1 in H00;
        apply first_values in H00 as (? & ? & ?);
        try rewrite /= const_const.
      all: try by rewrite separate2 in H00;
        apply first_values in H00 as (? & ? & ?).
      all: try by rewrite -(app_nil_l [_]) -(app_nil_r [_]) in H00;
        apply first_values in H00 as (? & ? & ?).
      all: try by rewrite - (app_nil_r [_]) in H00;
        apply first_values in H00 as (? & ? & ?);
        try apply v_to_e_is_const_list.
      all: try by rewrite separate2 separate1 in H00;
        repeat rewrite -cat_app in H00;
        repeat rewrite catA in H00;
        rewrite -catA in H00;
        rewrite -(catA bef) in H00;
        apply first_values in H00 as (? & ? & ?);
        (try apply const_list_concat);
        try apply v_to_e_is_const_list
      .  
      + rewrite separate1 in H00;
          apply first_values in H00 as (? & ? & ?) => //=.
        destruct ref => //.
      + rewrite -(app_nil_l [_]) -(app_nil_r [_]) in H00;
          apply first_values in H00 as (? & ? & ?) => //.
        inversion H4; subst.
        move/lfilledP in H0.
        apply lfilled_const in H0 as [??] => //.
      + exists (LH_base [] []). unfold lfilled, lfill => //=.
      + rewrite separate3 in H00;
          apply first_values in H00 as (? & ? & ?) => //=.
        do 2 rewrite const_const => //.
      + rewrite separate3 in H00;
          apply first_values in H00 as (? & ? & ?) => //=.
        do 2 rewrite const_const => //.
      + rewrite separate1 in H00;
          apply first_values in H00 as (? & ? & ?) => //.
        simpl; rewrite H2 => //.
      + exists (LH_base [] []); unfold lfilled, lfill => //.
      + rewrite -(app_nil_l [_]) -(app_nil_r [_]) in H00;
          apply first_values in H00 as (? & ? & ?) => //.
        inversion H5; subst.
        apply hfilled_to_llfill in H4 as [llh Hllh].
        rewrite -(cat0s [_]) in Hllh.
        rewrite -(cat0s [_]) in H0.
        move/lfilledP in H0.
        edestruct lfilled_llfill_first_values as (? & ?).
        exact H0. exact Hllh. all: try done.
      + rewrite -(app_nil_l [_]) -(app_nil_r [_]) in H00;
          apply first_values in H00 as (? & ? & ?) => //.
        inversion H6; subst.
        apply hfilled_to_llfill in H4 as [llh Hllh].
        rewrite -(cat0s [_]) in Hllh.
        rewrite -(cat0s [_]) in H0.
        move/lfilledP in H0.
        edestruct lfilled_llfill_first_values as (? & ?).
        exact H0. exact Hllh. all: try done.
      + move/lfilledP in H1; inversion H1; subst.
        all: move/lfilledP in H2; inversion H2; subst.
        all: try apply first_values in H3 as (? & ? & ?) => //.
        * specialize (IHHred IHm).
          apply const_list_snoc_eq3 in H3 as (vs2 & es2 & -> & -> & -> & Hvs2).
          all: try done.
          2: intros ->; empty_list_no_reduce.
          2: destruct (const_list es) eqn:Hres => //; by exfalso; eapply values_no_reduce.
          2: intros ->; by eapply AI_trap_irreducible.
          destruct vs.
          -- destruct es'0.
             ++ rewrite app_nil_r in Hfill, Hlen, H1, IHHred.
                rewrite cats0.
                apply IHHred => //.
             ++ eapply IHm in Hred as (lhres & Hfillres & Hσ).
                edestruct lfilled_prepend_append as [lhres' Hfillres'].
                instantiate (1 := []) => //.
                exact Hfillres.
                exists lhres'. split => //.
                repeat rewrite cat_app in Hlen.
                repeat rewrite length_app_rec in Hlen.
                specialize (length_cons_rec a es'0) as Hsol.
                repeat rewrite length_app_rec.
                lia.
                instantiate (1 := LH_prompt vs2 ts hs lh' es2).
                apply/lfilledP; constructor => //.
          -- eapply IHm in Hred as (lhres & Hfillres & Hσ).
             edestruct lfilled_prepend_append as [lhres' Hfillres'].
             exact H6. exact Hfillres.
             exists lhres'. split => //.
             repeat rewrite cat_app in Hlen.
             repeat rewrite length_app_rec in Hlen.
             specialize (length_cons_rec a vs) as Hsol.
             repeat rewrite length_app_rec.
             lia.
             instantiate (1 := LH_prompt vs2 ts hs lh' es2).
             apply/lfilledP; constructor => //.
        * inversion H5; subst. clear IHHred.
          edestruct IHm as (lhres & Hfillres & Hσ).
          3:{ eapply r_label.
              exact Hred.
              apply/lfilledP. exact H8.
              apply/lfilledP. exact H15. }
          repeat rewrite cat_app in Hlen.
          repeat rewrite length_app_rec in Hlen.
          unfold length_rec.
          rewrite /length_rec /= in Hlen.
          lia.
          apply/lfilledP. exact H0.
          exists (LH_prompt bef ts hs lhres aft).
          split => //. apply/lfilledP. constructor => //.
          apply/lfilledP => //.
Qed.          

  Lemma lfilled_reducible i lh e LI σ :
    lfilled i lh e LI ->
    reducible e σ ->
    reducible LI σ.
  Proof.
    intros Hfill [obs [e' [σ' [efs Hred]]]].
    unfold reducible, language.reducible.
    specialize (lfilled_swap e' Hfill) as [LI' HLI'].
    exists [], LI', σ', [].
    destruct σ as [[[? ?] ?] ?].
    destruct σ' as [[[? ?] ?] ?].
    rewrite /= /iris.prim_step in Hred.
    destruct Hred as [Hred [-> ->]].
    split;auto.
    by eapply r_label => //.
  Qed.

  Lemma local_frame_reducible n e s v i v' i' :
    reducible e (s,v,i) ->
    reducible [AI_local n (Build_frame v i) e] (s,v',i').
  Proof.
    intros [obs [e' [σ' [efs Hred]]]].
    unfold reducible, language.reducible.
    destruct σ' as [[ ? ?] ?].
    exists [], [AI_local n (Build_frame l i0) e'], (s0,v',i'), [].
    rewrite /= /iris.prim_step in Hred.
    destruct Hred as [Hred [-> ->]]. eauto.
    split;auto.
    eapply r_local => //.
  Qed.

  Lemma local_frame_lfilled_reducible j lh LI n e s v i v' i' :
    lfilled j lh e LI ->
    reducible e (s,v,i) ->
    reducible [AI_local n (Build_frame v i) LI] (s,v',i').
  Proof.
    intros Hfill Hred.
    apply lfilled_reducible with (i:=j) (lh:=lh) (LI:=LI) in Hred;auto.
    apply local_frame_reducible. auto.
  Qed.

  
  Lemma reduce_focus s f es s' f' es':
    reduce s f es s' f' es' ->
    (exists k lh vs e es'', const_list vs /\ (is_const e = false) /\
                         reduce s f (vs ++ [e]) s' f' es''  /\
                         lfilled k lh (vs ++ [e]) es /\ 
                         lfilled k lh es'' es')
    \/
      (exists k lh lhtr LI, lhtr <> LH_base [] [] /\
                         lfilled 0 lhtr [AI_trap] LI /\
                         lfilled k lh LI es /\
                         lfilled k lh [AI_trap] es' /\
                         (s, f) = (s', f')).
  Proof.
    intro Hred.
    induction Hred ;
      (try by left ; eexists 0, (LH_base [] []), [] , _, _ ;
       repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
       (try by rewrite app_nil_r) ; (try by apply v_to_e_is_const_list); constructor ) ; 
      (try by left ; eexists 0, (LH_base [] []), [_] , _, _ ;
       repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
       (try by rewrite app_nil_r) ; (repeat rewrite const_const); (try by apply v_to_e_is_const_list); constructor).
    (*; 
      (try by left ; eexists 0, (LH_base [] []), [_ ; _] , _, _ ;
       repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
       (try by rewrite app_nil_r) ; (try by apply v_to_e_is_const_list); constructor );
      (try by left ; eexists 0, (LH_base [] []), _ , _, _ ;
       repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
       (try by rewrite app_nil_r) ; (try by apply v_to_e_is_const_list); constructor).
    *)
    { destruct H.
      all: try by left; eexists 0, (LH_base [] []), [], _, _;
        repeat split; unfold lfilled, lfill; simpl; (try done); (try done);
        (try by rewrite app_nil_r);
        constructor; econstructor.
      all: try by left; eexists 0, (LH_base [] []), [_], _, _;
        repeat split; unfold lfilled, lfill; simpl; (try done); (try done);
        (try by rewrite app_nil_r); (try by rewrite const_const);
        constructor; constructor.
      all: try by left; eexists 0, (LH_base [] []), [_; _], _, _;
        repeat split; unfold lfilled, lfill; simpl; (try done); (try done);
        (try by rewrite app_nil_r);
        constructor; constructor.
      all: try by left; eexists 0, (LH_base [] []), [_; _; _], _, _;
        repeat split; unfold lfilled, lfill; simpl; (try done); (try done);
        (try by rewrite app_nil_r); (try by repeat rewrite const_const);
        constructor; constructor.
      all: try by left ; eexists 0, (LH_base [] []), _, _, _ ;
        repeat split ; unfold lfilled, lfill ; simpl ;
        (try done) ; (try done) ;
        (try by rewrite app_nil_r) ; 
        do 2 econstructor => //.
      - left; eexists 0, (LH_base [] []), [_], _, _.
        repeat split; unfold lfilled, lfill; simpl; (try done); (try done);
          (try by rewrite app_nil_r).
        destruct ref => //. 
        constructor; constructor. done.
      - left; eexists 0, (LH_base [] []), [_], _, _.
        repeat split; unfold lfilled, lfill; simpl; (try done); (try done);
          (try by rewrite app_nil_r).
        rewrite H => //. 
        constructor. econstructor => //.
      - right. exists 0, (LH_base [] []), lh, es.
        repeat split => //. intros ->.
        rewrite /lfilled /lfill /= in H0. move/eqP in H0. by apply H.
        rewrite /lfilled /lfill /= app_nil_r //. }
    - left; eexists 0, (LH_base [] []), [_], _, _.
        repeat split; unfold lfilled, lfill; simpl; (try done); (try done);
          (try by rewrite app_nil_r).
        eapply r_call_indirect_success => //.
    - left ; eexists 0, (LH_base [] []), [_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r). 
      eapply r_call_indirect_failure1 => //.
    - left ; eexists 0, (LH_base [] []), [_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_call_reference => //.
    - left; eexists 0, (LH_base [] []), _, _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      subst; apply v_to_e_is_const_list. done. eapply r_invoke_native => //. 
    - left ; eexists 0, (LH_base [] []), _, _, _ ; repeat split ;
        (try unfold lfilled, lfill => //=) ; (try done) ; (try by rewrite app_nil_r).
      rewrite H1 ; by apply v_to_e_is_const_list. done.
      eapply r_invoke_host => //.
    - left ; eexists 0, (LH_base [] []), _, _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r). done.
      eapply r_try_table => //.
    - left ; eexists 0, (LH_base [] []), _, _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r). subst; apply v_to_e_is_const_list. done.
      eapply r_throw => //.
    - left ; eexists 0, (LH_base [] []), [_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_throw_ref_desugar => //.
    - left ; eexists 0, (LH_base [] []), [], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_throw_ref => //.
    - left ; eexists 0, (LH_base [] []), [], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_throw_ref_ref => //. 
    - left ; eexists 0, (LH_base [] []), (_ ++ [_]), _, _.
      repeat split ; unfold lfilled, lfill ; simpl ;
        (repeat rewrite -cat_app); (try by rewrite cats0 -catA /=); (try done) ; (try done); (try by rewrite cats0).
      apply const_list_concat => //.
      rewrite -catA.
      eapply r_resume => //.
    - left ; eexists 0, (LH_base [] []), [_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_resume_failure => //.
    - left ; eexists 0, (LH_base [] []), _, _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      apply v_to_e_is_const_list. done.
      eapply r_suspend_desugar => //.
    - left ; eexists 0, (LH_base [] []), (_ ++ [_]), _, _.
      repeat split ; unfold lfilled, lfill ; simpl ;
        (repeat rewrite -cat_app); (try by rewrite cats0 -catA /=); (try done) ; (try done); (try by rewrite cats0).
      apply const_list_concat => //. apply v_to_e_is_const_list => //.
      rewrite -catA. eapply r_switch_desugar => //.
    - left ; eexists 0, (LH_base [] []), [], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_suspend => //.
    - left ; eexists 0, (LH_base [] []), [], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_switch => //.
    - left ; eexists 0, (LH_base [] []), [], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_switch_failure => //.
    - left ; eexists 0, (LH_base [] []), (_ ++ [_]), _, _.
      repeat split ; unfold lfilled, lfill ; simpl ;
        (repeat rewrite -cat_app); (try by rewrite cats0 -catA /=); (try done) ; (try done); (try by rewrite cats0).
      apply const_list_concat => //.
      rewrite -catA. eapply r_contbind => //.
    - left ; eexists 0, (LH_base [] []), [_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_contbind_failure => //.
    - left ; eexists 0, (LH_base [] []), (_ ++ [_]), _, _.
      repeat split ; unfold lfilled, lfill ; simpl ;
        (repeat rewrite -cat_app); (try by rewrite cats0 -catA /=); (try done) ; (try done); (try by rewrite cats0).
      apply const_list_concat => //. subst; apply v_to_e_is_const_list.
      rewrite -catA. eapply r_resume_throw => //.
    - left ; eexists 0, (LH_base [] []), [_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_resume_throw_failure => //.
    - left ; eexists 0, (LH_base [] []), [_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r). rewrite const_const => //. 
      eapply r_set_local => //. 
    - left ; eexists 0, (LH_base [] []), [_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_load_success => //.
    - left ; eexists 0, (LH_base [] []), [_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_load_failure => //. 
    - left ; eexists 0, (LH_base [] []), [_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_load_packed_success => //. 
    - left ; eexists 0, (LH_base [] []), [_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_load_packed_failure => //.
    - left ; eexists 0, (LH_base [] []), [_;_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_store_success => //. 
    - left ; eexists 0, (LH_base [] []), [_;_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_store_failure => //. 
    - left ; eexists 0, (LH_base [] []), [_;_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_store_packed_success => //. 
    - left ; eexists 0, (LH_base [] []), [_;_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_store_packed_failure => //. 
    - left ; eexists 0, (LH_base [] []), [], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_current_memory => //. 
    - left ; eexists 0, (LH_base [] []), [_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_grow_memory_success => //. 
    - left ; eexists 0, (LH_base [] []), [_], _, _.
      repeat split ; unfold lfilled, lfill ; simpl ; (try done) ; (try done) ;
        (try by rewrite app_nil_r).
      eapply r_grow_memory_failure => //. 
    - destruct IHHred as [ (k0 & lh0 & vs & e & es'' & Hvs & He & Hred' & Hes & Hes')
                         | (k0 & lh0 & bef & aft & Hbef & Hba & Hfill & Hfill' & Hσ) ].
      + destruct (lfilled_trans2 _ _ _ _ _ _ _ _ _ _ Hes Hes' H H0) as (lh' & Hfill1 & Hfill2).
        left ; exists (k0 + k), lh', vs, e, es'' => //=.  
      + destruct (lfilled_trans2 _ _ _ _ _ _ _ _ _ _ Hfill Hfill' H H0)
          as (lh' & Hfill1 & Hfill2).
        right ; exists (k0 + k), lh', bef, aft => //=.
  Qed.


  Lemma lfilled_last k lh es LI x :
    lfilled k lh [es] (LI ++ [::x]) ->
    (exists lh', lfilled k lh' [es] LI) \/ const_list LI.
  Proof.
    destruct lh as [bef aft | bef n es' lh aft | bef hs lh aft | bef tf hs lh aft].
    all: unfold lfilled, lfill; fold lfill.
    1-2: destruct k => //.
    all: destruct (const_list bef) eqn:Hbef => //.
    2-4: destruct (lfill _ _ _) eqn:Hfill => //.
    all: intros H.
    all: move/eqP in H.
    all: destruct (separate_last aft) as [[??]|] eqn:Hlast.
    all: try (apply separate_last_spec in Hlast as -> ; left).
    all: try (apply separate_last_None in Hlast as -> ; right).
    all: try rewrite app_nil_r in H.
    all: try rewrite cats0 in H.
    all: try rewrite app_comm_cons in H.
    all: repeat rewrite -cat_app in H. 
    all: repeat rewrite catA in H.
    all: apply concat_cancel_last in H as [-> ->].
    all: try done.
    exists (LH_base bef l).
    2: eexists (LH_rec bef n es' lh l0).
    3: eexists (LH_handler bef hs lh l0).
    4: eexists (LH_prompt bef tf hs lh l0).
    all: simpl.
    all: rewrite Hbef.
    2-4: rewrite Hfill.
    all: try by rewrite -catA.
    done.
  Qed. 
    
  Lemma lfilled_is_nil k lh es :
    lfilled k lh es [] -> k = 0 /\ lh = LH_base [] [] /\ es = [].
  Proof.
    intros H. move/lfilledP in H. inversion H; subst.
    all: try destruct vs => //.
    all: try destruct bef => //.
    destruct es => //.
    destruct es' => //.
  Qed. 
  
  Lemma reduce_append: forall e es es' σ σ' efs obs,
      reducible es σ ->
      prim_step (es ++ [e]) σ obs es' σ' efs ->
      (es' = take (length es' - 1) es' ++ [e] /\
         prim_step es σ obs (take (length es' - 1) es') σ' efs)
      \/ (exists lh lh', lfilled 0 lh [AI_trap] es' /\ lfilled 0 lh' [AI_trap] es /\ σ = σ').
  Proof.
    destruct σ as [[[??]?]?].
    destruct σ' as [[[??]?]?].
    intros efs obs Hred Hstep.
    destruct Hstep as (Hstep & -> & ->).
    destruct Hred as (obs & es1 & [[[??]?]?] & efs & (Hred & -> & ->)).
    destruct (reduce_focus _ _ _ _ _ _ Hstep) as [ (k & lh & vs & e0 & es'' &
                                                          Hvs & He & Hred' & Hes & Hes')
                                                     | (k & lh & lhtr & LI & Hlhtr & Htrap &
                                                          Hfill & Hfill' & Hσ)].
    - destruct lh.
      all: unfold lfilled, lfill in Hes; fold lfill in Hes.
      1-2: destruct k => //.
      all: destruct (const_list l2) eqn:Hl2 => //. 
      2-4: destruct (lfill _ _ _) eqn:Hfill => //.
      all: move/eqP in Hes.
      + destruct (separate_last l3) as [[??]|] eqn:Hlast.
        * apply separate_last_spec in Hlast as ->.
          repeat rewrite -cat_app in Hes.
          repeat rewrite catA in Hes.
          apply concat_cancel_last in Hes as [-> ->].
          unfold lfilled, lfill in Hes'.
          rewrite Hl2 in Hes'. move/eqP in Hes'. subst es'.
          repeat rewrite app_assoc. rewrite length_app /= Nat.add_sub take_app.
          left. repeat split => //=.
          repeat rewrite firstn_all. rewrite Nat.sub_diag /= app_nil_r. done.
          eapply r_label. done.
          instantiate (1 := LH_base l2 l4). instantiate (1 := 0).
          rewrite /lfilled /lfill /= Hl2 /=.
          repeat rewrite -cat_app. repeat rewrite catA. done.
          rewrite Nat.sub_diag.
          rewrite /lfilled /lfill /= Hl2 /=.
          rewrite firstn_all app_nil_r app_assoc. done.
        * apply separate_last_None in Hlast as ->.
          rewrite app_nil_r app_assoc in Hes.
          apply concat_cancel_last in Hes as [-> ->].
          exfalso; eapply values_no_reduce; first exact Hred.
          apply const_list_concat => //.
      + destruct (separate_last l4) as [[??]|] eqn:Hlast.
        * apply separate_last_spec in Hlast as ->.
          repeat rewrite -cat_app in Hes.
          rewrite app_comm_cons in Hes.
          rewrite -cat_app in Hes.
          repeat rewrite catA in Hes.
          apply concat_cancel_last in Hes as [-> ->].
          left. unfold lfilled, lfill in Hes'; fold lfill in Hes'.
          rewrite Hl2 in Hes'. destruct (lfill _ _ es'') eqn:Hfill' => //.
          move/eqP in Hes'; subst es'.
          rewrite app_comm_cons. repeat rewrite app_assoc.
          rewrite length_app /= Nat.add_sub take_app.
          repeat split => //=. rewrite firstn_all Nat.sub_diag app_nil_r //.
          eapply r_label. done.
          instantiate (1 := LH_rec l2 n l3 lh l6).
          instantiate (1 := S k).
          unfold lfilled, lfill; fold lfill; rewrite Hl2.
          rewrite Hfill. done.
          unfold lfilled, lfill; fold lfill; rewrite Hl2 Hfill'.
          repeat rewrite firstn_all. rewrite Nat.sub_diag /= app_nil_r.
          done.
        * apply separate_last_None in Hlast as ->.
          apply concat_cancel_last in Hes as [-> ->].
          exfalso; eapply values_no_reduce. exact Hred. done.
      + destruct (separate_last l4) as [[??]|] eqn:Hlast.
        * apply separate_last_spec in Hlast as ->.
          repeat rewrite -cat_app in Hes.
          repeat rewrite catA in Hes.
          apply concat_cancel_last in Hes as [-> ->].
          left. unfold lfilled, lfill in Hes'; fold lfill in Hes'.
          rewrite Hl2 in Hes'. destruct (lfill _ _ es'') eqn:Hfill' => //.
          move/eqP in Hes'; subst es'.
          repeat rewrite catA.
          rewrite length_app /= Nat.add_sub take_app.
          repeat split => //=. rewrite firstn_all Nat.sub_diag app_nil_r //.
          eapply r_label. done.
          instantiate (1 := LH_handler l2 l3 lh l6).
          instantiate (1 := k).
          unfold lfilled, lfill; fold lfill; rewrite Hl2.
          rewrite Hfill. rewrite catA. done.
          unfold lfilled, lfill; fold lfill; rewrite Hl2 Hfill'.
          repeat rewrite firstn_all. rewrite Nat.sub_diag /= app_nil_r.
          rewrite -catA. done.
        * apply separate_last_None in Hlast as ->.
          apply concat_cancel_last in Hes as [-> ->].
          exfalso; eapply values_no_reduce. exact Hred. done.
      + destruct (separate_last l5) as [[??]|] eqn:Hlast.
        * apply separate_last_spec in Hlast as ->.
          repeat rewrite -cat_app in Hes.
          repeat rewrite catA in Hes.
          apply concat_cancel_last in Hes as [-> ->].
          left. unfold lfilled, lfill in Hes'; fold lfill in Hes'.
          rewrite Hl2 in Hes'. destruct (lfill _ _ es'') eqn:Hfill' => //.
          move/eqP in Hes'; subst es'.
          repeat rewrite catA.
          rewrite length_app /= Nat.add_sub take_app.
          repeat split => //=. rewrite firstn_all Nat.sub_diag app_nil_r //.
          eapply r_label. done.
          instantiate (1 := LH_prompt l2 l3 l4 lh l7).
          instantiate (1 := k).
          unfold lfilled, lfill; fold lfill; rewrite Hl2.
          rewrite Hfill. rewrite catA. done.
          unfold lfilled, lfill; fold lfill; rewrite Hl2 Hfill'.
          repeat rewrite firstn_all. rewrite Nat.sub_diag /= app_nil_r.
          rewrite -catA. done.
        * apply separate_last_None in Hlast as ->.
          apply concat_cancel_last in Hes as [-> ->].
          exfalso; eapply values_no_reduce. exact Hred. done.
    - inversion Hσ; subst; clear Hσ.
      destruct lh.
      all: unfold lfilled, lfill in Hfill; fold lfill in Hfill.
      1-2: destruct k => //.
      all: destruct (const_list l) eqn:Hl => //.
      2-4: destruct (lfill _ _ _) eqn:Hfillrec => //.
      all: move/eqP in Hfill.
      + right. destruct (separate_last l2) as [[??]|] eqn:Hlast.
        * apply separate_last_spec in Hlast as ->.
          repeat rewrite app_assoc in Hfill.
          apply concat_cancel_last in Hfill as [-> ->].
          assert (lfilled 0 (LH_base l l3) LI ((l ++ LI) ++ l3)%list).
          { rewrite /lfilled /lfill /= Hl app_assoc //. }
          edestruct lfilled_trans as [lh' Hlh'].
          exact Htrap. exact H.
          simpl in Hlh'.
          repeat eexists.
          exact Hfill'. exact Hlh'.
        * apply separate_last_None in Hlast as ->.
          rewrite app_nil_r in Hfill.
          destruct (separate_last LI) as [[??]|] eqn:Hlast.
          -- apply separate_last_spec in Hlast as ->.
             rewrite app_assoc in Hfill.
             apply concat_cancel_last in Hfill as [-> ->].
             apply lfilled_last in Htrap.
             destruct Htrap as [[lh' Htrap] | Hl2].
             ++ assert (lfilled 0 (LH_base l []) l2 (l ++ l2)%list).
                rewrite /lfilled /lfill /= Hl app_nil_r //.
                edestruct lfilled_trans.
                exact Htrap. exact H.
                repeat eexists.
                exact Hfill'. exact H0.
             ++ exfalso; eapply values_no_reduce.
                exact Hred. apply const_list_concat => //.
          -- apply separate_last_None in Hlast as ->.
             apply lfilled_is_nil in Htrap as (? & ? & ?) => //.
      + destruct (separate_last l3) as [[??]|] eqn:Hlast.
        * apply separate_last_spec in Hlast as ->.
          rewrite app_comm_cons in Hfill.
          rewrite app_assoc in Hfill.
          apply concat_cancel_last in Hfill as [-> ->].
          unfold lfilled, lfill in Hfill'; fold lfill in Hfill'.
          rewrite Hl in Hfill'. destruct (lfill _ _ [_]) eqn:Hfilltrap => //.
          move/eqP in Hfill'; subst es'. left.
          rewrite app_comm_cons.
          repeat rewrite app_assoc.
          rewrite length_app /= Nat.add_sub take_app.
          repeat split => //=.
          rewrite firstn_all Nat.sub_diag app_nil_r //.
          eapply r_label; last first. 
          instantiate (2 := LH_rec l n l2 lh l5).
          instantiate (2 := S k).
          unfold lfilled, lfill; fold lfill => //=.
          rewrite Hl.
          erewrite Hfilltrap.
          rewrite firstn_all Nat.sub_diag app_nil_r //.
          unfold lfilled, lfill; fold lfill => /=.
          rewrite Hl. erewrite Hfillrec. done.
          constructor. econstructor.
          intros ->. apply filled_trivial in Htrap as [_ ->]. done.
          exact Htrap.
        * apply separate_last_None in Hlast as ->.
          apply concat_cancel_last in Hfill as [-> ->].
          exfalso; eapply values_no_reduce.
          exact Hred. done.
      + destruct (separate_last l3) as [[??]|] eqn:Hlast.
        * apply separate_last_spec in Hlast as ->.
          repeat rewrite -cat_app in Hfill.
          repeat rewrite catA in Hfill.
          apply concat_cancel_last in Hfill as [-> ->].
          unfold lfilled, lfill in Hfill'; fold lfill in Hfill'.
          rewrite Hl in Hfill'. destruct (lfill _ _ [_]) eqn:Hfilltrap => //.
          move/eqP in Hfill'; subst es'. left.
          repeat rewrite catA.
          rewrite length_app /= Nat.add_sub take_app.
          repeat split => //=.
          rewrite firstn_all Nat.sub_diag app_nil_r //.
          eapply r_label; last first. 
          instantiate (2 := LH_handler l l2 lh l5).
          instantiate (2 := k).
          unfold lfilled, lfill; fold lfill => //=.
          rewrite Hl.
          erewrite Hfilltrap.
          rewrite firstn_all Nat.sub_diag app_nil_r //.
          by rewrite -catA.
          unfold lfilled, lfill; fold lfill => /=.
          rewrite Hl. erewrite Hfillrec. by rewrite -catA.
          constructor. econstructor.
          intros ->. apply filled_trivial in Htrap as [_ ->]. done.
          exact Htrap.
        * apply separate_last_None in Hlast as ->.
          apply concat_cancel_last in Hfill as [-> ->].
          exfalso; eapply values_no_reduce.
          exact Hred. done.
      + destruct (separate_last l4) as [[??]|] eqn:Hlast.
        * apply separate_last_spec in Hlast as ->.
          repeat rewrite -cat_app in Hfill.
          repeat rewrite catA in Hfill.
          apply concat_cancel_last in Hfill as [-> ->].
          unfold lfilled, lfill in Hfill'; fold lfill in Hfill'.
          rewrite Hl in Hfill'. destruct (lfill _ _ [_]) eqn:Hfilltrap => //.
          move/eqP in Hfill'; subst es'. left.
          repeat rewrite catA.
          rewrite length_app /= Nat.add_sub take_app.
          repeat split => //=.
          rewrite firstn_all Nat.sub_diag app_nil_r //.
          eapply r_label; last first. 
          instantiate (2 := LH_prompt l l2 l3 lh l6).
          instantiate (2 := k).
          unfold lfilled, lfill; fold lfill => //=.
          rewrite Hl.
          erewrite Hfilltrap.
          rewrite firstn_all Nat.sub_diag app_nil_r //.
          by rewrite -catA.
          unfold lfilled, lfill; fold lfill => /=.
          rewrite Hl. erewrite Hfillrec. by rewrite -catA.
          constructor. econstructor.
          intros ->. apply filled_trivial in Htrap as [_ ->]. done.
          exact Htrap.
        * apply separate_last_None in Hlast as ->.
          apply concat_cancel_last in Hfill as [-> ->].
          exfalso; eapply values_no_reduce.
          exact Hred. done.
  Qed. 

  
  Lemma br_no_reduce s f lh i es s' f' es' :
    lfilled 0 lh [AI_basic (BI_br i)] es ->
    reduce s f es s' f' es' -> False.
  Proof.
    cut (forall n, length_rec es < n -> lfilled 0 lh [AI_basic (BI_br i)] es ->
              reduce s f es s' f' es' -> False).
    { intro Hn ; apply (Hn (S (length_rec es))) ; lia. }
    intro n. generalize dependent es. generalize dependent lh. generalize dependent es'.
    induction n ; intros es' lh es Hlen Hfill Hred ; first by inversion Hlen.
    destruct lh => //.
    all: unfold lfilled, lfill in Hfill; fold lfill in Hfill.
    all: destruct (const_list l) eqn:Hl => //.
    2-3: destruct (lfill _ _ _) eqn:Hfill' => //.
    all: move/eqP in Hfill.
    all: induction Hred.
    1, 44, 87: destruct H.
    all: try by found_intruse (AI_basic (BI_br i)) Hfill Hxl1.
    all: try by rewrite - (app_nil_r [_]) in Hfill;
        apply first_values in Hfill as (? & ? & ?);
      try (subst; apply v_to_e_is_const_list).
    all: try by rewrite separate2 separate1 -app_assoc in Hfill;
      (try destruct ref);
      (try destruct v; try destruct v); apply first_values in Hfill as (? & ? & ?);
      try rewrite /= H.
    all: try by rewrite separate3 separate2 -app_assoc in Hfill;
      apply first_values in Hfill as (? & ? & ?).
    all: try by rewrite separate4 separate3 -app_assoc in Hfill;
      destruct v1, v2; (try destruct v); (try destruct v0);
      apply first_values in Hfill as (? & ? & ?).
    all: try by destruct l => //; destruct l => //.
    all: try by rewrite separate2 separate1 in Hfill;
        repeat rewrite -cat_app in Hfill;
        repeat rewrite catA in Hfill;
        rewrite -catA -(catA l) in Hfill;
        apply first_values in Hfill as (? & ? & ?);
      (try apply const_list_concat);
      try (subst; apply v_to_e_is_const_list).
    all: try (move/lfilledP in H0; inversion H0;
      remember Hfill as Hfillll; clear Hfill HeqHfillll;
      subst;
      apply first_values in Hfillll as (? & ? & ?); subst => //). 
    - destruct l; try by destruct l.
      inversion Hfill; subst.
      assert (lfilled 0 lh [AI_basic (BI_br i)] l2); first by rewrite /lfilled Hfill'.
      apply lfilled_const in H0 as [??] => //.
    - destruct l; try by destruct l.
      inversion Hfill; subst.
      destruct lh; simpl in Hfill'.
      all: destruct (const_list l) eqn:Hl' => //.
      2-3: destruct (lfill _ _ _) => //. 
      all: destruct l => //.
      all: inversion Hfill'; subst => //.
    - inversion H4; subst.
      edestruct lfilled_first_values as (? & ?).
      instantiate (3 := []).
      unfold lfilled. simpl. erewrite Hfill'. done.
      instantiate (2 := []).
      apply/lfilledP. simpl. exact H2.
      all: try done.
    - destruct l; try by destruct l.
      inversion Hfill; subst.
      assert (lfilled 0 lh [AI_basic (BI_br i)] l3); first by rewrite /lfilled Hfill'.
      apply lfilled_const in H0 as [??] => //.
    - destruct l; try by destruct l.
      inversion Hfill; subst.
      destruct lh; simpl in Hfill'.
      all: destruct (const_list l) eqn:Hl' => //.
      2-3: destruct (lfill _ _ _) => //. 
      all: destruct l => //.
      all: inversion Hfill'; subst => //.
    - inversion H4; subst.
      edestruct lfilled_first_values as (? & ?).
      instantiate (3 := []).
      unfold lfilled. simpl. erewrite Hfill'. done.
      instantiate (2 := []).
      apply/lfilledP. simpl. exact H2.
      all: try done.
    - subst. move/lfilledP in H; inversion H; subst.
      all: try by apply first_values in H1 as (? & ? & ?).
      apply const_list_snoc_eq3 in H1 as (vs' & es'' & -> & -> & -> & Hvs') => //.
      2:{ intros ->. empty_list_no_reduce. }
      2:{ destruct (const_list es) eqn:Hes => //.
          exfalso; eapply values_no_reduce => //. }
      2:{ intros ->. eapply AI_trap_irreducible => //. }
      specialize (IHHred IHn).
      destruct vs.
      + destruct es'0.
        * apply IHHred. 
          simpl in Hlen. rewrite app_nil_r in Hlen. done.
          simpl. rewrite app_nil_r. done.
        * eapply IHn.
          3: exact Hred.
          simpl in Hlen.
          rewrite length_app_rec /= separate1 length_app_rec length_app_rec in Hlen.
          rewrite length_app_rec length_app_rec.
          specialize (length_cons_rec a es'0) as Hres.
          lia.
          instantiate (1 := LH_base vs' es'').
          rewrite /lfilled /lfill /= Hvs' //.
      + eapply IHn.
        3: exact Hred.
        simpl in Hlen.
        specialize (length_cons_rec a ((vs ++ vs') ++ (AI_basic (BI_br i) :: (es'' ++ es'0)%list)%SEQ)%list) as Hres.
        remember ( length_rec (a :: ((vs ++ vs') ++ (AI_basic (BI_br i) :: (es'' ++ es'0)%list)%SEQ)%list)) as x.
        rewrite length_app_rec length_app_rec separate1 length_app_rec length_app_rec in Hres.
        rewrite length_app_rec length_app_rec. lia.
        instantiate (1 := LH_base vs' es'').
        rewrite /lfilled /lfill /= Hvs' //.
    - destruct l; try by destruct l.
      inversion Hfill; subst.
      apply hfilled_to_llfill in H as [llh Hllh].
      edestruct lfilled_llfill_first_values as [??].
      instantiate (3 := []). unfold lfilled.
      simpl.
      erewrite Hfill'. done.
      instantiate (2 := []). exact Hllh. all: try done.
    - destruct l; try by destruct l.
      inversion Hfill; subst.
      apply hfilled_to_llfill in H as [llh Hllh].
      edestruct lfilled_llfill_first_values as [??].
      instantiate (3 := []). unfold lfilled.
      simpl.
      erewrite Hfill'. done.
      instantiate (2 := []). exact Hllh. all: try done.
    - subst. move/lfilledP in H; inversion H; subst.
      all: try by apply first_values in H1 as (? & ? & ?).
      + apply const_list_snoc_eq3 in H1 as (vs' & es'' & -> & -> & -> & Hvs') => //.
        2:{ intros ->. empty_list_no_reduce. }
        2:{ destruct (const_list es) eqn:Hes => //.
            exfalso; eapply values_no_reduce => //. }
        2:{ intros ->. eapply AI_trap_irreducible => //. }
        specialize (IHHred IHn).
        destruct vs.
        * destruct es'0.
          -- apply IHHred. 
             simpl in Hlen. rewrite app_nil_r in Hlen. done.
             simpl. rewrite app_nil_r. done.
          -- eapply IHn.
             3: exact Hred.
             simpl in Hlen.
             rewrite length_app_rec /= separate1 length_app_rec length_app_rec in Hlen.
             rewrite length_app_rec length_app_rec.
             specialize (length_cons_rec a es'0) as Hres.
             lia.
             instantiate (1 := LH_handler vs' l0 lh es'').
             unfold lfilled, lfill; fold lfill.
             rewrite Hvs' Hfill'. done.
        * eapply IHn.
          3: exact Hred.
          simpl in Hlen.
          specialize (length_cons_rec a ((vs ++ vs')%list ++ AI_handler l0 l2 :: (es'' ++ es'0)%list)) as Hres.
          remember (length_rec (a :: (vs ++ vs')%list ++ AI_handler l0 l2 :: (es'' ++ es'0)%list)) as x.
          rewrite length_app_rec length_app_rec separate1 length_app_rec length_app_rec in Hres.
          rewrite length_app_rec length_app_rec. lia.
          instantiate (1 := LH_handler vs' l0 lh es'').
          unfold lfilled, lfill; fold lfill.
          rewrite Hvs' Hfill'. done.
      + apply first_values in H1 as (? & ? & ?) => //.
        inversion H3; subst.
        move/lfilledP in H0; inversion H0; subst.
        eapply IHn.
        3:{ eapply r_label. exact Hred.
            apply/lfilledP. exact H6.
            apply/lfilledP. exact H12. }
        repeat rewrite cat_app in Hlen.
        rewrite length_app_rec length_app_rec in Hlen.
        unfold length_rec in Hlen.
        simpl in Hlen.
        unfold length_rec. lia.
        rewrite /lfilled. erewrite Hfill'. done.
    - destruct l; try by destruct l.
      inversion Hfill; subst.
      apply hfilled_to_llfill in H2 as [llh Hllh].
      edestruct lfilled_llfill_first_values as [??].
      instantiate (3 := []). unfold lfilled.
      simpl.
      erewrite Hfill'. done.
      instantiate (2 := []). exact Hllh. all: try done.
    - destruct l; try by destruct l.
      inversion Hfill; subst.
      apply hfilled_to_llfill in H2 as [llh Hllh].
      edestruct lfilled_llfill_first_values as [??].
      instantiate (3 := []). unfold lfilled.
      simpl.
      erewrite Hfill'. done.
      instantiate (2 := []). exact Hllh. all: try done.
    - subst. move/lfilledP in H; inversion H; subst.
      all: try by apply first_values in H1 as (? & ? & ?).
      + apply const_list_snoc_eq3 in H1 as (vs' & es'' & -> & -> & -> & Hvs') => //.
        2:{ intros ->. empty_list_no_reduce. }
        2:{ destruct (const_list es) eqn:Hes => //.
            exfalso; eapply values_no_reduce => //. }
        2:{ intros ->. eapply AI_trap_irreducible => //. }
        specialize (IHHred IHn).
        destruct vs.
        * destruct es'0.
          -- apply IHHred. 
             simpl in Hlen. rewrite app_nil_r in Hlen. done.
             simpl. rewrite app_nil_r. done.
          -- eapply IHn.
             3: exact Hred.
             simpl in Hlen.
             rewrite length_app_rec /= separate1 length_app_rec length_app_rec in Hlen.
             rewrite length_app_rec length_app_rec.
             specialize (length_cons_rec a es'0) as Hres.
             lia.
             instantiate (1 := LH_prompt vs' l0 l1 lh es'').
             unfold lfilled, lfill; fold lfill.
             rewrite Hvs' Hfill'. done.
        * eapply IHn.
          3: exact Hred.
          simpl in Hlen.
          specialize (length_cons_rec a ((vs ++ vs')%list ++ AI_prompt l0 l1 l3 :: (es'' ++ es'0)%list)) as Hres.
          remember (length_rec (a :: (vs ++ vs')%list ++ AI_prompt l0 l1 l3 :: (es'' ++ es'0)%list)) as x.
          rewrite length_app_rec length_app_rec separate1 length_app_rec length_app_rec in Hres.
          rewrite length_app_rec length_app_rec. lia.
          instantiate (1 := LH_prompt vs' l0 l1 lh es'').
          unfold lfilled, lfill; fold lfill.
          rewrite Hvs' Hfill'. done.
      + apply first_values in H1 as (? & ? & ?) => //.
        inversion H3; subst.
        move/lfilledP in H0; inversion H0; subst.
        eapply IHn.
        3:{ eapply r_label. exact Hred.
            apply/lfilledP. exact H6.
            apply/lfilledP. exact H13. }
        repeat rewrite cat_app in Hlen.
        rewrite length_app_rec length_app_rec in Hlen.
        unfold length_rec in Hlen.
        simpl in Hlen.
        unfold length_rec. lia.
        rewrite /lfilled. erewrite Hfill'. done.
Qed. 

  Lemma lfilled_first_non_value s f es s' f' es' k lh les les':
    reduce s f es s' f' es' ->
    lfilled k lh es les ->
    lfilled k lh es' les' ->
    exists vs e esf es' k0 lh0,
      const_list vs /\
        (forall n es LI, e = AI_label n es LI ->
                    (s, f) = (s', f') /\
                      (const_list LI \/ LI = [AI_trap] \/
                         exists k lh vs i, lfilled k lh (vs ++ [AI_basic (BI_br i)]) LI)) /\
        (forall hs LI, e = AI_handler hs LI ->
                  f = f' /\
                      (s = s' /\ const_list LI \/
                         (s = s' /\ exists lh, lfilled 0 lh [AI_trap] LI) \/
                         exists i hh vs a, hfilled (Var_handler i) hh [AI_throw_ref_desugared vs a i] LI)) /\
            
        (forall tf hs LI, e = AI_prompt tf hs LI ->
                     f = f' /\ 
                      (s = s' /\ const_list LI \/
                         (s = s' /\ exists lh, lfilled 0 lh [AI_trap] LI) \/
                         (exists x hh vs, hfilled (Var_prompt_suspend x) hh [AI_suspend_desugared vs x] LI) \/
                         exists x hh vs k tf, hfilled (Var_prompt_switch x) hh [AI_switch_desugared vs k tf x] LI
                         )) /\
        (is_const e = false ) /\ 
        reduce s f (vs ++ e :: esf) s' f' es' /\
        lfilled k0 lh0 (vs ++ e :: esf) les /\
        lfilled k0 lh0 es' les'.
  Proof.
    intros Hred Hfill Hfill'.
    generalize dependent k ; generalize dependent lh.
    induction Hred. (*as [ | | | | |
                        ? ? ? ? ? ? ? ? ? ? k0
                      | | | | | | 
                        ? ? ? ? ? k0
                      |
                        ? ? ? ? k0
                      |
                        ? ? ? ? ? k0
                      |
                        ? ? ? ? ? k0
                      |
                        ? ? ? ? ? ? k0
                      |
                        ? ? ? ? ? ? k0
                      |
                        ? ? ? ? ? ? k0
                      |
                        ? ? ? ? ? ? k0
                      | | | |
                        ? ? ? ? ? ? ? ? k0 lh0 ? ? ? ? | ]; *)
    all: intros lh0 k0 Hfill Hfill'.
    destruct H.
   
    all: try by eexists [], _ , [], _ (* [_] *), k0, lh0;
      (repeat split => //=); (try done);
      (try by econstructor);
      econstructor; econstructor.
    all: try by eexists [_], _ , [], _ (* [_] *), k0, lh0;
      (repeat split => //=); (try destruct ref => //); (try done);
      (try by rewrite const_const); (try by rewrite H);
      econstructor; try econstructor.
    all: try by eexists [_; _], _ , [], _ (* [_] *), k0, lh0;
      (repeat split => //=); (try done);
      econstructor; try econstructor.
    all: try by eexists [_; _; _], _ , [], [_], k0, lh0;
      (repeat split => //=); (try done);
      (try by do 2 rewrite const_const); econstructor; try econstructor.
    all: try by eexists _, _ , [], _ (* [_] *), k0, lh0;
      (repeat split => //=); (try done);
      (try by subst; apply v_to_e_is_const_list);
      (try by econstructor);
      econstructor; econstructor.
    all: try by eexists [], _ , [], _, k0, lh0;
      (repeat (split ; [ try (intros ??? Heq + intros ?? Heq) |] => //=)); (try done);
      [ inversion Heq; subst; eauto;
        (try by right; left; split; try exists (LH_base [] []));
        (try by right; right; right; repeat eexists);
        (try by right; right; left; repeat eexists);
        try by right; right; repeat eexists
      |  econstructor; try econstructor].
    all: try by eexists (_ ++ [_]), _ , [], _, k0, lh0;
        split; last (split; last (split; last (split; last (split; last (split; last (split))))));
        (try exact Hfill');
        (try by rewrite -catA; exact Hfill);
        (try by rewrite -catA; econstructor);
      (try by apply const_list_concat; subst; try apply v_to_e_is_const_list).
    - move/lfilledP in H0; inversion H0; subst.
      + exists vs, AI_trap, es', [AI_trap], k0, lh0.
        repeat split => //=. constructor. econstructor => //.
        instantiate (1 := LH_base vs es').
        apply/lfilledP; constructor => //.
      + eexists bef, _, aft, [AI_trap], k0, lh0.
        repeat split => //=. all: try done.
        inversion H3; subst. right; left.
        split => //. eexists; by apply/lfilledP.
        constructor. econstructor => //.
        apply/lfilledP. instantiate (1 := LH_handler bef hs lh' aft).
        constructor => //.
      + eexists bef, _, aft, [AI_trap], k0, lh0.
        repeat split => //=. all: try done.
        inversion H3; subst. right; left.
        split => //. eexists; by apply/lfilledP. constructor. econstructor => //.
        apply/lfilledP. instantiate (1 := LH_prompt bef ts hs lh' aft).
        constructor => //.
    - eexists [], _ , [], _, k0, lh0;
        split; last (split; last (split; last (split; last (split; last (split; last (split)))))).
      all: (try exact Hfill').
      all: (try exact Hfill).
      all: (try by econstructor).
      repeat split => //=. inversion H3; subst.
      right; right; left. repeat eexists. exact H2. 
    - eexists [], _ , [], _, k0, lh0;
        split; last (split; last (split; last (split; last (split; last (split; last (split)))))).
      all: (try exact Hfill').
      all: (try exact Hfill).
      all: (try by econstructor).
      repeat split => //=. inversion H4; subst.
      right; right; right. repeat eexists. exact H2. 
    - edestruct lfilled_trans2 as (lh1 & Hfill1 & Hfill2).
      exact H. exact H0. exact Hfill. exact Hfill'.
      apply (IHHred lh1 (k + k0)) => //=. 
Qed.         

  Lemma reduce_return_trap_label es s' f' vs n es'0 es'' es' :
    reduce s' f' es s' f' es' ->
    const_list vs ->
    es = (vs ++ [AI_label n es'0 [AI_trap]] ++ es'') ->
    ∃ lh', lfilled 0 lh' [AI_trap] es'.
  Proof.
    intros Hred.
    revert vs es''. induction Hred;[|intros vs' es'' Hconst Heq..].
    induction H; intros vs' es'' Hconst Heq;subst.
    all: try (do 2 destruct vs' => //).
    all: try (do 3 destruct vs' => //).
    all: try by destruct v; try destruct v; do 3 destruct vs' => //. 
    all: try (by apply const_list_concat_inv in Heq as [? [? ?]];auto; subst; try apply v_to_e_is_const_list).
    all: try by rewrite cat_app separate2 separate1 app_assoc app_assoc -app_assoc in Heq;
      apply first_values in Heq as (? & ? & ?) => //; apply const_list_concat => //; subst; try apply v_to_e_is_const_list.
(*    rewrite - (app_nil_r [_]) in Heq. apply first_values in Heq as (? & ? & ?) => //. 
      subst; apply v_to_e_is_const_list. *)
    - destruct ref; do 3 destruct vs' => //.
    - destruct v1, v2; try destruct v; try destruct v0; do 5 destruct vs' => //.
    - destruct v1, v2; try destruct v; try destruct v0; do 5 destruct vs' => //.
    - destruct vs'; last by destruct vs'.
      inversion Heq; subst. done. 
    - destruct vs'; last by destruct vs'.
      inversion Heq; subst. exists (LH_base [] []). eauto.
    - destruct vs'; last by destruct vs'.
      inversion Heq; subst.
      move/lfilledP in H1; inversion H1; subst.
      1-2: destruct vs0 => //; last by destruct vs0, vs => //.
      destruct vs => //; last by destruct vs => //.
      all: destruct bef; last by destruct bef.
      all: done.
    - move/lfilledP in H0. inversion H0 => //.
      all: by apply first_values in H1 as (? & ? & ?).
    - subst. apply lfilled_one_depth_trap in H as Hk => //.
      destruct Hk as [-> | ->].
      + apply lfilled_Ind_Equivalent in H. inversion H;subst.
        2-3: apply first_values in H1 as (? & ? & ?) => //.
        apply const_list_snoc_eq3 in H1;auto.
        2: eapply reduce_not_nil;eauto.
        2:{ destruct (const_list es) eqn:Habs => //.
            exfalso ; eapply values_no_reduce => //. }
        2: intros -> ; eapply AI_trap_irreducible => //.
        destruct H1 as [vs2 [es2 [Heq1 [Heq2 [Heq3 Hconst2]]]]].
        subst.
        edestruct IHHred as [lh' Hlh'];eauto.
        apply lfilled_Ind_Equivalent in Hlh'.
        inversion Hlh';subst.
        all: apply lfilled_Ind_Equivalent in H0.
        all: inversion H0;subst.
        * exists (LH_base (vs ++ vs0) (es'2 ++ es'1)).
          unfold lfilled, lfill => //=.
          rewrite const_list_concat => //.
          repeat rewrite -cat_app.
          repeat rewrite catA. 
          repeat rewrite -catA. done.
        * exists (LH_handler (vs ++ bef) hs lh'0 (aft ++ es'1)).
          unfold lfilled, lfill; fold lfill.
          rewrite const_list_concat => //.
          move/lfilledP in H3. unfold lfilled in H3; destruct (lfill _ _ _) => //.
          move/eqP in H3. subst. repeat rewrite catA. done.
        * exists (LH_prompt (vs ++ bef) ts hs lh'0 (aft ++ es'1)).
          unfold lfilled, lfill; fold lfill.
          rewrite const_list_concat => //.
          move/lfilledP in H3. unfold lfilled in H3; destruct (lfill _ _ _) => //.
          move/eqP in H3. subst. repeat rewrite catA. done.
      + apply lfilled_Ind_Equivalent in H.
        inversion H;subst.
        2-3: apply first_values in H1 as (? & ? & ?) => //. 
        apply first_values in H2 as [Heq1 [Heq2 Heq3]];auto.
        simplify_eq. apply lfilled_Ind_Equivalent in H6.
        apply filled_singleton in H6 as [? [? ?]].
        all: try by eapply reduce_not_nil;eauto.
        all: try done.
        subst.
        apply val_head_stuck_reduce in Hred.
        done. 
Qed.  


  Lemma reduce_focus_one es1 s f s' f' vs n es'0 LI es'' es' :
    reduce s f es1 s' f' es' ->
    es1 = (vs ++ [AI_label n es'0 LI] ++ es'') ->
    const_list vs ->
    iris.to_val LI = None ->
    (∀ i j lh vs0, const_list vs0 -> lfilled i lh (vs0 ++ [AI_basic (BI_br j)]) LI -> False) ->
    ∃ LI', reduce s f LI s' f' LI'.
  Proof.
    intros Hred.
    revert vs n es'0 LI es''.
    induction Hred;intros vs' n' es'0 LI'' es'' Heq Hconst HLI Hnbr.
    induction H;subst.
    all: try (subst; do 2 destruct vs' => //).
    all: try (subst; do 3 destruct vs' => //).
    all: try by destruct v; try destruct v; do 3 destruct vs' => //. 
    all: try by apply const_list_concat_inv in Heq as [? [? ?]];auto; subst; try apply v_to_e_is_const_list.
    all: try by rewrite cat_app separate2 separate1 app_assoc app_assoc -app_assoc in Heq;
      apply first_values in Heq as (? & ? & ?) => //; apply const_list_concat => //; subst; try apply v_to_e_is_const_list.
    - destruct ref; do 3 destruct vs' => //.
    - destruct v1, v2; try destruct v; try destruct v0; do 5 destruct vs' => //.
    - destruct v1, v2; try destruct v; try destruct v0; do 5 destruct vs' => //.
    - destruct vs'; last by destruct vs'.
      inversion Heq; subst. apply const_list_to_val in H as (vs & HLI' & _).
      rewrite HLI' in HLI => //.
    - destruct vs'; last by destruct vs'.
      inversion Heq; subst. done. 
    - destruct vs'; last by destruct vs'.
      inversion Heq; subst.
      apply const_es_exists in H as [vs' ->].
      apply lh_pull_const_r_app in H1 as [lh' Hlh'].
      eapply lfilled_to_vfill in Hlh' as (vh & Hlh & Hfill).
      2: instantiate (1 := i); lia.
      fold (of_val (brV vh)) in Hfill.
      apply (f_equal to_val) in Hfill.
      unfold to_val in Hfill. rewrite to_of_val in Hfill.
      rewrite HLI in Hfill => //.
    - move/lfilledP in H0. inversion H0; subst.
      all: apply first_values in H1 as (? & ? & ?) => //.
    - subst.
      apply reduce_not_nil in Hred as Hnil.
      apply val_head_stuck_reduce in Hred as Hnval.
      apply lfilled_Ind_Equivalent in H.
      inversion H;subst.
      3-4: try by apply first_values in H1 as (? & ? & ?).
      + apply const_list_snoc_eq3 in H1 as [? [? [? [? [? ?]]]]];auto;subst.
        eapply IHHred;eauto.
        destruct (const_list es) eqn:Habs => //.
        exfalso ; by eapply values_no_reduce.
        by intros -> ; eapply AI_trap_irreducible. 
      + apply first_values in H1 as [? [? ?]];auto. simplify_eq.
        apply lfilled_Ind_Equivalent in H6.
        apply lfilled_swap with (es':=es') in H6 as Hfill'.
        destruct Hfill' as [LI' Hfill'].
        exists LI'. eapply r_label;eauto.
Qed. 

  Lemma trap_reduce_state_eq i lh es s f s' f' es' :
    reduce s f es s' f' es' ->
    lfilled i lh [AI_trap] es -> 
    (s,f) = (s',f').
  Proof.
    intros Hred. 
    revert i lh.
    induction Hred;auto.
    all: intros j lhh Hfill%lfilled_Ind_Equivalent.
    1-12,14: inversion Hfill as [ bef l' aft Hbef Hj Hllh Htrap Heq | j' bef n' es'' lh' aft ? ? Hbef Hrec Hj Hllh Htrap Heq | bef hs' lh' aft ? ? ? Hbef Hrec Hj Hllh Htrap Heq | bef ts' hs' lh' aft ? ? ? Hbef Hrec Hj Hllh Htrap Heq].
    all: subst.
    all: try by rewrite - (app_nil_r [_]) in Heq;
      apply first_values in Heq as (? & ? & ?);
      try apply v_to_e_is_const_list.
    all: try by symmetry in Heq; rewrite separate2 separate1 -app_assoc in Heq;
      apply first_values in Heq as (? & ? & ?);
      try by (destruct v ; try destruct v).
     all: try by symmetry in Heq; rewrite separate3 separate2 -app_assoc in Heq;
       apply first_values in Heq as (? & ? & ?);
      try by (destruct v ; try destruct v).
    all: try by symmetry in Heq; rewrite separate2 separate1 in Heq;
      repeat rewrite cat_app in Heq;
      repeat rewrite app_assoc in Heq;
      rewrite -app_assoc in Heq;
      apply first_values in Heq as (? & ? & ?) => //;
                                                   apply const_list_concat; subst; try apply v_to_e_is_const_list.
    all: try by destruct bef; try destruct bef.
    - destruct bef; last by destruct bef.
      inversion Heq; subst.
      move/lfilledP in Hrec.
      apply hfilled_to_llfill in H2 as [llh Hllh].
      edestruct lfilled_llfill_first_values as [??].
      instantiate (3 := []). exact Hrec.
      instantiate (2 := []). exact Hllh.
      all: done.
    - destruct bef; last by destruct bef.
      inversion Heq; subst.
      move/lfilledP in Hrec.
      apply hfilled_to_llfill in H2 as [llh Hllh].
      edestruct lfilled_llfill_first_values as [??].
      instantiate (3 := []). exact Hrec.
      instantiate (2 := []). exact Hllh.
      all: done.
    - move/lfilledP in Hfill.
      eapply lfilled_singleton in Hfill as (? & ? & ? & ?);[..|apply H];auto.
      eapply IHHred. apply H1.
      eapply reduce_not_nil;eauto.
      destruct (const_list es) eqn:Habs => //.
      exfalso ; eapply values_no_reduce => //.
      intros -> ; eapply AI_trap_irreducible => //.
Qed. 


  Lemma trap_reduce_lfilled i lh es s f s' f' es' :
    reduce s f es s' f' es' ->
    lfilled i lh [AI_trap] es -> 
    exists lh' j, lfilled j lh' [AI_trap] es' ∧ j <= i.
  Proof.
    intros Hred. 
    revert i lh.
    induction Hred;auto.
    inversion H.
    all: intros j' lhh Hfill%lfilled_Ind_Equivalent.
    1-83,85: inversion Hfill as [ bef l' aft Hbef Hj Hllh Htrap Heq | j'' bef n' es'' lh' aft ? ? Hbef Hrec Hj Hllh Htrap Heq | bef hs' lh' aft ? ? ? Hbef Hrec Hj Hllh Htrap Heq | bef ts' hs' lh' aft ? ? ? Hbef Hrec Hj Hllh Htrap Heq].
    all: subst.
    all: try by rewrite - (app_nil_r [_]) in Heq;
      apply first_values in Heq as (? & ? & ?);
      try apply v_to_e_is_const_list.
    all: try by symmetry in Heq; rewrite separate2 separate1 -app_assoc in Heq;
      apply first_values in Heq as (? & ? & ?);
      try by (destruct v ; try destruct v); try by rewrite /= H0.
    all: try by symmetry in Heq; rewrite separate3 separate2 -app_assoc in Heq;
       apply first_values in Heq as (? & ? & ?);
      try by (destruct v ; try destruct v).
    all: try by symmetry in Heq; rewrite separate4 separate3 -app_assoc in Heq;
       apply first_values in Heq as (? & ? & ?);
      try by (destruct v1, v2 ; try destruct v; try destruct v0).
    all: try by symmetry in Heq; rewrite separate2 separate1 in Heq;
      repeat rewrite cat_app in Heq;
      repeat rewrite app_assoc in Heq;
      rewrite -app_assoc in Heq;
      apply first_values in Heq as (? & ? & ?) => //;
                                                   apply const_list_concat; subst; try apply v_to_e_is_const_list.
    all: try by destruct bef; try destruct bef.
    all: try by destruct ref; do 3 (destruct bef => //).
    all: try (destruct bef; last (by destruct bef); inversion Heq; subst).
    all: try by move/lfilledP in Hrec; apply lfilled_const in Hrec as [??]. 
    all: try by exists (LH_base [] []), 0; split; [eauto | lia].
    - move/lfilledP in Hrec.
      edestruct lfilled_first_values as [??].
      exact H2. instantiate (2 := []). exact Hrec. all: done.
    - move/lfilledP in Hrec.
      apply hfilled_to_llfill in H as [llh Hllh].
      edestruct lfilled_llfill_first_values as [??].
      instantiate (3 := []). exact Hrec.
      instantiate (2 := []). exact Hllh. all: done.
    - move/lfilledP in Hrec.
      apply hfilled_to_llfill in H as [llh Hllh].
      edestruct lfilled_llfill_first_values as [??].
      instantiate (3 := []). exact Hrec.
      instantiate (2 := []). exact Hllh. all: done.
    - move/lfilledP in Hrec.
      apply hfilled_to_llfill in H2 as [llh Hllh].
      edestruct lfilled_llfill_first_values as [??].
      instantiate (3 := []). exact Hrec.
      instantiate (2 := []). exact Hllh. all: done.
    - move/lfilledP in Hrec.
      apply hfilled_to_llfill in H2 as [llh Hllh].
      edestruct lfilled_llfill_first_values as [??].
      instantiate (3 := []). exact Hrec.
      instantiate (2 := []). exact Hllh. all: done.
    - move/lfilledP in Hfill.
      eapply lfilled_singleton in Hfill as (? & ? & ? & ?);[..|apply H];auto.
      eapply IHHred in H1 as (lh' & j & Hfill & Hj).
      edestruct lfilled_trans as [lhn Hfilln].
      exact Hfill. exact H0.
      exists lhn, (j + k).
      split => //. lia.
      eapply reduce_not_nil;eauto.
      destruct (const_list es) eqn:Habs => //.
      exfalso ; eapply values_no_reduce => //.
      intros -> ; eapply AI_trap_irreducible => //.
Qed. 

    
  Lemma trap_reduce_nested s f es s' f' es' lh i :
    lfilled i lh [AI_trap] es -> reduce s f es s' f' es' ->
    (exists lh' j, lfilled j lh' [AI_trap] es' ∧ j <= i) ∧ (s,f) = (s',f').
  Proof.
    intros Hfill Hred.
    eapply trap_reduce_state_eq in Hred as Heq;eauto.
    eapply trap_reduce_lfilled in Hred as Hf;eauto.
  Qed.

  Lemma trap_context_reduce locs s LI lh k :
    lfilled (S k) lh [AI_trap] LI ->
    ∃ e', reduce locs s LI locs s e'.
  Proof.
    revert LI k.
    induction lh;intros LI k Hfill%lfilled_Ind_Equivalent.
    all: inversion Hfill; simplify_eq.
    - induction k.
      + destruct lh.
        all: inversion H8; simplify_eq.
        * destruct (decide (l2 ++ [AI_trap] ++ l3 = [AI_trap])).
          -- destruct l2, l3 => //.
             2: destruct l2 => //.
             2: destruct l2, l3 => //.
             erewrite app_nil_l, app_nil_r.
             exists (l ++ [AI_trap] ++ l1).
             eapply r_label.
             2: instantiate (3:=0).
             2,3: apply lfilled_Ind_Equivalent;constructor;auto.
             apply r_simple. apply rs_label_trap. 
          -- exists (l ++ [AI_label n l0 ([AI_trap])] ++ l1).
             eapply r_label.
             2: instantiate (3:=1).
             2: instantiate (2 := LH_rec l n l0 (LH_base [] []) l1).
             2,3: apply lfilled_Ind_Equivalent;constructor 2;auto.
             2,3: apply lfilled_Ind_Equivalent.
             2,3: cbn;rewrite app_nil_r; by apply/eqseqP.
             apply r_simple. eapply rs_trap. auto.
             apply lfilled_Ind_Equivalent.
             instantiate (1 := LH_base l2 l3). constructor => //.
        * exists (l ++ [AI_label n l0 [AI_trap]] ++ l1).
          eapply r_label.
          2: instantiate (3 := 1).
          2: instantiate (2 := LH_rec l n l0 (LH_base [] []) l1).
          2,3: apply/lfilledP; constructor => //.
          2,3: apply/lfilledP; cbn; rewrite app_nil_r; apply/eqseqP => //.
          apply r_simple. eapply rs_trap. destruct l2 => //. destruct l2 => //.
          apply/lfilledP. instantiate (1 := LH_handler l2 l3 lh l4).
          constructor => //. 
        * exists (l ++ [AI_label n l0 [AI_trap]] ++ l1).
          eapply r_label.
          2: instantiate (3 := 1).
          2: instantiate (2 := LH_rec l n l0 (LH_base [] []) l1).
          2,3: apply/lfilledP; constructor => //.
          2,3: apply/lfilledP; cbn; rewrite app_nil_r; apply/eqseqP => //.
          apply r_simple. eapply rs_trap. destruct l2 => //. destruct l2 => //.
          apply/lfilledP. instantiate (1 := LH_prompt l2 l3 l4 lh l5).
          constructor => //. 
      + move/lfilledP in H8. apply IHlh in H8 as [e' He'].
        eexists.
        eapply r_label;[eauto|..].
        instantiate (2:= 1).
        instantiate (1 := LH_rec l n l0 (LH_base [] []) l1).
        all: apply lfilled_Ind_Equivalent;constructor;auto.
        all: apply lfilled_Ind_Equivalent.
        all: cbn;rewrite app_nil_r;by apply/eqseqP.
    - move/lfilledP in H7. apply IHlh in H7 as [e' He'].
      eexists.
      eapply r_label;[eauto|..].
      instantiate (2:= 0).
      instantiate (1 := LH_handler l l0 (LH_base [] []) l1).
      all: apply lfilled_Ind_Equivalent;constructor;auto.
      all: apply lfilled_Ind_Equivalent.
      all: cbn;rewrite app_nil_r;by apply/eqseqP.
    - move/lfilledP in H8. apply IHlh in H8 as [e' He'].
      eexists.
      eapply r_label;[eauto|..].
      instantiate (2:= 0).
      instantiate (1 := LH_prompt l l0 l1 (LH_base [] []) l2).
      all: apply lfilled_Ind_Equivalent;constructor;auto.
      all: apply lfilled_Ind_Equivalent.
      all: cbn;rewrite app_nil_r;by apply/eqseqP.
Qed.        

  Lemma to_val_trapV_lfilled_None es k lh LI :
    iris.to_val es = Some trapV ->
    lfilled (S k) lh es LI ->
    iris.to_val LI = None.
  Proof.
    intros Hes Hfill.
    apply to_val_trap_is_singleton in Hes as ->.
    eapply trap_context_reduce in Hfill as [e' Hred].
    eapply val_head_stuck_reduce;eauto.
    Unshelve.
    
    apply (Build_store_record [] [] [] [] [] [] []).
    apply (Build_frame [] (Build_instance [] [] [] [] [] [])).
  Qed.

  Lemma lfilled_to_val_0 i lh e es v :
    iris.to_val e = Some trapV ->
    lfilled i lh e es ->
    iris.to_val es = Some v ->
    i = 0.
  Proof.
    intros He Hfill Hes.
    destruct i;auto.
    exfalso.
    apply to_val_trapV_lfilled_None in Hfill;auto.
    unfold to_val in Hfill.
    congruence.
  Qed.

  Lemma reduce_det_local ws f ws' f' es1 es2 n f0 :
    iris.to_val es1 = None ->
    opsem.reduce ws f [AI_local n f0 es1] ws' f' es2 ->
    ∃ es2' f1, es2 = [AI_local n f1 es2'] ∧ f = f' ∧
                 opsem.reduce ws f0 es1 ws' f1 es2'.
  Proof.
    intros Hes1.
    remember [AI_local n f0 es1] as es.
    revert es2. induction 1;simplify_eq.
    inversion H; subst.
    all: try done.
    all: try do 2 destruct vcs => //.
    all: try do 2 destruct vs => //.
    - apply const_list_to_val in H4 as (? & ? & ?). congruence.
    - apply const_es_exists in H3 as [? ->].
      apply lfilled_to_sfill in H6 as [sh Hsh].
      rewrite -sfill_sh_pull_const_r in Hsh.
      rewrite Hsh in Hes1.
      fold (of_val (retV (sh_pull_const_r sh x))) in Hes1.
      rewrite to_of_val in Hes1. done.
    - move/lfilledP in H1.  inversion H1; subst.
      destruct vs => //. destruct vs => //.
      all: destruct bef => //. all: destruct bef => //.
    - move/lfilledP in H0; inversion H0; simplify_eq.
      2: by destruct vs; try destruct vs.
      2-3: by destruct bef; try destruct bef.
      rewrite - (app_nil_l [AI_local n f0 es1]) in H2.
      apply val_head_stuck_reduce in H as Hstuck.
      apply const_list_snoc_eq3 in H2 as (vs2 & es2 & Hnil & -> & Hnil' & Hvs2).
      destruct vs, vs2, es2, es'0 => //.
      all: try done.
      2, 4: intros ->; done.
      2: by destruct (const_list es) eqn:Habs => //; exfalso; eapply values_no_reduce.
      move/lfilledP in H1; simplify_eq.
      inversion H1; simplify_eq. rewrite cats0 cat0s.
      apply IHreduce. done.
    - eauto.
  Qed.

  Lemma reduce_det_label ws f ws' f' es1 n es es'' es2 :
    opsem.reduce ws f es'' ws' f' es2 ->
    ∀ l1 l2, es'' = (l1 ++ [AI_label n es es1] ++ l2) ->
    const_list l1 ->
    iris.to_val es1 = None ->
    ∃ es2', es2 = l1 ++ [AI_label n es es2'] ++ l2 ∧
              opsem.reduce ws f es1 ws' f' es2'.
  Proof.
    revert es2. induction 1.
    destruct H. 
    all:intros l1 l2 Heqes'' Hconst Hes1; simplify_eq.
    all: try destruct ref.
    all: try by do 2 destruct l1 => //.
    all: try by try (destruct v; try destruct v); do 3 destruct l1 => //.
    all: try by do 4 destruct l1 => //.
    all: try by try (destruct v1, v2; try destruct v; try destruct v0); do 5 destruct l1 => //.
    all: try by rewrite - (app_nil_r [_]) in Heqes''; apply first_values in Heqes'' as (? & ? & ?); subst; try apply v_to_e_is_const_list.
    all: try by repeat rewrite cat_app in Heqes''; rewrite separate2 separate1 app_assoc app_assoc - app_assoc in Heqes''; apply first_values in Heqes'' as (? & ? & ?); try apply const_list_concat; subst; try apply v_to_e_is_const_list => //.
    all: try (destruct l1; last (by destruct l1); inversion Heqes''; subst).
    - apply const_list_to_val in H as (? & ? & ?); congruence.
    - done.
    - apply const_es_exists in H as [? ->].
      apply lh_pull_const_r_app in H1 as [lh' Hlh'].
      apply lfilled_to_vfill with (i:=i) in Hlh' as (vh' & Heq & Hvh); last lia.
      rewrite -Hvh in Hes1. fold (of_val (brV vh')) in Hes1.
      rewrite to_of_val in Hes1 => //.
    - move/lfilledP in H0. inversion H0; subst.
      all: apply first_values in H1 as (?&?&?) => //.
    - move/lfilledP in H0; inversion H0; subst.
      2-4: apply first_values in H2 as (? & Hres & ?) => //; inversion Hres; subst.
      + apply val_head_stuck_reduce in H as Hstuck.
        apply const_list_snoc_eq3 in H2; eauto.
        2,4: by intros ->.
        2: by destruct (const_list es0) eqn:Habs => //; exfalso; eapply values_no_reduce.
        destruct H2 as (vs2 & es2 & Heq1 & Heq2 & Heq3 & Hcons').
        apply IHreduce in Heq2; eauto.
        simplify_eq.
        move/lfilledP in H1. inversion H1. simplify_eq.
        destruct Heq2 as (es2' & -> & Hstep).
        repeat erewrite <- app_assoc;erewrite app_assoc.
        eexists. split;eauto. 
      + move/lfilledP in H1. inversion H1. eexists. split;eauto.
        move/lfilledP in H7.
        move/lfilledP in H13.
        eapply r_label;eauto. 
  Qed.

  Lemma reduce_det_label_nil ws f ws' f' es1 es2 n es :
    iris.to_val es1 = None ->
    opsem.reduce ws f [AI_label n es es1] ws' f' es2 ->
    ∃ es2', es2 = [AI_label n es es2'] ∧
              opsem.reduce ws f es1 ws' f' es2'.
  Proof.
    intros Hes1.
    remember [AI_label n es es1] as es''.
    erewrite <-(app_nil_l [_]),<-(app_nil_r [_]) in Heqes''.
    intros Hred.
    eapply reduce_det_label in Heqes'';eauto.
  Qed.

(*
  Lemma reduce_det_prompt ws f ws' f' es1 n es es'' es2 :
    opsem.reduce ws f es'' ws' f' es2 ->
    ∀ l1 l2, es'' = (l1 ++ [AI_prompt n es es1] ++ l2) ->
    const_list l1 ->
    iris.to_val es1 = None ->
    ∃ es2', es2 = l1 ++ [AI_prompt n es es2'] ++ l2 ∧
              opsem.reduce ws f es1 ws' f' es2'.
  Proof.
    revert es2. induction 1.
    destruct H. 
    all:intros l1 l2 Heqes'' Hconst Hes1; simplify_eq.
    all: try destruct ref.
    all: try by do 2 destruct l1 => //.
    all: try by try (destruct v; try destruct v); do 3 destruct l1 => //.
    all: try by do 4 destruct l1 => //.
    all: try by try (destruct v1, v2; try destruct v; try destruct v0); do 5 destruct l1 => //.
    all: try by rewrite - (app_nil_r [_]) in Heqes''; apply first_values in Heqes'' as (? & ? & ?); subst; try apply v_to_e_is_const_list.
    all: try by repeat rewrite cat_app in Heqes''; rewrite separate2 separate1 app_assoc app_assoc - app_assoc in Heqes''; apply first_values in Heqes'' as (? & ? & ?); try apply const_list_concat; subst; try apply v_to_e_is_const_list => //.
    all: try (destruct l1; last (by destruct l1); inversion Heqes''; subst).
    - apply const_list_to_val in H as (? & ? & ?); congruence.
    - done.
    - move/lfilledP in H0. inversion H0; subst.
      all: apply first_values in H1 as (?&?&?) => //.

    - apply const_es_exists in H as [? ->].
      apply lh_pull_const_r_app in H1 as [lh' Hlh'].
      apply lfilled_to_vfill with (i:=i) in Hlh' as (vh' & Heq & Hvh); last lia.
      rewrite -Hvh in Hes1. fold (of_val (brV vh')) in Hes1.
      rewrite to_of_val in Hes1 => //.
    - move/lfilledP in H0; inversion H0; subst.
      2-4: apply first_values in H2 as (? & Hres & ?) => //; inversion Hres; subst.
      + apply val_head_stuck_reduce in H as Hstuck.
        apply const_list_snoc_eq3 in H2; eauto.
        2,4: by intros ->.
        2: by destruct (const_list es0) eqn:Habs => //; exfalso; eapply values_no_reduce.
        destruct H2 as (vs2 & es2 & Heq1 & Heq2 & Heq3 & Hcons').
        apply IHreduce in Heq2; eauto.
        simplify_eq.
        move/lfilledP in H1. inversion H1. simplify_eq.
        destruct Heq2 as (es2' & -> & Hstep).
        repeat erewrite <- app_assoc;erewrite app_assoc.
        eexists. split;eauto. 
      + move/lfilledP in H1. inversion H1. eexists. split;eauto.
        move/lfilledP in H7.
        move/lfilledP in H13.
        eapply r_label;eauto. 
  Qed. *)

  Lemma r_label_trans s f es s' f' es' k lh LI LI' :
    reduce_trans (s, f, es) (s', f', es') ->
    lfilled k lh es LI ->
    lfilled k lh es' LI' ->
    reduce_trans (s, f, LI) (s', f', LI').
  Proof.
    intros Hred HLI HLI'.
    remember (s, f, es) as y.
    remember (s', f', es') as y'.
    generalize dependent es. generalize dependent s.
    generalize dependent f. generalize dependent es'.
    generalize dependent s'. generalize dependent f'.
    generalize dependent LI. generalize dependent LI'.
    induction Hred; intros; subst.
    - constructor.
      eapply r_label.
      exact H. exact HLI. exact HLI'.
    - inversion Heqy; subst.
      eapply lfilled_inj in HLI'; try exact HLI.
      subst.
      by constructor.
    - destruct y as [[??]?].
      edestruct lfilled_swap as [LI'' HLI''].
      exact HLI.
      econstructor 3.
      + instantiate (1 := (_,_,_)).
        eapply IHHred1.
        done.
        exact HLI''.
        done.
        exact HLI.
      + eapply IHHred2.
        done.
        exact HLI'.
        done.
        exact HLI''.
  Qed. 
      
  
  Lemma lfilled_trap_reduce s f es k lh:
    lfilled k lh [AI_trap] es ->
    reduce_trans (s, f, es) (s, f, [AI_trap]).
  Proof.
    intros H.
    destruct (lfilled k lh [AI_trap] es) eqn:H' => //. 
    apply lfilled_Ind_Equivalent in H'.
    remember [AI_trap] as trap.
    induction H'; subst.
    - destruct (seq.cat vs es') eqn:Hvses'.
      + destruct vs, es' => //. simpl.
        constructor 2. 
      + constructor. constructor. econstructor.
        * destruct vs => //. destruct es' => //. destruct vs => //.
        * instantiate (1 := LH_base vs es').
          rewrite /lfilled /lfill /= H0 //.
    - econstructor 3.
      + eapply r_label_trans.
        by apply IHH'.
        instantiate (1 := LH_rec vs n es' (LH_base [] []) es'').
        instantiate (1 := 1).
        rewrite /lfilled /lfill /= H0 app_nil_r //.
        rewrite /lfilled /lfill /= H0. done.
      + destruct (vs ++ es'') eqn:Hvses''.
        * destruct vs, es'' => //.
          constructor.
          constructor. apply rs_label_trap.
        * econstructor 3.
          -- constructor.
             instantiate (1 := (_,_,_)).
             eapply r_label.
             2: instantiate (2 := LH_base vs es'').
             2: instantiate (2 := 0).
             2: instantiate (1 := [_]).
             2: rewrite /lfilled /lfill /= H0 //.
             constructor. apply rs_label_trap.
             rewrite /lfilled /lfill /= H0 //.
          -- constructor.
             constructor.
             econstructor.
             destruct vs => //. destruct es'' => //. destruct vs => //.
             instantiate (1 := LH_base vs es'').
             rewrite /lfilled /lfill /= H0 //.
    - econstructor 3.
      + eapply r_label_trans.
        by apply IHH'.
        instantiate (1 := LH_handler bef hs (LH_base [] []) aft).
        instantiate (1 := 0).
        rewrite /lfilled /lfill /= H0 app_nil_r //.
        rewrite /lfilled /lfill /= H0. done.
      + destruct (bef ++ aft) eqn:Hvses''.
        * destruct bef, aft => //.
          constructor.
          constructor. apply rs_handler_trap.
        * econstructor 3.
          -- constructor.
             instantiate (1 := (_,_,_)).
             eapply r_label.
             2: instantiate (2 := LH_base bef aft).
             2: instantiate (2 := 0).
             2: instantiate (1 := [_]).
             2: rewrite /lfilled /lfill /= H0 //.
             constructor. apply rs_handler_trap.
             rewrite /lfilled /lfill /= H0 //.
          -- constructor.
             constructor.
             econstructor.
             destruct bef => //. destruct aft => //. destruct bef => //.
             instantiate (1 := LH_base bef aft).
             rewrite /lfilled /lfill /= H0 //.
    - econstructor 3.
      + eapply r_label_trans.
        by apply IHH'.
        instantiate (1 := LH_prompt bef ts hs (LH_base [] []) aft).
        instantiate (1 := 0).
        rewrite /lfilled /lfill /= H0 app_nil_r //.
        rewrite /lfilled /lfill /= H0. done.
      + destruct (bef ++ aft) eqn:Hvses''.
        * destruct bef, aft => //.
          constructor.
          constructor. apply rs_prompt_trap.
        * econstructor 3.
          -- constructor.
             instantiate (1 := (_,_,_)).
             eapply r_label.
             2: instantiate (2 := LH_base bef aft).
             2: instantiate (2 := 0).
             2: instantiate (1 := [_]).
             2: rewrite /lfilled /lfill /= H0 //.
             constructor. apply rs_prompt_trap.
             rewrite /lfilled /lfill /= H0 //.
          -- constructor.
             constructor.
             econstructor.
             destruct bef => //. destruct aft => //. destruct bef => //.
             instantiate (1 := LH_base bef aft).
             rewrite /lfilled /lfill /= H0 //.
  Qed. 
             
      

  
End reduce_properties_lemmas.
