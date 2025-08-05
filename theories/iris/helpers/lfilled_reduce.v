From mathcomp Require Import ssreflect eqtype seq ssrbool.
From stdpp Require Import base list.
From Wasm Require Export stdpp_aux.
Require Export iris_reduction_core.

Set Bullet Behavior "Strict Subproofs".

(*
Ltac filled0 Hfill i lh :=
  let bef := fresh "bef" in
  let aft := fresh "aft" in
  let nn := fresh "nn" in
  let ll := fresh "ll" in
  let ll' := fresh "ll" in
  left ; simple_filled Hfill i lh bef aft nn ll ll' ;
  apply Logic.eq_sym, app_eq_unit in Hfill as [[ -> Hfill ] | [ _ Hfill ]] ;
  [ apply app_eq_unit in Hfill as [[ -> _ ] | [ -> -> ]] ;
    [ by empty_list_no_reduce
      | eexists ; repeat split ; (try done) ;
        [ 
        | unfold lfilled, lfill => //= ; try by rewrite app_nil_r 
        ]
    ]
  |
    apply app_eq_nil in Hfill as [-> ->]; 
      by empty_list_no_reduce ].

Ltac filled1 Hfill i lh Hes1 es1 :=
  let a := fresh "a" in
  let a0 := fresh "a" in
  let Ha := fresh "Ha" in
  let Ha0 := fresh "Ha" in
  let Hnil := fresh "Hnil" in
  let es := fresh "es" in
  let Heqes := fresh "Heqes" in
  let bef := fresh "bef" in
  let aft := fresh "aft" in
  let nn := fresh "nn" in
  let ll := fresh "ll" in
  let ll' := fresh "ll" in
  left ; simple_filled Hfill i lh bef aft nn ll ll' ;
  destruct bef as [| a bef];
  [ destruct es1 as [| a es1]; first (by empty_list_no_reduce) ;
    destruct es1 as [ | a0 es1] ;
    first (by inversion Hfill ; subst ; exfalso ; values_no_reduce) ;
    inversion Hfill as [[ Ha Ha0 Hnil ]] ;
    apply Logic.eq_sym in Hnil ;
    apply app_eq_nil in Hnil as [-> ->] ;
    eexists ; 
    repeat split ; (simpl ; try done) ;
    [ 
    | unfold lfilled, lfill => //= ; try by rewrite app_nil_r 
    ]
  | destruct bef as [|a0 bef];
    [ destruct es1 as [| a0 es1] ; first (by empty_list_no_reduce) ;
      inversion Hfill as [[ Ha Ha0 Hnil ]] ;
      apply Logic.eq_sym, app_eq_nil in Hnil as [-> ->] ;
      remember [a0] as es eqn:Heqes ;
      rewrite - Ha0 in Heqes ;
      apply Logic.eq_sym in Heqes ; 
      exfalso ;  no_reduce Heqes Hes1
    | inversion Hfill as [[ Ha Ha0 Hnil ]];
      apply Logic.eq_sym, app_eq_nil in Hnil as [-> Hnil] ;
      apply app_eq_nil in Hnil as [-> ->] ;
        by empty_list_no_reduce ]].

Ltac filled2 Hfill i lh Hes1 es1 :=
  let a := fresh "a" in
  let a0 := fresh "a" in
  let a1 := fresh "a" in
  let Ha := fresh "Ha" in
  let Ha0 := fresh "Ha" in
  let Ha1 := fresh "Ha" in
  let Hnil := fresh "Hnil" in
  let es := fresh "es" in
  let Heqes := fresh "Heqes" in
  let bef := fresh "bef" in
  let aft := fresh "aft" in
  let nn := fresh "nn" in
  let ll := fresh "ll" in
  let ll' := fresh "ll'" in
  left ; simple_filled Hfill i lh bef aft nn ll ll' ;
  destruct bef as [| a bef];
  [ destruct es1 as [| a es1] ; first (by empty_list_no_reduce ) ;
    destruct es1 as [| a0 es1] ;
    first (by inversion Hfill ; subst ; exfalso ; values_no_reduce ) ;
    destruct es1 as [| a1 es1];
    first (by inversion Hfill ; subst ; exfalso ; values_no_reduce ) ;
    inversion Hfill as [[ Ha Ha0 Ha1 Hnil]] ;
    apply Logic.eq_sym, app_eq_nil in Hnil as [-> ->] ;
    eexists ; 
    repeat split ; (simpl ; try done) ;
    [ 
    | unfold lfilled, lfill => //= ; try by rewrite app_nil_r 
    ]
  | destruct bef as [| a0 bef] ;
    [ destruct es1 as [| a0 es1] ; first (by empty_list_no_reduce ) ;
      destruct es1 as [| a1 es1] ;
      first (by inversion Hfill ; subst ; exfalso ; values_no_reduce ) ;
      inversion Hfill as [[ Ha Ha0 Ha1 Hnil ]] ;
      apply Logic.eq_sym, app_eq_nil in Hnil as [-> ->] ;
      remember [a0 ; a1] as es eqn:Heqes ;
      rewrite - Ha0 - Ha1 in Heqes ;
      apply Logic.eq_sym in Heqes ;
      exfalso ; no_reduce Heqes Hes1
    | destruct bef as [| a1 bef ];
      [ destruct es1 as [| a1 es1] ; first (by empty_list_no_reduce ) ;
        inversion Hfill as [[ Ha Ha0 Ha1 Hnil ]] ;
        apply Logic.eq_sym, app_eq_nil in Hnil as [-> ->] ;
        remember [a1] as es eqn:Heqes ;
        rewrite - Ha1 in Heqes ;
        apply Logic.eq_sym in Heqes ;
        exfalso ; no_reduce Heqes Hes1
      | inversion Hfill as [[ Ha Ha0 Ha1 Hnil ]] ;
        apply Logic.eq_sym, app_eq_nil in Hnil as [-> Hnil] ;
        apply app_eq_nil in Hnil as [-> ->] ;
          by empty_list_no_reduce ]]].
*)

Section lfilled_reduce_properties.
  
  Let reducible := @iris.program_logic.language.reducible wasm_lang.

  Let expr := iris.expr.
  Let val := iris.val.
  Let to_val := iris.to_val.

  (*
This lemma basically states that, enclosing es in an lh context cannot generate
new reduction paths. It can almost be proved using the determinacy lemma, but the arbitrary level of labels in the r_label case prevents an easy proof.

Note that this is a property very similar to Iris context.
*)
  Lemma lfilled_reduce i lh es LI f σ LI' f' σ' obs efs :
    lfilled i lh es LI ->
    reducible (es, f) σ ->
    prim_step (LI, f) σ obs (LI', f') σ' efs ->
    (exists es', prim_step (es, f) σ obs (es', f') σ' efs /\ lfilled i lh es' LI') \/
      (exists lh0, lfilled 0 lh0 [AI_trap] es /\ σ = σ' /\ f = f').

  Proof.
    intros Hfill Hred Hstep.

    destruct Hred as (obs0 & [es' f0] & s0 & efs0 & (Hes & -> & ->)).

    destruct Hstep as (HLI & -> & ->).

    generalize dependent LI. generalize dependent i.
    generalize dependent lh. generalize dependent LI'.
    cut (forall nnn LI' lh i LI, length_rec LI < nnn ->
                            lfilled i lh es LI
                            → opsem.reduce σ f LI σ' f' LI'
                            → (∃ es'0 : iris.expr0,
                                  prim_step (es, f) σ [] (es'0, f') σ' []
                                  ∧ lfilled i lh es'0 LI') ∨
                                (∃ lh0 : lholed, lfilled 0 lh0 [AI_trap] es /\
                                                   σ = σ' /\ f = f')). 

    { intros H LI' lh i LI ;
        assert (length_rec LI < S (length_rec LI)) ; first lia ; by eapply H. }  
    induction nnn ; intros LI' lh i LI Hlen Hfill HLI.
    lia.
    induction HLI.
    destruct H.
 

    all: try by lazymatch goal with
         | _ : length_rec [_;_] < _ |- _ => idtac
         end;
    
          move/lfilledP in Hfill; inversion Hfill; subst;
          try (by lazymatch goal with
                  | _ : (?vs ++ _ :: _)%SEQ = [_;_] |- _ =>
                      by try destruct ref; try destruct v; try destruct v; do 3 destruct vs => // 
                  end);
          lazymatch goal with
          | H : (?vs ++ ?es ++ ?aft)%SEQ = [_;_] |- _ =>
              destruct vs ;
              [ destruct es ; first empty_list_no_reduce;
                destruct es ; first (by exfalso; inversion H; subst; values_no_reduce; try destruct ref; try rewrite /= const_const) ;
                destruct es, aft ; try done ;
                inversion H; subst; 
                left ; eexists ; split ;
                [ split; last done;
                  try rewrite - Heqf';
                  repeat econstructor => //
                | unfold lfilled, lfill; simpl; done
                ]
              | destruct vs; last (by destruct vs, es, aft ; try done; empty_list_no_reduce);
                destruct es; first empty_list_no_reduce;
                destruct es, aft ; try done;
                inversion H; subst
              ]
          end; 
          lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  )
              ];
              inversion H3; subst => //
          end .
    all: try by lazymatch goal with
         | _ : length_rec [_;_;_] < _ |- _ => idtac
         end;
      move/lfilledP in Hfill; inversion Hfill; subst;
          try (by lazymatch goal with
                  | _ : (?vs ++ _ :: _)%SEQ = [_;_;_] |- _ =>
                      by do 4 destruct vs => //
                  end);
          lazymatch goal with
          | H : (?vs ++ ?es ++ ?aft)%SEQ = [_;_;_] |- _ =>
              destruct vs ;
              [ destruct es ; first empty_list_no_reduce;
                destruct es ; first (by exfalso; inversion H; subst; values_no_reduce) ;
                destruct es ; first (by exfalso; inversion H; subst; values_no_reduce) ;
                destruct es, aft ; try done ;
                inversion H; subst; 
                left ; eexists ; split ;
                [ split; last done;
                  try rewrite - Heqf';
                  repeat econstructor => //
                | unfold lfilled, lfill; simpl; done
                ]
              | destruct vs;
                [ destruct es; first empty_list_no_reduce;
                  destruct es; first (by exfalso; inversion H; subst; values_no_reduce);
                  destruct es, aft ; try done ;
                  inversion H; subst
                |  destruct vs; last (by destruct vs, es, aft ; try done; empty_list_no_reduce);
                   destruct es; first empty_list_no_reduce;
                   destruct es, aft ; try done;
                   inversion H; subst
                ]
              ]
          end;
        first lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  );
              destruct vs; last (by destruct vs, es; try done; empty_list_no_reduce);
              destruct es; first empty_list_no_reduce;
              destruct es; last done;
              inversion H3; subst
              ]
          end ;
      lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  );
              inversion H3; subst
              ]
      end .

    all: try by
      lazymatch goal with
      | _ : length_rec [_] < _ |- _ => idtac 
      end;
    move/lfilledP in Hfill; inversion Hfill; subst;
    try (by lazymatch goal with
                  | _ : (?vs ++ _ :: _)%SEQ = [_] |- _ =>
                      by do 2 destruct vs => //
           end);

      lazymatch goal with
        | H : (?vs ++ ?es ++ ?aft)%SEQ = [_] |- _ =>
            destruct vs; last (by destruct vs, es => //; empty_list_no_reduce);
            destruct es; first empty_list_no_reduce;
            destruct es, aft; try done;
            inversion H; subst;
            left; eexists ; split;
            [ split; last done ;
              try rewrite -Heqf';
              try econstructor; try econstructor => // 
            | unfold lfilled, lfill; simpl; done
            ]
        end
.

    - move/lfilledP in Hfill; inversion Hfill; subst;
      try (by lazymatch goal with
              | _ : (?vs ++ _ :: _)%SEQ = [_] |- _ =>
                  by do 2 destruct vs => //
              end).
      + destruct vs0; last by destruct vs0, es => //; empty_list_no_reduce.
        destruct es; first empty_list_no_reduce.
        destruct es, es'0 => //.
        inversion H0; subst.
        left; eexists; split.
        * split; last done.

          do 2 econstructor => //.
        * rewrite /lfilled /lfill /= app_nil_r //.
      + destruct bef; last by destruct bef.
        inversion H0; subst.
        move/lfilledP in H5.
        apply lfilled_const in H5 as [_ Hconst] => //.
        exfalso; values_no_reduce.
    - move/lfilledP in Hfill; inversion Hfill; subst;
      try (by lazymatch goal with
              | _ : (?vs ++ _ :: _)%SEQ = [_] |- _ =>
                  by do 2 destruct vs => //
              end).
      + destruct vs0; last by destruct vs0, es => //; empty_list_no_reduce.
        destruct es; first empty_list_no_reduce.
        destruct es, es'0 => //.
        inversion H0; subst.
        left; eexists; split.
        * split; last done.

          do 2 econstructor => //.
        * rewrite /lfilled /lfill /= app_nil_r //.
      + destruct bef; last by destruct bef.
        inversion H0; subst.
        move/lfilledP in H5.
        apply lfilled_const in H5 as [_ Hconst] => //.
        exfalso; values_no_reduce.
    - move/lfilledP in Hfill; inversion Hfill; subst;
      try (by lazymatch goal with
              | _ : (?vs ++ _ :: _)%SEQ = [_] |- _ =>
                  by do 2 destruct vs => //
              end).
      + destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
        destruct es; first empty_list_no_reduce.
        destruct es, es'0 => //.
        inversion H; subst.
        left; eexists; split.
        * split; last done.

          econstructor.
          apply rs_handler_trap.
        * rewrite /lfilled /lfill //.
      + destruct bef; last by destruct bef.
        inversion H; subst.
        move/lfilledP in H4.
        apply filled_singleton in H4 as (_ & _ & Hconst) => //.
        subst; exfalso; eapply AI_trap_irreducible => //.
        intros ->; empty_list_no_reduce.
    - move/lfilledP in Hfill; inversion Hfill; subst;
      try (by lazymatch goal with
              | _ : (?vs ++ _ :: _)%SEQ = [_] |- _ =>
                  by do 2 destruct vs => //
              end).
      + destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
        destruct es; first empty_list_no_reduce.
        destruct es, es'0 => //.
        inversion H; subst.
        left; eexists; split.
        * split; last done.

          econstructor.
          apply rs_prompt_trap.
        * rewrite /lfilled /lfill //.
      + destruct bef; last by destruct bef.
        inversion H; subst.
        move/lfilledP in H4.
        apply filled_singleton in H4 as (_ & _ & Hconst) => //.
        subst; exfalso; eapply AI_trap_irreducible => //.
        intros ->; empty_list_no_reduce.
    - move/lfilledP in Hfill; inversion Hfill; subst.
      all: try by lazymatch goal with
                  | _ : (?vs ++ _ :: _)%SEQ = [_;_;_;_] |- _ =>
                      destruct v1, v2; destruct v, v0; do 5 destruct vs => //
                  end.
      destruct vs.
      + repeat (destruct es; first by inversion H0; subst; exfalso; values_no_reduce; repeat rewrite /= const_const).
        destruct es, es'0 => //.
        inversion H0; subst.
        left. eexists.
        split.
        * split; last done.

          constructor. constructor => //.
        * rewrite /lfilled /lfill /= //.
      + destruct vs.
        * repeat (destruct es; first by inversion H0; subst; exfalso; values_no_reduce; repeat rewrite /= const_const).
          destruct es => //. inversion H0; subst.
    (* two values *)
           lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves) ;
              [ by move/lfilledP in H01; inversion H01; subst;
                destruct v2; destruct v;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by destruct v2; destruct v; do 4 destruct vs => //);
                try (by destruct v2; destruct v; do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred; try rewrite /= const_const);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  );
              inversion H3; subst
              ]
           end .
           destruct vs.
          -- repeat (destruct es; first by inversion H2; subst; exfalso; values_no_reduce; repeat rewrite /= const_const).
             destruct es => //.
             inversion H2; subst.
    (* 1 value *)
               lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  );
              inversion H3; subst
              ]
               end .
               destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
               destruct es; first empty_list_no_reduce.
               destruct es => //.
               inversion H2; subst.
    (* 0 values *)
                     lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  );
              inversion H3; subst
              ]
                     end .
                     destruct vs, es => //; empty_list_no_reduce.
          -- inversion H2; subst.
                 destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
               destruct es; first empty_list_no_reduce.
               destruct es => //.
               inversion H2; subst.
    (* 0 values *)
                     lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  );
              inversion H3; subst
              ]
                     end .
                     destruct vs, es => //; empty_list_no_reduce.
        * inversion H0; subst.
          destruct vs.
          -- repeat (destruct es; first by inversion H3; subst; exfalso; values_no_reduce; repeat rewrite /= const_const).
             destruct es => //.
             inversion H3; subst.
              (* 1 value *)
               lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  );
              inversion H3; subst
              ]
               end .
               destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
               destruct es; first empty_list_no_reduce.
               destruct es => //.
               inversion H2; subst.
    (* 0 values *)
                     lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  );
              inversion H3; subst
              ]
                     end .
                     destruct vs, es => //; empty_list_no_reduce.
          -- inversion H3; subst.
                 destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
               destruct es; first empty_list_no_reduce.
               destruct es => //.
               inversion H2; subst.
    (* 0 values *)
                     lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  );
              inversion H3; subst
              ]
                     end .
                     destruct vs, es => //; empty_list_no_reduce.
 - move/lfilledP in Hfill; inversion Hfill; subst.
      all: try by lazymatch goal with
                  | _ : (?vs ++ _ :: _)%SEQ = [_;_;_;_] |- _ =>
                      destruct v1, v2; destruct v, v0; do 5 destruct vs => //
                  end.
      destruct vs.
      + repeat (destruct es; first by inversion H0; subst; exfalso; values_no_reduce; repeat rewrite /= const_const).
        destruct es, es'0 => //.
        inversion H0; subst.
        left. eexists.
        split.
        * split; last done.

          constructor.
          apply rs_select_true => //.
        * rewrite /lfilled /lfill /= //.
      + destruct vs.
        * repeat (destruct es; first by inversion H0; subst; exfalso; values_no_reduce; repeat rewrite /= const_const).
          destruct es => //. inversion H0; subst.
    (* two values *)
           lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves) ;
              [ by move/lfilledP in H01; inversion H01; subst;
                destruct v2; destruct v;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by destruct v2; destruct v; do 4 destruct vs => //);
                try (by destruct v2; destruct v; do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred; try rewrite /= const_const);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  );
              inversion H3; subst
              ]
           end .
           destruct vs.
          -- repeat (destruct es; first by inversion H2; subst; exfalso; values_no_reduce; repeat rewrite /= const_const).
             destruct es => //.
             inversion H2; subst.
    (* 1 value *)
               lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  );
              inversion H3; subst
              ]
               end .
               destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
               destruct es; first empty_list_no_reduce.
               destruct es => //.
               inversion H2; subst.
    (* 0 values *)
                     lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  );
              inversion H3; subst
              ]
                     end .
                     destruct vs, es => //; empty_list_no_reduce.
          -- inversion H2; subst.
                 destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
               destruct es; first empty_list_no_reduce.
               destruct es => //.
               inversion H2; subst.
    (* 0 values *)
                     lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  );
              inversion H3; subst
              ]
                     end .
                     destruct vs, es => //; empty_list_no_reduce.
        * inversion H0; subst.
          destruct vs.
          -- repeat (destruct es; first by inversion H5; subst; exfalso; values_no_reduce; repeat rewrite /= const_const).
             destruct es => //.
             inversion H5; subst.
              (* 1 value *)
               lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  );
              inversion H3; subst
              ]
               end .
               destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
               destruct es; first empty_list_no_reduce.
               destruct es => //.
               inversion H2; subst.
    (* 0 values *)
                     lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  );
              inversion H3; subst
              ]
                     end .
                     destruct vs, es => //; empty_list_no_reduce.
          -- inversion H5; subst.
                 destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
               destruct es; first empty_list_no_reduce.
               destruct es => //.
               inversion H3; subst.
    (* 0 values *)
                     lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  );
              inversion H3; subst
              ]
                     end .
                     destruct vs, es => //; empty_list_no_reduce.                     
          
             
           
          

   
    - move/lfilledP in Hfill; inversion Hfill; subst;
        try (by lazymatch goal with
                | H : (?vs ++ _ :: _)%SEQ = (_ ++ [_])%SEQ |- _ =>
                    apply first_values in H as (? & ? & ?); try apply v_to_e_is_const_list
                end).
      apply const_list_snoc_eq3 in H3 => //.
      2: intros -> ; empty_list_no_reduce.
      2: destruct (const_list es) eqn:Habs => //; exfalso; values_no_reduce => //.
      2: intros -> ; exfalso; eapply AI_trap_irreducible => //.
      destruct H3 as (vs2 & es2 & -> & -> & Hnil & Hvs2).
      destruct es2, es'0 => //.
      destruct vs0.
      + left. eexists.
        split.
        * split; last done.

          econstructor. econstructor => //.
        * rewrite /lfilled /lfill /= //.
      + exfalso.
        eapply block_not_enough_arguments_no_reduce.
        exact Hes. exact Hvs2.
        rewrite /= length_app in H1. lia.
    - move/lfilledP in Hfill; inversion Hfill; subst;
        try (by lazymatch goal with
                | H : (?vs ++ _ :: _)%SEQ = (_ ++ [_])%SEQ |- _ =>
                    apply first_values in H as (? & ? & ?); try apply v_to_e_is_const_list
                end).
      apply const_list_snoc_eq3 in H3 => //.
      2: intros -> ; empty_list_no_reduce.
      2: destruct (const_list es) eqn:Habs => //; exfalso; values_no_reduce => //.
      2: intros -> ; exfalso; eapply AI_trap_irreducible => //.
      destruct H3 as (vs2 & es2 & -> & -> & Hnil & Hvs2).
      destruct es2, es'0 => //.
      destruct vs0.
      + left. eexists.
        split.
        * split; last done.
          rewrite app_nil_r .
          econstructor. econstructor => //.
        * rewrite /lfilled /lfill /= H1 //.
      + exfalso.
        eapply loop_not_enough_arguments_no_reduce.
        exact Hes. exact Hvs2.
        rewrite /= length_app in H1. lia.
    - move/lfilledP in Hfill; inversion Hfill; subst;
      try (by lazymatch goal with
              | _ : (?vs ++ _ :: _)%SEQ = [_] |- _ =>
                  by do 2 destruct vs => //
              end).
      + destruct vs0; last by destruct vs0, es => //; empty_list_no_reduce.
        destruct es; first empty_list_no_reduce.
        destruct es, es'0 => //.
        inversion H0; subst.
        left; eexists; split.
        * split; last done.

          do 2 econstructor => //.
        * rewrite /lfilled /lfill /= app_nil_r //.
      + destruct vs0; last by destruct vs0.
        inversion H0; subst.
        move/lfilledP in H5.
        apply lfilled_const in H5 as [_ Hconst] => //.
        exfalso; values_no_reduce.
    - move/lfilledP in Hfill; inversion Hfill; subst;
      try (by lazymatch goal with
              | _ : (?vs ++ _ :: _)%SEQ = [_] |- _ =>
                  by do 2 destruct vs => //
              end).
      + destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
        destruct es; first empty_list_no_reduce.
        destruct es, es'0 => //.
        inversion H; subst.
        left; eexists; split.
        * split; last done.

          econstructor.
          apply rs_label_trap.
        * rewrite /lfilled /lfill //.
      + destruct vs; last by destruct vs.
        inversion H; subst.
        move/lfilledP in H4.
        apply filled_singleton in H4 as (_ & _ & Hconst) => //.
        subst; exfalso; eapply AI_trap_irreducible => //.
        intros ->; empty_list_no_reduce.
    - move/lfilledP in Hfill; inversion Hfill; subst;
      try (by lazymatch goal with
              | _ : (?vs ++ _ :: _)%SEQ = [_] |- _ =>
                  by do 2 destruct vs => //
              end).
      + destruct vs0; last by destruct vs0, es => //; empty_list_no_reduce.
        destruct es; first empty_list_no_reduce.
        destruct es => //.
        inversion H2; subst.
        left.
        eexists. split.
        * split; last done. 
          constructor. eapply rs_br. 3: exact H1.
          done. done.
        * rewrite /lfilled /lfill /= app_nil_r //.
      + destruct vs0; last by destruct vs0.
        inversion H2; subst.
        exfalso.
        eapply lfilled_br_and_reduce.
        exact Hes.
        3: exact H1.
        all: try done.
        by apply/lfilledP.
                      
    -  move/lfilledP in Hfill; inversion Hfill; subst;
      try (by lazymatch goal with
              | _ : (?vs ++ _ :: _)%SEQ = [_] |- _ =>
                  by do 2 destruct vs => //
              end).
       destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
        destruct es; first empty_list_no_reduce.
        destruct es, es'0 => //.
        inversion H1; subst.
        left; eexists; split.
       + split; last done.

          do 2 econstructor => //.
       + rewrite /lfilled /lfill /= app_nil_r //.
    - move/lfilledP in Hfill; inversion Hfill; subst;
        try (by lazymatch goal with
                | _ : (?vs ++ _ :: _)%SEQ = [_] |- _ =>
                    by do 2 destruct vs => //
                end).
      destruct vs0; last by destruct vs0, es => //; empty_list_no_reduce.
      destruct es; first empty_list_no_reduce.
      destruct es => //.
      inversion H2; subst.
      left.
      eexists. split.
      + split; last done. 
        constructor. eapply rs_return. 3: exact H1.
        done. done.
      + rewrite /lfilled /lfill /= app_nil_r //.
    -  move/lfilledP in Hfill; inversion Hfill; subst;
          try (by lazymatch goal with
                  | _ : (?vs ++ _ :: _)%SEQ = [_;_] |- _ =>
                      by try destruct ref; try destruct v; try destruct v; do 3 destruct vs => // 
                  end).
          lazymatch goal with
          | H0 : (?vs ++ ?es ++ ?aft)%SEQ = [_;_] |- _ =>
              destruct vs ;
              [ destruct es ; first empty_list_no_reduce;
                destruct es ; first (by exfalso; inversion H0; subst; values_no_reduce; try destruct ref; try rewrite /= const_const; try rewrite /= H) ;
                destruct es, aft ; try done ;
                inversion H0; subst; 
                left ; eexists ; split ;
                [ split; last done;
                  try rewrite - Heqf';
                  repeat econstructor => //
                | unfold lfilled, lfill; simpl; done
                ]
              | destruct vs; last (by destruct vs, es, aft ; try done; empty_list_no_reduce);
                destruct es; first empty_list_no_reduce;
                destruct es, aft ; try done;
                inversion H0; subst
              ]
          end; 
          lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  )
              ];
              inversion H3; subst => //
          end .
    - edestruct lfilled_singleton as (j & lh' & Hlh' & Hj).
      9: exact H0. 8: exact Hfill.
      intros ->; empty_list_no_reduce.
      destruct (const_list es) eqn:Habs => //; exfalso; values_no_reduce => //.
      intros ->; eapply AI_trap_irreducible => //.
      all: try done.
      destruct i, j => //. 
      right. eexists; split => //.

    - move/lfilledP in Hfill; inversion Hfill; subst;
        try (by lazymatch goal with
                | H : (?vs ++ _ :: _)%SEQ = (_ ++ [_])%SEQ |- _ =>
                    apply first_values in H as (? & ? & ?); try apply v_to_e_is_const_list
                end).
      apply const_list_snoc_eq3 in H9 => //.
      2: apply v_to_e_is_const_list.
      2: intros -> ; empty_list_no_reduce.
      2: destruct (const_list es) eqn:Habs => //; exfalso; values_no_reduce => //.
      2: intros -> ; exfalso; eapply AI_trap_irreducible => //.
      destruct H9 as (vs2 & es2 & Hvs & -> & Hnil & Hvs2).
      destruct es2, es'0 => //.
      destruct vs.
      + simpl in Hvs; subst vs2. left. eexists.
        split.
        * split; last done.
          rewrite app_nil_r .
          eapply r_invoke_native => //.
        * rewrite /lfilled /lfill /= //.
      + exfalso.
        eapply invoke_not_enough_arguments_no_reduce_native.
        done.
        exact Hes. exact Hvs2.
        assert (length (v_to_e_list vcs) = length vcs); first by rewrite length_map.
        rewrite Hvs in H0.
        rewrite /= length_app in H0. lia.
    - move/lfilledP in Hfill; inversion Hfill; subst;
        try (by lazymatch goal with
                | H : (?vs ++ _ :: _)%SEQ = (_ ++ [_])%SEQ |- _ =>
                    apply first_values in H as (? & ? & ?); try apply v_to_e_is_const_list
                end).
      apply const_list_snoc_eq3 in H5 => //.
      2: apply v_to_e_is_const_list.
      2: intros -> ; empty_list_no_reduce.
      2: destruct (const_list es) eqn:Habs => //; exfalso; values_no_reduce => //.
      2: intros -> ; exfalso; eapply AI_trap_irreducible => //.
      destruct H5 as (vs2 & es2 & Hvs & -> & Hnil & Hvs2).
      destruct es2, es'0 => //.
      destruct vs.
      + simpl in Hvs; subst vs2. left. eexists.
        split.
        * split; last done.
          rewrite app_nil_r .
          eapply r_invoke_host => //.
        * rewrite /lfilled /lfill /= //.
      + exfalso.
        eapply invoke_not_enough_arguments_no_reduce_host.
        done.
        exact Hes. exact Hvs2.
        assert (length (v_to_e_list vcs) = length vcs); first by rewrite length_map.
        rewrite Hvs in H0.
        rewrite /= length_app in H0. lia.
    - move/lfilledP in Hfill; inversion Hfill; subst;
        try (by lazymatch goal with
                | H : (?vs ++ _ :: _)%SEQ = (_ ++ [_])%SEQ |- _ =>
                    apply first_values in H as (? & ? & ?); try apply v_to_e_is_const_list
                end).
      apply const_list_snoc_eq3 in H4 => //.
      2: intros -> ; empty_list_no_reduce.
      2: destruct (const_list es) eqn:Habs => //; exfalso; values_no_reduce => //.
      2: intros -> ; exfalso; eapply AI_trap_irreducible => //.
      destruct H4 as (vs2 & es2 & -> & -> & Hnil & Hvs2).
      destruct es2, es'0 => //.
      destruct vs0.
      + left. eexists.
        split.
        * split; last done.
          rewrite app_nil_r .
          eapply r_try_table => //.
        * rewrite /lfilled /lfill /= //.
      + exfalso.
        eapply try_table_not_enough_arguments_no_reduce.
        done.
        exact Hes. exact Hvs2.
        rewrite /= length_app in H2. lia.
    - move/lfilledP in Hfill; inversion Hfill; subst;
        try (by lazymatch goal with
                | H : (?vs ++ _ :: _)%SEQ = (_ ++ [_])%SEQ |- _ =>
                    apply first_values in H as (? & ? & ?); try apply v_to_e_is_const_list
                end).
      apply const_list_snoc_eq3 in H4 => //.
      2: apply v_to_e_is_const_list.
      2: intros -> ; empty_list_no_reduce.
      2: destruct (const_list es) eqn:Habs => //; exfalso; values_no_reduce => //.
      2: intros -> ; exfalso; eapply AI_trap_irreducible => //.
      destruct H4 as (vs2 & es2 & Hvs & -> & Hnil & Hvs2).
      destruct es2, es'0 => //.
      destruct vs.
      + simpl in Hvs; subst vs2. left. eexists.
        split.
        * split; last done.
          rewrite app_nil_r .
          eapply r_throw => //.
        * rewrite /lfilled /lfill /= //.
      + exfalso.
        eapply throw_not_enough_arguments_no_reduce.
        done. done.
        exact Hes. exact Hvs2.
        rewrite Hvs in H2.
        rewrite /= length_app in H2. lia.
    - move/lfilledP in Hfill; inversion Hfill; subst;
      try (by lazymatch goal with
              | _ : (?vs ++ _ :: _)%SEQ = [_] |- _ =>
                  by do 2 destruct vs => //
              end).
      + destruct vs0; last by destruct vs0, es => //; empty_list_no_reduce.
        destruct es; first empty_list_no_reduce.
        destruct es => //.
        inversion H1; subst.
        left.
        eexists. split.
        * split; last done. 
          eapply r_throw_ref. exact H. exact H0.
        * rewrite /lfilled /lfill /= app_nil_r //.
      + destruct bef; last by destruct bef.
        inversion H1; subst.
        exfalso.
        eapply hfilled_throw_ref_and_reduce.
        exact Hes.
        exact H.
        by apply/lfilledP.
    - move/lfilledP in Hfill; inversion Hfill; subst;
      try (by lazymatch goal with
              | _ : (?vs ++ _ :: _)%SEQ = [_] |- _ =>
                  by do 2 destruct vs => //
              end).
      + destruct vs0; last by destruct vs0, es => //; empty_list_no_reduce.
        destruct es; first empty_list_no_reduce.
        destruct es => //.
        inversion H1; subst.
        left.
        eexists. split.
        * split; last done. 
          eapply r_throw_ref_ref. exact H. exact H0.
        * rewrite /lfilled /lfill /= app_nil_r //.
      + destruct bef; last by destruct bef.
        inversion H1; subst.
        exfalso.
        eapply hfilled_throw_ref_and_reduce.
        exact Hes.
        exact H.
        by apply/lfilledP.
    - rewrite separate1 -cat_app catA in Hfill.
      move/lfilledP in Hfill; inversion Hfill; subst;
        try (by lazymatch goal with
                | H : (?vs ++ _ :: _)%SEQ = (_ ++ _)%SEQ |- _ =>
                    apply first_values in H as (? & ? & ?); try apply const_list_concat; try apply v_to_e_is_const_list
                end).
      apply const_list_snoc_eq3 in H5 => //.
      2: by apply const_list_concat; try apply v_to_e_is_const_list.
      2: intros -> ; empty_list_no_reduce.
      2: destruct (const_list es) eqn:Habs => //; exfalso; values_no_reduce => //.
      2: intros -> ; exfalso; eapply AI_trap_irreducible => //.
      destruct H5 as (vs2 & es2 & Hvs & -> & Hnil & Hvs2).
      destruct es2, es'0 => //.
      separate_last vs2.
      + rewrite app_assoc in Hvs.
        apply concat_cancel_last in Hvs as [-> <-].
        destruct vs0.
        * left. eexists.
          split.
          -- split; last done.
             rewrite app_nil_r .
             rewrite -cat_app -catA.
             eapply r_resume => //.
          -- rewrite /lfilled /lfill /= //.
        * exfalso.
          eapply resume_not_enough_arguments_no_reduce.
          done. done.
          rewrite -cat_app -catA in Hes.
          exact Hes. apply const_list_split in Hvs2 as [??] => //. 
          rewrite /= length_app in H1. lia.
      +  lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs; try destruct vs; try destruct vs; try destruct vs; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves);
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs => //);
                try (by do 4 destruct bef => //);
                destruct vs;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  )
              ];
              inversion H3; subst => //
         end .
    - move/lfilledP in Hfill; inversion Hfill; subst;
        try (by lazymatch goal with
                | H : (?vs ++ _ :: _)%SEQ = (_ ++ [_])%SEQ |- _ =>
                    apply first_values in H as (? & ? & ?); try apply v_to_e_is_const_list
                end).
      apply const_list_snoc_eq3 in H2 => //.
      2: apply v_to_e_is_const_list.
      2: intros -> ; empty_list_no_reduce.
      2: destruct (const_list es) eqn:Habs => //; exfalso; values_no_reduce => //.
      2: intros -> ; exfalso; eapply AI_trap_irreducible => //.
      destruct H2 as (vs2 & es2 & Hvs & -> & Hnil & Hvs2).
      destruct es2, es'0 => //.
      destruct vs0.
      + simpl in Hvs; subst vs2. left. eexists.
        split.
        * split; last done.
          rewrite app_nil_r.
          eapply r_suspend_desugar => //.
        * rewrite /lfilled /lfill /= //.
      + exfalso.
        eapply suspend_not_enough_arguments_no_reduce.
        done. done.
        exact Hes. exact Hvs2.
        assert (length (v_to_e_list vs) = length vs); first by rewrite length_map.
        rewrite Hvs in H2.
        rewrite /= length_app in H2. lia.
    - rewrite separate1 -cat_app catA in Hfill.
      move/lfilledP in Hfill; inversion Hfill; subst;
        try (by lazymatch goal with
                | H : (?vs ++ _ :: _)%SEQ = (_ ++ _)%SEQ |- _ =>
                    apply first_values in H as (? & ? & ?); try apply const_list_concat; try apply v_to_e_is_const_list
                end).
      apply const_list_snoc_eq3 in H5 => //.
      2: by apply const_list_concat; try apply v_to_e_is_const_list.
      2: intros -> ; empty_list_no_reduce.
      2: destruct (const_list es) eqn:Habs => //; exfalso; values_no_reduce => //.
      2: intros -> ; exfalso; eapply AI_trap_irreducible => //.
      destruct H5 as (vs2 & es2 & Hvs & -> & Hnil & Hvs2).
      destruct es2, es'0 => //.
      separate_last vs2.
      + rewrite app_assoc in Hvs.
        apply concat_cancel_last in Hvs as [Hvs <-].
        destruct vs0.
        * simpl in Hvs; subst l. left. eexists.
          split.
          -- split; last done.
             rewrite app_nil_r .
             rewrite -cat_app -catA.
             eapply r_switch_desugar => //.
          -- rewrite /lfilled /lfill /= //.
        * exfalso.
          eapply switch_not_enough_arguments_no_reduce.
          done. done.
          rewrite -cat_app -catA in Hes.
          exact Hes.
          apply const_list_split in Hvs2 as [??] => //.
          assert (length (v_to_e_list vs) = length vs); first by rewrite length_map.
          rewrite Hvs in H5.
          rewrite /= length_app in H5. lia.
      +  lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs1; try destruct vs1; try destruct vs1; try destruct vs1; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves) ;
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs1 => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs1 => //);
                try (by do 4 destruct bef => //);
                destruct vs1;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  )
              ];
              inversion H3; subst => //
         end .
    - move/lfilledP in Hfill; inversion Hfill; subst;
      try (by lazymatch goal with
              | _ : (?vs ++ _ :: _)%SEQ = [_] |- _ =>
                  by do 2 destruct vs => //
              end).
      + destruct vs0; last by destruct vs0, es => //; empty_list_no_reduce.
        destruct es; first empty_list_no_reduce.
        destruct es => //.
        inversion H3; subst.
        left.
        eexists. split.
        * split; last done. 
          eapply r_suspend. done. exact H0. exact H1. exact H2.
        * rewrite /lfilled /lfill /= app_nil_r //.
      + destruct bef; last by destruct bef.
        inversion H3; subst.
        exfalso.
        eapply hfilled_suspend_and_reduce.
        exact Hes.
        exact H2.
        by apply/lfilledP.
   - move/lfilledP in Hfill; inversion Hfill; subst;
      try (by lazymatch goal with
              | _ : (?vs ++ _ :: _)%SEQ = [_] |- _ =>
                  by do 2 destruct vs => //
              end).
      + destruct vs0; last by destruct vs0, es => //; empty_list_no_reduce.
        destruct es; first empty_list_no_reduce.
        destruct es => //.
        inversion H4; subst.
        left.
        eexists. split.
        * split; last done. 
          eapply r_switch. done. done. exact H1. exact H2. exact H3. 
        * rewrite /lfilled /lfill /=  //.
      + destruct bef; last by destruct bef.
        inversion H4; subst.
        exfalso.
        edestruct hfilled_switch_and_reduce as (? & ? & ? & _ & Habs & _).
        exact Hes.
        exact H2.
        by apply/lfilledP.
        rewrite Habs in H1 => //. 
    -  rewrite separate1 -cat_app catA in Hfill.
      move/lfilledP in Hfill; inversion Hfill; subst;
        try (by lazymatch goal with
                | H : (?vs ++ _ :: _)%SEQ = (_ ++ _)%SEQ |- _ =>
                    apply first_values in H as (? & ? & ?); try apply const_list_concat; try apply v_to_e_is_const_list
                end).
      apply const_list_snoc_eq3 in H4 => //.
      2: by apply const_list_concat; try apply v_to_e_is_const_list.
      2: intros -> ; empty_list_no_reduce.
      2: destruct (const_list es) eqn:Habs => //; exfalso; values_no_reduce => //.
      2: intros -> ; exfalso; eapply AI_trap_irreducible => //.
      destruct H4 as (vs2 & es2 & Hvs & -> & Hnil & Hvs2).
      destruct es2, es'0 => //.
      separate_last vs2.
      + rewrite app_assoc in Hvs.
        apply concat_cancel_last in Hvs as [-> <-].
        destruct vs0.
        * left. eexists.
          split.
          -- split; last done.
             rewrite app_nil_r .
             rewrite -cat_app -catA.
             eapply r_contbind => //.
          -- rewrite /lfilled /lfill /= //.
        * exfalso.
          eapply contbind_not_enough_arguments_no_reduce.
          done. done. done.
          rewrite -cat_app -catA in Hes.
          exact Hes.
          apply const_list_split in Hvs2 as [??] => //. 
          rewrite /= length_app in H2. lia.
      +  lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs1; try destruct vs1; try destruct vs1; try destruct vs1; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves) ;
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs1 => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs1 => //);
                try (by do 4 destruct bef => //);
                destruct vs1;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  )
              ];
              inversion H3; subst => //
         end .
    - rewrite separate1 -cat_app catA in Hfill.
      move/lfilledP in Hfill; inversion Hfill; subst;
        try (by lazymatch goal with
                | H : (?vs ++ _ :: _)%SEQ = (_ ++ _)%SEQ |- _ =>
                    apply first_values in H as (? & ? & ?); try apply const_list_concat; try apply v_to_e_is_const_list
                end).
      apply const_list_snoc_eq3 in H9 => //.
      2: by apply const_list_concat; try apply v_to_e_is_const_list.
      2: intros -> ; empty_list_no_reduce.
      2: destruct (const_list es) eqn:Habs => //; exfalso; values_no_reduce => //.
      2: intros -> ; exfalso; eapply AI_trap_irreducible => //.
      destruct H9 as (vs2 & es2 & Hvs & -> & Hnil & Hvs2).
      destruct es2, es'0 => //.
      separate_last vs2.
      + rewrite app_assoc in Hvs.
        apply concat_cancel_last in Hvs as [Hvs <-].
        destruct vs.
        * simpl in Hvs; subst l. left. eexists.
          split.
          -- split; last done.
             rewrite app_nil_r .
             rewrite -cat_app -catA.
             eapply r_resume_throw => //.
          -- rewrite /lfilled /lfill /= //.
        * exfalso.
          eapply resume_throw_not_enough_arguments_no_reduce.
          done. done. done.
          rewrite -cat_app -catA in Hes.
          exact Hes.
          apply const_list_split in Hvs2 as [??] => //. 
          rewrite Hvs /= length_app in H2. lia.
      +  lazymatch goal with
          | Hred : reduce _ _ ?esn _ _ _ |- _ =>
              clear - Hred; remember esn as ves;
              exfalso;
              induction Hred as [? ? ? ? H02 | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ?????????? Hred IHHred H02 H03 | ];
              first destruct H02 as [| | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | | ??? H01 ]; 
              try (by inversion Heqves);
              try (by destruct vs0; try destruct vs0; try destruct vs0; try destruct vs0; inversion Heqves);
              try (by destruct ves; try destruct ves; try destruct ves; try destruct ves; inversion Heqves) ;
              [ by move/lfilledP in H01; inversion H01; subst;
                try (by do 4 destruct vs0 => //);
                do 4 destruct bef => //
              | move/lfilledP in H02; inversion H02; subst;
                try (by do 4 destruct vs0 => //);
                try (by do 4 destruct bef => //);
                destruct vs0;
                first (
                    do 4 try (destruct es; first by inversion H3; subst; apply values_no_reduce in Hred);
                    inversion H3; subst;
                    destruct es => //; apply IHHred => //
                  )
              ];
              inversion H3; subst => //
         end .

    - destruct (decide (lh_true_depth lh <= lh_true_depth lh0)).
      + eapply true_depth_leq_filled in l as Hk.
        2: exact Hfill.
        2: exact H.
        destruct (empty_base lh) as [[l0 bef] aft] eqn:Hlh.
        eapply can_empty_base in Hfill as (besa & Hfill0 & Hfill12 & Hempty) => //=.
        edestruct (filled_twice k i lh0 l0 es0 besa les) as [lh2 Hminus] => //=.
        apply empty_base_same_true_depth in Hlh as <-. done.
        specialize (lh_minus_minus _ _ _ _ _ _ _ _ Hminus H Hfill12) ; intro Hfillm.
        move/lfilledP in Hfill0; inversion Hfill0; subst.
        move/lfilledP in Hfillm; inversion Hfillm; subst.
        * edestruct reduction_core as
            [(core & bc0 & ac0 & bc2 & ac2 & core' & Hbc0 & Hbc2 &
                Heqes & Heqes0 & Hbefs & Hafts &
                Hcore & Hes0')
            | (lht0 & lht1 & Hfill0' & Hfill1 & Hσ)].
          -- exact Hes.
          -- exact HLI.
          -- exact H3.
          -- exact H6.
          -- symmetry. exact H2.
          -- left.
             exists (bc0 ++ core' ++ ac0).
             repeat split.
             ++ eapply r_label.
                ** subst ; exact Hcore.
                ** instantiate (1 := LH_base bc0 ac0).
                   instantiate (1 := 0).
                   unfold lfilled, lfill.
                   rewrite Hbc0.
                   by rewrite Heqes.
                ** unfold lfilled, lfill.
                   by rewrite Hbc0.
             ++ eapply can_fill_base => //=.
                ** unfold lfilled, lfill.
                   rewrite H3.
                   repeat rewrite app_assoc.
                   rewrite Hbefs.
                   repeat rewrite - app_assoc.
                   rewrite Hafts.
                   rewrite (app_assoc bc2).
                   rewrite (app_assoc (bc2 ++ core')).
                   rewrite - (app_assoc bc2).
                   rewrite Hes0'.
                   done.
                ** eapply lh_minus_minus2.
                   --- exact Hminus.
                   --- exact H0.
                   --- unfold lfilled, lfill.
                       instantiate (1 := 0).
                       rewrite H6.
                       done. 
                   --- lia.
          -- right ; eexists ; split => //=.
             subst. by inversion Hσ. 
        * edestruct first_non_value_reduce as (vs' & e & aftes & Hvs & He & Heq) ;
            try exact Hes.
          rewrite Heq in H2.
          repeat rewrite cat_app in H2.
          repeat rewrite app_assoc in H2.
          repeat rewrite - (app_assoc (bef ++ vs')) in H2.
          rewrite - app_comm_cons in H2.
          apply first_values in H2 as (-> & <- & ->) => //=.
          2: by destruct He as [He | ->] => //; destruct e => //; destruct b.
          2: by apply const_list_concat.
          assert (lfilled (S k0) (LH_rec vs' n es'1 lh' aftes) es0 es).
          { rewrite Heq. apply/lfilledP. constructor => //. }
          edestruct lfilled_swap as [es'' Hfill'] ; first exact H2.
          assert (reduce s f es s' f' es'').
          { eapply r_label.
            exact HLI.
            exact H2.
            exact Hfill'. }
          left ; exists es''.
          repeat split => //=.
          eapply (can_fill_base i lh es'' _ les') => //=.
          -- unfold lfilled, lfill.
             rewrite H3.
             done.
          -- eapply lh_minus_minus2.
             ++ exact Hminus.
             ++ exact H0.
             ++ instantiate (1 := S k0). unfold lfilled, lfill ; fold lfill.
                unfold lfilled, lfill in Hfill' ; fold lfill in Hfill'.
                rewrite const_list_concat => //.
                rewrite Hvs in Hfill'.
                destruct (lfill k0 lh' es'0) ; last done.
                move/eqP in Hfill'; rewrite Hfill'.
                repeat rewrite app_assoc.
                repeat rewrite - app_assoc.
                done.
             ++ lia.
        * edestruct first_non_value_reduce as (vs' & e & aftes & Hvs & He & Heq) ;
            try exact Hes.
          rewrite Heq in H1.
          repeat rewrite cat_app in H1.
          repeat rewrite app_assoc in H1.
          repeat rewrite - (app_assoc (bef ++ vs')) in H1.
          rewrite - app_comm_cons in H1.
          apply first_values in H1 as (-> & <- & ->) => //=.
          2: by destruct He as [He | ->] => //; destruct e => //; destruct b.
          2: by apply const_list_concat.
          assert (lfilled (k - i) (LH_handler vs' hs lh' aftes) es0 es).
          { rewrite Heq. apply/lfilledP. constructor => //. }
          edestruct lfilled_swap as [es'' Hfill'] ; first exact H1.
          assert (reduce s f es s' f' es'').
          { eapply r_label.
            exact HLI.
            exact H1.
            exact Hfill'. }
          left ; exists es''.
          repeat split => //=.
          eapply (can_fill_base i lh es'' _ les') => //=.
          -- unfold lfilled, lfill.
             rewrite H3.
             done.
          -- eapply lh_minus_minus2.
             ++ exact Hminus.
             ++ exact H0.
             ++ instantiate (1 := k - i). unfold lfilled, lfill ; fold lfill.
                unfold lfilled, lfill in Hfill' ; fold lfill in Hfill'.
                rewrite const_list_concat => //.
                rewrite Hvs in Hfill'.
                destruct (lfill (k - i) lh' es'0) ; last done.
                move/eqP in Hfill'; rewrite Hfill'.
                repeat rewrite cat_app.
                repeat rewrite app_assoc.
                repeat rewrite - app_assoc.
                done.
             ++ lia.
        * edestruct first_non_value_reduce as (vs' & e & aftes & Hvs & He & Heq) ;
            try exact Hes.
          rewrite Heq in H1.
          repeat rewrite cat_app in H1.
          repeat rewrite app_assoc in H1.
          repeat rewrite - (app_assoc (bef ++ vs')) in H1.
          rewrite - app_comm_cons in H1.
          apply first_values in H1 as (-> & <- & ->) => //=.
          2: by destruct He as [He | ->] => //; destruct e => //; destruct b.
          2: by apply const_list_concat.
          assert (lfilled (k - i) (LH_prompt vs' ts hs lh' aftes) es0 es).
          { rewrite Heq. apply/lfilledP. constructor => //. }
          edestruct lfilled_swap as [es'' Hfill'] ; first exact H1.
          assert (reduce s f es s' f' es'').
          { eapply r_label.
            exact HLI.
            exact H1.
            exact Hfill'. }
          left ; exists es''.
          repeat split => //=.
          eapply (can_fill_base i lh es'' _ les') => //=.
          -- unfold lfilled, lfill.
             rewrite H3.
             done.
          -- eapply lh_minus_minus2.
             ++ exact Hminus.
             ++ exact H0.
             ++ instantiate (1 := k - i). unfold lfilled, lfill ; fold lfill.
                unfold lfilled, lfill in Hfill' ; fold lfill in Hfill'.
                rewrite const_list_concat => //.
                rewrite Hvs in Hfill'.
                destruct (lfill (k - i) lh' es'0) ; last done.
                move/eqP in Hfill'; rewrite Hfill'.
                repeat rewrite cat_app.
                repeat rewrite app_assoc.
                repeat rewrite - app_assoc.
                done.
             ++ lia.
      + assert (lh_true_depth lh0 < lh_true_depth lh) ; first lia.
        assert (lh_true_depth lh0 <= lh_true_depth lh) as Hk; first lia.
        eapply true_depth_leq_filled in Hk.
        2: exact H.
        2: exact Hfill.
        
        destruct (empty_base lh0) as [[l bef] aft] eqn:Hlh.
        eapply can_empty_base in H as (besa0 & Hfill0 & Hfill12 & Hempty) => //=.
        edestruct (filled_twice i k lh l es besa0 les) as [lh2 Hminus] => //=.
        apply empty_base_same_true_depth in Hlh as <-. lia.
        specialize (lh_minus_minus _ _ _ _ _ _ _ _ Hminus Hfill Hfill12) ; intro Hfillm.
        move/lfilledP in Hfill0; inversion Hfill0; subst.
        move/lfilledP in Hfillm; inversion Hfillm; subst.
        * exfalso; eapply true_depth_lt_minus => //.
        * edestruct first_non_value_reduce as (vs' & e & aftes & Hvs & He & Heq) ;
            try exact HLI.
          rewrite Heq in H2.
          repeat rewrite cat_app in H2.
          repeat rewrite app_assoc in H2.
          repeat rewrite - (app_assoc (bef ++ vs')) in H2.
          rewrite - app_comm_cons in H2.
          apply first_values in H2 as (-> & <- & ->) => //=.
          2: by destruct He as [He | ->] => //; destruct e => //; destruct b.
          2: by apply const_list_concat.
          apply const_list_split in H4 as [??].
          assert (lfilled (S k0) (LH_rec vs' n0 es'1 lh' aftes) es es0).
          { rewrite Heq. apply/lfilledP.
            constructor => //. } 
          assert (lfilled k lh0 es0 les).
          { eapply can_fill_base => //=.
            unfold lfilled, lfill => //=.
            rewrite H2.
            done. }
          destruct (length_lfilled_rec_or_same k lh0 es0 les) as [Hlenr | Heqes] => //=.
          assert (length_rec es0 < nnn) ; first lia.
          eapply IHnnn in H8 as [( es'' & (Hstep & _ & _) & Hfill0') | [lhtrap Htrap]] => //=.
          -- left ; exists es''.
             repeat split => //=.
             eapply lh_minus_plus.
             exact Hminus.
             instantiate (1 := k).
             lia.
             rewrite -H.
             unfold lfilled, lfill ; fold lfill.
             unfold lfilled, lfill in Hfill0' ; fold lfill in Hfill0'.
             rewrite Hvs in Hfill0'.
             rewrite const_list_concat => //. 
             destruct (lfill k0 lh' es'') ; last done.
             move/eqP in Hfill0'.
             rewrite - app_assoc.
             rewrite app_comm_cons.
             rewrite (app_assoc vs').
             rewrite - Hfill0'.
             done.
             eapply can_empty_base in H0 as (besa & Hfill1 & Hfill2 & _) => //=.
             move/lfilledP in Hfill1; inversion Hfill1; subst.
             done.
          -- right ; by eexists.
          -- destruct Heqes as (-> & -> & ->).
             move/lfilledP in H0; inversion H0; subst.
             rewrite /= cats0.
             apply IHHLI => //.
        * edestruct first_non_value_reduce as (vs' & e & aftes & Hvs & He & Heq) ;
            try exact HLI.
          rewrite Heq in H.
          repeat rewrite cat_app in H.
          repeat rewrite app_assoc in H.
          repeat rewrite - (app_assoc (bef ++ vs')) in H.
          rewrite - app_comm_cons in H.
          apply first_values in H as (-> & <- & ->) => //=.
          2: by destruct He as [He | ->] => //; destruct e => //; destruct b.
          2: by apply const_list_concat.
          apply const_list_split in H2 as [??].
          assert (lfilled (i - k) (LH_handler vs' hs lh' aftes) es es0).
          { rewrite Heq. apply/lfilledP.
            constructor => //. } 
          assert (lfilled k lh0 es0 les).
          { eapply can_fill_base => //=.
            unfold lfilled, lfill => //=.
            rewrite H.
            done. }
          destruct (length_lfilled_rec_or_same k lh0 es0 les) as [Hlenr | Heqes] => //=.
          assert (length_rec es0 < nnn) ; first lia.
          eapply IHnnn in H6 as [( es'' & (Hstep & _ & _) & Hfill0') | [lhtrap Htrap]] => //=.
          -- left ; exists es''.
             repeat split => //=.
             eapply lh_minus_plus.
             exact Hminus.
             instantiate (1 := k).
             lia.
             unfold lfilled, lfill ; fold lfill.
             unfold lfilled, lfill in Hfill0' ; fold lfill in Hfill0'.
             rewrite Hvs in Hfill0'.
             rewrite const_list_concat => //. 
             destruct (lfill (i - k) lh' es'') ; last done.
             move/eqP in Hfill0'.
             repeat rewrite cat_app.
             repeat rewrite app_assoc.
             rewrite - (app_assoc _ _ [_]).
             rewrite - (app_assoc bef).
             rewrite - (app_assoc vs').
             repeat rewrite cat_app in Hfill0'.
             rewrite - Hfill0'.
             rewrite - app_assoc.
             done.
             eapply can_empty_base in H0 as (besa & Hfill1 & Hfill2 & _) => //=.
             move/lfilledP in Hfill1; inversion Hfill1; subst.
             done.
          -- right ; by eexists.
          -- destruct Heqes as (-> & -> & ->).
             move/lfilledP in H0; inversion H0; subst.
             rewrite /= cats0.
             apply IHHLI => //.
        * edestruct first_non_value_reduce as (vs' & e & aftes & Hvs & He & Heq) ;
            try exact HLI.
          rewrite Heq in H.
          repeat rewrite cat_app in H.
          repeat rewrite app_assoc in H.
          repeat rewrite - (app_assoc (bef ++ vs')) in H.
          rewrite - app_comm_cons in H.
          apply first_values in H as (-> & <- & ->) => //=.
          2: by destruct He as [He | ->] => //; destruct e => //; destruct b.
          2: by apply const_list_concat.
          apply const_list_split in H2 as [??].
          assert (lfilled (i - k) (LH_prompt vs' ts hs lh' aftes) es es0).
          { rewrite Heq. apply/lfilledP.
            constructor => //. } 
          assert (lfilled k lh0 es0 les).
          { eapply can_fill_base => //=.
            unfold lfilled, lfill => //=.
            rewrite H.
            done. }
          destruct (length_lfilled_rec_or_same k lh0 es0 les) as [Hlenr | Heqes] => //=.
          assert (length_rec es0 < nnn) ; first lia.
          eapply IHnnn in H6 as [( es'' & (Hstep & _ & _) & Hfill0') | [lhtrap Htrap]] => //=.
          -- left ; exists es''.
             repeat split => //=.
             eapply lh_minus_plus.
             exact Hminus.
             instantiate (1 := k).
             lia.
             unfold lfilled, lfill ; fold lfill.
             unfold lfilled, lfill in Hfill0' ; fold lfill in Hfill0'.
             rewrite Hvs in Hfill0'.
             rewrite const_list_concat => //. 
             destruct (lfill (i - k) lh' es'') ; last done.
             move/eqP in Hfill0'.
             repeat rewrite cat_app.
             repeat rewrite app_assoc.
             rewrite - (app_assoc _ _ [_]).
             rewrite - (app_assoc bef).
             rewrite - (app_assoc vs').
             repeat rewrite cat_app in Hfill0'.
             rewrite - Hfill0'.
             rewrite - app_assoc.
             done.
             eapply can_empty_base in H0 as (besa & Hfill1 & Hfill2 & _) => //=.
             move/lfilledP in Hfill1; inversion Hfill1; subst.
             done.
          -- right ; by eexists.
          -- destruct Heqes as (-> & -> & ->).
             move/lfilledP in H0; inversion H0; subst.
             rewrite /= cats0.
             apply IHHLI => //.
    -  move/lfilledP in Hfill; inversion Hfill; subst;
      try (by lazymatch goal with
              | _ : (?vs ++ _ :: _)%SEQ = [_] |- _ =>
                  by do 2 destruct vs => //
              end).
       destruct vs; last by destruct vs, es => //; empty_list_no_reduce.
       destruct es; first by empty_list_no_reduce.
       destruct es => //.
       inversion H; subst.
       left; eexists. split.
       split; last done.

       eapply r_local.
       exact HLI.
       rewrite /lfilled /lfill /= //. 
  Qed.

End lfilled_reduce_properties.

