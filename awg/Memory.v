Require Import TLA.
Require Import Rules.
Require Import Arith.
Require Import ZArith.
Require Import Omega.
Require Import Setoid.
Require Import FunctionalExtensionality.
Require Import Basic.
Require Import Rules.

Open Scope tla.

Inductive Mode := Record | Play.

Module Type MemParams <: BasicParams.
  Parameter PatternIsh : Type.
  Parameter IsPattern : PatternIsh -> Prop.
  Parameter NilPattern : PatternIsh.
  Parameter NilPatternPattern : IsPattern NilPattern.
  Parameter EqNilPatternClassical : forall p, IsPattern p -> p = NilPattern \/ p <> NilPattern.
  Parameter MaxMemoryLen : nat.
  Parameter MaxMemoryLenGtZ : (0 < MaxMemoryLen)%nat.

  Fixpoint IsListPattern (ls : list PatternIsh) : Prop :=
    match ls with
      | nil => True
      | (cons h tl) => IsPattern h /\ IsListPattern tl
    end.

End MemParams.

Module ParamsFromMem (Params : MemParams) <: BasicParams.
  Definition PatternIsh := list Params.PatternIsh.
  Definition IsPattern := Params.IsListPattern.
  Definition NilPattern : PatternIsh := nil.
  Theorem NilPatternPattern : IsPattern NilPattern.
  Proof.
    unfold IsPattern, NilPattern.
    simpl. auto.
  Qed.
  Theorem EqNilPatternClassical : forall p, IsPattern p -> p = NilPattern \/ p <> NilPattern.
  Proof.
    intros p H.
    unfold NilPattern, IsPattern.
    destruct p. left; auto. right; intros F; inversion F.
  Qed.
End ParamsFromMem.

Module Memory (Params : MemParams).
  Import Params.

  Hint Resolve NilPatternPattern.

  Record St := {
      ready : bool;
      status : MemStatus;
      mode : Mode;
      memory : list PatternIsh;
      output : list PatternIsh}.

  Section Model.
    Variable st st' : St.
    Let ready' := (st').(ready). Let ready := st.(ready).
    Let status' := (st').(status). Let status := st.(status).
    Let mode' := (st').(mode). Let mode := st.(mode).
    Let memory' := (st').(memory). Let memory := st.(memory).
    Let output' := (st').(output). Let output := st.(output).

    Definition TypeInvariant := IsListPattern memory /\ IsListPattern output.

    Definition Initialize :=
      ready = false
      /\ ready' = true
      /\ (mode = Play -> output = nil)
      /\ match status' with
          | Valid => mode' = Record /\ memory' = nil
          | _ => mode' = mode /\ memory' = memory
         end
      /\ output' = output.

    Definition Reset :=
      ready' = false
      /\ memory' = nil
      /\ output' = nil
      /\ ignore st.

    Definition Flush :=
      ready = true
      /\ status = Valid
      /\ mode = Record
      /\ memory' = nil
      /\ output' = nil
      /\ ready' = ready
      /\ status' = status
      /\ mode' = mode.

    Definition Write p := 
      ready = true
      /\ status = Valid
      /\ mode = Record
      /\ (length memory < MaxMemoryLen)%nat
      /\ (p <> NilPattern -> memory' = cons p memory)
      /\ (p = NilPattern -> memory' = memory)
      /\ ready' = ready
      /\ status' = status
      /\ mode' = mode
      /\ output' = output.

    Definition StartPlay :=
      ready = true
      /\ status = Valid
      /\ mode = Record
      /\ output = nil
      /\ memory <> nil
      /\ mode' = Play
      /\ ready' = ready /\ status' = status /\ memory' = memory /\ output' = output.

    Definition DoPlay :=
      ready = true
      /\ status = Valid
      /\ mode = Play
      /\ exists h t, memory = cons h t
      /\ memory' = t
      /\ output' = cons h output
      /\ ready' = ready /\ status'= status /\ mode' = mode.

    Definition EndPlay :=
      ready = true
      /\ status = Valid
      /\ mode = Play
      /\ memory = nil
      /\ mode' = Record
      /\ output' = output
      /\ ready' = ready /\ status' = status /\ memory' = memory.

    Definition PowerOn :=
      ready = false
      /\ IsListPattern memory
      /\ (length memory <= MaxMemoryLen)%nat
      /\ output = nil.

    Definition Next :=
      Initialize
      \/ Reset
      \/ Flush
      \/ (exists p, IsPattern p /\ Write p)
      \/ StartPlay
      \/ DoPlay
      \/ EndPlay.
  End Model.

  Definition Fairness :=
     WF Initialize
     `/\ WF DoPlay
     `/\ WF EndPlay.

  Definition Spec := ` PowerOn `/\ [][Next] `/\ Fairness.

  Lemma Next_TypeInvariant : forall st st', TypeInvariant st
      -> Next st st' -> TypeInvariant st'.
  Proof.
    intros st st' tst next.
    unfold TypeInvariant in *.
    destruct tst as (memst,patst).
    destruct st, st'. simpl in *.
    destruct next as [
      (H0,(H1,(H2,(H3,H4))))
      |[(H0,(H1,(H2,H3)))
      |[(H0,(H1,(H2,(H3,(H4,(H5,(H6,H7)))))))
      |[(p,(isPatP,(H0,(H1,(H2,(H3,(H4,(H5,(H6,(H7,(H8,H9)))))))))))
      |[(H0,(H1,(H2,(H3,(H4,(H5,(H6,(H7,(H8,H9)))))))))
      |[(H0,(H1,(H2,(h,(t,(H4,(H5,(H6,(H7,(H8,H9))))))))))
      |(H0,(H1,(H2,(H3,(H4,(H5,(H6,(H7,H8))))))))
    ]]]]]];
    simpl in *.
    destruct status1; destruct H3 as (H3,H5); rewrite H5; rewrite H4; repeat split; auto.
    rewrite H1, H2; repeat split; auto.
    rewrite H3, H4; repeat split; auto.
    rewrite H9; split; auto.
    assert (H : p = NilPattern \/ p <> NilPattern). apply EqNilPatternClassical. auto.
    destruct H as [H|H]. apply H5 in H. rewrite H. auto.
    apply H4 in H. rewrite H. split; auto.
    rewrite H8, H9; repeat split; auto.
    rewrite H4 in memst. destruct memst as (iPt,memst).
    rewrite H6, H5; repeat split; auto.
    rewrite H8. rewrite H5. repeat split; auto.
  Qed.

  Theorem Spec_TypeInvariant : valid (Spec `=> [] ` TypeInvariant).
  Proof.
    apply tla_inv_gen.
    intros s H. destruct H as (H,_).
    unfold PowerOn, TypeInvariant in *; simpl in *.
    destruct H as (_,(H,(_,H0))). rewrite H0. repeat split; auto.
    intros s. apply Next_TypeInvariant.
  Qed.
(*
  Definition ValidIsDefined st := (st.(ready) = true /\ st.(status) = Valid) 
                                  -> exists lst, st.(memory) = lst.

  Lemma Next_ValidIsDefined : forall st st', ValidIsDefined st -> Next st st'
    -> ValidIsDefined st'.
  Proof.
    intros st st' valDef next H.
    destruct H as (H,H0).
    unfold ValidIsDefined in *.
    destruct next as [
    (_,(_,(H1,_)))
    |[(H1,_)
    |[(_,(_,(_,(H1,_))))
    |[(p,(isPatp,(memls,(H1,(_,(_,(_,(_,(H2,(H3,_))))))))))
    |[(H1,(H2,(_,(_,(_,(_,(_,(H3,_))))))))
    |[(_,(_,(_,(_,(t,(_,(H1,_)))))))
    |(_,(_,(_,(H1,(_,(_,(_,(_,H2))))))))]]]]]]; simpl in *.
    apply H1 in H0. destruct H0 as (_,H0). exists nil. auto.
    rewrite H1 in H. inversion H.
    exists nil. auto.
    assert (H4 : p = NilPattern \/ p <> NilPattern). apply EqNilPatternClassical; auto.
    destruct H4 as [H4|H4]. exists memls. apply H3 in H4. rewrite H4. auto.
    exists ((p :: memls)%list). apply H2 in H4. auto.
    rewrite H3. apply valDef. split; auto.
    exists t. auto.
    rewrite H2. exists nil; auto.
  Qed.

  Theorem Spec_ValidIsDefined : valid (Spec `=> [] ` ValidIsDefined).
  Proof.
    apply tla_inv_gen.
    intros s H H0. destruct H0 as (H0,H1). destruct H as ((H,_),_). rewrite H0 in H.
    inversion H.
    intros s. simpl. apply Next_ValidIsDefined.
  Qed.
*)
  Module FROMMEM := ParamsFromMem (Params).
  Module BASIC := Basic.Basic (FROMMEM).

  Definition refinement_mapping (st : St) : BASIC.St := 
    match st with
      | {|  ready := ready0; 
            status := status0; 
            memory := memory0; 
            mode := mode0;
            output := output0 |} =>
              {|  BASIC.ready := ready0;
                  BASIC.status := status0;
                  BASIC.memory := match mode0 with
                                  | Record => memory0
                                  | Play => ((List.rev output0) ++ memory0)%list
                                  end;
                  BASIC.output := match mode0 with
                                  | Record => List.rev output0
                                  | Play => nil
                                  end |}
    end.

  Lemma Next_refinement : forall st st', TypeInvariant st -> Next st st' ->
      (BASIC.Next (refinement_mapping st) (refinement_mapping st') \/
      (refinement_mapping st = refinement_mapping st')).
  Proof.
    intros st st' typInv next.
    unfold Next, BASIC.Next in *.
    destruct next as [
      (H0,(H1,(H2,(H3,H4))))
      |[(H0,(H1,(H2,H3)))
      |[(H0,(H1,(H2,(H3,(H4,(H5,(H6,H7)))))))
      |[(p,(isPatP,(H0,(H1,(H2,(H3,(H4,(H5,(H6,(H7,(H8,H9)))))))))))
      |[(H0,(H1,(H2,(H3,(H4,(H5,(H6,(H7,(H8,H9)))))))))
      |[(H0,(H1,(H2,(h,(t,(H4,(H5,(H6,(H7,(H8,H9))))))))))
      |(H0,(H1,(H2,(H3,(H4,(H5,(H6,(H7,H8))))))))
    ]]]]]].

    left. left. 
    unfold BASIC.Initialize.
    destruct st, st'; simpl in *. rewrite <- H0, H1, H4.
    destruct status1; repeat split; auto; destruct H3 as (H3,H5); 
    try (rewrite H3); try (rewrite H5); auto.
    destruct mode0; auto; intuition; rewrite H; auto.

    left. right. left.
    unfold BASIC.Reset, ignore.
    destruct st, st'; simpl in *. rewrite H0, H1, H2; simpl.
    destruct mode1; repeat split; auto.

    left. right. right. left.
    unfold Flush, BASIC.Flush in *.
    destruct st, st'; simpl in *.
    rewrite H7.
    rewrite H6, H5, H4, H3, H2, H1. repeat split; auto.

    left. right. right. right. left.
    unfold Write, BASIC.Write in *.
    assert (H10 : p = NilPattern \/ p <> NilPattern). apply EqNilPatternClassical; auto.
    destruct st, st'; simpl in *.
    rewrite H8. rewrite H0, H1, H2, H6, H7, H9, H1. 
    destruct H10 as [H10|H10].
    apply H5 in H10.
    rewrite H10. exists FROMMEM.NilPattern; intuition.
    apply H4 in H10. rewrite H10.
    destruct typInv as (ty,_). simpl in ty.
    exists ((p :: memory0)%list). repeat split; auto. intros H; inversion H.

    right.
    destruct st, st'. simpl in *.
    rewrite H9, H8, H7, H6, H5, H3, H2, H1, H0. simpl in *.
    auto.

    right.
    destruct st, st'. simpl in *.
    rewrite H9, H8, H7, H6, H5, H4, H2, H1, H0.
    simpl.
    rewrite <- List.app_assoc.
    simpl. auto.

    left. right. right. right. right.
    unfold BASIC.Run.
    destruct st, st'; simpl in *.
    rewrite H8, H7, H6, H5, H4, H3, H2, H1, H0.
    repeat split; auto.
    rewrite List.app_nil_r. auto.
    rewrite List.app_nil_r in H. auto.
  Qed.


End Memory.

