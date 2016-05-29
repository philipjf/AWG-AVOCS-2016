Require Import TLA.
Require Import Rules.
Require Import Arith.
Require Import ZArith.
Require Import Omega.
Require Import Setoid.
Require Import FunctionalExtensionality.

Open Scope Z.
Open Scope tla.

Definition ignore {A : Type} (x : A) := True.

Module Type BasicParams.
  Parameter PatternIsh : Type.
  Parameter IsPattern : PatternIsh -> Prop.
  Parameter NilPattern : PatternIsh.
  Parameter NilPatternPattern : IsPattern NilPattern.
  Parameter EqNilPatternClassical : forall p, IsPattern p -> p = NilPattern \/ p <> NilPattern.
End BasicParams.

Inductive MemStatus : Type := Valid | InValid.

Module Basic (Params : BasicParams).
  Import Params.
  Hint Resolve NilPatternPattern.

  Record St := {
      ready : bool;
      status : MemStatus;
      memory : PatternIsh;
      output : PatternIsh}.
  Section Model.
    Variable st st' : St.

    Let ready' := (st').(ready). Let ready := st.(ready).
    Let status' := (st').(status). Let status := st.(status).
    Let memory' := (st').(memory). Let memory := st.(memory).
    Let output' := (st').(output). Let output := st.(output).

    Definition TypeInvariant :=
      IsPattern memory
      /\ IsPattern output.

    Definition Initialize :=
      ready = false
      /\ ready' = true
      /\ match status' with
         | Valid => memory' = NilPattern
         | _ => memory = memory' end
      /\ output = output'.

    Definition Reset :=
      ready' = false
      /\ IsPattern memory'
      /\ output' = NilPattern
      /\ ignore st. (* this is to make it include the unprimed and
                       not just primed variables so Reset is a action
                       not a predicate *)

    Definition Flush :=
      ready = true
      /\ status = Valid
      /\ memory' = NilPattern
      /\ output' = NilPattern
      /\ ready = ready' /\ status = status'.

    Definition Write p :=
      ready = true
      /\ status = Valid
      /\ (p <> NilPattern -> memory' = p)
      /\ (p = NilPattern -> memory' = memory)
      /\ ready' = ready /\ status' = status /\ output' = output.

    Definition Run :=
      ready = true
      /\ status = Valid
      /\ (memory <> NilPattern -> (output' = memory /\ memory' = NilPattern))
      /\ (memory = NilPattern -> (output' = output /\ memory' = memory))
      /\ ready' = ready /\ status' = status.

    Definition PowerOn :=
      ready = false
      /\ output = NilPattern
      /\ IsPattern memory.

    Definition Next :=
      Initialize
      \/ Reset
      \/ Flush
      \/ (exists p, IsPattern p /\ Write p)
      \/ Run.
    
  End Model.

  Definition Fairness := WF Initialize.

  Definition Spec := `PowerOn `/\ [][Next] `/\ Fairness.

  Definition ResetEnabled := ENABLED Reset. (* observe though that reset is always enabled *)

  Definition CommandEnabled := ENABLED Run
                                       `/\ ENABLED Flush
                                       `/\ FORALL (fun p =>
                                                     (` (fun _ => IsPattern p))
                                                     `=> ENABLED (fun st st' => Write st st' p)). 

  Definition CommandsEnabledIffValid := CommandEnabled `<=> ` (fun st => st.(ready) = true /\ st.(status) = Valid).

  Lemma Next_TypeInvariant : forall s s', Next s s' -> TypeInvariant s -> TypeInvariant s'.
  Proof.
    intros s s' H H0.
    destruct H0 as (H0,H1).
    destruct H as [(H,(H2,(H3,H4)))
                  |[(H,(H2,(H3,_)))
                   |[(H,(H2,(H3,(H4,(H5,H6)))))
                    |[(p,(H,(H2,(H3,(H4,(H5,(H6,(H7,H8))))))))
                     |(H,(H2,(H3,(H4,(H5,H6)))))]]]]; split; auto.
    destruct (status s'). 
        rewrite H3; auto. rewrite <- H3; auto.
    rewrite <- H4; auto.
    rewrite H3; auto.
    rewrite H3; auto.
    rewrite H4; auto.
    pose (H9 := EqNilPatternClassical p H).
    destruct H9 as [H9|H9]. apply H5 in H9. rewrite H9; auto.
    apply H4 in H9. rewrite H9; auto.
    rewrite H8; auto.
    pose (H7 := EqNilPatternClassical (memory s) H0).
    destruct H7 as [H7|H7]. apply H4 in H7.
    destruct H7 as (H7,H8). rewrite H8; auto.
    apply H3 in H7. destruct H7 as (H7,H8).
    rewrite H8. auto.
    pose (H7 := EqNilPatternClassical (memory s) H0).
    destruct H7 as [H7|H7]. apply H4 in H7.
    destruct H7 as (H7,H8). rewrite H7; auto.
    apply H3 in H7. destruct H7 as (H7,H8).
    rewrite H7. auto.
  Qed.
  
  Theorem Spec_then_TypeInvariant : valid (Spec `=> [] `TypeInvariant).
  Proof.
    apply tla_inv_gen.
    intros s H.
    destruct H as ((H,(H0,H1)),_).
    repeat split; auto. rewrite H0; auto.
    intros s H H0.
    simpl.
    assert (R: s @ 1%behavior 0%nat = s 1%nat). auto.
    rewrite R.
    apply Next_TypeInvariant with (s 0%nat); auto.
  Qed.

  Theorem Spec_then_ResetEnabled : valid (Spec `=> [] ResetEnabled).
  Proof.
    intros s H.
    apply ModusPonens with (`PowerOn `/\ [][Next]).
    apply tla_inv.
    intros x H0. unfold Reset, PowerOn, ignore in *. exists x.
    destruct H0 as (H0,(H1,H2)). rewrite H1. repeat split; trivial.
    intros x y H0 H1. destruct H0 as (st',H0).
    exists st'. destruct H0 as (H0,(H2,(H4,H5))). repeat split; trivial.
    destruct H as (H,(H1,H2)).
    split; trivial.
  Qed.


  Lemma Next_CommandsEnabledIffValid : forall s, TypeInvariant (s 0%nat) ->
                                                 eval CommandsEnabledIffValid s ->
                                                 Next (s 0%nat) (s 1%nat) ->
                                                 eval CommandsEnabledIffValid (s @ 1).
  Proof.
    intros s H H0 H1.
    simpl in *.
    destruct H as (is_pat_mem,is_pat_out).
    destruct H0 as (H0,H2).
    split.
    intros H.
    destruct H as ((st',(H,(H3,_))),_). split; auto.
    intros H.
    destruct H as (ready_next_true,status_next_valid).
    assert (H3 : TypeInvariant (s 1%nat)). apply Next_TypeInvariant with (s 0%nat); auto; split; auto.
    destruct H3 as (is_pat_next_mem,is_pat_next_out).
    assert (H3 : memory (s @ 1%behavior 0%nat) = NilPattern \/ memory (s @ 1%behavior 0%nat) <> NilPattern).  apply EqNilPatternClassical; auto.
    repeat split.
    unfold Run. destruct H3 as [H3|H3]. rewrite H3.
    set (nst := {|
      ready := ready (s @ 1%behavior 0%nat);
      status := status (s @ 1%behavior 0%nat);
      memory := NilPattern;
      output := output (s @ 1%behavior 0%nat)|}).
    exists nst; repeat split; unfold nst; auto; intuition.
    set (nst := {|
      ready := ready (s @ 1%behavior 0%nat);
      status := status (s @ 1%behavior 0%nat);
      memory := NilPattern;
      output := memory (s @ 1%behavior 0%nat)|}).
    exists nst; repeat split; unfold nst; auto; intuition.
    unfold Flush.
    set (nst := {|
      ready := ready (s @ 1%behavior 0%nat);
      status := status (s @ 1%behavior 0%nat);
      memory := NilPattern;
      output := NilPattern|}).
    exists nst; repeat split; unfold nst; auto.
    intros x H.
    unfold Write.
    assert (H4 : x = NilPattern \/ x <> NilPattern). apply EqNilPatternClassical; auto.
    destruct H4 as [H4|H4].
    set (nst := {|
      ready := ready (s @ 1%behavior 0%nat);
      status := status (s @ 1%behavior 0%nat);
      memory :=  memory (s @ 1%behavior 0%nat);
      output := output (s @ 1%behavior 0%nat)|}).
    exists nst; repeat split; unfold nst; auto; intuition.
    set (nst := {|
      ready := ready (s @ 1%behavior 0%nat);
      status := status (s @ 1%behavior 0%nat);
      memory :=  x;
      output := output (s @ 1%behavior 0%nat)|}).
    exists nst; repeat split; unfold nst; auto; intuition.
  Qed.

  Theorem Spec_then_CommandsEnabledIffValid : valid (Spec `=> [] CommandsEnabledIffValid).
  Proof.
    assert (G : valid (Spec  `=> [] (CommandsEnabledIffValid `/\ `TypeInvariant))).
    apply tla_inv_gen.
    intros s H.
    split. simpl. simpl in H. destruct H as ((H,(H0,H1)),(H2,H3)).
    rewrite H.
    split; intros H4. destruct H4 as ((st',(H4,_)),_).
    rewrite H4 in H. inversion H.
    destruct H4 as (H4,_). inversion H4.
    assert (H0 : forall n, eval ` TypeInvariant (s @ n)). apply Spec_then_TypeInvariant; auto.
    specialize H0 with 0%nat. auto.
    (* induction case *)
    intros s H H0.
    destruct H as (H,H1).
    split.
    apply Next_CommandsEnabledIffValid; auto.
    apply Next_TypeInvariant with (s 0%nat); auto.
    intros s H n.
    apply G in H.
    simpl in H.
    specialize H with n. destruct H as (H,H1).
    auto.
  Qed.
  
End Basic.

