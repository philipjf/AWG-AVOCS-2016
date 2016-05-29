Require Import TLA.
Require Import Rules.
Require Import Arith.
Require Import ZArith.
Require Import Omega.
Require Import Setoid.
Require Import FunctionalExtensionality.
Require Import Basic.
Require Import Rules.

Open Scope Z.
Open Scope tla.

Definition ignore {A : Type} (x : A) := True.

Module Command (Params : BasicParams).
  Import Params.

  Hint Resolve NilPatternPattern.
  
  Inductive Control : Type := Ready | Busy | Done.
  Inductive Command : Type :=
  | Flush : Command
  | Write : PatternIsh -> Command
  | Run : Command.
  Definition IsCommand (c : Command) : Prop := match c with
                                                 | Write p => IsPattern p
                                                 | _ => True
                                                end.


  Record St := {
      ready : bool;
      status : MemStatus;
      ctrl : Control;
      cmd : Command;
      memory : PatternIsh;
      output : PatternIsh}.

  Section Model.
    Variable st st' : St.

    Let ready' := (st').(ready). Let ready := st.(ready).
    Let status' := (st').(status). Let status := st.(status).
    Let ctrl' := (st').(ctrl). Let ctrl := st.(ctrl).
    Let cmd' := (st').(cmd). Let cmd := st.(cmd).
    Let memory' := (st').(memory). Let memory := st.(memory).
    Let output' := (st').(output). Let output := st.(output).

    Definition TypeInvariant :=
      IsCommand cmd
      /\ IsPattern memory
      /\ IsPattern output.

    Definition Initialize :=
      ready = false
      /\ ready' = true
      /\ ctrl' = Ready
      /\ match status' with
         | Valid => memory' = NilPattern
         | _ => memory = memory' end
      /\ output = output'
      /\ cmd = cmd'.

    Definition Reset :=
      ready' = false
      /\ IsPattern memory'
      /\ IsCommand cmd'
      /\ output' = NilPattern
      /\ ignore st. (* this is to make it include the unprimed and
                       not just primed variables so Reset is a action
                       not a predicate *)
    Definition Req c :=
      ready = true
      /\ status = Valid
      /\ ctrl = Ready
      /\ cmd' = c
      /\ ctrl' = Busy
      /\ ready = ready' /\ status = status' /\ memory = memory' /\ output = output'.

    Definition DoFlush :=
      cmd = Flush
      /\ memory' = NilPattern
      /\ output' = NilPattern.

    Definition DoWrite :=
      (exists p, cmd = Write p
                 /\ (p <> NilPattern -> memory' = p)
                 /\ (p = NilPattern -> memory' = memory))
      /\ output = output'.

    Definition DoRun :=
      cmd = Run
      /\ (memory <> NilPattern -> (output' = memory /\  memory' = NilPattern))
      /\ (memory = NilPattern -> (output' = output /\ memory' = memory)).

    Definition Do :=
      ready = true
      /\ status = Valid
      /\ ctrl = Busy
      /\ (DoFlush \/ DoWrite \/ DoRun)
      /\ ctrl' = Done
      /\ (ready' = ready /\ status' = status /\ cmd' = cmd).

    Definition Resp :=
      ready = true
      /\ status = Valid
      /\ ctrl = Done
      /\ ctrl' = Ready
      /\ (ready' = ready
          /\ status' = status
          /\ cmd' = cmd
          /\ memory' = memory
          /\ output' = output).

    Definition PowerOn :=
      ready = false
      /\ IsCommand cmd
      /\ IsPattern memory
      /\ output = NilPattern.

    Definition Next :=
      Initialize
      \/ Reset
      \/ (exists c, IsCommand c /\ Req c)
      \/ Do
      \/ Resp.

  End Model.

  Definition Fairness :=
    WF Initialize
    `/\ WF Do
    `/\ WF Resp.

  Definition Spec := `PowerOn `/\ [][Next] `/\ Fairness.

  Lemma Next_TypeInvariant : forall st st', TypeInvariant st -> Next st st' -> TypeInvariant st'.
  Proof.
    intros st st' H H0.
    destruct st.
    destruct st'.
    unfold TypeInvariant in H. simpl in H.
    destruct H as (IsCmd_cmd0,(IsPat_memy0,IsPat_out0)).
    destruct H0 as [(_,(_,(_,(H0,(out_unchanged,cmd_unchanged)))))
                   |[(_,(IsPat_mem1,(IsPat_cmd1,(out1_nilPat,_))))
                    |[(c,(isCommand_c,(_,(_,(_,(cmd1_c,(_,(_,(_,(mem_unchanged,out_unchanged))))))))))
                     |[(_,(_,(_,([(_,(mem1_nilPat,out1_nilPat))
                                 |[((p,(cmd0_writeP,(p_ifnotnilPat,p_ifNilPat))),out_unchanged)
                                  |(_,(mem0_ifnotnilPat,mem0_ifNilPat))]],(_,(_,(_,cmd_unchanged)))))))
                      |(_,(_,(_,(_,(_,(_,(cmd_unchanged,(mem_unchanged,out_unchanged))))))))]]]]; simpl in *; unfold TypeInvariant; simpl;

    try (rewrite cmd_unchanged in *);
    try (rewrite out_unchanged in *);
    try (rewrite mem_unchanged in *);
    try (rewrite out1_nilPat);
    try (rewrite mem1_nilPat);
    try (rewrite cmd1_c);
    try (rewrite cmd0_writeP in *); repeat split; auto.

    destruct status1; rewrite H0 in *;  auto.

    unfold IsCommand in *.
    assert (H : p = NilPattern \/ p <> NilPattern). apply EqNilPatternClassical; auto.
    destruct H as [H|H].
    apply p_ifNilPat in H; rewrite H; auto.
    apply p_ifnotnilPat in H; rewrite H; auto.

    assert (H : memory0 = NilPattern \/ memory0 <> NilPattern). apply EqNilPatternClassical; auto.
    destruct H as [H|H].
    apply mem0_ifNilPat in H. destruct H as (H,H0). rewrite H0; auto.
    apply mem0_ifnotnilPat in H. destruct H as (H,H0). rewrite H0; auto.

    assert (H : memory0 = NilPattern \/ memory0 <> NilPattern). apply EqNilPatternClassical; auto.
    destruct H as [H|H].
    apply mem0_ifNilPat in H. destruct H as (H,H0). rewrite H; auto.
    apply mem0_ifnotnilPat in H. destruct H as (H,H0). rewrite H; auto.
  Qed.

  Theorem Spec_TypeInvariant : valid (Spec `=> [] ` TypeInvariant).       
  Proof.
    apply tla_inv_gen.
    intros s H.
    destruct H as ((H,(H0,(H1,H2))),_). simpl in *.
    repeat split; auto; rewrite H2; auto.
    intros s H H0.  apply Next_TypeInvariant with (s 0%nat); auto.
  Qed.

  Module BASIC := Basic.Basic Params.


  Definition refinement_mapping : St -> BASIC.St :=
    fun x => match x with
               | {| ready := ready0;
                    status := status0;
                    output := output0;
                    memory := memory0 |} =>
                 {|
                   BASIC.ready := ready0;
                   BASIC.status := status0;
                   BASIC.memory := memory0;
                   BASIC.output := output0 |}
             end.

  Lemma refines_Next : forall st st',
                          TypeInvariant st
                          -> Next st st'
                          -> (BASIC.Next
                                (refinement_mapping st)
                                (refinement_mapping st') \/
                              refinement_mapping st = refinement_mapping st').
  Proof.
    intros st st' typeInvSt H.
    destruct typeInvSt as (isCommandSt,(isPatternMemSt,isPatternOutSt)).
    unfold Next in *.
    unfold BASIC.Next in *.
    Ltac break_up := unfold BASIC.Initialize, BASIC.Reset, BASIC.Flush, BASIC.Write, BASIC.Run in *;
      unfold Initialize, Reset, Req, Do, Resp in *.
    destruct H as [H|[H|[(c,(isComc,H))|[H|H]]]].
    left. left.  break_up; destruct st, st'; simpl in *.
    destruct H as (H,(H1,(H2,(H3,(H4,H5))))).
    destruct status1; repeat split; auto.
    left. right. left. break_up; destruct st, st'; simpl in *.
    destruct H as (H,(H1,(H2,(H3,H4)))); repeat split; auto.
    right. break_up; destruct st, st'; simpl in *.
    destruct H as (_,(_,(_,(_,(_,(H4,(H5,(H6,H7)))))))).
    rewrite H4, H5, H6, H7; auto.
    destruct st. simpl. 
    destruct H as (H,(H0,(H1,([H2|[H2|H2]],(H3,(H4,(H5,H6))))))); destruct cmd0 as [|p|];
    unfold DoFlush,DoWrite,DoRun in *; simpl in *.
    left. right. right. left.
    break_up; destruct st'; simpl in *.
    destruct H2 as (_,(H2,H7)).
    repeat split; auto.
    destruct H2 as (H2,_); inversion H2.
    destruct H2 as (H2,_); inversion H2.
    destruct H2 as ((p0,(H2,_)),_); inversion H2.
    destruct H2 as ((p0,(H2,(H7,H8))),H9).
    left. right. right. right. left. exists p.
    assert (H10 : p = p0). inversion H2; auto.
    rewrite H10 in *.
    repeat split; auto; destruct st'; simpl in *; auto.
    destruct H2 as ((p0,(H2,_)),_); inversion H2.
    destruct H2 as (H2,_); inversion H2.
    destruct H2 as (H2,_); inversion H2.
    destruct H2 as (_,(H2,H7)).
    left. do 4 right.
    destruct st'; repeat split; simpl in *; auto; intuition.
    right.
    destruct H as (H,(H1,(H2,(H3,(H4,(H5,(H6,(H7,H8)))))))).
    destruct st, st'; simpl in *. rewrite H4, H5, H7, H8. auto.
  Qed.


  Lemma refines_init : forall st, PowerOn st -> BASIC.PowerOn (refinement_mapping st).
  Proof.
    intros st H.
    unfold PowerOn, BASIC.PowerOn in *.
    destruct H as (H,(H0,(H1,H2))).
    destruct st; simpl in *.
    repeat split; auto.
  Qed.


  Theorem refines : valid (Spec `=> (map refinement_mapping BASIC.Spec)).
  Proof.
    intros s H.
    assert (tyInv : eval ([] `TypeInvariant) s). apply Spec_TypeInvariant in H; auto.
    destruct H as (init,(next,fairness)).
    rewrite map_eval.
    unfold BASIC.Spec.
    split. rewrite <- map_eval. apply refines_init; auto.
    split. rewrite <- map_eval. simpl.
    intros n. simpl in next. specialize next with n.
    destruct next as [H|H].
    apply refines_Next; auto; apply tyInv.
    right; rewrite H; trivial.
    assert (H : forall s s',Initialize s s' 
        -> BASIC.Initialize (refinement_mapping s) (refinement_mapping s')).
    intros s0 s1 H. destruct s0. destruct s1.
    unfold Initialize in H. unfold BASIC.Initialize. simpl in *.
    destruct H as (H,(H1,(H2,(H3,(H4,H5))))).
    destruct status1; repeat split; auto.
    apply RefineWF with Initialize.
    assumption.
    intros s0 s1 H0. left. intros H2. destruct H2 as (H2,(H3,H4)).
    destruct s0. destruct s1. simpl in *. rewrite H2 in *.
    rewrite H3 in *. inversion H0.
    intros s0 H1.
    destruct H1 as (s',(H1,(H3,(H4,H5)))).
    exists ({|ready := true;
              status := BASIC.status s';
              ctrl := Ready;
              cmd := cmd s0;
              memory := BASIC.memory s';
              output := output s0|}).
    destruct s0, s'. simpl in *.
    repeat split; auto.
    destruct fairness as (WF_init,_); auto.
  Qed.

  Definition ResetEnabled := ENABLED Reset.


  Lemma Next_ResetEnabled : forall st st',
                          (exists s, Reset st s) 
                          -> Next st st' 
                          -> exists s, Reset st' s.
  Proof.
    intros st st' H next.
    destruct st, st'.
    unfold Reset.
    destruct H as (s,H). exists s. unfold Reset in H.
    repeat split; intuition; auto.
  Qed.

  Theorem Spec_ResetEnabled : valid (Spec `=> [] ResetEnabled).
  Proof.
    apply tla_inv_gen.
    intros s H. destruct H as ((H,(H1,(H2,H3))),_).
    simpl.
    exists ({|ready := false;
              status := (s 0%nat).(status);
              ctrl := (s 0%nat).(ctrl);
              cmd := (s 0%nat).(cmd);
              memory := (s 0%nat).(memory);
              output := NilPattern|}).
    unfold Reset; simpl; repeat split; auto.
    intros s. apply Next_ResetEnabled.
  Qed.

  Definition IsCommand' {T} c := ` fun (x : T) => IsCommand c.

  Definition CommandsEnabled := E_ForallRigid (fun c => IsCommand' c 
                                  `=> ENABLED (fun a b => Req a b c)).

  Definition CommandsEnabledIffValidAndReady := CommandsEnabled `<=> 
                                                ` fun st => st.(ready) = true
                                                         /\ st.(status) = Valid
                                                         /\ st.(ctrl) = Ready.


  Lemma Next_CommandsEnabledIffValidAndReady : forall st st',
      ((forall c, IsCommand c -> exists s, Req st s c) <-> (st.(ready) = true
                                                         /\ st.(status) = Valid
                                                         /\ st.(ctrl) = Ready))
      -> Next st st'
      -> (forall c, IsCommand c -> exists s, Req st' s c) <-> ((st').(ready) = true
                                                         /\ (st').(status) = Valid
                                                         /\ (st').(ctrl) = Ready).
  Proof.
    intros st st' H next.
    split.

    intros H0.
    assert (H1 : exists s : St, Req st' s Flush). apply H0; simpl; auto.
    destruct H1 as (s,H1). unfold Req in H1. repeat split; intuition; auto.


    intros H0 c isCmdC. destruct H0 as (H0,(H1,H2)).
    exists ({| ready := ready st';
               status := status st';
               ctrl := Busy;
               cmd := c;
               memory := memory st';
               output := output st'|}).
    repeat split; simpl; auto.
  Qed.


  Theorem Spec_CommandsEnabledIffValidAndReady : valid (Spec `=> [] CommandsEnabledIffValidAndReady).
  Proof.
    apply tla_inv_gen.
    intros s H. destruct H as (H,_).
    split. intros H1. simpl in H1.
    assert (H2 : exists st' : St, Req (s 0%nat) st' Flush). apply H1; auto; unfold IsCommand; auto.
    destruct H2 as (st', H2). unfold Req in H2. repeat split; intuition; auto.
    intros H1 c H2. simpl in H2.
    destruct H1 as (H1,(H3,H4)).
    unfold Req.
    exists ({|  ready := ready (s O);
                status := status (s O);
                ctrl := Busy;
                cmd := c;
                memory := memory (s O);
                output := output (s O)|}).
    repeat split; simpl; auto.
    intros s. apply Next_CommandsEnabledIffValidAndReady.
  Qed.

  Definition CommandsComplete := ` (fun st => st.(ctrl) = Busy) `~> ` (fun st => st.(ctrl) = Ready).

  Lemma Spec_NotBad : valid (Spec `=> [] ` fun st => ~ (st.(ready) = true 
                                                        /\ st.(status) = InValid
                                                        /\ (st.(ctrl) = Busy \/ st.(ctrl) = Done))).
  Proof.
    apply tla_inv_gen.
    intros s H F. destruct H as (H,_).
    destruct H as (H,_). destruct F as (F,_). rewrite F in H. inversion H.
    intros s H next F.
    destruct F as (rt,(si,cb)). simpl in H.
    destruct next as [(_,(_,(F,_)))
                     |[(F,_)
                     |[(c,(isC,(_,(F0,(_,(_,(_,(_,(F1,_)))))))))
                     |[(_,(F0,(_,(_,(_,(_,(F1,_)))))))
                     |(_,(F0,(_,(_,(_,(F1,_))))))]]]]; unfold shift in *; simpl in *.
    destruct cb as [cb|cb].
    assert (W : Busy = Ready). rewrite <- cb; rewrite <- F; auto. inversion W.
    assert (W : Done = Ready). rewrite <- cb; rewrite <- F; auto. inversion W.
    assert (W : true = false). rewrite <- rt; rewrite <- F; auto. inversion W.
    assert (W : InValid = Valid). rewrite <- si; rewrite <- F0; rewrite F1; auto. inversion W.
    assert (W : InValid = Valid). rewrite <- si; rewrite <- F0; rewrite <- F1; auto. inversion W.
    assert (W : InValid = Valid). rewrite <- si; rewrite <- F0; rewrite <- F1; auto. inversion W.
  Qed.

  Definition IsReady st := st.(ctrl) = Ready.
  Definition IsBusy st := st.(ctrl) = Busy.
  Definition IsDone st := st.(ctrl) = Done.
  Definition IsValid st := st.(status) = Valid.
  Definition IsInvalid st := st.(status) = InValid.
  Definition ReadyTrue st := st.(ready) = true.
  Definition ReadyFalse st := st.(ready) = false.


  Lemma Spec_ReadyFalseLeadstoReady : valid (Spec `=> ((` ReadyFalse) `~> ` IsReady)).
  Proof.
    intros s spec.
    assert (H : eval (([]<> ` IsReady) `\/ ([]<> `ReadyTrue)) s).
    destruct spec as (_,(_,([wfI|wfI],_))); simpl in *; unfold Initialize in *; 
    unfold IsReady; unfold ReadyFalse.
    left. intros n. specialize wfI with n. destruct wfI as (m,((_,(_,(wfI,_))),_)).
    exists (S m). rewrite <- wfI; auto.
    right. intros n. specialize wfI with n.
    destruct wfI as (m,wfI).
    assert (F : ready ((s @ n) @ m%behavior 0%nat) = true \/ ready ((s @ n) @ m%behavior 0%nat) = false).
    destruct (ready ((s @ n) @ m%behavior 0%nat)); auto.
    destruct F as [F|F]. exists m; auto.
    exfalso. apply wfI.
    exists ({| ready := true;
               ctrl := Ready;
               status := Valid;
               memory := NilPattern;
               output := output ((s @ n) @ m%behavior 0%nat);
               cmd := cmd ((s @ n) @ m%behavior 0%nat)|}).
    repeat split; simpl; auto.
    destruct H as [H|H].
    simpl in *; intros n; specialize H with n; auto.
    apply deriveLeadsTo.
    intros n H0.
    destruct spec as (_,(spec,_)).
    simpl in *. unfold ReadyFalse in *. unfold IsReady in *. specialize spec with n.
    destruct spec as [
    [next
    |[next
    |[(c,(_,(H1,_)))
    |[(H1,_)
    |(H1,_)]]]]
    |next].
    firstorder.
    firstorder.
    rewrite H0 in H1. inversion H1.
    rewrite H0 in H1. inversion H1.
    rewrite H0 in H1. inversion H1.
    left. rewrite next in H0. rewrite <- H0. auto.
    clear spec.
    simpl in *. intros n. specialize H with n.
    destruct H as (m,H). exists m. unfold ReadyTrue in *. unfold ReadyFalse in *.
    rewrite H; intros F; inversion F.
  Qed.

  Lemma Spec_ValidAndDoneLeadsToReady : valid (Spec `=> 
          ((` ReadyTrue `/\ ` IsValid `/\ ` IsDone) `~> ` IsReady)).
  Proof.
    intros s spec.
    assert (T :  eval (` ReadyTrue `/\ ` IsValid `/\ ` IsDone `~> (` IsReady `\/ ` ReadyFalse)) s 
                  -> eval (` ReadyTrue `/\ ` IsValid `/\ ` IsDone `~> ` IsReady) s).
    intros H n H0.
    apply H in H0.
    destruct H0 as (m,[H0|H0]).
    exists m; auto.
    apply Spec_ReadyFalseLeadstoReady in spec.
    apply spec in H0. destruct H0 as (m0,H0).
    exists ((m0 + m)%nat). unfold IsReady in *. simpl in *.
    rewrite <- H0. do 2 rewrite <- contraction; auto.
    apply T. clear T.
    assert (H : eval (([]<> ` IsReady) `\/ ([]<> `~ (` ReadyTrue `/\ ` IsValid `/\ ` IsDone))) s).
    destruct spec as (_,(_,(_,(_,[fair|fair]))));
    unfold IsReady, ReadyTrue, IsValid, IsDone, Resp in *.
    left. intros n. simpl in *. specialize fair with n.
    destruct fair as (m,((_,(_,(_,(H,_)))),_)).
    exists (S m). rewrite <- H; auto. 
    right. simpl in *. intros n. specialize fair with n.
    destruct fair as (m,fair). exists m.
    intros H. destruct H as (H,(H0,H1)).
    destruct (ready ((s @ n) @ m%behavior 0%nat)).
    destruct (status ((s @ n) @ m%behavior 0%nat)).
    destruct (ctrl ((s @ n) @ m%behavior 0%nat)).
    inversion H1. inversion H1.
    apply fair.
    exists ({| ctrl := Ready;
               ready := true;
               status := Valid;
               cmd := cmd ((s @ n) @ m%behavior 0%nat);
               memory :=  memory ((s @ n) @ m%behavior 0%nat);
               output := output ((s @ n) @ m%behavior 0%nat) |}). repeat split; auto.
    inversion H0.
    inversion H.
    destruct H as [H|H].
    clear spec. intros n _. simpl in *. specialize H with n. destruct H as (m,H).
    exists m. left; auto.
    apply deriveLeadsTo; auto.
    intros n H0.
    destruct spec as (_,(next,_)).
    simpl in next. specialize next with n. clear H.
    unfold ReadyTrue, IsValid, IsDone, IsReady, ReadyFalse in *.
    simpl in *.
    destruct H0 as (H0,(H1,H2)).
    destruct next as [
    [(H3,_)
    |[next
    |[(c,(_,(_,(_,(H3,_)))))
    |[(_,(_,(H3,_)))
    |(_,(_,(_,(H3,_))))]]]]
    |next].
    assert (W : true = false). rewrite <- H3. rewrite H0. auto. inversion W.
    right. right. firstorder.
    assert (W : Ready = Done). rewrite <- H3. rewrite <- H2. auto. inversion W.
    assert (W : Busy = Done). rewrite <- H3. rewrite <- H2. auto. inversion W.
    right. left. rewrite <- H3. auto.
    rewrite next in *. rewrite <- H0. rewrite <- H1. rewrite <- H2.
    left; repeat split; auto.
  Qed.

  Lemma Spec_ValidAndBusyLeadsToReady : valid (Spec `=> 
          ((` ReadyTrue `/\ ` IsValid `/\ ` IsBusy) `~> ` IsReady)).
  Proof.
     intros s spec.
     assert (T :  eval (` ReadyTrue `/\ ` IsValid `/\ ` IsBusy 
                  `~> ((` ReadyTrue `/\ ` IsValid `/\ ` IsDone) `\/ (` IsReady `\/ ` ReadyFalse))) s 
                  -> eval (` ReadyTrue `/\ ` IsValid `/\ ` IsBusy `~> ` IsReady) s).
     intros H n H0. apply H in H0.
     destruct H0 as (m,[H0|[H0|H0]]).
     apply Spec_ValidAndDoneLeadsToReady in spec.
     apply spec in H0. unfold IsReady in *.
     destruct H0 as (n0,H0). exists ((n0 + m)%nat).
     simpl in *. rewrite <- H0. do 2 rewrite <- contraction. auto.
     exists m. auto.
     apply Spec_ReadyFalseLeadstoReady in spec. apply spec in H0.
     destruct H0 as (m0,H0). exists ((m0 + m)%nat).
     unfold IsReady in *. 
     simpl in *. rewrite <- H0. do 2 rewrite <- contraction. auto.
     apply T. clear T.
     (* break *)
     assert (H: eval (([]<> (` IsReady `\/ ` ReadyFalse)) 
                   `\/ []<> `~ (` ReadyTrue `/\ ` IsValid `/\ ` IsBusy)) s).
     assert (H0 : eval (` ReadyTrue `/\ ` IsValid `/\ ` IsDone `~> `IsReady) s).
     apply Spec_ValidAndDoneLeadsToReady; auto.
     assert (TY : eval ([] ` TypeInvariant) s). apply Spec_TypeInvariant in spec. auto.
     destruct spec as (_,(_,(_,([fair|fair],_)))).
     unfold Do in fair.
     simpl in fair. left. intros n. specialize fair with n.
     destruct fair as (m,fair).
     assert (H1 : eval (` ReadyTrue `/\ `IsValid `/\ `IsDone) ((s @ n) @ (S m)%behavior)).
     unfold ReadyTrue, IsValid, IsDone. simpl.
     destruct fair as ((H1,(H2,(_,(_,(H3,(H4,(H5,_))))))),_).
     rewrite <- H1. rewrite <- H2. rewrite <- H3. rewrite <- H4. rewrite <- H5.
     repeat split; auto.
     apply H0 in H1. destruct H1 as (m0,H1). exists ((m0 + S m)%nat).
     left. unfold IsReady in *. rewrite <- H1.
     unfold eval. do 2 rewrite <- contraction. simpl. auto.
     right. intros n. simpl in fair.
     specialize fair with n. destruct fair as (m,fair).
     clear H0. exists m. unfold ReadyTrue, IsValid, IsBusy, Do in *. simpl in *.
     intros F. destruct F as (H,(H0,H1)).
     destruct (ready ((s @ n) @ m%behavior 0%nat)).
     destruct (status ((s @ n) @ m%behavior 0%nat)).
     destruct (ctrl ((s @ n) @ m%behavior 0%nat)).
     inversion H1.
     unfold DoFlush, DoWrite, DoRun in *.
     apply fair.
     assert (IsC : IsCommand (cmd ((s @ n) @ m%behavior 0%nat))).
     specialize TY with ((m + n)%nat). rewrite contraction.
     destruct TY as (TY0,(TY1,TY2)). auto.
     destruct (cmd ((s @ n) @ m%behavior 0%nat)).
     exists ({| ctrl := Done;
                ready := true;
                status := Valid;
                cmd := Flush;
                output := NilPattern;
                memory := NilPattern|}).
     repeat split; simpl; auto.
     simpl in IsC.
     apply EqNilPatternClassical in IsC. destruct IsC as [IsC|IsC].
     exists ({| ctrl := Done;
                ready := true;
                status := Valid;
                cmd := Write p;
                output := (output ((s @ n) @ m%behavior 0%nat));
                memory := (memory ((s @ n) @ m%behavior 0%nat))|}).
     repeat split; simpl; auto. right. left. split; auto. exists p. repeat split; auto.
     intros F. exfalso. apply F; auto.
     exists ({| ctrl := Done;
                ready := true;
                status := Valid;
                cmd := Write p;
                output := (output ((s @ n) @ m%behavior 0%nat));
                memory := p|}).
     repeat split; simpl; auto. right. left. split; auto. exists p. repeat split; auto.
     intros F. exfalso. apply IsC; auto.
     assert (Q : IsPattern (memory ((s @ n) @ m%behavior 0%nat))).
     specialize TY with ((m + n) % nat). unfold TypeInvariant in TY.
     rewrite contraction. destruct TY as (_,(TY,_)). auto.
     apply EqNilPatternClassical in Q.
     destruct Q as [Q|Q].
     exists ({| ctrl := Done;
                ready := true;
                status := Valid;
                cmd := Run;
                output := output ((s @ n) @ m%behavior 0%nat);
                memory := memory ((s @ n) @ m%behavior 0%nat)|}). 
     repeat split; simpl; auto. right. right. repeat split; auto.
     exfalso; apply H2; auto.
     exists ({| ctrl := Done;
                ready := true;
                status := Valid;
                cmd := Run;
                output := memory ((s @ n) @ m%behavior 0%nat);
                memory := NilPattern|}).
     repeat split; simpl; auto. right. right. repeat split; auto.
     exfalso; apply Q; auto.
     inversion H1.
     inversion H0.
     inversion H.
     destruct H as [H|H].
     intros n _. simpl in *. specialize H with n. destruct H as (m,H).
     exists m. right. auto.
     apply deriveLeadsTo; auto. clear H.
     intros n H. destruct spec as (_,(next,_)).
     simpl in next. specialize next with n.
     destruct H as (H,(H0,H1)).
     unfold ReadyTrue, IsValid, IsBusy, IsDone, IsReady, ReadyFalse in *.
     simpl in *.
     unfold Next in *.
     destruct next as [
     [(H2,_)
     |[(H2,_)
     |[(c,(_,(_,(_,(H2,_)))))
     |[(H2,(H3,(_,(_,(H4,(H5,(H6,_)))))))
     |(_,(_,(H2,_)))]]]]
     |next].
     assert (W : true = false). rewrite <- H2. rewrite <- H. auto. inversion W.
     right. right. right. rewrite <- H2. auto.
     assert (W : Ready = Busy). rewrite <- H2. rewrite <- H1. auto. inversion W.
     right. left. rewrite <- H2. rewrite <- H3. rewrite <- H4. 
      rewrite <- H5. rewrite <- H6. repeat split; auto.
     assert (W : Done = Busy). rewrite <- H2. rewrite <- H1. auto. inversion W.
     rewrite next in *. left. rewrite <- H. rewrite <- H0. rewrite <- H1.
     repeat split; auto.
  Qed.

  Theorem Spec_CommandsComplete : valid (Spec `=> CommandsComplete).
  Proof.
    intros s spec.
    (*assert (H : eval ((` ReadyTrue `/\ ` IsValid `/\ ` IsBusy) `~> ` IsReady) s).
    apply Spec_ValidAndBusyLeadsToReady; auto.*)
    pose (H1 := Spec_NotBad s spec).
    intros n H0.
    assert (H2 : eval ( (` ReadyTrue `/\ ` IsValid `/\ ` IsBusy) 
                    `\/ (` ReadyTrue `/\ ` IsValid `/\ ` IsDone) 
                    `\/ ` ReadyFalse `\/ ` IsReady) s @ n).
    unfold  IsValid, IsBusy, IsReady, IsDone, ReadyTrue, ReadyFalse in *.
    simpl. simpl in H1. specialize H1 with n.
    destruct (ctrl (s @ n%behavior 0%nat)).
    right; right. right. auto.

    destruct (ready (s @ n%behavior 0%nat)).
    destruct (status (s @ n%behavior 0%nat)).
    left. repeat split; auto.
    exfalso. apply H1. repeat split; auto.
    right. right. left. auto.

    destruct (ready (s @ n%behavior 0%nat)).
    destruct (status (s @ n%behavior 0%nat)).
    right. left. repeat split; auto.
    exfalso. apply H1. repeat split; auto.
    right. right. left. auto.

    destruct H2 as [H2|[H2|[H2|H2]]].
    pose (H3 := Spec_ValidAndBusyLeadsToReady s spec).
    apply H3; auto.
    pose (H3 := Spec_ValidAndDoneLeadsToReady s spec).
    apply H3; auto.
    pose (H3 := Spec_ReadyFalseLeadstoReady s spec).
    apply H3; auto.
    unfold IsReady in H2. simpl in *. 
    exists O. rewrite shift_0. auto.
  Qed.

  Definition InitializeAfterReset := ` (fun st => st.(ready) = false) 
                                     `~> 
                                     ` fun st => st.(ready) = true.

  Theorem Spec_InitializeAfterReset : valid (Spec `=> InitializeAfterReset).
  Proof.
    intros s H.
    destruct H as (init,(next,([wfI|wfI],fairness))).
    intros n H. simpl in wfI. specialize wfI with n.
    destruct wfI as (m,(wfI,H0)).
    exists (S m). simpl. unfold Initialize in wfI.
    destruct wfI as (_,(wfI,_)). auto.
    simpl in wfI.
    intros n H. specialize wfI with n.
    destruct wfI as (m,imp).
    exists m. simpl.
    assert (B : ready ((s @ n) @ m%behavior 0%nat) = true \/ ready ((s @ n) @ m%behavior 0%nat) = false).
    destruct (ready ((s @ n) @ m%behavior 0%nat)); intuition.
    destruct B as [B|B]; auto.
    exfalso. apply imp. unfold Initialize.
    exists ({| ready := true;
               ctrl := Ready;
               status := Valid;
               memory := NilPattern;
               output := output ((s @ n) @ m%behavior 0%nat);
               cmd := cmd ((s @ n) @ m%behavior 0%nat) |}).
    simpl. repeat split; auto.
  Qed.


End Command.

