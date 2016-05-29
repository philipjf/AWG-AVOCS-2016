Require Import TLA.
Require Import Rules.
Require Import Arith.
Require Import ZArith.
Require Import Omega.
Require Import Setoid.
Require Import FunctionalExtensionality.
Require Import Memory.
Require Import Command.
Require Import Rules.

Module Total (Params : MemParams).
  Module MEMORY := Memory (Params).
  Module COMMAND := Command (MEMORY.FROMMEM).
  Print MEMORY.BASIC.St.
  Print COMMAND.BASIC.St.
  Definition castSt1 (st : MEMORY.BASIC.St) : COMMAND.BASIC.St :=
    match st with
    | {|  MEMORY.BASIC.ready := ready; 
          MEMORY.BASIC.status := status;
          MEMORY.BASIC.memory := memory;
          MEMORY.BASIC.output := output |} =>
            {|
              COMMAND.BASIC.ready := ready;
              COMMAND.BASIC.status := status;
              COMMAND.BASIC.memory := memory;
              COMMAND.BASIC.output := output |}
    end.

  Definition castSt2 (st : COMMAND.BASIC.St) : MEMORY.BASIC.St :=
    match st with
    | {|  COMMAND.BASIC.ready := ready; 
          COMMAND.BASIC.status := status;
          COMMAND.BASIC.memory := memory;
          COMMAND.BASIC.output := output |} =>
            {|
              MEMORY.BASIC.ready := ready;
              MEMORY.BASIC.status := status;
              MEMORY.BASIC.memory := memory;
              MEMORY.BASIC.output := output |}
    end.
  Lemma castStInv1 : forall st, st = castSt2 (castSt1 st).
  Proof.
    intros st. destruct st; auto.
  Qed.

  Lemma castStInv2 : forall st, st = castSt1 (castSt2 st).
  Proof.
    intros st. destruct st; auto.
  Qed.

  Definition sameSt (st1 : MEMORY.BASIC.St) (st2 : COMMAND.BASIC.St) : Prop :=
    castSt1 st1 = st2.

  Definition sameStAlt : forall st1 st2, sameSt st1 st2 <-> st1 = castSt2 (st2).
  Proof.
    intros st1 st2. unfold sameSt.
    destruct st1, st2. split; intros H; inversion H; auto.
  Qed.

  Inductive St : Type := Make_St : forall st1 st2, 
    sameSt (MEMORY.refinement_mapping st1) (COMMAND.refinement_mapping st2) -> St.

  Definition p1 (st : St) : MEMORY.St :=
    match st with
    | Make_St m _ _ => m
    end.

  Definition p2 (st : St) : COMMAND.St :=
    match st with
    | Make_St _ m _ => m
    end.

  Definition Spec : Expr St := (map p1 MEMORY.Spec) `/\ (map p2 COMMAND.Spec).

End Total.