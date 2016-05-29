Require Import Behavior.
Require Import Expr.

Require Import Arith.
Require Import Omega.
Require Import FunctionalExtensionality.

Local Open Scope behavior.
Local Open Scope tla.
(*
Lemma skip_predicate_inner :
  forall (A : Type) (P : Predicate A) (s : Behavior A),
    eval `P s ->
    eval SKIP s ->
    eval `P s@1.
Proof.
  unfold shift. simpl.
  intros A P s HP HSkip.
  rewrite <- HSkip.
  assumption.
Qed.
 *)

Theorem tla_inv :
  forall (A : Type) (Init P : Predicate A) (Next : Action A),
    (forall x, Init x -> P x) ->
    (forall x y, P x -> Next x y -> P y) ->
    valid (`Init `/\ [][Next] `=> [] `P).
Proof.
  unfold valid. simpl. unfold shift. simpl.
  intros A Init P Next Hinv1 Hinv2 s (Hini,Hnxt) n.
  induction n; auto.
  specialize (Hnxt n).
  destruct Hnxt as [H | H].
  apply Hinv2 with (s n); auto.
  rewrite <- H; auto.
Qed.

Theorem tla_inv_gen :
  forall (A : Type) (Init : Predicate A) (Next : Action A) (F P : Expr A),
    (valid (`Init `/\ [][Next] `/\ F `=> P)) ->
    (forall s, eval P s -> Next (s 0) (s 1) -> eval P (s @ 1)) ->
    valid (`Init `/\ [][Next] `/\ F `=> [] P).
Proof.
  intros A Init Next F P H H0 s.
  intros H1 n.
  destruct H1 as (H1,(H2,H3)).
  generalize dependent s.
  induction n.
  intros s H1 H2 H3.
  apply H. simpl. rewrite shift_0. repeat split; auto.
  intros s H1 H2 H3.
  assert (R : s @ (S n) = (s @ n) @ 1). extensionality x. unfold shift.
  assert (R' : x + S n = x + 1 + n). omega.
  rewrite R'. trivial.
  rewrite R. clear R.
  assert (H4 : Next (s @ n 0) (s @ n 1) \/ s @ n 0 = s @ n 1). apply H2.
  destruct H4 as [H4|H4].
  apply H0; trivial.
  apply IHn; trivial.
  apply stutter_equiv_shift_1 in H4.
  rewrite contraction in *. simpl in H4.
  assert (H5 : eval P (s @ (S n)) <-> eval P (s @ n)).  apply stutter_equiv_eval; auto.
  simpl. apply H5. apply IHn; auto.
Qed.