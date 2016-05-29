Set Implicit Arguments.

Require Import Arith.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Setoid.

Require Import Behavior.
Require Import Expr.
Require Import ExprEquiv.

Local Open Scope behavior.
Local Open Scope tla.

Hint Unfold valid.

Theorem STL1 :
  forall (A : Type) (P : Expr A),
    valid P -> valid ([] P).
Proof.
  firstorder.
Qed.

Theorem STL2 :
  forall (A : Type) (P : Expr A),
    valid ([]P `=> P).
Proof.
  unfold valid. simpl.
  intros A P s H.
  rewrite <- shift_0.
  apply H.
Qed.

Theorem STL3 :
  forall (A : Type) (P : Expr A),
    valid ([]([]P) `<=> []P).
Proof.
  unfold valid. simpl.
  intros A P s. split.
  intros H n; specialize (H n 0); rewrite shift_0 in H; assumption.
  intros H n m; specialize (H (m + n)); rewrite contraction; assumption.
Qed.

Theorem STL4 :
  forall (A : Type) (P Q : Expr A),
    valid (P `=> Q) ->
    valid ([]P `=> []Q).
Proof.
  firstorder.
Qed.

Theorem STL5 :
  forall (A : Type) (P Q : Expr A),
    valid ([] (P `/\ Q) `<=> []P `/\ []Q).
Proof.
  firstorder.
Qed.

Theorem STL6 :
  forall (A : Type) (P Q : Expr A),
    valid (<>[] (P `/\ Q) `<=> <>[]P `/\ <>[]Q).
Proof.
  split; try (solve [firstorder]).
  intros ((n,HP),(m,HQ)).
  exists (n + m). intros o. split.

  specialize (HP (m+o)).
  replace ((s@(n+m))@o) with ((s@n)@(m+o))
    by (unfold shift; extensionality t; intuition).
  assumption.

  specialize (HQ (n+o)).
  replace (s@(n+m)@o) with ((s@m)@(n+o))
    by (unfold shift; extensionality t; intuition).
  assumption.
Qed.

Theorem ImplicationIntroduction : forall (A : Type) (P Q : Expr A) s,
                                    (eval P s -> eval Q s)
                                    -> eval (P `=> Q) s.
Proof.
  auto.
Qed.

Theorem ModusPonens : forall (A : Type) (P Q : Expr A) s, (eval (P `=> Q) s) -> eval P s -> eval Q s.
Proof.
  auto.
Qed.


Theorem RefineWF : forall (A B : Type) (mapping : A -> B) (P : Action A) (Q : Action B),
  (forall s s', P s s' -> Q (mapping s) (mapping s'))
  -> (forall s s', mapping s = mapping s' -> ~ P s s' \/ s = s')
  -> (forall s, (exists s', Q (mapping s) s') -> (exists s', P s s'))
  -> forall s, eval (WF P) s -> eval (WF Q) (fun x => mapping (s x)).
Proof.
  intros A B mapping P Q H diseq H2 s H0.
  assert (H1 : forall s, eval (ENABLED P) s -> eval (ENABLED Q) (fun x => mapping (s x))).
    intros s0 H1. destruct H1 as (s1,H1).
    exists (mapping s1). apply H; auto.

  assert (H3 : forall s, ~ (exists s', P s s') -> ~ (exists s', Q (mapping s) s')).
  intros st N R. apply N. apply H2. auto.

  assert (wfP : eval (WF P) s). assumption.
  destruct wfP as [wfP|noAct].
  left. intros n. simpl in wfP. specialize wfP with n.
  destruct wfP as (m,(Pm,dif)).
  exists m. split. apply H. simpl. apply Pm.
  intros H4. apply diseq in H4. destruct H4; auto.


  right. intros n. simpl in noAct. specialize noAct with n.
  destruct noAct as (n0,noAct). exists n0. apply H3; auto.
Qed.

Theorem DeriveAlwaysEventually : forall (A : Type) (P Q : Expr A) s,
  (forall n, eval P (s @ n) -> eval (P `\/ Q) (s @ (S n))) ->
  (*ignoring classicality condition*) (forall n, eval (<> Q) (s @ n) \/ ~ eval (<> Q) (s @ n)) -> 
  eval ([] (P `=> ([] P) `\/ (<> Q))) s.
Proof.
  intros A P Q s H class n H0.
  assert (T : forall m, (forall k, k <= m -> eval P ((s @ n) @ k)) \/ eval (<> Q) (s @ n)).
  intros m. induction m.
  left. intros k H1. inversion H1. rewrite shift_0. auto.
  destruct IHm as [IHm|IHm].
  assert (H1 : eval P (s @ (m + n))). rewrite <- contraction. apply IHm; auto.
  apply H in H1. destruct H1 as [H1|H1].
  left. intros k H2. inversion H2. rewrite contraction. simpl. auto.
  apply IHm; auto.
  right. exists (S m). rewrite contraction. auto.
  right; auto. specialize class with n.
  destruct class. right; auto.
  left. intros m. specialize T with m. destruct T as [T|T].
  apply T; auto.
  exfalso. apply H1. auto.
Qed.


Theorem mapEventuall : forall T (P Q : Expr T), valid (P `=> Q) ->
  valid (<> P `=> <> Q).
Proof.
  intros T P Q H s eP.
  simpl in *. destruct eP as (n,eP).
  exists n. apply H; auto.
Qed.

Theorem deriveLeadsTo' : forall T (P Q : Expr T) s,
  (forall n, eval P (s @ n) -> eval (P `\/ Q) (s @ (S n)))
  -> eval (<> `~ P) s -> eval (P `=> <> Q) s.
Proof.
  intros T P Q s H neP.
  assert (H0 : eval P s -> forall m, (forall k, k <= m -> eval P (s @ k)) \/ eval (<> Q) s).
  intros H0 m. induction m. left; intros k H1. inversion H1. rewrite shift_0; auto.
  destruct IHm as [IHm|IHm].
  assert (H1 : eval P s @ m). apply IHm; auto.
  apply H in H1. destruct H1 as [H1|H1].
  left. intros k H2. inversion H2; auto.
  right. exists (S m); auto.
  right; auto.
  intros H1. destruct neP as (m,neP).
  assert (H2 : (forall k : nat, k <= m -> eval P s @ k) \/ eval (<> Q) s). auto.
  destruct H2 as [H2|H2] ; auto.
  simpl in *. exfalso. apply neP. apply H2; auto.
Qed.

Theorem deriveLeadsTo : forall T (P Q : Expr T) s,
  (forall n, eval P (s @ n) -> eval (P `\/ Q) (s @ (S n)))
  -> eval ([] <> `~ P) s -> eval (P `~> Q) s.
Proof.
  intros T P Q s H neP n.
  apply deriveLeadsTo'; auto.
  intros m H0.
  rewrite contraction. simpl. apply H.
  rewrite <- contraction. auto.
Qed.


