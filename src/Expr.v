Set Implicit Arguments.

Require Import Logic.FunctionalExtensionality.
Require Import Behavior.
Local Open Scope behavior.


Section Syntax.

  Variable A : Type.

  Definition Predicate := A -> Prop.
  Definition Action := A -> A -> Prop.

  Inductive Expr :=
  | E_Predicate : Predicate -> Expr
  | E_AlwaysAction : forall {B : Type}, (A -> B) -> Action -> Expr
  | E_EventuallyAction : forall {B : Type}, (A -> B) -> Action -> Expr
  | E_Neg : Expr -> Expr
  | E_Conj : Expr -> Expr -> Expr
  | E_Disj : Expr -> Expr -> Expr
  | E_Impl : Expr -> Expr -> Expr
  | E_Equiv : Expr -> Expr -> Expr
  | E_Always : Expr -> Expr
  | E_Eventually : Expr -> Expr
  | E_ForallRigid : forall {B : Type}, (B -> Expr) -> Expr
  | E_ExistsRigid : forall {B : Type}, (B -> Expr) -> Expr.

  Definition E_Enabled (r : Action) :=
    E_Predicate (fun st => exists st', r st st').
(*
  Definition E_Skip := E_Action eq.
  Definition E_Box e := E_Disj e E_Skip.
 *)
  
End Syntax.

(*Arguments E_Skip {A}.*)

(* Notations *)

Delimit Scope tla_scope with tla.

Notation "P `<=> Q" :=
  (E_Equiv P Q) (at level 95, no associativity) : tla_scope.

Notation "P `=> Q" :=
  (E_Impl P Q) (at level 90, right associativity) : tla_scope.


Notation "P `\/ Q" :=
  (E_Disj P Q) (at level 85, right associativity) : tla_scope.

Notation "P `/\ Q" :=
  (E_Conj P Q) (at level 80, right associativity): tla_scope.

Notation "`~ P" :=
  (E_Neg P) (at level 75, right associativity) : tla_scope.

Notation "[] P" :=
  (E_Always P) (at level 75, right associativity) : tla_scope.

Notation "<> P" :=
  (E_Eventually P) (at level 75, right associativity) : tla_scope.

Definition E_LeadsTo {T} (P Q : Expr T) := E_Always (E_Impl P (E_Eventually Q)).

Notation "P `~> Q" :=
  (E_LeadsTo P Q) (at level 90, right associativity) : tla_scope.


Notation "'ENABLED' r" :=
  (E_Enabled r) (at level 70, no associativity) : tla_scope.

Notation "[][ R ]" := (E_AlwaysAction (fun x => x)  R) : tla_scope.

Notation "<>< R >" := (E_EventuallyAction (fun x => x)  R) : tla_scope.

(* Notation "'SKIP'" := (E_Skip) : tla_scope. *)

Notation "` P" :=
  (E_Predicate P) (at level 0, right associativity) : tla_scope.

Notation "'FORALL' p" := (E_ForallRigid p) (at level 70, right associativity)
                         : tla_scope.

Notation "'EXISTS' p" := (E_ForallRigid p) (at level 70, right associativity)
                         : tla_scope.



(* Coercing predicates doesn't seem to work all the time, so use the
explicit notation above. *)
(* Coercion E_Predicate : Predicate >-> Expr. *)

Local Open Scope tla.


Definition WF {T} (A : Action T) : Expr T :=
  ([] (E_EventuallyAction (fun x => x) A)) `\/ ([]<>(`~ ENABLED A)).

Definition SF {T} (A : Action T) : Expr T :=
  ([] (E_EventuallyAction (fun x => x) A)) `\/ (<>[](`~ ENABLED A)).
  

Arguments WF _ A%tla.
Arguments SF _ A%tla.

Fixpoint eval (A : Type) (e : Expr A) : Behavior A -> Prop :=
  match e with
    | E_Predicate p => fun s => p (s 0)
    | E_AlwaysAction f r => fun s => forall n, (r (s@n 0) (s@n 1)) \/ f (s@n 0) = f (s@n 1)
    | E_EventuallyAction f r => fun s => exists n, (r (s@n 0) (s@ n 1)) /\ f (s@n 0) <> f (s@n 1)
    | `~ e => fun s => ~ eval e s
    | e1 `/\ e2 => fun s => eval e1 s /\ eval e2 s
    | e1 `\/ e2 => fun s => eval e1 s \/ eval e2 s
    | e1 `=> e2 => fun s => eval e1 s -> eval e2 s
    | e1 `<=> e2 => fun s => eval e1 s <-> eval e2 s
    | [] e => fun s => forall n, eval e (s@n)
    | <> e => fun s => exists n, eval e (s@n)
    | E_ForallRigid f => fun s => forall x, eval (f x) s
    | E_ExistsRigid f => fun s => exists x, eval (f x) s
  end.

Definition valid (A : Type) (e : Expr A) : Prop :=
  forall s, eval e s.

Arguments valid _ e%tla.
Arguments eval _ e%tla s%behavior.

Fixpoint map (C A : Type) (f : C -> A) (e : Expr A) : Expr C :=
  match e with
    | E_Predicate P => E_Predicate (fun st => P (f st))
    | E_AlwaysAction g R => E_AlwaysAction (fun st => g (f st)) (fun st st' => R (f st) (f st'))
    | E_EventuallyAction g R => E_EventuallyAction (fun st => g (f st)) (fun st st' => R (f st) (f st'))
    | `~ P => `~ (map f P)
    | P `/\ Q => (map f P) `/\ (map f Q)
    | P `\/ Q => (map f P) `\/ (map f Q)
    | P `=> Q => (map f P) `=> (map f Q)
    | P `<=> Q => (map f P) `<=> (map f Q)
    | [] P => [] (map f P)
    | <> P => <> (map f P)
    | E_ForallRigid g => E_ForallRigid (fun x => map f (g x))
    | E_ExistsRigid g => E_ExistsRigid (fun x => map f (g x))
  end.

Lemma same_args_same_res : forall A, forall B, forall (f : A -> B), forall x y, x = y -> f x = f y.
    intros A B f x y H; rewrite H; auto.
Qed.

Lemma map_id :
  forall (A : Type) (e : Expr A),
    map (fun x => x) e = e.
Proof.
  assert (arg : forall A, forall B, forall (f : A -> B), forall x y, x = y -> f x = f y). intros A B f x y H; rewrite H; auto.
  induction e; simpl;
  try (rewrite IHe1; rewrite IHe2; trivial);
  try (rewrite IHe; trivial);
  try trivial;
  try (apply same_args_same_res; extensionality x; auto).
Qed.

Lemma map_map :
  forall (A B C : Type) (f : A -> B) (g : B -> C) (e : Expr C),
    map f (map g e) = map (fun x => g (f x)) e.
Proof.
  induction e; simpl;
  try (rewrite IHe1; rewrite IHe2; trivial);
  try (rewrite IHe; trivial);
  try trivial;
  try (apply same_args_same_res; extensionality x; auto).
Qed.

Lemma slide_shift : forall A B (f : A -> B) s n, (fun x => f (s x)) @ n = fun x => f ((s @ n) x).
Proof.
  intros A B f s n.
  extensionality x.
  induction n; auto.
Qed.

Lemma map_eval :
  forall (A B : Type) (f : A -> B) (e : Expr B) (s : Behavior A),
    eval (map f e) s <-> eval e (fun x => f (s x)).
Proof.
  intros A B f e s.  generalize dependent s.
  induction e; simpl; intros;
  try (rewrite IHe1; rewrite IHe2; solve [intuition]);
  try (rewrite IHe; solve [intuition]);
  try solve [intuition].
  split; intros H n;
  [ try (rewrite slide_shift; apply IHe; trivial) |
    specialize H with n; rewrite slide_shift in H; apply IHe in H; trivial].
  split; intros H; destruct H as (n,H); exists n;
  [ rewrite slide_shift; apply IHe; trivial |
    rewrite slide_shift in H; apply IHe in H; trivial].
  split; intros H0 x; apply H; trivial.
  split; intros H0; destruct H0 as (x,H0); exists x; apply H; trivial.
Qed.


Theorem stutter_equiv_eval : forall A (e : Expr A) (s s' : Behavior A), stutter_equiv s s' ->
                                                                        eval e s <->
                                                                        eval e s'.
Proof.
  intros A e.
  induction e; intros s s' H0; simpl.
  apply stutter_equiv_same_first in H0; rewrite H0; split; auto.
  split; intros H1 n; unfold shift in *; simpl in *;
  set (a' := fun x y => a x y \/ b x = b y). 
  assert (H2 :  a' (s' n) (s' (S n)) \/ s' n = s' (S n)).
  apply stutter_equiv_induct_next with s; auto. intros n0.
  specialize H1 with n0. destruct H1 as [H1|H1]; left. left; auto. right; auto.
  destruct H2 as [[H2|H2]|H2]. left; auto. right; auto. rewrite H2; right; auto.
  assert (H2 :  a' (s n) (s (S n)) \/ s n = s (S n)).
  apply stutter_equiv_induct_next with s'; auto. symmetry; auto. intros n0.
  specialize H1 with n0. destruct H1 as [H1|H1]; left. left; auto. right; auto.
  destruct H2 as [[H2|H2]|H2]. left; auto. right; auto. rewrite H2; right; auto.
  split; intros H1. 
  apply stutter_equiv_induct_next'' with s; auto.
  apply stutter_equiv_induct_next'' with s'; auto.
  assert (H : s = fun n => s @ n 0). extensionality n; auto.
  rewrite <- H. symmetry. auto.
  split; intros H1 H2; apply H1. apply IHe with s'; auto.  apply IHe with s; auto. symmetry; auto.
  assert (H3 : stutter_equiv s s'); auto.
  apply IHe1 in H0. apply IHe2 in H3.
  intuition.
  assert (H3 : stutter_equiv s s'); auto.
  apply IHe1 in H0. apply IHe2 in H3.
  split; intros H1; destruct H1; intuition.
  assert (H3 : stutter_equiv s s'); auto.
  apply IHe1 in H0. apply IHe2 in H3.
  intuition.
  assert (H3 : stutter_equiv s s'); auto.
  apply IHe1 in H0. apply IHe2 in H3.
  intuition.
  split; intros H1 n.
  assert (H2: exists m, stutter_equiv (s' @ n) (s @ m)). apply stutter_equiv_univ. symmetry; auto.
  destruct H2 as (m,H2). apply IHe in H2. intuition.
  assert (H2 : exists m, stutter_equiv (s @ n) (s' @ m)). apply stutter_equiv_univ; auto.
  destruct H2 as (m,H2). apply IHe in H2. intuition.
  split; intros H1; destruct H1 as (n,H1).
  assert (H2 : exists m, stutter_equiv (s @ n) (s' @ m)). apply stutter_equiv_univ; auto.
  destruct H2 as (m,H2). apply IHe in H2. exists m; intuition.
  assert (H2 : exists m, stutter_equiv (s' @ n) (s @ m)). apply stutter_equiv_univ. symmetry; auto.
  destruct H2 as (m,H2). apply IHe in H2. exists m; intuition.
  split; intros H1 x; specialize H with x s s'; intuition.
  split; intros H1; destruct H1 as (x,H1); specialize H with x s s'; exists x; intuition.
Qed.