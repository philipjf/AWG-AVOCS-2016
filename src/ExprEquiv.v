Require Import Behavior.
Require Import Expr.

Definition expr_equiv {A : Type} (s : Behavior A) (P Q : Expr A) : Prop :=
  eval (P `<=> Q) s.

Require Import Relations.
Require Import Setoid.
Require Import Morphisms.
Import RelationClasses.

Lemma expr_equiv_refl :
  forall A s, reflexive _ (@expr_equiv A s).
Proof. firstorder. Qed.

Lemma expr_equiv_sym :
  forall A s, symmetric _ (@expr_equiv A s).
Proof. firstorder. Qed.

Lemma expr_equiv_trans :
  forall A s, transitive _ (@expr_equiv A s).
Proof. firstorder. Qed.

Add Parametric Relation A s : (Expr A) (@expr_equiv A s)
    reflexivity proved by (expr_equiv_refl A s)
    symmetry proved by (expr_equiv_sym A s)
    transitivity proved by (expr_equiv_trans A s)
      as expr_equiv_rel.

Add Parametric Morphism A s : (fun e => @eval A e s) with
    signature @expr_equiv A s ==> iff as expr_eval_mor.
Proof. firstorder. Qed.

Add Parametric Morphism A s : (@E_Neg A) with
    signature @expr_equiv A s ==> @expr_equiv A s as expr_neg_mor.
Proof. firstorder. Qed.

Add Parametric Morphism A s : (@E_Conj A) with
    signature @expr_equiv A s ==> @expr_equiv A s ==> @expr_equiv A s as expr_conj_mor.
Proof. firstorder. Qed.

Add Parametric Morphism A s : (@E_Disj A) with
    signature @expr_equiv A s ==> @expr_equiv A s ==> @expr_equiv A s as expr_disj_mor.
Proof. firstorder. Qed.

Add Parametric Morphism A s : (@E_Impl A) with
    signature @expr_equiv A s ==> @expr_equiv A s ==> @expr_equiv A s as expr_impl_mor.
Proof. firstorder. Qed.

Add Parametric Morphism A s : (@E_Equiv A) with
    signature @expr_equiv A s ==> @expr_equiv A s ==> @expr_equiv A s as expr_equiv_mor.
Proof. firstorder. Qed.

Add Parametric Morphism (A B : Set) s (f : A -> B) : (@map A B f) with
    signature @expr_equiv B  (fun i => f (s i)) ==> @expr_equiv A s as expr_map_mor.
Proof.
  unfold expr_equiv, valid. simpl. intros e1 e2 H.
  do 2 try (rewrite map_eval).
  assumption.
Qed.

Section simpl_map.

  Local Open Scope tla.

  Variables A B : Type.
  Variable f : A -> B.

  Lemma simpl_map_always :
    forall s e, eval (map f ([] e)) s <-> eval ([] (map f e)) s.
  Proof.
    reflexivity.
  Qed.

  Lemma simpl_map_conj :
    forall s e1 e2, eval (map f (e1 `/\ e2)) s <-> eval (map f e1 `/\ map f e2) s.
  Proof.
    reflexivity.
  Qed.

  Lemma simpl_map_disj :
    forall s e1 e2, eval (map f (e1 `\/ e2)) s <-> eval (map f e1 `\/ map f e2) s.
  Proof.
    reflexivity.
  Qed.

End simpl_map.

Ltac simpl_map :=
  repeat (rewrite simpl_map_always || rewrite simpl_map_conj || rewrite simpl_map_disj).
