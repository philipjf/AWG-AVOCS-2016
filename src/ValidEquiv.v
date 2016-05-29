Require Import Expr.

Definition valid_equiv {A : Type} (P Q : Expr A) : Prop :=
  valid (P `<=> Q).

Require Import Relations.
Require Import Setoid.
Require Import Morphisms.
Import RelationClasses.

Lemma valid_equiv_refl :
  forall A, reflexive _ (@valid_equiv A).
Proof. firstorder. Qed.

Lemma valid_equiv_sym :
  forall A, symmetric _ (@valid_equiv A).
Proof. firstorder. Qed.

Lemma valid_equiv_trans :
  forall A, transitive _ (@valid_equiv A).
Proof. firstorder. Qed.

Add Parametric Relation A : (Expr A) (@valid_equiv A)
    reflexivity proved by (valid_equiv_refl A)
    symmetry proved by (valid_equiv_sym A)
    transitivity proved by (valid_equiv_trans A)
      as valid_equiv_rel.

Add Parametric Morphism A : (@valid A) with
    signature valid_equiv ==> iff as valid_mor.
Proof. firstorder. Qed.

Add Parametric Morphism A : (@E_Neg A) with
    signature valid_equiv ==> valid_equiv as valid_neg_mor.
Proof. firstorder. Qed.

Add Parametric Morphism A : (@E_Conj A) with
    signature valid_equiv ==> valid_equiv ==> valid_equiv as valid_conj_mor.
Proof. firstorder. Qed.

Add Parametric Morphism A : (@E_Disj A) with
    signature valid_equiv ==> valid_equiv ==> valid_equiv as valid_disj_mor.
Proof. firstorder. Qed.

Add Parametric Morphism A : (@E_Impl A) with
    signature valid_equiv ==> valid_equiv ==> valid_equiv as valid_impl_mor.
Proof. firstorder. Qed.

Add Parametric Morphism A : (@E_Equiv A) with
    signature valid_equiv ==> valid_equiv ==> valid_equiv as valid_equiv_mor.
Proof. firstorder. Qed.

Add Parametric Morphism A : (@E_Always A) with
    signature valid_equiv ==> valid_equiv as valid_always_mor.
Proof. firstorder. Qed.

Add Parametric Morphism A : (@E_Eventually A) with
    signature valid_equiv ==> valid_equiv as valid_eventually_mor.
Proof. firstorder. Qed.

Module Examples.
  (* Examples *)
  Local Open Scope tla.

  Variable A : Type.
  Implicit Types P Q : Expr A.

  Goal forall P Q, valid_equiv P Q -> valid_equiv Q P.
    intros. symmetry. assumption.
  Qed.

  Goal forall P Q, valid_equiv P Q -> valid P -> valid Q.
  Proof.
    intros. rewrite <- H. assumption.
  Qed.

  Goal
    forall P Q,
      valid_equiv P Q ->
      forall R, valid ([] P `/\ R) -> valid ([] Q `/\ R).
  Proof.
    intros P Q Heq.
    setoid_rewrite <- Heq. (* rewrite under forall r *)
    trivial.
  Qed.

End Examples.
