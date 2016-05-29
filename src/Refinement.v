Set Implicit Arguments.

Require Import Behavior.
Require Import Expr.

Local Open Scope behavior.
Local Open Scope tla.

Definition refines (A C : Type)
  (m : C -> A)    (* Projection from "concrete" to "abstract" states *)
  (P : Expr A)    (* "Abstract" specification *)
  (Q : Expr C)    (* "Concrete" specification *)
  := valid (Q `=> map m P).

Theorem refines_refl :
  forall (A : Type) (P : Expr A),
    refines (fun x => x) P P.
Proof.
  unfold refines, valid. simpl.
  intros.
  rewrite map_id.
  assumption.
Qed.

Theorem refines_trans :
  forall (A B C : Type) (m1 : B -> A) (m2 : C -> B) P Q R,
    refines m1 P Q ->
    refines m2 Q R ->
    refines (fun x => m1 (m2 x)) P R.
Proof.
  unfold refines, valid. simpl.
  intros A B C m1 m2 P Q R HQP HRQ s H.
  rewrite <- map_map.
  rewrite map_eval.
  apply HQP.
  rewrite <- map_eval.
  apply HRQ.
  assumption.
Qed.

Theorem refinement_preserves_invariant :
  forall (A C : Type)
         (m : C -> A)
         (P : Expr A)
         (Q : Expr C)
         (I : Predicate A),
    refines m P Q ->
    valid (P `=> [] `I) ->
    valid (Q `=> [] map m `I).
Proof.
  unfold refines, valid. simpl. unfold shift. simpl.
  intros A C m P Q I Hrefines Hinv s H n.
  specialize (Hinv (fun x => m (s x))).
  apply Hinv.
  rewrite <- map_eval.
  intuition.
Qed.

Lemma refine_conj :
  forall (A C : Type) s (m : C -> A) Pa Pc Qa Qc,
    eval (Qc `=> map m Qa) s ->
    eval (Pc `=> map m Pa) s ->
    eval (Pc `/\ Qc) s ->
    eval (map m (Pa `/\ Qa)) s.
Proof. firstorder. Qed.

Theorem refine_predicate :
  forall (A C : Type) (m : C -> A) (Pa : Predicate A) (Pc : Predicate C),
    (forall x, Pc x -> Pa (m x)) ->
    refines m `Pa `Pc.
Proof. firstorder. Qed.

Theorem refine_always :
  forall (A C : Type) (m : C -> A) P Q,
    refines m P Q ->
    refines m ([]P) ([]Q).
Proof. firstorder. Qed.
(*
Theorem refine_box :
  forall (A C : Type) (m : C -> A) (ra : Action A) (rc : Action C),
    (forall x y, rc x y -> ra (m x) (m y)) ->
    refines m ([ra]) ([rc]).
Proof.
  unfold refines, valid. simpl.
  intros.
  intuition; auto using f_equal.
Qed.
*)
Theorem refine_always_box :
  forall (A C : Type) (m : C -> A) (ra : Action A) (rc : Action C),
    (forall x y, rc x y -> ra (m x) (m y)) ->
    refines m ([][ra]) ([][rc]).
Proof.
  intros.
  unfold refines, valid. intros s. simpl.
  intros H0 n. specialize H0 with n.
  destruct H0 as [H0|H0]; [left; auto | right; rewrite H0; trivial].
Qed.
(*
Theorem refine_skip_skip :
  forall (A C : Type) (m : C -> A),
    refines m SKIP SKIP.
Proof.
  unfold refines, valid. simpl.
  auto using f_equal.
Qed.
 *)

Lemma disj_pw_impl :
  forall P1 Q1 P2 Q2 : Prop,
    (P1 -> P2) ->
    (Q1 -> Q2) ->
    (P1 \/ Q1) ->
    (P2 \/ Q2).
Proof. firstorder. Qed.
