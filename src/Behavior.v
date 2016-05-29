Require Import Arith.
Require Import FunctionalExtensionality.
Require Import Program.
Require Import Omega.

Set Implicit Arguments.

Definition Behavior (A : Type) := nat -> A.

Section shift.

  Variable A : Type.

  Implicit Types s : Behavior A.

  Definition shift s n : Behavior A :=
    fun t => s (t + n).

  Lemma unshift : forall s n i, shift s n i = s (i+n).
  Proof. unfold shift. auto. Qed.

  Lemma shift_0 : forall s, shift s 0 = s.
  Proof.
    intros s; extensionality x; replace (s x) with (s (x + 0)) by auto; apply unshift.
  Qed.

  Lemma contraction : forall s n m, shift (shift s n) m = shift s (m + n).
  Proof.
    unfold shift; intros s n m; extensionality x; rewrite plus_assoc; auto.
  Qed.

End shift.

Delimit Scope behavior_scope with behavior.

Notation "s @ n" :=
  (shift s n)
    (at level 1, no associativity) : behavior_scope.

Definition stutter_relation {A : Type} (R : Behavior A -> Behavior A -> Prop) :=
  (forall s s', R s s' -> s 0 = s' 0) /\
  (forall s s', R s s' -> exists m, R (shift s 1) (shift s' m) /\ forall k, k < m -> s' 0 = s' k) /\
  (forall s s', R s s' -> exists m, R (shift s m) (shift s' 1) /\ forall k, k < m -> s 0 = s k).

Definition stutter_equiv {A : Type} (s s' : Behavior A) : Prop :=
  exists R, R s s' /\ stutter_relation R.

Lemma stutter_equiv_stuttering_relation : forall A, stutter_relation (stutter_equiv : Behavior A -> Behavior A -> Prop).
Proof.
  intros A.
  repeat split; intros s s' H; destruct H as (R,(H,(H0,(H1,H2)))); auto.
  apply H1 in H. destruct H as (m,(H,H3)); exists m; split; auto; exists R; repeat split; auto.
  apply H2 in H. destruct H as (m,(H,H3)); exists m; split; auto; exists R; repeat split; auto.
Qed.

Lemma stutter_relation_univ : forall A (R : Behavior A -> Behavior A -> Prop),
                           stutter_relation R ->
                           forall s s',
                             R s s' ->
                             forall n, exists m, R (shift s n) (shift s' m).
Proof.
  intros A R H s s' H0 n.
  generalize dependent s. generalize dependent s'.
  induction n.
  intros s' s H0. exists 0. do 2 rewrite shift_0. auto.
  intros s' s H0. destruct H as (H,(H1,H2)).
  apply H1 in H0. destruct H0 as (m,(H0,H3)).
  apply IHn in H0. destruct H0 as (m0,H0).
  do 2 rewrite contraction in H0.
  exists (m0 + m). replace (S n) with (n + 1) by omega. auto.
Qed.

Theorem stutter_equiv_univ : forall A (s s' : Behavior A), stutter_equiv s s' ->
                                                          forall n, exists m,
                                                            stutter_equiv (shift s n) (shift s' m).
Proof.
  intros A s s' H n.
  apply stutter_relation_univ; trivial.
  apply stutter_equiv_stuttering_relation.
Qed.  

Lemma id_stutter_prop : forall A, stutter_relation (fun (s s': Behavior A) => s = s').
Proof.
  intros A.
  repeat split; intros s s' H; rewrite H; auto; exists 1; split; auto;
  intros k H0; replace k with 0 by omega; auto.
Qed.

Theorem refl_stutter_equiv : forall A (s : Behavior A), stutter_equiv s s.
Proof.
  intros A s.
  exists (fun s s' => s = s'). split; trivial.
  apply id_stutter_prop.
Qed.

Lemma flip_stutter_relation : forall A (R : Behavior A -> Behavior A -> Prop),
                            stutter_relation R ->
                            stutter_relation (fun s s' => R s' s).
Proof.
  intros A R H.
  destruct H as (H,(H0,H1)).
  repeat split; auto.
  intros s s' H2. symmetry. auto.
Qed.

Theorem sym_stutter_equiv : forall A (s s' : Behavior A),
                              stutter_equiv s s'
                              -> stutter_equiv s' s.
Proof.
  intros A s s' H.
  destruct H as (R,(H,RS)).
  exists (fun s s' => R s' s).
  split; trivial.
  apply flip_stutter_relation; trivial.
Qed.

Lemma le_difference : forall n m, n <= m -> exists r, m = n + r.
Proof.
  intros n m H.
  generalize dependent n.
  induction m.
  intros n H. inversion H. exists 0; omega.
  intros n H.
  inversion H.
  exists 0; omega.
  assert (T : exists r, m = n + r). apply IHm; auto.
  destruct T as (r, T). exists (S r). omega.
Qed.

Lemma stutter_relation_univ_small : forall A R (s s' : Behavior A) n,
                                      stutter_relation R ->
                                      R s s' ->
                                      (forall k, k < n -> s 0 = s k) ->
                                      exists m, R (shift s n) (shift s' m) /\
                                                (forall k, k < m -> s' 0 = s' k).
Proof.
  intros A R s s' n H H0 H1.
  generalize dependent s. generalize dependent s'.
  induction n.
  intros s' s H0 H1. exists 0. split. do 2 rewrite shift_0. auto.
  intros k H2. exfalso. omega.
  intros s' s H0 H1.
  destruct H as (R_zero,(R_left,R_right)).
  assert (H2 : exists m, R (shift s n) (shift s' m) /\ (forall k, k < m -> s' 0 = s' k)).
  apply IHn; auto.
  destruct H2 as (m,(H2,H3)).
  assert (H4 : exists m0,
                 R (shift (shift s n) 1) (shift (shift s' m) m0)
                 /\ forall k, k < m0 -> (shift s' m) 0 = (shift s' m) k).
  apply R_left; auto.
  destruct H4 as (m0,(H4,H5)).
  unfold shift in H5. simpl in H5.
  assert (H6 : s 0 = (shift s' m) 0). transitivity ((shift s n) 0). unfold shift. simpl. apply H1.
  omega. apply R_zero; auto.
  unfold shift in H6. simpl in H6.
  exists (m0 + m). split.
  do 2 rewrite contraction in H4. simpl in H4. auto.
  intros k H.
  assert (H7 : k < m \/ m <= k). omega.
  destruct H7 as [H7|H7]. apply H3; auto.
  apply le_difference in H7.
  destruct H7 as (r,H7).
  assert (H8 : k = r + m). omega. clear H7.
  rewrite H8 in *.
  transitivity (s' m). transitivity (s 0); auto. symmetry. apply R_zero; auto.
  apply H5. omega.
Qed.
  
Lemma comp_stutter_prop : forall A (R1 R2 : Behavior A -> Behavior A -> Prop),
                            stutter_relation R1 ->
                            stutter_relation R2 ->
                            stutter_relation (fun s s' => exists s'', R1 s s'' /\ R2 s'' s').
Proof.
  intros A R1 R2 H H0.
  repeat split; intros s s' H1; destruct H1 as (t,(H1,H2)).
  destruct H as (H,_). destruct H0 as (H0,_). transitivity (t 0); auto.
  destruct H as (R1_zero,(R1_right,R1_left)).
  apply R1_right in H1. destruct H1 as (m,(H1,H3)).
  assert (H4 : exists m0, R2 (shift t m) (shift s' m0) /\ forall k, k < m0 -> s' 0 = s' k).
  apply stutter_relation_univ_small; auto.
  destruct H4 as (m0,(H4,H5)). exists m0. split; auto. exists (shift t m). split; auto.
  destruct H0 as (R2_zero,(R2_right,R2_left)).
  assert (H3 : exists m : nat,
              R2 (shift t m) (shift s' 1) /\
              (forall k : nat, k < m -> t 0 = t k)). apply R2_left; auto.
  destruct H3 as (m,(H3,H4)).
  set (R1_flip := fun a b => R1 b a).
  assert (H5 : exists m0, R1_flip (shift t m) (shift s m0) /\
                          (forall k, k < m0 -> s 0 = s k)).
  apply stutter_relation_univ_small; auto.
  unfold R1_flip.
  apply flip_stutter_relation. auto.
  unfold R1_flip in *. clear R1_flip.
  destruct H5 as (m0,(H5,H6)).
  exists m0. split; auto. exists (shift t m); split; auto.
Qed.

Theorem trans_stutter_equiv : forall A (s t s' : Behavior A),
                                stutter_equiv s t ->
                                stutter_equiv t s' ->
                                stutter_equiv s s'.
Proof.
  intros A s t s' H H0.
  destruct H as (R1,(H,R1_rel)).
  destruct H0 as (R2,(H0,R2_rel)).
  exists (fun a b => exists c, R1 a c /\ R2 c b).
  split. exists t. split; auto.
  apply comp_stutter_prop; auto.
Qed.
  
Definition prop_extension {A} (R : Behavior A -> Behavior A -> Prop) :=
  fun s s' => R s s' \/ (s 0 = s' 0 /\ R (shift s 1) (shift s' 1)).

Lemma extend_stutter_relation : forall A (R : Behavior A -> Behavior A -> Prop),
                                  stutter_relation R ->
                                  stutter_relation (prop_extension R).
Proof.
  intros A R H.
  destruct H as (H,(H0,H1)).
  repeat split; intros s s' H2; destruct H2 as [H2|(H2,H3)]; auto.
  apply H0 in H2. destruct H2 as (m,(H2,H3)). exists m. split; auto. left; auto.
  exists 1. split. left. auto. intros k H4. replace k with 0 by omega; auto.
  apply H1 in H2. destruct H2 as (m,(H2,H3)). exists m. split; auto. left; auto.
  exists 1. split. left. auto. intros k H4. replace k with 0 by omega; auto.
Qed.
  
Theorem extend_stutter_equiv : forall A (s s' : Behavior A), s 0 = s' 0 ->
                                            stutter_equiv (shift s 1) (shift s' 1) ->
                                            stutter_equiv s s'.
Proof.
  intros A s s' H H0.
  destruct H0 as (R,(H0,H1)).
  exists (prop_extension R). split.
  right; split; auto.
  apply extend_stutter_relation; auto.
Qed.  

Definition front_relation {A} (s s' : Behavior A) := exists m n, s 0 = s' 0 /\
                                                                 (forall k, k <= m -> s 0 = s k) /\
                                                                 (forall k, k <= n -> s' 0 = s' k) /\
                                                                 shift s m = shift s' n.

Lemma front_relation_refl : forall A (s : Behavior A), front_relation s s.
Proof.
  intros A s.
  exists 0. exists 0. repeat split; auto; intros k H; replace k with 0 by omega; auto.
Qed.

Lemma front_relation_step : forall A  (s s' : Behavior A),  front_relation s s' ->
   exists m : nat,
     front_relation s @ 1%behavior s' @ m%behavior /\
     (forall k : nat, k < m -> s' 0 = s' k).
Proof.
  intros A s s' H.
  destruct H as (m,(n,(same_zero,(lt_m,(lt_n,same_tail))))).
  destruct m. exists (S n). split. rewrite shift_0 in same_tail.
  rewrite same_tail. rewrite contraction. simpl. apply front_relation_refl.
  intros k H. apply lt_n; omega.
  exists n. split. exists m. exists 0.
  assert (same_one : s 0 = s 1). apply lt_m; omega.
  repeat split.
  unfold shift. simpl. transitivity (s 0). auto. 
  transitivity (s' 0); auto.
  intros k H. unfold shift. simpl. transitivity (s 0); auto.
  apply lt_m; omega.
  intros k H. replace k with 0 by omega. auto.
  do 2 rewrite contraction. simpl. replace (m + 1) with (S m) by omega. auto.
  intros k H. apply lt_n; omega.
Qed.

Lemma front_relation_sym : forall A (s s' : Behavior A), front_relation s s' ->
                                                         front_relation s' s.
Proof.
  intros A s s' H.
  destruct H as (m,(n,(same_refl,(lt_m,(lt_n,same_tail))))).
  exists n. exists m. repeat split; auto.
Qed.
  
Lemma front_stutter_relation : forall A, stutter_relation (front_relation : Behavior A -> Behavior A -> Prop).
Proof.
  intros A.
  repeat split; intros s s' H.
  destruct H as (m,(n,(same_zero,(lt_m,(lt_n,same_tail))))); auto.
  apply front_relation_step; auto.
  apply front_relation_sym in H. apply front_relation_step in H.
  destruct H as (m,(H,H0)).
  exists m. split; auto. apply front_relation_sym; auto.
Qed.

Lemma front_relation_shift_1 : forall A (s : Behavior A), s 0 = s 1 ->
                                                          front_relation (shift s 1) s.
Proof.
  intros A s H.
  exists 0. exists 1. repeat split; auto.
  intros k H0. replace k with 0 by omega; auto.
  intros k H0. assert (H1 : k = 0 \/ k = 1). omega. destruct H1 as [H1|H1]; rewrite H1; auto.
  rewrite contraction. auto.
Qed.

Theorem stutter_equiv_shift_1 : forall A (s : Behavior A), s 0 = s 1 ->
                                                         stutter_equiv (shift s 1) s.
Proof.
  intros A s H.
  exists front_relation. split.
  apply front_relation_shift_1; auto.
  apply front_stutter_relation; auto.
Qed.

Theorem stutter_equiv_induct_next : forall A (s s' : Behavior A) R,
                                      stutter_equiv s s' ->
                                      (forall n, R (s n) (s (S n)) \/ s n = s (S n)) ->
                                      (forall n, R (s' n) (s' (S n)) \/ s' n = s' (S n)).
Proof.
  intros A s s' R H H0 n.
  assert (H1 : exists m, stutter_equiv (shift s' n) (shift s m)).
  apply stutter_equiv_univ. apply sym_stutter_equiv; auto.
  destruct H1 as (m,H1).
  assert (H2 : stutter_relation (stutter_equiv : Behavior A -> Behavior A -> Prop)).
  apply stutter_equiv_stuttering_relation.
  destruct H2 as (same_zero,(step_left,step_right)).
  assert (H2 : (shift s' n) 0 = (shift s m) 0). apply same_zero.  auto.
  unfold shift in H2. simpl in H2.
  rewrite H2.
  apply step_left in H1.
  destruct H1 as (m0,(H1,H3)).
  destruct m0.
  assert (H4 : (shift (shift s' n) 1) 0 = (shift (shift s m) 0) 0). apply same_zero; auto.
  unfold shift in H4. simpl in H4.
  rewrite H4. right; auto.
  assert (H4 : (shift s m) 0 = (shift s m) m0). apply H3; omega.
  unfold shift in H4. simpl in H4.
  assert (H5 : (shift (shift s' n) 1) 0 = (shift (shift s m) (S m0)) 0). apply same_zero; auto.
  unfold shift in H5. simpl in H5.
  rewrite H4. rewrite H5.
  apply H0.
Qed.

Theorem stutter_equiv_same_first : forall A (s s' : Behavior A),
                                     stutter_equiv s s' ->
                                     s 0 = s' 0.
Proof.
  intros A s s' H.
  destruct H as (r,(H,(same_zero,_))).
  auto.
Qed.

Theorem stutter_equiv_induct_next'_base
     : forall (A : Type) (s s' : Behavior A) (R : A -> A -> Prop),
       stutter_equiv s s' ->
       R (s 0) (s 1) -> s 0 <> s 1 ->
       exists n : nat, R (s' n) (s' (S n)).
Proof.
  intros A s s' R H H1 H2.
  pose (H3 := stutter_equiv_stuttering_relation A).
  destruct H3 as (H3,(H4,H5)).
  assert (H6 : exists m, stutter_equiv s @ 1%behavior s' @ m%behavior /\
       (forall k : nat, k < m -> s' 0 = s' k)). apply H4; auto.
  destruct H6 as (m,(H6,H7)).
  assert (H0 : s 0 = s' 0). apply H3; auto.
  destruct m.
  apply H3 in H6. unfold shift in H6. simpl in H6.
  rewrite H0 in H2. rewrite H6 in H2. exfalso. apply H2; auto.
  exists m.
  apply H3 in H6. unfold shift in H6. simpl in H6.
  rewrite <- H6.
  specialize H7 with m. rewrite <- H7; auto.
  rewrite <- H0.
  auto.
Qed.

Theorem stutter_equiv_induct_next'
     : forall (A : Type) (s s' : Behavior A) (R : A -> A -> Prop),
       stutter_equiv s s' ->
       (exists n : nat, R (s n) (s (S n)) /\ s n <> s (S n)) ->
       exists n : nat, R (s' n) (s' (S n)).
Proof.
  intros A s s' R H H1.
  destruct H1 as (n,(H1,H2)).
  assert (H3 : exists m, stutter_equiv (shift s n) (shift s' m)). apply stutter_equiv_univ; auto.
  destruct H3 as (m,H3). 
  assert (H4 : exists n0, R ((s' @ m%behavior) n0) ((s' @ m%behavior) (S n0))).
  apply stutter_equiv_induct_next'_base with (s @ n%behavior); auto.
  destruct H4 as (n0,H4).
  unfold shift in H4. simpl in H4.
  exists (n0 + m); auto.
Qed.

Theorem stutter_equiv_induct_next''
     : forall (A : Type) (s s' : Behavior A) (R : A -> A -> Prop) (B : Type) (f : A -> B),
       stutter_equiv s s' ->
       (exists n : nat, R (s n) (s (S n)) /\ f (s n) <> f (s (S n))) ->
       exists n : nat, R (s' n) (s' (S n)) /\ f (s' n) <> f (s' (S n)).
Proof.
  intros A s s' R B f H H1.
  destruct H1 as (n,(H1,H2)).
  set (M := fun x y => R x y /\ f x <> f y).
  assert (H3 : exists m, M (s' m) (s' (S m))).
  apply stutter_equiv_induct_next' with s; auto.
  exists n. unfold M. repeat split; auto. intros N. apply H2; rewrite N; auto.
  auto.
Qed.


Require Import Relations.
Require Import Setoid.
Require Import Morphisms.
Import RelationClasses.

Add Parametric Relation A : (Behavior A) (@stutter_equiv A)
    reflexivity proved by (fun s => refl_stutter_equiv s)
    symmetry proved by (fun s s' H => sym_stutter_equiv H)
    transitivity proved by (fun s t s' H0 H1 => trans_stutter_equiv H0 H1)
      as stutter_equiv_rel.
