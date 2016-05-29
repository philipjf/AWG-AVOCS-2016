Require Import Logic.JMeq.
Set Universe Polymorphism.
Lemma JMeq_projT2 : forall (A : Type) (P : A -> Type) (a b : sigT P), a = b -> JMeq (projT2 a) (projT2 b).
Proof.
  intros A P a b H.
  rewrite H.
  auto.
Qed.  

Inductive V : Type :=
  mk_V : forall (T : Type), (T -> V) -> V.
Definition proj1_V (x : V) : Type := match x with
  | mk_V T F => T
  end.

Definition proj2_V (x : V) : proj1_V x -> V := match x with
  | mk_V T F => F
  end.

Inductive equiv_V : V -> V -> Prop :=
  bisim_V : forall (T : Type) (S : Type) (RT : T -> V) (RS : S -> V) (R : T -> S -> Prop),
    (forall x, exists y, R x y)
    -> (forall y, exists x, R x y)
    -> (forall x y, R x y -> equiv_V (RT x) (RS y))
    -> equiv_V (mk_V T RT) (mk_V S RS).

Lemma equiv_V_rep : forall (T S : Type) (RT : T -> V) (RS : S -> V), equiv_V (mk_V T RT) (mk_V S RS) ->
  exists R, (forall x, exists y, R x y) /\ (forall y, exists x, R x y) /\ (forall x y, R x y -> equiv_V (RT x) (RS y)) /\ equiv_V (mk_V T RT) (mk_V S RS).
Proof.
  intros T S RT RS H.
  inversion H.
  exists R; split; try split; try split; auto.
  intros x y H7.
  apply JMeq_projT2 in H1.
  simpl in H1. apply JMeq_eq in H1.
  apply JMeq_projT2 in H3.
  simpl in H3. apply JMeq_eq in H3.
  rewrite <- H1. rewrite <- H3; auto.
Qed. 

Theorem reflexive_equiv_V : forall (s : V), equiv_V s s.
Proof.
  intros s.
  induction s.
  apply bisim_V with (fun x => fun y => x = y); auto.
  intros x. exists x. auto.
  intros y. exists y. auto.
  intros x y H0. rewrite H0. apply H; auto.
Qed.

Theorem symmetric_equiv_V : forall (s t : V), equiv_V s t -> equiv_V t s.
Proof.
  intros s t H.
  induction H.
  apply bisim_V with (fun x => fun y => R y x); firstorder.
Qed.


Theorem transitive_equiv_V : forall s t u, equiv_V s u -> equiv_V u t -> equiv_V s t.
Proof.
  intros s t u H H0.
  generalize dependent t.
  induction H.
  intros t H3.
  destruct t as (U,RU).
  apply equiv_V_rep in H3.
  destruct H3 as (R2,(H3,(H4,(H5,H6)))).
  apply bisim_V with (fun x y => exists z, R x z /\ R2 z y).
  intros x. specialize H with x. destruct H as (z,H).
  specialize H3 with z. destruct H3 as (y,H3).
  firstorder.
  intros y. specialize H4 with y. destruct H4 as (x,R4).
  specialize H0 with x. destruct H0 as (z,H0).
  firstorder.
  firstorder.
Qed.

Require Export Setoid.
(* Require Export SetoidClass. *)

Lemma transitive_equiv_V' : transitive V equiv_V.
Proof.
  unfold transitive.
  intros x y z H H0.
  apply transitive_equiv_V with y; auto.
Qed.

Add Parametric Relation : V equiv_V
  reflexivity proved by reflexive_equiv_V
  symmetry proved by symmetric_equiv_V
  transitivity proved by transitive_equiv_V'
  as V_rel.

Inductive elem (x : V) : V -> Prop :=
  is_elem : forall T F (t : T), equiv_V (F t) x -> elem x (mk_V T F).

Theorem elem_rep : forall T F s, elem s (mk_V T F) -> exists b, equiv_V (F b) s.
Proof.
  intros T F s H.
  inversion H as (T0,F0,b,H0,H1).
  exists b; auto.
Qed.

Theorem elem_exten_r : forall a b s, equiv_V a b -> elem s a -> elem s b.
Proof.
  intros a b s H H0.
  inversion H0 as (T,F,t,H1,H2).
  rewrite <- H2 in H.
  destruct b as (S,G).
  apply equiv_V_rep in H.
  destruct H as (R,(H3,(H4,(H5,H6)))).
  specialize H3 with t. destruct H3 as (t',H3).
  apply is_elem with t'.
  apply transitive_equiv_V with (F t); auto.
  apply symmetric_equiv_V; auto.
Qed.

Theorem elem_exten_l : forall s s' a, equiv_V s s' -> elem s a -> elem s' a.
Proof.
  intros s s' a H H0.
  inversion H0 as (T,F,t,H1,H2).
  apply is_elem with t.
  apply transitive_equiv_V with s; auto.
Qed.
(*
Add Parametric Morphism : elem with
  signature equiv_V ==> equiv_V ==> iff as elem_mor.
Proof.
  intros x y H x0 y0 H0.
  split; intros H1.
  apply elem_exten_l with x; auto.
  apply elem_exten_r with x0; auto.
  apply elem_exten_l with y. symmetry; auto.
  apply elem_exten_r with y0; auto. symmetry; auto.
Qed.
*)
Theorem extensionality : forall (a b : V), (forall s, elem s a <-> elem s b) -> equiv_V a b.
Proof.
  intros a b H.
  destruct a as (T,F).
  destruct b as (S,G).
  apply bisim_V with (fun x y => equiv_V (F x) (G y)).
  intros x.
    assert (H0 : elem (F x) (mk_V S G)). apply H.
    apply is_elem with x. apply reflexive_equiv_V.
    inversion H0 as (T0,F0,t,H1,H2).
    exists t. apply symmetric_equiv_V; auto.
  intros y.
    assert (H0 : elem (G y) (mk_V T F)). apply H.
    apply is_elem with y. apply reflexive_equiv_V.
    inversion H0 as (T0,F0,t,H1,H2).
    exists t. auto.
  auto.
Qed.    


Definition subset s t := forall a, elem a s -> elem a t.

Theorem subset_exten : forall s s' t t', equiv_V s s' -> equiv_V t t' -> subset s t -> subset s' t'.
Proof.
  intros s s' t t' H H0 H1 a H2.
  unfold subset in H1.
  specialize H1 with a.
  apply elem_exten_r with t; auto.
  apply H1.
  apply elem_exten_r with s'; auto.
  apply symmetric_equiv_V; auto.
Qed.

Definition powerset (x : V) : V := match x with
  | mk_V T F => mk_V (T -> Prop) (fun P => mk_V {y : T | P y} (fun r => F (proj1_sig r)))
  end.

Theorem powerset_is_powerset : forall s t, elem t (powerset s) <-> subset t s.
Proof.
  intros s t.
  split.
  intros H.  destruct s as (T,F). simpl in H.
  inversion H as (S,G,x,H0,H1).
  apply JMeq_projT2 in H2. simpl in H2. apply JMeq_eq in H2.
  intros a H3.
  assert (H4 : elem a (G x)). apply elem_exten_r with t; auto. 
    apply symmetric_equiv_V. auto.
  clear H3.
  rewrite H2 in H4.
  inversion H4 as (U,FU,z,H3,H5).
  apply JMeq_projT2 in H6. simpl in H6. apply JMeq_eq in H6.
  destruct z as (z,Hz).
  apply is_elem with z.
  rewrite H6 in H3. simpl in H3. auto.
  intros H.
  unfold subset in H.
  destruct s as (S,G).
  simpl.
  destruct t as (T,F).
  apply is_elem with (fun s => exists t, equiv_V (G s) (F t)).
  apply bisim_V with (fun x y => equiv_V (G (proj1_sig x)) (F y)); try firstorder.
  destruct x as (x,H0). auto.
  assert (H1 : elem (F y) (mk_V S G)). apply H.
  apply is_elem with y. apply reflexive_equiv_V.
  inversion H1 as (T0, F0, y0, H0, H2).
  assert (H4 : exists t : T, equiv_V (F0 y0) (F t)). exists y; auto.
  set (x := exist (fun y1 => exists t : T, equiv_V (F0 y1) (F t)) y0 H4).
  exists x.
  auto.
Qed.

Theorem powerset_exten : forall s s', equiv_V s s' -> equiv_V (powerset s) (powerset s').
Proof.
  intros s s' H.
  apply extensionality.
  intros s0.
  split.
  intros H0.
  apply powerset_is_powerset.
  apply subset_exten with s0 s. reflexivity. auto.
  apply powerset_is_powerset; auto.
  intros H0.
  apply powerset_is_powerset.
  apply subset_exten with s0 s'. reflexivity. symmetry; auto.
  apply powerset_is_powerset; auto.
Qed.

Definition emptyset : V := mk_V Empty_set (Empty_set_rect (fun x => V)).

Lemma emptyset_is_empty : forall x, ~ elem x emptyset.
Proof.
  intros x H.
  inversion H as (T,F,t,H0,H1).
  inversion t.
Qed.

Theorem epsilon_induction : forall (P : V -> Prop), (forall x y, equiv_V x y -> P x -> P y) -> (forall x, (forall y, elem y x -> P y) -> P x) -> forall x, P x.
Proof.
  intros P E H x.
  induction x.
  apply H.
  intros y H1.
  inversion H1.  
  apply E with (F0 t); auto.
  apply JMeq_projT2 in H4.
  apply JMeq_eq in H4.
  simpl in H4.
  rewrite H4. auto.
Qed.

Definition singleton (x : V) : V := mk_V unit (fun y => x).

Theorem singleton_exten : forall x x', equiv_V x x' -> equiv_V (singleton x) (singleton x').
  intros x x' H.
  unfold singleton.
  apply bisim_V with (fun a b => True); firstorder.
Qed.

Theorem signleton_single : forall x, elem x (singleton x) /\ forall y, elem y (singleton x) -> equiv_V x y.
Proof.
  intros x. split.
  unfold singleton.
  apply is_elem; auto.
  apply tt.
  apply reflexive_equiv_V.
  intros y H.
  unfold singleton in H.
  inversion H.
  apply JMeq_projT2 in H2.
  apply JMeq_eq in H2.
  simpl in H2.
  rewrite H2 in H1.
  auto.
Qed.  

Definition pair (a : V) (b : V) : V := mk_V bool (fun x => if x then a else b).

Theorem pair_extens : forall a a' b b', equiv_V a a' -> equiv_V b b' -> equiv_V (pair a b) (pair a' b').
Proof.
  intros a a' b b' H H0.
  apply bisim_V with (fun x y => x = y); auto; try (
  intros x; exists x; auto).
  intros x y H1. induction x; rewrite <- H1; auto.
Qed.

Theorem pair_pair : forall a b c, elem c (pair a b) <-> equiv_V a c \/ equiv_V b c.
Proof.
  intros a b c.
  unfold pair.
  split.
  intros H. inversion H as (T,F,x,H1,H2). 
  apply JMeq_projT2 in H0.  apply JMeq_eq in H0. simpl in H0. 
  rewrite -> H0 in H1.
  induction x; auto.
  intros H.
  destruct H.
  apply is_elem with true; auto.
  apply is_elem with false; auto.
Qed.

Definition union (x : V) : V := match x with
  | mk_V T F => mk_V {x : T & proj1_V (F x)} (
     fun (y : {x : T & proj1_V (F x)}) => 
       let (x, y0) := y
       in proj2_V (F x) y0
     )
  end.

Theorem union_is_union : forall x, forall a, (exists b, elem a b /\ elem b x) <-> elem a (union x). 
Proof.
  intros x a.
  split.
  intros H. destruct H as (b,(H,H0)).
  inversion H0 as (T,F,t,H1,H2).
  assert (H3 : elem a (F t)). apply elem_exten_r with b; auto.
  apply symmetric_equiv_V. auto.
  inversion H3 as (S,G,s,H4,H5).
  simpl.
  assert (H6 : proj1_V (mk_V S G) = proj1_V (F t)). rewrite H5. auto.
  simpl in H6.
  assert (H7 : exists (G : proj1_V (F t) -> V) (s : proj1_V (F t)), mk_V (proj1_V (F t)) G = F t /\ equiv_V (G s) a).
  rewrite <- H6. exists G. exists s. auto. 
  clear H4. clear H5.  clear H6. clear s. clear G. clear S.
  destruct H7 as (G,(s,(H4,H5))).
  assert (H6 : JMeq (proj2_V (mk_V (proj1_V (F t)) G)) (proj2_V (F t))).
  rewrite H4. auto.
  simpl in H6.
  apply JMeq_eq in H6.
  rewrite H6 in H5.
  apply is_elem with (existT (fun r => proj1_V (F r)) t s); auto.
  destruct x as (T,F).
  simpl.
  intros H.
  inversion H as (T0,G,t,H0,H1). clear H1. clear T0.
  apply JMeq_projT2 in H2. apply JMeq_eq in H2. simpl in H2.
  rewrite H2 in H0. clear H2. clear G.
  destruct t as (x,s).
  assert (R : F x = mk_V (proj1_V (F x)) (proj2_V (F x))).
  assert (H1 : exists y, y = F x). exists (F x); auto.
  destruct H1 as (y,H1). rewrite <- H1.
  induction y; auto.
  assert (H1 : exists s, equiv_V (proj2_V (mk_V (proj1_V (F x)) (proj2_V (F x))) s) a). rewrite <- R. exists s; auto.
  clear H0. clear s. destruct H1 as (s,H0).
  exists (mk_V (proj1_V (F x)) (proj2_V (F x))).
  split.
  apply is_elem with s. simpl in H0. auto.
  apply is_elem with x. rewrite <- R. apply reflexive_equiv_V.
Qed.

Fixpoint encode_nat (n : nat) : V := match n with
  | 0 => emptyset
  | S m => singleton (encode_nat m)
end.

Lemma encoded_s_zero_differ : forall n, ~ equiv_V (encode_nat (S n)) (encode_nat 0).
Proof.
  intros n H.
  simpl in H.
  assert (H0 : elem (encode_nat n) emptyset).
  apply elem_exten_r with (encode_nat (S n)); simpl; auto.
  unfold singleton. apply is_elem with tt; auto. apply reflexive_equiv_V.
  unfold emptyset in H0.
  inversion H0 as (T,F,t,H1,H2).
  inversion t.
Qed.

Theorem same_encoded_nat : forall n m, equiv_V (encode_nat n) (encode_nat m) -> n = m.
Proof.
  intros n.
  induction n.
  intros m H.  destruct m; auto.
  apply symmetric_equiv_V in H.
  apply encoded_s_zero_differ in H. inversion H.
  intros m H.
  destruct m.
  apply encoded_s_zero_differ in H. inversion H.
  simpl in H.
  unfold singleton in H.
  apply equiv_V_rep in H.
  destruct H as (R,(H0,(H1,(H2,H3)))).
  assert (H4 : forall x y, R x y -> x = y).
  intros x y H. induction x. induction y; auto.
  assert (H5 : forall x y, R x y). intros x y. induction x. specialize H0 with tt.
  destruct H0 as (z,H0). induction z. induction y. auto.
  assert (H6 : n = m). apply IHn.
  apply H2 with tt tt. auto.
  auto.
Qed.

Definition naturals := mk_V nat encode_nat.

Theorem natural_equiv_encode_nat : forall v, elem v naturals <-> exists n, equiv_V v (encode_nat n).
Proof.
  intros v.
  split.
  unfold naturals.
  intros H.
  inversion H as (T,F,t,H0,H1).
  exists t. apply symmetric_equiv_V. auto.
  intros H.
  destruct H as (n,H).
  apply is_elem with n.
  apply symmetric_equiv_V; auto.
Qed.

Lemma encode_nat_in_naturals  : forall n, elem (encode_nat n) naturals.
Proof.
  intros n.
  apply natural_equiv_encode_nat.
  exists n; apply reflexive_equiv_V.
Qed.

Theorem set_cannot_contain_self : forall v, ~elem v v.
Proof.
  apply epsilon_induction.
  intros x y H H0 H1.
  apply H0. apply elem_exten_r with y. apply symmetric_equiv_V; auto.
  apply elem_exten_l with y. apply symmetric_equiv_V; auto.
  auto.
  intros x H H0.
  apply H with x; auto.
Qed.

Definition specification (s : V) (P : V -> Prop) :=
  match s with
  | mk_V T F => mk_V {x : T | P (F x)} (fun y => F (proj1_sig y))
  end.

Theorem specification_ext : forall s s' (P : V -> Prop), (forall x x', equiv_V x x' -> P x -> P x')
  -> equiv_V s s' -> equiv_V (specification s P) (specification s' P).
Proof.
  intros s s' P H H0.
  destruct s as (T,F).
  destruct s' as (S,G).
  simpl.
  apply equiv_V_rep in H0.
  destruct H0 as (R,(H1,(H2,(H3,H4)))).
  apply bisim_V with (fun a b => R (proj1_sig a) (proj1_sig b)).
  intros x.
  destruct x as (x,Hx).
  specialize H1 with x. destruct H1 as (y,Rxy).
  assert (Hy : P (G y)). apply H with (F x); auto.
  exists (exist (fun r => P (G r)) y Hy). auto.
  intros y. destruct y as (y,Hy).
  specialize H2 with y. destruct H2 as (x,Rxy).
  assert (Hx : P (F x)). apply H with (G y); auto.
  apply symmetric_equiv_V. apply H3; auto.
  exists (exist (fun r => P (F r)) x Hx); auto.
  auto.
Qed.

Theorem specification_spec : forall a s (P : V -> Prop), (forall x x', equiv_V x x' -> P x -> P x') -> elem a (specification s P) <-> elem a s /\ P a.
Proof.
  intros a s P H.
  split.
  intros H0.
  destruct s as (T,F). inversion H0 as (T0,F0,t,H1,H2).
  apply JMeq_projT2 in H3. apply JMeq_eq in H3. simpl in H3.
  rewrite H3  in H1.
  destruct t as (x,PFx).
  simpl in H1.
  split.
  apply is_elem with x; auto.
  apply H with (F x); auto.  
  intros H0.
  destruct H0 as (H0,H1).
  inversion H0 as (T,F,t,H2,H3).
  simpl.
  assert (H4 : P (F t)). apply H with a; auto. apply symmetric_equiv_V; auto.
  apply is_elem with (exist (fun r => P (F r)) t H4).
  auto.
Qed.


Definition replacement (f : V -> V) (u : V) := match u with
  | mk_V T F => mk_V T (fun x => f (F x))
end.

Theorem replacement_exten : forall f g u u', (forall s s', equiv_V s s' -> equiv_V (f s) (g s'))
  -> (forall s, equiv_V (f s) (g s)) -> equiv_V u u' -> equiv_V (replacement f u) (replacement g u').
Proof.
  intros f g u u' H H0 H1.
  destruct u as (T,F).
  destruct u' as (S,G).
  apply equiv_V_rep in H1.
  destruct H1 as (R,(H2,(H3,(H4,H5)))).
  simpl.  
  apply bisim_V with R; auto.
Qed.

Theorem replacement_replaces : forall f u b, (forall s s', equiv_V s s' -> equiv_V (f s) (f s')) -> (exists a, elem a u /\ equiv_V b (f a)) <-> elem b (replacement f u).
Proof.
  intros f u b H.
  destruct u as (T,F). simpl.
  split. 
  intros H0. destruct H0 as (a,(H0,H1)).
  apply elem_rep in H0. destruct H0 as (t, H0).
  apply is_elem with t.
  apply transitive_equiv_V with (f a); auto. 
  apply symmetric_equiv_V; auto.
  intros H0.
  apply elem_rep in H0. destruct H0 as (t,H0).
  exists (F t). split.
  apply is_elem with t; auto. apply reflexive_equiv_V.
  apply symmetric_equiv_V; auto.
Qed.

Section promoteV.
Universe less.
Universe more.
Constraint less < more.
Definition promoteT (t : Type@{less}) : Type@{more} := t.

Definition promote (x : V@{less}) : V@{more} := V_rect (fun x => V) (fun T v rec => mk_V (promoteT T) rec) x.
End promoteV.

Lemma promote_elem : forall a b, elem a (promote b) -> exists c, equiv_V a (promote c).
Proof.
  intros a b. generalize dependent a.
  induction b.
  intros a H0.  
  apply elem_rep in H0.
  destruct H0 as (b, H0).
  unfold promoteT in *.
  exists (v b). symmetry. auto.
Qed.

Definition U : V := mk_V V promote.


Definition transitive_set s : Prop := forall a b, elem a b -> elem b s -> elem a s.
Definition pairclosed_set s : Prop := forall a b, elem a s -> elem b s -> elem (pair a b) s.
Definition powersetclosed_set s : Prop := forall a, elem a s -> elem (powerset a) s.
Definition familyclosed_set s : Prop := forall T F, (forall (t : T), elem (F t) s) -> elem (mk_V T F) s.

Definition Grothendieck_universe s : Prop := transitive_set s
                                             /\ pairclosed_set s
                                             /\ powersetclosed_set s
                                             /\ familyclosed_set s.

Lemma U_transitive : transitive_set U.
Proof.
  unfold U.
  unfold transitive_set.
  intros a b H H0.
  apply elem_rep in H0.
  destruct H0 as (t,H0).
  assert (H1: elem a (promote t)). apply elem_exten_r with b; auto. symmetry; auto.
  apply promote_elem in H1.
  destruct H1 as (c,H1).  
  apply elem_exten_l with (promote c). symmetry; auto.
  apply is_elem with c. reflexivity.
Qed.  

Lemma U_pairclosed : pairclosed_set U.
Proof.
  unfold U.
  unfold pairclosed_set.
  intros a b H H0.
  apply elem_rep in H.
  destruct H as (t,H).
  apply elem_rep in H0.
  destruct H0 as (s,H0).
  apply is_elem with (mk_V bool (fun x => if x then t else s)).  
  unfold pair.
  simpl. unfold promoteT.
  apply bisim_V with (fun a b => a = b).
  intros x. exists x; auto.
  intros x. exists x; auto.
  intros x y H1. rewrite H1. induction y; auto.
Qed.

Lemma promotion_equiv : forall s, equiv_V (promote s) s.
Proof.
  intros s.
  induction s.
  simpl. unfold promoteT.
  apply bisim_V with (fun a b => a = b).
  intros x. exists x. auto.
  intros x. exists x. auto.
  intros x y H0. rewrite H0. apply H.
Qed.

Lemma U_familyclosed : familyclosed_set U.
Proof.
  unfold familyclosed_set.
  intros T F H.
  apply is_elem with (mk_V T F).
  apply promotion_equiv.
Qed.


Lemma U_powersetclosed : powersetclosed_set U.
Proof.
  Admitted.
(*
  unfold powersetclosed_set. unfold U.
  intros a H.
  apply elem_rep in H.
  destruct H as (b,H).
  apply is_elem with (powerset b).
  apply transitive_equiv_V with (powerset (promote b)).
  destruct b as (T,F).
  simpl.
  apply reflexive_equiv_V.
*)

Set Printing Universes.
Check U_powersetclosed.

Theorem U_universe : Grothendieck_universe U.
Proof.
  repeat split.
  apply U_transitive.
  apply U_pairclosed.
  apply U_powersetclosed.
  apply U_familyclosed.
Qed.