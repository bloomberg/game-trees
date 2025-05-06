(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

Require Import List.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Import ListNotations.

(* There is [SigTNotations] for [sigT] but nothing for [sig]. *)
Notation "( x ; y )" := (@exist _ _ x y) (at level 0, format "( x ; '/ ' y )").
Notation "x .1" := (proj1_sig x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (proj2_sig x) (at level 1, left associativity, format "x .2").

Ltac inv x := inversion x; subst; clear x.

Lemma sig_surjective :
  forall {A : Type} (P : A -> Prop) (p : sig P), p = (p.1; p.2).
Proof.
  intros A P p.
  destruct p. simpl. auto.
Qed.

Lemma Forall_mp :
  forall {A : Type}
         (P Q : A -> Prop)
         (l : list A),
  Forall (fun a => P a -> Q a) l ->
  Forall (fun a => P a) l ->
  Forall (fun a => Q a) l.
Proof.
  intros A P Q l pf1 pf2.
  induction l; auto.
  inversion pf1; subst.
  inversion pf2; subst.
  eapply Forall_cons; auto.
Qed.

Fixpoint unite
  {A : Type} (P : A -> Prop) (l : list {a : A | P a}) : {l : list A | Forall P l}.
Proof.
  destruct l as [|x xs].
  exists []. constructor.
  pose proof (xs' := unite A P xs).
  exists (x.1 :: xs'.1).
  constructor.
  exact (x.2).
  exact (xs'.2).
Defined.

Fixpoint zip_proofs
  {A : Type} (P : A -> Prop)
  (l : list A) (pf : Forall P l) {struct l} : list {a : A | P a}.
Proof.
  destruct l as [|x xs].
  * refine [].
  * refine ((x; _) :: @zip_proofs A P xs _); inversion pf; auto.
Defined.

Definition distribute
  {A : Type} (P : A -> Prop)
  (lpf : {l : list A | Forall P l}) : list {a : A | P a} :=
  zip_proofs P lpf.1 lpf.2.

(* To show that round trip between distribute and unite preserves the elements. *)
Lemma distribute_unite :
  forall
    {A : Type} (P : A -> Prop) (l : list {a : A | P a}),
  distribute P (unite P l) = l.
Proof.
  unfold distribute.
  intros A P l.
  induction l; simpl; auto.
  f_equal. simpl.
  rewrite sig_surjective; auto.
  auto.
Qed.

(* To show that round trip between distribute and unite preserves the elements. *)
Lemma unite_distribute :
  forall
    {A : Type} (P : A -> Prop) (l : list A) (pf : Forall P l),
  (unite P (distribute P (l; pf))).1 = l.
Proof.
  unfold distribute; simpl.
  intros A P l pf.
  induction l; simpl; f_equal; auto.
Qed.

Lemma Forall_unite_map_distribute :
  forall
    {A : Type}
    {P1 P2 : A -> Prop}
    (f : sig P2 -> sig P2)
    (l : list A) (pf : Forall P2 l),
  (forall (a : A) (p1 : P1 a) (p2 : P2 a), P1 (f (a; p2)).1) ->
  Forall P1 l ->
  Forall P1 (unite P2 (map f (distribute P2 (l; pf)))).1.
Proof.
  unfold distribute; simpl.
  intros A P1 P2 f l pf1 pf2 pf3.
  induction l.
  simpl; constructor.
  constructor.
  simpl.
  eapply pf2.
  inv pf3; auto.
  eapply IHl.
  inv pf3; auto.
Qed.

Lemma proj1_unite_map_distribute :
  forall {A : Type} (P : A -> Prop)
         (f1 : sig P -> sig P)
         (f2 : sig P -> sig P)
         (l : list A) (pf1 pf2 : Forall P l),
  (forall (a : A) (p1 p2 : P a), (f1 (a; p1)).1 = (f2 (a; p2)).1) ->
    (unite P (map f1 (distribute P (l; pf1)))).1
  = (unite P (map f2 (distribute P (l; pf2)))).1.
Proof.
  unfold distribute; simpl.
  intros A P f1 f2 l pf1 pf2 eq.
  induction l; simpl.
  auto.
  f_equal.
  eapply eq.
  eapply IHl.
Qed.

Lemma In_distribute :
  forall
    {A : Type} (P : A -> Prop)
    (l : {l : list A | Forall P l})
    (a : A) (p : P a),
  In (a; p) (distribute P l) -> In a l.1 /\ P a.
Proof.
  intros A P l a p pf.
  destruct l as [l pf'].
  induction l; intuition.
  destruct pf.
  left. pose proof (eq := proj1_sig_eq H). simpl in eq; auto.
  right.
  simpl in IHl.
  refine (proj1 (IHl _ _)).
  unfold distribute.
  eauto.
Qed.
