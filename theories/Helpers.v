(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

Require Import Corelib.Relations.Relation_Definitions.
From Stdlib Require Import List.

Import ListNotations.

(* There is [SigTNotations] for [sigT] but nothing for [sig]. *)
Notation "( x ; y )" := (@exist _ _ x y) (at level 0, format "( x ; '/ ' y )").
Notation "x .1" := (proj1_sig x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (proj2_sig x) (at level 1, left associativity, format "x .2").

Ltac inv x := inversion x; subst; clear x.

(* The eta law for the [sig] inductive type. *)
Lemma sig_eta :
  forall {A : Type} (P : A -> Prop) (p : sig P), p = (p.1; p.2).
Proof.
  intros A P p.
  destruct p. simpl. auto.
Qed.

(* Function application at the [Forall] level. *)
Lemma Forall_appl :
  forall {A B : Type}
         (P : A -> B -> Prop)
         (l : list A),
  Forall (fun a => forall (b : B), P a b) l ->
  forall (b : B), Forall (fun a => P a b) l.
Proof.
  intros A B P l pf1 b.
  induction l; auto.
  inversion pf1; subst.
  eapply Forall_cons; auto.
Qed.

(* Modus ponens at the [Forall] level. *)
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

(* Convert a list of [P]-satisfying dependent pairs (i.e. [sig]),
   into a dependent pair of a [list] and that the entire list satisfies [P]. *)
Fixpoint unite
  {A : Type} {P : A -> Prop} (l : list {a : A | P a}) : {l : list A | Forall P l}.
Proof.
  destruct l as [|x xs].
  exists []. constructor.
  pose proof (xs' := unite A P xs).
  exists (x.1 :: xs'.1).
  constructor.
  exact (x.2).
  exact (xs'.2).
Defined.

(* Same thing as [distribute], but this auxiliary function takes
   the [list] and the proof separately so that
   it can do structural recursion on the list. *)
Fixpoint zip_proofs
  {A : Type} {P : A -> Prop}
  (l : list A) (pf : Forall P l) {struct l} : list {a : A | P a}.
Proof.
  destruct l as [|x xs].
  * refine [].
  * refine ((x; _) :: @zip_proofs A P xs _); inversion pf; auto.
Defined.

(* Convert a [list] and a proof that all the elements of the list satisfy [P],
   into a list of dependent pairs where each element satisfies [P]. *)
Definition distribute
  {A : Type} {P : A -> Prop}
  (lpf : {l : list A | Forall P l}) : list {a : A | P a} :=
  zip_proofs lpf.1 lpf.2.

(* To show that round trip between distribute and unite preserves the elements. *)
Lemma distribute_unite :
  forall
    {A : Type} {P : A -> Prop} (l : list {a : A | P a}),
  distribute (unite l) = l.
Proof.
  unfold distribute.
  intros A P l.
  induction l; simpl; auto.
  f_equal. simpl.
  rewrite sig_eta; auto.
  auto.
Qed.

(* To show that round trip between distribute and unite preserves the elements. *)
Lemma unite_distribute :
  forall
    {A : Type} {P : A -> Prop} (l : list A) (pf : Forall P l),
  (unite (distribute (l; pf))).1 = l.
Proof.
  unfold distribute; simpl.
  intros A P l pf.
  induction l; simpl; f_equal; auto.
Qed.

(* If the dependent pair (a; p) is in the [distribute]d list,
   then [a] was in the first projection of [l]. *)
Lemma In_distribute :
  forall
    {A : Type} {P : A -> Prop}
    (l : {l : list A | Forall P l})
    (a : A) (p : P a),
  In (a; p) (distribute l) -> In a l.1.
Proof.
  intros A P l a p pf.
  destruct l as [l pf'].
  induction l; intuition auto.
  destruct pf.
  left. pose proof (eq := proj1_sig_eq H). simpl in eq; auto.
  right.
  simpl in IHl; eauto.
Qed.
