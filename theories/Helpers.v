(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Small dependent-list and proof-transport helpers used across the library. *)

Require Import Corelib.Relations.Relation_Definitions.
From Stdlib Require Import List.

Import ListNotations.

(* There is [SigTNotations] for [sigT] but nothing for [sig]. *)
Notation "( x ; y )" := (@exist _ _ x y) (at level 0, format "( x ; '/ ' y )").
Notation "x .1" := (proj1_sig x) (at level 1, left associativity, format "x .1").
Notation "x .2" := (proj2_sig x) (at level 1, left associativity, format "x .2").

Ltac inv x := inversion x; subst; clear x.

(** The eta law for the [sig] inductive type. *)
Lemma sig_eta :
  forall {A : Type} (P : A -> Prop) (p : sig P), p = (p.1; p.2).
Proof.
  intros A P p.
  destruct p. simpl. auto.
Qed.

(** Function application at the [Forall] level. *)
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

(** Modus ponens at the [Forall] level. *)
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

(** Over a list where every element satisfies [P] or [Q], either some element
   satisfies [P] or all elements satisfy [Q]. *)
Lemma split_exists_or_forall :
  forall {A : Type} (P Q : A -> Prop) (l : list A),
    (forall x, In x l -> P x \/ Q x) ->
    (exists x, In x l /\ P x) \/ (forall x, In x l -> Q x).
Proof.
  intros A P Q l.
  induction l as [|a l IH]; intros Hall.
  - right; intros x Hin; inversion Hin.
  - destruct (Hall a (or_introl eq_refl)) as [HaP | HaQ].
    + left; exists a; split; [left; reflexivity | exact HaP].
    + assert (Hall_tail : forall x : A, In x l -> P x \/ Q x)
        by (intros x Hin; apply Hall; right; exact Hin).
      destruct (IH Hall_tail) as [Hex | HallQ].
      * left; destruct Hex as [x [Hin HP]].
        exists x; split; [right; exact Hin | exact HP].
      * right; intros x Hin.
        destruct Hin as [Hx | Hin']; [subst; exact HaQ | apply HallQ; exact Hin'].
Qed.

(** Pointwise implication between filter predicates bounds the filtered
   lengths. *)
Lemma filter_impl_length_le :
  forall {A : Type} (f g : A -> bool) (l : list A),
    (forall x, In x l -> f x = true -> g x = true) ->
    length (filter f l) <= length (filter g l).
Proof.
  intros A f g l; induction l as [|a l IH]; intros Himpl; simpl; [apply le_n|].
  destruct (f a) eqn:Ef.
  - rewrite (Himpl a (or_introl eq_refl) Ef); simpl.
    apply le_n_S, IH.
    intros x Hx; apply Himpl; right; exact Hx.
  - destruct (g a); simpl.
    + apply le_S, IH.
      intros x Hx; apply Himpl; right; exact Hx.
    + apply IH.
      intros x Hx; apply Himpl; right; exact Hx.
Qed.

(** A filter whose predicate rejects every element is empty. *)
Lemma filter_none :
  forall {A : Type} (f : A -> bool) (l : list A),
    (forall x, In x l -> f x = false) -> filter f l = [].
Proof.
  intros A f l H; induction l as [|a l IH]; simpl; auto.
  rewrite (H a) by (left; auto).
  apply IH; intros x Hx; apply H; right; auto.
Qed.

(** A filter whose predicate accepts every element is the identity. *)
Lemma filter_all :
  forall {A : Type} (f : A -> bool) (l : list A),
    (forall x, In x l -> f x = true) -> filter f l = l.
Proof.
  intros A f l H; induction l as [|a l IH]; simpl; auto.
  rewrite (H a) by (left; auto).
  f_equal; apply IH; intros x Hx; apply H; right; auto.
Qed.

(** A prefix of a constant list is the shorter constant list. *)
Lemma firstn_repeat_le :
  forall {A : Type} (x : A) n i, i <= n -> firstn i (repeat x n) = repeat x i.
Proof.
  intros A x n; induction n as [|k IH]; intros i Hi.
  - assert (i = 0) by (destruct i; [reflexivity | inversion Hi]); subst;
      reflexivity.
  - destruct i as [|j]; auto.
    simpl; f_equal; apply IH.
    apply le_S_n; exact Hi.
Qed.

(** An injective map preserves [NoDup]. *)
Lemma NoDup_map_inj :
  forall {A B : Type} (f : A -> B) (l : list A),
    (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
Proof.
  intros A B f l Hinj Hnd; induction Hnd as [|a l Ha Hnd IH]; simpl;
    constructor; auto.
  intros Hin; apply in_map_iff in Hin; destruct Hin as [y [Hy Hiny]].
  apply Hinj in Hy; subst; contradiction.
Qed.

(** Concatenating duplicate-free disjoint lists preserves [NoDup]. *)
Lemma NoDup_app_disj :
  forall {A : Type} (l1 l2 : list A),
    NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) ->
    NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 H1; induction H1 as [|a l1 Ha H1 IH]; intros H2 Hd; simpl; auto.
  constructor.
  - intros Hin; apply in_app_iff in Hin; destruct Hin as [Hin | Hin].
    + contradiction.
    + apply (Hd a); auto; left; auto.
  - apply IH; auto.
    intros x Hx; apply Hd; right; auto.
Qed.

(** [existsb] and [forallb] commute with [map]. *)
Lemma existsb_map :
  forall {A B : Type} (f : B -> bool) (g : A -> B) (l : list A),
    existsb f (map g l) = existsb (fun x => f (g x)) l.
Proof.
  intros A B f g l; induction l as [|a l IH]; simpl; congruence.
Qed.

Lemma forallb_map :
  forall {A B : Type} (f : B -> bool) (g : A -> B) (l : list A),
    forallb f (map g l) = forallb (fun x => f (g x)) l.
Proof.
  intros A B f g l; induction l as [|a l IH]; simpl; congruence.
Qed.

(** A test that ignores its argument is the test, on any nonempty list. *)
Lemma existsb_const :
  forall {A : Type} (c : bool) (l : list A),
    l <> [] -> existsb (fun _ => c) l = c.
Proof.
  intros A c l Hne; destruct c.
  - destruct l as [|a l]; [contradiction | reflexivity].
  - clear Hne; induction l as [|a l IH]; simpl; congruence.
Qed.

(** Pointwise equal tests agree under [existsb]. *)
Lemma existsb_ext_in :
  forall {A : Type} (f g : A -> bool) (l : list A),
    (forall x, In x l -> f x = g x) -> existsb f l = existsb g l.
Proof.
  intros A f g l; induction l as [|a l IH]; intros H; simpl; auto.
  rewrite (H a (or_introl eq_refl)), IH; auto.
  intros x Hx; apply H; right; auto.
Qed.

(** Convert a list of [P]-satisfying dependent pairs (i.e. [sig]),
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

(** Same thing as [distribute], but this auxiliary function takes
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

(** Convert a [list] and a proof that all the elements of the list satisfy [P],
   into a list of dependent pairs where each element satisfies [P]. *)
Definition distribute
  {A : Type} {P : A -> Prop}
  (lpf : {l : list A | Forall P l}) : list {a : A | P a} :=
  zip_proofs lpf.1 lpf.2.

(** To show that round trip between distribute and unite preserves the elements. *)
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

(** To show that round trip between distribute and unite preserves the elements. *)
Lemma unite_distribute :
  forall
    {A : Type} {P : A -> Prop} (l : list A) (pf : Forall P l),
  (unite (distribute (l; pf))).1 = l.
Proof.
  unfold distribute; simpl.
  intros A P l pf.
  induction l; simpl; f_equal; auto.
Qed.

(** If the dependent pair (a; p) is in the [distribute]d list,
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
