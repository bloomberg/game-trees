(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

Require Import Corelib.Classes.Morphisms.
Require Import Corelib.Classes.RelationClasses.
Require Import Corelib.Relations.Relation_Definitions.
From Stdlib Require Import List.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Relations.Operators_Properties.
From Stdlib Require Import Program.Equality.

Require Import GameTrees.Helpers.
Require Import GameTrees.Trees.

Import ListNotations.

CoInductive colist (A : Type) : Type :=
| conil : colist A
| cocons : A -> colist A -> colist A.

Arguments conil {A}.
Arguments cocons {A} x xs.

CoInductive cotree (A : Type) : Type :=
| conode : A -> colist (cotree A) -> cotree A.

Arguments conode {A} a f.

Definition coforest (A : Type) : Type :=
  colist (cotree A).

Definition root {A : Type} (t : cotree A) : A :=
  match t with
  | conode a _ => a
  end.

Definition children {A : Type} (t : cotree A) : colist (cotree A) :=
  match t with
  | conode _ f => f
  end.

Definition comap {A B : Type} (f : A -> B) : colist A -> colist B :=
  cofix comap (l : colist A) : colist B :=
    match l with
    | conil => conil
    | cocons x xs => cocons (f x) (comap xs)
    end.

CoFixpoint comap_cotree {A B : Type} (g : A -> B) (t : cotree A) : cotree B :=
  match t with
  | conode a f => conode (g a) (comap (comap_cotree g) f)
  end.

Definition singleton_cotree {A : Type} (a : A) : cotree A := conode a conil.
Definition singleton_coforest {A : Type} (a : A) : coforest A := cocons (conode a conil) conil.

CoFixpoint colist_of_list {A : Type} (l : list A) : colist A :=
  match l with
  | [] => conil
  | x :: xs => cocons x (colist_of_list xs)
  end.

Definition coforest_of_list {A : Type} (l : list A) : coforest A :=
  comap singleton_cotree (colist_of_list l).

Fixpoint list_of_colist {A : Type} (fuel : nat) (l : colist A) {struct fuel} : list A :=
  match fuel with
  | O => nil
  | S fuel' =>
    match l with
    | conil => nil
    | cocons x xs => cons x (list_of_colist fuel' xs)
    end
  end.

Fixpoint tree_of_cotree {A : Type} (fuel : nat) (t : cotree A) {struct fuel} : tree A :=
  match t with
  | conode a f =>
    match fuel with
    | O => node a []
    | S fuel' =>
        node a (map (tree_of_cotree fuel') (list_of_colist fuel f))
    end
  end.

CoFixpoint unfold_cotree {A : Type} (next : A -> list A) (init : A) : cotree A :=
  conode init (comap (unfold_cotree next) (colist_of_list (next init))).

Definition finite_cotree {A : Type} (ct : cotree A) : Type :=
  { n : nat | tree_of_cotree n ct = tree_of_cotree (1 + n) ct }.

Theorem finite_cotree_means_tree :
  forall {A : Type} (ct : cotree A),
    finite_cotree ct ->
    { t : tree A | exists (n : nat), tree_of_cotree n ct = t }.
Proof.
  intros A ct [n eq].
  exists (tree_of_cotree n ct).
  exists n; auto.
Qed.

Inductive In_colist {A : Type} (x : A) : colist A -> Prop :=
| In_cocons_hd : forall xs, In_colist x (cocons x xs)
| In_cocons_tl : forall y xs, In_colist x xs -> In_colist x (cocons y xs).

Inductive CoExists {A : Type} (P : A -> Prop) : colist A -> Prop :=
| CoExists_cocons_hd : forall x l, P x -> CoExists P (cocons x l)
| CoExists_cocons_tl : forall x l, CoExists P l -> CoExists P (cocons x l).

Inductive In_cotree {A : Type} (a : A) : cotree A -> Prop :=
| In_conode : forall f, In_cotree a (conode a f)
| In_cochildren : forall a' f,
    CoExists (In_cotree a) f -> In_cotree a (conode a' f).

CoInductive CoForall {A : Type} (P : A -> Prop) : colist A -> Prop :=
| CoForall_conil : CoForall P conil
| CoForall_cocons : forall x l, P x -> CoForall P l -> CoForall P (cocons x l).

CoInductive Forall_conodes {A : Type} (P : A -> Prop) : cotree A -> Prop :=
| Forall_conodes_conode : forall a f, P a -> CoForall (Forall_conodes P) f -> Forall_conodes P (conode a f).

Lemma CoExists_exists :
  forall {A : Type} (P : A -> Prop) (l : colist A),
    CoExists P l <-> (exists x : A, In_colist x l /\ P x).
Proof.
  intros A P l; split.
  {
    intros pf.
    induction pf.
    repeat econstructor; eauto.
    destruct IHpf as [a [H1 H2]].
    exists a.
    split; auto.
    right; auto.
  }
  {
    intros pf.
    destruct pf as [x [H1 H2]].
    induction H1.
    left; auto.
    right; auto.
  }
Qed.

Lemma In_cotree_better_ind :
  forall (A : Type) (a : A) (P : cotree A -> Prop),
       (forall (f : coforest A), P (conode a f)) ->
       (forall (a' : A) (f : coforest A), CoExists (fun t => In_cotree a t /\ P t) f -> P (conode a' f)) ->
       forall (t : cotree A), In_cotree a t -> P t.
Proof.
  intros A a P tpf1 tpf2.
  refine (fix F (t : cotree A) (i : In_cotree a t) {struct i} : P t := _).
  inv i.
  eapply tpf1.
  eapply tpf2; eauto.
  induction H; [left | right]; intuition.
Qed.

Lemma CoForall_forall :
  forall {A : Type} (P : A -> Prop) (l : colist A),
    CoForall P l <-> (forall x : A, In_colist x l -> P x).
Proof.
  intros.
  split.
  { intros pf x i.
    induction i.
    inversion pf; subst; clear pf.
    auto.
    inversion pf; subst; clear pf.
    auto. }
  { generalize l; clear l.
    cofix C.
    intros l pf.
    destruct l; constructor.
    eapply pf; left; auto.
    eapply C.
    intros x i; eapply pf; right; auto. }
Qed.

CoInductive bisimilar_colist
            {A : Type}
            (R : relation A)
          : relation (colist A) :=
| conil_bisim : bisimilar_colist R conil conil
| cocons_bisim : forall a1 a2 l1 l2,
    R a1 a2 ->
    bisimilar_colist R l1 l2 ->
    bisimilar_colist R (cocons a1 l1) (cocons a2 l2).

Instance bisimilar_colist_Reflexive :
  forall {A : Type} (R : relation A) (r : @Reflexive A R), @Reflexive _ (bisimilar_colist R).
Proof.
  cofix C.
  intros A R r x.
  destruct x.
  constructor.
  constructor.
  eapply r; eauto.
  eapply C; eauto.
Qed.

Instance bisimilar_colist_Symmetric :
  forall {A : Type} (R : relation A) (r : @Symmetric A R), @Symmetric _ (bisimilar_colist R).
Proof.
  cofix C.
  intros A R r x y pf.
  destruct x, y.
  constructor.
  inv pf.
  inv pf.
  inv pf.
  constructor; eauto.
  eapply C; eauto.
Qed.

Instance bisimilar_colist_Transitive :
  forall {A : Type} (R : relation A) (r : @Transitive A R), @Transitive _ (bisimilar_colist R).
Proof.
  cofix C.
  intros A R r x y z pf1 pf2.
  destruct x, y, z.
  repeat constructor.
  inv pf2; inv H.
  repeat constructor.
  inv pf1.
  inv pf1.
  inv pf1.
  inv pf2.
  inv pf1; inv pf2.
  constructor; eauto.
  eapply C; eauto.
Qed.

CoInductive bisimilar_cotree
          {A : Type}
          (R : relation A)
          : relation (cotree A) :=
| conode_bisim : forall a1 a2 f1 f2,
    R a1 a2 ->
    bisimilar_colist (bisimilar_cotree R) f1 f2 ->
    bisimilar_cotree R (conode a1 f1) (conode a2 f2).

Instance bisimilar_cotree_Reflexive :
  forall {A : Type} (R : relation A) (r : @Reflexive A R), @Reflexive _ (bisimilar_cotree R).
Proof.
  cofix C1.
  intros A R r x.
  destruct x.
  constructor.
  eapply r; eauto.
  { generalize c; clear c.
    cofix C2.
    intros c; destruct c.
    constructor.
    constructor.
    eapply C1; eauto.
    eapply C2; eauto. }
Qed.

Instance bisimilar_cotree_Symmetric :
  forall {A : Type} (R : relation A) (r : @Symmetric A R), @Symmetric _ (bisimilar_cotree R).
Proof.
  cofix C1.
  intros A R r x y pf.
  destruct x, y.
  inv pf.
  constructor; eauto.
  { generalize c0 c H4.
    cofix C2.
    intros x y pf.
    destruct x, y.
    constructor.
    inv pf.
    inv pf.
    inv pf.
    constructor; eauto.
    eapply C1; eauto. }
Qed.

Instance bisimilar_cotree_Transitive :
  forall {A : Type} (R : relation A) (r : @Transitive A R), @Transitive _ (bisimilar_cotree R).
Proof.
  cofix C1.
  intros A R r x y z pf1 pf2.
  destruct x, y, z.
  constructor.
  { inv pf2.
    inv pf1.
    eapply r; eauto. }
  { inv pf1.
    inv pf2.
    generalize c c0 c1 H4 H6.
    cofix C2.
    intros x y z pf1 pf2.
    destruct x, y, z.
    repeat constructor.
    inv pf2.
    repeat constructor.
    inv pf1.
    inv pf1.
    inv pf1.
    inv pf2.
    inv pf1; inv pf2.
    constructor; eauto.
    eapply C1; eauto. }
Qed.

Definition colist_unfold {A : Type} (l : colist A) :=
  match l with conil => conil | cocons x xs => cocons x xs end.

Lemma colist_unfold_eq : forall {A : Type} (l : colist A), l = colist_unfold l.
Proof. destruct l; auto. Qed.

Definition cotree_unfold {A : Type} (t : cotree A) :=
  match t with conode a f => conode a f end.

Lemma cotree_unfold_eq : forall {A : Type} (t : cotree A), t = cotree_unfold t.
Proof. destruct t; auto. Qed.

Lemma CoForall_comap :
  forall {A B : Type} (f : A -> B) (P : B -> Prop) (l : colist A),
  CoForall P (comap f l) <-> CoForall (fun x : A => P (f x)) l.
Proof.
  intros A B f P l.
  split; intros pf.
  { generalize l pf; clear l pf.
    cofix C.
    intros l pf.
    destruct l.
    constructor.
    pattern (comap f (cocons a l)) in pf.
    rewrite colist_unfold_eq in pf; simpl in pf.
    constructor.
    inv pf; auto.
    eapply C.
    inv pf; auto.
  }
  { generalize l pf; clear l pf.
    cofix C.
    intros l pf.
    destruct l.
    pattern (comap f conil).
    rewrite colist_unfold_eq; simpl.
    constructor.
    pattern (comap f (cocons a l)).
    rewrite colist_unfold_eq; simpl.
    constructor.
    inv pf; auto.
    eapply C.
    inv pf; auto.
  }
Qed.

Lemma In_colist_iff_In_colist_of_list :
  forall {A : Type} (a : A) (l : list A),
    In a l <-> In_colist a (colist_of_list l).
Proof.
  intros A a l; split.
  { intros pf.
    induction l.
    inv pf.
    pattern (colist_of_list (a0 :: l)).
    rewrite colist_unfold_eq; simpl.
    inv pf.
    left.
    right; auto. }
  { induction l.
    { pattern (@colist_of_list A []).
      rewrite colist_unfold_eq; simpl.
      intros pf. inv pf. }
    {
      pattern (colist_of_list (a0 :: l)).
      rewrite colist_unfold_eq; simpl.
      intros pf.
      inv pf.
      left; auto.
      right; auto. } }
Qed.

Lemma CoForall_colist_of_list :
  forall {A : Type} (P : A -> Prop) (l : list A),
    CoForall P (colist_of_list l) <-> Forall P l.
Proof.
  intros A P l.
  rewrite CoForall_forall.
  rewrite Forall_forall.
  split; intros x pf pf'.
  rewrite -> In_colist_iff_In_colist_of_list in pf'; auto.
  rewrite <- In_colist_iff_In_colist_of_list in pf'; auto.
Qed.

Lemma in_comap :
  forall {A B : Type} (f : A -> B) (l : colist A) (x : A),
    In_colist x l -> In_colist (f x) (comap f l).
Proof.
  intros A B f l x i.
  induction i.
  pattern (comap f (cocons x xs)).
  rewrite colist_unfold_eq; simpl.
  left; auto.
  pattern (comap f (cocons y xs)).
  rewrite colist_unfold_eq; simpl.
  right; auto.
Qed.

Lemma comap_fusion :
  forall {A B C : Type}
         (R : relation C)
        `(r : Reflexive C R)
         (f : A -> B) (g : B -> C)
         (l : colist A),
         bisimilar_colist R (comap g (comap f l)) (comap (fun x => g (f x)) l).
Proof.
  cofix rec.
  intros A B C R S f g l.
  destruct l.
  {
    pattern (comap g (comap f conil)).
    rewrite colist_unfold_eq; simpl.
    pattern (comap (fun x : A => g (f x)) conil).
    rewrite colist_unfold_eq; simpl.
    repeat constructor.
  }
  {
    pattern (comap g (comap f (cocons a l))).
    rewrite colist_unfold_eq; simpl.
    pattern (comap (fun x : A => g (f x)) (cocons a l)).
    rewrite colist_unfold_eq; simpl.
    constructor; auto.
  }
Qed.

CoInductive Forall_subcotrees {A : Type} (P : cotree A -> Prop) : cotree A -> Prop :=
| Forall_subcotrees_conode : forall a f, P (conode a f) -> CoForall (Forall_subcotrees P) f -> Forall_subcotrees P (conode a f).

Inductive Exists_subcotree {A : Type} (P : cotree A -> Prop) : cotree A -> Prop :=
| Exists_subcotree_here : forall a f, P (conode a f) -> Exists_subcotree P (conode a f)
| Exists_subcotree_there : forall a f, CoExists (Exists_subcotree P) f -> Exists_subcotree P (conode a f).

Add Parametric Relation
  (A : Type) :
  A (@eq A)
  reflexivity proved by (@eq_Reflexive A)
  symmetry proved by (@eq_Symmetric A)
  transitivity proved by (@eq_Transitive A) as eq_setoid.

Add Parametric Relation
  (A : Type) (R : relation A)
  (r : @Reflexive _ R) (s : @Symmetric _ R) (t : @Transitive _ R) :
  (colist A)
  (bisimilar_colist R)
  reflexivity proved by (@bisimilar_colist_Reflexive A R r)
  symmetry proved by (@bisimilar_colist_Symmetric A R s)
  transitivity proved by (@bisimilar_colist_Transitive A R t) as colist_setoid.

Add Parametric Relation
  (A : Type) (R : relation A)
  (r : @Reflexive _ R) (s : @Symmetric _ R) (t : @Transitive _ R) :
  (cotree A)
  (bisimilar_cotree R)
  reflexivity proved by (@bisimilar_cotree_Reflexive A R r)
  symmetry proved by (@bisimilar_cotree_Symmetric A R s)
  transitivity proved by (@bisimilar_cotree_Transitive A R t) as cotree_setoid.

Lemma CoExists_proj1 :
  forall {A : Type} (P Q : A -> Prop) (l : colist A),
    CoExists (fun a => P a /\ Q a) l -> CoExists P l.
Proof.
  intros A P Q l pf.
  induction pf; [left | right]; intuition.
Qed.

Lemma Forall_conodes_In_cotree :
  forall {A : Type} (P : A -> Prop) (t : cotree A),
    Forall_conodes P t <->
    (forall (x : A), In_cotree x t -> P x).
Proof.
  intros A P t; split.
  { intros fa x i.
    generalize fa i.
    refine (In_cotree_better_ind A x
              (fun t => Forall_conodes P t -> In_cotree x t -> P x)
              _ _ t i);
      clear fa i.
    { intros f fa i.
      inv fa.
      inv i; auto. }
    { intros a' f pf fa i.
      inv fa.
      inv i; auto.
      clear H1.
      { generalize H2 H0; clear H2 H0.
        induction pf.
        { intros pf1 pf2.
          inv pf1.
          inv pf2; intuition. }
        { intros pf1 pf2.
          inv pf1.
          inv pf2; intuition.
          eapply H.
          eapply CoExists_proj1.
          eapply pf. } } } }
  { generalize t; clear t.
    cofix C1.
    intros t pf.
    destruct t; constructor.
    eapply pf; eauto.
    left.
    generalize c pf; clear c pf.
    cofix C2.
    intros c pf.
    destruct c; constructor.
    eapply C1; eauto.
    intros x i.
    eapply pf; eauto.
    right; left; auto.
    eapply C2; eauto.
    intros x i.
    eapply pf; eauto.
    inv i.
    left.
    right; right; auto. }
Qed.

Fixpoint In_cotree_morph_aux
         {A : Type}
         (a : A)
         (t1 t2 : cotree A)
         (pf : bisimilar_cotree eq t1 t2)
         (i : In_cotree a t1) : In_cotree a t2.
Proof.
  destruct i.
  inv pf. left.
  inv pf.
  right.
  generalize f f2 H4 H; clear f f2 H4 H.
  refine (fix F (f1 : coforest A) (f2 : coforest A)
                (pf : bisimilar_colist (bisimilar_cotree eq) f1 f2)
                (i : CoExists (In_cotree a) f1) := _).
  destruct i.
  { inv pf.
    constructor.
    eapply In_cotree_morph_aux; eauto. }
  { inv pf.
    right.
    eapply F; eauto. }
Qed.

Add Parametric Morphism (A : Type) : (@In_cotree A)
  with signature (@eq A) ==> (@bisimilar_cotree A eq) ==> iff as In_cotree_morph.
Proof.
  intros a t1 t2 pf; split; intros i;
  eapply In_cotree_morph_aux; eauto.
  symmetry; auto.
Qed.

Add Parametric Morphism (A : Type) (P : A -> Prop) : (@Forall_conodes A P)
  with signature (@bisimilar_cotree A eq) ==> iff as Forall_conodes_morph.
Proof.
  intros t1 t2 pf.
  split.
  { generalize t1 t2 pf; clear t1 t2 pf.
    cofix C1.
    intros t1 t2 pf a.
    inv pf.
    auto.
    inv a.
    constructor; auto.
    clear a2 H2.
    generalize f1 f2 H0 H3; clear f1 f2 H0 H3.
    cofix C2.
    intros f1 f2 H1 H3.
    inv H1.
    constructor.
    inv H3.
    constructor; auto.
    eapply C1; eauto.
    eapply C2; eauto. }
  { generalize t1 t2 pf; clear t1 t2 pf.
    cofix C1.
    intros t1 t2 pf a.
    inv pf.
    auto.
    inv a.
    constructor; auto.
    clear a2 H2.
    generalize f1 f2 H0 H3; clear f1 f2 H0 H3.
    cofix C2.
    intros f1 f2 H1 H3.
    inv H1.
    constructor.
    inv H3.
    constructor; auto.
    eapply C1; eauto.
    eapply C2; eauto. }
Qed.

Add Parametric Morphism
  (A : Type)
  (R : relation A) (E : Equivalence R)
  (P : A -> Prop) (PR : Proper (R ==> iff) P)
  : (@CoForall A P)
  with signature (@bisimilar_colist A R) ==> iff as CoForall_morph.
Proof.
  destruct E as [r s t].
  intros l1 l2 pf.
  split.
  { generalize l1 l2 pf; clear l1 l2 pf.
    cofix C1.
    intros l1 l2 pf a.
    inv pf.
    auto.
    inv a.
    constructor.
    unfold "==>", Proper in PR.
    specialize (PR a1 a2).
    intuition.
    eapply C1; eauto. }
  { generalize l1 l2 pf; clear l1 l2 pf.
    cofix C1.
    intros l1 l2 pf a.
    inv pf.
    auto.
    inv a.
    constructor.
    unfold "==>", Proper in PR.
    specialize (PR a1 a2).
    intuition.
    eapply C1; eauto. }
Qed.

Lemma In_coforest_CoForall_Forall_conodes :
  forall {A : Type} (P : A -> Prop) (f : coforest A),
    (forall (x : A), CoExists (In_cotree x) f -> P x) ->
    CoForall (Forall_conodes P) f.
Proof.
  intros A P.
  cofix C2.
  intros c pf.
  destruct c.
  constructor.
  constructor.
  rewrite Forall_conodes_In_cotree.
  intros x i.
  eapply pf; eauto.
  left; auto.
  eapply C2; eauto.
  intros x i.
  eapply pf; eauto.
  right; auto.
Qed.


Lemma CoForall_mp :
  forall {A : Type} (P Q : A -> Prop) (l : colist A),
    CoForall (fun a => P a -> Q a) l ->
    CoForall (fun a => P a) l ->
    CoForall (fun a => Q a) l.
Proof.
  intros A P Q.
  cofix C.
  intros l pf1 pf2.
  destruct l.
  constructor.
  inv pf1.
  inv pf2.
  constructor; auto.
Qed.

Lemma CoForall_and :
  forall {A : Type} (P Q : A -> Prop) (l : colist A),
    CoForall (fun a => P a) l ->
    CoForall (fun a => Q a) l ->
    CoForall (fun a => P a /\ Q a) l.
Proof.
  intros A P Q.
  cofix C.
  intros l pf1 pf2.
  destruct l.
  constructor.
  inv pf1.
  inv pf2.
  constructor; auto.
Qed.

Lemma CoForall_and_inv1 :
  forall {A : Type} (P Q : A -> Prop) (l : colist A),
    CoForall (fun a => P a /\ Q a) l ->
    CoForall (fun a => P a) l.
Proof.
  intros A P Q.
  cofix C.
  intros l pf.
  destruct l.
  constructor.
  inv pf.
  constructor; intuition.
Qed.

Lemma CoForall_and_inv2 :
  forall {A : Type} (P Q : A -> Prop) (l : colist A),
    CoForall (fun a => P a /\ Q a) l ->
    CoForall (fun a => Q a) l.
Proof.
  intros A P Q.
  cofix C.
  intros l pf.
  destruct l.
  constructor.
  inv pf.
  constructor; intuition.
Qed.

Lemma CoForall_impl :
  forall {A : Type} (P Q : A -> Prop),
    (forall a, P a -> Q a) ->
  forall (l : colist A),
    CoForall (fun a => P a) l ->
    CoForall (fun a => Q a) l.
Proof.
  intros A P Q.
  cofix C.
  intros pf1 l pf2.
  destruct l.
  constructor.
  inv pf2.
  constructor; auto.
Qed.

Lemma CoForall_impl_In :
  forall {A : Type} (P Q : A -> Prop) (l : colist A),
    (forall a, In_colist a l -> P a -> Q a) ->
    CoForall (fun a => P a) l ->
    CoForall (fun a => Q a) l.
Proof.
  intros A P Q.
  cofix C.
  intros l pf1 pf2.
  destruct l eqn:eq.
  constructor.
  assert (i : In_colist a l).
  { rewrite eq. constructor. }
  inv pf2.
  constructor.
  eapply pf1; eauto.
  eapply C; eauto.
  clear i H1 H2.
  intros a0 i p.
  eapply pf1; eauto.
  eright; eauto.
Qed.

Lemma Forall_conodes_impl :
  forall {A : Type} (P Q : A -> Prop),
    (forall a, P a -> Q a) ->
  forall (t : cotree A),
    Forall_conodes (fun a => P a) t ->
    Forall_conodes (fun a => Q a) t.
Proof.
  intros A P Q pf1.
  cofix C1.
  intros t pf2.
  destruct t.
  constructor.
  inv pf2; auto.
  inv pf2; auto.
  generalize c H2; clear c H2.
  cofix C2.
  intros c H2.
  destruct c.
  constructor.
  inv H2.
  constructor; auto.
Qed.

Definition finite_game {A : Type} (next : A -> list A) (initial : A) : Type :=
  finite_cotree (unfold_cotree next initial).

Definition path
           {A : Type}
           (next : forall (a : A), list A) : A -> A -> Prop :=
  clos_refl_trans A (fun (x y : A) => In y (next x)).

Definition path_n1
           {A : Type}
           (next : forall (a : A), list A) : A -> A -> Prop :=
  @clos_refl_trans_n1 A (fun (x y : A) => In y (next x)).

Definition path_1n
           {A : Type}
           (next : forall (a : A), list A) : A -> A -> Prop :=
  @clos_refl_trans_1n A (fun (x y : A) => In y (next x)).

Lemma unfold_cotree_unwrap :
  forall
    {A : Type}
    (next : forall (a : A), list A)
    (init : A),
    bisimilar_cotree eq
      (unfold_cotree next init)
      (conode init (comap (unfold_cotree next) (colist_of_list (next init)))).
Proof.
  intros A next init.
  pattern (unfold_cotree next init) at 1.
  rewrite cotree_unfold_eq; simpl.
  reflexivity.
Qed.

Lemma unfold_cotree_sound_aux :
  forall
    {A : Type}
    (next : A -> list A),
  forall (init mid : A),
    path next init mid ->
    Forall_conodes (path next init) (unfold_cotree next mid).
Proof.
  intros A next.
  cofix C1.
  intros init mid pf.
  pattern (unfold_cotree next mid).
  rewrite cotree_unfold_eq; simpl.
  constructor.
  auto.
  destruct (next mid) eqn:eq.
  { pattern (comap (unfold_cotree next) (colist_of_list [])).
    rewrite colist_unfold_eq; simpl.
    constructor.
  }
  { pattern (comap (unfold_cotree next) (colist_of_list (a :: l))).
    rewrite colist_unfold_eq; simpl.
    constructor.
    eapply C1.
    eapply rt_trans; [eapply pf | eapply rt_step; rewrite eq; eleft; auto].
    assert (H : incl l (next mid)).
    { rewrite eq. eapply incl_tl; eapply incl_refl. }
    clear eq.
    generalize l H; clear l H.
    cofix C2.
    intros l pf'.
    destruct l.
    { rewrite colist_unfold_eq; simpl.
      constructor.
    }
    { rewrite colist_unfold_eq; simpl.
      constructor.
      eapply C1.
      eapply rt_trans; [eapply pf | eapply rt_step].
      destruct (incl_cons_inv pf'); eauto.
      eapply C2.
      destruct (incl_cons_inv pf'); eauto.
    }
  }
Qed.

Theorem unfold_cotree_sound :
  forall
    {A : Type}
    (next : forall (a : A), list A)
    (init : A),
  forall (a : A),
    In_cotree a (unfold_cotree next init) ->
    path next init a.
Proof.
  intros A next init.
  rewrite <- Forall_conodes_In_cotree.
  eapply (unfold_cotree_sound_aux next init init).
  eapply rt_refl.
Qed.

Theorem unfold_cotree_complete_1n :
  forall
    {A : Type}
    (next : forall (a : A), list A)
    (init : A),
  forall (a : A),
    path_1n next init a ->
    In_cotree a (unfold_cotree next init).
Proof.
  intros A next init a ch.
  rewrite unfold_cotree_unwrap.
  dependent induction ch.
  constructor.
  constructor.
  rewrite CoExists_exists.
  eexists (unfold_cotree next _).
  split.
  { eapply in_comap.
    rewrite <- In_colist_iff_In_colist_of_list; eauto. }
  { rewrite <- unfold_cotree_unwrap in *; eauto. }
Qed.

Theorem unfold_cotree_complete :
  forall
    {A : Type}
    (next : forall (a : A), list A)
    (init : A),
  forall (a : A),
    path next init a ->
    In_cotree a (unfold_cotree next init).
Proof.
  intros A next init a.
  pose proof (unfold_cotree_complete_1n next init a).
  unfold path, path_1n in *.
  rewrite <- clos_rt_rt1n_iff in *; auto.
Qed.
