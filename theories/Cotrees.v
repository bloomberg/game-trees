(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

Require Import Corelib.Classes.Morphisms.
Require Import Corelib.Classes.RelationClasses.
Require Import Corelib.Relations.Relation_Definitions.
From Stdlib Require Import List.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Relations.Operators_Properties.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Lia.

Require Import GameTrees.Helpers.
Require Import GameTrees.Trees.

Import ListNotations.

(* Coinductive counterpart of [list]. *)
CoInductive colist (A : Type) : Type :=
| conil : colist A
| cocons : A -> colist A -> colist A.

Arguments conil {A}.
Arguments cocons {A} x xs.

(* Coinductive counterpart of [tree]. *)
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

(* The [colist] counterpart of the [map] function. *)
Definition comap {A B : Type} (f : A -> B) : colist A -> colist B :=
  cofix comap (l : colist A) : colist B :=
    match l with
    | conil => conil
    | cocons x xs => cocons (f x) (comap xs)
    end.

(* The [cotree] counterpart of the [map_tree] function. *)
CoFixpoint comap_cotree {A B : Type} (g : A -> B) (t : cotree A) : cotree B :=
  match t with
  | conode a f => conode (g a) (comap (comap_cotree g) f)
  end.

Definition singleton_cotree {A : Type} (a : A) : cotree A := conode a conil.
Definition singleton_coforest {A : Type} (a : A) : coforest A := cocons (conode a conil) conil.

(* Turn a [list] into a [colist]. *)
CoFixpoint colist_of_list {A : Type} (l : list A) : colist A :=
  match l with
  | [] => conil
  | x :: xs => cocons x (colist_of_list xs)
  end.

Definition coforest_of_list {A : Type} (l : list A) : coforest A :=
  comap singleton_cotree (colist_of_list l).

(* Take elements from [colist] and put in a [list], as long as there is some fuel. *)
Fixpoint list_of_colist {A : Type} (fuel : nat) (l : colist A) {struct fuel} : list A :=
  match fuel with
  | O => nil
  | S fuel' =>
    match l with
    | conil => nil
    | cocons x xs => cons x (list_of_colist fuel' xs)
    end
  end.

(* Take elements from [cotree] and put in a [tree], as long as there is some fuel. *)
Fixpoint tree_of_cotree {A : Type} (fuel : nat) (t : cotree A) {struct fuel} : tree A :=
  match t with
  | conode a f =>
    match fuel with
    | O => node a []
    | S fuel' =>
        node a (map (tree_of_cotree fuel') (list_of_colist fuel f))
    end
  end.

(* Given an initial game state and the (possibly infinite) "next states" function,
   build the entire (possibly infinite) game tree.
   The [cotree] counterpart of the [unfold_tree] function. *)
CoFixpoint unfold_cotree {A : Type} (next : A -> colist A) (init : A) : cotree A :=
  conode init (comap (unfold_cotree next) (next init)).

(* The [colist] counterpart of the [In] predicate. *)
Inductive In_colist {A : Type} (x : A) : colist A -> Prop :=
| In_cocons_hd : forall xs, In_colist x (cocons x xs)
| In_cocons_tl : forall y xs, In_colist x xs -> In_colist x (cocons y xs).

(* The [colist] counterpart of the [Exists] predicate. *)
Inductive CoExists {A : Type} (P : A -> Prop) : colist A -> Prop :=
| CoExists_cocons_hd : forall x l, P x -> CoExists P (cocons x l)
| CoExists_cocons_tl : forall x l, CoExists P l -> CoExists P (cocons x l).

(* The [cotree] counterpart of the [In_tree] predicate. *)
Inductive In_cotree {A : Type} (a : A) : cotree A -> Prop :=
| In_conode : forall f, In_cotree a (conode a f)
| In_cochildren : forall a' f,
    CoExists (In_cotree a) f -> In_cotree a (conode a' f).

(* The [colist] counterpart of the [Forall] predicate. *)
CoInductive CoForall {A : Type} (P : A -> Prop) : colist A -> Prop :=
| CoForall_conil : CoForall P conil
| CoForall_cocons : forall x l, P x -> CoForall P l -> CoForall P (cocons x l).

(* The [cotree] counterpart of the [Forall_nodes] predicate. *)
CoInductive Forall_conodes {A : Type} (P : A -> Prop) : cotree A -> Prop :=
| Forall_conodes_conode : forall a f, P a -> CoForall (Forall_conodes P) f -> Forall_conodes P (conode a f).

(* The [colist] counterpart of the [incl] relation. *)
Definition coincl {A : Type} (l1 l2 : colist A) : Prop :=
  forall (a : A), In_colist a l1 -> In_colist a l2.

Lemma coincl_refl :
  forall {A : Type} (l : colist A), coincl l l.
Proof. intros A l a pf; auto. Qed.

Lemma coincl_tl :
  forall {A : Type} (a : A) (l1 l2 : colist A), coincl l1 l2 -> coincl l1 (cocons a l2).
Proof.
  intros A a l1 l2 pf a' pf'.
  constructor; auto.
Qed.

Lemma coincl_cons_inv :
  forall {A : Type} (a : A) (l1 l2 : colist A),
    coincl (cocons a l1) l2 -> In_colist a l2 /\ coincl l1 l2.
Proof.
  intros A a l1 l2 pf.
  split; [| intros a' pf']; apply pf; constructor; auto.
Qed.

(* The [colist] counterpart of [Exists_exists]. *)
Lemma CoExists_exists :
  forall {A : Type} (P : A -> Prop) (l : colist A),
    CoExists P l <-> (exists x : A, In_colist x l /\ P x).
Proof.
  intros A P l; split.
  { intros pf.
    induction pf.
    repeat econstructor; eauto.
    destruct IHpf as [a [H1 H2]].
    exists a.
    split; auto.
    right; auto. }
  { intros pf.
    destruct pf as [x [H1 H2]].
    induction H1.
    left; auto.
    right; auto. }
Qed.

(* A better induction principle for [In_cotree],
   since [In_cotree_ind] does not specify that
   [P] holds for the elements in the subtrees. *)
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

(* The [colist] counterpart of [Forall_forall]. *)
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

(* A bisimilarity relation on [colist]s, where the elements are related by [R]. *)
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

(* A bisimilarity relation on [cotree]s, where the elements are related by [R]. *)
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

(* Chlipala's [frob] for [colist]s.
   For the original [frob], see http://adam.chlipala.net/cpdt/html/Cpdt.Coinductive.html
   An identity function that pattern matches on the [colist] and reconstructs the original.
   It induces a reduction context that allows guardedness checks to succeed. *)
Definition colist_unfold {A : Type} (l : colist A) : colist A :=
  match l with conil => conil | cocons x xs => cocons x xs end.

(* Proof that [colist_unfold] indeed acts like the identity function. *)
Lemma colist_unfold_eq : forall {A : Type} (l : colist A), l = colist_unfold l.
Proof. destruct l; auto. Qed.

(* Chlipala's [frob] for [cotree]s.
   An identity function that pattern matches on the [cotree] and reconstructs the original.
   It induces a reduction context that allows guardedness checks to succeed. *)
Definition cotree_unfold {A : Type} (t : cotree A) : cotree A :=
  match t with conode a f => conode a f end.

(* Proof that [colist_unfold] indeed acts like the identity function. *)
Lemma cotree_unfold_eq : forall {A : Type} (t : cotree A), t = cotree_unfold t.
Proof. destruct t; auto. Qed.

(* The [colist] counterpart of [Forall_map]. *)
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

(* Any [In] proof about a list is equivalent to
   the [In_colist] proof about the [colist] version of the same list. *)
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

(* Any [Forall] proof about a list is equivalent to
   the [CoForall] proof about the [colist] version of the same list. *)
Lemma Forall_iff_CoForall_colist_of_list :
  forall {A : Type} (P : A -> Prop) (l : list A),
    Forall P l <-> CoForall P (colist_of_list l).
Proof.
  intros A P l.
  rewrite CoForall_forall.
  rewrite Forall_forall.
  split; intros x pf pf'.
  rewrite <- In_colist_iff_In_colist_of_list in pf'; auto.
  rewrite -> In_colist_iff_In_colist_of_list in pf'; auto.
Qed.

(* The [colist] counterpart of [in_map]. *)
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

(* The [colist] counterpart of [map_map]. *)
Lemma comap_comap :
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

(* If there is an element in a [colist] satisfying properties [P] and [Q],
   there is an element in that [colist] satisfying [P] and
   there is an element in that [colist] satisfying [Q]. *)
Lemma CoExists_proj :
  forall {A : Type} (P Q : A -> Prop) (l : colist A),
    CoExists (fun a => P a /\ Q a) l -> CoExists P l /\ CoExists Q l.
Proof.
  intros A P Q l pf.
  induction pf.
  split; left; intuition.
  split; right; intuition.
Qed.

(* The [cotree] counterpart of [Forall_nodes_In_tree]. *)
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
          eapply proj1, CoExists_proj.
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

(* If two [cotree]s are bisimilar where the elements are related by [eq],
   then any element [In_cotree] of one is [In_cotree] of the other. *)
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

(* If every element [x] that appears somewhere in the [coforest] satisfies [P],
   then the whole [coforest] satisfies the property that all its conodes satisfy [P]. *)
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

(* The [colist] counterpart of [Forall_mp]. *)
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

(* The [colist] counterpart of [Forall_and]. *)
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

(* The [colist] counterpart of [Forall_and_inv]. *)
Lemma CoForall_and_inv :
  forall {A : Type} (P Q : A -> Prop) (l : colist A),
    CoForall (fun a => P a /\ Q a) l ->
    CoForall (fun a => P a) l /\ CoForall (fun a => P a) l.
Proof.
  intros A P Q.
  split; revert l H; cofix C;
  intros l pf;
  destruct l;
  constructor;
  inv pf; intuition.
Qed.

(* The [colist] counterpart of [Forall_impl]. *)
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

(* If whenever an element [a] is in the colist, [P a] implies [Q a],
   then any [colist] that satisfies [P] everywhere also satisfies [Q] everywhere. *)
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

(* If [P a] always implies [Q a],
   then any [cotree] whose nodes all satisfy [P] also has all nodes satisfying [Q]. *)
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

(* There is a sequence of steps from x to y in zero or more steps,
   where a one-step edge is "y appears in [next] x". *)
Definition reachable
           {A : Type}
           (next : forall (a : A), colist A) : A -> A -> Prop :=
  clos_refl_trans A (fun (x y : A) => In_colist y (next x)).

(* Same as [reachable], but the transitive closure is right-stepping. *)
Definition reachable_n1
           {A : Type}
           (next : forall (a : A), colist A) : A -> A -> Prop :=
  @clos_refl_trans_n1 A (fun (x y : A) => In_colist y (next x)).

(* Same as [reachable], but the transitive closure is left-stepping. *)
Definition reachable_1n
           {A : Type}
           (next : forall (a : A), colist A) : A -> A -> Prop :=
  @clos_refl_trans_1n A (fun (x y : A) => In_colist y (next x)).

(* An explicit unfolding of a call to [unfold_cotree] is bisimilar to the original. *)
Lemma unfold_cotree_unwrap :
  forall
    {A : Type}
    (next : forall (a : A), colist A)
    (init : A),
    bisimilar_cotree eq
      (unfold_cotree next init)
      (conode init (comap (unfold_cotree next) (next init))).
Proof.
  intros A next init.
  pattern (unfold_cotree next init) at 1.
  rewrite cotree_unfold_eq; simpl.
  reflexivity.
Qed.

(* If [mid] is [reachable] from [init],
   then every node produced by [unfold_cotree next mid] is [reachable] from [mid]. *)
Lemma unfold_cotree_sound_aux :
  forall
    {A : Type}
    (next : A -> colist A),
  forall (init mid : A),
    reachable next init mid ->
    Forall_conodes (reachable next init) (unfold_cotree next mid).
Proof.
  intros A next.
  cofix C1.
  intros init mid pf.
  pattern (unfold_cotree next mid).
  rewrite cotree_unfold_eq; simpl.
  constructor.
  auto.
  destruct (next mid) eqn:eq.
  { pattern (comap (unfold_cotree next) conil).
    rewrite colist_unfold_eq; simpl.
    constructor.
  }
  { pattern (comap (unfold_cotree next) (cocons a c)).
    rewrite colist_unfold_eq; simpl.
    constructor.
    eapply C1.
    eapply rt_trans; [eapply pf | eapply rt_step; rewrite eq; eleft; auto].
    assert (H : coincl c (next mid)).
    { rewrite eq. eapply coincl_tl; eapply coincl_refl. }
    clear eq.
    generalize c H; clear c H.
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
      destruct (coincl_cons_inv _ _ _ pf'); eauto.
      eapply C2.
      destruct (coincl_cons_inv _ _ _ pf'); eauto.
    }
  }
Qed.

(* If a state is the unfolded game tree,
   then that state must be [reachable] in a game from the initial state. *)
Theorem unfold_cotree_sound :
  forall
    {A : Type}
    (next : forall (a : A), colist A)
    (init : A),
  forall (a : A),
    In_cotree a (unfold_cotree next init) ->
    reachable next init a.
Proof.
  intros A next init.
  rewrite <- Forall_conodes_In_cotree.
  eapply (unfold_cotree_sound_aux next init init).
  eapply rt_refl.
Qed.

(* Any game state left-steppingly reachable from the initial state
   must be in the unfolded game tree. *)
Theorem unfold_cotree_complete_1n :
  forall
    {A : Type}
    (next : forall (a : A), colist A)
    (init : A),
  forall (a : A),
    reachable_1n next init a ->
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
    eauto. }
  { rewrite <- unfold_cotree_unwrap in *; eauto. }
Qed.

(* Any game state [reachable] from the initial state
   must be in the unfolded game tree. *)
Theorem unfold_cotree_complete :
  forall
    {A : Type}
    (next : forall (a : A), colist A)
    (init : A),
  forall (a : A),
    reachable next init a ->
    In_cotree a (unfold_cotree next init).
Proof.
  intros A next init a.
  pose proof (unfold_cotree_complete_1n next init a).
  unfold reachable, reachable_1n in *.
  rewrite <- clos_rt_rt1n_iff in *; auto.
Qed.

(* A [colist] is finite if there is a number [n] at which
   taking [n] or [1+n] elements from the [colist] results in the same [list]. *)
Definition finite_colist {A : Type} (cl : colist A) : Type :=
  { n : nat | list_of_colist n cl = list_of_colist (1 + n) cl }.

(* A [cotree] is finite if there is a number [n] at which
   taking [n] or [1+n] elements from the [cotree] results in the same [tree]. *)
Definition finite_cotree {A : Type} (ct : cotree A) : Type :=
  { n : nat | tree_of_cotree n ct = tree_of_cotree (1 + n) ct }.

(* A finite game is one whose unfolded game tree is finite. *)
Definition finite_game {A : Type} (next : A -> colist A) (initial : A) : Type :=
  finite_cotree (unfold_cotree next initial).

(* A function to extract the saturated [list] from the [colist] finiteness proof. *)
Definition finite_colist_means_list :
  forall {A : Type} (cl : colist A),
    finite_colist cl ->
    { l : list A | exists (n : nat), list_of_colist n cl = l }.
Proof.
  intros A cl [n eq].
  exists (list_of_colist n cl).
  exists n; auto.
Defined.

(* A function to extract the saturated [tree] from the [cotree] finiteness proof. *)
Definition finite_cotree_means_tree :
  forall {A : Type} (ct : cotree A),
    finite_cotree ct ->
    { t : tree A | exists (n : nat), tree_of_cotree n ct = t }.
Proof.
  intros A ct [n eq].
  exists (tree_of_cotree n ct).
  exists n; auto.
Defined.

(* We define finiteness of [colist]s by saturation of
   [list_of_colist] at a particular [fuel] argument.
   Here we make sure that this is indeed saturation,
   and adding even more [fuel] does not bring more elements. *)
Theorem finite_colist_stable :
  forall {A : Type} (cl : colist A) (n m : nat),
    list_of_colist n cl = list_of_colist (1 + n) cl ->
    list_of_colist n cl = list_of_colist (m + n) cl.
Proof.
  intros A cl n m H.
  revert cl m H.
  induction n as [| n IH]; intros cl m H.
  - simpl in H.
    destruct cl, m; simpl in *; auto.
    discriminate.
  - destruct cl; simpl in *.
    + rewrite PeanoNat.Nat.add_succ_r; auto.
    + inv H.
      rewrite PeanoNat.Nat.add_succ_r; simpl.
      f_equal.
      eapply IH; eauto.
Qed.

(* Equality of maps over the same list gives pointwise equality. *)
Lemma map_eq_Forall_pointwise {A B : Type} (f g : A -> B) (l : list A) :
  map f l = map g l -> Forall (fun x => f x = g x) l.
Proof.
  revert f g.
  induction l as [|x xs IH]; intros f g H; simpl in H; auto.
  inv H; auto.
Qed.

(* If the (S n)-prefix doesn't increase length, it equals the n-prefix. *)
Lemma list_of_colist_succ_eq_if_same_len
      {A : Type} (f : colist A) (n : nat) :
  length (list_of_colist (S n) f) = length (list_of_colist n f) ->
  list_of_colist (S n) f = list_of_colist n f.
Proof.
  revert f.
  induction n as [|n IH]; intros f Hlen.
  - destruct f; simpl in *; [auto | discriminate].
  - destruct f; simpl in *; auto.
    apply PeanoNat.Nat.succ_inj in Hlen.
    specialize (IH f Hlen).
    f_equal; auto.
Qed.

(* We define finiteness of [cotree]s by saturation of
   [tree_of_cotree] at a particular [fuel] argument.
   Here we make sure that this is indeed saturation,
   and adding even more [fuel] does not bring more elements. *)
Theorem finite_cotree_stable :
  forall {A : Type} (ct : cotree A) (n m : nat),
    tree_of_cotree n ct = tree_of_cotree (1 + n) ct ->
    tree_of_cotree n ct = tree_of_cotree (m + n) ct.
Proof.
  intros A ct n.
  revert ct.
  induction n as [| n IH]; intros [a f] m H; simpl in *.
  - destruct f; simpl in *.
    + destruct m; auto.
    + discriminate.
  - destruct f as [| ch rest]; simpl in *.
    + rewrite PeanoNat.Nat.add_succ_r; auto.
    + inv H. rename H1 into Hhd, H2 into Htl.

      (* Show the (S n)-prefix of 'rest' didn't actually grow *)
      assert (Hlen :
        length (list_of_colist (S n) rest) = length (list_of_colist n rest)).
      { apply (f_equal (@length _)) in Htl. now rewrite !length_map in Htl. }

      assert (Hrest_eq :
        list_of_colist (S n) rest = list_of_colist n rest).
      { eapply list_of_colist_succ_eq_if_same_len; eauto. }

      (* rewrite inside Htl to use [list_of_colist (S n) rest] so [Hrest_eq] applies *)
      change (match rest with
              | conil => []
              | cocons x xs => x :: list_of_colist n xs
              end)
        with (list_of_colist (S n) rest) in Htl.

      (* now both sides of Htl are maps over [list_of_colist n rest] vs [list_of_colist (S n) rest] *)
      rewrite Hrest_eq in Htl.
      (* obtain pointwise stabilization for each child in the n-prefix of [rest] *)
      pose proof (Hfor := map_eq_Forall_pointwise
                            (tree_of_cotree n) (tree_of_cotree (S n))
                            (list_of_colist n rest) Htl).

      (* head child stabilizes up to any larger fuel by IH *)
      assert (Hhd_m : tree_of_cotree n ch = tree_of_cotree (m + n) ch)
        by (apply IH; auto).

      (* the list of children itself stabilizes for all larger prefixes *)
      assert (Hrest_stable :
        list_of_colist n rest = list_of_colist (m + n) rest).
      { apply finite_colist_stable; auto. }

      (* convert pointwise stabilization into a map equality on the fixed list *)
      set (L := list_of_colist n rest) in *.
      assert (Hmap_tail : map (tree_of_cotree n) L = map (tree_of_cotree (m + n)) L).
      { clear -IH Hfor.
        revert Hfor; induction L as [|x xs IHxs]; intros HF; simpl; auto.
        inv HF; subst; simpl. f_equal; auto. }

      rewrite PeanoNat.Nat.add_succ_r; simpl.
      f_equal.
      f_equal; auto.
      rewrite <- Hrest_stable; auto.
Qed.
