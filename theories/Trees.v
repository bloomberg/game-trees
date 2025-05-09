(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

Require Import Corelib.Program.Wf.
Require Import Corelib.Relations.Relation_Definitions.
From Stdlib Require Import List.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Relations.Operators_Properties.
From Stdlib Require Import Program.Equality.

Require Import GameTrees.Helpers.
Require Import GameTrees.Relations.

Import ListNotations.

Inductive tree (A : Type) : Type :=
| node : A -> list (tree A) -> tree A.

Arguments node {A} a f.

Definition root {A : Type} (t : tree A) : A :=
  match t with
  | node a _ => a
  end.

Definition children {A : Type} (t : tree A) : list (tree A) :=
  match t with
  | node _ f => f
  end.

Definition forest (A : Type) : Type := list (tree A).

Fixpoint size_tree {A : Type} (t : tree A) : nat :=
  match t with
  | node a f => 1 + list_sum (map size_tree f)
  end.

(* Returns the elements of a tree in pre-order. *)
Fixpoint flatten_tree {A : Type} (t : tree A) : list A :=
  match t with
  | node a f => a :: concat (map flatten_tree f)
  end.

Definition flatten_forest {A : Type} (f : forest A) : list A :=
  concat (map flatten_tree f).

Fixpoint map_tree {A B : Type} (g : A -> B) (t : tree A) : tree B :=
  match t with
  | node a f => node (g a) (map (map_tree g) f)
  end.

Definition map_forest {A B : Type} (g : A -> B) (f : forest A) : forest B :=
  map (map_tree g) f.

Definition singleton_tree {A : Type} (a : A) : tree A := node a [].
Definition singleton_forest {A : Type} (a : A) : forest A := (node a []) :: [].

Definition forest_of_list {A : Type} (l : list A) : forest A :=
  map singleton_tree l.

(* Take the [height]-many levels from the tree *)
Fixpoint take_tree {A : Type} (height : nat) (t : tree A) : tree A :=
  match t with
  | node a f =>
    match height with
    | O => node a []
    | S height' =>
      node a (map (take_tree height') f)
    end
  end.

Fixpoint fold_tree {A B : Type} (g : A -> list B -> B) (t : tree A) : B :=
  match t with
  | node a f => g a (map (fold_tree g) f)
  end.

Fixpoint leaves {A : Type} (t : tree A) : list A :=
  match t with
  | node a [] => [a]
  | node _ f => concat (map leaves f)
  end.

Inductive monotonic_tree {A : Type} (R : relation A)
        : forall (bound : option A), tree A -> Prop :=
| monotonic_node_unbounded :
    forall a f,
      Forall (monotonic_tree R (Some a)) f ->
      monotonic_tree R None (node a f)
| monotonic_node_bounded :
    forall b a f,
      R a b ->
      Forall (monotonic_tree R (Some a)) f ->
      monotonic_tree R (Some b) (node a f).

Definition monotonic_forest
          {A : Type} (R : relation A)
          (bound : option A) (f : forest A) : Prop :=
  Forall (monotonic_tree R bound) f.

Fixpoint tree_forall_ind
    (A : Type) (P : tree A -> Prop)
    (tpf : forall (a : A) (f : forest A), Forall P f -> P (node a f))
    (t : tree A) {struct t} : P t :=
  match t with
  | node a f =>
      tpf a f
        (list_ind (Forall P) (Forall_nil P)
           (fun x xs IHxs => Forall_cons x (tree_forall_ind A P tpf x) IHxs) f)
  end.

Lemma map_tree_monotonic :
  forall {A B : Type}
         {R1 : relation A} {R2 : B -> B -> Prop}
         (bound : option A)
         (g : A -> B)
         (op : monotone R1 R2 g)
         (t : tree A),
         @monotonic_tree A R1 bound t ->
         @monotonic_tree B R2 (option_map g bound) (map_tree g t).
Proof.
  intros A B R1 R2 bound g op t.
  generalize bound; clear bound.
  refine (tree_forall_ind A
            (fun (t : tree A) =>
               forall (bound : option A),
                 monotonic_tree R1 bound t ->
                 monotonic_tree R2 (option_map g bound) (map_tree g t)) _ t).
  intros a f pfs bound pf; simpl.
  inv pf; simpl.
  { constructor; auto.
    dependent induction f.
    constructor.
    inv H1.
    inv pfs.
    constructor.
    eapply (H1 (Some a)); eauto.
    eapply IHf; eauto. }
  { constructor; auto.
    dependent induction f.
    constructor.
    inv H3.
    inv pfs.
    simpl; constructor.
    eapply (H3 (Some a)); eauto.
    eapply IHf; eauto. }
Qed.

Lemma forest_of_list_monotonic_unbounded :
  forall
    {A : Type} (R : relation A)
    (l : list A),
    @monotonic_forest A R None (forest_of_list l).
Proof.
  intros A lt l.
  unfold monotonic_forest, forest_of_list.
  rewrite Forall_map.
  rewrite Forall_forall.
  intros x i.
  unfold singleton_tree.
  repeat constructor.
Qed.

Lemma forest_of_list_monotonic_bounded :
  forall
    {A : Type} (R : relation A)
    (bound : A)
    (l : list A),
    Forall (fun x => R x bound) l ->
    @monotonic_forest A R (Some bound) (forest_of_list l).
Proof.
  intros A R bound l pf.
  unfold monotonic_forest, forest_of_list.
  rewrite Forall_map.
  dependent induction l; inv pf; constructor; auto.
  unfold singleton_tree.
  repeat (constructor; auto).
Qed.

Inductive Forall_nodes {A : Type} (P : A -> Prop) : tree A -> Prop :=
| Forall_nodes_node : forall a f, P a -> Forall (Forall_nodes P) f -> Forall_nodes P (node a f).

Lemma Forall_flatten_tree :
  forall {A : Type}
         (P : A -> Prop)
         (t : tree A),
         Forall_nodes P t <->
         Forall P (flatten_tree t).
Proof.
  intros A P t.
  split.
  { eapply (tree_forall_ind _ (fun t => Forall_nodes P t -> Forall P (flatten_tree t)));
      simpl in *; intros.
    inversion H0; subst; auto.
    eapply Forall_cons; eauto.
    eapply Forall_concat.
    eapply Forall_map.
    eapply Forall_mp; eauto.
  }
  { eapply (tree_forall_ind _ (fun t => Forall P (flatten_tree t) -> Forall_nodes P t));
      simpl in *; intros.
    inversion H0; subst; auto.
    constructor; auto.
    rewrite Forall_concat in *.
    rewrite Forall_map in *.
    eapply Forall_mp; [apply H | apply H4].
  }
Qed.

Lemma Forall_map_tree :
  forall {A B : Type}
         (P : B -> Prop)
         (f : A -> B)
         (t : tree A),
         Forall_nodes P (map_tree f t) <->
         Forall_nodes (fun x => P (f x)) t.
Proof.
  intros A B P f t.
  split.
  { eapply (tree_forall_ind _ (fun t => Forall_nodes _ (map_tree f t) -> Forall_nodes _ t));
      simpl in *; intros.
    inversion H0; subst.
    constructor; auto.
    rewrite Forall_map in *.
    eapply Forall_mp; [apply H | apply H4].
  }
  { eapply (tree_forall_ind _ (fun t => Forall_nodes _ t -> Forall_nodes _ (map_tree f t)));
      simpl in *; intros.
    inversion H0; subst.
    constructor; auto.
    rewrite Forall_map in *.
    eapply Forall_mp; [apply H | apply H4].
  }
Qed.

Lemma Forall_forest_of_list :
  forall {A : Type}
         (P : A -> Prop)
         (xs : list A),
         Forall P xs <->
         Forall (Forall_nodes P) (forest_of_list xs).
Proof.
  intros A P xs.
  induction xs.
  simpl.
  repeat constructor.
  repeat (constructor; auto).
  all: simpl in *; inversion H; subst; simpl in *; intuition.
  unfold singleton_tree in *.
  inversion H2; subst; auto.
Qed.

Inductive In_tree {A : Type} (a : A) : tree A -> Prop :=
| In_this : forall f, In_tree a (node a f)
| In_that : forall a' f, Exists (In_tree a) f -> In_tree a (node a' f).

Definition In_forest {A : Type} (a : A) (f : forest A) : Prop :=
  Exists (fun t => In_tree a t) f.

Lemma Forall_nodes_In_tree :
  forall {A : Type} (P : A -> Prop) (t : tree A),
    Forall_nodes P t <-> (forall (x : A), In_tree x t -> P x).
Proof.
  intros A P t.
  split.
  { refine (tree_forall_ind A
              (fun t => Forall_nodes P t -> forall x : A, In_tree x t -> P x) _ t).
    intros a f IH pf x i.
    inv i; inv pf; auto.
    induction f; inv H0.
    inv IH; inv H3; auto.
    eapply IHf; auto.
    inv IH; auto.
    inv H3; auto. }
  { refine (tree_forall_ind A
              (fun t => (forall x : A, In_tree x t -> P x) -> Forall_nodes P t) _ t).
    intros a f IH pf; constructor.
    eapply pf; constructor.
    induction f; constructor.
    { inv IH.
      eapply H1.
      intros x i.
      eapply pf.
      repeat constructor; auto. }
    eapply IHf.
    inv IH; auto.
    { intros x i.
      eapply pf.
      inv i.
      constructor.
      constructor.
      right; auto. } }
Qed.

Inductive Forall_subtrees {A : Type} (P : tree A -> Prop) : tree A -> Prop :=
| Forall_subtrees_node : forall a f, P (node a f) -> Forall (Forall_subtrees P) f -> Forall_subtrees P (node a f).

Inductive Exists_subtree {A : Type} (P : tree A -> Prop) : tree A -> Prop :=
| Exists_subtree_here : forall a f, P (node a f) -> Exists_subtree P (node a f)
| Exists_subtree_there : forall a f, Exists (Exists_subtree P) f -> Exists_subtree P (node a f).

Inductive Exists_all_paths {A : Type} (P : tree A -> Prop) : tree A -> Prop :=
| Exists_all_paths_here : forall a f, P (node a f) -> Exists_all_paths P (node a f)
| Exists_all_paths_there : forall a f, Forall (Exists_all_paths P) f -> Exists_all_paths P (node a f).

Inductive AllUntil {A : Type} (P1 P2 : tree A -> Prop) : tree A -> Prop :=
| AllUntil_here : forall a f, P2 (node a f) -> AllUntil P1 P2 (node a f)
| AllUntil_there : forall a f, P1 (node a f) -> Forall (AllUntil P1 P2) f -> AllUntil P1 P2 (node a f).

Inductive ExistsUntil {A : Type} (P1 P2 : tree A -> Prop) : tree A -> Prop :=
| ExistsUntil_here : forall a f, P2 (node a f) -> ExistsUntil P1 P2 (node a f)
| ExistsUntil_there : forall a f, P1 (node a f) -> Exists (ExistsUntil P1 P2) f -> ExistsUntil P1 P2 (node a f).

Fixpoint unfold_tree_aux
    {A : Type}
    (R : relation A)
    (next : forall (a1 : A), {l : list A | Forall (fun a2 => R a2 a1) l })
    (init : A)
    (acc : Acc R init) {struct acc}
  : tree A :=
  match acc with
  | Acc_intro _ acc' =>
    node init (map (fun '(x;pf) => unfold_tree_aux R next x (acc' x pf))
                   (distribute (fun a => R a init) (next init)))
  end.

Definition unfold_tree
    {A : Type}
    (R : relation A)
   `{WF : @WellFounded A R}
    (next : forall (a : A), {l : list A | Forall (fun x => R x a) l })
    (init : A)
  : tree A :=
  unfold_tree_aux R next init (wellfounded init).

Fixpoint Forall_unfold_tree_aux
    {A : Type}
    (R : relation A)
    (P : A -> Prop)
    (next : forall (a : A), {l : list A | Forall (fun x => R x a) l })
    (init : A)
    (acc : Acc R init) {struct acc} :
    P init ->
    (forall (a : A) (pf : P a), Forall P (next a).1) ->
    Forall_nodes P (unfold_tree_aux R next init acc).
Proof.
  intros p pf.
  destruct acc.
  constructor; auto.
  eapply Forall_map.
  eapply Forall_forall.
  intros [x pf'] i.
  eapply Forall_unfold_tree_aux; eauto.
  destruct (In_distribute _ _ x pf' i).
  specialize (pf init p).
  rewrite Forall_forall in pf.
  auto.
Qed.

Lemma Forall_unfold_tree :
  forall
    {A : Type}
    (R : relation A)
   `{WF : WellFounded A R}
    (P : A -> Prop)
    (next : forall (a : A), {l : list A | Forall (fun x => R x a) l })
    (init : A) (p : P init),
    (forall (a : A) (pf : P a), Forall P (next a).1) ->
    Forall_nodes P (unfold_tree R next init).
Proof.
  intros A R WF P next init p pf.
  unfold unfold_tree.
  eapply Forall_unfold_tree_aux; auto.
Qed.

Fixpoint unfold_tree_aux_same
    {A : Type}
    (R : relation A)
    (next : forall (a : A), {l : list A | Forall (fun x => R x a) l })
    (init : A)
    (acc1 : Acc R init)
    (acc2 : Acc R init)
    {struct acc1} :
  unfold_tree_aux R next init acc1 = unfold_tree_aux R next init acc2.
Proof.
  destruct acc1 as [acc1], acc2 as [acc2].
  simpl.
  f_equal.
  eapply map_ext.
  intros [x pf].
  eapply unfold_tree_aux_same.
Qed.

Definition path
           {A : Type} {R : relation A}
           (next : forall (a : A), {l : list A | Forall (fun x => R x a) l })
           : A -> A -> Prop :=
  clos_refl_trans _ (fun (x y : A) => In y (next x).1).

Definition path_1n
           {A : Type} {R : relation A}
           (next : forall (a : A), {l : list A | Forall (fun x => R x a) l })
           : A -> A -> Prop :=
  clos_refl_trans_1n _ (fun (x y : A) => In y (next x).1).

Fixpoint unfold_tree_aux_sound
    {A : Type}
    (R : relation A)
    (next : forall (a : A), {l : list A | Forall (fun x => R x a) l })
    (init : A)
    (acc : Acc R init)
    (a : A)
    (i : In_tree a (unfold_tree_aux R next init acc))
    {struct acc} :
    path next init a.
Proof.
  generalize a i.
  rewrite <- Forall_nodes_In_tree.
  destruct acc.
  constructor.
  eapply rt_refl.
  eapply Forall_map.
  eapply Forall_forall.
  intros [x pf] i'.
  destruct (In_distribute _ _ x pf i') as [i'' pf']; auto.
  rewrite Forall_nodes_In_tree.
  intros y i'''.
  eapply rt_trans.
  eapply rt_step; eauto.
  eapply (unfold_tree_aux_sound A R next x _ y i''').
Qed.

Theorem unfold_tree_sound :
  forall
    {A : Type}
    (R : relation A)
   `{WF : WellFounded A R}
    (next : forall (a : A), {l : list A | Forall (fun x => R x a) l })
    (init : A),
  forall (a : A),
    In_tree a (unfold_tree R next init) ->
    path next init a.
Proof.
  intros A R WF next init a i.
  eapply unfold_tree_aux_sound; eauto.
Qed.

Lemma unfold_tree_unwrap :
  forall
    {A : Type}
    (R : relation A)
   `{WF : WellFounded A R}
    (next : forall (a : A), {l : list A | Forall (fun x => R x a) l })
    (init : A),
      unfold_tree R next init
    = node init (map (unfold_tree R next) (next init).1).
Proof.
  intros A R WF next init.
  unfold unfold_tree.
  destruct (wellfounded init).
  simpl.
  f_equal.
  destruct (next init) as [l pf].
  induction l as [|x xs IH].
  simpl; auto.
  Opaque unfold_tree_aux.
  simpl.
  f_equal.
  eapply unfold_tree_aux_same.
  eapply IH.
  Transparent unfold_tree_aux.
Qed.

Lemma unfold_tree_complete_1n :
  forall
    {A : Type}
    (R : relation A)
   `{WF : WellFounded A R}
    (next : forall (a : A), {l : list A | Forall (fun x => R x a) l })
    (init : A),
  forall (a : A),
    path_1n next init a ->
    In_tree a (unfold_tree R next init).
Proof.
  intros A R WF next init a ch.
  dependent induction ch.
  rewrite unfold_tree_unwrap.
  left.
  rewrite unfold_tree_unwrap.
  right.
  rewrite Exists_exists.
  exists (unfold_tree R next y).
  split; auto.
  eapply in_map; eauto.
Qed.

Theorem unfold_tree_complete :
  forall
    {A : Type}
    (R : relation A)
   `{WF : WellFounded A R}
    (next : forall (a : A), {l : list A | Forall (fun x => R x a) l })
    (init : A),
  forall (a : A),
    path next init a ->
    In_tree a (unfold_tree R next init).
Proof.
  intros A R WF next init a.
  pose proof (unfold_tree_complete_1n R next init a).
  unfold path, path_1n in *.
  rewrite clos_rt_rt1n_iff; auto.
Qed.
