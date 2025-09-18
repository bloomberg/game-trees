(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

Require Import Corelib.Classes.RelationClasses.
Require Import Corelib.Relations.Relation_Definitions.
From Stdlib Require Import Streams.
From Stdlib Require Import List.
From Stdlib Require Import Logic.Decidable.
From Stdlib Require Import Relations.Relation_Operators.

Require Import ExtLib.Core.RelDec.

Require Import GameTrees.Helpers.
Require Import GameTrees.Relations.
Require Import GameTrees.Trees.

Import ListNotations.
Import SigTNotations.

(* If R behaves like a "less than" relation,
   this function gets you the max of two elements. *)
Definition max2
           {A : Type}
           (R : relation A) `{RelDec A R}
           (x y : A) : A :=
  if rel_dec x y then y else x.

(* If R behaves like a "less than" relation,
   this function gets you the max in a list, or [None] if the list is empty. *)
Definition max
           {A : Type}
           (R : relation A) `{RelDec A R}
           (l : list A) : option A :=
  fold_right (fun x o => match o with
                         | None => Some x
                         | Some y => Some (max2 R x y)
                         end) None l.

Class StronglyConnected {A : Type} (R : relation A) : Prop :=
  strongly_connected : forall (a b : A), R a b \/ R b a.

Lemma max2_is_max :
  forall
    {A : Type} (R : relation A)
   `{D : RelDec A R} `{@RelDec_Correct A R D}
   `{Reflexive A R} `{Transitive A R} `{StronglyConnected A R}
    (x y : A),
    R x (max2 R x y) /\ R y (max2 R x y).
Proof.
  intros A R [D] [DC] Rf T C x y.
  unfold max2.
  pose proof (D' := DC x y).
  destruct (x ?[ R ] y) eqn:eq; intuition auto.
  pose proof (C x y).
  intuition auto with *.
Qed.

Lemma max_is_in :
  forall
    {A : Type} (R : relation A)
   `{D : RelDec A R} `{@RelDec_Correct A R D}
   `{Reflexive A R} `{Transitive A R} `{StronglyConnected A R}
    (l : list A),
  match max R l with
  | Some x => In x l
  | None => True
  end.
Proof.
 intros.
 induction l as [|x xs]; simpl; auto.
 destruct (max R xs); intuition auto.
 unfold max2.
 destruct (x ?[ R ] a); intuition auto.
Qed.

Lemma max_is_max :
  forall
    {A : Type} (R : relation A)
   `{D : RelDec A R} `{@RelDec_Correct A R D}
   `{Reflexive A R} `{Transitive A R} `{StronglyConnected A R}
    (l : list A),
  match max R l with
  | Some x => Forall (fun a => R a x) l
  | None => l = []
  end.
Proof.
  intros A R D DC Rf T S l.
  induction l as [|x xs]; simpl; auto.
  destruct (max R xs) eqn:eq; subst; auto.
  constructor.
  { destruct (max2_is_max R x a); auto. }
  { generalize IHxs.
    eapply Forall_impl.
    intros b pf.
    eapply T; eauto.
    destruct (max2_is_max R x a); auto. }
Qed.

(* An infinite stream of how the player turns go,
   and a decidable "less than" relation on how the score of each is evaluated. *)
Definition players (S : Type) :=
  Stream {R : relation S & RelDec R}.

(* The [Stream] counterpart of [CoForall]. *)
CoInductive Each {A : Type} (P : A -> Prop) : Stream A -> Prop :=
| EachCons : forall x l, P x -> Each P l -> Each P (Cons x l).


Definition player_operations_correct {S : Type} (ps : players S) :=
  Each (fun '(R; D) => RelDec_Correct D /\ Reflexive R /\ Transitive R /\ StronglyConnected R) ps.

(* The same player taking every turn: P1, P1, P1, ... *)
CoFixpoint one_player
           {S : Type}
           (R : relation S) `{D : RelDec S R} : players S :=
  Cons (R; D) (one_player R).

(* Two players taking turns one after another: P1, P2, P1, P2, ... *)
CoFixpoint two_players
           {S : Type}
           (R1 : relation S) `{D1 : RelDec S R1}
           (R2 : relation S) `{D2 : RelDec S R2} : players S :=
  Cons (R1; D1)
    (Cons (R2; D2) (two_players R1 R2)).

(* Three players taking turns one after another: P1, P2, P3, P1, P2, P3, ... *)
CoFixpoint three_players
           {S : Type}
           (R1 : relation S) `{D1 : RelDec S R1}
           (R2 : relation S) `{D2 : RelDec S R2}
           (R3 : relation S) `{D3 : RelDec S R3} : players S :=
  Cons (R1; D1)
    (Cons (R2; D2)
       (Cons (R3; D3) (three_players R1 R2 R3))).

(* Generalized version of the minimax algorithm for finite game trees.
   Annotates every node of the finite game tree [t] with
   the backed-up utility for the player whose turn it is at that depth. *)
Fixpoint eval_tree
         {G S : Type}
         (ps : players S)
         (score : G -> S)
         (t : tree G) : tree (G * S) :=
  match ps with
  | Cons (R; D) ps' =>
    match t with
    | node a f =>
        let f' := map (eval_tree ps' score) f in
        node (a, match max R (map snd (map root f')) with
                 | Some new_score => new_score
                 | None => score a
                 end) f'
    end
  end.

(* Walks the tree once and tags every node with the current head of a stream,
   recursing on children with the stream's tail.
   i.e. it "layers" metadata from a stream onto the tree level-by-level. *)
Fixpoint annotate_tree_levels
         {A B : Type}
         (s : Stream B)
         (t : tree A) : tree (A * B) :=
  match s with
  | Cons b s' =>
    match t with
    | node a f =>
      node (a, b) (map (annotate_tree_levels s') f)
    end
  end.

(* At every annotated node, the stored score is
   a (relation-)maximum of its children's backed-up scores.
   Concretely, it shows each child's score relates
   (via that node's player relation [R]) to the node's score chosen by [max]. *)
Lemma eval_tree_correct_rel :
  forall
    {G S : Type}
    (ps : players S)
    (score : G -> S)
    (t : tree G),
  player_operations_correct ps ->
  Forall_subtrees
    (fun t => let '((g, s), (R; _)) := root t in
              let later_scores : list S :=
                map (fun '((_, s), _) => s) (map root (children t)) in
              Forall (fun x => R x s) later_scores)
    (annotate_tree_levels ps (eval_tree ps score t)).
Proof.
  intros G S ps score t c.
  generalize ps c; clear ps c.
  refine (@tree_forall_ind G (fun t =>
    forall (ps : players S),
      player_operations_correct ps ->
      Forall_subtrees
        (fun t => let '((g, s), (R; _)) := root t in
                  let later_scores : list S :=
                    map (fun '((_, s), _) => s) (map root (children t)) in
                  Forall (fun x => R x s) later_scores)
        (annotate_tree_levels ps (eval_tree ps score t))) _ t).
  intros a f IH ps c.
  destruct ps as [[R D] ps].
  inv c.
  destruct H1 as [C [Rf [T SC]]].
  pose proof (IH' := Forall_appl _ _ (Forall_appl _ _ IH ps) H2);
    simpl in IH'; clear IH; rename IH' into IH.
  simpl in *.
  constructor; simpl.
  - set (f' := map (eval_tree ps score) f).
    set (ls := map snd (map root f')).
    assert (map_root_annotate_levels_snd_triple :
      forall {A B S : Type} (s : Stream B) (ts : list (tree (A * S))),
        map (fun '(_, s0, _) => s0) (map root (map (annotate_tree_levels s) ts))
      = map snd (map root ts)).
        { clear. intros A B S s ts.
          induction ts as [|t ts IH]; simpl; auto.
          assert (root_annotate_levels_snd_triple :
            forall {A B S : Type} (s : Stream B) (t : tree (A * S)),
            (fun '(_, s0, _) => s0) (root (annotate_tree_levels s t)) = snd (root t)).
          { clear. intros A B S s t. destruct s as [b s']; destruct t as [[a s0] f]; auto. }
            now rewrite root_annotate_levels_snd_triple, IH. }
    unfold relation in *.
    rewrite (map_root_annotate_levels_snd_triple _ _ _ ps f').
    fold ls.
    destruct (max R ls) as [s|] eqn:Hm.
    + pose proof (@max_is_max S R D C Rf T SC ls) as H.
      now rewrite Hm in H.
    + pose proof (@max_is_max S R D C Rf T SC ls) as H.
      rewrite Hm in H; now rewrite H.
  - eapply Forall_map.
    eapply Forall_map.
    eapply Forall_map.
    eapply Forall_map.
    eauto.
Qed.
