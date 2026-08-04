(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Allcock's Theorem 1.1, case (ii).

    The case names the shortest loop on a position whose controlled value lies
    in [-1, 1] and which holds a four-loop, provided what is left after
    removing one four-loop is not exactly three three-chains.

    [Shortest.shortest_loop_is_four] identifies that move as a four-loop, and
    [Opener.open_4loop_optimal] shows opening a four-loop attains the value
    whenever the position is not made of three-chains and four-loops alone.
    [allcock_case_ii_optimal] is the two composed.

    The positions the composition misses are exactly those made of
    three-chains and four-loops. [case_ii_only34_shape] pins them down: the
    case's own bounds leave three, up to order. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.Shortest.
Require Import GameTrees.Opener.
Require Import GameTrees.Only34.

Import ListNotations.

Open Scope Z_scope.

(** * The strategy opens the shortest loop in this case *)

Lemma allcock_move_case_ii :
  forall G, case_ii G = true -> allcock_move G = shortest_of is_loop_b G.
Proof.
  intros G H; unfold allcock_move.
  assert (Hd : (case_i G || case_ii G || case_iii G)%bool = true)
    by (rewrite H; destruct (case_i G), (case_iii G); reflexivity).
  rewrite Hd; reflexivity.
Qed.

Lemma case_ii_parts :
  forall G, case_ii G = true ->
    cval G <= 1 /\ -1 <= cval G /\ (1 <= count4 G)%nat /\
    rest_is_three_threes_b G = false.
Proof.
  intros G H; unfold case_ii in H.
  apply andb_true_iff in H; destruct H as [H Hnr].
  apply negb_true_iff in Hnr.
  apply andb_true_iff in H; destruct H as [H H4].
  apply andb_true_iff in H; destruct H as [Hle Hge].
  apply Z.leb_le in Hle; apply Z.leb_le in Hge; apply Nat.leb_le in H4.
  repeat split; assumption.
Qed.

(** * The case, where the position is not all three-chains and four-loops *)

Theorem allcock_case_ii_optimal :
  forall G p,
    wf G -> case_ii G = true -> only34 G = false ->
    allcock_move G = Some p ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hii Honly Hm.
  destruct (case_ii_parts G Hii) as [Hle [Hge [H4 Hnr]]].
  rewrite (allcock_move_case_ii G Hii) in Hm.
  assert (Hp4 : fst p = Loop 4)
    by (apply (shortest_loop_is_four G p Hw H4); exact Hm).
  assert (Hin : In p (selections G))
    by (apply (shortest_of_In is_loop_b); exact Hm).
  destruct p as [C rest]; cbn [fst] in Hp4; subst C.
  assert (H4b : existsb is_4loop_b G = true)
    by (apply (proj2 (count4_pos_iff G)); lia).
  destruct (open_4loop_optimal G rest Hw Hin H4b Honly ltac:(lia))
    as [Hval Hmin].
  split; [symmetry; exact Hval | exact Hmin].
Qed.

(** * The case, where the position is all three-chains and four-loops *)

(** Here the value and the option are both read off the two counts, and the
    case's bounds admit only three pairs: the fourth, three three-chains
    beside one four-loop, is exactly what the case sets aside. *)
Theorem allcock_case_ii_only34 :
  forall G p,
    wf G -> case_ii G = true -> only34 G = true ->
    allcock_move G = Some p ->
    value G = value_open p.
Proof.
  intros G p Hw Hii H34 Hm.
  destruct (case_ii_parts G Hii) as [Hle [Hge [H4 Hnr]]].
  rewrite (allcock_move_case_ii G Hii) in Hm.
  assert (Hp4 : fst p = Loop 4)
    by (apply (shortest_loop_is_four G p Hw H4); exact Hm).
  assert (Hin : In p (selections G))
    by (apply (shortest_of_In is_loop_b); exact Hm).
  destruct p as [C rest]; cbn [fst] in Hp4; subst C.
  destruct (only34_open_four G rest Hw H34 Hin) as [Hv Ho].
  rewrite Hv, Ho.
  destruct (case_ii_only34_counts G H34 H4 Hge Hle)
    as [[E3 E4] | [[E3 E4] | [[E3 E4] | [E3 E4]]]];
    try (rewrite E3, E4; reflexivity).
  exfalso; rewrite (only34_three_threes G H34 E3 E4) in Hnr; discriminate.
Qed.

(** * Case (ii), complete *)

Theorem allcock_case_ii_complete :
  forall G p,
    wf G -> case_ii G = true -> allcock_move G = Some p ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hii Hm.
  assert (Hval : value G = value_open p).
  { destruct (only34 G) eqn:E34.
    - apply (allcock_case_ii_only34 G p Hw Hii E34 Hm).
    - destruct (allcock_case_ii_optimal G p Hw Hii E34 Hm) as [Hv _];
        exact Hv. }
  assert (HNil : G <> []).
  { destruct (case_ii_parts G Hii) as [_ [_ [H4 _]]].
    intros ->; unfold count4 in H4; simpl in H4; lia. }
  split; [exact Hval|].
  apply (allcock_move_optimal_iff G p HNil Hm); exact Hval.
Qed.
