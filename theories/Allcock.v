(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Allcock's Theorem 1.1, on the three named cases.

    [DotsAndBoxes.allcock_move] opens the shortest loop in three cases and
    plays the standard move otherwise. The three cases are proved here:
    whenever one of them applies, the move the strategy names attains the value
    and no opening is better.

    The original development states the strategy and checks it by computation
    through [DotsAndBoxes.allcock_okb], which compares the named move against
    the value on a position at a time. [allcock_named_cases_optimal] replaces
    that check by a proof on those cases, so no computation is needed to know
    the strategy is right when one of them fires. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.AllcockI.
Require Import GameTrees.AllcockII.
Require Import GameTrees.AllcockIII.
Require Import GameTrees.AllcockStd.

Import ListNotations.

Open Scope Z_scope.

(** * The three named cases *)

Theorem allcock_named_cases_optimal :
  forall G p,
    wf G -> (case_i G || case_ii G || case_iii G)%bool = true ->
    allcock_move G = Some p ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hd Hm.
  destruct (case_i G) eqn:E1.
  - apply (allcock_case_i_optimal G p Hw E1 Hm).
  - destruct (case_ii G) eqn:E2.
    + apply (allcock_case_ii_complete G p Hw E2 Hm).
    + destruct (case_iii G) eqn:E3.
      * apply (allcock_case_iii_optimal G p Hw E3 Hm).
      * exfalso; cbn in Hd; discriminate.
Qed.

(** So on those cases the computational check is redundant: it succeeds. *)
Corollary allcock_okb_named_cases :
  forall G,
    wf G -> (case_i G || case_ii G || case_iii G)%bool = true ->
    allcock_okb G = true.
Proof.
  intros G Hw Hd; unfold allcock_okb.
  destruct (allcock_move G) as [p|] eqn:Hm; [|reflexivity].
  destruct (allcock_named_cases_optimal G p Hw Hd Hm) as [Hval _].
  apply Z.eqb_eq; exact Hval.
Qed.

(** And the strategy opens the shortest loop there, which on a position with a
    four-loop is a four-loop. *)
Corollary allcock_named_cases_move :
  forall G,
    (case_i G || case_ii G || case_iii G)%bool = true ->
    allcock_move G = shortest_of is_loop_b G.
Proof.
  intros G Hd; unfold allcock_move; rewrite Hd; reflexivity.
Qed.

(** * Outside the three cases *)

Lemma allcock_move_standard :
  forall G,
    (case_i G || case_ii G || case_iii G)%bool = false ->
    allcock_move G = standard_move G.
Proof. intros G H; unfold allcock_move; rewrite H; reflexivity. Qed.

(** There the strategy plays the standard move, and
    [AllcockStd.standard_move_reduces] turns its optimality into an identity
    between the closed form at the position and at what the move leaves. A
    position of one component needs nothing at all. *)
Theorem allcock_standard_optimal :
  forall G p,
    wf G -> (case_i G || case_ii G || case_iii G)%bool = false ->
    allcock_move G = Some p ->
    (snd p = [] \/ v41 G = vopen (fst p) (v41 (snd p))) ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hd Hm Hcase.
  rewrite (allcock_move_standard G Hd) in Hm.
  destruct (list_eq_dec comp_eq_dec (snd p) []) as [Hnil | Hnn].
  - apply (standard_move_singleton G p Hm Hnil).
  - destruct Hcase as [Hnil | Hid]; [contradiction|].
    apply (standard_move_reduces G p Hw Hm Hnn Hid).
Qed.

(** * The strategy, in one statement *)

(** Allcock's opener is optimal: outright on the three named cases, and
    elsewhere as soon as the closed form at the position agrees with the
    opening of the closed form at what the move leaves behind. *)
Theorem allcock_move_optimal :
  forall G p,
    wf G -> allcock_move G = Some p ->
    ((case_i G || case_ii G || case_iii G)%bool = true
     \/ snd p = []
     \/ v41 G = vopen (fst p) (v41 (snd p))) ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hm Hcase.
  destruct (case_i G || case_ii G || case_iii G)%bool eqn:Hd.
  - apply (allcock_named_cases_optimal G p Hw Hd Hm).
  - apply (allcock_standard_optimal G p Hw Hd Hm).
    destruct Hcase as [Hc | [Hnil | Hid]];
      [rewrite Hc in Hd; discriminate | left; exact Hnil | right; exact Hid].
Qed.
