(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** The closed form, for every position the board can present.

    [ShortDecomp.svalue_split] separates the chains of one and two boxes from
    the rest, and what remains is wellformed, so Berlekamp and Scott's
    classification computes it. Composing the two gives a closed form on
    positions their theory does not reach: fold the short chains onto
    [DotsAndBoxes.v41] of the loony part.

    [svalue_closed] is that composition. [svalue_closed_wf] checks it against
    the original theory, where it must and does agree. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.ShortControl.
Require Import GameTrees.ShortSmall.
Require Import GameTrees.ShortExact.
Require Import GameTrees.ShortAll.
Require Import GameTrees.ShortSplit.
Require Import GameTrees.ShortFold.
Require Import GameTrees.ShortDecomp.

Import ListNotations.

Open Scope Z_scope.

(** * The loony part, by the existing classification *)

Definition vlong (L : position) : Z :=
  match L with [] => 0 | C :: R => v41 (C :: R) end.

Definition sv (G : position) : Z :=
  g (c1 G) (c2 G) (vlong (longpart G)).

(** * The closed form *)

Theorem svalue_closed : forall G, swf G -> svalue G = sv G.
Proof.
  intros G Hw; rewrite (svalue_split G Hw); unfold sv; f_equal.
  assert (Hlw : wf (longpart G)) by (apply longpart_wf; exact Hw).
  destruct (longpart G) as [|C L] eqn:E; [reflexivity|].
  assert (Hcons : wf (C :: L)) by exact Hlw.
  cbn [vlong]; rewrite (svalue_wf _ Hcons).
  apply value_complete; [exact Hcons | discriminate].
Qed.

(** * Agreement with the original theory *)

(** On a wellformed position there are no short chains, the fold is empty, and
    the closed form is Berlekamp and Scott's. *)
Corollary svalue_closed_wf :
  forall G, wf G -> G <> [] -> value G = v41 G.
Proof.
  intros G Hw HNil; apply value_complete; assumption.
Qed.

Corollary sv_wf :
  forall G, wf G -> G <> [] -> sv G = v41 G.
Proof.
  intros G Hw HNil; unfold sv.
  assert (Hns : existsb shortb G = false).
  { apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [C [HinC HCs]].
    unfold wf in Hw; rewrite Forall_forall in Hw.
    specialize (Hw C HinC); destruct C as [n | n]; [|discriminate].
    pose proof (shortb_chain n HCs) as Hb; cbn [wf_comp] in Hw; lia. }
  assert (Ha : c1 G = 0%nat).
  { unfold c1; destruct (filter chain1b G) as [|C l] eqn:Ef; [reflexivity|].
    exfalso; assert (HinC : In C (filter chain1b G))
      by (rewrite Ef; left; reflexivity).
    apply filter_In in HinC; destruct HinC as [Hin Hc].
    assert (existsb shortb G = true)
      by (apply existsb_exists; exists C; split;
          [exact Hin | apply chain1b_shortb; exact Hc]).
    congruence. }
  assert (Hb : c2 G = 0%nat).
  { unfold c2; destruct (filter chain2b G) as [|C l] eqn:Ef; [reflexivity|].
    exfalso; assert (HinC : In C (filter chain2b G))
      by (rewrite Ef; left; reflexivity).
    apply filter_In in HinC; destruct HinC as [Hin Hc].
    assert (existsb shortb G = true)
      by (apply existsb_exists; exists C; split;
          [exact Hin | apply chain2b_shortb; exact Hc]).
    congruence. }
  rewrite Ha, Hb, g_00, (longpart_id G Hns).
  destruct G as [|C R]; [contradiction | reflexivity].
Qed.

(** So the closed form strictly extends the original: it agrees wherever that
    applies, and computes the rest. *)
Theorem svalue_closed_extends :
  forall G, wf G -> G <> [] -> value G = sv G.
Proof.
  intros G Hw HNil.
  rewrite (sv_wf G Hw HNil); apply value_complete; assumption.
Qed.
