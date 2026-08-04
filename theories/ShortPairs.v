(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Two-component positions, and why Berlekamp's terminal bonus does not
    transfer to short chains.

    [svalue_pair] is the closed form for every position of two components,
    short chains included: the opener picks whichever of the two openings is
    cheaper, and each is read off the other component's length. No induction is
    needed, because a single component is taken whole.

    [svalue_pair_chain1] and [svalue_pair_chain2] read off the short cases: a
    chain of one or two boxes beside anything longer drives its length down by
    exactly its own.

    [tb_does_not_transfer] is the obstruction to porting [value_complete]. On a
    three-chain beside a four-loop the effective terminal bonus is six, which is
    Berlekamp's value; on a one-box or two-box chain beside the same loop it is
    eight, where his classification, which sees only loops and three-chains,
    reports four. A handout of two has no slot in the 4/6/8 split, so the split
    has to be replaced rather than extended. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.ShortControl.

Import ListNotations.

Open Scope Z_scope.

(** * Every two-component position, in closed form *)

Lemma svalue_single_c : forall C, svalue [C] = Z.of_nat (csize C).
Proof.
  intros C.
  assert (H : svalue [C] = svopen C (svalue []))
    by (rewrite svalue_cons; reflexivity).
  assert (Hn : svalue (@nil comp) = 0) by reflexivity.
  rewrite H, Hn; unfold svopen.
  assert (Hz : 0 <= Z.of_nat (shand C)) by lia.
  rewrite Z.max_l by lia; lia.
Qed.

(** The opener opens one of the two, and whichever it is, the other is then
    taken whole. *)
Theorem svalue_pair :
  forall C D,
    svalue [C; D] =
    Z.min (svopen C (Z.of_nat (csize D))) (svopen D (Z.of_nat (csize C))).
Proof.
  intros C D.
  rewrite svalue_cons; simpl selections; simpl map.
  unfold svalue_open; cbn [fst snd].
  rewrite !svalue_single_c.
  unfold minl; simpl fold_left; reflexivity.
Qed.

(** * The short cases *)

Lemma shand_chain1 : shand (Chain 1) = 1%nat.
Proof. reflexivity. Qed.

Lemma shand_chain2 : shand (Chain 2) = 2%nat.
Proof. reflexivity. Qed.

(** A component of two boxes or more has a handout of at least two, unless it
    is the one-box chain. *)
Lemma shand_ge2 : forall D, (2 <= csize D)%nat -> (2 <= shand D)%nat.
Proof.
  intros [k | k] Hc; unfold shand, hand; simpl csize in *; lia.
Qed.

Lemma shand_ge1 : forall D, (1 <= csize D)%nat -> (1 <= shand D)%nat.
Proof.
  intros [k | k] Hc; unfold shand, hand; simpl csize in *; lia.
Qed.

Lemma shand_loop : forall k, (4 <= k)%nat -> shand (Loop k) = 4%nat.
Proof. intros k Hk; unfold shand, hand; cbn [csize]; lia. Qed.

(** A one-box chain beside anything takes exactly one box off it. *)
Theorem svalue_pair_chain1 :
  forall D, (1 <= csize D)%nat ->
    svalue [Chain 1; D] = Z.of_nat (csize D) - 1.
Proof.
  intros D Hc; rewrite svalue_pair.
  pose proof (shand_ge1 D Hc) as Hh.
  pose proof (shand_le_csize D) as Hle.
  assert (Hz : 1 <= Z.of_nat (shand D) <= Z.of_nat (csize D)) by lia.
  unfold svopen at 1; rewrite shand_chain1; simpl csize.
  unfold svopen.
  rewrite (Z.max_r (1 - Z.of_nat (csize D))) by lia.
  rewrite (Z.max_l (Z.of_nat (csize D) - 1)) by lia.
  lia.
Qed.

(** A two-box chain beside anything of two boxes or more takes two off it. *)
Theorem svalue_pair_chain2 :
  forall D, (2 <= csize D)%nat ->
    svalue [Chain 2; D] = Z.of_nat (csize D) - 2.
Proof.
  intros D Hc; rewrite svalue_pair.
  pose proof (shand_ge2 D Hc) as Hh.
  pose proof (shand_le_csize D) as Hle.
  assert (Hz : 2 <= Z.of_nat (shand D) <= Z.of_nat (csize D)) by lia.
  unfold svopen at 1; rewrite shand_chain2; simpl csize.
  unfold svopen.
  rewrite (Z.max_r (2 - Z.of_nat (csize D))) by lia.
  rewrite (Z.max_l (Z.of_nat (csize D) - 2)) by lia.
  lia.
Qed.

(** So the short chain families beside a loop are settled outright. *)
Corollary svalue_chain1_loop :
  forall k, (4 <= k)%nat -> svalue [Chain 1; Loop k] = Z.of_nat k - 1.
Proof. intros k Hk; apply svalue_pair_chain1; simpl csize; lia. Qed.

Corollary svalue_chain2_loop :
  forall k, (4 <= k)%nat -> svalue [Chain 2; Loop k] = Z.of_nat k - 2.
Proof. intros k Hk; apply svalue_pair_chain2; simpl csize; lia. Qed.

(** * Berlekamp's terminal bonus does not transfer *)

(** The effective terminal bonus of a position: what the value exceeds the
    capped base by. On the positions Berlekamp's theory covers and where the
    controlled value is at least two, this is his [tb]. *)
Definition ebonus (G : position) : Z := svalue G - scbase G.

(** On a three-chain beside a four-loop it is six, which is what [tb] reports
    for a position of loops and three-chains. *)
Example ebonus_three_loop : ebonus [Chain 3; Loop 4] = 6.
Proof. reflexivity. Qed.

Example tb_three_loop_is_six : tb [Chain 3; Loop 4] = 6.
Proof. reflexivity. Qed.

(** On a one-box or a two-box chain beside the same loop it is eight, while
    [tb] reports four: the classification sees a chain that is not a
    three-chain and drops to its default, but a handout of one or two boxes is
    not a handout of two boxes from a long chain. *)
Example ebonus_one_loop : ebonus [Chain 1; Loop 4] = 8.
Proof. reflexivity. Qed.

Example ebonus_two_loop : ebonus [Chain 2; Loop 4] = 8.
Proof. reflexivity. Qed.

Example tb_one_loop_is_four : tb [Chain 1; Loop 4] = 4.
Proof. reflexivity. Qed.

Example tb_two_loop_is_four : tb [Chain 2; Loop 4] = 4.
Proof. reflexivity. Qed.

(** The obstruction, as one statement: [tb] is correct on the long position and
    wrong by four on both short ones, so no reading of the 4/6/8 split extends
    it. Extending [value_complete] to short chains needs a different
    classification, not a wider one. *)
Theorem tb_does_not_transfer :
  ebonus [Chain 3; Loop 4] = tb [Chain 3; Loop 4] /\
  ebonus [Chain 1; Loop 4] = tb [Chain 1; Loop 4] + 4 /\
  ebonus [Chain 2; Loop 4] = tb [Chain 2; Loop 4] + 4.
Proof. repeat split; reflexivity. Qed.

(** And the discrepancy is not an artefact of one loop length: it persists as
    the loop grows. *)
Theorem tb_gap_persists :
  forall k, (4 <= k)%nat ->
    ebonus [Chain 1; Loop k] = 8 /\ tb [Chain 1; Loop k] = 4.
Proof.
  intros k Hk; split; [| reflexivity].
  unfold ebonus; rewrite (svalue_chain1_loop k Hk).
  assert (Hb : scbase [Chain 1; Loop k] = Z.of_nat k - 9).
  { cbn [scbase]; unfold sweight.
    rewrite shand_chain1, (shand_loop k Hk); cbn [csize]; lia. }
  rewrite Hb; lia.
Qed.
