(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Positions of short chains, and the bounds the control proof needs.

    The control bound for the capped recursion breaks into an easy step, where
    removing a component cannot raise the terminal bonus, and a rise case where
    it can. The rise is narrow: it needs the opened component to hold a
    strictly larger handout than anything left, and the cap to stay above what
    is left. That forces the remainder to be chains of at most three boxes.

    [svalue_scbase_short] and [svalue_scbase_small] are the two bounds those
    remainders satisfy, and they are what lets the rise case be discharged by
    the controller taking the opened component whole rather than declining
    it. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.ShortControl.

Import ListNotations.

Open Scope Z_scope.

(** * Chains of bounded length *)

(** A chain of one or two boxes: one with no handout to spare. *)
Definition shortb (C : comp) : bool :=
  match C with Chain n => ((1 <=? n) && (n <=? 2))%nat | Loop _ => false end.

(** A chain of at most three boxes. *)
Definition smallb (C : comp) : bool :=
  match C with Chain n => ((1 <=? n) && (n <=? 3))%nat | Loop _ => false end.

Lemma shortb_chain : forall n, shortb (Chain n) = true -> (1 <= n <= 2)%nat.
Proof.
  intros n H; unfold shortb in H; apply andb_true_iff in H.
  destruct H as [H1 H2]; apply Nat.leb_le in H1; apply Nat.leb_le in H2; lia.
Qed.

Lemma smallb_chain : forall n, smallb (Chain n) = true -> (1 <= n <= 3)%nat.
Proof.
  intros n H; unfold smallb in H; apply andb_true_iff in H.
  destruct H as [H1 H2]; apply Nat.leb_le in H1; apply Nat.leb_le in H2; lia.
Qed.

Lemma shortb_loop : forall n, shortb (Loop n) = false.
Proof. reflexivity. Qed.

Lemma smallb_loop : forall n, smallb (Loop n) = false.
Proof. reflexivity. Qed.

Lemma shortb_smallb : forall C, shortb C = true -> smallb C = true.
Proof.
  intros [n | n] H; [|discriminate].
  pose proof (shortb_chain n H) as Hb.
  unfold smallb; apply andb_true_iff; split; apply Nat.leb_le; lia.
Qed.

(** A short chain has its whole self as handout, so it weighs its own length
    against the controller. *)
Lemma sweight_short :
  forall C, shortb C = true -> sweight C = - Z.of_nat (csize C).
Proof.
  intros [n | n] H; [|discriminate].
  pose proof (shortb_chain n H) as Hb.
  unfold sweight, shand, hand; cbn [csize]; rewrite Nat.min_r by lia; lia.
Qed.

Lemma svopen_short :
  forall C w, shortb C = true -> svopen C w = Z.abs (w - Z.of_nat (csize C)).
Proof.
  intros [n | n] w H; [|discriminate].
  pose proof (shortb_chain n H) as Hb.
  unfold svopen, shand, hand; cbn [csize]; rewrite Nat.min_r by lia.
  destruct (Z.le_gt_cases w (Z.of_nat n)) as [Hle | Hgt].
  - rewrite Z.abs_neq by lia; lia.
  - rewrite Z.abs_eq by lia; lia.
Qed.

(** Every chain of one to three boxes weighs at least one against the
    controller. *)
Lemma sweight_small_neg :
  forall C, smallb C = true -> sweight C <= -1.
Proof.
  intros [n | n] H; [|discriminate].
  pose proof (smallb_chain n H) as Hb.
  unfold sweight, shand, hand; cbn [csize].
  destruct n as [|[|[|[|n]]]]; cbn [Nat.min]; lia.
Qed.

Lemma scbase_small_nonpos :
  forall H, forallb smallb H = true -> scbase H <= 0.
Proof.
  induction H as [|C H IH]; intros Hf; [reflexivity|].
  simpl in Hf; apply andb_true_iff in Hf; destruct Hf as [HC HH].
  cbn [scbase]; pose proof (sweight_small_neg C HC); pose proof (IH HH); lia.
Qed.

(** The head of a position is always an available opening. *)
Lemma In_head_selections :
  forall C G, In (C, G) (selections (C :: G)).
Proof. intros C G; simpl; left; reflexivity. Qed.

Lemma svalue_le_head :
  forall C G, svalue (C :: G) <= svopen C (svalue G).
Proof.
  intros C G.
  exact (svalue_le_open (C :: G) (C, G) (In_head_selections C G)).
Qed.

(** * The two bounds *)

(** On chains of at most two boxes the controller banks nothing: the value
    never exceeds what the base has already given away. *)
Theorem svalue_scbase_short :
  forall H, forallb shortb H = true -> svalue H + scbase H <= 0.
Proof.
  induction H as [|C H IH]; intros Hf; [reflexivity|].
  simpl in Hf; apply andb_true_iff in Hf; destruct Hf as [HC HH].
  specialize (IH HH).
  pose proof (svalue_le_head C H) as Hle.
  rewrite (svopen_short C (svalue H) HC) in Hle.
  pose proof (svalue_nonneg H) as Hpos.
  cbn [scbase]; rewrite (sweight_short C HC).
  assert (Hc : 0 <= Z.of_nat (csize C)) by lia.
  destruct (Z.le_gt_cases (svalue H) (Z.of_nat (csize C))) as [Hb | Hb].
  - rewrite Z.abs_neq in Hle by lia; lia.
  - rewrite Z.abs_eq in Hle by lia; lia.
Qed.

(** On chains of at most three boxes it exceeds it by at most two, which is
    the three-chain's own surplus. *)
Theorem svalue_scbase_small :
  forall H, forallb smallb H = true -> svalue H + scbase H <= 2.
Proof.
  induction H as [|C H IH]; intros Hf; [cbn; lia|].
  simpl in Hf; apply andb_true_iff in Hf; destruct Hf as [HC HH].
  specialize (IH HH).
  pose proof (svalue_le_head C H) as Hle.
  pose proof (svalue_nonneg H) as Hpos.
  pose proof (scbase_small_nonpos H HH) as Hcb.
  destruct C as [n | n]; [|discriminate].
  pose proof (smallb_chain n HC) as Hb.
  unfold svopen, shand, hand in Hle; cbn [csize] in Hle.
  cbn [scbase]; unfold sweight, shand, hand; cbn [csize].
  assert (Hn : n = 1%nat \/ n = 2%nat \/ n = 3%nat) by lia.
  destruct Hn as [-> | [-> | ->]]; cbn [Nat.min] in Hle |- *.
  - destruct (Z.le_gt_cases (svalue H) 1) as [Hz | Hz];
      [rewrite Z.max_l in Hle by lia | rewrite Z.max_r in Hle by lia]; lia.
  - destruct (Z.le_gt_cases (svalue H) 2) as [Hz | Hz];
      [rewrite Z.max_l in Hle by lia | rewrite Z.max_r in Hle by lia]; lia.
  - destruct (Z.le_gt_cases (svalue H) 2) as [Hz | Hz];
      [rewrite Z.max_l in Hle by lia | rewrite Z.max_r in Hle by lia]; lia.
Qed.

(** A position of short chains is one of small chains. *)
Lemma forallb_short_small :
  forall H, forallb shortb H = true -> forallb smallb H = true.
Proof.
  induction H as [|C H IH]; intros Hf; [reflexivity|].
  simpl in Hf |- *; apply andb_true_iff in Hf; destruct Hf as [HC HH].
  rewrite (shortb_smallb C HC); simpl; apply IH; exact HH.
Qed.
