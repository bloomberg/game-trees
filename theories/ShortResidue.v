(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Below the threshold.

    [ShortExact.svalue_scval2_ge2] settles every position whose capped
    controlled value reaches two. Beneath it the value is not a function of the
    controlled value alone, so a classification is needed rather than a formula.

    This file establishes the two invariants that constrain it. Both values
    carry the parity of the board, so they never differ by an odd amount; and
    the terminal bonus is even, which is what puts the parity into the
    controlled value. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.ShortControl.
Require Import GameTrees.ShortBonus.
Require Import GameTrees.ShortExact.

Import ListNotations.

Open Scope Z_scope.

(** * The capped opening carries the parity of what it opens *)

Lemma svopen_parity :
  forall C w,
    Z.even (svopen C w) = Z.even (Z.of_nat (csize C) + w).
Proof.
  intros C w; unfold svopen.
  destruct (Z.le_ge_cases w (Z.of_nat (shand C))) as [H | H].
  - rewrite Z.max_l by lia.
    rewrite Z.even_sub, Z.even_add.
    destruct (Z.even (Z.of_nat (csize C))), (Z.even w); reflexivity.
  - rewrite Z.max_r by lia.
    replace (Z.of_nat (csize C) - 2 * Z.of_nat (shand C) + w)
      with ((Z.of_nat (csize C) + w) - 2 * Z.of_nat (shand C)) by lia.
    rewrite Z.even_sub.
    replace (Z.even (2 * Z.of_nat (shand C))) with true
      by (rewrite Z.even_mul; reflexivity).
    destruct (Z.even (Z.of_nat (csize C) + w)); reflexivity.
Qed.

(** * The capped value carries the parity of the board *)

Theorem svalue_parity :
  forall G, Z.even (svalue G) = Z.even (Z.of_nat (size G)).
Proof.
  assert (Haux : forall n G, (length G <= n)%nat ->
            Z.even (svalue G) = Z.even (Z.of_nat (size G))).
  { induction n as [|n IH]; intros G Hn.
    - assert (HG : G = []) by (destruct G; simpl in Hn; [reflexivity | lia]).
      subst G; reflexivity.
    - destruct (list_eq_dec comp_eq_dec G []) as [-> | HNil]; [reflexivity|].
      destruct (svalue_attained G HNil) as [p [Hp Hval]].
      rewrite Hval; unfold svalue_open.
      rewrite svopen_parity.
      pose proof (selections_size G p Hp) as Hsz.
      pose proof (selections_length G p Hp) as Hlen.
      rewrite Z.even_add.
      rewrite (IH (snd p)) by lia.
      rewrite <- Z.even_add.
      rewrite <- Nat2Z.inj_add, Hsz; reflexivity. }
  intros G; apply (Haux (length G)); lia.
Qed.

(** * The terminal bonus is even *)

Lemma maxsh_even : forall G, Z.even (maxsh G) = true.
Proof.
  induction G as [|C G IH]; [reflexivity|].
  rewrite maxsh_cons.
  destruct (Z.max_dec (2 * Z.of_nat (shand C)) (maxsh G)) as [E | E]; rewrite E.
  - rewrite Z.even_mul; reflexivity.
  - exact IH.
Qed.

Lemma cap_even : forall G, Z.even (cap G) = true.
Proof.
  intros G; unfold cap.
  destruct (existsb longchain_b G); [reflexivity|].
  destruct (existsb is_3chain_b G); reflexivity.
Qed.

Lemma stb_even : forall G, Z.even (stb G) = true.
Proof.
  intros G; unfold stb.
  destruct (Z.min_dec (maxsh G) (cap G)) as [E | E]; rewrite E;
    [apply maxsh_even | apply cap_even].
Qed.

(** * So the controlled value carries it too *)

Lemma scbase_parity :
  forall G, Z.even (scbase G) = Z.even (Z.of_nat (size G)).
Proof.
  induction G as [|C G IH]; [reflexivity|].
  cbn [scbase]; unfold sweight.
  rewrite size_cons, Nat2Z.inj_add.
  replace (Z.of_nat (csize C) - 2 * Z.of_nat (shand C) + scbase G)
    with ((Z.of_nat (csize C) + scbase G) - 2 * Z.of_nat (shand C)) by lia.
  rewrite Z.even_sub.
  replace (Z.even (2 * Z.of_nat (shand C))) with true
    by (rewrite Z.even_mul; reflexivity).
  rewrite !Z.even_add, IH.
  destruct (Z.even (Z.of_nat (csize C))), (Z.even (Z.of_nat (size G)));
    reflexivity.
Qed.

Theorem scval2_parity :
  forall G, Z.even (scval2 G) = Z.even (Z.of_nat (size G)).
Proof.
  intros G; unfold scval2.
  rewrite Z.even_add, (stb_even G), (scbase_parity G).
  destruct (Z.even (Z.of_nat (size G))); reflexivity.
Qed.

(** The two never differ by an odd amount, whatever the position. Below the
    threshold this is what forces the residue to step in twos. *)
Theorem svalue_scval2_parity :
  forall G, Z.even (svalue G) = Z.even (scval2 G).
Proof.
  intros G; rewrite (svalue_parity G), (scval2_parity G); reflexivity.
Qed.

Corollary svalue_scval2_even_gap :
  forall G, Z.even (svalue G - scval2 G) = true.
Proof.
  intros G; rewrite Z.even_sub, (svalue_scval2_parity G).
  destruct (Z.even (scval2 G)); reflexivity.
Qed.
