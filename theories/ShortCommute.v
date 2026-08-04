(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Pushing a long opening past the short-chain fold.

    The decomposition's lower bound needs the short chains to be foldable
    across a loony opening: folding first and opening after is never dearer
    than opening first and folding after.

    [h1_commute] is that, for the fold of one-box chains. The proof is one step
    of monotonicity followed by one step of exchange, and it needs both sides
    to be comparable first: [h1_parity] and [ShortResidue.svopen_parity] show
    the two carry the same parity, which is what licenses [abs_step_mono].

    With [ShortFold.g_collapse] this covers every position holding a one-box
    chain, since there the two-box chains are already two one-box steps. *)

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
Require Import GameTrees.ShortResidue.
Require Import GameTrees.ShortAll.
Require Import GameTrees.ShortSplit.
Require Import GameTrees.ShortFold.

Import ListNotations.

Open Scope Z_scope.

(** * Openings leave nothing negative behind *)

Lemma svopen_nonneg : forall C y, 0 <= y -> 0 <= svopen C y.
Proof.
  intros C y Hy; rewrite svopen_alt.
  pose proof (shand_le_csize C) as H.
  pose proof (Z.abs_nonneg (y - Z.of_nat (shand C))) as Ha; lia.
Qed.

Lemma svopen_chain1 : forall z, svopen (Chain 1) z = Z.abs (z - 1).
Proof. intros z; rewrite (svopen_short (Chain 1) z) by reflexivity; reflexivity. Qed.

(** * The one-box fold carries a parity *)

Lemma h1_zero : forall y, 0 <= y -> h1 0 y = y.
Proof.
  intros y Hy; unfold h1.
  rewrite (proj2 (Z.leb_le 0 y)) by lia; lia.
Qed.

Lemma h1_parity :
  forall m y, 0 <= m -> 0 <= y -> Z.even (h1 m y) = Z.even (y + m).
Proof.
  intros m y Hm Hy; unfold h1.
  destruct (m <=? y) eqn:E.
  - apply Z.leb_le in E.
    rewrite Z.even_sub, Z.even_add.
    destruct (Z.even y), (Z.even m); reflexivity.
  - apply Z.leb_gt in E.
    rewrite Z.even_add.
    destruct (Z.even (m - y)) eqn:Ev; rewrite Z.even_sub in Ev;
      destruct (Z.even y), (Z.even m); cbn in Ev |- *;
      solve [reflexivity | discriminate].
Qed.

(** * One step of the fold is monotone on arguments of equal parity *)

Lemma abs_step_mono :
  forall p q,
    0 <= p -> p <= q -> Z.even p = Z.even q ->
    Z.abs (p - 1) <= Z.abs (q - 1).
Proof.
  intros p q Hp Hpq He.
  destruct (Z.le_gt_cases 1 p) as [H1 | H1].
  - rewrite (Z.abs_eq (p - 1)) by lia.
    rewrite (Z.abs_eq (q - 1)) by lia; lia.
  - assert (Hp0 : p = 0) by lia; subst p.
    assert (Hq1 : q <> 1) by (intros ->; cbn in He; discriminate).
    rewrite (Z.abs_neq (0 - 1)) by lia.
    destruct (Z.eq_dec q 0) as [-> | Hq0].
    + rewrite (Z.abs_neq (0 - 1)) by lia; lia.
    + rewrite (Z.abs_eq (q - 1)) by lia; lia.
Qed.

(** * The commutation *)

(** A loony opening pushed past the fold of one-box chains. *)
Theorem h1_commute :
  forall C n x,
    shortb C = false -> swf_comp C -> 0 <= x ->
    h1 (Z.of_nat n) (svopen C x) <= svopen C (h1 (Z.of_nat n) x).
Proof.
  intros C n x HC HwC Hx.
  assert (Hs : 0 <= svopen C x) by (apply svopen_nonneg; exact Hx).
  induction n as [|n IH].
  - cbn [Z.of_nat]; rewrite (h1_zero (svopen C x) Hs), (h1_zero x Hx).
    apply Z.le_refl.
  - assert (Hn : Z.of_nat (S n) = Z.of_nat n + 1) by lia.
    rewrite Hn.
    rewrite (h1_step (Z.of_nat n) (svopen C x)) by lia.
    rewrite (h1_step (Z.of_nat n) x) by lia.
    (* the two sides agree in parity, so one step of the fold preserves the
       inequality; the exchange then moves the opening outside *)
    assert (Hpar : Z.even (h1 (Z.of_nat n) (svopen C x))
                   = Z.even (svopen C (h1 (Z.of_nat n) x))).
    { assert (A : Z.even (h1 (Z.of_nat n) (svopen C x))
                  = Z.even (svopen C x + Z.of_nat n))
        by (apply h1_parity; lia).
      assert (B : Z.even (svopen C (h1 (Z.of_nat n) x))
                  = Z.even (Z.of_nat (csize C) + h1 (Z.of_nat n) x))
        by (apply svopen_parity).
      assert (Cc : Z.even (svopen C x) = Z.even (Z.of_nat (csize C) + x))
        by (apply svopen_parity).
      assert (D : Z.even (h1 (Z.of_nat n) x) = Z.even (x + Z.of_nat n))
        by (apply h1_parity; lia).
      rewrite A, B, !Z.even_add, Cc, D, !Z.even_add.
      destruct (Z.even (Z.of_nat (csize C))), (Z.even x),
               (Z.even (Z.of_nat n)); reflexivity. }
    eapply Z.le_trans.
    + apply abs_step_mono;
        [apply h1_nonneg; lia | exact IH | exact Hpar].
    + pose proof (svopen_exchange (Chain 1) C (h1 (Z.of_nat n) x)
                    eq_refl HC HwC (h1_nonneg (Z.of_nat n) x
                      ltac:(lia) Hx)) as Hex.
      rewrite !svopen_chain1 in Hex; exact Hex.
Qed.

(** * The two-box fold, where monotonicity is unavailable *)

(** With no one-box chain the fold is not order preserving, so the argument
    above does not apply. It commutes all the same, but for a different reason:
    once the fold has not run out its value is at most two, and both sides
    carry the same parity, so a value of two cannot meet a zero on the other
    side. The one configuration that would allow it, a four-loop opposite a
    fold that has already run out, forces the opened value back up to the
    fold's reach and is excluded. *)
Theorem g_0b_commute :
  forall C b x,
    shortb C = false -> swf_comp C -> 0 <= x ->
    g 0 b (svopen C x) <= svopen C (g 0 b x).
Proof.
  intros C b x HC HwC Hx.
  pose proof (shand_long_ge2 C HwC HC) as Hk.
  pose proof (shand_le_csize C) as Hle.
  pose proof (svopen_nonneg C x Hx) as HA0.
  pose proof (g_nonneg 0 b x Hx) as Hq0.
  destruct (Z.le_gt_cases (2 * Z.of_nat b) (svopen C x)) as [Hbig | Hsmall].
  - (* the fold has run out on the opened side *)
    rewrite (g_0b_big b (svopen C x) Hbig).
    rewrite (svopen_alt C (g 0 b x)), (svopen_alt C x).
    destruct (Z.le_gt_cases (2 * Z.of_nat b) x) as [Hx2 | Hx2].
    + rewrite (g_0b_big b x Hx2).
      destruct (Z.abs_spec (x - Z.of_nat (shand C))) as [[H1 E1] | [H1 E1]];
        destruct (Z.abs_spec (x - 2 * Z.of_nat b - Z.of_nat (shand C)))
          as [[H2 E2] | [H2 E2]]; rewrite E1, E2; lia.
    + assert (Hq2 : g 0 b x <= 2) by (apply g_0b_small; lia).
      destruct (Z.abs_spec (x - Z.of_nat (shand C))) as [[H1 E1] | [H1 E1]];
        destruct (Z.abs_spec (g 0 b x - Z.of_nat (shand C)))
          as [[H2 E2] | [H2 E2]]; rewrite E1, E2; lia.
  - (* the fold has not run out: its value is at most two *)
    assert (Hsm : g 0 b (svopen C x) <= 2) by (apply g_0b_small; lia).
    assert (Hsn : 0 <= g 0 b (svopen C x)) by (apply g_nonneg; lia).
    assert (Hrhs0 : 0 <= svopen C (g 0 b x)) by (apply svopen_nonneg; lia).
    assert (Hpar : Z.even (g 0 b (svopen C x)) = Z.even (svopen C (g 0 b x))).
    { assert (Q1 : Z.even (g 0 b (svopen C x)) = Z.even (svopen C x))
        by (rewrite (g_parity 0 b (svopen C x)); f_equal; cbn [Z.of_nat]; lia).
      assert (Q2 : Z.even (g 0 b x) = Z.even x)
        by (rewrite (g_parity 0 b x); f_equal; cbn [Z.of_nat]; lia).
      rewrite Q1, (svopen_parity C (g 0 b x)), (svopen_parity C x).
      rewrite !Z.even_add, Q2; reflexivity. }
    destruct (Z.eq_dec (g 0 b (svopen C x)) 2) as [H2 | Hne2].
    + rewrite H2 in Hpar |- *.
      assert (Hrne : svopen C (g 0 b x) <> 0).
      { intros Hz; rewrite (svopen_alt C (g 0 b x)) in Hz.
        pose proof (Z.abs_nonneg (g 0 b x - Z.of_nat (shand C))) as Hab.
        assert (Hu0 : Z.of_nat (csize C) = Z.of_nat (shand C)) by lia.
        assert (Hqk : g 0 b x = Z.of_nat (shand C)).
        { destruct (Z.abs_spec (g 0 b x - Z.of_nat (shand C)))
            as [[? E] | [? E]]; rewrite E in Hz; lia. }
        (* a long component with no surplus is a four-loop *)
        assert (Hk4 : Z.of_nat (shand C) = 4).
        { destruct C as [n | n].
          - cbn [swf_comp] in HwC; unfold shortb in HC.
            apply andb_false_iff in HC.
            assert (Hn3 : (3 <= n)%nat)
              by (destruct HC as [H | H]; apply Nat.leb_gt in H; lia).
            unfold shand, hand in Hu0; cbn [csize] in Hu0; lia.
          - cbn [swf_comp] in HwC; destruct HwC as [H4 _].
            unfold shand, hand; cbn [csize]; lia. }
        (* so the fold on x has run out, and the opened value reaches its
           reach exactly, contradicting the case *)
        assert (Hxbig : 2 * Z.of_nat b <= x).
        { destruct (Z.le_gt_cases (2 * Z.of_nat b) x) as [H | H]; [lia|].
          assert (Hs2 : g 0 b x <= 2) by (apply g_0b_small; lia); lia. }
        rewrite (g_0b_big b x Hxbig) in Hqk.
        rewrite (svopen_alt C x) in Hsmall.
        assert (Hxv : x - Z.of_nat (shand C) = 2 * Z.of_nat b) by lia.
        rewrite Hxv, (Z.abs_eq (2 * Z.of_nat b)) in Hsmall by lia; lia. }
      assert (He : Z.even (svopen C (g 0 b x)) = true)
        by (rewrite <- Hpar; reflexivity).
      assert (Hne1 : svopen C (g 0 b x) <> 1)
        by (intros E; rewrite E in He; discriminate).
      lia.
    + destruct (Z.eq_dec (g 0 b (svopen C x)) 0) as [H0 | Hne0]; [lia|].
      assert (H1 : g 0 b (svopen C x) = 1) by lia.
      rewrite H1 in Hpar |- *.
      assert (Ho : Z.even (svopen C (g 0 b x)) = false)
        by (rewrite <- Hpar; reflexivity).
      assert (Hz0 : svopen C (g 0 b x) <> 0)
        by (intros E; rewrite E in Ho; discriminate).
      lia.
Qed.

(** * What it gives for a position holding a one-box chain *)

Corollary g_commute_a1 :
  forall C a b x,
    shortb C = false -> swf_comp C -> (1 <= a)%nat -> 0 <= x ->
    g a b (svopen C x) <= svopen C (g a b x).
Proof.
  intros C a b x HC HwC Ha Hx.
  assert (Hs : 0 <= svopen C x) by (apply svopen_nonneg; exact Hx).
  rewrite (g_collapse a b (svopen C x) Ha Hs).
  rewrite (g_collapse a b x Ha Hx).
  assert (Hm : Z.of_nat a + 2 * Z.of_nat b = Z.of_nat (a + 2 * b)) by lia.
  rewrite Hm; apply h1_commute; assumption.
Qed.

(** * Commutation, for every position *)

(** A loony opening pushed past the short-chain fold, whichever chains it
    holds. *)
Theorem g_commute :
  forall C a b x,
    shortb C = false -> swf_comp C -> 0 <= x ->
    g a b (svopen C x) <= svopen C (g a b x).
Proof.
  intros C a b x HC HwC Hx.
  destruct a as [|a']; [apply g_0b_commute; assumption|].
  apply g_commute_a1; [assumption | assumption | lia | assumption].
Qed.
