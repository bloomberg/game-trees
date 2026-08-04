(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** The short-chain fold in closed form.

    [ShortSplit.g] folds the short chains onto the value of what remains. This
    file computes it.

    A one-box chain steps the value by one. Iterated, that is [h1]: it counts
    down to zero and then alternates, so below its reach the answer depends only
    on a parity. [g_a0_closed] identifies the fold of one-box chains with [h1],
    and [h1_mono] is the monotonicity that follows: on arguments of equal
    parity the fold is order preserving.

    The monotonicity is what the decomposition needs, and it holds only while a
    one-box chain is present. Steps of two alone cannot reach odd residues, and
    the corresponding fold is governed modulo four rather than modulo two;
    [h1_mono_fails_by_two] records the failure. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.ShortControl.
Require Import GameTrees.ShortSmall.
Require Import GameTrees.ShortAll.
Require Import GameTrees.ShortSplit.

Import ListNotations.

Open Scope Z_scope.

(** * Taking absolute values does not disturb parity *)

Lemma even_abs : forall z, Z.even (Z.abs z) = Z.even z.
Proof.
  intros z; destruct (Z.abs_spec z) as [[_ ->] | [_ ->]]; [reflexivity|].
  rewrite Z.even_opp; reflexivity.
Qed.

Lemma even_sub1 : forall z, Z.even (z - 1) = negb (Z.even z).
Proof.
  intros z; rewrite Z.even_sub; cbn [Z.even].
  destruct (Z.even z); reflexivity.
Qed.

Lemma even_sub2 : forall z, Z.even (z - 2) = Z.even z.
Proof.
  intros z; rewrite Z.even_sub; cbn [Z.even].
  destruct (Z.even z); reflexivity.
Qed.

Lemma even_add1 : forall z, Z.even (z + 1) = negb (Z.even z).
Proof.
  intros z; rewrite Z.even_add; cbn [Z.even].
  destruct (Z.even z); reflexivity.
Qed.

Lemma even_add2 : forall z, Z.even (z + 2) = Z.even z.
Proof.
  intros z; rewrite Z.even_add; cbn [Z.even].
  destruct (Z.even z); reflexivity.
Qed.

(** * The fold carries a parity of its own *)

(** Every step moves the value by the length of the chain opened, so the fold
    shifts parity by the number of one-box chains and leaves the two-box ones
    alone. *)
Theorem g_parity :
  forall a b w, Z.even (g a b w) = Z.even (w + Z.of_nat a).
Proof.
  intros a b w.
  remember (a + b)%nat as n eqn:En; revert a b w En.
  induction n as [|n IH]; intros a b w En.
  - assert (Ha : a = 0%nat) by lia; assert (Hb : b = 0%nat) by lia; subst.
    rewrite g_00; f_equal; lia.
  - destruct a as [|a']; destruct b as [|b'].
    + rewrite g_00; f_equal; lia.
    + rewrite g_0b, even_abs, even_sub2.
      rewrite (IH 0%nat b' w) by lia; reflexivity.
    + rewrite g_a0, even_abs, even_sub1.
      rewrite (IH a' 0%nat w) by lia.
      assert (Hz : w + Z.of_nat (S a') = (w + Z.of_nat a') + 1) by lia.
      rewrite Hz, even_add1; reflexivity.
    + (* both branches of the minimum share the parity, so the minimum has it *)
      assert (Hz : w + Z.of_nat (S a') = (w + Z.of_nat a') + 1) by lia.
      assert (E1 : Z.even (Z.abs (g a' (S b') w - 1))
                   = Z.even (w + Z.of_nat (S a'))).
      { rewrite even_abs, even_sub1, (IH a' (S b') w) by lia.
        rewrite Hz, even_add1; reflexivity. }
      assert (E2 : Z.even (Z.abs (g (S a') b' w - 2))
                   = Z.even (w + Z.of_nat (S a'))).
      { rewrite even_abs, even_sub2, (IH (S a') b' w) by lia; reflexivity. }
      rewrite g_ab.
      destruct (Z.min_dec (Z.abs (g a' (S b') w - 1))
                          (Z.abs (g (S a') b' w - 2))) as [E | E];
        rewrite E; assumption.
Qed.

(** * One-box chains alone *)

(** The fold of [m] one-box chains: it counts the value down to zero and then
    alternates, so beneath its reach only a parity survives. *)
Definition h1 (m w : Z) : Z :=
  if m <=? w then w - m else (if Z.even (m - w) then 0 else 1).

Lemma h1_nonneg : forall m w, 0 <= m -> 0 <= w -> 0 <= h1 m w.
Proof.
  intros m w Hm Hw; unfold h1.
  destruct (m <=? w) eqn:E; [apply Z.leb_le in E; lia|].
  destruct (Z.even (m - w)); lia.
Qed.

Lemma h1_step :
  forall m w, 0 <= m -> 0 <= w -> h1 (m + 1) w = Z.abs (h1 m w - 1).
Proof.
  intros m w Hm Hw; unfold h1.
  destruct (Z.lt_trichotomy w m) as [Hlt | [Heq | Hgt]].
  - (* below the reach on both sides: the parity flips *)
    rewrite (proj2 (Z.leb_gt (m + 1) w)) by lia.
    rewrite (proj2 (Z.leb_gt m w)) by lia.
    replace (m + 1 - w) with ((m - w) + 1) by lia.
    rewrite Z.even_add; cbn [Z.even].
    destruct (Z.even (m - w)); reflexivity.
  - subst w; rewrite (proj2 (Z.leb_gt (m + 1) m)) by lia.
    rewrite (proj2 (Z.leb_le m m)) by lia.
    replace (m + 1 - m) with 1 by lia; cbn [Z.even].
    replace (m - m) with 0 by lia; reflexivity.
  - rewrite (proj2 (Z.leb_le m w)) by lia.
    destruct (Z.le_gt_cases (m + 1) w) as [H | H].
    + rewrite (proj2 (Z.leb_le (m + 1) w)) by lia.
      rewrite Z.abs_eq by lia; lia.
    + assert (Hw1 : w = m + 1 - 1) by lia.
      rewrite (proj2 (Z.leb_gt (m + 1) w)) by lia.
      replace (m + 1 - w) with 1 by lia; cbn [Z.even].
      rewrite Z.abs_eq by lia; lia.
Qed.

(** The fold of one-box chains is exactly that. *)
Theorem g_a0_closed :
  forall a w, 0 <= w -> g a 0 w = h1 (Z.of_nat a) w.
Proof.
  induction a as [|a IH]; intros w Hw.
  - rewrite g_00; unfold h1; cbn [Z.of_nat].
    rewrite (proj2 (Z.leb_le 0 w)) by lia; lia.
  - rewrite g_a0, (IH w Hw), Nat2Z.inj_succ.
    replace (Z.succ (Z.of_nat a)) with (Z.of_nat a + 1) by lia.
    rewrite (h1_step (Z.of_nat a) w) by lia; reflexivity.
Qed.

(** * Monotonicity on arguments of equal parity *)

Theorem h1_mono :
  forall m x y,
    0 <= m -> 0 <= x -> x <= y -> Z.even x = Z.even y ->
    h1 m x <= h1 m y.
Proof.
  intros m x y Hm Hx Hxy Hp; unfold h1.
  destruct (Z.le_gt_cases m x) as [H1 | H1].
  - (* both beyond the reach *)
    rewrite (proj2 (Z.leb_le m x)) by lia.
    rewrite (proj2 (Z.leb_le m y)) by lia; lia.
  - rewrite (proj2 (Z.leb_gt m x)) by lia.
    destruct (Z.le_gt_cases m y) as [H2 | H2].
    + (* x below, y beyond: the parity decides whether one box is left over *)
      rewrite (proj2 (Z.leb_le m y)) by lia.
      destruct (Z.even (m - x)) eqn:E; [lia|].
      assert (Hne : y <> m).
      { intros Hym; rewrite Z.even_sub in E.
        rewrite <- Hym, <- Hp in E.
        destruct (Z.even x); discriminate. }
      lia.
    + rewrite (proj2 (Z.leb_gt m y)) by lia.
      rewrite !Z.even_sub, Hp.
      destruct (Z.even m), (Z.even y); cbn [Bool.eqb]; lia.
Qed.

(** Steps of two are not monotone in the same way: two one-box chains carry
    zero and two to zero and two, but a single two-box chain reverses them. *)
Example h1_mono_fails_by_two :
  g 0 1 0 = 2 /\ g 0 1 2 = 0.
Proof. split; reflexivity. Qed.

(** * Two one-box steps against one two-box step *)

(** Two one-box chains never cost more than a two-box chain, and cost the same
    unless the value has already reached zero. *)
Lemma abs_two_steps :
  forall p, 0 <= p -> Z.abs (Z.abs (p - 1) - 1) <= Z.abs (p - 2).
Proof.
  intros p Hp; destruct (Z.le_gt_cases 2 p) as [H2 | H2].
  - rewrite (Z.abs_eq (p - 1)) by lia.
    rewrite (Z.abs_eq (p - 1 - 1)) by lia.
    rewrite (Z.abs_eq (p - 2)) by lia; lia.
  - assert (Hp01 : p = 0 \/ p = 1) by lia.
    destruct Hp01 as [-> | ->].
    + rewrite (Z.abs_neq (0 - 1)) by lia.
      rewrite (Z.abs_eq (- (0 - 1) - 1)) by lia.
      rewrite (Z.abs_neq (0 - 2)) by lia; lia.
    + rewrite (Z.abs_eq (1 - 1)) by lia.
      rewrite (Z.abs_neq (1 - 1 - 1)) by lia.
      rewrite (Z.abs_neq (1 - 2)) by lia; lia.
Qed.

Lemma abs_two_steps_eq :
  forall p, 1 <= p -> Z.abs (Z.abs (p - 1) - 1) = Z.abs (p - 2).
Proof.
  intros p Hp; rewrite (Z.abs_eq (p - 1)) by lia.
  destruct (Z.le_gt_cases 2 p) as [H2 | H2].
  - rewrite (Z.abs_eq (p - 1 - 1)) by lia.
    rewrite (Z.abs_eq (p - 2)) by lia; lia.
  - assert (Hp1 : p = 1) by lia; subst.
    rewrite (Z.abs_neq (1 - 1 - 1)) by lia.
    rewrite (Z.abs_neq (1 - 2)) by lia; lia.
Qed.

(** * The two-box fold, where the collapse needs it *)

Lemma g_0b_big :
  forall b w, 2 * Z.of_nat b <= w -> g 0 b w = w - 2 * Z.of_nat b.
Proof.
  induction b as [|b IH]; intros w Hw.
  - rewrite g_00; cbn [Z.of_nat]; lia.
  - rewrite g_0b, (IH w) by lia.
    rewrite Nat2Z.inj_succ, Z.abs_eq by lia; lia.
Qed.

Lemma g_0b_small :
  forall b w, 0 <= w -> w <= 2 * Z.of_nat b -> g 0 b w <= 2.
Proof.
  induction b as [|b IH]; intros w Hw Hb.
  - cbn [Z.of_nat] in Hb; assert (w = 0) by lia; subst.
    rewrite g_00; lia.
  - rewrite g_0b, Nat2Z.inj_succ in *.
    destruct (Z.le_gt_cases w (2 * Z.of_nat b)) as [H | H].
    + pose proof (IH w Hw H) as Hle.
      pose proof (g_nonneg 0 b w Hw) as Hge; lia.
    + rewrite (g_0b_big b w) by lia; lia.
Qed.

(** Below its reach the two-box fold is one on odd arguments, since it is at
    most two and carries the parity of what it started from. *)
Lemma g_0b_odd :
  forall b w,
    0 <= w -> w <= 2 * Z.of_nat b -> Z.even w = false -> g 0 b w = 1.
Proof.
  intros b w Hw Hb Ho.
  pose proof (g_0b_small b w Hw Hb) as Hle.
  pose proof (g_nonneg 0 b w Hw) as Hge.
  pose proof (g_parity 0 b w) as Hp.
  cbn [Z.of_nat] in Hp; rewrite Z.add_0_r, Ho in Hp.
  assert (Hne0 : g 0 b w <> 0) by (intros E; rewrite E in Hp; discriminate).
  assert (Hne2 : g 0 b w <> 2) by (intros E; rewrite E in Hp; discriminate).
  lia.
Qed.

Lemma h1_zero_even :
  forall m w, 0 <= m -> 0 <= w -> h1 m w = 0 -> Z.even (m - w) = true.
Proof.
  intros m w Hm Hw H; unfold h1 in H.
  destruct (m <=? w) eqn:E.
  - apply Z.leb_le in E; assert (Hwm : w = m) by lia.
    rewrite Hwm; replace (m - m) with 0 by lia; reflexivity.
  - destruct (Z.even (m - w)) eqn:Ev; [reflexivity | discriminate].
Qed.

(** * The collapse *)

(** With a one-box chain present, every two-box chain is worth two one-box
    steps: the interleaving that alternates never loses, and the two-box step
    is only ever as good. *)
Theorem g_collapse :
  forall a b w,
    (1 <= a)%nat -> 0 <= w ->
    g a b w = h1 (Z.of_nat a + 2 * Z.of_nat b) w.
Proof.
  assert (Haux : forall n a b w, (a + b <= n)%nat -> (1 <= a)%nat -> 0 <= w ->
                   g a b w = h1 (Z.of_nat a + 2 * Z.of_nat b) w).
  { induction n as [|n IH]; intros a b w Hn Ha Hw; [lia|].
    destruct a as [|a']; [lia|].
    destruct b as [|b'].
    - rewrite (g_a0_closed (S a') w Hw); f_equal; lia.
    - rewrite g_ab.
      set (m2 := Z.of_nat (S a') + 2 * Z.of_nat b').
      assert (Hm2 : 0 <= m2) by (unfold m2; lia).
      assert (IH2 : g (S a') b' w = h1 m2 w) by (apply IH; lia).
      assert (Htgt : Z.of_nat (S a') + 2 * Z.of_nat (S b') = m2 + 2)
        by (unfold m2; lia).
      assert (Hstep2 : h1 (m2 + 2) w = Z.abs (Z.abs (h1 m2 w - 1) - 1)).
      { replace (m2 + 2) with ((m2 + 1) + 1) by lia.
        rewrite (h1_step (m2 + 1) w) by lia.
        rewrite (h1_step m2 w) by lia; reflexivity. }
      assert (Hp0 : 0 <= h1 m2 w) by (apply h1_nonneg; lia).
      assert (Hle2 : h1 (m2 + 2) w <= Z.abs (h1 m2 w - 2))
        by (rewrite Hstep2; apply abs_two_steps; exact Hp0).
      rewrite Htgt, IH2.
      destruct a' as [|a''].
      + (* exactly one one-box chain: the first branch is the two-box fold *)
        assert (Hm2v : m2 = 1 + 2 * Z.of_nat b') by (unfold m2; lia).
        destruct (Z.le_gt_cases (m2 + 2) w) as [Hbig | Hsmall].
        * (* beyond the reach: both branches agree with the target *)
          rewrite (g_0b_big (S b') w) by (rewrite Nat2Z.inj_succ; lia).
          assert (Hh : h1 (m2 + 2) w = w - (m2 + 2))
            by (unfold h1; rewrite (proj2 (Z.leb_le (m2 + 2) w)) by lia; lia).
          assert (Hh2 : h1 m2 w = w - m2)
            by (unfold h1; rewrite (proj2 (Z.leb_le m2 w)) by lia; lia).
          rewrite Hh, Hh2, Nat2Z.inj_succ.
          rewrite (Z.abs_eq (w - 2 * Z.succ (Z.of_nat b') - 1)) by lia.
          rewrite (Z.abs_eq (w - m2 - 2)) by lia.
          replace (w - 2 * Z.succ (Z.of_nat b') - 1) with (w - (m2 + 2)) by lia.
          replace (w - m2 - 2) with (w - (m2 + 2)) by lia.
          apply Z.min_id.
        * destruct (Z.eq_dec (h1 m2 w) 0) as [Hz | Hnz].
          -- (* the two-box step overshoots, so the one-box chain is taken *)
             assert (Hev : Z.even (m2 - w) = true)
               by (apply h1_zero_even; lia).
             assert (Hodd : Z.even w = false).
             { rewrite Z.even_sub, Hm2v in Hev.
               replace (1 + 2 * Z.of_nat b') with (2 * Z.of_nat b' + 1) in Hev
                 by lia.
               rewrite even_add1 in Hev.
               replace (Z.even (2 * Z.of_nat b')) with true in Hev
                 by (rewrite Z.even_mul; reflexivity).
               cbn [negb] in Hev.
               destruct (Z.even w); [discriminate | reflexivity]. }
             assert (Hbnd : w <= 2 * Z.of_nat (S b'))
               by (rewrite Nat2Z.inj_succ; lia).
             rewrite (g_0b_odd (S b') w Hw Hbnd Hodd).
             rewrite Hz, Hstep2, Hz.
             rewrite (Z.abs_neq (0 - 1)) by lia.
             rewrite (Z.abs_eq (- (0 - 1) - 1)) by lia.
             rewrite (Z.abs_eq (1 - 1)) by lia.
             rewrite (Z.abs_neq (0 - 2)) by lia; reflexivity.
          -- (* otherwise the two branches agree *)
             assert (Heq : Z.abs (h1 m2 w - 2) = h1 (m2 + 2) w)
               by (rewrite Hstep2; symmetry; apply abs_two_steps_eq; lia).
             rewrite Heq; apply Z.min_r.
             (* the target never exceeds the one-box branch *)
             assert (Hq : 0 <= g 0 (S b') w) by (apply g_nonneg; lia).
             assert (Hpar : Z.even (g 0 (S b') w) = Z.even w)
               by (pose proof (g_parity 0 (S b') w) as Hg;
                   cbn [Z.of_nat] in Hg; rewrite Z.add_0_r in Hg; exact Hg).
             assert (Ht01 : h1 (m2 + 2) w = 0 \/ h1 (m2 + 2) w = 1).
             { unfold h1; rewrite (proj2 (Z.leb_gt (m2 + 2) w)) by lia.
               destruct (Z.even (m2 + 2 - w)); [left | right]; reflexivity. }
             destruct Ht01 as [-> | Ht1]; [apply Z.abs_nonneg|].
             rewrite Ht1.
             (* the target is one only when the board is even, and then the
                one-box branch cannot vanish *)
             assert (Hwe : Z.even w = true).
             { unfold h1 in Ht1.
               rewrite (proj2 (Z.leb_gt (m2 + 2) w)) in Ht1 by lia.
               destruct (Z.even (m2 + 2 - w)) eqn:E; [discriminate|].
               assert (Hm2odd : Z.even m2 = false).
               { rewrite Hm2v.
                 replace (1 + 2 * Z.of_nat b') with (2 * Z.of_nat b' + 1)
                   by lia.
                 rewrite even_add1.
                 replace (Z.even (2 * Z.of_nat b')) with true
                   by (rewrite Z.even_mul; reflexivity).
                 reflexivity. }
               rewrite Z.even_sub, even_add2, Hm2odd in E.
               destruct (Z.even w); [reflexivity | discriminate]. }
             assert (Hne1 : g 0 (S b') w <> 1).
             { intros E; rewrite E in Hpar; rewrite Hwe in Hpar; discriminate. }
             assert (H01 : 1 <= Z.abs (g 0 (S b') w - 1)).
             { destruct (Z.abs_spec (g 0 (S b') w - 1)) as [[Hs ->] | [Hs ->]];
                 lia. }
             exact H01.
      + (* at least two one-box chains: the first branch is one step short *)
        assert (IH1 : g (S a'') (S b') w
                      = h1 (Z.of_nat (S a'') + 2 * Z.of_nat (S b')) w)
          by (apply IH; lia).
        assert (Hidx : Z.of_nat (S a'') + 2 * Z.of_nat (S b') = m2 + 1)
          by (unfold m2; lia).
        rewrite IH1, Hidx.
        assert (Hfirst : Z.abs (h1 (m2 + 1) w - 1) = h1 (m2 + 2) w).
        { replace (m2 + 2) with ((m2 + 1) + 1) by lia.
          rewrite (h1_step (m2 + 1) w) by lia; reflexivity. }
        rewrite Hfirst; apply Z.min_l; exact Hle2. }
  intros a b w Ha Hw; exact (Haux (a + b)%nat a b w (Nat.le_refl _) Ha Hw).
Qed.

(** * What the one-box fold gives the decomposition *)

Corollary g_a0_mono :
  forall a x y,
    0 <= x -> x <= y -> Z.even x = Z.even y ->
    g a 0 x <= g a 0 y.
Proof.
  intros a x y Hx Hxy Hp.
  rewrite (g_a0_closed a x Hx), (g_a0_closed a y) by lia.
  apply h1_mono; lia || assumption.
Qed.
