(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Splitting the short chains off the loony endgame.

    Opening a chain of one or two boxes is not a loony move, which is why
    [DotsAndBoxes.wf_comp] demands three boxes of a chain in the first place.
    The short chains therefore separate from the rest of the position: the
    value is obtained by folding them onto the value of what remains.

    [svopen_exchange] is the exchange step that separation rests on. Opening a
    short chain ahead of a long component is never worse than the other order.
    It fails between two short chains, where [Chain 2] ahead of [Chain 1] loses
    two boxes, so the fold below minimises over the interleavings rather than
    fixing an order.

    [longpart] and [g] are the two halves of the split: the components that
    remain loony, and the fold that puts the short ones back. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Sorting.Permutation.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.ShortControl.
Require Import GameTrees.ShortSmall.
Require Import GameTrees.ShortExact.
Require Import GameTrees.ShortAll.

Import ListNotations.

Open Scope Z_scope.

(** * An opening, measured from its handout *)

(** Every opening is the component's surplus over its handout, plus the
    distance from the handout to what is left behind. *)
Lemma svopen_alt :
  forall C x,
    svopen C x
    = Z.of_nat (csize C) - Z.of_nat (shand C)
      + Z.abs (x - Z.of_nat (shand C)).
Proof.
  intros C x; unfold svopen.
  destruct (Z.le_gt_cases x (Z.of_nat (shand C))) as [H | H].
  - rewrite (Z.abs_neq (x - Z.of_nat (shand C))) by lia.
    rewrite Z.max_l by lia; lia.
  - rewrite (Z.abs_eq (x - Z.of_nat (shand C))) by lia.
    rewrite Z.max_r by lia; lia.
Qed.

Lemma svopen_short_alt :
  forall C x, shortb C = true -> svopen C x = Z.abs (x - Z.of_nat (csize C)).
Proof. intros C x H; apply svopen_short; exact H. Qed.

(** A short chain hands over everything it has. *)
Lemma shand_short_eq :
  forall C, shortb C = true -> shand C = csize C.
Proof.
  intros [n | n] H; [|discriminate].
  pose proof (shortb_chain n H) as Hb.
  unfold shand, hand; cbn [csize]; lia.
Qed.

(** A component that is not short hands over two boxes or four. *)
Lemma shand_long_ge2 :
  forall C, swf_comp C -> shortb C = false -> (2 <= shand C)%nat.
Proof.
  intros [n | n] Hw Hs; cbn [swf_comp] in Hw.
  - unfold shortb in Hs; apply andb_false_iff in Hs.
    assert (Hn : (3 <= n)%nat).
    { destruct Hs as [H | H]; apply Nat.leb_gt in H; lia. }
    unfold shand, hand; cbn [csize]; lia.
  - destruct Hw as [H4 _]; unfold shand, hand; cbn [csize]; lia.
Qed.

(** * The exchange inequality, in arithmetic *)

Lemma abs_exchange :
  forall u s k y,
    0 <= u -> 0 <= s -> s <= k -> 0 <= y ->
    Z.abs (u + Z.abs (y - k) - s) <= u + Z.abs (Z.abs (y - s) - k).
Proof.
  intros u s k y Hu Hs0 Hsk Hy.
  destruct (Z.le_gt_cases y k) as [H1 | H1].
  - rewrite (Z.abs_neq (y - k)) by lia.
    destruct (Z.le_gt_cases y s) as [H2 | H2].
    + rewrite (Z.abs_neq (y - s)) by lia.
      rewrite (Z.abs_neq (- (y - s) - k)) by lia.
      apply (proj2 (Z.abs_le _ _)); lia.
    + rewrite (Z.abs_eq (y - s)) by lia.
      rewrite (Z.abs_neq (y - s - k)) by lia.
      apply (proj2 (Z.abs_le _ _)); lia.
  - rewrite (Z.abs_eq (y - k)) by lia.
    rewrite (Z.abs_eq (y - s)) by lia.
    destruct (Z.le_gt_cases 0 (y - s - k)) as [H3 | H3].
    + rewrite (Z.abs_eq (y - s - k)) by lia.
      apply (proj2 (Z.abs_le _ _)); lia.
    + rewrite (Z.abs_neq (y - s - k)) by lia.
      apply (proj2 (Z.abs_le _ _)); lia.
Qed.

(** * The exchange inequality, on openings *)

(** Opening a short chain ahead of a long component is never worse. *)
Theorem svopen_exchange :
  forall S L y,
    shortb S = true -> shortb L = false -> swf_comp L -> 0 <= y ->
    svopen S (svopen L y) <= svopen L (svopen S y).
Proof.
  intros S L y HS HL HwL Hy.
  rewrite (svopen_alt L y), (svopen_short_alt S _ HS).
  rewrite (svopen_short_alt S y HS), (svopen_alt L _).
  rewrite <- (shand_short_eq S HS).
  pose proof (shand_short_le2 S HS) as Hs2.
  pose proof (shand_long_ge2 L HwL HL) as Hk2.
  pose proof (shand_le_csize L) as Hu.
  apply abs_exchange; lia.
Qed.

(** The exchange genuinely needs the second component to be long: two short
    chains do not commute, and the two-box chain must not go first. *)
Example exchange_needs_long :
  svopen (Chain 2) (svopen (Chain 1) 1) = 2
  /\ svopen (Chain 1) (svopen (Chain 2) 1) = 0.
Proof. split; reflexivity. Qed.

(** * The long part *)

Definition longpart (G : position) : position :=
  filter (fun C => negb (shortb C)) G.

Lemma longpart_short :
  forall C G, shortb C = true -> longpart (C :: G) = longpart G.
Proof. intros C G H; unfold longpart; simpl; rewrite H; reflexivity. Qed.

Lemma longpart_long :
  forall C G, shortb C = false -> longpart (C :: G) = C :: longpart G.
Proof. intros C G H; unfold longpart; simpl; rewrite H; reflexivity. Qed.

Lemma longpart_perm :
  forall G H, Permutation G H -> Permutation (longpart G) (longpart H).
Proof.
  intros G H Hp; unfold longpart.
  apply (Permutation_filter (fun C => negb (shortb C))); exact Hp.
Qed.

(** Everything the long part keeps is loony to open, so it is wellformed
    whenever the position it came from was admissible at all. *)
Lemma longpart_wf : forall G, swf G -> wf (longpart G).
Proof.
  intros G Hw; apply swf_no_short_wf.
  - unfold swf, longpart; rewrite Forall_forall; intros D HD.
    apply filter_In in HD; destruct HD as [HD _].
    unfold swf in Hw; rewrite Forall_forall in Hw; apply Hw; exact HD.
  - apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDs]].
    apply filter_In in HD; destruct HD as [_ Hn].
    rewrite HDs in Hn; discriminate.
Qed.

Lemma longpart_all_long :
  forall G, existsb shortb (longpart G) = false.
Proof.
  intros G; apply not_true_is_false; intros Hc.
  apply existsb_exists in Hc; destruct Hc as [D [HD HDs]].
  apply filter_In in HD; destruct HD as [_ Hn].
  rewrite HDs in Hn; discriminate.
Qed.

(** * The fold that puts the short chains back *)

(** One-box chains step by one and two-box chains by two, and the opener takes
    whichever interleaving is cheapest. The fuel is the number of short chains,
    which is what the recursion consumes. *)
Fixpoint gf (n a b : nat) (w : Z) : Z :=
  match n with
  | O => w
  | S n' =>
    match a, b with
    | O, O => w
    | S a', O => Z.abs (gf n' a' O w - 1)
    | O, S b' => Z.abs (gf n' O b' w - 2)
    | S a', S b' =>
        Z.min (Z.abs (gf n' a' (S b') w - 1)) (Z.abs (gf n' (S a') b' w - 2))
    end
  end.

Definition g (a b : nat) (w : Z) : Z := gf (a + b) a b w.

Lemma gf_more :
  forall n m a b w, (a + b <= n)%nat -> (n <= m)%nat -> gf n a b w = gf m a b w.
Proof.
  induction n as [|n IH]; intros m a b w Hn Hm.
  - assert (Ha : a = 0%nat) by lia; assert (Hb : b = 0%nat) by lia; subst.
    destruct m; reflexivity.
  - destruct m as [|m]; [lia|].
    destruct a as [|a']; destruct b as [|b']; cbn [gf].
    + reflexivity.
    + rewrite (IH m 0%nat b' w) by lia; reflexivity.
    + rewrite (IH m a' 0%nat w) by lia; reflexivity.
    + rewrite (IH m a' (S b') w) by lia.
      rewrite (IH m (S a') b' w) by lia; reflexivity.
Qed.

Lemma gf_g : forall n a b w, (a + b <= n)%nat -> gf n a b w = g a b w.
Proof.
  intros n a b w H; unfold g; symmetry; apply gf_more; lia.
Qed.

Lemma g_00 : forall w, g 0 0 w = w.
Proof. intros w; reflexivity. Qed.

Lemma g_a0 : forall a w, g (S a) 0 w = Z.abs (g a 0 w - 1).
Proof.
  intros a w; unfold g at 1.
  replace (S a + 0)%nat with (S (a + 0))%nat by lia; cbn [gf].
  rewrite (gf_g (a + 0) a 0 w) by lia; reflexivity.
Qed.

Lemma g_0b : forall b w, g 0 (S b) w = Z.abs (g 0 b w - 2).
Proof.
  intros b w; unfold g at 1; cbn [Nat.add gf].
  rewrite (gf_g b 0 b w) by lia; reflexivity.
Qed.

Lemma g_ab :
  forall a b w,
    g (S a) (S b) w
    = Z.min (Z.abs (g a (S b) w - 1)) (Z.abs (g (S a) b w - 2)).
Proof.
  intros a b w; unfold g at 1.
  replace (S a + S b)%nat with (S (a + S b))%nat by lia; cbn [gf].
  rewrite (gf_g (a + S b) a (S b) w) by lia.
  rewrite (gf_g (a + S b) (S a) b w) by lia; reflexivity.
Qed.

(** The fold is one-Lipschitz, since every step is. *)
Lemma g_nonneg : forall a b w, 0 <= w -> 0 <= g a b w.
Proof.
  intros a b w Hw; unfold g.
  remember (a + b)%nat as n eqn:En; revert a b w Hw En.
  induction n as [|n IH]; intros a b w Hw En; cbn [gf].
  - destruct a, b; try lia; exact Hw.
  - destruct a as [|a']; destruct b as [|b']; try exact Hw;
      try apply Z.abs_nonneg.
    apply Z.min_glb; apply Z.abs_nonneg.
Qed.
