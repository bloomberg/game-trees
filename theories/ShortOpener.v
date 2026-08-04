(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Which component to open, when a short chain is present.

    Allcock's standard move opens a three-chain if there is one. Below that
    length the same shape holds: on any position holding a chain of one or two
    boxes, one of those chains is an optimal opening.

    It follows from [ShortDecomp.svalue_split]. The value is the short-chain
    fold applied to the loony part, the fold is a minimum over the two kinds of
    short chain, and each of those is realised by opening one. So the minimum
    is attained by a short chain and nothing longer improves on it. *)

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
Require Import GameTrees.ShortSplit.
Require Import GameTrees.ShortFold.
Require Import GameTrees.ShortLip.
Require Import GameTrees.ShortDecomp.

Import ListNotations.

Open Scope Z_scope.

(** * What a short opening is worth *)

Lemma short_option_value :
  forall G C rest,
    swf G -> In (C, rest) (selections G) -> shortb C = true ->
    svalue_open (C, rest)
    = Z.abs (g (c1 rest) (c2 rest) (svalue (longpart G))
             - Z.of_nat (csize C)).
Proof.
  intros G C rest Hw Hsel HCs.
  assert (E : svalue rest = g (c1 rest) (c2 rest) (svalue (longpart G))).
  { rewrite (svalue_split rest (swf_rest G C rest Hw Hsel)); f_equal.
    pose proof (selections_perm G (C, rest) Hsel) as Hp; simpl in Hp.
    pose proof (longpart_perm _ _ Hp) as Hlp.
    rewrite (longpart_short C rest HCs) in Hlp.
    apply svalue_perm; exact Hlp. }
  unfold svalue_open; cbn [fst snd].
  rewrite (svopen_short C (svalue rest) HCs), E; reflexivity.
Qed.

(** * Counts across a short opening *)

Lemma short_counts :
  forall G C rest,
    In (C, rest) (selections G) ->
    c1 G = ((if chain1b C then 1 else 0) + c1 rest)%nat /\
    c2 G = ((if chain2b C then 1 else 0) + c2 rest)%nat.
Proof.
  intros G C rest Hsel.
  pose proof (selections_perm G (C, rest) Hsel) as Hp; simpl in Hp.
  split.
  - rewrite <- (c1_perm _ _ Hp), c1_cons; reflexivity.
  - rewrite <- (c2_perm _ _ Hp), c2_cons; reflexivity.
Qed.

(** * A short chain is an optimal opening *)

Theorem short_opening_optimal :
  forall G,
    swf G -> existsb shortb G = true ->
    exists p, In p (selections G) /\ shortb (fst p) = true
              /\ svalue G = svalue_open p.
Proof.
  intros G Hw Hs.
  set (w := svalue (longpart G)).
  assert (Hval : svalue G = g (c1 G) (c2 G) w) by (apply svalue_split; exact Hw).
  (* a one-box chain, when there is one *)
  assert (Hone : (1 <= c1 G)%nat ->
            exists p, In p (selections G) /\ chain1b (fst p) = true
                      /\ svalue_open p = Z.abs (g (pred (c1 G)) (c2 G) w - 1)).
  { intros Ha; destruct (c1_pos_ex G Ha) as [C [HinC HC]].
    assert (HCs : shortb C = true) by (apply chain1b_shortb; exact HC).
    destruct (In_selections G C HinC) as [rest Hsel].
    destruct (short_counts G C rest Hsel) as [E1 E2].
    rewrite HC in E1; rewrite (chain1b_chain2b C HC) in E2.
    exists (C, rest); repeat split; [exact Hsel | exact HC |].
    rewrite (short_option_value G C rest Hw Hsel HCs).
    rewrite (csize_chain1b C HC).
    replace (pred (c1 G)) with (c1 rest) by lia.
    replace (c2 G) with (c2 rest) by lia; reflexivity. }
  (* a two-box chain, when there is one *)
  assert (Htwo : (1 <= c2 G)%nat ->
            exists p, In p (selections G) /\ chain2b (fst p) = true
                      /\ svalue_open p = Z.abs (g (c1 G) (pred (c2 G)) w - 2)).
  { intros Hb; destruct (c2_pos_ex G Hb) as [C [HinC HC]].
    assert (HCs : shortb C = true) by (apply chain2b_shortb; exact HC).
    assert (HC1 : chain1b C = false).
    { destruct (chain1b C) eqn:E; [|reflexivity].
      rewrite (chain1b_chain2b C E) in HC; discriminate. }
    destruct (In_selections G C HinC) as [rest Hsel].
    destruct (short_counts G C rest Hsel) as [E1 E2].
    rewrite HC1 in E1; rewrite HC in E2.
    exists (C, rest); repeat split; [exact Hsel | exact HC |].
    rewrite (short_option_value G C rest Hw Hsel HCs).
    rewrite (csize_chain2b C HC).
    replace (c1 G) with (c1 rest) by lia.
    replace (pred (c2 G)) with (c2 rest) by lia; reflexivity. }
  (* at least one kind is present *)
  assert (Hpos : (1 <= c1 G)%nat \/ (1 <= c2 G)%nat).
  { destruct (Nat.eq_dec (c1 G) 0) as [Ha | Ha]; [|left; lia].
    destruct (Nat.eq_dec (c2 G) 0) as [Hb | Hb]; [|right; lia].
    exfalso; rewrite (no_short_of_counts G Ha Hb) in Hs; discriminate. }
  destruct (c1 G) as [|a'] eqn:Ea; destruct (c2 G) as [|b'] eqn:Eb.
  - exfalso; destruct Hpos; lia.
  - destruct (Htwo ltac:(lia)) as [p [Hp [HC Hv]]].
    exists p; repeat split;
      [exact Hp | apply chain2b_shortb; exact HC |].
    rewrite Hval, Hv, g_0b; reflexivity.
  - destruct (Hone ltac:(lia)) as [p [Hp [HC Hv]]].
    exists p; repeat split;
      [exact Hp | apply chain1b_shortb; exact HC |].
    rewrite Hval, Hv, g_a0; reflexivity.
  - destruct (Hone ltac:(lia)) as [p1 [Hp1 [HC1 Hv1]]].
    destruct (Htwo ltac:(lia)) as [p2 [Hp2 [HC2 Hv2]]].
    cbn [pred] in Hv1, Hv2.
    destruct (Z.min_dec (Z.abs (g a' (S b') w - 1))
                        (Z.abs (g (S a') b' w - 2))) as [E | E].
    + exists p1; repeat split;
        [exact Hp1 | apply chain1b_shortb; exact HC1 |].
      rewrite Hval, Hv1, g_ab, E; reflexivity.
    + exists p2; repeat split;
        [exact Hp2 | apply chain2b_shortb; exact HC2 |].
      rewrite Hval, Hv2, g_ab, E; reflexivity.
Qed.

(** * The one-box chain is the branch to take *)

Lemma h1_le1 : forall m w, w <= m -> h1 m w <= 1.
Proof.
  intros m w H; unfold h1.
  destruct (m <=? w) eqn:E; [apply Z.leb_le in E; lia|].
  destruct (Z.even (m - w)); lia.
Qed.

(** The minimum defining the fold is always attained by the one-box step. *)
Theorem g_step1 :
  forall a b w, 0 <= w -> g (S a) b w = Z.abs (g a b w - 1).
Proof.
  intros a b w Hw; destruct b as [|b']; [rewrite g_a0; reflexivity|].
  rewrite g_ab; apply Z.min_l.
  destruct a as [|a'].
  - (* no one-box chain left behind: the two-box fold stays small *)
    assert (Hp : g 1 b' w = h1 (1 + 2 * Z.of_nat b') w).
    { rewrite (g_collapse 1 b' w ltac:(lia) Hw); f_equal; cbn [Z.of_nat]; lia. }
    rewrite Hp.
    destruct (Z.le_gt_cases (2 * Z.of_nat (S b')) w) as [Hbig | Hsm].
    + (* both sides run off the end together *)
      rewrite (g_0b_big (S b') w Hbig).
      assert (Hh : h1 (1 + 2 * Z.of_nat b') w = w - (1 + 2 * Z.of_nat b')).
      { unfold h1; rewrite (proj2 (Z.leb_le (1 + 2 * Z.of_nat b') w))
          by (rewrite Nat2Z.inj_succ in Hbig; lia); lia. }
      rewrite Hh, Nat2Z.inj_succ.
      replace (w - 2 * Z.succ (Z.of_nat b') - 1)
        with (w - (1 + 2 * Z.of_nat b') - 2) by lia.
      apply Z.le_refl.
    + (* the two-box fold is at most two, the one-box side at least one away *)
      assert (Hq2 : g 0 (S b') w <= 2) by (apply g_0b_small; lia).
      assert (Hq0 : 0 <= g 0 (S b') w) by (apply g_nonneg; lia).
      assert (Hp1 : h1 (1 + 2 * Z.of_nat b') w <= 1)
        by (apply h1_le1; rewrite Nat2Z.inj_succ in Hsm; lia).
      assert (Hp0 : 0 <= h1 (1 + 2 * Z.of_nat b') w)
        by (apply h1_nonneg; lia).
      destruct (Z.abs_spec (g 0 (S b') w - 1)) as [[? E1] | [? E1]];
        rewrite E1;
        rewrite (Z.abs_neq (h1 (1 + 2 * Z.of_nat b') w - 2)) by lia; lia.
  - (* a one-box chain remains: both sides collapse onto the same index *)
    assert (H1 : g (S a') (S b') w
                 = h1 (Z.of_nat (S a') + 2 * Z.of_nat (S b')) w)
      by (apply g_collapse; [lia | exact Hw]).
    assert (H2 : g (S (S a')) b' w
                 = h1 (Z.of_nat (S (S a')) + 2 * Z.of_nat b') w)
      by (apply g_collapse; [lia | exact Hw]).
    rewrite H1, H2.
    set (m := Z.of_nat (S a') + 2 * Z.of_nat b').
    assert (E1 : Z.of_nat (S a') + 2 * Z.of_nat (S b') = m + 2)
      by (unfold m; rewrite Nat2Z.inj_succ; lia).
    assert (E2 : Z.of_nat (S (S a')) + 2 * Z.of_nat b' = m + 1)
      by (unfold m; rewrite Nat2Z.inj_succ; lia).
    rewrite E1, E2.
    assert (Hm : 0 <= m) by (unfold m; lia).
    assert (Hstep : h1 (m + 2) w = Z.abs (Z.abs (h1 m w - 1) - 1)).
    { replace (m + 2) with ((m + 1) + 1) by lia.
      rewrite (h1_step (m + 1) w) by lia.
      rewrite (h1_step m w) by lia; reflexivity. }
    replace (Z.abs (h1 (m + 2) w - 1)) with (h1 (m + 3) w).
    2:{ replace (m + 3) with ((m + 2) + 1) by lia.
        rewrite (h1_step (m + 2) w) by lia; reflexivity. }
    assert (Hstep3 : h1 (m + 3) w
                     = Z.abs (Z.abs (h1 (m + 1) w - 1) - 1)).
    { replace (m + 3) with ((m + 2) + 1) by lia.
      rewrite (h1_step (m + 2) w) by lia.
      replace (m + 2) with ((m + 1) + 1) by lia.
      rewrite (h1_step (m + 1) w) by lia; reflexivity. }
    rewrite Hstep3; apply abs_two_steps; apply h1_nonneg; lia.
Qed.

(** * The opener rule, named *)

Lemma chain1b_eq : forall C, chain1b C = true -> C = Chain 1.
Proof. intros [[|[|n]] | n] H; try discriminate; reflexivity. Qed.

Lemma chain2b_eq : forall C, chain2b C = true -> C = Chain 2.
Proof. intros [[|[|[|n]]] | n] H; try discriminate; reflexivity. Qed.

(** A one-box chain is optimal whenever the position holds one. *)
Theorem chain1_opening_optimal :
  forall G,
    swf G -> (1 <= c1 G)%nat ->
    exists rest, In (Chain 1, rest) (selections G)
                 /\ svalue G = svalue_open (Chain 1, rest).
Proof.
  intros G Hw Ha.
  destruct (c1_pos_ex G Ha) as [C [HinC HC]].
  assert (HCe : C = Chain 1) by (apply chain1b_eq; exact HC); subst C.
  assert (HCs : shortb (Chain 1) = true) by reflexivity.
  destruct (In_selections G (Chain 1) HinC) as [rest Hsel].
  exists rest; split; [exact Hsel|].
  destruct (short_counts G (Chain 1) rest Hsel) as [E1 E2].
  cbn [chain1b chain2b] in E1, E2.
  rewrite (short_option_value G (Chain 1) rest Hw Hsel HCs); cbn [csize].
  rewrite (svalue_split G Hw).
  destruct (c1 G) as [|a'] eqn:Ea; [lia|].
  replace (c1 rest) with a' by lia.
  replace (c2 rest) with (c2 G) by lia.
  apply g_step1, svalue_nonneg.
Qed.

(** With none, a two-box chain is. *)
Theorem chain2_opening_optimal :
  forall G,
    swf G -> c1 G = 0%nat -> (1 <= c2 G)%nat ->
    exists rest, In (Chain 2, rest) (selections G)
                 /\ svalue G = svalue_open (Chain 2, rest).
Proof.
  intros G Hw Ha Hb.
  destruct (c2_pos_ex G Hb) as [C [HinC HC]].
  assert (HCe : C = Chain 2) by (apply chain2b_eq; exact HC); subst C.
  assert (HCs : shortb (Chain 2) = true) by reflexivity.
  destruct (In_selections G (Chain 2) HinC) as [rest Hsel].
  exists rest; split; [exact Hsel|].
  destruct (short_counts G (Chain 2) rest Hsel) as [E1 E2].
  cbn [chain1b chain2b] in E1, E2.
  rewrite (short_option_value G (Chain 2) rest Hw Hsel HCs); cbn [csize].
  rewrite (svalue_split G Hw).
  destruct (c2 G) as [|b'] eqn:Eb; [lia|].
  replace (c1 rest) with 0%nat by lia.
  replace (c2 rest) with b' by lia.
  rewrite Ha, g_0b; reflexivity.
Qed.

(** So the rule is: open a one-box chain if there is one, otherwise a two-box
    chain. This is the short-chain counterpart of Allcock's standard move,
    which opens a three-chain if there is one. *)
Theorem short_opener_rule :
  forall G,
    swf G -> existsb shortb G = true ->
    (exists rest, In (Chain 1, rest) (selections G)
                  /\ svalue G = svalue_open (Chain 1, rest))
    \/ (c1 G = 0%nat /\
        exists rest, In (Chain 2, rest) (selections G)
                     /\ svalue G = svalue_open (Chain 2, rest)).
Proof.
  intros G Hw Hs.
  destruct (Nat.eq_dec (c1 G) 0) as [Ha | Ha].
  - right; split; [exact Ha|].
    apply chain2_opening_optimal; [exact Hw | exact Ha |].
    destruct (Nat.eq_dec (c2 G) 0) as [Hb | Hb]; [|lia].
    exfalso; rewrite (no_short_of_counts G Ha Hb) in Hs; discriminate.
  - left; apply chain1_opening_optimal; [exact Hw | lia].
Qed.
