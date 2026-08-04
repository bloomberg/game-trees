(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** The long opening never beats the fold.

    [long_option_ge] is the lower bound the decomposition rests on: opening a
    loony component of the long part is never cheaper than folding the short
    chains onto the long part's own value.

    The two cases are proved differently, and have to be. With a one-box chain
    present the fold collapses onto [ShortFold.h1], which is order preserving
    on arguments of equal parity, so monotonicity and then commutation suffice.
    With only two-box chains the fold is not order preserving and that route is
    unavailable; what closes it instead is [ShortLip.svalue_add_ge], since the
    one configuration that would break the bound needs a four-loop whose
    removal raises the value by more than its own size. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Sorting.Permutation.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.ShortControl.
Require Import GameTrees.ShortPairs.
Require Import GameTrees.ShortSmall.
Require Import GameTrees.ShortExact.
Require Import GameTrees.ShortResidue.
Require Import GameTrees.ShortAll.
Require Import GameTrees.ShortSplit.
Require Import GameTrees.ShortFold.
Require Import GameTrees.ShortCommute.
Require Import GameTrees.ShortLip.

Import ListNotations.

Open Scope Z_scope.

(** * Bookkeeping across a selection *)

Lemma swf_rest :
  forall G C rest, swf G -> In (C, rest) (selections G) -> swf rest.
Proof.
  intros G C rest Hw Hsel.
  pose proof (swf_of_selection G C rest Hw Hsel) as H; inversion H; assumption.
Qed.

Lemma longpart_id : forall G, existsb shortb G = false -> longpart G = G.
Proof.
  induction G as [|C G IH]; intros H; [reflexivity|].
  simpl in H; apply orb_false_iff in H; destruct H as [HC HG].
  rewrite (longpart_long C G HC), (IH HG); reflexivity.
Qed.

Lemma no_short_of_counts :
  forall G, c1 G = 0%nat -> c2 G = 0%nat -> existsb shortb G = false.
Proof.
  intros G H1 H2; apply not_true_is_false; intros Hc.
  apply existsb_exists in Hc; destruct Hc as [C [HinC HCs]].
  destruct (shortb_cases C HCs) as [Hc1 | Hc2].
  - assert (Hin : In C (filter chain1b G))
      by (apply filter_In; split; assumption).
    unfold c1 in H1; destruct (filter chain1b G);
      [contradiction | simpl in H1; lia].
  - assert (Hin : In C (filter chain2b G))
      by (apply filter_In; split; assumption).
    unfold c2 in H2; destruct (filter chain2b G);
      [contradiction | simpl in H2; lia].
Qed.

(** The two branches of the fold, as upper bounds on it. *)
Lemma g_le_branch1 :
  forall a b w, g (S a) b w <= Z.abs (g a b w - 1).
Proof.
  intros a b w; destruct b as [|b'].
  - rewrite g_a0; apply Z.le_refl.
  - rewrite g_ab; apply Z.le_min_l.
Qed.

Lemma g_le_branch2 :
  forall a b w, g a (S b) w <= Z.abs (g a b w - 2).
Proof.
  intros a b w; destruct a as [|a'].
  - rewrite g_0b; apply Z.le_refl.
  - rewrite g_ab; apply Z.le_min_r.
Qed.

(** * A position and its opening share a parity *)

Lemma parity_pair :
  forall C L', Z.even (svalue (C :: L')) = Z.even (svopen C (svalue L')).
Proof.
  intros C L'.
  assert (A : Z.even (svalue (C :: L')) = Z.even (Z.of_nat (size (C :: L'))))
    by apply svalue_parity.
  assert (B : Z.even (svopen C (svalue L'))
              = Z.even (Z.of_nat (csize C) + svalue L'))
    by apply svopen_parity.
  assert (Cc : Z.even (svalue L') = Z.even (Z.of_nat (size L')))
    by apply svalue_parity.
  assert (D : Z.of_nat (size (C :: L'))
              = Z.of_nat (csize C) + Z.of_nat (size L'))
    by (rewrite size_cons; lia).
  rewrite A, B, D, !Z.even_add, Cc; reflexivity.
Qed.

(** * A loony component with no surplus is a four-loop *)

Lemma no_surplus_is_four_loop :
  forall C,
    shortb C = false -> swf_comp C ->
    csize C = shand C -> shand C = 4%nat.
Proof.
  intros [n | n] HC HwC Hu; cbn [swf_comp] in HwC.
  - unfold shortb in HC; apply andb_false_iff in HC.
    assert (Hn3 : (3 <= n)%nat)
      by (destruct HC as [H | H]; apply Nat.leb_gt in H; lia).
    unfold shand, hand in Hu; cbn [csize] in Hu; lia.
  - destruct HwC as [H4 _]; unfold shand, hand in *; cbn [csize] in *; lia.
Qed.

(** * The bound *)

Theorem long_option_ge :
  forall C L' a b,
    shortb C = false -> swf_comp C ->
    g a b (svalue (C :: L')) <= svopen C (g a b (svalue L')).
Proof.
  intros C L' a b HC HwC.
  pose proof (svalue_nonneg L') as Hx.
  pose proof (svalue_nonneg (C :: L')) as Hw.
  pose proof (svalue_le_head C L') as Hle.
  pose proof (svalue_add_ge C L') as Hge.
  pose proof (parity_pair C L') as Hpar.
  pose proof (shand_long_ge2 C HwC HC) as Hk.
  pose proof (shand_le_csize C) as Hkt.
  set (w := svalue (C :: L')) in *.
  set (x := svalue L') in *.
  destruct a as [|a'].
  - (* only two-box chains: no monotonicity available *)
    destruct (Z.le_gt_cases (2 * Z.of_nat b) w) as [Hbig | Hsmall].
    + (* the fold has run out *)
      rewrite (g_0b_big b w Hbig), (svopen_alt C (g 0 b x)).
      rewrite (svopen_alt C x) in Hle.
      destruct (Z.le_gt_cases (2 * Z.of_nat b) x) as [Hx2 | Hx2].
      * rewrite (g_0b_big b x Hx2).
        destruct (Z.abs_spec (x - Z.of_nat (shand C))) as [[? E1] | [? E1]];
          destruct (Z.abs_spec (x - 2 * Z.of_nat b - Z.of_nat (shand C)))
            as [[? E2] | [? E2]]; rewrite E1 in Hle; rewrite E2; lia.
      * assert (Hq2 : g 0 b x <= 2) by (apply g_0b_small; lia).
        assert (Hq0 : 0 <= g 0 b x) by (apply g_nonneg; lia).
        destruct (Z.abs_spec (x - Z.of_nat (shand C))) as [[? E1] | [? E1]];
          destruct (Z.abs_spec (g 0 b x - Z.of_nat (shand C)))
            as [[? E2] | [? E2]]; rewrite E1 in Hle; rewrite E2; lia.
    + (* the fold has not run out: its value is at most two *)
      assert (Hsm : g 0 b w <= 2) by (apply g_0b_small; lia).
      assert (Hsn : 0 <= g 0 b w) by (apply g_nonneg; lia).
      assert (Hq0 : 0 <= g 0 b x) by (apply g_nonneg; lia).
      assert (Hrhs0 : 0 <= svopen C (g 0 b x)) by (apply svopen_nonneg; lia).
      assert (Hp2 : Z.even (g 0 b w) = Z.even (svopen C (g 0 b x))).
      { assert (Q1 : Z.even (g 0 b w) = Z.even w)
          by (rewrite (g_parity 0 b w); f_equal; cbn [Z.of_nat]; lia).
        assert (Q2 : Z.even (g 0 b x) = Z.even x)
          by (rewrite (g_parity 0 b x); f_equal; cbn [Z.of_nat]; lia).
        rewrite Q1, Hpar, (svopen_parity C x), (svopen_parity C (g 0 b x)).
        rewrite !Z.even_add, Q2; reflexivity. }
      destruct (Z.eq_dec (g 0 b w) 2) as [H2 | Hne2].
      * rewrite H2 in Hp2 |- *.
        assert (Hrne : svopen C (g 0 b x) <> 0).
        { intros Hz; rewrite (svopen_alt C (g 0 b x)) in Hz.
          pose proof (Z.abs_nonneg (g 0 b x - Z.of_nat (shand C))) as Hab.
          assert (Hu0 : csize C = shand C) by lia.
          assert (Hqk : g 0 b x = Z.of_nat (shand C)).
          { destruct (Z.abs_spec (g 0 b x - Z.of_nat (shand C)))
              as [[? E] | [? E]]; rewrite E in Hz; lia. }
          pose proof (no_surplus_is_four_loop C HC HwC Hu0) as Hk4.
          (* the fold on the remainder has run out, forcing its value up *)
          assert (Hxbig : 2 * Z.of_nat b <= x).
          { destruct (Z.le_gt_cases (2 * Z.of_nat b) x) as [H | H]; [lia|].
            assert (Hs2 : g 0 b x <= 2) by (apply g_0b_small; lia); lia. }
          rewrite (g_0b_big b x Hxbig) in Hqk.
          (* so the remainder exceeds the whole by more than the component *)
          lia. }
        assert (He : Z.even (svopen C (g 0 b x)) = true)
          by (rewrite <- Hp2; reflexivity).
        assert (Hne1 : svopen C (g 0 b x) <> 1)
          by (intros E; rewrite E in He; discriminate).
        lia.
      * destruct (Z.eq_dec (g 0 b w) 0) as [H0 | Hne0]; [lia|].
        assert (H1 : g 0 b w = 1) by lia.
        rewrite H1 in Hp2 |- *.
        assert (Ho : Z.even (svopen C (g 0 b x)) = false)
          by (rewrite <- Hp2; reflexivity).
        assert (Hz0 : svopen C (g 0 b x) <> 0)
          by (intros E; rewrite E in Ho; discriminate).
        lia.
  - (* a one-box chain is present: the fold collapses and is monotone *)
    assert (Hs : 0 <= svopen C x) by (apply svopen_nonneg; exact Hx).
    assert (Hmono : g (S a') b w <= g (S a') b (svopen C x)).
    { rewrite (g_collapse (S a') b w) by lia.
      rewrite (g_collapse (S a') b (svopen C x)) by lia.
      apply h1_mono; [lia | exact Hw | exact Hle | exact Hpar]. }
    eapply Z.le_trans; [exact Hmono|].
    apply g_commute; assumption.
Qed.

(** * The decomposition *)

(** The short chains separate from the loony endgame: the value is the fold of
    the chains of one and two boxes onto the value of everything else. *)
Theorem svalue_split :
  forall G, swf G -> svalue G = g (c1 G) (c2 G) (svalue (longpart G)).
Proof.
  assert (Haux : forall n G, (length G <= n)%nat -> swf G ->
                   svalue G = g (c1 G) (c2 G) (svalue (longpart G))).
  { induction n as [|n IH]; intros G Hn Hw.
    - assert (HG : G = []) by (destruct G; simpl in Hn; [reflexivity | lia]).
      subst G; reflexivity.
    - (* the recursive value of any remainder *)
      assert (Hstep : forall C rest, In (C, rest) (selections G) ->
                svalue rest = g (c1 rest) (c2 rest) (svalue (longpart rest))).
      { intros C rest Hsel.
        pose proof (selections_length G (C, rest) Hsel) as Hl; simpl in Hl.
        apply IH; [lia | exact (swf_rest G C rest Hw Hsel)]. }
      (* opening a short chain leaves the long part alone *)
      assert (Hshort : forall C rest, In (C, rest) (selections G) ->
                shortb C = true ->
                svalue rest = g (c1 rest) (c2 rest) (svalue (longpart G))).
      { intros C rest Hsel HCs.
        rewrite (Hstep C rest Hsel); f_equal.
        pose proof (selections_perm G (C, rest) Hsel) as Hp; simpl in Hp.
        pose proof (longpart_perm _ _ Hp) as Hlp.
        rewrite (longpart_short C rest HCs) in Hlp.
        apply svalue_perm; exact Hlp. }
      assert (Hcnt1 : forall C rest, In (C, rest) (selections G) ->
                c1 G = ((if chain1b C then 1 else 0) + c1 rest)%nat).
      { intros C rest Hsel.
        pose proof (selections_perm G (C, rest) Hsel) as Hp; simpl in Hp.
        rewrite <- (c1_perm _ _ Hp), c1_cons; reflexivity. }
      assert (Hcnt2 : forall C rest, In (C, rest) (selections G) ->
                c2 G = ((if chain2b C then 1 else 0) + c2 rest)%nat).
      { intros C rest Hsel.
        pose proof (selections_perm G (C, rest) Hsel) as Hp; simpl in Hp.
        rewrite <- (c2_perm _ _ Hp), c2_cons; reflexivity. }
      (* every one-box option realises the first branch *)
      assert (Hopt1 : (1 <= c1 G)%nat ->
                svalue G <= Z.abs (g (pred (c1 G)) (c2 G)
                                     (svalue (longpart G)) - 1)).
      { intros Ha; destruct (c1_pos_ex G Ha) as [C [HinC HCs]].
        assert (HCsh : shortb C = true) by (apply chain1b_shortb; exact HCs).
        destruct (In_selections G C HinC) as [rest Hsel].
        pose proof (svalue_le_open G (C, rest) Hsel) as Hle.
        unfold svalue_open in Hle; cbn [fst snd] in Hle.
        rewrite (svopen_short C (svalue rest) HCsh) in Hle.
        rewrite (csize_chain1b C HCs) in Hle.
        rewrite (Hshort C rest Hsel HCsh) in Hle.
        pose proof (Hcnt1 C rest Hsel) as E1.
        pose proof (Hcnt2 C rest Hsel) as E2.
        rewrite HCs in E1; rewrite (chain1b_chain2b C HCs) in E2.
        assert (Er1 : c1 rest = pred (c1 G)) by lia.
        assert (Er2 : c2 rest = c2 G) by lia.
        rewrite Er1, Er2 in Hle; exact Hle. }
      (* and every two-box option the second *)
      assert (Hopt2 : (1 <= c2 G)%nat ->
                svalue G <= Z.abs (g (c1 G) (pred (c2 G))
                                     (svalue (longpart G)) - 2)).
      { intros Hb; destruct (c2_pos_ex G Hb) as [C [HinC HCs]].
        assert (HCsh : shortb C = true) by (apply chain2b_shortb; exact HCs).
        assert (HC1 : chain1b C = false).
        { destruct (chain1b C) eqn:E; [|reflexivity].
          rewrite (chain1b_chain2b C E) in HCs; discriminate. }
        destruct (In_selections G C HinC) as [rest Hsel].
        pose proof (svalue_le_open G (C, rest) Hsel) as Hle.
        unfold svalue_open in Hle; cbn [fst snd] in Hle.
        rewrite (svopen_short C (svalue rest) HCsh) in Hle.
        rewrite (csize_chain2b C HCs) in Hle.
        rewrite (Hshort C rest Hsel HCsh) in Hle.
        pose proof (Hcnt1 C rest Hsel) as E1.
        pose proof (Hcnt2 C rest Hsel) as E2.
        rewrite HC1 in E1; rewrite HCs in E2.
        assert (Er1 : c1 rest = c1 G) by lia.
        assert (Er2 : c2 rest = pred (c2 G)) by lia.
        rewrite Er1, Er2 in Hle; exact Hle. }
      apply Z.le_antisymm.
      + (* the fold is attainable *)
        destruct (c1 G) as [|a'] eqn:Ea; destruct (c2 G) as [|b'] eqn:Eb.
        * rewrite g_00, (longpart_id G (no_short_of_counts G Ea Eb)).
          apply Z.le_refl.
        * rewrite g_0b; apply Hopt2; lia.
        * rewrite g_a0; apply Hopt1; lia.
        * rewrite g_ab; apply Z.min_glb; [apply Hopt1 | apply Hopt2]; lia.
      + (* no option beats it *)
        destruct (list_eq_dec comp_eq_dec G []) as [-> | HNil].
        { simpl in Hn; apply Z.le_refl. }
        destruct (svalue_attained G HNil) as [p [Hp Hval]].
        destruct p as [C rest]; rewrite Hval.
        unfold svalue_open; cbn [fst snd].
        pose proof (Hcnt1 C rest Hp) as E1.
        pose proof (Hcnt2 C rest Hp) as E2.
        destruct (shortb C) eqn:HCsh.
        * (* a short chain was opened *)
          rewrite (svopen_short C (svalue rest) HCsh).
          rewrite (Hshort C rest Hp HCsh).
          destruct (shortb_cases C HCsh) as [HC1 | HC2].
          -- rewrite HC1 in E1; rewrite (chain1b_chain2b C HC1) in E2.
             rewrite (csize_chain1b C HC1).
             assert (Ha : c1 G = S (c1 rest)) by lia.
             assert (Hb : c2 G = c2 rest) by lia.
             rewrite Ha, Hb; apply g_le_branch1.
          -- assert (HC1 : chain1b C = false).
             { destruct (chain1b C) eqn:E; [|reflexivity].
               rewrite (chain1b_chain2b C E) in HC2; discriminate. }
             rewrite HC1 in E1; rewrite HC2 in E2.
             rewrite (csize_chain2b C HC2).
             assert (Ha : c1 G = c1 rest) by lia.
             assert (Hb : c2 G = S (c2 rest)) by lia.
             rewrite Ha, Hb; apply g_le_branch2.
        * (* a loony component was opened *)
          assert (HC1 : chain1b C = false).
          { destruct (chain1b C) eqn:E; [|reflexivity].
            rewrite (chain1b_shortb C E) in HCsh; discriminate. }
          assert (HC2 : chain2b C = false).
          { destruct (chain2b C) eqn:E; [|reflexivity].
            rewrite (chain2b_shortb C E) in HCsh; discriminate. }
          rewrite HC1 in E1; rewrite HC2 in E2.
          assert (Ha : c1 G = c1 rest) by lia.
          assert (Hb : c2 G = c2 rest) by lia.
          rewrite (Hstep C rest Hp), Ha, Hb.
          assert (HwC : swf_comp C).
          { pose proof (swf_of_selection G C rest Hw Hp) as Hs.
            inversion Hs; assumption. }
          assert (Hlp : svalue (longpart G) = svalue (C :: longpart rest)).
          { pose proof (selections_perm G (C, rest) Hp) as Hq; simpl in Hq.
            pose proof (longpart_perm _ _ Hq) as Hlq.
            rewrite (longpart_long C rest HCsh) in Hlq.
            symmetry; apply svalue_perm; exact Hlq. }
          rewrite Hlp; apply long_option_ge; assumption. }
  intros G Hw; exact (Haux (length G) G (Nat.le_refl _) Hw).
Qed.
