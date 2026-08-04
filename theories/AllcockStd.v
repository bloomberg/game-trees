(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Allcock's Theorem 1.1: the standard move.

    Outside the three named cases the strategy opens a three-chain if there is
    one, otherwise a shortest loop, otherwise a shortest chain.

    [DotsAndBoxes.open_optimal_of_cval] already says when an opening is
    optimal: the terminal bonus survives it, what is left is worth at least the
    handout given away, and what is left is above the threshold.
    [standard_move_optimal_of_criterion] is that criterion applied to the
    standard move, whichever of the three components it names.

    [value_of_min_option] is the small step the criterion leaves out: a legal
    opening that no other opening beats is the value. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.Shortest.
Require Import GameTrees.AllcockI.
Require Import GameTrees.Only34.
From Stdlib Require Import Sorting.Permutation.

Import ListNotations.

Open Scope Z_scope.

(** * A minimal opening is the value *)

Lemma value_of_min_option :
  forall G p,
    In p (selections G) ->
    (forall q, In q (selections G) -> value_open p <= value_open q) ->
    value G = value_open p.
Proof.
  intros G p Hp Hmin.
  apply Z.le_antisymm; [apply value_le_open; exact Hp|].
  assert (HNil : G <> []) by (intros ->; simpl in Hp; destruct Hp).
  destruct (value_attained G HNil) as [q [Hq Hv]].
  rewrite Hv; apply Hmin; exact Hq.
Qed.

(** * The criterion, applied to the standard move *)

Theorem standard_move_optimal_of_criterion :
  forall G p,
    wf G -> standard_move G = Some p ->
    tb (fst p :: snd p) = tb (snd p) ->
    Z.of_nat (hand (fst p)) <= cval (snd p) ->
    2 <= cval (snd p) ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hm Htb Hh Hc.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  destruct (open_optimal_of_cval G p Hw Hin Htb Hh Hc) as [_ Hmin].
  split; [apply value_of_min_option; assumption | exact Hmin].
Qed.

(** * Where a three-chain remains, the bonus looks after itself *)

(** Opening one three-chain out of several leaves the terminal bonus alone, so
    only the threshold has to be checked. *)
Theorem standard_move_3chain_optimal :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p ->
    existsb is_3chain_b (snd p) = true ->
    2 <= cval (snd p) ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm H3r Hc.
  assert (Hp3 : fst p = Chain 3)
    by (apply (standard_move_three G p H3); exact Hm).
  apply (standard_move_optimal_of_criterion G p Hw Hm).
  - rewrite Hp3; apply tb_cons_3chain_with3; exact H3r.
  - rewrite Hp3; cbn [hand]; lia.
  - exact Hc.
Qed.

(** * The threshold, from the position rather than the remainder *)

(** Removing a three-chain raises the controlled value by exactly one, since
    the chain weighs minus one and the bonus is unmoved. So the remainder
    clears the threshold as soon as the position itself reaches one. *)
Theorem standard_move_3chain_ge1 :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p ->
    existsb is_3chain_b (snd p) = true ->
    1 <= cval G ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm H3r Hcv.
  assert (Hp3 : fst p = Chain 3)
    by (apply (standard_move_three G p H3); exact Hm).
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  pose proof (selections_perm G p Hin) as Hperm.
  assert (Htb : tb (fst p :: snd p) = tb (snd p))
    by (rewrite Hp3; apply tb_cons_3chain_with3; exact H3r).
  assert (Hcr : cval (snd p) = cval G + 1).
  { rewrite <- (cval_perm _ _ Hperm).
    unfold cval; rewrite cbase_cons, Htb, Hp3, weight_chain; cbn [Z.of_nat].
    unfold cval; lia. }
  apply (standard_move_3chain_optimal G p Hw H3 Hm H3r); lia.
Qed.

(** * When opening a three-chain leaves the bonus alone *)

(** The bonus can only move if what remains is loops and nothing else: in every
    other shape the three-chain neither creates nor destroys the conditions the
    bonus is read from. This is weaker than asking a second three-chain to
    remain, and covers the positions where the only three-chain is opened. *)
Theorem tb_cons_3chain_not_all_loops :
  forall rest,
    forallb is_loop_b rest = false -> tb (Chain 3 :: rest) = tb rest.
Proof.
  intros rest H.
  destruct rest as [|D rest']; [discriminate|].
  rewrite (tb_cons_form (Chain 3) (D :: rest')).
  assert (Hnl : forallb is_loop_b (Chain 3 :: D :: rest') = false)
    by reflexivity.
  rewrite Hnl.
  assert (He : existsb is_loop_b (Chain 3 :: D :: rest')
               = existsb is_loop_b (D :: rest')) by reflexivity.
  assert (Hf : forallb (fun C => (is_loop_b C || is_3chain_b C)%bool)
                 (Chain 3 :: D :: rest')
               = forallb (fun C => (is_loop_b C || is_3chain_b C)%bool)
                   (D :: rest')) by reflexivity.
  rewrite He, Hf.
  rewrite (tb_cons_form D rest'), H; reflexivity.
Qed.

(** * The standard move on a three-chain, in its widest form *)

Theorem standard_move_3chain_stable :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p ->
    forallb is_loop_b (snd p) = false ->
    1 <= cval G ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnl Hcv.
  assert (Hp3 : fst p = Chain 3)
    by (apply (standard_move_three G p H3); exact Hm).
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  pose proof (selections_perm G p Hin) as Hperm.
  assert (Htb : tb (fst p :: snd p) = tb (snd p))
    by (rewrite Hp3; apply tb_cons_3chain_not_all_loops; exact Hnl).
  assert (Hcr : cval (snd p) = cval G + 1).
  { rewrite <- (cval_perm _ _ Hperm).
    unfold cval; rewrite cbase_cons, Htb, Hp3, weight_chain; cbn [Z.of_nat].
    unfold cval; lia. }
  apply (standard_move_optimal_of_criterion G p Hw Hm Htb);
    [rewrite Hp3; cbn [hand]; lia | lia].
Qed.

(** * With no three-chain, the standard move opens a loop *)

Lemma shortest_of_none_of_no_witness :
  forall f G, (forall C, In C G -> f C = false) -> shortest_of f G = None.
Proof.
  intros f G H; unfold shortest_of.
  destruct (filter (fun p => f (fst p)) (selections G)) as [|p l] eqn:E;
    [reflexivity|].
  exfalso.
  assert (Hin : In p (filter (fun q => f (fst q)) (selections G)))
    by (rewrite E; left; reflexivity).
  apply filter_In in Hin; destruct Hin as [Hsel Hf].
  assert (HinG : In (fst p) G) by (apply selections_In; exact Hsel).
  rewrite (H (fst p) HinG) in Hf; discriminate.
Qed.

Lemma no_3chain_of_count0 :
  forall G, count3 G = 0%nat -> forall C, In C G -> is_3chain_b C = false.
Proof.
  intros G H C HC; destruct (is_3chain_b C) eqn:E; [|reflexivity].
  exfalso; unfold count3 in H.
  assert (Hin : In C (filter is_3chain_b G))
    by (apply filter_In; split; assumption).
  destruct (filter is_3chain_b G); [destruct Hin | simpl in H; lia].
Qed.

Lemma standard_move_loop :
  forall G p,
    count3 G = 0%nat -> standard_move G = Some p ->
    is_loop_b (fst p) = true \/ shortest_of is_loop_b G = None.
Proof.
  intros G p H3 Hm; unfold standard_move in Hm.
  rewrite (shortest_of_none_of_no_witness is_3chain_b G
             (no_3chain_of_count0 G H3)) in Hm.
  destruct (shortest_of is_loop_b G) as [q|] eqn:EL; [|right; reflexivity].
  injection Hm as <-; left.
  destruct (shortest_of_min is_loop_b G q EL) as [Hq _]; exact Hq.
Qed.

(** * The standard move on a loop *)

(** With no three-chain anywhere the bonus is unmoved, so only the remainder's
    controlled value has to clear four, and that is a bound on the loop's own
    length against the position. *)
Theorem standard_move_loop_optimal :
  forall G p,
    wf G -> count3 G = 0%nat -> standard_move G = Some p ->
    is_loop_b (fst p) = true -> snd p <> [] ->
    Z.of_nat (csize (fst p)) - 4 <= cval G ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hloop Hnil Hb.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  pose proof (selections_perm G p Hin) as Hperm.
  assert (H3c : existsb is_3chain_b (fst p :: snd p) = false).
  { apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    assert (HDG : In D G) by (apply (Permutation_in _ Hperm); exact HD).
    rewrite (no_3chain_of_count0 G H3 D HDG) in HDf; discriminate. }
  assert (Htb : tb (fst p :: snd p) = tb (snd p))
    by (apply tb_remove_loop_no3; assumption).
  assert (Hcr : cval (snd p) = cval G - Z.of_nat (csize (fst p)) + 8).
  { rewrite <- (cval_perm _ _ Hperm).
    assert (Ew : weight (fst p) = Z.of_nat (csize (fst p)) - 8)
      by (destruct (fst p) as [n | n]; [discriminate Hloop | apply weight_loop]).
    unfold cval; rewrite cbase_cons, Htb, Ew; unfold cval; lia. }
  apply (standard_move_optimal_of_criterion G p Hw Hm Htb).
  - destruct (fst p) as [n | n]; [discriminate Hloop|].
    cbn [hand csize] in *; lia.
  - lia.
Qed.

(** * The standard move on a chain *)

Lemma no_member_of_count0 :
  forall (f : comp -> bool) G,
    length (filter f G) = 0%nat -> forall C, In C G -> f C = false.
Proof.
  intros f G H C HC; destruct (f C) eqn:E; [|reflexivity].
  exfalso.
  assert (Hin : In C (filter f G)) by (apply filter_In; split; assumption).
  destruct (filter f G); [destruct Hin | simpl in H; lia].
Qed.

Lemma cbase_nonneg_of_weights :
  forall G, (forall D, In D G -> 0 <= weight D) -> 0 <= cbase G.
Proof.
  induction G as [|D G IH]; intros Hw; [reflexivity|].
  rewrite cbase_cons.
  pose proof (Hw D (or_introl eq_refl)).
  pose proof (IH (fun E HE => Hw E (or_intror HE))); lia.
Qed.

Lemma cbase_ge_member :
  forall G C,
    In C G -> (forall D, In D G -> 0 <= weight D) -> weight C <= cbase G.
Proof.
  induction G as [|D G IH]; intros C HC Hw; [destruct HC|].
  rewrite cbase_cons; destruct HC as [<- | HC].
  - pose proof (cbase_nonneg_of_weights G (fun E HE => Hw E (or_intror HE)));
      lia.
  - pose proof (IH C HC (fun E HE => Hw E (or_intror HE))).
    pose proof (Hw D (or_introl eq_refl)); lia.
Qed.

(** With neither a three-chain nor a loop every component is a chain of at
    least four boxes, so every weight is nonnegative and the position's
    controlled value already exceeds the chain that is opened. The bonus is
    four on both sides, so the criterion needs nothing further. *)
Theorem standard_move_chain_optimal :
  forall G p,
    wf G -> count3 G = 0%nat -> count_loops G = 0%nat ->
    standard_move G = Some p -> snd p <> [] ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 HL Hm Hnil.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  pose proof (selections_perm G p Hin) as Hperm.
  assert (Hnl : forall C, In C G -> is_loop_b C = false)
    by (apply (no_member_of_count0 is_loop_b G); exact HL).
  assert (Hn3 : forall C, In C G -> is_3chain_b C = false)
    by (apply no_3chain_of_count0; exact H3).
  (* every component is a chain of at least four boxes *)
  assert (Hbig : forall C, In C G -> (4 <= csize C)%nat).
  { intros C HC; pose proof (Hnl C HC) as H1; pose proof (Hn3 C HC) as H2.
    unfold wf in Hw; rewrite Forall_forall in Hw; specialize (Hw C HC).
    destruct C as [n | n]; [|discriminate H1].
    cbn [wf_comp] in Hw; cbn [csize].
    destruct (Nat.eq_dec n 3) as [-> | Hne]; [discriminate H2 | lia]. }
  assert (Hwt : forall D, In D G -> 0 <= weight D).
  { intros D HD; pose proof (Hbig D HD); pose proof (Hnl D HD).
    destruct D as [n | n]; [|discriminate].
    rewrite weight_chain; cbn [csize] in *; lia. }
  (* the bonus is four on both sides *)
  assert (HeG : existsb is_loop_b G = false).
  { apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    rewrite (Hnl D HD) in HDf; discriminate. }
  assert (HeR : existsb is_loop_b (snd p) = false).
  { apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    assert (HDG : In D G)
      by (apply (Permutation_in _ Hperm); right; exact HD).
    rewrite (Hnl D HDG) in HDf; discriminate. }
  assert (HNil : G <> []) by (intros ->; simpl in Hin; destruct Hin).
  assert (HtbG : tb G = 4) by (apply tb_no_loops; assumption).
  assert (HtbR : tb (snd p) = 4) by (apply tb_no_loops; assumption).
  assert (Htb : tb (fst p :: snd p) = tb (snd p)).
  { rewrite HtbR, <- HtbG; apply tb_perm; exact Hperm. }
  (* the controlled value already exceeds the opened chain *)
  assert (HinC : In (fst p) G) by (apply selections_In; exact Hin).
  assert (Hge : weight (fst p) <= cbase G)
    by (apply cbase_ge_member; assumption).
  assert (Hcr : cval (snd p) = cval G - weight (fst p)).
  { rewrite <- (cval_perm _ _ Hperm).
    unfold cval; rewrite cbase_cons, Htb; unfold cval; lia. }
  assert (HcG : cval G = cbase G + 4) by (unfold cval; rewrite HtbG; lia).
  apply (standard_move_optimal_of_criterion G p Hw Hm Htb).
  - assert (Hlp : is_loop_b (fst p) = false) by (apply Hnl; exact HinC).
    assert (Hh : (hand (fst p) = 2)%nat)
      by (destruct (fst p) as [n | n]; [reflexivity | discriminate Hlp]).
    rewrite Hh; cbn [Z.of_nat]; lia.
  - lia.
Qed.

(** * Below the threshold: opening a four-loop *)

(** With no three-chain and the controlled value under two, both the position
    and what a four-loop leaves are read from [DotsAndBoxes.w38], and removing
    the loop shifts the table by exactly the four that
    [DotsAndBoxes.w38_step] records. *)
Theorem standard_move_4loop_below :
  forall G p,
    wf G -> count3 G = 0%nat -> standard_move G = Some p ->
    fst p = Loop 4 -> snd p <> [] ->
    cval G < 2 -> cval (snd p) < 2 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hp4 Hnil HcG Hcr2.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  pose proof (selections_perm G p Hin) as Hperm.
  assert (HNil : G <> []) by (intros ->; simpl in Hin; destruct Hin).
  assert (Hn3 : forall C, In C G -> is_3chain_b C = false)
    by (apply no_3chain_of_count0; exact H3).
  assert (HeG : existsb is_3chain_b G = false).
  { apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    rewrite (Hn3 D HD) in HDf; discriminate. }
  assert (HeR : existsb is_3chain_b (snd p) = false).
  { apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    assert (HDG : In D G)
      by (apply (Permutation_in _ Hperm); right; exact HD).
    rewrite (Hn3 D HDG) in HDf; discriminate. }
  assert (Hwr : wf (snd p))
    by (destruct (selections_wf G p Hw Hin) as [_ H]; exact H).
  (* both sides are read from the same table *)
  assert (HvG : value G = w38 (cval G) (count4 G))
    by (apply value_no3; assumption).
  assert (HvR : value (snd p) = w38 (cval (snd p)) (count4 (snd p)))
    by (apply value_no3; assumption).
  (* the bonus is unmoved and the controlled value rises by four *)
  assert (Htb : tb (fst p :: snd p) = tb (snd p)).
  { apply tb_remove_loop_no3; [rewrite Hp4; reflexivity | | exact Hnil].
    apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    assert (HDG : In D G) by (apply (Permutation_in _ Hperm); exact HD).
    rewrite (Hn3 D HDG) in HDf; discriminate. }
  assert (Hcr : cval (snd p) = cval G + 4).
  { rewrite <- (cval_perm _ _ Hperm).
    unfold cval; rewrite cbase_cons, Htb, Hp4.
    assert (Ew : weight (Loop 4) = -4) by reflexivity.
    rewrite Ew; unfold cval; lia. }
  assert (Hc4 : count4 G = S (count4 (snd p))).
  { rewrite <- (count4_perm _ _ Hperm), Hp4, count4_cons; reflexivity. }
  (* the opening is a distance from four, and the table shifts by four *)
  assert (Hval : value G = value_open p).
  { unfold value_open; rewrite Hp4 at 1; rewrite HvR, vopen_loop4, HvG.
    pose proof (w38_range (cval (snd p)) (count4 (snd p))) as Hb.
    rewrite Z.abs_neq by lia.
    rewrite Hc4, Hcr.
    pose proof (w38_step (cval G) (count4 (snd p))); lia. }
  split; [exact Hval|].
  apply (opener_optimal_iff G p HNil Hin); exact Hval.
Qed.

(** * Across the threshold: opening a four-loop *)

(** When the four-loop lifts the remainder over the threshold, the two sides
    are computed by different formulas and have to be reconciled. They agree:
    the remainder is its own controlled value, so the opening is the distance
    from that to four, which is the absolute controlled value of the position;
    and with a four-loop present [DotsAndBoxes.w38] is on its [w10] branch,
    where [DotsAndBoxes.w10_small] is exactly that absolute value. *)
Theorem standard_move_4loop_cross :
  forall G p,
    wf G -> count3 G = 0%nat -> standard_move G = Some p ->
    fst p = Loop 4 -> snd p <> [] ->
    cval G < 2 -> 2 <= cval (snd p) ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hp4 Hnil HcG Hcr2.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  pose proof (selections_perm G p Hin) as Hperm.
  assert (HNil : G <> []) by (intros ->; simpl in Hin; destruct Hin).
  assert (Hn3 : forall C, In C G -> is_3chain_b C = false)
    by (apply no_3chain_of_count0; exact H3).
  assert (HeG : existsb is_3chain_b G = false).
  { apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    rewrite (Hn3 D HD) in HDf; discriminate. }
  assert (Hwr : wf (snd p))
    by (destruct (selections_wf G p Hw Hin) as [_ H]; exact H).
  assert (HvG : value G = w38 (cval G) (count4 G))
    by (apply value_no3; assumption).
  assert (HvR : value (snd p) = cval (snd p))
    by (apply value_cval_ge2; assumption).
  assert (Htb : tb (fst p :: snd p) = tb (snd p)).
  { apply tb_remove_loop_no3; [rewrite Hp4; reflexivity | | exact Hnil].
    apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    assert (HDG : In D G) by (apply (Permutation_in _ Hperm); exact HD).
    rewrite (Hn3 D HDG) in HDf; discriminate. }
  assert (Hcr : cval (snd p) = cval G + 4).
  { rewrite <- (cval_perm _ _ Hperm).
    unfold cval; rewrite cbase_cons, Htb, Hp4.
    assert (Ew : weight (Loop 4) = -4) by reflexivity.
    rewrite Ew; unfold cval; lia. }
  assert (Hc4 : count4 G = S (count4 (snd p))).
  { rewrite <- (count4_perm _ _ Hperm), Hp4, count4_cons; reflexivity. }
  (* the four-loop puts the table on its small branch *)
  assert (Hbr : (2 <=? cval G + 4 * Z.of_nat (count4 G)) = true)
    by (apply Z.leb_le; rewrite Hc4; lia).
  assert (Hw10 : w38 (cval G) (count4 G) = Z.abs (cval G)).
  { unfold w38; rewrite Hbr; apply w10_small; lia. }
  assert (Hval : value G = value_open p).
  { unfold value_open; rewrite Hp4 at 1; rewrite HvR, vopen_loop4, HvG, Hw10.
    rewrite Hcr; f_equal; lia. }
  split; [exact Hval|].
  apply (opener_optimal_iff G p HNil Hin); exact Hval.
Qed.

(** * Opening a six-loop *)

Lemma vopen_loop6 : forall w, w <= 4 -> vopen (Loop 6) w = 6 - w.
Proof.
  intros w H; rewrite vopen_max; cbn [csize hand].
  rewrite Z.max_l by lia; lia.
Qed.

(** With neither a three-chain nor a four-loop the value is read from the
    board's size alone, and [DotsAndBoxes.w4z_step6] is exactly what removing
    six boxes does to that reading. *)
Theorem standard_move_6loop :
  forall G p,
    wf G -> count3 G = 0%nat -> count4 G = 0%nat ->
    standard_move G = Some p ->
    is_loop_b (fst p) = true -> csize (fst p) = 6%nat -> snd p <> [] ->
    cval G < 2 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 H4 Hm Hloop Hsz Hnil HcG.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  pose proof (selections_perm G p Hin) as Hperm.
  assert (HNil : G <> []) by (intros ->; simpl in Hin; destruct Hin).
  assert (Hn3 : forall C, In C G -> is_3chain_b C = false)
    by (apply no_3chain_of_count0; exact H3).
  assert (Hn4 : forall C, In C G -> is_4loop_b C = false)
    by (apply (no_member_of_count0 is_4loop_b G); exact H4).
  assert (Hmem : forall (f : comp -> bool),
            (forall C, In C G -> f C = false) -> existsb f (snd p) = false).
  { intros f Hf; apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    assert (HDG : In D G)
      by (apply (Permutation_in _ Hperm); right; exact HD).
    rewrite (Hf D HDG) in HDf; discriminate. }
  assert (HmemG : forall (f : comp -> bool),
            (forall C, In C G -> f C = false) -> existsb f G = false).
  { intros f Hf; apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    rewrite (Hf D HD) in HDf; discriminate. }
  assert (Hwr : wf (snd p))
    by (destruct (selections_wf G p Hw Hin) as [_ H]; exact H).
  (* the opened component is a six-loop *)
  assert (Hp6 : fst p = Loop 6).
  { destruct (fst p) as [n | n]; [discriminate Hloop|].
    cbn [csize] in Hsz; rewrite Hsz; reflexivity. }
  (* the bonus is unmoved, so the controlled value rises by two *)
  assert (Htb : tb (fst p :: snd p) = tb (snd p)).
  { apply tb_remove_loop_no3; [exact Hloop | | exact Hnil].
    apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    assert (HDG : In D G) by (apply (Permutation_in _ Hperm); exact HD).
    rewrite (Hn3 D HDG) in HDf; discriminate. }
  assert (Hcr : cval (snd p) = cval G + 2).
  { rewrite <- (cval_perm _ _ Hperm).
    unfold cval; rewrite cbase_cons, Htb, Hp6.
    assert (Ew : weight (Loop 6) = -2) by reflexivity.
    rewrite Ew; unfold cval; lia. }
  (* both sides are read from the board's size *)
  assert (HvG : value G = w4z (Z.of_nat (size G)))
    by (apply value_no34; try assumption;
        [apply HmemG; exact Hn3 | apply HmemG; exact Hn4 | lia]).
  assert (HvR : value (snd p) = w4z (Z.of_nat (size (snd p))))
    by (apply value_no34; try assumption;
        [apply Hmem; exact Hn3 | apply Hmem; exact Hn4 | lia]).
  assert (Hszr : (6 + size (snd p))%nat = size G).
  { rewrite <- Hsz; exact (selections_size G p Hin). }
  assert (Hval : value G = value_open p).
  { unfold value_open; rewrite Hp6 at 1; rewrite HvR.
    pose proof (w4z_range (Z.of_nat (size (snd p)))) as Hr.
    rewrite vopen_loop6 by lia.
    rewrite HvG.
    pose proof (w4z_step6 (Z.of_nat (size G))) as Hs.
    assert (E : Z.of_nat (size G) - 6 = Z.of_nat (size (snd p))) by lia.
    rewrite E in Hs.
    rewrite Z.abs_neq in Hs by lia; lia. }
  split; [exact Hval|].
  apply (opener_optimal_iff G p HNil Hin); exact Hval.
Qed.

(** * A single component *)

(** With one component there is nothing to choose: the opener takes it whole
    and the position is worth its own size. *)
Lemma vopen_zero : forall C, vopen C 0 = Z.of_nat (csize C).
Proof.
  intros C; rewrite vopen_max.
  pose proof (Nat2Z.is_nonneg (hand C)); rewrite Z.max_l by lia; lia.
Qed.

Theorem standard_move_singleton :
  forall G p,
    standard_move G = Some p -> snd p = [] ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hm Hnil.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  pose proof (selections_perm G p Hin) as Hperm.
  rewrite Hnil in Hperm.
  apply Permutation_length_1_inv in Hperm.
  assert (Hval : value G = value_open p).
  { rewrite Hperm, value_single.
    unfold value_open; rewrite Hnil.
    assert (Hz : value (@nil comp) = 0) by reflexivity.
    rewrite Hz, vopen_zero; reflexivity. }
  split; [exact Hval|].
  assert (HNil : G <> []) by (rewrite Hperm; discriminate).
  apply (opener_optimal_iff G p HNil Hin); exact Hval.
Qed.

(** * The three-chain block, reduced to the closed form *)

(** Opening a three-chain costs one plus the distance from two, so with
    [DotsAndBoxes.value_complete] on both sides the whole block reduces to an
    identity between the closed form at the position and at what is left. That
    turns the remaining work from a statement about play into arithmetic. *)
Theorem standard_move_3chain_reduces :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    v41 G = 1 + Z.abs (v41 (snd p) - 2) ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil Hid.
  assert (Hp3 : fst p = Chain 3)
    by (apply (standard_move_three G p H3); exact Hm).
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  assert (HNil : G <> []) by (intros ->; simpl in Hin; destruct Hin).
  assert (Hwr : wf (snd p))
    by (destruct (selections_wf G p Hw Hin) as [_ H]; exact H).
  assert (Hval : value G = value_open p).
  { unfold value_open; rewrite Hp3 at 1; rewrite vopen_chain3.
    rewrite (value_complete G Hw HNil).
    rewrite (value_complete (snd p) Hwr Hnil); exact Hid. }
  split; [exact Hval|].
  apply (opener_optimal_iff G p HNil Hin); exact Hval.
Qed.

(** The same for the whole standard move, whatever it opens: the block reduces
    to comparing the closed form against the opening of the closed form. *)
Theorem standard_move_reduces :
  forall G p,
    wf G -> standard_move G = Some p -> snd p <> [] ->
    v41 G = vopen (fst p) (v41 (snd p)) ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hm Hnil Hid.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  assert (HNil : G <> []) by (intros ->; simpl in Hin; destruct Hin).
  assert (Hwr : wf (snd p))
    by (destruct (selections_wf G p Hw Hin) as [_ H]; exact H).
  assert (Hval : value G = value_open p).
  { unfold value_open.
    rewrite (value_complete G Hw HNil).
    rewrite (value_complete (snd p) Hwr Hnil); exact Hid. }
  split; [exact Hval|].
  apply (opener_optimal_iff G p HNil Hin); exact Hval.
Qed.

(** * The closed form on its last branch *)

(** Where none of the earlier branches applies, the classifier is read from the
    board's parity alone. *)
Lemma v41_branch5 :
  forall G,
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    (1 <= count3 G)%nat ->
    ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool = false ->
    v41 G = if Z.even (Z.of_nat (size G)) then 2 else 1.
Proof.
  intros G Hc H2 H3 H4; unfold v41.
  rewrite (proj2 (Z.leb_gt 2 (cval G))) by lia.
  rewrite H2.
  rewrite (proj2 (Nat.eqb_neq (count3 G) 0)) by lia.
  rewrite H4; reflexivity.
Qed.

(** Opening a three-chain takes three boxes, so the parity flips and the
    classifier alternates between two and one. That is exactly the cost of the
    opening, so the identity holds outright. *)
Theorem standard_move_3chain_parity :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool = false ->
    (1 <= count3 (snd p))%nat ->
    cval (snd p) < 2 ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = false ->
    ((count3 (snd p) =? 1)%nat
     && (Z.of_nat (size (snd p)) mod 4 =? 3))%bool = false ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G H4G H3r HcR H2R H4R.
  assert (Hp3 : fst p = Chain 3)
    by (apply (standard_move_three G p H3); exact Hm).
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  assert (Hsz : (3 + size (snd p))%nat = size G).
  { pose proof (selections_size G p Hin) as H; rewrite Hp3 in H; exact H. }
  apply (standard_move_3chain_reduces G p Hw H3 Hm Hnil).
  rewrite (v41_branch5 G HcG H2G H3 H4G).
  rewrite (v41_branch5 (snd p) HcR H2R H3r H4R).
  assert (Hpar : Z.even (Z.of_nat (size G))
                 = negb (Z.even (Z.of_nat (size (snd p))))).
  { assert (E : Z.of_nat (size G) = Z.of_nat (size (snd p)) + 3) by lia.
    rewrite E, Z.even_add; cbn [Z.even].
    destruct (Z.even (Z.of_nat (size (snd p)))); reflexivity. }
  rewrite Hpar.
  destruct (Z.even (Z.of_nat (size (snd p)))); reflexivity.
Qed.

(** * The closed form on its four-loop branch *)

Lemma v41_branch2 :
  forall G,
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = true ->
    v41 G = Z.abs (cval G).
Proof.
  intros G Hc H; unfold v41.
  rewrite (proj2 (Z.leb_gt 2 (cval G))) by lia.
  rewrite H; reflexivity.
Qed.

(** With the position and its remainder both on that branch, the controlled
    value is pinned: the case's own exclusions leave only minus two, where the
    opening's cost matches exactly. *)
Theorem standard_move_3chain_both_4loop :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G = -2 -> cval (snd p) = -1 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = true ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = true ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG HcR H2G H2R.
  apply (standard_move_3chain_reduces G p Hw H3 Hm Hnil).
  rewrite (v41_branch2 G ltac:(lia) H2G).
  rewrite (v41_branch2 (snd p) ltac:(lia) H2R).
  rewrite HcG, HcR; reflexivity.
Qed.

(** And where the position is on the parity branch while the remainder is on
    the four-loop branch at minus two, the remainder is worth two and the
    opening costs nothing beyond its own one. *)
Theorem standard_move_3chain_parity_over_4loop :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool = false ->
    Z.even (Z.of_nat (size G)) = false ->
    cval (snd p) = -2 ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = true ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G H4G Hodd HcR H2R.
  apply (standard_move_3chain_reduces G p Hw H3 Hm Hnil).
  rewrite (v41_branch5 G HcG H2G H3 H4G), Hodd.
  rewrite (v41_branch2 (snd p) ltac:(lia) H2R), HcR; reflexivity.
Qed.

(** * The closed form on its remaining branches *)

Lemma v41_branch1 : forall G, 2 <= cval G -> v41 G = cval G.
Proof.
  intros G H; unfold v41; rewrite (proj2 (Z.leb_le 2 (cval G))) by lia.
  reflexivity.
Qed.

Lemma v41_branch4 :
  forall G,
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    count3 G = 1%nat -> Z.of_nat (size G) mod 4 = 3 ->
    v41 G = w310 (cval G) (count4 G).
Proof.
  intros G Hc H2 H3 Hmod; unfold v41.
  rewrite (proj2 (Z.leb_gt 2 (cval G))) by lia.
  rewrite H2.
  rewrite (proj2 (Nat.eqb_neq (count3 G) 0)) by lia.
  rewrite (proj2 (Nat.eqb_eq (count3 G) 1)) by exact H3.
  rewrite (proj2 (Z.eqb_eq (Z.of_nat (size G) mod 4) 3)) by exact Hmod.
  reflexivity.
Qed.

(** * The last three branch pairs *)

(** Each is settled by reading both sides and comparing: opening a three-chain
    costs one plus the distance from two, and in every pair the two readings
    differ by exactly that. *)
Theorem standard_move_3chain_w310_over_value :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    count3 G = 1%nat -> Z.of_nat (size G) mod 4 = 3 ->
    w310 (cval G) (count4 G) = 3 ->
    cval (snd p) = 4 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G Hc1 Hmod Hw310 HcR.
  apply (standard_move_3chain_reduces G p Hw H3 Hm Hnil).
  rewrite (v41_branch4 G HcG H2G Hc1 Hmod), Hw310.
  rewrite (v41_branch1 (snd p) ltac:(lia)), HcR; reflexivity.
Qed.

Theorem standard_move_3chain_parity_over_w310 :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool = false ->
    Z.even (Z.of_nat (size G)) = true ->
    cval (snd p) < 2 ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = false ->
    count3 (snd p) = 1%nat -> Z.of_nat (size (snd p)) mod 4 = 3 ->
    w310 (cval (snd p)) (count4 (snd p)) = 3 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G H4G Hev HcR H2R Hc1R HmodR Hw310.
  apply (standard_move_3chain_reduces G p Hw H3 Hm Hnil).
  rewrite (v41_branch5 G HcG H2G H3 H4G), Hev.
  rewrite (v41_branch4 (snd p) HcR H2R Hc1R HmodR), Hw310; reflexivity.
Qed.

Theorem standard_move_3chain_parity_over_value :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool = false ->
    Z.even (Z.of_nat (size G)) = false ->
    cval (snd p) = 2 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G H4G Hodd HcR.
  apply (standard_move_3chain_reduces G p Hw H3 Hm Hnil).
  rewrite (v41_branch5 G HcG H2G H3 H4G), Hodd.
  rewrite (v41_branch1 (snd p) ltac:(lia)), HcR; reflexivity.
Qed.

(** * The closed form when the last three-chain has gone *)

Lemma v41_branch3 :
  forall G,
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    count3 G = 0%nat ->
    v41 G = w38 (cval G) (count4 G).
Proof.
  intros G Hc H2 H3; unfold v41.
  rewrite (proj2 (Z.leb_gt 2 (cval G))) by lia.
  rewrite H2.
  rewrite (proj2 (Nat.eqb_eq (count3 G) 0)) by exact H3.
  reflexivity.
Qed.

(** Opening the only three-chain moves the remainder onto the three-chain-free
    branch, and the two readings differ by the cost of the opening. *)
Theorem standard_move_3chain_w310_over_w38 :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    count3 G = 1%nat -> Z.of_nat (size G) mod 4 = 3 ->
    w310 (cval G) (count4 G) = 3 ->
    cval (snd p) < 2 ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = false ->
    count3 (snd p) = 0%nat ->
    w38 (cval (snd p)) (count4 (snd p)) = 4 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G Hc1 Hmod Hw310 HcR H2R Hc0R Hw38.
  apply (standard_move_3chain_reduces G p Hw H3 Hm Hnil).
  rewrite (v41_branch4 G HcG H2G Hc1 Hmod), Hw310.
  rewrite (v41_branch3 (snd p) HcR H2R Hc0R), Hw38; reflexivity.
Qed.

Theorem standard_move_3chain_parity_over_w38 :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool = false ->
    Z.even (Z.of_nat (size G)) = true ->
    cval (snd p) < 2 ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = false ->
    count3 (snd p) = 0%nat ->
    w38 (cval (snd p)) (count4 (snd p)) = 3 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G H4G Hev HcR H2R Hc0R Hw38.
  apply (standard_move_3chain_reduces G p Hw H3 Hm Hnil).
  rewrite (v41_branch5 G HcG H2G H3 H4G), Hev.
  rewrite (v41_branch3 (snd p) HcR H2R Hc0R), Hw38; reflexivity.
Qed.

(** * Discharging the table value from the position *)

(** With no four-loop the three-chain table is read at zero, where it is three
    whatever the controlled value, so the numeric hypothesis is not needed. *)
Lemma w310_no4loop : forall c, c < 2 -> w310 c 0 = 3.
Proof.
  intros c H; unfold w310.
  replace (c + 4 * Z.of_nat 0) with c by (cbn [Z.of_nat]; lia).
  rewrite (proj2 (Z.leb_gt 2 c)) by lia; reflexivity.
Qed.

Corollary standard_move_3chain_w310_over_value' :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    count3 G = 1%nat -> Z.of_nat (size G) mod 4 = 3 ->
    count4 G = 0%nat ->
    cval (snd p) = 4 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G Hc1 Hmod H4 HcR.
  apply (standard_move_3chain_w310_over_value G p Hw H3 Hm Hnil HcG H2G
           Hc1 Hmod); [rewrite H4; apply w310_no4loop; exact HcG | exact HcR].
Qed.

Corollary standard_move_3chain_w310_over_w38' :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    count3 G = 1%nat -> Z.of_nat (size G) mod 4 = 3 ->
    count4 G = 0%nat ->
    cval (snd p) < 2 ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = false ->
    count3 (snd p) = 0%nat ->
    w38 (cval (snd p)) (count4 (snd p)) = 4 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G Hc1 Hmod H4 HcR H2R Hc0R Hw38.
  apply (standard_move_3chain_w310_over_w38 G p Hw H3 Hm Hnil HcG H2G
           Hc1 Hmod);
    [rewrite H4; apply w310_no4loop; exact HcG
     | exact HcR | exact H2R | exact Hc0R | exact Hw38].
Qed.

(** * The three-chain-free table at the values that arise *)

(** On the remainders that arise here the table is read at a fixed point, so
    the numeric hypothesis is a computation rather than an assumption. Which
    branch of [DotsAndBoxes.w38] does the reading differs between them: the
    first two fall to [w11], the third to [w10]. *)
Lemma w38_at_0_0 : w38 0 0 = 4.
Proof. reflexivity. Qed.

Lemma w38_at_1_0 : w38 1 0 = 3.
Proof. reflexivity. Qed.

Lemma w38_at_m3_2 : w38 (-3) 2 = 3.
Proof. reflexivity. Qed.

Corollary standard_move_3chain_w310_over_w38_at0 :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    count3 G = 1%nat -> Z.of_nat (size G) mod 4 = 3 -> count4 G = 0%nat ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = false ->
    count3 (snd p) = 0%nat ->
    cval (snd p) = 0 -> count4 (snd p) = 0%nat ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G Hc1 Hmod H4 H2R Hc0R HcR H4R.
  apply (standard_move_3chain_w310_over_w38' G p Hw H3 Hm Hnil HcG H2G
           Hc1 Hmod H4); [lia | exact H2R | exact Hc0R |].
  rewrite HcR, H4R; exact w38_at_0_0.
Qed.

Corollary standard_move_3chain_parity_over_w38_at1 :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool = false ->
    Z.even (Z.of_nat (size G)) = true ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = false ->
    count3 (snd p) = 0%nat ->
    cval (snd p) = 1 -> count4 (snd p) = 0%nat ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G H4G Hev H2R Hc0R HcR H4R.
  apply (standard_move_3chain_parity_over_w38 G p Hw H3 Hm Hnil HcG H2G
           H4G Hev); [lia | exact H2R | exact Hc0R |].
  rewrite HcR, H4R; exact w38_at_1_0.
Qed.

Corollary standard_move_3chain_parity_over_w38_atm3 :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool = false ->
    Z.even (Z.of_nat (size G)) = true ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = false ->
    count3 (snd p) = 0%nat ->
    cval (snd p) = -3 -> count4 (snd p) = 2%nat ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G H4G Hev H2R Hc0R HcR H4R.
  apply (standard_move_3chain_parity_over_w38 G p Hw H3 Hm Hnil HcG H2G
           H4G Hev); [lia | exact H2R | exact Hc0R |].
  rewrite HcR, H4R; exact w38_at_m3_2.
Qed.

(** * Why the priority ordering is needed *)

(** Opening a shortest component is not optimal in general. On a six-loop
    beside a four-chain the chain is the shorter component, but opening it
    hands over six where opening the loop hands over two. So the strategy's
    ordering of three-chain before loop before chain is doing real work, and
    the case analysis above cannot be replaced by a rule that simply takes the
    shortest component available. *)
Example shortest_is_not_optimal :
  value [Loop 6; Chain 4] = 2
  /\ value_open (Chain 4, [Loop 6]) = 6
  /\ value_open (Loop 6, [Chain 4]) = 2.
Proof. repeat split; reflexivity. Qed.

(** The standard move takes the loop there, since no three-chain is present. *)
Example standard_move_takes_the_loop :
  standard_move [Loop 6; Chain 4] = Some (Loop 6, [Chain 4]).
Proof. reflexivity. Qed.

(** * The loop block is covered outright *)

Lemma standard_move_is_shortest_loop :
  forall G p,
    count3 G = 0%nat -> standard_move G = Some p ->
    is_loop_b (fst p) = true ->
    shortest_of is_loop_b G = Some p.
Proof.
  intros G p H3 Hm Hloop.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  assert (HinC : In (fst p) G) by (apply selections_In; exact Hin).
  unfold standard_move in Hm.
  rewrite (shortest_of_none_of_no_witness is_3chain_b G
             (no_3chain_of_count0 G H3)) in Hm.
  destruct (shortest_of is_loop_b G) as [q|] eqn:EL.
  - exact Hm.
  - exfalso.
    rewrite (shortest_of_none is_loop_b G EL (fst p) HinC) in Hloop;
      discriminate.
Qed.

(** A shortest loop of eight boxes or more leaves every weight nonnegative, so
    the position's controlled value already clears the bound; a four-loop or a
    six-loop that does not clear it falls under the other two cases. The three
    together therefore leave nothing over. *)
Theorem loop_block_exhaustive :
  forall G p,
    wf G -> count3 G = 0%nat -> standard_move G = Some p ->
    is_loop_b (fst p) = true ->
    Z.of_nat (csize (fst p)) - 4 <= cval G
    \/ (is_4loop_b (fst p) = true /\ cval G < 2)
    \/ (count4 G = 0%nat /\ csize (fst p) = 6%nat /\ cval G < 2).
Proof.
  intros G p Hw H3 Hm Hloop.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  assert (HinC : In (fst p) G) by (apply selections_In; exact Hin).
  assert (HNil : G <> []) by (intros ->; simpl in Hin; destruct Hin).
  pose proof (standard_move_is_shortest_loop G p H3 Hm Hloop) as Hs.
  destruct (shortest_of_min is_loop_b G p Hs) as [_ Hmn].
  assert (Hmin : forall D, In D G -> is_loop_b D = true ->
            (csize (fst p) <= csize D)%nat).
  { intros D HD Hl.
    destruct (In_selections G D HD) as [rest Hsel].
    exact (Hmn (D, rest) Hsel Hl). }
  assert (Hev : (4 <= csize (fst p))%nat /\ Nat.even (csize (fst p)) = true).
  { unfold wf in Hw; rewrite Forall_forall in Hw; specialize (Hw (fst p) HinC).
    destruct (fst p) as [n | n]; [discriminate Hloop|].
    cbn [wf_comp csize] in *; tauto. }
  destruct Hev as [Hge4 Heven].
  destruct (Z.le_gt_cases (Z.of_nat (csize (fst p)) - 4) (cval G))
    as [Hok | Hbad]; [left; exact Hok|].
  assert (Hsmall : (csize (fst p) <= 7)%nat).
  { destruct (Nat.le_gt_cases (csize (fst p)) 7) as [H | H]; [exact H|].
    exfalso.
    assert (Hwt : forall D, In D G -> 0 <= weight D).
    { intros D HD.
      unfold wf in Hw; rewrite Forall_forall in Hw.
      pose proof (Hw D HD) as HwD.
      destruct D as [n | n].
      - assert (Hn3 : is_3chain_b (Chain n) = false)
          by (apply (no_3chain_of_count0 G H3); exact HD).
        cbn [wf_comp] in HwD; rewrite weight_chain; cbn [csize].
        destruct (Nat.eq_dec n 3) as [He | Hne];
          [rewrite He in Hn3; cbn in Hn3; discriminate Hn3 | lia].
      - pose proof (Hmin (Loop n) HD eq_refl) as Hm8.
        rewrite weight_loop; cbn [csize] in *; lia. }
    pose proof (cbase_ge_member G (fst p) HinC Hwt) as Hcb.
    pose proof (tb_pos G HNil) as Htb.
    assert (Hwp : weight (fst p) = Z.of_nat (csize (fst p)) - 8).
    { destruct (fst p) as [n | n]; [discriminate Hloop | apply weight_loop]. }
    unfold cval in Hbad; lia. }
  assert (Hcase : csize (fst p) = 4%nat \/ csize (fst p) = 6%nat).
  { apply Nat.even_spec in Heven; destruct Heven as [k Hk]; lia. }
  destruct Hcase as [H4 | H6].
  - right; left; split; [|lia].
    destruct (fst p) as [n | n]; [discriminate Hloop|].
    cbn [csize] in H4; rewrite H4; reflexivity.
  - right; right; split; [|split; [exact H6 | lia]].
    destruct (count4 G) as [|k] eqn:E4; [reflexivity|].
    exfalso.
    destruct (In_selections G (Loop 4) (count4_pos_In G ltac:(lia)))
      as [rest Hsel].
    pose proof (Hmin (Loop 4) (count4_pos_In G ltac:(lia)) eq_refl) as Hle.
    cbn [csize] in Hle; lia.
Qed.

(** * Positions with no three-chain, outright *)

Lemma count_loops_zero_of_none :
  forall G, shortest_of is_loop_b G = None -> count_loops G = 0%nat.
Proof.
  intros G H; unfold count_loops.
  destruct (filter is_loop_b G) as [|D l] eqn:E; [reflexivity|].
  exfalso.
  assert (Hin : In D (filter is_loop_b G)) by (rewrite E; left; reflexivity).
  apply filter_In in Hin; destruct Hin as [HinG Hf].
  rewrite (shortest_of_none is_loop_b G H D HinG) in Hf; discriminate.
Qed.

(** Every chain has at least four boxes here, so the criterion applies with
    nothing to check. *)
Theorem standard_move_chain_complete :
  forall G p,
    wf G -> count3 G = 0%nat -> count_loops G = 0%nat ->
    standard_move G = Some p ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 HL Hm.
  destruct (list_eq_dec comp_eq_dec (snd p) []) as [Hnil | Hnn].
  - apply (standard_move_singleton G p Hm Hnil).
  - apply (standard_move_chain_optimal G p Hw H3 HL Hm Hnn).
Qed.

(** And with [loop_block_exhaustive] the loop openings are covered too. *)
Theorem standard_move_loop_complete :
  forall G p,
    wf G -> count3 G = 0%nat -> standard_move G = Some p ->
    is_loop_b (fst p) = true ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hloop.
  destruct (list_eq_dec comp_eq_dec (snd p) []) as [Hnil | Hnn].
  - apply (standard_move_singleton G p Hm Hnil).
  - destruct (loop_block_exhaustive G p Hw H3 Hm Hloop)
      as [Hb | [[H4 Hc] | [H4 [H6 Hc]]]].
    + apply (standard_move_loop_optimal G p Hw H3 Hm Hloop Hnn Hb).
    + assert (Hp4 : fst p = Loop 4) by (apply is_4loop_b_eq; exact H4).
      destruct (Z.lt_ge_cases (cval (snd p)) 2) as [Hcr | Hcr].
      * apply (standard_move_4loop_below G p Hw H3 Hm Hp4 Hnn Hc Hcr).
      * apply (standard_move_4loop_cross G p Hw H3 Hm Hp4 Hnn Hc Hcr).
    + apply (standard_move_6loop G p Hw H3 H4 Hm Hloop H6 Hnn Hc).
Qed.

(** So the standard move is optimal on every position holding no three-chain,
    with no hypothesis beyond wellformedness. *)
Theorem standard_move_no3_complete :
  forall G p,
    wf G -> count3 G = 0%nat -> standard_move G = Some p ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm.
  destruct (is_loop_b (fst p)) eqn:Hl.
  - apply (standard_move_loop_complete G p Hw H3 Hm Hl).
  - assert (HL : count_loops G = 0%nat).
    { apply count_loops_zero_of_none.
      destruct (shortest_of is_loop_b G) as [q|] eqn:EL; [|reflexivity].
      exfalso.
      assert (Hpq : p = q).
      { unfold standard_move in Hm.
        rewrite (shortest_of_none_of_no_witness is_3chain_b G
                   (no_3chain_of_count0 G H3)), EL in Hm.
        injection Hm as Hm; symmetry; exact Hm. }
      destruct (shortest_of_min is_loop_b G q EL) as [Hq _].
      rewrite Hpq, Hq in Hl; discriminate. }
    apply (standard_move_chain_complete G p Hw H3 HL Hm).
Qed.

(** * Where the four-loop branch can sit *)

(** Three three-chains beside a four-loop is a position of three-chains and
    four-loops, so it can never satisfy the four-loop branch's own exclusion. *)
Lemma three_threes_is_only34 :
  forall G,
    (1 <= count4 G)%nat -> rest_is_three_threes_b G = true -> only34 G = true.
Proof.
  intros G H4 Hr; unfold rest_is_three_threes_b in Hr.
  apply andb_true_iff in Hr; destruct Hr as [Hc3 Hlen].
  apply Nat.eqb_eq in Hc3; apply Nat.eqb_eq in Hlen.
  set (H := drop_first is_4loop_b G) in *.
  assert (Hsel : In (Loop 4, H) (selections G))
    by (apply drop_first_4loop_sel; exact H4).
  pose proof (selections_perm G (Loop 4, H) Hsel) as Hp; simpl in Hp.
  assert (Hall : forallb is_3chain_b H = true)
    by (apply filter_full; unfold count3 in Hc3; rewrite Hc3, Hlen; reflexivity).
  assert (Hcons : only34 (Loop 4 :: H) = true).
  { unfold only34; rewrite forallb_forall; intros C HC.
    destruct HC as [<- | HC]; [reflexivity|].
    rewrite forallb_forall in Hall; rewrite (Hall C HC); reflexivity. }
  apply (only34_perm_inv (Loop 4 :: H) G Hp Hcons).
Qed.

(** So outside the three named cases, a position on the four-loop branch has
    controlled value exactly minus two: the values from minus one to one are
    precisely what case (ii) claims, and the one position case (ii) sets aside
    is not on this branch at all. *)
Theorem branch2_cval_m2 :
  forall G,
    case_ii G = false ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = true ->
    cval G < 2 ->
    cval G = -2.
Proof.
  intros G Hii Hb Hlt.
  apply andb_true_iff in Hb; destruct Hb as [Hb Hge].
  apply andb_true_iff in Hb; destruct Hb as [H4 H34].
  apply Z.leb_le in Hge; apply negb_true_iff in H34.
  assert (Hc4 : (1 <= count4 G)%nat) by (apply count4_pos_iff; exact H4).
  unfold case_ii in Hii.
  apply andb_false_iff in Hii; destruct Hii as [Hii | Hnr].
  - apply andb_false_iff in Hii; destruct Hii as [Hii | Hc].
    + apply andb_false_iff in Hii; destruct Hii as [Hle | Hm1].
      * apply Z.leb_gt in Hle; lia.
      * apply Z.leb_gt in Hm1; lia.
    + apply Nat.leb_gt in Hc; lia.
  - apply negb_false_iff in Hnr.
    rewrite (three_threes_is_only34 G Hc4 Hnr) in H34; discriminate.
Qed.
