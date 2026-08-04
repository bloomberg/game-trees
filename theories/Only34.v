(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Positions of three-chains and four-loops, in canonical order.

    These are the positions Allcock's case (ii) leaves over, and they are
    determined by their two counts: [only34_perm] sorts any of them into
    three-chains followed by four-loops.

    [value_perm] is what makes that useful. It follows from
    [ShortLip.svalue_perm] through [DotsAndBoxes.svalue_wf], since the capped
    value agrees with the original on wellformed positions. The original
    development does not carry it. *)

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
Require Import GameTrees.ShortAll.
Require Import GameTrees.ShortSplit.
Require Import GameTrees.ShortLip.
Require Import GameTrees.Shortest.

Import ListNotations.

Open Scope Z_scope.

(** * Wellformedness and the value are permutation invariant *)

Lemma wf_perm : forall G H, Permutation G H -> wf G -> wf H.
Proof.
  intros G H Hp Hw; unfold wf in *; rewrite Forall_forall in *.
  intros C HC; apply Hw.
  apply (Permutation_in _ (Permutation_sym Hp)); exact HC.
Qed.

Theorem value_perm :
  forall G H, wf G -> Permutation G H -> value G = value H.
Proof.
  intros G H Hw Hp.
  assert (HwH : wf H) by (apply (wf_perm G H Hp Hw)).
  rewrite <- (svalue_wf G Hw), <- (svalue_wf H HwH).
  apply svalue_perm; exact Hp.
Qed.

(** * Sorting a position of three-chains and four-loops *)

Lemma only34_cons :
  forall C G, only34 (C :: G) = true ->
    (is_3chain_b C = true \/ is_4loop_b C = true) /\ only34 G = true.
Proof.
  intros C G H; unfold only34 in H; simpl in H.
  apply andb_true_iff in H; destruct H as [HC HG].
  split; [apply orb_true_iff; exact HC | exact HG].
Qed.

(** [DotsAndBoxes.perm_mix_of_only34] already sorts such a position into
    [mix], and [DotsAndBoxes.value_mix] computes that. With [value_perm] the
    two combine: a position of three-chains and four-loops is worth what its
    counts say, whatever order it is written in. *)
Corollary only34_value :
  forall G, wf G -> only34 G = true ->
    value G = v36 (count3 G) (count4 G).
Proof.
  intros G Hw H34.
  rewrite (value_perm G (mix (count3 G) (count4 G)) Hw
             (perm_mix_of_only34 G H34)).
  apply value_mix.
Qed.

(** * What is left after opening a four-loop *)

Lemma only34_perm_inv :
  forall G H, Permutation G H -> only34 G = true -> only34 H = true.
Proof.
  intros G H Hp H34; unfold only34 in *; rewrite forallb_forall in *.
  intros C HC; apply H34.
  apply (Permutation_in _ (Permutation_sym Hp)); exact HC.
Qed.

Theorem only34_rest :
  forall G rest,
    only34 G = true -> In (Loop 4, rest) (selections G) ->
    only34 rest = true /\
    count3 rest = count3 G /\ S (count4 rest) = count4 G.
Proof.
  intros G rest H34 Hsel.
  pose proof (selections_perm G (Loop 4, rest) Hsel) as Hp; simpl in Hp.
  assert (Hr : only34 (Loop 4 :: rest) = true)
    by (apply (only34_perm_inv G); [apply Permutation_sym; exact Hp | exact H34]).
  destruct (only34_cons (Loop 4) rest Hr) as [_ Hrest].
  split; [exact Hrest|].
  split.
  - rewrite <- (count3_perm _ _ Hp); reflexivity.
  - rewrite <- (count4_perm _ _ Hp); reflexivity.
Qed.

(** And what remains is again in canonical form, so its value is computable
    from the counts alone. *)
Corollary only34_rest_value :
  forall G rest,
    wf G -> only34 G = true -> In (Loop 4, rest) (selections G) ->
    value rest = v36 (count3 G) (pred (count4 G)).
Proof.
  intros G rest Hw H34 Hsel.
  destruct (only34_rest G rest H34 Hsel) as [Hr [H3 H4]].
  pose proof (selections_perm G (Loop 4, rest) Hsel) as Hp; simpl in Hp.
  assert (Hwr : wf rest).
  { assert (Hwc : wf (Loop 4 :: rest))
      by (apply (wf_perm G); [apply Permutation_sym; exact Hp | exact Hw]).
    inversion Hwc; assumption. }
  rewrite (only34_value rest Hwr Hr), H3.
  replace (pred (count4 G)) with (count4 rest) by lia; reflexivity.
Qed.

(** * Opening a four-loop, on such a position *)

(** The value and the option are both read off the counts, so the comparison
    Allcock's case (ii) needs is arithmetic in [v36]. *)
Theorem only34_open_four :
  forall G rest,
    wf G -> only34 G = true -> In (Loop 4, rest) (selections G) ->
    value G = v36 (count3 G) (count4 G) /\
    value_open (Loop 4, rest) = vopen (Loop 4) (v36 (count3 G)
                                                   (pred (count4 G))).
Proof.
  intros G rest Hw H34 Hsel.
  split; [apply only34_value; assumption|].
  unfold value_open; cbn [fst snd].
  rewrite (only34_rest_value G rest Hw H34 Hsel); reflexivity.
Qed.

(** * The controlled value of such a position *)

Lemma cbase_mix : forall t f, cbase (mix t f) = - Z.of_nat t - 4 * Z.of_nat f.
Proof.
  induction t as [|t IH]; intros f.
  - change (mix 0 f) with (repeat (Loop 4) f).
    rewrite cbase_repeat_loop4; lia.
  - rewrite mix_chain_cons, cbase_cons, weight_chain, (IH f); lia.
Qed.

Lemma In_mix_three : forall t f, (1 <= t)%nat -> In (Chain 3) (mix t f).
Proof.
  intros t f Ht; destruct t as [|t']; [lia|].
  rewrite mix_chain_cons; left; reflexivity.
Qed.

Lemma In_mix_four : forall t f, (1 <= f)%nat -> In (Loop 4) (mix t f).
Proof.
  intros t f Hf; unfold mix; apply in_or_app; right.
  destruct f as [|f']; [lia|]; left; reflexivity.
Qed.

(** With both kinds present the terminal bonus is six. *)
Lemma tb_mix : forall t f, (1 <= t)%nat -> (1 <= f)%nat -> tb (mix t f) = 6.
Proof.
  intros t f Ht Hf; apply tb_six.
  - apply existsb_exists; exists (Loop 4).
    split; [apply In_mix_four; exact Hf | reflexivity].
  - apply existsb_exists; exists (Chain 3).
    split; [apply In_mix_three; exact Ht | reflexivity].
  - apply forallb_forall; intros C HC.
    destruct (In_mix t f C HC) as [-> | ->]; reflexivity.
Qed.

Theorem cval_mix :
  forall t f, (1 <= t)%nat -> (1 <= f)%nat ->
    cval (mix t f) = 6 - Z.of_nat t - 4 * Z.of_nat f.
Proof.
  intros t f Ht Hf; unfold cval.
  rewrite cbase_mix, (tb_mix t f Ht Hf); lia.
Qed.

(** * Which counts Allcock's case (ii) admits *)

Theorem case_ii_only34_counts :
  forall G,
    only34 G = true -> (1 <= count4 G)%nat ->
    -1 <= cval G -> cval G <= 1 ->
    (count3 G = 0 /\ count4 G = 2)%nat \/
    (count3 G = 1 /\ count4 G = 1)%nat \/
    (count3 G = 2 /\ count4 G = 1)%nat \/
    (count3 G = 3 /\ count4 G = 1)%nat.
Proof.
  intros G H34 H4 Hge Hle.
  rewrite (cval_perm G (mix (count3 G) (count4 G))
             (perm_mix_of_only34 G H34)) in Hge, Hle.
  destruct (count3 G) as [|t] eqn:E3.
  - rewrite (cval_mix0 (count4 G) H4) in Hge, Hle; left; split; lia.
  - rewrite (cval_mix (S t) (count4 G) ltac:(lia) H4) in Hge, Hle.
    assert (Ht : (t = 0 \/ t = 1 \/ t = 2)%nat) by lia.
    destruct Ht as [-> | [-> | ->]];
      [right; left | right; right; left | right; right; right];
      split; lia.
Qed.

(** * Excluding three three-chains beside a four-loop *)

Lemma only34_counts_length :
  forall G, only34 G = true -> (count3 G + count4 G)%nat = length G.
Proof.
  induction G as [|C G IH]; intros H; [reflexivity|].
  destruct (only34_cons C G H) as [HC HG]; specialize (IH HG).
  destruct HC as [H3 | H4].
  - assert (E : C = Chain 3) by (apply is_3chain_b_eq; exact H3); subst C.
    assert (E3 : count3 (Chain 3 :: G) = S (count3 G)) by reflexivity.
    assert (E4 : count4 (Chain 3 :: G) = count4 G) by reflexivity.
    rewrite E3, E4; simpl length; lia.
  - assert (E : C = Loop 4) by (apply is_4loop_b_eq; exact H4); subst C.
    assert (E3 : count3 (Loop 4 :: G) = count3 G) by reflexivity.
    assert (E4 : count4 (Loop 4 :: G) = S (count4 G)) by reflexivity.
    rewrite E3, E4; simpl length; lia.
Qed.

(** [DotsAndBoxes.drop_first] really does remove a four-loop. *)
Lemma drop_first_4loop_sel :
  forall G, (1 <= count4 G)%nat ->
    In (Loop 4, drop_first is_4loop_b G) (selections G).
Proof.
  intros G H4; unfold drop_first.
  destruct (filter (fun p => is_4loop_b (fst p)) (selections G))
    as [|p l] eqn:E.
  - exfalso.
    destruct (In_selections G (Loop 4) (count4_pos_In G H4)) as [rest Hsel].
    assert (Hin : In (Loop 4, rest)
                    (filter (fun q => is_4loop_b (fst q)) (selections G)))
      by (apply filter_In; split; [exact Hsel | reflexivity]).
    rewrite E in Hin; destruct Hin.
  - assert (Hin : In p (filter (fun q => is_4loop_b (fst q)) (selections G)))
      by (rewrite E; left; reflexivity).
    apply filter_In in Hin; destruct Hin as [Hsel Hf].
    assert (Hp : fst p = Loop 4) by (apply is_4loop_b_eq; exact Hf).
    destruct p as [C rest]; cbn [fst snd] in *; subst C; exact Hsel.
Qed.

(** Three three-chains beside one four-loop is exactly the position the case
    sets aside, so that pair cannot arise. *)
Theorem only34_three_threes :
  forall G,
    only34 G = true -> count3 G = 3%nat -> count4 G = 1%nat ->
    rest_is_three_threes_b G = true.
Proof.
  intros G H34 H3 H4; unfold rest_is_three_threes_b.
  assert (Hsel : In (Loop 4, drop_first is_4loop_b G) (selections G))
    by (apply drop_first_4loop_sel; lia).
  destruct (only34_rest G (drop_first is_4loop_b G) H34 Hsel) as [Hr [E3 E4]].
  assert (Hlen : (count3 (drop_first is_4loop_b G)
                  + count4 (drop_first is_4loop_b G))%nat
                 = length (drop_first is_4loop_b G))
    by (apply only34_counts_length; exact Hr).
  apply andb_true_iff; split; apply Nat.eqb_eq; lia.
Qed.
