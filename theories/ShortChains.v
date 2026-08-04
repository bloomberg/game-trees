(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Chains of one and two boxes.

    [GameTrees.DotsAndBoxes] asks a chain to hold at least three boxes, so that
    the hard-hearted handout of two is always available, and caps the handout at
    the component so that shorter chains can be written down at all. It proves
    the capped recursion conservative and computes the uniform families, and
    stops there: the classification behind [value_complete] reads the terminal
    bonus off the component names, and a chain with no handout to spare has no
    place in that reading.

    This file replaces the reading rather than widening it. [stb] is the smaller
    of twice the largest handout the position holds and the cap the opener can
    force it down to, and [stb_eq_tb] proves that on every wellformed position
    this is exactly Berlekamp's terminal bonus. On that footing
    [scval2_le_svalue] is the control bound and [svalue_scval2_ge2] the
    threshold theorem, both on every position the board can present.

    Beneath the threshold the short chains separate from the rest.
    [svalue_split] is the decomposition: the value is the fold [g] of the chains
    of one and two boxes onto the value of everything else, which is wellformed
    and so computed by [DotsAndBoxes.v41]. [svalue_closed] composes the two, and
    [svalue_closed_extends] checks the result against the original theory, where
    it must and does agree. [short_opener_rule] is the opening rule that falls
    out: open a one-box chain if there is one, otherwise a two-box chain. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Sorting.Permutation.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.

Import ListNotations.

Open Scope Z_scope.

(** ****************************************************************** *)
(** The capped weight, and the base built from it.

    [DotsAndBoxes.cbase] sums each component's length less twice its handout.
    With the handout capped at the component, [scbase] is that same sum for the
    capped recursion, and it agrees with Berlekamp's wherever a chain is long
    enough to spare a handout at all. What goes on top of it is the terminal
    bonus, which cannot simply be reused; the next section shows why, and the
    one after that supplies the replacement. *)

(** * The capped weight *)

(** What a component is worth to the controller who declines it. *)
Definition sweight (C : comp) : Z :=
  Z.of_nat (csize C) - 2 * Z.of_nat (shand C).

Fixpoint scbase (G : position) : Z :=
  match G with [] => 0 | C :: r => sweight C + scbase r end.

Lemma scbase_perm : forall G H, Permutation G H -> scbase G = scbase H.
Proof.
  intros G H HP; induction HP; simpl; try lia; congruence.
Qed.

Lemma selections_scbase :
  forall G p, In p (selections G) -> scbase G = sweight (fst p) + scbase (snd p).
Proof.
  intros G p Hp.
  rewrite <- (scbase_perm _ _ (selections_perm G p Hp)); reflexivity.
Qed.

(** * Bounding the capped value from below *)

(** A lower bound on every option is a lower bound on the capped value. *)
Lemma svalue_lower_bound :
  forall G b,
    G <> [] ->
    (forall p, In p (selections G) -> b <= svalue_open p) ->
    b <= svalue G.
Proof.
  intros G b HNil Hb.
  destruct (svalue_attained G HNil) as [p [Hp Hval]].
  rewrite Hval; apply Hb; exact Hp.
Qed.

(** ****************************************************************** *)
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

(** ****************************************************************** *)
(** One-box chains beside a single long component.

    The capped recursion is conservative and the uniform families of one- and
    two-box chains are settled, but the analogue of [value_complete] is not.
    [svalue_ones_one] is the first mixed family: any number of one-box chains
    beside a single long component, whose value is the component's length
    driven down one box at a time under the map that opens a one-box chain. *)

(** * Iterating a one-box opening *)

(** Opening a one-box chain sends the worth of what is left to its distance
    from one. *)
Fixpoint dec1 (a : nat) (w : Z) : Z :=
  match a with O => w | S k => Z.abs (dec1 k w - 1) end.

Lemma dec1_S : forall a w, dec1 (S a) w = Z.abs (dec1 a w - 1).
Proof. reflexivity. Qed.

Definition onechains (a : nat) : position := repeat (Chain 1) a.

Lemma onechains_S : forall a, onechains (S a) = Chain 1 :: onechains a.
Proof. reflexivity. Qed.

(** Removing a component from [onechains a ++ [C]] leaves either a shorter
    such position or the one-box chains alone. *)
Lemma selections_ones_one :
  forall a C p,
    In p (selections (onechains a ++ [C])) ->
    (fst p = Chain 1 /\ exists a', a = S a' /\ snd p = onechains a' ++ [C]) \/
    (fst p = C /\ snd p = onechains a).
Proof.
  induction a as [|a IH]; intros C p Hp.
  - simpl in Hp; destruct Hp as [<- | []].
    right; split; reflexivity.
  - rewrite onechains_S in Hp; simpl app in Hp; simpl selections in Hp.
    destruct Hp as [<- | Hp].
    + left; cbn [fst snd]; split; [reflexivity|].
      exists a; split; reflexivity.
    + apply in_map_iff in Hp; destruct Hp as [[qc qr] [Heq Hq]].
      cbn [fst snd] in Heq; subst p.
      destruct (IH C (qc, qr) Hq) as [[Hc [a' [Ha Hs]]] | [Hc Hs]];
        cbn [fst snd] in Hc, Hs.
      * left; cbn [fst snd]; split; [exact Hc|].
        exists a; split; [reflexivity|].
        rewrite Hs, Ha, onechains_S; reflexivity.
      * right; cbn [fst snd]; split; [exact Hc|].
        rewrite Hs, onechains_S; reflexivity.
Qed.

Lemma ones_one_nonnil : forall a C, onechains a ++ [C] <> [].
Proof.
  intros [|a] C; simpl; discriminate.
Qed.

(** The long component is always available to open. *)
Lemma In_selections_ones_one :
  forall a C, In (C, onechains a) (selections (onechains a ++ [C])).
Proof.
  induction a as [|a IH]; intros C; [simpl; left; reflexivity|].
  rewrite onechains_S; simpl app; simpl selections; right.
  apply in_map_iff; exists (C, onechains a); split; [reflexivity | apply IH].
Qed.

(** The handout of a component with two boxes or more is between one and its
    own length. *)
Lemma shand_range :
  forall C, (2 <= csize C)%nat -> (1 <= shand C <= csize C)%nat.
Proof.
  intros [k | k] Hc; unfold shand, hand; simpl csize in *; lia.
Qed.

(** The position is worth no more than the component, since opening the
    component is one of the opener's choices. *)
Lemma svalue_ones_one_bounded :
  forall a C,
    (2 <= csize C)%nat ->
    0 <= svalue (onechains a ++ [C]) <= Z.of_nat (csize C).
Proof.
  intros a C Hc; split; [apply svalue_nonneg|].
  eapply Z.le_trans;
    [apply (svalue_le_open _ _ (In_selections_ones_one a C))|].
  unfold svalue_open; cbn [fst snd]; unfold svopen.
  rewrite svalue_chain1_heap.
  pose proof (shand_range C Hc) as Hr.
  assert (Hz : (1 <= Z.of_nat (shand C) <= Z.of_nat (csize C))) by lia.
  apply Z.max_lub; destruct (Nat.even a); lia.
Qed.

(** Opening the long component is never better than opening a one-box chain,
    once the component holds two boxes or more. *)
Lemma open_long_not_better :
  forall a C,
    (2 <= csize C)%nat ->
    Z.abs (svalue (onechains a ++ [C]) - 1)
      <= svopen C (svalue (onechains (S a))).
Proof.
  intros a C Hc.
  destruct (svalue_ones_one_bounded a C Hc) as [H1 H2].
  unfold svopen; rewrite svalue_chain1_heap.
  pose proof (shand_range C Hc) as Hr.
  assert (Hz : (1 <= Z.of_nat (shand C) <= Z.of_nat (csize C))) by lia.
  eapply Z.le_trans; [| apply Z.le_max_l].
  apply (proj2 (Z.abs_le _ _)).
  destruct (Nat.even (S a)); lia.
Qed.

(** The value of any number of one-box chains beside one long component: the
    component's length, driven down one step per one-box chain and bouncing at
    zero. *)
Theorem svalue_ones_one :
  forall a C,
    (2 <= csize C)%nat ->
    svalue (onechains a ++ [C]) = dec1 a (Z.of_nat (csize C)).
Proof.
  intros a C Hc; induction a as [|a IH].
  - simpl onechains; simpl app; simpl dec1; apply svalue_single_c.
  - assert (Hopt : forall p, In p (selections (onechains (S a) ++ [C])) ->
              svalue_open p = Z.abs (svalue (onechains a ++ [C]) - 1) \/
              svalue_open p = svopen C (svalue (onechains (S a)))).
    { intros p Hp.
      destruct (selections_ones_one (S a) C p Hp)
        as [[Hf [a' [Ha Hs]]] | [Hf Hs]].
      - left; unfold svalue_open; rewrite Hf, Hs.
        injection Ha as Ha; subst a'.
        rewrite svopen_chain1; reflexivity.
      - right; unfold svalue_open; rewrite Hf, Hs; reflexivity. }
    assert (Hin1 : In (Chain 1, onechains a ++ [C])
                      (selections (onechains (S a) ++ [C])))
      by (rewrite onechains_S; simpl app; simpl selections; left; reflexivity).
    assert (HinC : In (C, onechains (S a))
                      (selections (onechains (S a) ++ [C])))
      by apply In_selections_ones_one.
    rewrite (svalue_two_options (onechains (S a) ++ [C])
               (Z.abs (svalue (onechains a ++ [C]) - 1))
               (svopen C (svalue (onechains (S a)))));
      [| apply ones_one_nonnil | exact Hopt | | ].
    + rewrite dec1_S, IH.
      pose proof (open_long_not_better a C Hc) as Hle.
      rewrite IH in Hle; lia.
    + exists (Chain 1, onechains a ++ [C]); split; [exact Hin1|].
      unfold svalue_open; cbn [fst snd]; rewrite svopen_chain1; reflexivity.
    + exists (C, onechains (S a)); split; [exact HinC | reflexivity].
Qed.

(** The two regimes read off the iteration: the component is worn down one box
    at a time, and once it is gone the one-box chains alternate. *)
Corollary svalue_ones_one_le :
  forall a C,
    (2 <= csize C)%nat -> (a <= csize C)%nat ->
    svalue (onechains a ++ [C]) = Z.of_nat (csize C) - Z.of_nat a.
Proof.
  intros a C Hc Ha; rewrite (svalue_ones_one a C Hc).
  assert (Haux : forall k w, 0 <= Z.of_nat k <= w -> dec1 k w = w - Z.of_nat k).
  { induction k as [|k IH]; intros w Hk.
    - simpl dec1; simpl Z.of_nat; lia.
    - rewrite Nat2Z.inj_succ in Hk.
      rewrite dec1_S, (IH w) by lia.
      rewrite Nat2Z.inj_succ, Z.abs_eq by lia; lia. }
  apply Haux; lia.
Qed.

(** And a one-box chain really does change the value: beside a three-chain the
    capped theory reports two where the uncapped one reports nothing. *)
Example svalue_one_three : svalue (onechains 1 ++ [Chain 3]) = 2.
Proof. reflexivity. Qed.

Example svalue_two_ones_three : svalue (onechains 2 ++ [Chain 3]) = 1.
Proof. reflexivity. Qed.

Example svalue_four_ones_three : svalue (onechains 4 ++ [Chain 3]) = 1.
Proof. reflexivity. Qed.

(** ****************************************************************** *)
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

(** ****************************************************************** *)
(** The terminal bonus for the capped recursion.

    Berlekamp's [tb] is eight on a position of loops, six when a loop sits over
    three-chains, and four otherwise. [tb_does_not_transfer] shows
    that classification is wrong once chains of one or two boxes are admitted:
    it sees a chain that is not a three-chain and drops to its default, where
    the true bonus beside a loop is eight.

    The reading that does extend separates two things the 4/6/8 split conflates.
    [maxsh] is twice the largest handout the position holds, which is what the
    controller can hope to end on. [cap] is what the opener can force her down
    to by holding back a long chain: four when some chain has four boxes or
    more, six when some three-chain is there, eight otherwise. The bonus is the
    smaller, and [stb_eq_tb] proves that on every wellformed position this is
    exactly Berlekamp's [tb]. So the definition is not fitted to the short
    cases; it agrees with his everywhere his applies. *)

(** * The two ingredients *)

(** Twice the largest handout in the position. *)
Definition maxsh (G : position) : Z :=
  fold_right (fun C acc => Z.max (2 * Z.of_nat (shand C)) acc) 0 G.

(** A chain of four boxes or more. *)
Definition longchain_b (C : comp) : bool :=
  match C with Chain n => Nat.leb 4 n | Loop _ => false end.

(** What the opener can force the controller down to. *)
Definition cap (G : position) : Z :=
  if existsb longchain_b G then 4
  else if existsb is_3chain_b G then 6
  else 8.

Definition stb (G : position) : Z := Z.min (maxsh G) (cap G).

Definition scval2 (G : position) : Z := scbase G + stb G.

(** * Elementary facts *)

Lemma maxsh_nil : maxsh [] = 0.
Proof. reflexivity. Qed.

Lemma maxsh_cons :
  forall C G, maxsh (C :: G) = Z.max (2 * Z.of_nat (shand C)) (maxsh G).
Proof. reflexivity. Qed.

Lemma maxsh_perm : forall G H, Permutation G H -> maxsh G = maxsh H.
Proof.
  intros G H HP; induction HP.
  - reflexivity.
  - rewrite !maxsh_cons, IHHP; reflexivity.
  - rewrite !maxsh_cons; lia.
  - congruence.
Qed.

Lemma cap_perm : forall G H, Permutation G H -> cap G = cap H.
Proof.
  intros G H HP; unfold cap.
  rewrite (existsb_perm longchain_b _ _ HP), (existsb_perm is_3chain_b _ _ HP).
  reflexivity.
Qed.

Lemma stb_perm : forall G H, Permutation G H -> stb G = stb H.
Proof.
  intros G H HP; unfold stb.
  rewrite (maxsh_perm _ _ HP), (cap_perm _ _ HP); reflexivity.
Qed.

Lemma scval2_perm : forall G H, Permutation G H -> scval2 G = scval2 H.
Proof.
  intros G H HP; unfold scval2.
  rewrite (scbase_perm _ _ HP), (stb_perm _ _ HP); reflexivity.
Qed.

Lemma cap_range : forall G, 4 <= cap G <= 8.
Proof.
  intros G; unfold cap.
  destruct (existsb longchain_b G); [lia|].
  destruct (existsb is_3chain_b G); lia.
Qed.

(** * On wellformed positions this is Berlekamp's bonus *)

(** A wellformed chain has handout two, a wellformed loop handout four. *)
Lemma shand_wf_chain :
  forall n, (3 <= n)%nat -> (shand (Chain n) = 2)%nat.
Proof. intros n Hn; unfold shand, hand; cbn [csize]; lia. Qed.

Lemma shand_wf_loop :
  forall n, (4 <= n)%nat -> (shand (Loop n) = 4)%nat.
Proof. intros n Hn; unfold shand, hand; cbn [csize]; lia. Qed.

(** Every wellformed handout is at most four, so twice it is at most eight. *)
Lemma maxsh_le8 : forall G, wf G -> maxsh G <= 8.
Proof.
  induction G as [|C G IH]; intros Hw; [cbn; lia|].
  assert (HwC : wf_comp C) by (apply (wf_head C G); exact Hw).
  assert (HwG : wf G) by (apply (wf_tail C G); exact Hw).
  rewrite maxsh_cons; specialize (IH HwG).
  destruct C as [k | k].
  - rewrite (shand_wf_chain k HwC); lia.
  - destruct HwC as [H4 _]; rewrite (shand_wf_loop k H4); lia.
Qed.

(** With a loop present the largest handout is four, doubled to eight. *)
Lemma maxsh_of_loop :
  forall G, wf G -> existsb is_loop_b G = true -> maxsh G = 8.
Proof.
  induction G as [|C G IH]; intros Hw He; [discriminate|].
  assert (HwC : wf_comp C) by (apply (wf_head C G); exact Hw).
  assert (HwG : wf G) by (apply (wf_tail C G); exact Hw).
  rewrite maxsh_cons.
  simpl in He; apply orb_true_iff in He; destruct He as [HC | HG].
  - destruct C as [k | k]; [discriminate|].
    destruct HwC as [H4 _]; rewrite (shand_wf_loop k H4).
    pose proof (maxsh_le8 G HwG) as Hle; lia.
  - rewrite (IH HwG HG).
    destruct C as [k | k].
    + rewrite (shand_wf_chain k HwC); lia.
    + destruct HwC as [H4 _]; rewrite (shand_wf_loop k H4); lia.
Qed.

(** With no loop the largest handout is two, doubled to four. *)
Lemma maxsh_no_loop :
  forall G, wf G -> G <> [] -> existsb is_loop_b G = false -> maxsh G = 4.
Proof.
  induction G as [|C G IH]; intros Hw HNil He; [contradiction|].
  assert (HwC : wf_comp C) by (apply (wf_head C G); exact Hw).
  assert (HwG : wf G) by (apply (wf_tail C G); exact Hw).
  simpl in He; apply orb_false_iff in He; destruct He as [HC HG].
  destruct C as [k | k]; [|discriminate].
  rewrite maxsh_cons, (shand_wf_chain k HwC).
  destruct G as [|D G'].
  - rewrite maxsh_nil; lia.
  - rewrite (IH HwG ltac:(discriminate) HG); lia.
Qed.

(** * Chains that are not loops *)

Lemma longchain_not_loop : forall C, longchain_b C = true -> is_loop_b C = false.
Proof. intros [n | n] H; [reflexivity | discriminate]. Qed.

Lemma three_not_loop : forall C, is_3chain_b C = true -> is_loop_b C = false.
Proof. intros [n | n] H; [reflexivity | discriminate]. Qed.

(** A wellformed component that is not a loop is a three-chain or a long
    chain, since its length is at least three. *)
Lemma wf_nonloop_class :
  forall C, wf_comp C -> is_loop_b C = false ->
    is_3chain_b C = true \/ longchain_b C = true.
Proof.
  intros [n | n] Hw Hl; [|discriminate].
  cbn [wf_comp] in Hw.
  destruct n as [|[|[|[|m]]]]; try lia.
  - left; reflexivity.
  - right; unfold longchain_b; apply Nat.leb_le; lia.
Qed.

Lemma forallb_false_of_witness :
  forall (f g : comp -> bool) G,
    existsb g G = true -> (forall C, g C = true -> f C = false) ->
    forallb f G = false.
Proof.
  intros f g G He Himp.
  apply existsb_exists in He; destruct He as [D [HD Hg]].
  destruct (forallb f G) eqn:E; [|reflexivity].
  exfalso; rewrite forallb_forall in E; specialize (E D HD).
  rewrite (Himp D Hg) in E; discriminate.
Qed.

Lemma forallb_false_of_existsb_false :
  forall (f : comp -> bool) C G,
    existsb f (C :: G) = false -> forallb f (C :: G) = false.
Proof.
  intros f C G H; simpl in H |- *.
  apply orb_false_iff in H; destruct H as [HC _]; rewrite HC; reflexivity.
Qed.

(** With no long chain and no three-chain a wellformed position is all
    loops. *)
Lemma no_long_no_three_all_loops :
  forall G, wf G -> existsb longchain_b G = false ->
    existsb is_3chain_b G = false -> forallb is_loop_b G = true.
Proof.
  induction G as [|C G IH]; intros Hw Hl H3; [reflexivity|].
  simpl in Hl, H3 |- *.
  apply orb_false_iff in Hl; destruct Hl as [HlC HlG].
  apply orb_false_iff in H3; destruct H3 as [H3C H3G].
  assert (HwC : wf_comp C) by (apply (wf_head C G); exact Hw).
  destruct (is_loop_b C) eqn:EL.
  - simpl; apply IH; [apply (wf_tail C G); exact Hw | exact HlG | exact H3G].
  - exfalso; destruct (wf_nonloop_class C HwC EL) as [H | H]; congruence.
Qed.

(** And with no long chain every component is a loop or a three-chain, which
    is the condition Berlekamp's six-bonus tests. *)
Lemma no_long_all_loop_or_three :
  forall G, wf G -> existsb longchain_b G = false ->
    forallb (fun C => is_loop_b C || is_3chain_b C)%bool G = true.
Proof.
  induction G as [|C G IH]; intros Hw Hl; [reflexivity|].
  simpl in Hl |- *.
  apply orb_false_iff in Hl; destruct Hl as [HlC HlG].
  assert (HwC : wf_comp C) by (apply (wf_head C G); exact Hw).
  assert (HC : (is_loop_b C || is_3chain_b C)%bool = true).
  { destruct (is_loop_b C) eqn:EL; [reflexivity|].
    destruct (wf_nonloop_class C HwC EL) as [H | H];
      [rewrite H; apply orb_true_r | congruence]. }
  rewrite HC; simpl.
  apply IH; [apply (wf_tail C G); exact Hw | exact HlG].
Qed.

(** A long chain is neither, so it breaks that condition. *)
Lemma long_not_all_loop_or_three :
  forall G, existsb longchain_b G = true ->
    forallb (fun C => is_loop_b C || is_3chain_b C)%bool G = false.
Proof.
  intros G H.
  apply (forallb_false_of_witness _ longchain_b G H).
  intros [n | n] Hg; [|discriminate].
  unfold longchain_b in Hg; apply Nat.leb_le in Hg.
  cbn [is_loop_b is_3chain_b orb].
  destruct n as [|[|[|[|m]]]]; try lia; reflexivity.
Qed.

(** * The bonus restricts to Berlekamp's *)

(** On every wellformed position the two agree, so [stb] is not a new
    convention but the same one read through the handouts. *)
Theorem stb_eq_tb :
  forall G, wf G -> G <> [] -> stb G = tb G.
Proof.
  intros G Hw HNil.
  destruct G as [|C G']; [contradiction|].
  unfold stb, cap; rewrite tb_cons_form.
  destruct (existsb is_loop_b (C :: G')) eqn:EL.
  - rewrite (maxsh_of_loop (C :: G') Hw EL).
    destruct (existsb longchain_b (C :: G')) eqn:ELC.
    + rewrite (forallb_false_of_witness is_loop_b longchain_b _ ELC
                 longchain_not_loop).
      rewrite (long_not_all_loop_or_three _ ELC), andb_false_r; reflexivity.
    + destruct (existsb is_3chain_b (C :: G')) eqn:E3.
      * rewrite (forallb_false_of_witness is_loop_b is_3chain_b _ E3
                   three_not_loop).
        rewrite (no_long_all_loop_or_three _ Hw ELC); reflexivity.
      * rewrite (no_long_no_three_all_loops _ Hw ELC E3); reflexivity.
  - rewrite (maxsh_no_loop (C :: G') Hw ltac:(discriminate) EL).
    rewrite (forallb_false_of_existsb_false is_loop_b C G' EL), andb_false_l.
    destruct (existsb longchain_b (C :: G'));
      [reflexivity
       | destruct (existsb is_3chain_b (C :: G')); reflexivity].
Qed.

(** So the capped controlled value extends Berlekamp's on his own domain. *)
Corollary scval2_eq_cval :
  forall G, wf G -> G <> [] -> scval2 G = cval G.
Proof.
  intros G Hw HNil; unfold scval2, cval.
  rewrite (stb_eq_tb G Hw HNil).
  f_equal.
  clear HNil; induction G as [|C G IH]; [reflexivity|].
  assert (HwC : wf_comp C) by (apply (wf_head C G); exact Hw).
  cbn [scbase cbase]; rewrite (IH (wf_tail C G Hw)).
  unfold sweight, weight; f_equal.
  destruct C as [k | k].
  - rewrite (shand_wf_chain k HwC); reflexivity.
  - destruct HwC as [H4 _]; rewrite (shand_wf_loop k H4); reflexivity.
Qed.

(** ****************************************************************** *)
(** Berlekamp's control bound for the capped recursion, with the true bonus.

    [DotsAndBoxes.cval_le_value] is Berlekamp's bound: the controller who never
    gives up control banks the controlled value. It is stated for [wf]
    positions, and its terminal bonus reads the component names, which is what
    fails once a chain with no handout to spare is admitted. [stb] is the
    replacement and [stb_eq_tb] shows it is Berlekamp's on every wellformed
    position. This section proves the bound for it.

    The induction splits on whether removing the opened component can raise
    the bonus. It usually cannot, and then the controller declines and the
    bound follows from the remainder. When it can, the remainder is forced to
    be chains of at most three boxes, and there the controller takes the
    component whole instead; [svalue_scbase_short] and [svalue_scbase_small]
    supply the two bounds that case needs. *)

(** * Handouts take three values *)

Lemma shand_values :
  forall C, swf_comp C -> (shand C = 1 \/ shand C = 2 \/ shand C = 4)%nat.
Proof.
  intros [n | n] Hw; cbn [swf_comp] in Hw; unfold shand, hand; cbn [csize].
  - destruct (Nat.eq_dec n 1) as [-> | Hne]; [left; reflexivity|].
    right; left; lia.
  - destruct Hw as [H4 _]; right; right; lia.
Qed.

Lemma maxsh_values :
  forall G, swf G -> G <> [] -> maxsh G = 2 \/ maxsh G = 4 \/ maxsh G = 8.
Proof.
  induction G as [|C G IH]; intros Hw HNil; [contradiction|].
  assert (HsC : swf_comp C)
    by (unfold swf in Hw; rewrite Forall_forall in Hw; apply Hw; left; auto).
  assert (HsG : swf G)
    by (unfold swf in Hw |- *; rewrite Forall_forall in Hw |- *;
        intros x Hx; apply Hw; right; exact Hx).
  rewrite maxsh_cons.
  destruct (shand_values C HsC) as [H1 | [H2 | H4]]; rewrite ?H1, ?H2, ?H4.
  - destruct G as [|D G']; [rewrite maxsh_nil; left; reflexivity|].
    destruct (IH HsG ltac:(discriminate)) as [E | [E | E]]; rewrite E; auto.
  - destruct G as [|D G']; [rewrite maxsh_nil; right; left; reflexivity|].
    destruct (IH HsG ltac:(discriminate)) as [E | [E | E]]; rewrite E; auto.
  - destruct G as [|D G']; [rewrite maxsh_nil; right; right; reflexivity|].
    destruct (IH HsG ltac:(discriminate)) as [E | [E | E]]; rewrite E; auto.
Qed.

(** * Small handouts force short components *)

Lemma maxsh_in :
  forall G C, In C G -> 2 * Z.of_nat (shand C) <= maxsh G.
Proof.
  induction G as [|D G IH]; intros C HC; [destruct HC|].
  rewrite maxsh_cons; destruct HC as [<- | HC]; [lia|].
  pose proof (IH C HC); lia.
Qed.

Lemma shortb_of_shand1 :
  forall C, swf_comp C -> (shand C <= 1)%nat -> shortb C = true.
Proof.
  intros [n | n] Hw Hs; cbn [swf_comp] in Hw;
    unfold shand, hand in Hs; cbn [csize] in Hs.
  - assert (Hn : n = 1%nat) by lia.
    subst n; reflexivity.
  - destruct Hw as [H4 _]; lia.
Qed.

Lemma smallb_of_shand2 :
  forall C, swf_comp C -> (shand C <= 2)%nat -> longchain_b C = false ->
    smallb C = true.
Proof.
  intros [n | n] Hw Hs Hl; cbn [swf_comp] in Hw;
    unfold shand, hand in Hs; cbn [csize] in Hs.
  - unfold longchain_b in Hl; apply Nat.leb_gt in Hl.
    unfold smallb; apply andb_true_iff; split; apply Nat.leb_le; lia.
  - destruct Hw as [H4 _]; lia.
Qed.

Lemma maxsh_le2_short :
  forall G, swf G -> maxsh G <= 2 -> forallb shortb G = true.
Proof.
  intros G Hw Hm; rewrite forallb_forall; intros C HC.
  assert (HsC : swf_comp C)
    by (unfold swf in Hw; rewrite Forall_forall in Hw; apply Hw; exact HC).
  pose proof (maxsh_in G C HC) as Hin.
  apply shortb_of_shand1; [exact HsC | lia].
Qed.

Lemma maxsh_le4_small :
  forall G, swf G -> maxsh G <= 4 -> existsb longchain_b G = false ->
    forallb smallb G = true.
Proof.
  intros G Hw Hm Hl; rewrite forallb_forall; intros C HC.
  assert (HsC : swf_comp C)
    by (unfold swf in Hw; rewrite Forall_forall in Hw; apply Hw; exact HC).
  pose proof (maxsh_in G C HC) as Hin.
  assert (HlC : longchain_b C = false).
  { destruct (longchain_b C) eqn:E; [|reflexivity].
    exfalso; assert (Hbad : existsb longchain_b G = true)
      by (apply existsb_exists; exists C; split; assumption).
    congruence. }
  apply smallb_of_shand2; [exact HsC | lia | exact HlC].
Qed.

Lemma smallb_no3_short :
  forall G, forallb smallb G = true -> existsb is_3chain_b G = false ->
    forallb shortb G = true.
Proof.
  induction G as [|C G IH]; intros Hs H3; [reflexivity|].
  simpl in Hs, H3 |- *.
  apply andb_true_iff in Hs; destruct Hs as [HsC HsG].
  apply orb_false_iff in H3; destruct H3 as [H3C H3G].
  assert (HC : shortb C = true).
  { destruct C as [n | n]; [|discriminate].
    pose proof (smallb_chain n HsC) as Hb.
    assert (Hn3 : n <> 3%nat)
      by (intros ->; cbn in H3C; discriminate).
    unfold shortb; apply andb_true_iff; split; apply Nat.leb_le; lia. }
  rewrite HC; simpl; apply IH; assumption.
Qed.

(** * The cap cannot rise when a component is added *)

Lemma cap_cons_le : forall C G, cap (C :: G) <= cap G.
Proof.
  intros C G; unfold cap; simpl.
  destruct (longchain_b C); simpl.
  - destruct (existsb longchain_b G); [lia|].
    destruct (existsb is_3chain_b G); lia.
  - destruct (existsb longchain_b G); [lia|].
    destruct (is_3chain_b C); simpl;
      destruct (existsb is_3chain_b G); lia.
Qed.

Lemma cap_long : forall G, existsb longchain_b G = true -> cap G = 4.
Proof. intros G H; unfold cap; rewrite H; reflexivity. Qed.

Lemma cap_six :
  forall G, existsb longchain_b G = false -> existsb is_3chain_b G = true ->
    cap G = 6.
Proof. intros G H1 H2; unfold cap; rewrite H1, H2; reflexivity. Qed.

(** * When the bonus rises *)

(** A rise forces the opened component to hold a strictly larger handout than
    anything left, and the cap to stay above it. *)
Lemma stb_rise_gaps :
  forall C rest,
    stb rest < stb (C :: rest) ->
    maxsh rest < 2 * Z.of_nat (shand C) /\ maxsh rest < cap (C :: rest).
Proof.
  intros C rest Hlt.
  pose proof (cap_cons_le C rest) as Hcap.
  unfold stb in *; rewrite maxsh_cons in Hlt.
  split.
  - destruct (Z.le_gt_cases (2 * Z.of_nat (shand C)) (maxsh rest)) as [Hle | Hgt];
      [|lia].
    rewrite Z.max_r in Hlt by lia; lia.
  - destruct (Z.le_gt_cases (cap (C :: rest)) (maxsh rest)) as [Hle | Hgt];
      [|lia].
    lia.
Qed.

(** The bound the rise case needs: the controller takes the component whole,
    and what she gives up is covered by the handout she gains. *)
Lemma rise_bound :
  forall C rest,
    swf (C :: rest) -> rest <> [] ->
    stb rest < stb (C :: rest) ->
    svalue rest + scbase rest + stb (C :: rest) <= 2 * Z.of_nat (shand C).
Proof.
  intros C rest Hw HNil Hlt.
  destruct (stb_rise_gaps C rest Hlt) as [Hg1 Hg2].
  assert (HsR : swf rest)
    by (unfold swf in Hw |- *; rewrite Forall_forall in Hw |- *;
        intros x Hx; apply Hw; right; exact Hx).
  assert (Hstb : stb (C :: rest) <= 2 * Z.of_nat (shand C)).
  { unfold stb; rewrite maxsh_cons; lia. }
  destruct (Z.le_gt_cases (maxsh rest) 2) as [Hm2 | Hm2].
  - (* everything left is a one-box chain *)
    pose proof (svalue_scbase_short rest (maxsh_le2_short rest HsR Hm2)); lia.
  - (* the cap is above four, so no long chain is left *)
    assert (Hm4 : maxsh rest <= 4).
    { destruct (maxsh_values rest HsR HNil) as [E | [E | E]]; try lia.
      pose proof (cap_range (C :: rest)); lia. }
    assert (Hmeq : maxsh rest = 4).
    { destruct (maxsh_values rest HsR HNil) as [E | [E | E]]; lia. }
    assert (Hnl : existsb longchain_b (C :: rest) = false).
    { destruct (existsb longchain_b (C :: rest)) eqn:E; [|reflexivity].
      exfalso; rewrite (cap_long _ E) in Hg2; lia. }
    assert (HnlR : existsb longchain_b rest = false)
      by (simpl in Hnl; apply orb_false_iff in Hnl; tauto).
    pose proof (maxsh_le4_small rest HsR Hm4 HnlR) as Hsm.
    destruct (existsb is_3chain_b rest) eqn:E3.
    + (* a three-chain is left, so the cap is six *)
      assert (Hcap6 : cap (C :: rest) = 6).
      { apply cap_six; [exact Hnl|].
        simpl; rewrite E3; apply orb_true_r. }
      assert (HsC : swf_comp C)
        by (unfold swf in Hw; rewrite Forall_forall in Hw; apply Hw;
            left; reflexivity).
      assert (HhC : 2 * Z.of_nat (shand C) = 8).
      { destruct (shand_values C HsC) as [E | [E | E]];
          rewrite E in Hg1 |- *; lia. }
      pose proof (svalue_scbase_small rest Hsm).
      unfold stb; rewrite maxsh_cons; lia.
    + (* none is, so the sharper bound applies *)
      pose proof (svalue_scbase_short rest (smallb_no3_short rest Hsm E3)); lia.
Qed.

(** * The bound *)

Theorem scval2_le_svalue :
  forall G, swf G -> G <> [] -> scval2 G <= svalue G.
Proof.
  assert (Haux : forall n G, (length G <= n)%nat -> swf G -> G <> [] ->
                   scval2 G <= svalue G).
  { induction n as [|n IH]; intros G Hn Hw HNil.
    - exfalso; apply HNil; destruct G; [reflexivity | simpl in Hn; lia].
    - apply svalue_lower_bound; [exact HNil|].
      intros q Hq.
      pose proof (selections_length G q Hq) as Hlen.
      pose proof (selections_perm G q Hq) as Hperm.
      destruct (selections_swf G q Hw Hq) as [HwC Hwr].
      assert (Hsc : scval2 G = scval2 (fst q :: snd q))
        by (rewrite (scval2_perm _ _ Hperm); reflexivity).
      assert (Hsw : swf (fst q :: snd q))
        by (unfold swf; constructor; assumption).
      assert (Hsle : Z.of_nat (shand (fst q)) <= Z.of_nat (csize (fst q)))
        by (pose proof (shand_le_csize (fst q)); lia).
      rewrite Hsc; unfold scval2; cbn [scbase].
      destruct (list_eq_dec comp_eq_dec (snd q) []) as [Hnil | Hrne].
      + (* the last component, taken whole *)
        unfold svalue_open, svopen; rewrite Hnil.
        assert (Hb : stb (fst q :: @nil comp) <= 2 * Z.of_nat (shand (fst q))).
        { unfold stb; rewrite maxsh_cons, maxsh_nil.
          rewrite Z.max_l by lia; apply Z.le_min_l. }
        assert (Hs0 : svalue (@nil comp) = 0) by reflexivity.
        rewrite Hs0.
        eapply Z.le_trans; [| apply Z.le_max_l].
        cbn [scbase]; unfold sweight; lia.
      + assert (Hrec : scval2 (snd q) <= svalue (snd q))
          by (apply IH; [lia | exact Hwr | exact Hrne]).
        destruct (Z.le_gt_cases (stb (fst q :: snd q)) (stb (snd q)))
          as [Hle | Hgt].
        * (* the bonus does not rise: decline and appeal to the rest *)
          unfold svalue_open, svopen.
          eapply Z.le_trans; [| apply Z.le_max_r].
          unfold scval2 in Hrec; unfold sweight; lia.
        * (* the bonus rises: take the component whole *)
          pose proof (rise_bound (fst q) (snd q) Hsw Hrne Hgt)
            as Hrb.
          unfold svalue_open, svopen.
          eapply Z.le_trans; [| apply Z.le_max_l].
          unfold sweight; lia. }
  intros G Hw HNil; apply (Haux (length G)); [lia | exact Hw | exact HNil].
Qed.

(** So on wellformed positions this is exactly Berlekamp's control bound,
    recovered through the handouts rather than the component names. *)
Corollary scval2_le_svalue_wf :
  forall G, wf G -> G <> [] -> cval G <= value G.
Proof.
  intros G Hw HNil.
  rewrite <- (scval2_eq_cval G Hw HNil), <- (svalue_wf G Hw).
  apply scval2_le_svalue; [apply wf_swf; exact Hw | exact HNil].
Qed.

(** ****************************************************************** *)
(** Where the capped control bound is exact.

    [scval2_le_svalue] bounds the capped value below by the capped
    controlled value. Berlekamp and Scott prove the two agree once the
    controlled value reaches two, and [DotsAndBoxes.value_cval_ge2] is that
    theorem for wellformed positions.

    [svalue_step_eq] is the step the agreement rests on: an opening that leaves
    the terminal bonus alone, and leaves behind at least the handout it gives
    away, realises the controlled value exactly. [svalue_scval2_ge2_wf] transfers
    Berlekamp and Scott through [scval2_eq_cval], so only positions
    holding a chain of one or two boxes remain. *)

(** * Declining is the controller's choice once the rest is worth the handout *)

Lemma svopen_decline :
  forall C w, Z.of_nat (shand C) <= w -> svopen C w = sweight C + w.
Proof.
  intros C w H; unfold svopen, sweight.
  rewrite Z.max_r by lia; lia.
Qed.

(** * The step *)

(** An opening that leaves the bonus alone and leaves at least its own handout
    behind realises the capped controlled value. *)
Theorem svalue_step_eq :
  forall G p,
    swf G -> In p (selections G) ->
    stb (fst p :: snd p) = stb (snd p) ->
    Z.of_nat (shand (fst p)) <= scval2 (snd p) ->
    svalue (snd p) = scval2 (snd p) ->
    svalue G = scval2 G.
Proof.
  intros G p Hw Hp Htb Hh Hrec.
  assert (HNil : G <> []) by (intros ->; simpl in Hp; destruct Hp).
  assert (Hperm : Permutation (fst p :: snd p) G)
    by (apply selections_perm; exact Hp).
  apply Z.le_antisymm.
  - (* the named opening is no better than the controlled value *)
    eapply Z.le_trans; [apply (svalue_le_open G p Hp)|].
    unfold svalue_open; rewrite Hrec, (svopen_decline (fst p) _ Hh).
    rewrite <- (scval2_perm _ _ Hperm).
    unfold scval2; cbn [scbase]; lia.
  - apply scval2_le_svalue; [exact Hw | exact HNil].
Qed.

(** * Berlekamp and Scott, transferred *)

(** On wellformed positions the capped theory is the original one, so the
    agreement above two comes across unchanged. *)
Theorem svalue_scval2_ge2_wf :
  forall G, wf G -> G <> [] -> 2 <= scval2 G -> svalue G = scval2 G.
Proof.
  intros G Hw HNil H2.
  rewrite (svalue_wf G Hw), (scval2_eq_cval G Hw HNil).
  rewrite (scval2_eq_cval G Hw HNil) in H2.
  apply value_cval_ge2; [exact Hw | exact H2].
Qed.

(** * Short chains are never large *)

(** A short chain leaves the cap alone, being neither a long chain nor a
    three-chain. *)
Lemma cap_cons_short :
  forall C G, shortb C = true -> cap (C :: G) = cap G.
Proof.
  intros C G H; unfold cap; simpl.
  assert (Hl : longchain_b C = false).
  { destruct C as [n | n]; [|reflexivity].
    pose proof (shortb_chain n H) as Hb.
    unfold longchain_b; apply Nat.leb_gt; lia. }
  assert (H3 : is_3chain_b C = false).
  { destruct C as [n | n]; [|reflexivity].
    pose proof (shortb_chain n H) as Hb.
    destruct n as [|[|[|n]]]; cbn; try reflexivity; lia. }
  rewrite Hl, H3; simpl; reflexivity.
Qed.

(** And its handout is at most four, so it can only raise the largest handout
    from that of a one-box heap. *)
Lemma shand_short_le2 : forall C, shortb C = true -> (shand C <= 2)%nat.
Proof.
  intros [n | n] H; [|discriminate].
  pose proof (shortb_chain n H) as Hb.
  unfold shand, hand; cbn [csize]; lia.
Qed.

(** So opening a short chain leaves the bonus alone whenever what remains
    already holds a handout as large. *)
Theorem stb_cons_short :
  forall C rest,
    shortb C = true ->
    2 * Z.of_nat (shand C) <= maxsh rest ->
    stb (C :: rest) = stb rest.
Proof.
  intros C rest Hs Hm.
  unfold stb; rewrite maxsh_cons, (cap_cons_short C rest Hs).
  rewrite Z.max_r by exact Hm; reflexivity.
Qed.

(** * Every position is wellformed or holds a short chain *)

(** Wellformedness and its relaxation differ only on chains, so a position the
    relaxation admits and [shortb] misses is wellformed outright. *)
Lemma swf_no_short_wf :
  forall G, swf G -> existsb shortb G = false -> wf G.
Proof.
  induction G as [|C G IH]; intros Hw Hs; [constructor|].
  simpl in Hs; apply orb_false_iff in Hs; destruct Hs as [HC HG].
  inversion Hw as [|D E HwC HwG Heq]; subst.
  constructor; [| apply IH; assumption].
  destruct C as [k | k]; [| exact HwC].
  cbn [swf_comp] in HwC; cbn [wf_comp].
  unfold shortb in HC; apply andb_false_iff in HC.
  destruct HC as [H | H]; apply Nat.leb_gt in H; lia.
Qed.

(** * Handouts, and where the largest of them sits *)

Lemma maxsh_ge_of_In :
  forall C G, In C G -> 2 * Z.of_nat (shand C) <= maxsh G.
Proof.
  intros C G; induction G as [|D G IH]; intros HC; [destruct HC|].
  rewrite maxsh_cons; destruct HC as [<- | HC].
  - apply Z.le_max_l.
  - eapply Z.le_trans; [apply IH; exact HC | apply Z.le_max_r].
Qed.

Lemma shand_swf_ge1 : forall C, swf_comp C -> (1 <= shand C)%nat.
Proof.
  intros [n | n] H; cbn [swf_comp] in H.
  - unfold shand, hand; cbn [csize]; lia.
  - destruct H as [H4 _]; unfold shand, hand; cbn [csize]; lia.
Qed.

Lemma selection_rest_In :
  forall G C rest D, In (C, rest) (selections G) -> In D rest -> In D G.
Proof.
  intros G C rest D Hsel HD.
  pose proof (selections_perm G (C, rest) Hsel) as Hp; simpl in Hp.
  apply (Permutation_in _ Hp); simpl; right; exact HD.
Qed.

Lemma swf_of_selection :
  forall G C rest, swf G -> In (C, rest) (selections G) -> swf (C :: rest).
Proof.
  intros G C rest Hw Hsel.
  pose proof (selections_perm G (C, rest) Hsel) as Hp; simpl in Hp.
  unfold swf in Hw |- *; rewrite Forall_forall; intros D HD.
  rewrite Forall_forall in Hw; apply Hw; apply (Permutation_in _ Hp HD).
Qed.

(** * A single component is always exact *)

(** Twice a component's handout never exceeds the cap it sets on its own: a
    chain's is at most four, which is the floor of the cap, and a loop's is
    eight, which is the cap a lone loop leaves. *)
Lemma shand2_le_cap_single :
  forall C, swf_comp C -> 2 * Z.of_nat (shand C) <= cap [C].
Proof.
  intros [n | n] H.
  - pose proof (cap_range [Chain n]) as Hr.
    unfold shand, hand; cbn [csize]; lia.
  - cbn [swf_comp] in H; destruct H as [H4 _].
    assert (Hc : cap [Loop n] = 8) by reflexivity.
    rewrite Hc; unfold shand, hand; cbn [csize]; lia.
Qed.

Lemma stb_single :
  forall C, swf_comp C -> stb [C] = 2 * Z.of_nat (shand C).
Proof.
  intros C H; unfold stb; rewrite maxsh_cons, maxsh_nil.
  rewrite Z.max_l by lia.
  apply Z.min_l, shand2_le_cap_single; exact H.
Qed.

Lemma svalue_single_scval2 :
  forall C, swf_comp C -> svalue [C] = scval2 [C].
Proof.
  intros C H; rewrite svalue_single_c; unfold scval2; cbn [scbase].
  rewrite (stb_single C H); unfold sweight; lia.
Qed.

(** * Choosing which short chain to open *)

Definition chain1b (C : comp) : bool :=
  match C with Chain 1 => true | _ => false end.

Lemma chain1b_shortb : forall C, chain1b C = true -> shortb C = true.
Proof. intros [[|[|n]] | n] H; try discriminate; reflexivity. Qed.

Lemma shand_chain1b : forall C, chain1b C = true -> shand C = 1%nat.
Proof. intros [[|[|n]] | n] H; try discriminate; reflexivity. Qed.

Lemma shand_ge2_of_not_chain1 :
  forall C, swf_comp C -> chain1b C = false -> (2 <= shand C)%nat.
Proof.
  intros [n | n] Hw Hc; cbn [swf_comp] in Hw.
  - destruct n as [|[|n]]; [lia | discriminate |].
    unfold shand, hand; cbn [csize]; lia.
  - destruct Hw as [H4 _]; unfold shand, hand; cbn [csize]; lia.
Qed.

Lemma shand_short_not1 :
  forall C, shortb C = true -> chain1b C = false -> shand C = 2%nat.
Proof.
  intros [n | n] Hs Hc; [|discriminate].
  pose proof (shortb_chain n Hs) as Hb.
  destruct n as [|[|n]]; [lia | discriminate |].
  unfold shand, hand; cbn [csize]; lia.
Qed.

(** Open a one-box chain if there is one, and a two-box chain otherwise. Either
    way what is left holds a handout at least as large as the one given away,
    so the terminal bonus does not move. *)
Lemma short_selection :
  forall G, swf G -> existsb shortb G = true ->
    exists C rest,
      In (C, rest) (selections G) /\ shortb C = true /\
      (rest = [] \/ 2 * Z.of_nat (shand C) <= maxsh rest).
Proof.
  intros G Hw Hs; unfold swf in Hw.
  destruct (existsb chain1b G) eqn:E1.
  - apply existsb_exists in E1; destruct E1 as [C [HinC HC]].
    destruct (In_selections G C HinC) as [rest Hrest].
    exists C, rest; split; [exact Hrest|].
    split; [apply chain1b_shortb; exact HC|].
    destruct rest as [|D rest']; [left; reflexivity | right].
    assert (HinD : In D G)
      by (eapply selection_rest_In; [exact Hrest | left; reflexivity]).
    rewrite Forall_forall in Hw; pose proof (shand_swf_ge1 D (Hw D HinD)) as Hd.
    pose proof (maxsh_ge_of_In D (D :: rest') (or_introl eq_refl)) as Hm.
    rewrite (shand_chain1b C HC); lia.
  - apply existsb_exists in Hs; destruct Hs as [C [HinC HC]].
    assert (H1 : chain1b C = false).
    { destruct (chain1b C) eqn:E; [|reflexivity].
      exfalso; assert (existsb chain1b G = true)
        by (apply existsb_exists; exists C; split; assumption).
      congruence. }
    destruct (In_selections G C HinC) as [rest Hrest].
    exists C, rest; split; [exact Hrest | split; [exact HC|]].
    destruct rest as [|D rest']; [left; reflexivity | right].
    assert (HinD : In D G)
      by (eapply selection_rest_In; [exact Hrest | left; reflexivity]).
    assert (HD1 : chain1b D = false).
    { destruct (chain1b D) eqn:E; [|reflexivity].
      exfalso; assert (existsb chain1b G = true)
        by (apply existsb_exists; exists D; split; assumption).
      congruence. }
    rewrite Forall_forall in Hw.
    pose proof (shand_ge2_of_not_chain1 D (Hw D HinD) HD1) as Hd.
    pose proof (maxsh_ge_of_In D (D :: rest') (or_introl eq_refl)) as Hm.
    rewrite (shand_short_not1 C HC H1); lia.
Qed.

(** * The capped control bound is exact above two *)

(** Berlekamp and Scott's threshold theorem, on every position the board can
    present: chains of one and two boxes included. *)
Theorem svalue_scval2_ge2 :
  forall G, swf G -> G <> [] -> 2 <= scval2 G -> svalue G = scval2 G.
Proof.
  assert (Haux : forall n G, (length G <= n)%nat -> swf G -> G <> [] ->
                   2 <= scval2 G -> svalue G = scval2 G).
  { induction n as [|n IH]; intros G Hlen Hw HNil H2.
    - destruct G as [|C G']; [contradiction | simpl in Hlen; lia].
    - destruct (existsb shortb G) eqn:Es.
      + destruct (short_selection G Hw Es) as [C [rest [Hsel [Hshort Hcase]]]].
        pose proof (selections_perm G (C, rest) Hsel) as Hperm; simpl in Hperm.
        pose proof (swf_of_selection G C rest Hw Hsel) as Hwcr.
        inversion Hwcr as [|D E HwC HwR Heq]; subst.
        destruct Hcase as [Hnil | Hmax].
        * subst rest; apply Permutation_length_1_inv in Hperm; subst G.
          apply svalue_single_scval2; exact HwC.
        * assert (Hnil2 : rest <> []).
          { intros ->; rewrite maxsh_nil in Hmax.
            pose proof (shand_swf_ge1 C HwC); lia. }
          assert (Htb : stb (C :: rest) = stb rest)
            by (apply stb_cons_short; assumption).
          (* the controlled value only rises when the short chain is removed *)
          assert (Hsw : sweight C <= -1)
            by (rewrite (sweight_short C Hshort);
                pose proof (shand_swf_ge1 C HwC);
                pose proof (shand_le_csize C); lia).
          assert (Hsplit : scval2 G = sweight C + scval2 rest).
          { rewrite <- (scval2_perm _ _ Hperm).
            unfold scval2; cbn [scbase]; rewrite Htb; lia. }
          assert (H2r : 2 <= scval2 rest) by lia.
          assert (Hh : Z.of_nat (shand C) <= scval2 rest)
            by (pose proof (shand_short_le2 C Hshort); lia).
          assert (Hlr : (length rest <= n)%nat).
          { apply Permutation_length in Hperm; simpl in Hperm; lia. }
          assert (Hrec : svalue rest = scval2 rest)
            by (apply IH; assumption).
          exact (svalue_step_eq G (C, rest) Hw Hsel Htb Hh Hrec).
      + apply svalue_scval2_ge2_wf;
          [apply (swf_no_short_wf G Hw Es) | exact HNil | exact H2]. }
  intros G Hw HNil H2; exact (Haux (length G) G (Nat.le_refl _) Hw HNil H2).
Qed.

(** ****************************************************************** *)
(** Below the threshold.

    [svalue_scval2_ge2] settles every position whose capped controlled value
    reaches two. Beneath it the value is not a function of the controlled value
    alone, so a classification is needed rather than a formula.

    This section establishes the two invariants that constrain it. Both values
    carry the parity of the board, so they never differ by an odd amount; and
    the terminal bonus is even, which is what puts the parity into the
    controlled value. *)

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

(** ****************************************************************** *)
(** Positions made only of chains of one and two boxes, in closed form.

    These are the positions Berlekamp and Scott's classification does not
    reach, and the ones on which substituting the capped controlled value into
    [DotsAndBoxes.v41] gives the wrong answer. They admit a closed form of
    their own, in the two counts alone.

    Writing [a] for the number of one-box chains and [b] for the two-box
    chains, the value is the parity of [a] when there is a one-box chain, and
    twice the parity of [b] when there is not. A one-box chain forces a
    response worth a single box, so a supply of them reduces the position to a
    parity count; with none, the two-box chains alternate in pairs and an odd
    number of them leaves the controller two.

    The two cases are genuinely distinct: five two-box chains are worth two,
    while the board's own parity would predict nothing. *)

(** * The two kinds of short chain *)

Definition chain2b (C : comp) : bool :=
  match C with Chain 2 => true | _ => false end.

Lemma shortb_cases :
  forall C, shortb C = true -> chain1b C = true \/ chain2b C = true.
Proof.
  intros [n | n] H; [|discriminate].
  pose proof (shortb_chain n H) as Hb.
  destruct n as [|[|[|n]]].
  - lia.
  - left; reflexivity.
  - right; reflexivity.
  - lia.
Qed.

Lemma chain1b_chain2b :
  forall C, chain1b C = true -> chain2b C = false.
Proof. intros [[|[|n]] | n] H; try discriminate; reflexivity. Qed.

Lemma csize_chain1b : forall C, chain1b C = true -> csize C = 1%nat.
Proof. intros [[|[|n]] | n] H; try discriminate; reflexivity. Qed.

Lemma csize_chain2b : forall C, chain2b C = true -> csize C = 2%nat.
Proof. intros [[|[|[|n]]] | n] H; try discriminate; reflexivity. Qed.

Lemma chain2b_shortb : forall C, chain2b C = true -> shortb C = true.
Proof. intros [[|[|[|n]]] | n] H; try discriminate; reflexivity. Qed.

(** * Counting the two kinds *)

Definition c1 (G : position) : nat := length (filter chain1b G).
Definition c2 (G : position) : nat := length (filter chain2b G).

Lemma c1_cons :
  forall C G, c1 (C :: G) = ((if chain1b C then 1 else 0) + c1 G)%nat.
Proof. intros C G; unfold c1; simpl; destruct (chain1b C); reflexivity. Qed.

Lemma c2_cons :
  forall C G, c2 (C :: G) = ((if chain2b C then 1 else 0) + c2 G)%nat.
Proof. intros C G; unfold c2; simpl; destruct (chain2b C); reflexivity. Qed.

Lemma Permutation_filter :
  forall (f : comp -> bool) l l',
    Permutation l l' -> Permutation (filter f l) (filter f l').
Proof.
  intros f l l' H; induction H; simpl.
  - apply perm_nil.
  - destruct (f x); [apply perm_skip|]; assumption.
  - destruct (f x), (f y); try apply perm_swap; apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

Lemma c1_perm : forall G H, Permutation G H -> c1 G = c1 H.
Proof.
  intros G H Hp; unfold c1.
  apply Permutation_length, Permutation_filter; exact Hp.
Qed.

Lemma c2_perm : forall G H, Permutation G H -> c2 G = c2 H.
Proof.
  intros G H Hp; unfold c2.
  apply Permutation_length, Permutation_filter; exact Hp.
Qed.

(** Every component of an all-short position is counted exactly once. *)
Lemma c1_c2_length :
  forall G, forallb shortb G = true -> (c1 G + c2 G)%nat = length G.
Proof.
  induction G as [|C G IH]; intros Hf; [reflexivity|].
  simpl in Hf; apply andb_true_iff in Hf; destruct Hf as [HC HG].
  rewrite c1_cons, c2_cons; simpl length.
  destruct (shortb_cases C HC) as [H1 | H2].
  - rewrite H1, (chain1b_chain2b C H1); pose proof (IH HG); lia.
  - assert (H1 : chain1b C = false).
    { destruct (chain1b C) eqn:E; [|reflexivity].
      rewrite (chain1b_chain2b C E) in H2; discriminate. }
    rewrite H1, H2; pose proof (IH HG); lia.
Qed.

Lemma c1_pos_ex :
  forall G, (1 <= c1 G)%nat -> exists C, In C G /\ chain1b C = true.
Proof.
  intros G H; unfold c1 in H.
  destruct (filter chain1b G) as [|C l] eqn:E; simpl in H; [lia|].
  exists C; apply (proj1 (filter_In chain1b C G)); rewrite E; left; reflexivity.
Qed.

Lemma c2_pos_ex :
  forall G, (1 <= c2 G)%nat -> exists C, In C G /\ chain2b C = true.
Proof.
  intros G H; unfold c2 in H.
  destruct (filter chain2b G) as [|C l] eqn:E; simpl in H; [lia|].
  exists C; apply (proj1 (filter_In chain2b C G)); rewrite E; left; reflexivity.
Qed.

(** * The closed form *)

Definition fshort (a b : nat) : Z :=
  if (a =? 0)%nat then (if Nat.odd b then 2 else 0)
  else (if Nat.odd a then 1 else 0).

Lemma fshort_range : forall a b, 0 <= fshort a b <= 2.
Proof.
  intros a b; unfold fshort.
  destruct (a =? 0)%nat, (Nat.odd b), (Nat.odd a); lia.
Qed.

(** Opening a one-box chain realises the closed form exactly. *)
Lemma cand1_eq :
  forall a b, (1 <= a)%nat ->
    Z.abs (fshort (pred a) b - 1) = fshort a b.
Proof.
  intros a b Ha; destruct a as [|k]; [lia|].
  cbn [pred]; unfold fshort; cbn [Nat.eqb].
  destruct k as [|k'].
  - cbn [Nat.eqb Nat.odd]; destruct (Nat.odd b); reflexivity.
  - cbn [Nat.eqb]; rewrite (odd_S (S k')).
    destruct (Nat.odd (S k')); reflexivity.
Qed.

(** Opening a two-box chain is never better, and is the only option when no
    one-box chain is present. *)
Lemma cand2_ge :
  forall a b, (1 <= b)%nat ->
    fshort a b <= Z.abs (fshort a (pred b) - 2).
Proof.
  intros a b Hb; destruct b as [|k]; [lia|].
  cbn [pred]; unfold fshort; destruct (a =? 0)%nat.
  - rewrite (odd_S k); destruct (Nat.odd k); cbn [negb]; lia.
  - destruct (Nat.odd a); lia.
Qed.

Lemma cand2_eq :
  forall b, (1 <= b)%nat ->
    Z.abs (fshort 0 (pred b) - 2) = fshort 0 b.
Proof.
  intros b Hb; destruct b as [|k]; [lia|].
  cbn [pred]; unfold fshort; cbn [Nat.eqb].
  rewrite (odd_S k); destruct (Nat.odd k); cbn [negb]; reflexivity.
Qed.

(** * Every option of an all-short position is one of two values *)

Lemma allshort_of_selection :
  forall G C rest,
    forallb shortb G = true -> In (C, rest) (selections G) ->
    forallb shortb rest = true /\ shortb C = true.
Proof.
  intros G C rest Hf Hsel.
  pose proof (selections_perm G (C, rest) Hsel) as Hp; simpl in Hp.
  rewrite forallb_forall in Hf.
  split.
  - rewrite forallb_forall; intros D HD.
    apply Hf, (Permutation_in _ Hp); simpl; right; exact HD.
  - apply Hf, (Permutation_in _ Hp); simpl; left; reflexivity.
Qed.

(** * The theorem *)

Theorem svalue_allshort :
  forall G, forallb shortb G = true -> svalue G = fshort (c1 G) (c2 G).
Proof.
  assert (Haux : forall n G, (length G <= n)%nat -> forallb shortb G = true ->
                   svalue G = fshort (c1 G) (c2 G)).
  { induction n as [|n IH]; intros G Hlen Hf.
    - assert (HG : G = []) by (destruct G; simpl in Hlen; [reflexivity | lia]).
      subst G; reflexivity.
    - destruct (list_eq_dec comp_eq_dec G []) as [-> | HNil]; [reflexivity|].
      (* every option is the one-box candidate or the two-box candidate *)
      assert (Hopt : forall C rest, In (C, rest) (selections G) ->
                svalue_open (C, rest) =
                  (if chain1b C
                   then Z.abs (fshort (pred (c1 G)) (c2 G) - 1)
                   else Z.abs (fshort (c1 G) (pred (c2 G)) - 2))).
      { intros C rest Hsel.
        destruct (allshort_of_selection G C rest Hf Hsel) as [Hr HC].
        pose proof (selections_perm G (C, rest) Hsel) as Hp; simpl in Hp.
        pose proof (selections_length G (C, rest) Hsel) as Hl; simpl in Hl.
        assert (Hrec : svalue rest = fshort (c1 rest) (c2 rest))
          by (apply IH; [lia | exact Hr]).
        assert (E1 : c1 G = ((if chain1b C then 1 else 0) + c1 rest)%nat)
          by (rewrite <- (c1_perm _ _ Hp), c1_cons; reflexivity).
        assert (E2 : c2 G = ((if chain2b C then 1 else 0) + c2 rest)%nat)
          by (rewrite <- (c2_perm _ _ Hp), c2_cons; reflexivity).
        unfold svalue_open; cbn [fst snd].
        rewrite (svopen_short C (svalue rest) HC), Hrec.
        destruct (shortb_cases C HC) as [H1 | H2].
        - rewrite H1, (csize_chain1b C H1), (chain1b_chain2b C H1) in *.
          rewrite E1, E2; simpl; reflexivity.
        - assert (H1 : chain1b C = false).
          { destruct (chain1b C) eqn:E; [|reflexivity].
            rewrite (chain1b_chain2b C E) in H2; discriminate. }
          rewrite H1, H2, (csize_chain2b C H2) in *.
          rewrite E1, E2; simpl; reflexivity. }
      (* at least one kind is present *)
      pose proof (c1_c2_length G Hf) as Hsum.
      assert (Hlen1 : (1 <= length G)%nat)
        by (destruct G; [contradiction | simpl; lia]).
      apply Z.le_antisymm.
      + (* the controller opens a one-box chain if there is one *)
        destruct (Nat.eq_dec (c1 G) 0) as [Hz | Hz].
        * assert (Hb : (1 <= c2 G)%nat) by lia.
          destruct (c2_pos_ex G Hb) as [C [HinC HC]].
          destruct (In_selections G C HinC) as [rest Hsel].
          pose proof (svalue_le_open G (C, rest) Hsel) as Hle.
          rewrite (Hopt C rest Hsel) in Hle.
          assert (H1 : chain1b C = false).
          { destruct (chain1b C) eqn:E; [|reflexivity].
            rewrite (chain1b_chain2b C E) in HC; discriminate. }
          rewrite H1, Hz in Hle; rewrite Hz.
          rewrite (cand2_eq (c2 G) Hb) in Hle; exact Hle.
        * assert (Ha : (1 <= c1 G)%nat) by lia.
          destruct (c1_pos_ex G Ha) as [C [HinC HC]].
          destruct (In_selections G C HinC) as [rest Hsel].
          pose proof (svalue_le_open G (C, rest) Hsel) as Hle.
          rewrite (Hopt C rest Hsel), HC in Hle.
          rewrite (cand1_eq (c1 G) (c2 G) Ha) in Hle; exact Hle.
      + (* and no option does better *)
        destruct (svalue_attained G HNil) as [p [Hp Hval]].
        destruct p as [C rest]; rewrite Hval, (Hopt C rest Hp).
        destruct (allshort_of_selection G C rest Hf Hp) as [_ HC].
        destruct (chain1b C) eqn:E1.
        * assert (Ha : (1 <= c1 G)%nat).
          { pose proof (selections_perm G (C, rest) Hp) as Hq; simpl in Hq.
            rewrite <- (c1_perm _ _ Hq), c1_cons, E1; lia. }
          rewrite (cand1_eq (c1 G) (c2 G) Ha); apply Z.le_refl.
        * assert (H2 : chain2b C = true)
            by (destruct (shortb_cases C HC) as [H | H];
                [rewrite H in E1; discriminate | exact H]).
          assert (Hb : (1 <= c2 G)%nat).
          { pose proof (selections_perm G (C, rest) Hp) as Hq; simpl in Hq.
            rewrite <- (c2_perm _ _ Hq), c2_cons, H2; lia. }
          apply (cand2_ge (c1 G) (c2 G) Hb). }
  intros G Hf; exact (Haux (length G) G (Nat.le_refl _) Hf).
Qed.

(** ****************************************************************** *)
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
  rewrite (svopen_alt L y), (svopen_short S _ HS).
  rewrite (svopen_short S y HS), (svopen_alt L _).
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

(** ****************************************************************** *)
(** The short-chain fold in closed form.

    [g] folds the short chains onto the value of what remains. This section
    computes it.

    A one-box chain steps the value by one. Iterated, that is [h1]: it counts
    down to zero and then alternates, so below its reach the answer depends only
    on a parity. [g_a0_closed] identifies the fold of one-box chains with [h1],
    and [h1_mono] is the monotonicity that follows: on arguments of equal
    parity the fold is order preserving.

    The monotonicity is what the decomposition needs, and it holds only while a
    one-box chain is present. Steps of two alone cannot reach odd residues, and
    the corresponding fold is governed modulo four rather than modulo two;
    [h1_mono_fails_by_two] records the failure. *)

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

(** ****************************************************************** *)
(** Pushing a long opening past the short-chain fold.

    The decomposition's lower bound needs the short chains to be foldable
    across a loony opening: folding first and opening after is never dearer
    than opening first and folding after.

    [h1_commute] is that, for the fold of one-box chains. The proof is one step
    of monotonicity followed by one step of exchange, and it needs both sides
    to be comparable first: [h1_parity] and [svopen_parity] show
    the two carry the same parity, which is what licenses [abs_step_mono].

    With [g_collapse] this covers every position holding a one-box
    chain, since there the two-box chains are already two one-box steps. *)

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
  assert (Hs : 0 <= svopen C x) by apply svopen_nonneg.
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
  pose proof (svopen_nonneg C x) as HA0.
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
    assert (Hrhs0 : 0 <= svopen C (g 0 b x)) by apply svopen_nonneg.
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
  assert (Hs : 0 <= svopen C x) by apply svopen_nonneg.
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

(** ****************************************************************** *)
(** Adding a component moves the value by at most its size.

    [svalue_add_abs] is a stability property of the capped value on its own,
    independent of any fold: putting one more component on the table, or taking
    one off, changes the margin by no more than the boxes it holds.

    The upper half needs only the opening that takes the new component. The
    lower half is an induction, and rests on [svopen_lipschitz]: an opening
    never magnifies a difference in what it is played against, because it is a
    distance from the handout and distances are one-Lipschitz. *)

(** * An opening never magnifies a difference *)

Lemma svopen_lipschitz :
  forall D y y', Z.abs (svopen D y - svopen D y') <= Z.abs (y - y').
Proof.
  intros D y y'; rewrite !(svopen_alt D).
  apply (proj2 (Z.abs_le _ _)).
  destruct (Z.abs_spec (y - Z.of_nat (shand D))) as [[H1 E1] | [H1 E1]];
    destruct (Z.abs_spec (y' - Z.of_nat (shand D))) as [[H2 E2] | [H2 E2]];
    destruct (Z.abs_spec (y - y')) as [[H3 E3] | [H3 E3]];
    rewrite E1, E2, E3; lia.
Qed.

(** * Taking the new component is enough for the upper half *)

Lemma svalue_add_le :
  forall C R, svalue (C :: R) <= svalue R + Z.of_nat (csize C).
Proof.
  intros C R.
  eapply Z.le_trans; [apply svalue_le_head|].
  rewrite (svopen_alt C).
  pose proof (svalue_nonneg R) as Hw.
  pose proof (shand_le_csize C) as Hk.
  destruct (Z.abs_spec (svalue R - Z.of_nat (shand C))) as [[H E] | [H E]];
    rewrite E; lia.
Qed.

(** The same opening also bounds the drop, when it is the one taken. *)
Lemma svopen_self_ge :
  forall C w,
    0 <= w -> w - Z.of_nat (csize C) <= svopen C w.
Proof.
  intros C w Hw; rewrite (svopen_alt C).
  pose proof (shand_le_csize C) as Hk.
  destruct (Z.abs_spec (w - Z.of_nat (shand C))) as [[H E] | [H E]];
    rewrite E; lia.
Qed.

(** * The bound *)

Theorem svalue_add_abs :
  forall C R, Z.abs (svalue (C :: R) - svalue R) <= Z.of_nat (csize C).
Proof.
  assert (Haux : forall n C R, (length R <= n)%nat ->
                   Z.abs (svalue (C :: R) - svalue R) <= Z.of_nat (csize C)).
  { induction n as [|n IH]; intros C R Hn.
    - assert (HR : R = []) by (destruct R; simpl in Hn; [reflexivity | lia]).
      subst R; rewrite svalue_single_c.
      assert (Hz : svalue (@nil comp) = 0) by reflexivity.
      rewrite Hz, Z.sub_0_r, Z.abs_eq by lia; lia.
    - apply (proj2 (Z.abs_le _ _)); split; [| pose proof (svalue_add_le C R); lia].
      destruct (svalue_attained (C :: R) ltac:(discriminate)) as [p [Hp Hval]].
      simpl in Hp; destruct Hp as [<- | Hp].
      + (* the new component was the one opened *)
        rewrite Hval; unfold svalue_open; cbn [fst snd].
        pose proof (svopen_self_ge C (svalue R) (svalue_nonneg R)); lia.
      + (* something already there was opened *)
        apply in_map_iff in Hp; destruct Hp as [[D r] [Heq Hq]].
        simpl in Heq; subst p.
        rewrite Hval; unfold svalue_open; cbn [fst snd].
        pose proof (svalue_le_open R (D, r) Hq) as Hle.
        unfold svalue_open in Hle; cbn [fst snd] in Hle.
        pose proof (selections_length R (D, r) Hq) as Hlen; simpl in Hlen.
        assert (Hchain : svopen D (svalue r) - svopen D (svalue (C :: r))
                         <= Z.of_nat (csize C)).
        { pose proof (svopen_lipschitz D (svalue (C :: r)) (svalue r)) as Hlip.
          assert (H1 : svopen D (svalue r) - svopen D (svalue (C :: r))
                       <= Z.abs (svopen D (svalue (C :: r))
                                 - svopen D (svalue r))).
          { destruct (Z.abs_spec (svopen D (svalue (C :: r))
                                  - svopen D (svalue r))) as [[? E] | [? E]];
              rewrite E; lia. }
          assert (H2 : Z.abs (svalue (C :: r) - svalue r) <= Z.of_nat (csize C))
            by (apply IH; lia).
          lia. }
        lia. }
  intros C R; exact (Haux (length R) C R (Nat.le_refl _)).
Qed.

(** The two halves, stated separately for use. *)
Corollary svalue_add_ge :
  forall C R, svalue R - Z.of_nat (csize C) <= svalue (C :: R).
Proof.
  intros C R; pose proof (svalue_add_abs C R) as H.
  destruct (Z.abs_spec (svalue (C :: R) - svalue R)) as [[? E] | [? E]];
    rewrite E in H; lia.
Qed.

(** * The capped value does not depend on the order of components *)

Theorem svalue_perm :
  forall G H, Permutation G H -> svalue G = svalue H.
Proof.
  assert (Haux : forall n G H, (length G <= n)%nat -> Permutation G H ->
                   svalue G <= svalue H).
  { induction n as [|n IH]; intros G H Hn Hp.
    - assert (HG : G = []) by (destruct G; simpl in Hn; [reflexivity | lia]).
      subst G; apply Permutation_nil in Hp; subst H; apply Z.le_refl.
    - destruct (list_eq_dec comp_eq_dec H []) as [-> | HNil].
      + apply Permutation_sym in Hp; apply Permutation_nil in Hp; subst G.
        apply Z.le_refl.
      + destruct (svalue_attained H HNil) as [p [Hq Hval]].
        pose proof (selections_perm H p Hq) as Hph.
        assert (HpG : Permutation (fst p :: snd p) G).
        { eapply Permutation_trans;
            [exact Hph | apply Permutation_sym; exact Hp]. }
        assert (HinG : In (fst p) G)
          by (apply (Permutation_in _ HpG); left; reflexivity).
        destruct (In_selections G (fst p) HinG) as [rest' Hsel'].
        pose proof (selections_perm G (fst p, rest') Hsel') as HpG';
          simpl in HpG'.
        assert (Hrr : Permutation (snd p) rest').
        { apply (Permutation_cons_inv (a := fst p)).
          eapply Permutation_trans;
            [exact HpG | apply Permutation_sym; exact HpG']. }
        assert (Hlen : (length (snd p) <= n)%nat).
        { pose proof (selections_length H p Hq) as Hl.
          apply Permutation_length in Hp; lia. }
        assert (Heq : svalue (snd p) = svalue rest').
        { apply Z.le_antisymm.
          - apply (IH (snd p) rest'); [lia | exact Hrr].
          - apply (IH rest' (snd p));
              [apply Permutation_length in Hrr; lia
               | apply Permutation_sym; exact Hrr]. }
        rewrite Hval.
        eapply Z.le_trans; [apply (svalue_le_open G (fst p, rest') Hsel')|].
        unfold svalue_open; cbn [fst snd]; rewrite Heq; apply Z.le_refl. }
  intros G H Hp; apply Z.le_antisymm.
  - apply (Haux (length G)); [lia | exact Hp].
  - apply (Haux (length H)); [lia | apply Permutation_sym; exact Hp].
Qed.

(** ****************************************************************** *)
(** The long opening never beats the fold.

    [long_option_ge] is the lower bound the decomposition rests on: opening a
    loony component of the long part is never cheaper than folding the short
    chains onto the long part's own value.

    The two cases are proved differently, and have to be. With a one-box chain
    present the fold collapses onto [h1], which is order preserving
    on arguments of equal parity, so monotonicity and then commutation suffice.
    With only two-box chains the fold is not order preserving and that route is
    unavailable; what closes it instead is [svalue_add_ge], since the
    one configuration that would break the bound needs a four-loop whose
    removal raises the value by more than its own size. *)

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
      assert (Hrhs0 : 0 <= svopen C (g 0 b x)) by apply svopen_nonneg.
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
    assert (Hs : 0 <= svopen C x) by apply svopen_nonneg.
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

(** ****************************************************************** *)
(** The closed form, for every position the board can present.

    [svalue_split] separates the chains of one and two boxes from
    the rest, and what remains is wellformed, so Berlekamp and Scott's
    classification computes it. Composing the two gives a closed form on
    positions their theory does not reach: fold the short chains onto
    [DotsAndBoxes.v41] of the loony part.

    [svalue_closed] is that composition. [svalue_closed_wf] checks it against
    the original theory, where it must and does agree. *)

(** * The loony part, by the existing classification *)

Definition vlong (L : position) : Z :=
  match L with [] => 0 | C :: R => v41 (C :: R) end.

Definition sv (G : position) : Z :=
  g (c1 G) (c2 G) (vlong (longpart G)).

(** * The closed form *)

Theorem svalue_closed : forall G, swf G -> svalue G = sv G.
Proof.
  intros G Hw; rewrite (svalue_split G Hw); unfold sv; f_equal.
  assert (Hlw : wf (longpart G)) by (apply longpart_wf; exact Hw).
  destruct (longpart G) as [|C L] eqn:E; [reflexivity|].
  assert (Hcons : wf (C :: L)) by exact Hlw.
  cbn [vlong]; rewrite (svalue_wf _ Hcons).
  apply value_complete; [exact Hcons | discriminate].
Qed.

(** * Agreement with the original theory *)

(** On a wellformed position there are no short chains, the fold is empty, and
    the closed form is Berlekamp and Scott's. *)
Corollary svalue_closed_wf :
  forall G, wf G -> G <> [] -> value G = v41 G.
Proof.
  intros G Hw HNil; apply value_complete; assumption.
Qed.

Corollary sv_wf :
  forall G, wf G -> G <> [] -> sv G = v41 G.
Proof.
  intros G Hw HNil; unfold sv.
  assert (Hns : existsb shortb G = false).
  { apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [C [HinC HCs]].
    unfold wf in Hw; rewrite Forall_forall in Hw.
    specialize (Hw C HinC); destruct C as [n | n]; [|discriminate].
    pose proof (shortb_chain n HCs) as Hb; cbn [wf_comp] in Hw; lia. }
  assert (Ha : c1 G = 0%nat).
  { unfold c1; destruct (filter chain1b G) as [|C l] eqn:Ef; [reflexivity|].
    exfalso; assert (HinC : In C (filter chain1b G))
      by (rewrite Ef; left; reflexivity).
    apply filter_In in HinC; destruct HinC as [Hin Hc].
    assert (existsb shortb G = true)
      by (apply existsb_exists; exists C; split;
          [exact Hin | apply chain1b_shortb; exact Hc]).
    congruence. }
  assert (Hb : c2 G = 0%nat).
  { unfold c2; destruct (filter chain2b G) as [|C l] eqn:Ef; [reflexivity|].
    exfalso; assert (HinC : In C (filter chain2b G))
      by (rewrite Ef; left; reflexivity).
    apply filter_In in HinC; destruct HinC as [Hin Hc].
    assert (existsb shortb G = true)
      by (apply existsb_exists; exists C; split;
          [exact Hin | apply chain2b_shortb; exact Hc]).
    congruence. }
  rewrite Ha, Hb, g_00, (longpart_id G Hns).
  destruct G as [|C R]; [contradiction | reflexivity].
Qed.

(** So the closed form strictly extends the original: it agrees wherever that
    applies, and computes the rest. *)
Theorem svalue_closed_extends :
  forall G, wf G -> G <> [] -> value G = sv G.
Proof.
  intros G Hw HNil.
  rewrite (sv_wf G Hw HNil); apply value_complete; assumption.
Qed.

(** ****************************************************************** *)
(** Which component to open, when a short chain is present.

    Allcock's standard move opens a three-chain if there is one. Below that
    length the same shape holds: on any position holding a chain of one or two
    boxes, one of those chains is an optimal opening.

    It follows from [svalue_split]. The value is the short-chain
    fold applied to the loony part, the fold is a minimum over the two kinds of
    short chain, and each of those is realised by opening one. So the minimum
    is attained by a short chain and nothing longer improves on it. *)

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

(** ****************************************************************** *)
(** The controller's tests, for the capped recursion.

    [DotsAndBoxes.value_gt4_iff] is Allcock's Theorem 1.4: an endgame is worth
    more than four exactly when its controlled value is. Half of it is the
    control bound and carries over at once. The other half asks that a
    controlled value of at most four caps the endgame at four, and the argument
    behind it does not: the classification it appeals to is stated for
    wellformed positions.

    What replaces it is the decomposition. [g_le_shift] bounds the short-chain
    fold by what it started from less the boxes it hands over, and
    [tb_longpart_le_stb] shows the long part's terminal bonus never exceeds the
    whole position's. Together they cap the value at four, and
    [svalue_gt4_iff] is Theorem 1.4 on every position the board can present. *)

(** * The fold gives away what it is handed *)

Theorem g_le_shift :
  forall a b w,
    0 <= w -> g a b w <= Z.max (w - (Z.of_nat a + 2 * Z.of_nat b)) 2.
Proof.
  intros a b w Hw.
  remember (a + b)%nat as n eqn:En; revert a b w Hw En.
  induction n as [|n IH]; intros a b w Hw En.
  - assert (Ha : a = 0%nat) by lia; assert (Hb : b = 0%nat) by lia; subst.
    rewrite g_00; cbn [Z.of_nat]; lia.
  - destruct a as [|a']; destruct b as [|b'].
    + rewrite g_00; cbn [Z.of_nat]; lia.
    + rewrite g_0b.
      assert (Hrec : g 0 b' w <= Z.max (w - (Z.of_nat 0 + 2 * Z.of_nat b')) 2)
        by (apply (IH 0%nat b' w Hw); lia).
      assert (Hpos : 0 <= g 0 b' w) by (apply g_nonneg; exact Hw).
      destruct (Z.abs_spec (g 0 b' w - 2)) as [[? E] | [? E]]; rewrite E; lia.
    + rewrite g_a0.
      assert (Hrec : g a' 0 w <= Z.max (w - (Z.of_nat a' + 2 * Z.of_nat 0)) 2)
        by (apply (IH a' 0%nat w Hw); lia).
      assert (Hpos : 0 <= g a' 0 w) by (apply g_nonneg; exact Hw).
      destruct (Z.abs_spec (g a' 0 w - 1)) as [[? E] | [? E]]; rewrite E; lia.
    + rewrite g_ab.
      assert (Hrec : g a' (S b') w
                     <= Z.max (w - (Z.of_nat a' + 2 * Z.of_nat (S b'))) 2)
        by (apply (IH a' (S b') w Hw); lia).
      assert (Hpos : 0 <= g a' (S b') w) by (apply g_nonneg; exact Hw).
      eapply Z.le_trans; [apply Z.le_min_l|].
      destruct (Z.abs_spec (g a' (S b') w - 1)) as [[? E] | [? E]];
        rewrite E; lia.
Qed.

(** * The long part carries the smaller terminal bonus *)

Lemma existsb_longpart :
  forall (f : comp -> bool),
    (forall C, shortb C = true -> f C = false) ->
    forall G, existsb f (longpart G) = existsb f G.
Proof.
  intros f Hf G; induction G as [|C G IH]; [reflexivity|].
  destruct (shortb C) eqn:E.
  - rewrite (longpart_short C G E); cbn [existsb].
    rewrite (Hf C E), IH; reflexivity.
  - rewrite (longpart_long C G E); cbn [existsb]; rewrite IH; reflexivity.
Qed.

Lemma cap_longpart : forall G, cap (longpart G) = cap G.
Proof.
  intros G; unfold cap.
  rewrite (existsb_longpart longchain_b), (existsb_longpart is_3chain_b);
    [reflexivity | | ].
  - intros [k | k] H; [|reflexivity].
    pose proof (shortb_chain k H) as Hb.
    destruct k as [|[|[|k]]]; cbn; solve [reflexivity | lia].
  - intros [k | k] H; [|reflexivity].
    pose proof (shortb_chain k H) as Hb.
    unfold longchain_b; apply Nat.leb_gt; lia.
Qed.

Lemma maxsh_longpart_le : forall G, maxsh (longpart G) <= maxsh G.
Proof.
  induction G as [|C G IH]; [cbn; lia|].
  destruct (shortb C) eqn:E.
  - rewrite (longpart_short C G E), maxsh_cons; lia.
  - rewrite (longpart_long C G E), !maxsh_cons; lia.
Qed.

Lemma stb_longpart_le : forall G, stb (longpart G) <= stb G.
Proof.
  intros G; unfold stb; rewrite cap_longpart.
  pose proof (maxsh_longpart_le G); lia.
Qed.

(** So the bonus the wellformed part is entitled to is one the whole position
    can pay. *)
Theorem tb_longpart_le_stb :
  forall G, swf G -> longpart G <> [] -> tb (longpart G) <= stb G.
Proof.
  intros G Hw HNil.
  rewrite <- (stb_eq_tb (longpart G) (longpart_wf G Hw) HNil).
  apply stb_longpart_le.
Qed.

(** * The short chains hand over exactly their own boxes *)

Lemma scbase_longpart :
  forall G,
    scbase G = scbase (longpart G) - (Z.of_nat (c1 G) + 2 * Z.of_nat (c2 G)).
Proof.
  induction G as [|C G IH]; [cbn; lia|].
  rewrite c1_cons, c2_cons.
  destruct (shortb C) eqn:E.
  - rewrite (longpart_short C G E); cbn [scbase].
    rewrite (sweight_short C E).
    destruct (shortb_cases C E) as [H1 | H2].
    + rewrite H1, (chain1b_chain2b C H1), (csize_chain1b C H1).
      cbn [Nat.add]; rewrite Nat2Z.inj_succ; lia.
    + assert (H1 : chain1b C = false).
      { destruct (chain1b C) eqn:Ec; [|reflexivity].
        rewrite (chain1b_chain2b C Ec) in H2; discriminate. }
      rewrite H1, H2, (csize_chain2b C H2).
      cbn [Nat.add]; rewrite Nat2Z.inj_succ; lia.
  - rewrite (longpart_long C G E); cbn [scbase].
    assert (H1 : chain1b C = false).
    { destruct (chain1b C) eqn:Ec; [|reflexivity].
      rewrite (chain1b_shortb C Ec) in E; discriminate. }
    assert (H2 : chain2b C = false).
    { destruct (chain2b C) eqn:Ec; [|reflexivity].
      rewrite (chain2b_shortb C Ec) in E; discriminate. }
    rewrite H1, H2; cbn [Nat.add]; lia.
Qed.

(** * The capped base is Berlekamp's on a wellformed position *)

Lemma scbase_wf : forall G, wf G -> scbase G = cbase G.
Proof.
  induction G as [|C G IH]; intros Hw; [reflexivity|].
  assert (HwC : wf_comp C) by (apply (wf_head C G); exact Hw).
  cbn [scbase cbase]; rewrite (IH (wf_tail C G Hw)).
  unfold sweight, weight; f_equal.
  destruct C as [k | k].
  - rewrite (shand_wf_chain k HwC); reflexivity.
  - destruct HwC as [H4 _]; rewrite (shand_wf_loop k H4); reflexivity.
Qed.

(** * A controlled value of at most four caps the endgame at four *)

Theorem svalue_le4_of_scval2_le4 :
  forall G, swf G -> scval2 G <= 4 -> svalue G <= 4.
Proof.
  intros G Hw Hc.
  rewrite (svalue_closed G Hw); unfold sv.
  destruct (longpart G) as [|C L'] eqn:EL.
  - (* nothing loony is left, so the fold starts from nothing *)
    cbn [vlong].
    pose proof (g_le_shift (c1 G) (c2 G) 0 ltac:(lia)) as Hb; lia.
  - (* what is loony is wellformed, so its closed form is the value *)
    assert (HwL : wf (C :: L')) by (rewrite <- EL; apply longpart_wf; exact Hw).
    assert (HLnil : (C :: L') <> []) by discriminate.
    assert (Hv : vlong (C :: L') = value (C :: L'))
      by (cbn [vlong]; symmetry; apply value_complete; assumption).
    assert (Hnn : 0 <= vlong (C :: L'))
      by (rewrite Hv; apply value_nonneg; exact HwL).
    assert (Hbnd : vlong (C :: L')
                   <= 4 + (Z.of_nat (c1 G) + 2 * Z.of_nat (c2 G))).
    { destruct (Z_le_gt_dec 2 (cval (C :: L'))) as [Hge2 | Hlt2].
      - (* the long part is its own controlled value, and that is bounded *)
        assert (Hcv : vlong (C :: L') = cval (C :: L'))
          by (rewrite Hv; apply value_cval_ge2; assumption).
        assert (Hsb : scbase (C :: L') = scbase G
                      + (Z.of_nat (c1 G) + 2 * Z.of_nat (c2 G))).
        { pose proof (scbase_longpart G) as H; rewrite EL in H; lia. }
        assert (Htb : tb (C :: L') <= stb G).
        { rewrite <- EL; apply tb_longpart_le_stb;
            [exact Hw | rewrite EL; discriminate]. }
        assert (Hcb : cval (C :: L') = scbase (C :: L') + tb (C :: L'))
          by (unfold cval; rewrite (scbase_wf _ HwL); reflexivity).
        unfold scval2 in Hc; lia.
      - (* or it is below the threshold, where four is the ceiling *)
        cbn [vlong]; pose proof (v41_le4 (C :: L') ltac:(lia)); lia. }
    pose proof (g_le_shift (c1 G) (c2 G) (vlong (C :: L')) Hnn) as Hb; lia.
Qed.

(** Allcock's Theorem 1.4, on every position the board can present: an endgame
    is worth more than four exactly when its controlled value is. *)
Theorem svalue_gt4_iff :
  forall G, swf G -> (4 < svalue G <-> 4 < scval2 G).
Proof.
  intros G Hw; split.
  - intros H.
    destruct (Z_le_gt_dec (scval2 G) 4) as [Hle | Hgt]; [|lia].
    exfalso; pose proof (svalue_le4_of_scval2_le4 G Hw Hle); lia.
  - intros H.
    destruct (list_eq_dec comp_eq_dec G []) as [-> | HNil].
    + unfold scval2, stb, maxsh, cap in H; cbn in H; lia.
    + rewrite (svalue_scval2_ge2 G Hw HNil ltac:(lia)); exact H.
Qed.

(** So the controller's loop test reads off the capped controlled value, just
    as Berlekamp's does off his. *)
Corollary keep_control_loop_iff_short :
  forall G, swf G -> (4 < svalue G <-> 4 < scval2 G).
Proof. exact svalue_gt4_iff. Qed.

(** * The fold, when a one-box chain is present *)

(** With a one-box chain in hand the two-box chains are already two one-box
    steps, so the whole fold collapses to [h1] and the closed form is read off
    a single index. *)
Theorem sv_collapse_one :
  forall G,
    swf G -> (1 <= c1 G)%nat ->
    sv G = h1 (Z.of_nat (c1 G) + 2 * Z.of_nat (c2 G)) (vlong (longpart G)).
Proof.
  intros G Hw Ha; unfold sv.
  assert (Hnn : 0 <= vlong (longpart G)).
  { destruct (longpart G) as [|C L'] eqn:EL; [cbn; lia|].
    assert (HwL : wf (C :: L')) by (rewrite <- EL; apply longpart_wf; exact Hw).
    cbn [vlong]; rewrite <- (value_complete (C :: L') HwL ltac:(discriminate)).
    apply value_nonneg; exact HwL. }
  apply g_collapse; [exact Ha | exact Hnn].
Qed.
