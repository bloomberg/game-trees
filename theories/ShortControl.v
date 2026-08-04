(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Berlekamp's control bound for the capped recursion, and case (iii).

    [DotsAndBoxes.cval_le_value] is the control bound: the controller who never
    gives up control banks the controlled value, so it is a lower bound on the
    value. It is stated for [wf] positions only, and its terminal bonus reads
    the shape of the whole position, which is what fails once a chain of one or
    two boxes is admitted: those have no handout to leave.

    [scval_le_svalue] is the bound for the capped recursion, on every [swf]
    position. Its terminal bonus is the smallest handout the position holds,
    doubled, which is what the opener can always force the controller to end
    on. It is weaker than Berlekamp's on the positions both cover, and it is
    exact on a single component.

    [case_iii_only34] settles case (iii) of Allcock's Theorem 1.1 on the
    positions of three-chains and four-loops, where the closed form is the
    table of [value_mix]. *)

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

(** * The capped weight and terminal bonus *)

(** What a component is worth to the controller who declines it. *)
Definition sweight (C : comp) : Z :=
  Z.of_nat (csize C) - 2 * Z.of_nat (shand C).

Fixpoint scbase (G : position) : Z :=
  match G with [] => 0 | C :: r => sweight C + scbase r end.

(** The handout a component offers, doubled: what the controller gains by
    taking it whole instead of declining it. *)
Definition hb (C : comp) : Z := 2 * Z.of_nat (shand C).

Lemma hb_le8 : forall C, hb C <= 8.
Proof.
  intros C; unfold hb, shand.
  pose proof (Nat.le_min_l (hand C) (csize C)) as H.
  assert (Hh : (hand C <= 4)%nat) by (destruct C; simpl hand; lia).
  lia.
Qed.

Lemma hb_nonneg : forall C, 0 <= hb C.
Proof. intros C; unfold hb; lia. Qed.

(** The opener chooses which component is left for last, so the controller can
    count on no more than the smallest handout the position holds. *)
Definition smin (G : position) : Z :=
  fold_right (fun C acc => Z.min (hb C) acc) 8 G.

Lemma smin_nil : smin [] = 8.
Proof. reflexivity. Qed.

Lemma smin_cons : forall C G, smin (C :: G) = Z.min (hb C) (smin G).
Proof. reflexivity. Qed.

Lemma smin_single : forall C, smin [C] = hb C.
Proof.
  intros C; rewrite smin_cons, smin_nil.
  pose proof (hb_le8 C); lia.
Qed.

Lemma smin_le_tail : forall C G, smin (C :: G) <= smin G.
Proof. intros C G; rewrite smin_cons; apply Z.le_min_r. Qed.

Lemma smin_perm : forall G H, Permutation G H -> smin G = smin H.
Proof.
  intros G H HP; induction HP.
  - reflexivity.
  - rewrite !smin_cons, IHHP; reflexivity.
  - rewrite !smin_cons; lia.
  - congruence.
Qed.

Lemma scbase_perm : forall G H, Permutation G H -> scbase G = scbase H.
Proof.
  intros G H HP; induction HP; simpl; try lia; congruence.
Qed.

(** The capped controlled value. *)
Definition scval (G : position) : Z := scbase G + smin G.

Lemma scval_single : forall C, scval [C] = Z.of_nat (csize C).
Proof.
  intros C; unfold scval; simpl scbase; rewrite smin_single.
  unfold sweight, hb; lia.
Qed.

Lemma selections_scbase :
  forall G p, In p (selections G) -> scbase G = sweight (fst p) + scbase (snd p).
Proof.
  intros G p Hp.
  rewrite <- (scbase_perm _ _ (selections_perm G p Hp)); reflexivity.
Qed.

Lemma selections_smin :
  forall G p,
    In p (selections G) -> smin G = Z.min (hb (fst p)) (smin (snd p)).
Proof.
  intros G p Hp.
  rewrite <- (smin_perm _ _ (selections_perm G p Hp)), smin_cons; reflexivity.
Qed.

(** * The bound *)

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

(** The control bound for the capped recursion: on every position of chains of
    any length and loops, the controller who keeps control banks at least the
    capped controlled value. *)
Theorem scval_le_svalue :
  forall G, swf G -> G <> [] -> scval G <= svalue G.
Proof.
  assert (Haux : forall n G, (length G <= n)%nat -> swf G -> G <> [] ->
                   scval G <= svalue G).
  { induction n as [|n IH]; intros G Hn Hw HNil.
    - exfalso; apply HNil; destruct G; [reflexivity | simpl in Hn; lia].
    - apply svalue_lower_bound; [exact HNil|].
      intros q Hq.
      pose proof (selections_length G q Hq) as Hlen.
      pose proof (selections_scbase G q Hq) as Hcb.
      pose proof (selections_smin G q Hq) as Hsm.
      destruct (selections_swf G q Hw Hq) as [HwC Hwr].
      assert (Hsle : Z.of_nat (shand (fst q)) <= Z.of_nat (csize (fst q)))
        by (pose proof (shand_le_csize (fst q)); lia).
      destruct (list_eq_dec comp_eq_dec (snd q) []) as [Hnil | Hrne].
      + (* the opened component is the last one, and is taken whole *)
        assert (Hs0 : svalue (snd q) = 0)
          by (rewrite Hnil; reflexivity).
        assert (Hsm' : smin G = hb (fst q)).
        { rewrite Hsm, Hnil, smin_nil.
          pose proof (hb_le8 (fst q)); lia. }
        assert (Hcb' : scbase G = sweight (fst q))
          by (rewrite Hcb, Hnil; simpl scbase; lia).
        unfold svalue_open, svopen; rewrite Hs0.
        eapply Z.le_trans; [| apply Z.le_max_l].
        unfold scval; rewrite Hcb', Hsm'; unfold sweight, hb; lia.
      + (* otherwise decline it and appeal to what is left *)
        assert (Hrec : scval (snd q) <= svalue (snd q))
          by (apply IH; [lia | exact Hwr | exact Hrne]).
        assert (Hmin : smin G <= smin (snd q))
          by (rewrite Hsm; apply Z.le_min_r).
        unfold svalue_open, svopen.
        eapply Z.le_trans; [| apply Z.le_max_r].
        unfold scval in Hrec |- *; unfold sweight in Hcb; lia. }
  intros G Hw HNil; apply (Haux (length G)); [lia | exact Hw | exact HNil].
Qed.

(** The bound is attained on a single component, so it is not slack
    everywhere. *)
Corollary scval_tight_single :
  forall C, swf_comp C -> scval [C] = svalue [C].
Proof.
  intros C _; rewrite scval_single.
  assert (H : svalue [C] = svopen C (svalue []))
    by (rewrite svalue_cons; reflexivity).
  assert (Hn : svalue (@nil comp) = 0) by reflexivity.
  rewrite H, Hn; unfold svopen.
  assert (Hz : 0 <= Z.of_nat (shand C)) by lia.
  rewrite Z.max_l by lia; lia.
Qed.

(** And it is a genuine bound where the uncapped theory cannot speak: a one-box
    chain beside a three-chain. *)
Example scval_short_instance :
  scval [Chain 1; Chain 3] = 0 /\ svalue [Chain 1; Chain 3] = 2.
Proof. split; reflexivity. Qed.

(** * Case (iii) on positions of three-chains and four-loops *)

(** Where the position is one three-chain among four-loops, opening a four-loop
    attains the value, so it is an optimal opening. This is case (iii) of
    Allcock's Theorem 1.1 restricted to the family the table of [value_mix]
    covers. *)
Theorem case_iii_only34 :
  forall f rest,
    In (Loop 4, rest) (selections (mix 1 (S f))) ->
    value_open (Loop 4, rest) = value (mix 1 (S f)) /\
    (forall q, In q (selections (mix 1 (S f))) ->
       value_open (Loop 4, rest) <= value_open q).
Proof.
  intros f rest Hsel.
  destruct (selections_mix 1 (S f) (Loop 4, rest) Hsel)
    as [[Hc _] | [_ [f' [Hf Hperm]]]]; [cbn [fst] in Hc; discriminate|].
  cbn [snd] in Hperm; injection Hf as Hf; subst f'.
  assert (Hv : value rest = v36 1 f)
    by (rewrite (value_perm rest (mix 1 f) Hperm); apply value_mix).
  assert (Hop : value_open (Loop 4, rest) = value (mix 1 (S f))).
  { unfold value_open; cbn [fst snd]; rewrite Hv, vopen_loop4, value_mix.
    change (v36 1 f) with (if Nat.even f then 3 else 1).
    change (v36 1 (S f)) with (if Nat.even (S f) then 3 else 1).
    rewrite even_S; destruct (Nat.even f); reflexivity. }
  assert (HNil : mix 1 (S f) <> []) by (apply mix_nonnil; simpl; lia).
  split; [exact Hop|].
  apply (proj1 (opener_optimal_iff _ _ HNil Hsel)); symmetry; exact Hop.
Qed.

(** Opening the three-chain instead is strictly worse as soon as a four-loop is
    there, which is why case (iii) departs from the standard move. *)
Theorem case_iii_chain_worse :
  forall f rest,
    In (Chain 3, rest) (selections (mix 1 (S f))) ->
    value (mix 1 (S f)) <= value_open (Chain 3, rest).
Proof.
  intros f rest Hsel; apply value_le_open; exact Hsel.
Qed.

(** On the smallest instance the gap is visible: one three-chain and one
    four-loop is worth one, opening the loop attains it, and opening the chain
    costs two more. *)
Example case_iii_smallest :
  value (mix 1 1) = 1 /\
  value_open (Loop 4, [Chain 3]) = 1 /\
  value_open (Chain 3, [Loop 4]) = 3.
Proof. repeat split; reflexivity. Qed.
