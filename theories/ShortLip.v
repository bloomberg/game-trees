(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Adding a component moves the value by at most its size.

    [svalue_add_abs] is a stability property of the capped value on its own,
    independent of any fold: putting one more component on the table, or taking
    one off, changes the margin by no more than the boxes it holds.

    The upper half needs only the opening that takes the new component. The
    lower half is an induction, and rests on [svopen_lipschitz]: an opening
    never magnifies a difference in what it is played against, because it is a
    distance from the handout and distances are one-Lipschitz. *)

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

Import ListNotations.

Open Scope Z_scope.

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

(** And the form the decomposition needs: removing a component from a position
    cannot raise its value by more than the component's size. *)
Corollary svalue_remove_ge :
  forall G C rest,
    In (C, rest) (selections G) ->
    svalue rest - Z.of_nat (csize C) <= svalue G.
Proof.
  intros G C rest Hsel.
  pose proof (selections_perm G (C, rest) Hsel) as Hp; simpl in Hp.
  pose proof (svalue_add_ge C rest) as H.
  rewrite <- (svalue_perm _ _ Hp); exact H.
Qed.
