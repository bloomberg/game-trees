(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

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

Import ListNotations.

Open Scope Z_scope.

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

Lemma odd_S : forall k, Nat.odd (S k) = negb (Nat.odd k).
Proof. intros k; rewrite Nat.odd_succ, Nat.negb_odd; reflexivity. Qed.

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
