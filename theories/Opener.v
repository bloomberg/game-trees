(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Two further cases of Allcock's Theorem 1.1, and the short chain families.

    [DotsAndBoxes] proves case (i) of Theorem 1.1 and the criterion
    [open_optimal_of_step] behind it, and leaves the rest checked position by
    position. [open_4loop_optimal] settles the regime of case (ii): where a
    four-loop sits beside a component that is neither a three-chain nor a
    four-loop, and the controlled value is at least minus two, opening the
    four-loop is optimal. [open_3chain_optimal] settles the standard move
    wherever two three-chains are present.

    The short chain development of [DotsAndBoxes] proves the capped recursion
    conservative and gives the uniform families, and states that the analogue
    of [value_complete] fails. [svalue_ones_one] is the first mixed family: any
    number of one-box chains beside a single long component, whose value is the
    component iterated under the map that opens a one-box chain. *)

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

(** * Case (ii): opening a four-loop *)

(** A four-loop beside a component that is neither a three-chain nor a
    four-loop leaves the terminal bonus alone when it is removed, so the
    controlled value of the remainder is four higher. *)
Lemma four_loop_rest :
  forall G rest,
    wf G -> In (Loop 4, rest) (selections G) ->
    only34 G = false ->
    tb (Loop 4 :: rest) = tb rest /\ cval rest = cval G + 4.
Proof.
  intros G rest Hw Hsel Honly.
  assert (Hex : existsb (fun C => negb (is_3chain_b C || is_4loop_b C)%bool) G
                = true)
    by (unfold only34 in Honly; rewrite <- negb_forallb, Honly; reflexivity).
  apply existsb_exists in Hex; destruct Hex as [D [HD HDn]].
  apply negb_true_iff, orb_false_iff in HDn; destruct HDn as [HD3 HD4].
  assert (HwD : wf_comp D)
    by (unfold wf in Hw; rewrite Forall_forall in Hw; apply Hw; exact HD).
  pose proof (selections_perm G (Loop 4, rest) Hsel) as Hperm;
    cbn [fst snd] in Hperm.
  assert (HDrest : In D rest).
  { assert (HDG : In D (Loop 4 :: rest))
      by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact HD]).
    destruct HDG as [HDeq | HDr]; [|exact HDr].
    exfalso; rewrite <- HDeq in HD4; discriminate. }
  assert (Htb : tb (Loop 4 :: rest) = tb rest)
    by (apply (tb_remove_4loop rest D); assumption).
  split; [exact Htb|].
  pose proof (selections_cval G (Loop 4, rest) Hsel) as Hcv;
    cbn [fst snd] in Hcv.
  rewrite weight_loop_len, Htb in Hcv.
  unfold cval in *; simpl Z.of_nat in Hcv; lia.
Qed.

(** Case (ii) of Allcock's Theorem 1.1, in the regime where the closed form is
    the absolute controlled value: opening the four-loop attains the value, so
    no opening is better. *)
Theorem open_4loop_optimal :
  forall G rest,
    wf G -> In (Loop 4, rest) (selections G) ->
    existsb is_4loop_b G = true ->
    only34 G = false ->
    -2 <= cval G ->
    value_open (Loop 4, rest) = value G /\
    (forall q, In q (selections G) -> value_open (Loop 4, rest) <= value_open q).
Proof.
  intros G rest Hw Hsel H4 Honly Hge.
  destruct (four_loop_rest G rest Hw Hsel Honly) as [Htb Hcr].
  assert (HNil : G <> []) by (intros ->; simpl in Hsel; destruct Hsel).
  assert (Hwr : wf rest)
    by exact (proj2 (selections_wf G (Loop 4, rest) Hw Hsel)).
  assert (Hvr : value rest = cval G + 4)
    by (rewrite (value_cval_ge2 rest Hwr) by lia; exact Hcr).
  assert (Hop : value_open (Loop 4, rest) = Z.abs (cval G)).
  { unfold value_open; cbn [fst snd]; rewrite Hvr, vopen_loop4.
    f_equal; lia. }
  assert (HvG : value G = Z.abs (cval G))
    by (apply value_with_4loop; assumption).
  split; [rewrite Hop, HvG; reflexivity|].
  apply (proj1 (opener_optimal_iff G (Loop 4, rest) HNil Hsel)).
  rewrite Hop, HvG; reflexivity.
Qed.

(** * The standard move where three-chains abound *)

(** With another three-chain left behind, removing a three-chain leaves the
    terminal bonus alone, so the criterion applies and the standard move is
    optimal. *)
Theorem open_3chain_optimal :
  forall G rest,
    wf G -> In (Chain 3, rest) (selections G) ->
    existsb is_3chain_b rest = true ->
    2 <= cval rest ->
    value_open (Chain 3, rest) = cval G /\
    (forall q, In q (selections G) -> value_open (Chain 3, rest) <= value_open q).
Proof.
  intros G rest Hw Hsel H3 Hc.
  apply (open_chain_optimal_ge2 G 3 rest Hw Hsel);
    [apply tb_cons_3chain_with3; exact H3 | exact Hc].
Qed.

(** So on a position of two or more three-chains whose controlled value stays
    at two after one is removed, the standard move is provably optimal. *)
Corollary standard_move_optimal_two_threes :
  forall G rest,
    wf G -> In (Chain 3, rest) (selections G) ->
    (1 <= count3 rest)%nat ->
    2 <= cval rest ->
    value G = value_open (Chain 3, rest).
Proof.
  intros G rest Hw Hsel H3 Hc.
  assert (Hex : existsb is_3chain_b rest = true)
    by (apply count3_pos_iff; lia).
  destruct (open_3chain_optimal G rest Hw Hsel Hex Hc) as [Hop Hmin].
  assert (HNil : G <> []) by (intros ->; simpl in Hsel; destruct Hsel).
  apply (proj2 (opener_optimal_iff G (Chain 3, rest) HNil Hsel)); exact Hmin.
Qed.

(** * One-box chains beside a long component *)

(** Opening a one-box chain sends the worth of what is left to its distance
    from one. *)
Fixpoint dec1 (a : nat) (w : Z) : Z :=
  match a with O => w | S k => Z.abs (dec1 k w - 1) end.

Lemma dec1_S : forall a w, dec1 (S a) w = Z.abs (dec1 a w - 1).
Proof. reflexivity. Qed.

(** The iteration stays inside the interval the component fixes. *)
Lemma dec1_bounds : forall a w, 1 <= w -> 0 <= dec1 a w <= w.
Proof.
  induction a as [|a IH]; intros w Hw; simpl; [lia|].
  destruct (IH w Hw) as [H1 H2]; lia.
Qed.

Definition ones (a : nat) : position := repeat (Chain 1) a.

Lemma ones_S : forall a, ones (S a) = Chain 1 :: ones a.
Proof. reflexivity. Qed.

(** A single component is taken whole, whatever its length. *)
Lemma svalue_single : forall C, svalue [C] = Z.of_nat (csize C).
Proof.
  intros C.
  assert (H : svalue [C] = svopen C (svalue []))
    by (rewrite svalue_cons; reflexivity).
  assert (Hn : svalue (@nil comp) = 0) by reflexivity.
  rewrite H, Hn; unfold svopen.
  assert (Hz : (0 <= shand C)%nat) by lia.
  assert (Hz' : 0 <= Z.of_nat (shand C)) by lia.
  rewrite Z.max_l by lia.
  lia.
Qed.

(** Removing a component from [ones a ++ [C]] leaves either a shorter such
    position or the one-box chains alone. *)
Lemma selections_ones_one :
  forall a C p,
    In p (selections (ones a ++ [C])) ->
    (fst p = Chain 1 /\ exists a', a = S a' /\ snd p = ones a' ++ [C]) \/
    (fst p = C /\ snd p = ones a).
Proof.
  induction a as [|a IH]; intros C p Hp.
  - simpl in Hp; destruct Hp as [<- | []].
    right; split; reflexivity.
  - rewrite ones_S in Hp; simpl app in Hp; simpl selections in Hp.
    destruct Hp as [<- | Hp].
    + left; cbn [fst snd]; split; [reflexivity|].
      exists a; split; reflexivity.
    + apply in_map_iff in Hp; destruct Hp as [[qc qr] [Heq Hq]].
      cbn [fst snd] in Heq; subst p.
      destruct (IH C (qc, qr) Hq) as [[Hc [a' [Ha Hs]]] | [Hc Hs]];
        cbn [fst snd] in Hc, Hs.
      * left; cbn [fst snd]; split; [exact Hc|].
        exists a; split; [reflexivity|].
        rewrite Hs, Ha, ones_S; reflexivity.
      * right; cbn [fst snd]; split; [exact Hc|].
        rewrite Hs, ones_S; reflexivity.
Qed.

Lemma ones_one_nonnil : forall a C, ones a ++ [C] <> [].
Proof.
  intros [|a] C; simpl; discriminate.
Qed.

(** The long component is always available to open. *)
Lemma In_selections_ones_one :
  forall a C, In (C, ones a) (selections (ones a ++ [C])).
Proof.
  induction a as [|a IH]; intros C; [simpl; left; reflexivity|].
  rewrite ones_S; simpl app; simpl selections; right.
  apply in_map_iff; exists (C, ones a); split; [reflexivity | apply IH].
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
    (2 <= csize C)%nat -> 0 <= svalue (ones a ++ [C]) <= Z.of_nat (csize C).
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
    Z.abs (svalue (ones a ++ [C]) - 1)
      <= svopen C (svalue (ones (S a))).
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
    svalue (ones a ++ [C]) = dec1 a (Z.of_nat (csize C)).
Proof.
  intros a C Hc; induction a as [|a IH].
  - simpl ones; simpl app; simpl dec1; apply svalue_single.
  - assert (Hopt : forall p, In p (selections (ones (S a) ++ [C])) ->
              svalue_open p = Z.abs (svalue (ones a ++ [C]) - 1) \/
              svalue_open p = svopen C (svalue (ones (S a)))).
    { intros p Hp.
      destruct (selections_ones_one (S a) C p Hp)
        as [[Hf [a' [Ha Hs]]] | [Hf Hs]].
      - left; unfold svalue_open; rewrite Hf, Hs.
        injection Ha as Ha; subst a'.
        rewrite svopen_chain1; reflexivity.
      - right; unfold svalue_open; rewrite Hf, Hs; reflexivity. }
    assert (Hin1 : In (Chain 1, ones a ++ [C])
                      (selections (ones (S a) ++ [C])))
      by (rewrite ones_S; simpl app; simpl selections; left; reflexivity).
    assert (HinC : In (C, ones (S a)) (selections (ones (S a) ++ [C])))
      by apply In_selections_ones_one.
    rewrite (svalue_two_options (ones (S a) ++ [C])
               (Z.abs (svalue (ones a ++ [C]) - 1))
               (svopen C (svalue (ones (S a)))));
      [| apply ones_one_nonnil | exact Hopt | | ].
    + rewrite dec1_S, IH.
      pose proof (open_long_not_better a C Hc) as Hle.
      rewrite IH in Hle; lia.
    + exists (Chain 1, ones a ++ [C]); split; [exact Hin1|].
      unfold svalue_open; cbn [fst snd]; rewrite svopen_chain1; reflexivity.
    + exists (C, ones (S a)); split; [exact HinC | reflexivity].
Qed.

(** The two regimes read off the iteration: the component is worn down one box
    at a time, and once it is gone the one-box chains alternate. *)
Corollary svalue_ones_one_le :
  forall a C,
    (2 <= csize C)%nat -> (a <= csize C)%nat ->
    svalue (ones a ++ [C]) = Z.of_nat (csize C) - Z.of_nat a.
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
Example svalue_one_three : svalue (ones 1 ++ [Chain 3]) = 2.
Proof. reflexivity. Qed.

Example svalue_two_ones_three : svalue (ones 2 ++ [Chain 3]) = 1.
Proof. reflexivity. Qed.

Example svalue_four_ones_three : svalue (ones 4 ++ [Chain 3]) = 1.
Proof. reflexivity. Qed.
