(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Short chains.

    [GameTrees.DotsAndBoxes] asks every chain to have at least three boxes,
    and the handout of two is then always available. A chain of one box has no
    such handout, and there [vopen] is simply wrong: with one box and a
    remainder worth three it reports zero, when the controller can only take
    the box and open, for minus two.

    [shand] caps the handout at the component itself and [svopen] is the
    recursion built on it. [svopen_wf] proves the two agree wherever the
    existing theory applies, so this is a conservative extension, and
    [svopen_chain1] and [svopen_chain2] give the short cases the earlier
    development cannot state. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.

Open Scope Z_scope.

(** * The capped handout *)

(** The controller cannot leave more than the component holds. *)
Definition shand (C : comp) : nat := Nat.min (hand C) (csize C).

Definition svopen (C : comp) (w : Z) : Z :=
  Z.max (Z.of_nat (csize C) - w)
        (Z.of_nat (csize C) - 2 * Z.of_nat (shand C) + w).

Lemma shand_le_csize : forall C, (shand C <= csize C)%nat.
Proof. intros C; unfold shand; lia. Qed.

(** * Conservativity *)

Lemma shand_wf : forall C, wf_comp C -> shand C = hand C.
Proof.
  intros C H; unfold shand.
  pose proof (hand_le_csize C H); lia.
Qed.

(** Wherever the earlier development applies, the capped recursion is the
    same recursion. *)
Theorem svopen_wf :
  forall C w, wf_comp C -> svopen C w = vopen C w.
Proof.
  intros C w H; unfold svopen; rewrite (shand_wf C H), <- vopen_max; reflexivity.
Qed.

(** * The capped recursion is still sound *)

(** The opener never profits at a single component, however short. *)
Theorem svopen_nonneg : forall C w, 0 <= svopen C w.
Proof.
  intros C w; unfold svopen.
  pose proof (shand_le_csize C) as Hs.
  assert (Hz : (Z.of_nat (shand C) <= Z.of_nat (csize C)))
    by (apply Nat2Z.inj_le; exact Hs).
  destruct (Z.le_gt_cases w (Z.of_nat (csize C))) as [Hle | Hgt].
  - eapply Z.le_trans; [| apply Z.le_max_l]; lia.
  - eapply Z.le_trans; [| apply Z.le_max_r]; lia.
Qed.

(** The capped handout still shares the parity of the component and the
    remainder, so the counting arguments carry over. *)
Theorem svopen_parity :
  forall C w, Z.even (svopen C w) = Z.even (Z.of_nat (csize C) + w).
Proof.
  intros C w; unfold svopen.
  destruct (Z.le_gt_cases (Z.of_nat (csize C) - w)
                          (Z.of_nat (csize C) - 2 * Z.of_nat (shand C) + w))
    as [Hle | Hgt].
  - rewrite Z.max_r by lia.
    replace (Z.of_nat (csize C) - 2 * Z.of_nat (shand C) + w)
      with ((Z.of_nat (csize C) + w) - 2 * Z.of_nat (shand C)) by lia.
    rewrite Z.even_sub, (Z.even_mul 2 (Z.of_nat (shand C))); simpl Z.even at 2.
    destruct (Z.even (Z.of_nat (csize C) + w)); reflexivity.
  - rewrite Z.max_l by lia.
    rewrite Z.even_sub, Z.even_add.
    destruct (Z.even (Z.of_nat (csize C))), (Z.even w); reflexivity.
Qed.

(** * The short cases *)

(** A single box: take it and open, or leave it and keep control. *)
Theorem svopen_chain1 : forall w, svopen (Chain 1) w = Z.abs (w - 1).
Proof.
  intros w; unfold svopen, shand; simpl csize; simpl hand; simpl Nat.min.
  destruct (Z.le_gt_cases w 1) as [Hle | Hgt].
  - rewrite Z.abs_neq by lia; lia.
  - rewrite Z.abs_eq by lia; lia.
Qed.

(** Two boxes: the handout is the whole chain, so declining takes nothing. *)
Theorem svopen_chain2 : forall w, svopen (Chain 2) w = Z.abs (w - 2).
Proof.
  intros w; unfold svopen, shand; simpl csize; simpl hand; simpl Nat.min.
  destruct (Z.le_gt_cases w 2) as [Hle | Hgt].
  - rewrite Z.abs_neq by lia; lia.
  - rewrite Z.abs_eq by lia; lia.
Qed.

(** The uncapped recursion really does go wrong on a one-box chain: it
    reports zero where the controller can only lose two. *)
Example vopen_chain1_wrong : vopen (Chain 1) 3 = 0 /\ svopen (Chain 1) 3 = 2.
Proof. split; reflexivity. Qed.

(** * Positions with short chains *)

(** Chains of one or two boxes, and the loops the board can produce. *)
Definition swf_comp (C : comp) : Prop :=
  match C with
  | Chain n => (1 <= n)%nat
  | Loop n => (4 <= n)%nat /\ Nat.even n = true
  end.

Definition swf (G : position) : Prop := Forall swf_comp G.

Lemma wf_swf : forall G, wf G -> swf G.
Proof.
  intros G H; unfold swf; rewrite Forall_forall.
  unfold wf in H; rewrite Forall_forall in H.
  intros C HC; specialize (H C HC).
  destruct C as [k | k]; simpl in *; [lia | exact H].
Qed.

(** So every wellformed loony position is one the capped theory covers, and
    on those the two recursions agree component by component. *)
Theorem svopen_agrees_on_wf :
  forall G, wf G -> Forall (fun C => forall w, svopen C w = vopen C w) G.
Proof.
  intros G H; unfold wf in H; rewrite Forall_forall in H.
  rewrite Forall_forall; intros C HC w.
  apply svopen_wf, H, HC.
Qed.

(** * The value with short chains allowed *)

Fixpoint svf (fuel : nat) (G : position) : Z :=
  match fuel with
  | O => 0
  | S f =>
      match selections G with
      | [] => 0
      | p :: more =>
          minl (svopen (fst p) (svf f (snd p)))
               (map (fun q => svopen (fst q) (svf f (snd q))) more)
      end
  end.

Definition svalue (G : position) : Z := svf (length G) G.

Lemma svf_vf : forall fuel G, wf G -> svf fuel G = vf fuel G.
Proof.
  induction fuel as [|f IH]; intros G HG; [reflexivity|].
  simpl svf; simpl vf.
  destruct (selections G) as [|p more] eqn:E; [reflexivity|].
  assert (Hp : In p (selections G)) by (rewrite E; left; reflexivity).
  destruct (selections_wf G p HG Hp) as [Hcp Hrp].
  rewrite (IH (snd p) Hrp), (svopen_wf (fst p) (vf f (snd p)) Hcp).
  f_equal.
  apply map_ext_in; intros q Hq.
  assert (Hq' : In q (selections G)) by (rewrite E; right; exact Hq).
  destruct (selections_wf G q HG Hq') as [Hcq Hrq].
  rewrite (IH (snd q) Hrq), (svopen_wf (fst q) (vf f (snd q)) Hcq); reflexivity.
Qed.

(** The capped value is the value, wherever the value is defined. Every
    closed form of [GameTrees.DotsAndBoxes] therefore transfers, and what is
    new is only the positions the earlier theory had to exclude. *)
Theorem svalue_wf : forall G, wf G -> svalue G = value G.
Proof. intros G H; unfold svalue, value; apply svf_vf; exact H. Qed.

(** The opener never profits, short chains or not. *)
Theorem svalue_nonneg : forall G, 0 <= svalue G.
Proof.
  assert (Haux : forall n G, (length G <= n)%nat -> 0 <= svf n G).
  { induction n as [|n IH]; intros G Hn; [apply Z.le_refl|].
    simpl svf; destruct (selections G) as [|p more] eqn:E;
      [apply Z.le_refl|].
    apply minl_lower_bound; [apply svopen_nonneg|].
    intros y Hy; apply in_map_iff in Hy; destruct Hy as [q [<- _]].
    apply svopen_nonneg. }
  intros G; unfold svalue; apply Haux; lia.
Qed.

(** A lone short chain is taken whole. *)
Example svalue_chain1 : svalue [Chain 1] = 1.
Proof. reflexivity. Qed.

Example svalue_two_chain1 : svalue [Chain 1; Chain 1] = 0.
Proof. reflexivity. Qed.
