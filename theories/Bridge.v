(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** The bridge between the two halves of the long chain rule.

    [Decomposition] proves the turn count of a completed game from the dots and
    the doublecrosses, and proves that a loony position of [k] components is won
    by its opener exactly when [k] is odd. It leaves the two unconnected,
    proposing that the turns remaining once the endgame begins are the
    components.

    That proposal is false. A turn of the endgame is an opening, and the
    controller who declines spends a second turn-ending move on the handout,
    which is also where the doublecrosses come from. This file models the
    endgame play with the controller's decision recorded, and proves
    [eturns_components]: the turns are the components plus the declines.
    [eturns_eq_components_iff] is the exact condition under which the proposal
    holds, and [decline_can_be_strict] shows it fails already on two
    three-chains, where declining is strictly better than taking all.

    What the parity of the components really governs is [etakealls]: control
    passes exactly on a component taken whole, so [opener_after] is the parity
    of those, not of the turns. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.Decomposition.

Import ListNotations.

(** * The controller's decision *)

(** Handed an open component the controller either takes it whole, giving up
    control, or leaves the handout and keeps it. *)
Inductive decision : Type := TakeAll | Decline.

Definition step : Type := (comp * decision)%type.

Definition is_decline (p : step) : bool :=
  match snd p with Decline => true | TakeAll => false end.

Definition declines (ps : list step) : nat :=
  length (filter is_decline ps).

Definition takealls (ps : list step) : nat :=
  length (filter (fun p => negb (is_decline p)) ps).

Lemma declines_takealls :
  forall ps, (takealls ps + declines ps = length ps)%nat.
Proof.
  induction ps as [|p ps IH]; [reflexivity|].
  unfold declines, takealls in *; simpl.
  destruct (is_decline p); simpl; lia.
Qed.

(** * A play of the endgame *)

(** Each turn opens one component of what is left; the play ends when nothing
    remains. *)
Fixpoint eplay (G : position) (ps : list step) : Prop :=
  match ps with
  | [] => G = []
  | p :: r => exists rest, In (fst p, rest) (selections G) /\ eplay rest r
  end.

Lemma eplay_nil : forall G, eplay G [] <-> G = [].
Proof. intros G; simpl; split; auto. Qed.

(** A play removes one component per turn, so it has as many turns as the
    position has components. *)
Theorem eplay_length :
  forall ps G, eplay G ps -> length ps = length G.
Proof.
  induction ps as [|p ps IH]; intros G H; simpl in H.
  - subst G; reflexivity.
  - destruct H as [rest [Hin Hr]].
    simpl length; rewrite (IH rest Hr).
    pose proof (selections_length G (fst p, rest) Hin) as Hl; simpl in Hl; lia.
Qed.

(** Every position admits a play, whatever the controller decides. *)
Theorem eplay_exists :
  forall G (d : comp -> decision),
    exists ps, eplay G ps /\ length ps = length G.
Proof.
  assert (Haux : forall n G (d : comp -> decision),
            (length G <= n)%nat -> exists ps, eplay G ps).
  { induction n as [|n IH]; intros G d Hn.
    - assert (HG : G = []) by (destruct G; simpl in Hn; [reflexivity | lia]).
      subst G; exists []; reflexivity.
    - destruct G as [|C G]; [exists []; reflexivity|].
      destruct (IH G d ltac:(simpl in Hn; lia)) as [ps Hps].
      exists ((C, d C) :: ps); simpl.
      exists G; split; [left; reflexivity | exact Hps]. }
  intros G d; destruct (Haux (length G) G d ltac:(lia)) as [ps Hps].
  exists ps; split; [exact Hps | apply eplay_length; exact Hps].
Qed.

(** * Counting the turns *)

(** A turn ends on a move that takes no box. Opening a component is such a
    move, and so is the handout a declining controller leaves; taking a
    component whole is not, since the last box keeps the move. *)
Definition eturns (ps : list step) : nat := (length ps + declines ps)%nat.

(** The corrected bridge: the turns of an endgame are its components together
    with its declines. *)
Theorem eturns_components :
  forall ps G, eplay G ps -> eturns ps = (length G + declines ps)%nat.
Proof.
  intros ps G H; unfold eturns; rewrite (eplay_length ps G H); reflexivity.
Qed.

(** So the turns are the components exactly when nothing is declined, which is
    the condition [Decomposition] leaves unstated. *)
Theorem eturns_eq_components_iff :
  forall ps G, eplay G ps -> (eturns ps = length G <-> declines ps = 0%nat).
Proof.
  intros ps G H; rewrite (eturns_components ps G H); lia.
Qed.

Corollary eturns_ge_components :
  forall ps G, eplay G ps -> (length G <= eturns ps)%nat.
Proof.
  intros ps G H; rewrite (eturns_components ps G H); lia.
Qed.

(** * Control *)

(** Control passes exactly when a component is taken whole. *)
Fixpoint opener_after (start : bool) (ps : list step) : bool :=
  match ps with
  | [] => start
  | p :: r => opener_after (if is_decline p then start else negb start) r
  end.

Lemma opener_after_parity :
  forall ps start, opener_after start ps = xorb start (Nat.odd (takealls ps)).
Proof.
  induction ps as [|p ps IH]; intros start; simpl.
  - unfold takealls; simpl; destruct start; reflexivity.
  - unfold takealls in *; simpl.
    destruct (is_decline p); simpl.
    + rewrite IH; reflexivity.
    + rewrite IH, Nat.odd_succ, <- Nat.negb_odd.
      destruct start; destruct (Nat.odd (length (filter (fun q => negb (is_decline q)) ps)));
        reflexivity.
Qed.

(** So the player left to open at the end of the endgame is fixed by the parity
    of the components taken whole, and not by the parity of the turns. *)
Theorem opener_after_takealls :
  forall ps start, opener_after start ps = xorb start (Nat.odd (takealls ps)).
Proof. exact opener_after_parity. Qed.

(** When nothing is declined the two parities agree, and only then. *)
Theorem opener_after_of_no_decline :
  forall ps G start,
    eplay G ps -> declines ps = 0%nat ->
    opener_after start ps = xorb start (Nat.odd (length G)).
Proof.
  intros ps G start Hp Hd.
  rewrite opener_after_parity.
  pose proof (declines_takealls ps) as Ht.
  rewrite (eplay_length ps G Hp) in Ht; rewrite Hd in Ht.
  replace (takealls ps) with (length G) by lia; reflexivity.
Qed.

(** * Doublecrosses *)

(** A declined chain hands over two boxes, taken by one move that completes
    both: one doublecross. A declined loop hands over four, taken by two such
    moves. *)
Definition edx (C : comp) : nat := Nat.div2 (hand C).

Lemma edx_chain : forall k, edx (Chain k) = 1%nat.
Proof. reflexivity. Qed.

Lemma edx_loop : forall k, edx (Loop k) = 2%nat.
Proof. reflexivity. Qed.

Fixpoint eextra (ps : list step) : nat :=
  match ps with
  | [] => 0%nat
  | p :: r => ((if is_decline p then edx (fst p) else 0) + eextra r)%nat
  end.

(** A component taken whole yields no doublecross, and a declined one yields
    one or two, so the doublecrosses bracket the declines. *)
Theorem eextra_bounds :
  forall ps, (declines ps <= eextra ps <= 2 * declines ps)%nat.
Proof.
  induction ps as [|p ps IH]; [simpl; unfold declines; simpl; lia|].
  unfold declines in *; simpl.
  destruct (is_decline p) eqn:E; simpl.
  - destruct (fst p) as [k | k]; simpl; lia.
  - lia.
Qed.

(** In particular the endgame doublecrosses vanish exactly when nothing is
    declined, which by [eturns_eq_components_iff] is exactly when the turns are
    the components. *)
Theorem eextra_zero_iff :
  forall ps, eextra ps = 0%nat <-> declines ps = 0%nat.
Proof.
  intros ps; pose proof (eextra_bounds ps); lia.
Qed.

Corollary eturns_eq_components_iff_no_doublecross :
  forall ps G, eplay G ps -> (eturns ps = length G <-> eextra ps = 0%nat).
Proof.
  intros ps G H; rewrite (eturns_eq_components_iff ps G H), eextra_zero_iff.
  reflexivity.
Qed.

(** With no doublecrosses the endgame turns are the components and control is
    read off their parity: this is the proposal of [Decomposition], with the
    hypothesis it needs made explicit. *)
Theorem bridge_when_no_doublecross :
  forall ps G start,
    eplay G ps -> eextra ps = 0%nat ->
    eturns ps = length G /\
    opener_after start ps = xorb start (Nat.odd (length G)).
Proof.
  intros ps G start Hp He.
  apply eextra_zero_iff in He.
  split.
  - apply (eturns_eq_components_iff ps G Hp); exact He.
  - apply (opener_after_of_no_decline ps G start Hp He).
Qed.

(** * Declining is not exceptional *)

Open Scope Z_scope.

(** On two three-chains the controller strictly prefers to decline: taking the
    opened chain whole is worth nothing to her, declining is worth two. *)
Theorem decline_can_be_strict :
  give_up_control (Chain 3) (value [Chain 3]) = 0 /\
  keep_control (Chain 3) (value [Chain 3]) = 2 /\
  give_up_control (Chain 3) (value [Chain 3])
    < keep_control (Chain 3) (value [Chain 3]).
Proof.
  rewrite value_single; cbn [csize].
  unfold give_up_control, keep_control; cbn [csize hand].
  repeat split; lia.
Qed.

(** And that preference is the value: opening either component of two
    three-chains is worth two, which is what declining secures. *)
Theorem two_three_chains_declines :
  value [Chain 3; Chain 3] = 2 /\
  vopen (Chain 3) (value [Chain 3]) = keep_control (Chain 3) (value [Chain 3]).
Proof.
  split.
  - vm_compute; reflexivity.
  - apply controller_keeps.
    rewrite value_single; cbn [csize hand]; lia.
Qed.

(** So the play the endgame actually takes on that position declines, its turns
    exceed its components, and the proposal fails there. *)
Theorem proposal_fails :
  exists (G : position) (ps : list step),
    eplay G ps /\ declines ps <> 0%nat /\ eturns ps <> length G.
Proof.
  exists [Chain 3; Chain 3], [(Chain 3, Decline); (Chain 3, TakeAll)].
  repeat split.
  - simpl; exists [Chain 3]; split; [left; reflexivity|].
    exists (@nil comp); split; [left; reflexivity | reflexivity].
  - unfold declines; simpl; discriminate.
  - unfold eturns, declines; simpl; discriminate.
Qed.

(** * What survives *)

(** The half of the rule that does hold without qualification: the components
    are the turns of the Nimstring game, where nothing is scored and so nothing
    can be declined. That is [Decomposition.opening_run], and every [eplay] in
    which the controller always takes whole is one. *)
Theorem eplay_all_takeall_is_opening_run :
  forall ps G,
    eplay G ps -> declines ps = 0%nat ->
    (length ps = length G /\ eturns ps = length ps).
Proof.
  intros ps G Hp Hd; split.
  - apply eplay_length; exact Hp.
  - unfold eturns; lia.
Qed.

(** And the corrected statement of the whole rule at the level of the endgame:
    the turns are the components plus the declines, the doublecrosses bracket
    the declines, and control is the parity of what was taken whole. *)
Theorem long_chain_bridge :
  forall ps G start,
    eplay G ps ->
    eturns ps = (length G + declines ps)%nat /\
    (declines ps <= eextra ps <= 2 * declines ps)%nat /\
    opener_after start ps = xorb start (Nat.odd (takealls ps)) /\
    (takealls ps + declines ps = length G)%nat.
Proof.
  intros ps G start Hp; repeat split.
  - apply (eturns_components ps G Hp).
  - apply eextra_bounds.
  - apply eextra_bounds.
  - apply opener_after_parity.
  - pose proof (declines_takealls ps) as H.
    rewrite (eplay_length ps G Hp) in H; exact H.
Qed.
