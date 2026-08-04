(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** The long chain rule.

    [DotsAndBoxesBoard.long_chain_identity] counts: over a completed game the
    turns taken exceed the dots by the doublecrosses. That is arithmetic, not
    yet a statement about players. What turns it into one is [p1_run]: since
    a move that scores keeps the move and a move that does not ends the turn,
    the player to move after any legal prefix is the first player exactly when
    an even number of turns has been taken. Parity of turns is therefore
    parity of the mover.

    Putting the two together, [long_chain_rule] fixes the parity of the turn
    count from the dots and the doublecrosses alone, and [mover_at_end] reads
    off which player the board hands the move to when it is full. That is the
    rule in the form it is used: the first player controls the count of dots
    plus doublecrosses, and that count decides who is on move at every later
    parity checkpoint.

    The other half of the rule is about components rather than turns, and
    lives in [GameTrees.Nimstring]: a loony position is won by its opener
    exactly when the number of components is odd. [loony_opener_parity] says
    this of a board decomposition, so the long chains and loops a board breaks
    into decide the endgame by their number.

    What is not proved here is the bridge between the two halves, that the
    turns remaining once the loony endgame begins are exactly the components.
    That needs a model of when the opening ends, which this development does
    not have. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxesBoard.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.Nimstring.
Require Import GameTrees.Decomposition.
Require Import GameTrees.Grundy.

Section LongChain.

Variables m n : nat.

(** * Unfoldings *)

Lemma run_cons :
  forall s e ms, run m n s (e :: ms) = run m n (db_play m n s e) ms.
Proof. reflexivity. Qed.

Lemma turns_cons :
  forall s e ms,
    turns m n s (e :: ms) =
    ((match ngain m n (laid s) e with O => 1 | S _ => 0 end)
     + turns m n (db_play m n s e) ms)%nat.
Proof. reflexivity. Qed.

(** A move that takes no box ends the turn; one that takes a box keeps it. *)
Lemma p1_play :
  forall s e,
    p1 (db_play m n s e) =
    match ngain m n (laid s) e with
    | O => negb (p1 s)
    | S _ => p1 s
    end.
Proof.
  intros s e; unfold db_play.
  destruct (ngain m n (laid s) e); [reflexivity | destruct (p1 s); reflexivity].
Qed.

(** * The mover is the parity of the turns *)

(** After any sequence of moves the mover has flipped exactly once per turn,
    so it is determined by the parity of the turn count. *)
Theorem p1_run :
  forall ms s, p1 (run m n s ms) = xorb (p1 s) (Nat.odd (turns m n s ms)).
Proof.
  induction ms as [|e ms IH]; intros s.
  - simpl run; simpl turns; destruct (p1 s); reflexivity.
  - rewrite run_cons, turns_cons, (IH (db_play m n s e)), p1_play.
    destruct (ngain m n (laid s) e).
    + simpl Nat.add.
      rewrite Nat.odd_succ, <- Nat.negb_odd.
      destruct (p1 s); destruct (Nat.odd (turns m n (db_play m n s e) ms));
        reflexivity.
    + simpl Nat.add; reflexivity.
Qed.

(** From the empty board the mover is the first player exactly on an even
    number of turns. *)
Corollary p1_run_init :
  forall ms, p1 (run m n init ms) = negb (Nat.odd (turns m n init ms)).
Proof.
  intros ms; rewrite (p1_run ms init).
  change (p1 init) with true.
  destruct (Nat.odd (turns m n init ms)); reflexivity.
Qed.

(** * The rule *)

(** The parity of the turn count is fixed by the dots and the doublecrosses,
    and by nothing else about the play. *)
Theorem long_chain_rule :
  forall ms,
    legal m n init ms ->
    complete m n (run m n init ms) ->
    Nat.odd (turns m n init ms) = Nat.even (dots m n + extra m n init ms).
Proof.
  intros ms Hl Hc.
  rewrite <- (long_chain_identity m n ms Hl Hc).
  rewrite Nat.even_succ, <- Nat.negb_even, <- Nat.negb_odd, negb_involutive.
  reflexivity.
Qed.

(** So the board hands the move back to the first player, once full, exactly
    when the dots and doublecrosses together are odd. *)
Theorem mover_at_end :
  forall ms,
    legal m n init ms ->
    complete m n (run m n init ms) ->
    p1 (run m n init ms) = Nat.odd (dots m n + extra m n init ms).
Proof.
  intros ms Hl Hc.
  rewrite p1_run_init, (long_chain_rule ms Hl Hc), <- Nat.negb_odd,
          negb_involutive.
  reflexivity.
Qed.

(** With no doublecrosses the rule is about the dots alone. *)
Corollary mover_at_end_no_doublecross :
  forall ms,
    legal m n init ms ->
    complete m n (run m n init ms) ->
    extra m n init ms = 0%nat ->
    p1 (run m n init ms) = Nat.odd (dots m n).
Proof.
  intros ms Hl Hc H0.
  rewrite (mover_at_end ms Hl Hc), H0, Nat.add_0_r; reflexivity.
Qed.

(** A player who takes every box scores every one of them, so the
    doublecrosses are what the loser gives away: the parity the first player
    steers is [dots + extra] and nothing else. *)
Corollary turns_determined_mod2 :
  forall ms ms',
    legal m n init ms -> complete m n (run m n init ms) ->
    legal m n init ms' -> complete m n (run m n init ms') ->
    extra m n init ms = extra m n init ms' ->
    Nat.odd (turns m n init ms) = Nat.odd (turns m n init ms').
Proof.
  intros ms ms' Hl Hc Hl' Hc' He.
  rewrite (long_chain_rule ms Hl Hc), (long_chain_rule ms' Hl' Hc'), He.
  reflexivity.
Qed.

End LongChain.

(** * The component half of the rule *)

(** A board decomposition names one component per long chain and per loop, so
    the Nimstring endgame it presents is won by its opener exactly when their
    number is odd. *)
Theorem loony_opener_parity :
  forall loops chains,
    winb (nimstring (comps_position loops chains)) = true <->
    Nat.odd (length loops + length chains) = true.
Proof.
  intros loops chains.
  rewrite nimstring_opener_wins.
  unfold comps_position; rewrite length_app, !length_map; reflexivity.
Qed.

(** With no loops it is the long chains alone that decide. *)
Corollary loony_opener_chains :
  forall chains,
    winb (nimstring (comps_position [] chains)) = true <->
    Nat.odd (length chains) = true.
Proof.
  intros chains; rewrite loony_opener_parity; reflexivity.
Qed.

(** * Turns in the endgame are components *)

(** A run of openings: each turn of a loony endgame takes one component, and
    the run ends when nothing is left. *)
Fixpoint opening_run (G : position) (ps : list (comp * position)) : Prop :=
  match ps with
  | [] => G = []
  | p :: r => In p (selections G) /\ opening_run (snd p) r
  end.

(** So a run that empties the position takes exactly one turn per component.
    This is the half of the long chain rule that counts components rather
    than dots. *)
Theorem opening_run_length :
  forall ps G, opening_run G ps -> length ps = length G.
Proof.
  induction ps as [|p ps IH]; intros G H; simpl in H.
  - subst G; reflexivity.
  - destruct H as [Hp Hr].
    simpl length; rewrite (IH (snd p) Hr).
    pose proof (selections_length G p Hp); lia.
Qed.

(** Every loony position admits such a run, so the count is attained. *)
Theorem opening_run_exists :
  forall G, exists ps, opening_run G ps /\ length ps = length G.
Proof.
  assert (Haux : forall k G, (length G <= k)%nat -> exists ps, opening_run G ps).
  { induction k as [|k IH]; intros G Hk.
    - assert (HG : G = []) by (destruct G; simpl in Hk; [reflexivity | lia]).
      subst G; exists []; reflexivity.
    - destruct G as [|C G]; [exists []; reflexivity|].
      destruct (IH G) as [ps Hps]; [simpl in Hk; lia|].
      exists ((C, G) :: ps); split; [left; reflexivity | exact Hps]. }
  intros G; destruct (Haux (length G) G ltac:(lia)) as [ps Hps].
  exists ps; split; [exact Hps | apply opening_run_length; exact Hps].
Qed.

(** Putting the two halves together: the opener of a loony endgame wins
    exactly when the endgame runs for an odd number of turns. *)
Corollary endgame_opener_parity :
  forall G ps,
    opening_run G ps ->
    (winb (nimstring G) = true <-> Nat.odd (length ps) = true).
Proof.
  intros G ps H; rewrite nimstring_opener_wins, (opening_run_length ps G H).
  reflexivity.
Qed.

(** And on a board decomposition the turn count is the number of long chains
    and loops. *)
Corollary decomp_endgame_turns :
  forall loops chains ps,
    opening_run (comps_position loops chains) ps ->
    length ps = (length loops + length chains)%nat.
Proof.
  intros loops chains ps H.
  rewrite (opening_run_length ps _ H).
  unfold comps_position; rewrite length_app, !length_map; reflexivity.
Qed.
