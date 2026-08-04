(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Nimstring on an arbitrary graph.

    [GameTrees.Nimstring] computes Grundy values on a loony position, where
    every component is a long chain or a loop and a turn therefore consumes
    exactly one component. On a general graph that is false: a cut that frees
    a coin obliges the mover to cut again, so a turn is a run of scoring cuts
    closed by one that scores nothing.

    [turn_options] collects the graphs a complete turn can leave, which is
    what makes the position an impartial game in the sense of
    [GameTrees.Grundy]: between those options the players do alternate.
    [ns_tree] is the resulting game tree and [ns_grundy] its Grundy value, so
    [ns_wins_iff] decides the normal-play winner on every graph. No closed
    form is offered, and none should be: Nimstring is PSPACE-complete. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.Trees.
Require Import GameTrees.Grundy.
Require Import GameTrees.StringsAndCoins.
Require Import GameTrees.SCGame.

(** * Turns *)

Lemma flat_map_ext_in :
  forall {A B : Type} (f g : A -> list B) (l : list A),
    (forall x, In x l -> f x = g x) -> flat_map f l = flat_map g l.
Proof.
  intros A B f g l; induction l as [|a l IH]; intros H; simpl; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH; [reflexivity|].
  intros x Hx; apply H; right; exact Hx.
Qed.

Lemma flat_map_singleton :
  forall {A B : Type} (f : A -> B) (l : list A),
    flat_map (fun x => [f x]) l = map f l.
Proof.
  intros A B f l; induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite IH; reflexivity.
Qed.

(** A cut scores when it sets some uncollected coin loose. *)
Definition scores (V : list coin) (g : sgraph) (s : strng) : bool :=
  existsb (fun x => negb (freeb g x) && freeb (cut s g) x)%bool V.

(** The graphs a complete turn can leave. A scoring cut obliges another, so
    the turn continues; a cut that scores nothing ends it. *)
Fixpoint turn_options (fuel : nat) (V : list coin) (g : sgraph) : list sgraph :=
  match fuel with
  | O => []
  | S f =>
      flat_map (fun s =>
                  if scores V g s
                  then turn_options f V (cut s g)
                  else [cut s g])
               g
  end.

(** One step of the recursion, kept as a lemma so proofs never have to unfold
    [flat_map] and [cut] together. *)
Lemma turn_options_S :
  forall f V g,
    turn_options (S f) V g =
    flat_map (fun s =>
                if scores V g s then turn_options f V (cut s g) else [cut s g])
             g.
Proof. reflexivity. Qed.

(** Every turn cuts at least one string, so it strictly shrinks the graph.
    This is what licenses the recursion below. *)
Lemma turn_options_shorter :
  forall fuel V g g',
    In g' (turn_options fuel V g) -> (length g' < length g)%nat.
Proof.
  induction fuel as [|f IH]; intros V g g' H; simpl in H; [destruct H|].
  apply in_flat_map in H; destruct H as [s [Hs Hg']].
  assert (Hcut : (length (cut s g) < length g)%nat)
    by (apply cut_length_lt; exact Hs).
  destruct (scores V g s).
  - specialize (IH V (cut s g) g' Hg'); lia.
  - destruct Hg' as [<- | []]; lia.
Qed.

(** The options do not depend on the fuel once it covers the graph. *)
Lemma turn_options_stable :
  forall n V g f1 f2,
    (length g <= n)%nat -> (length g <= f1)%nat -> (length g <= f2)%nat ->
    turn_options f1 V g = turn_options f2 V g.
Proof.
  induction n as [|n IH]; intros V g f1 f2 Hn H1 H2.
  - assert (Hg : g = []) by (destruct g; simpl in Hn; [reflexivity | lia]).
    subst g; destruct f1, f2; reflexivity.
  - destruct g as [|s0 r]; [destruct f1, f2; reflexivity|].
    destruct f1 as [|f1]; [simpl in H1; lia|].
    destruct f2 as [|f2]; [simpl in H2; lia|].
    rewrite !turn_options_S.
    apply flat_map_ext_in; intros s Hs.
    assert (Hcut : (length (cut s (s0 :: r)) < length (s0 :: r))%nat)
      by (apply cut_length_lt; exact Hs).
    destruct (scores V (s0 :: r) s); [|reflexivity].
    apply (IH V (cut s (s0 :: r))); lia.
Qed.

(** The canonical option set. *)
Definition turns_from (V : list coin) (g : sgraph) : list sgraph :=
  turn_options (length g) V g.

Lemma turns_from_nil : forall V, turns_from V [] = [].
Proof. intros V; reflexivity. Qed.

Lemma turns_from_shorter :
  forall V g g', In g' (turns_from V g) -> (length g' < length g)%nat.
Proof. intros V g g'; apply turn_options_shorter. Qed.

Lemma turn_options_turns_from :
  forall V g f, (length g <= f)%nat -> turn_options f V g = turns_from V g.
Proof.
  intros V g f Hf; unfold turns_from.
  apply (turn_options_stable (length g)); lia.
Qed.

(** With no coins to free no cut ever scores, so a turn is a single cut. *)
Lemma turns_from_no_coins :
  forall g, turns_from [] g = map (fun s => cut s g) g.
Proof.
  intros g; unfold turns_from.
  destruct (length g) as [|k] eqn:El.
  - assert (Hg : g = []) by (destruct g; [reflexivity | simpl in El; discriminate]).
    subst g; reflexivity.
  - assert (Hpt : forall s, In s g ->
              (if scores [] g s then turn_options k [] (cut s g)
               else [cut s g]) = [cut s g]).
    { intros s _; unfold scores; simpl existsb; reflexivity. }
    rewrite turn_options_S.
    rewrite (flat_map_ext_in
               (fun s => if scores [] g s then turn_options k [] (cut s g)
                         else [cut s g])
               (fun s => [cut s g]) g Hpt).
    apply flat_map_singleton.
Qed.

(** * The game tree *)

Fixpoint ns_tree (fuel : nat) (V : list coin) (g : sgraph) : Grundy.game :=
  match fuel with
  | O => node tt []
  | S f => node tt (map (ns_tree f V) (turns_from V g))
  end.

Lemma ns_tree_S :
  forall f V g, ns_tree (S f) V g = node tt (map (ns_tree f V) (turns_from V g)).
Proof. reflexivity. Qed.

Lemma ns_tree_nil : forall f V, ns_tree f V [] = node tt [].
Proof. intros [|f] V; reflexivity. Qed.

Lemma ns_tree_stable :
  forall n V g f1 f2,
    (length g <= n)%nat -> (length g <= f1)%nat -> (length g <= f2)%nat ->
    ns_tree f1 V g = ns_tree f2 V g.
Proof.
  induction n as [|n IH]; intros V g f1 f2 Hn H1 H2.
  - assert (Hg : g = []) by (destruct g; simpl in Hn; [reflexivity | lia]).
    subst g; rewrite !ns_tree_nil; reflexivity.
  - destruct g as [|s0 r]; [rewrite !ns_tree_nil; reflexivity|].
    destruct f1 as [|f1]; [simpl in H1; lia|].
    destruct f2 as [|f2]; [simpl in H2; lia|].
    rewrite !ns_tree_S; f_equal.
    apply map_ext_in; intros g' Hg'.
    pose proof (turns_from_shorter V (s0 :: r) g' Hg') as Hlt.
    apply (IH V g'); lia.
Qed.

(** The Nimstring game of a graph. *)
Definition nimstring_game (V : list coin) (g : sgraph) : Grundy.game :=
  ns_tree (length g) V g.

Lemma ns_tree_nimstring :
  forall V g f, (length g <= f)%nat -> ns_tree f V g = nimstring_game V g.
Proof.
  intros V g f Hf; unfold nimstring_game.
  apply (ns_tree_stable (length g)); lia.
Qed.

(** The fixpoint equation: the options are the graphs a turn can leave. *)
Theorem nimstring_game_unfold :
  forall V g,
    g <> [] ->
    nimstring_game V g = node tt (map (nimstring_game V) (turns_from V g)).
Proof.
  intros V g Hg; unfold nimstring_game at 1.
  destruct (length g) as [|k] eqn:El.
  { exfalso; apply Hg; destruct g; [reflexivity | simpl in El; discriminate]. }
  rewrite ns_tree_S; f_equal.
  apply map_ext_in; intros g' Hg'.
  pose proof (turns_from_shorter V g g' Hg') as Hlt.
  apply ns_tree_nimstring; lia.
Qed.

Lemma nimstring_game_nil : forall V, nimstring_game V [] = node tt [].
Proof. intros V; reflexivity. Qed.

(** * Grundy values *)

Definition ns_grundy (V : list coin) (g : sgraph) : nat :=
  grundy (nimstring_game V g).

Theorem ns_grundy_unfold :
  forall V g,
    g <> [] ->
    ns_grundy V g = mex (map (fun g' => ns_grundy V g') (turns_from V g)).
Proof.
  intros V g Hg; unfold ns_grundy.
  rewrite (nimstring_game_unfold V g Hg), grundy_eq, map_map; reflexivity.
Qed.

Lemma ns_grundy_nil : forall V, ns_grundy V [] = 0%nat.
Proof. intros V; reflexivity. Qed.

(** The mover wins a Nimstring position exactly when its Grundy value is
    nonzero. This is the whole normal-play theory, and unlike the loony case
    it holds on every graph. *)
Theorem ns_wins_iff :
  forall V g, winb (nimstring_game V g) = true <-> ns_grundy V g <> 0%nat.
Proof. intros V g; apply winb_grundy. Qed.

(** A position with no strings is lost by the mover. *)
Example ns_empty_loses : forall V, winb (nimstring_game V []) = false.
Proof. intros V; reflexivity. Qed.

(** * Sums *)

(** Nimstring positions on disjoint graphs add, since [GameTrees.Grundy]
    gives the exclusive or for the disjunctive sum of the trees. *)
Corollary ns_grundy_sum :
  forall V1 g1 V2 g2,
    grundy (tsum (nimstring_game V1 g1) (nimstring_game V2 g2))
    = Nat.lxor (ns_grundy V1 g1) (ns_grundy V2 g2).
Proof. intros; apply grundy_tsum. Qed.

(** * Agreement with the loony development *)

(** With no coins the game is plain edge-deletion, one cut per turn, so a
    graph of [k] strings is the Nim heap of [k] and its value is the parity
    of [k] once every option is a single cut. This is the shape
    [GameTrees.Nimstring] assumes throughout, recovered here as the special
    case where nothing scores. *)
Theorem ns_grundy_no_coins_step :
  forall g,
    g <> [] ->
    ns_grundy [] g = mex (map (fun s => ns_grundy [] (cut s g)) g).
Proof.
  intros g Hg.
  rewrite (ns_grundy_unfold [] g Hg), turns_from_no_coins, map_map; reflexivity.
Qed.

(** * Small instances *)

Example ns_one_string : ns_grundy [] [(ground, 1)] = 1%nat.
Proof. vm_compute; reflexivity. Qed.

Example ns_two_strings : ns_grundy [] [(ground, 1); (ground, 2)] = 0%nat.
Proof. vm_compute; reflexivity. Qed.

(** With the coin present the single string is a scoring cut, so the turn
    runs on and leaves nothing: the value drops to zero. *)
Example ns_one_string_with_coin : ns_grundy [1] [(ground, 1)] = 0%nat.
Proof. vm_compute; reflexivity. Qed.
