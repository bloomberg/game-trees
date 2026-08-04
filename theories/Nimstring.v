(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Nimstring on a loony position.

    Nimstring is Strings and Coins under normal play: the player who cannot
    move loses, and completing a coin still grants another move. On a loony
    position, where every component is a long chain or a loop, a turn consumes
    exactly one component, so the game tree is the tree of component removals
    and the position is an impartial game in the sense of [GameTrees.Grundy].

    [nimstring_grundy] computes its Grundy value: it is the parity of the
    number of components. So the opener of a loony Nimstring position wins
    exactly when the component count is odd, which is the same parity that
    [DotsAndBoxesBoard.long_chain_identity] tracks through the doublecrosses. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.
Require Import GameTrees.Helpers.
Require Import GameTrees.Trees.
Require Import GameTrees.Grundy.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.StringsAndCoins.

Import ListNotations.

(** * The Nimstring tree of a loony position *)

(** One turn removes one component. The fuel bounds the number of turns, and
    a turn always removes a component, so the position's own length is
    enough. *)
Fixpoint nstree (fuel : nat) (G : position) : Grundy.game :=
  match fuel with
  | O => node tt []
  | S f => node tt (map (fun p => nstree f (snd p)) (selections G))
  end.

Lemma nstree_nil : forall fuel, nstree fuel [] = node tt [].
Proof. intros [|f]; reflexivity. Qed.

(** * Everything a turn can leave has the same Grundy value *)

Lemma mex_all_zero :
  forall l, l <> [] -> (forall x, In x l -> x = 0%nat) -> mex l = 1%nat.
Proof.
  intros l Hne Hall; apply mex_unique.
  - intros Hin; pose proof (Hall 1%nat Hin); discriminate.
  - intros x Hx.
    assert (Hx0 : x = 0%nat) by lia; subst x.
    destruct l as [|a l]; [contradiction|].
    rewrite <- (Hall a (or_introl eq_refl)); left; reflexivity.
Qed.

Lemma mex_all_one :
  forall l, (forall x, In x l -> x = 1%nat) -> mex l = 0%nat.
Proof.
  intros l Hall; apply mex_unique.
  - intros Hin; pose proof (Hall 0%nat Hin); discriminate.
  - intros x Hx; lia.
Qed.

(** * The Grundy value *)

Definition parity (k : nat) : nat := if Nat.even k then 0 else 1.

Lemma parity_succ : forall k, parity (S k) = (if Nat.even k then 1 else 0)%nat.
Proof.
  intros k; unfold parity; rewrite Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even k); reflexivity.
Qed.

(** The value of a loony Nimstring position is the parity of its component
    count. *)
Theorem nimstring_grundy :
  forall fuel G,
    (length G <= fuel)%nat -> grundy (nstree fuel G) = parity (length G).
Proof.
  induction fuel as [|f IH]; intros G Hf.
  - assert (HG : G = []) by (destruct G; simpl in Hf; [reflexivity | lia]).
    subst G; reflexivity.
  - simpl nstree; rewrite grundy_eq, map_map.
    destruct G as [|C G].
    + simpl; reflexivity.
    + simpl length in Hf.
      assert (Hchild : forall x,
        In x (map (fun p => grundy (nstree f (snd p))) (selections (C :: G))) ->
        x = parity (length G)).
      { intros x Hx; apply in_map_iff in Hx; destruct Hx as [p [<- Hp]].
        pose proof (selections_length (C :: G) p Hp) as Hl; simpl in Hl.
        rewrite (IH (snd p)) by lia.
        f_equal; lia. }
      assert (Hne : map (fun p => grundy (nstree f (snd p)))
                        (selections (C :: G)) <> []).
      { simpl selections; simpl map; discriminate. }
      simpl length; rewrite parity_succ.
      destruct (Nat.even (length G)) eqn:Ev.
      * apply mex_all_zero; [exact Hne|].
        intros x Hx; rewrite (Hchild x Hx); unfold parity; rewrite Ev;
          reflexivity.
      * apply mex_all_one.
        intros x Hx; rewrite (Hchild x Hx); unfold parity; rewrite Ev;
          reflexivity.
Qed.

Definition nimstring (G : position) : Grundy.game := nstree (length G) G.

Corollary nimstring_value :
  forall G, grundy (nimstring G) = parity (length G).
Proof. intros G; apply nimstring_grundy; lia. Qed.

(** So the player to move wins exactly on an odd number of components. *)
Theorem nimstring_opener_wins :
  forall G, winb (nimstring G) = true <-> Nat.odd (length G) = true.
Proof.
  intros G; rewrite winb_grundy, nimstring_value.
  unfold parity; rewrite <- Nat.negb_even.
  destruct (Nat.even (length G)); simpl; split;
    solve [intros H; exfalso; apply H; reflexivity
          | discriminate | intros _; discriminate | intros _; reflexivity].
Qed.

(** A single component is a first player win, and two are a second player
    win: the alternation the long chain rule counts. *)
Example nimstring_one : forall C, winb (nimstring [C]) = true.
Proof. intros C; apply nimstring_opener_wins; reflexivity. Qed.

Example nimstring_two : forall C D, winb (nimstring [C; D]) = false.
Proof.
  intros C D; destruct (winb (nimstring [C; D])) eqn:E; [|reflexivity].
  apply nimstring_opener_wins in E; discriminate.
Qed.

(** ****************************************************************** *)
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

(** ****************************************************************** *)
(** Nimstring on a graph that splits.

    [GameTrees.Nimstring] gives the Grundy value of a Nimstring
    position and, through [ns_grundy_sum], the exclusive or for a [tsum] of
    two games. It never says when a position is such a sum. This file settles
    that it never is.

    Two edge lists are separate when no coin still
    in play is held by both: every coin of [V1] is already free of [g2] and
    every coin of [V2] free of [g1]. A cut in one half then frees only coins
    of that half, which [scores_split_l] and [scores_split_r] prove.

    That is as far as the separation goes. A cut which scores obliges another
    cut, and the mover may take it anywhere, so a turn beginning in one half
    can end in the other. Those crossing turns are options no disjunctive sum
    offers, and [ns_grundy_not_additive] exhibits a separated pair where they
    change the value: two halves worth one apiece whose union is worth two
    rather than the exclusive or, zero.

    So Nimstring values do not add over separated graphs, and
    [NimstringGeneral.ns_grundy_sum], which is [Grundy.grundy_tsum] restated,
    describes a decomposition that Strings and Coins does not admit. The
    lemmas below are the part of the separation that does hold. *)

(** * Degrees across an append *)

Lemma incident_app :
  forall g1 g2 x, incident (g1 ++ g2) x = incident g1 x ++ incident g2 x.
Proof.
  intros g1 g2 x; unfold incident; apply filter_app.
Qed.

Lemma deg_app : forall g1 g2 x, (deg (g1 ++ g2) x = deg g1 x + deg g2 x)%nat.
Proof.
  intros g1 g2 x; unfold deg; rewrite incident_app, length_app; reflexivity.
Qed.

Lemma freeb_app :
  forall g1 g2 x, freeb (g1 ++ g2) x = (freeb g1 x && freeb g2 x)%bool.
Proof.
  intros g1 g2 x; unfold freeb; rewrite deg_app.
  destruct (deg g1 x) as [|a] eqn:E1; destruct (deg g2 x) as [|b] eqn:E2;
    simpl; reflexivity.
Qed.

(** * Cutting only shrinks a degree *)

Lemma deg_cut_le : forall s g x, (deg (cut s g) x <= deg g x)%nat.
Proof.
  intros s g x; unfold cut, deg, incident.
  induction g as [|t r IH]; simpl; [lia|].
  destruct ((fst t =? fst s) && (snd t =? snd s))%bool.
  - destruct (touches x t); simpl; lia.
  - simpl; destruct (touches x t); simpl; lia.
Qed.

Lemma freeb_cut_mono :
  forall s g x, freeb g x = true -> freeb (cut s g) x = true.
Proof.
  intros s g x H; unfold freeb in *.
  apply Nat.eqb_eq in H; apply Nat.eqb_eq.
  pose proof (deg_cut_le s g x); lia.
Qed.

(** * Cutting across an append *)

Definition smatch (t s : strng) : bool :=
  ((fst t =? fst s) && (snd t =? snd s))%bool.

Lemma smatch_refl : forall s, smatch s s = true.
Proof. intros s; unfold smatch; rewrite !Nat.eqb_refl; reflexivity. Qed.

(** A cut whose string lies in the first half stays in the first half. *)
Lemma cut_app_l :
  forall s g1 g2,
    existsb (fun t => smatch t s) g1 = true ->
    cut s (g1 ++ g2) = cut s g1 ++ g2.
Proof.
  intros s g1 g2; unfold cut; induction g1 as [|t r IH]; intros H;
    [discriminate|].
  simpl in H |- *.
  destruct (smatch t s) eqn:Et; unfold smatch in Et; rewrite Et.
  - reflexivity.
  - simpl in H; rewrite (IH H); reflexivity.
Qed.

(** And one that matches nothing there falls through to the second. *)
Lemma cut_app_r :
  forall s g1 g2,
    existsb (fun t => smatch t s) g1 = false ->
    cut s (g1 ++ g2) = g1 ++ cut s g2.
Proof.
  intros s g1 g2; unfold cut; induction g1 as [|t r IH]; intros H;
    [reflexivity|].
  simpl in H |- *.
  apply orb_false_iff in H; destruct H as [Et Hr].
  unfold smatch in Et; rewrite Et.
  rewrite (IH Hr); reflexivity.
Qed.

Lemma existsb_smatch_of_In :
  forall s g, In s g -> existsb (fun t => smatch t s) g = true.
Proof.
  intros s g H; apply existsb_exists; exists s; split;
    [exact H | apply smatch_refl].
Qed.

(** * Separation *)

(** The coins of [V1] are already free of [g2], and those of [V2] of [g1], so
    neither half can free a coin belonging to the other. *)
Definition sep (V1 V2 : list coin) (g1 g2 : sgraph) : Prop :=
  (forall x, In x V1 -> freeb g2 x = true) /\
  (forall x, In x V2 -> freeb g1 x = true).

Lemma sep_cut_l :
  forall V1 V2 g1 g2 s, sep V1 V2 g1 g2 -> sep V1 V2 (cut s g1) g2.
Proof.
  intros V1 V2 g1 g2 s [H1 H2]; split.
  - exact H1.
  - intros x Hx; apply freeb_cut_mono, H2, Hx.
Qed.

Lemma sep_cut_r :
  forall V1 V2 g1 g2 s, sep V1 V2 g1 g2 -> sep V1 V2 g1 (cut s g2).
Proof.
  intros V1 V2 g1 g2 s [H1 H2]; split.
  - intros x Hx; apply freeb_cut_mono, H1, Hx.
  - exact H2.
Qed.

Lemma existsb_false_forall :
  forall {A : Type} (f : A -> bool) (l : list A),
    (forall x, In x l -> f x = false) -> existsb f l = false.
Proof.
  intros A f l; induction l as [|a l IH]; intros H; simpl; [reflexivity|].
  rewrite (H a (or_introl eq_refl)); simpl.
  apply IH; intros x Hx; apply H; right; exact Hx.
Qed.

(** * Scoring across a split *)

Lemma scores_app :
  forall V l g, scores V g l = existsb (fun x => negb (freeb g x) && freeb (cut l g) x)%bool V.
Proof. reflexivity. Qed.

(** A cut in the first half scores exactly the coins of [V1] it frees. *)
Lemma scores_split_l :
  forall V1 V2 g1 g2 s,
    sep V1 V2 g1 g2 ->
    In s g1 ->
    scores (V1 ++ V2) (g1 ++ g2) s = scores V1 g1 s.
Proof.
  intros V1 V2 g1 g2 s [Hs1 Hs2] Hin.
  rewrite !scores_app, existsb_app.
  rewrite (cut_app_l s g1 g2 (existsb_smatch_of_In s g1 Hin)).
  assert (E1 : existsb (fun x => negb (freeb (g1 ++ g2) x)
                                 && freeb (cut s g1 ++ g2) x)%bool V1
             = existsb (fun x => negb (freeb g1 x)
                                 && freeb (cut s g1) x)%bool V1).
  { apply existsb_ext_in; intros x Hx.
    rewrite !freeb_app, (Hs1 x Hx), !andb_true_r; reflexivity. }
  assert (E2 : existsb (fun x => negb (freeb (g1 ++ g2) x)
                                 && freeb (cut s g1 ++ g2) x)%bool V2
             = false).
  { apply existsb_false_forall; intros x Hx.
    rewrite !freeb_app, (Hs2 x Hx); simpl.
    rewrite (freeb_cut_mono s g1 x (Hs2 x Hx)); simpl.
    destruct (freeb g2 x); reflexivity. }
  rewrite E1, E2, orb_false_r; reflexivity.
Qed.

(** Symmetrically for the second half. *)
Lemma scores_split_r :
  forall V1 V2 g1 g2 s,
    sep V1 V2 g1 g2 ->
    existsb (fun t => smatch t s) g1 = false ->
    In s g2 ->
    scores (V1 ++ V2) (g1 ++ g2) s = scores V2 g2 s.
Proof.
  intros V1 V2 g1 g2 s [Hs1 Hs2] Hno Hin.
  rewrite !scores_app, existsb_app.
  rewrite (cut_app_r s g1 g2 Hno).
  assert (E2 : existsb (fun x => negb (freeb (g1 ++ g2) x)
                                 && freeb (g1 ++ cut s g2) x)%bool V2
             = existsb (fun x => negb (freeb g2 x)
                                 && freeb (cut s g2) x)%bool V2).
  { apply existsb_ext_in; intros x Hx.
    rewrite !freeb_app, (Hs2 x Hx), !andb_true_l; reflexivity. }
  assert (E1 : existsb (fun x => negb (freeb (g1 ++ g2) x)
                                 && freeb (g1 ++ cut s g2) x)%bool V1
             = false).
  { apply existsb_false_forall; intros x Hx.
    rewrite !freeb_app, (Hs1 x Hx), andb_true_r.
    rewrite (freeb_cut_mono s g2 x (Hs1 x Hx)), andb_true_r.
    destruct (freeb g1 x); reflexivity. }
  rewrite E1, E2, orb_false_l; reflexivity.
Qed.


(** * The sum law fails *)

(** Two halves that share no coin. The first is a coin held by two ground
    strings; the second is a coin on the ground carrying a second coin behind
    it, so that cutting its outer string frees nothing but cutting the inner
    one does. *)
Definition cx_g1 : sgraph := [(0, 1); (0, 1)].
Definition cx_g2 : sgraph := [(0, 2); (2, 4)].
Definition cx_V1 : list coin := [1; 3].
Definition cx_V2 : list coin := [2; 4].

Lemma cx_sep : sep cx_V1 cx_V2 cx_g1 cx_g2.
Proof.
  split; intros x Hx; simpl in Hx;
    destruct Hx as [<- | [<- | []]]; vm_compute; reflexivity.
Qed.

(** Each half is worth one and the union is worth two, where the exclusive or
    is zero: the crossing turns are real options and they raise the value. *)
Lemma cx_values :
  ns_grundy cx_V1 cx_g1 = 1%nat /\
  ns_grundy cx_V2 cx_g2 = 1%nat /\
  ns_grundy (cx_V1 ++ cx_V2) (cx_g1 ++ cx_g2) = 2%nat.
Proof. repeat split; vm_compute; reflexivity. Qed.

(** So Nimstring values do not add over separated graphs. *)
Theorem ns_grundy_not_additive :
  exists V1 V2 g1 g2,
    sep V1 V2 g1 g2 /\
    ns_grundy (V1 ++ V2) (g1 ++ g2)
      <> Nat.lxor (ns_grundy V1 g1) (ns_grundy V2 g2).
Proof.
  exists cx_V1, cx_V2, cx_g1, cx_g2; split;
    [exact cx_sep | vm_compute; discriminate].
Qed.

(** And the failure is not an artefact of the separation being too weak: the
    halves are disjoint in the strongest sense available, each leaving every
    coin of the other untouched. *)
Corollary ns_grundy_not_additive_strict :
  (forall x, In x cx_V1 -> freeb cx_g2 x = true) /\
  (forall x, In x cx_V2 -> freeb cx_g1 x = true) /\
  ns_grundy (cx_V1 ++ cx_V2) (cx_g1 ++ cx_g2)
    <> Nat.lxor (ns_grundy cx_V1 cx_g1) (ns_grundy cx_V2 cx_g2).
Proof.
  destruct cx_sep as [H1 H2]; repeat split;
    [exact H1 | exact H2 | vm_compute; discriminate].
Qed.
