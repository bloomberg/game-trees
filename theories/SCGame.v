(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Strings and Coins as a game on an arbitrary graph.

    [GameTrees.StringsAndCoins] gives the graph and the duality with the
    board, but no play: it says what a position looks like, not what a move
    is. Here a state carries the strings still uncut, the coins not yet
    collected, the two scores and the mover. A move cuts a string; every coin
    the cut sets loose is collected by the mover, who then keeps the move,
    exactly as completing a box grants another turn on the board.

    Cutting removes a string, so [sc_measure] falls at every move and the
    game is finite on any graph. [sc_determined] is Zermelo's theorem for it,
    read off [GameTrees.Determinacy] in the three-way form, since Strings and
    Coins can be drawn. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.Determinacy.
Require Import GameTrees.StringsAndCoins.

(** * Cutting removes a string *)

Definition strng_eqb (s t : strng) : bool :=
  ((fst s =? fst t) && (snd s =? snd t))%bool.

Lemma strng_eqb_true_iff : forall s t, strng_eqb s t = true <-> s = t.
Proof.
  intros [a b] [c d]; unfold strng_eqb; simpl; split.
  - intros H; apply andb_true_iff in H; destruct H as [H1 H2].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2; subst; reflexivity.
  - intros H; injection H as -> ->; rewrite !Nat.eqb_refl; reflexivity.
Qed.

Lemma strng_eqb_refl : forall s, strng_eqb s s = true.
Proof. intros s; apply strng_eqb_true_iff; reflexivity. Qed.

Definition smemb (s : strng) (g : sgraph) : bool := existsb (strng_eqb s) g.

Lemma smemb_true_iff : forall s g, smemb s g = true <-> In s g.
Proof.
  intros s g; unfold smemb; rewrite existsb_exists; split.
  - intros [x [Hx He]]; apply strng_eqb_true_iff in He; subst; auto.
  - intros H; exists s; split; [exact H | apply strng_eqb_refl].
Qed.

(** A cut really removes one string, so the graph shrinks. *)
Lemma cut_length_lt :
  forall s g, In s g -> (length (cut s g) < length g)%nat.
Proof.
  intros s g; unfold cut; induction g as [|t r IH]; intros H; [destruct H|].
  simpl remove_one.
  destruct ((fst t =? fst s) && (snd t =? snd s))%bool eqn:E.
  - simpl; lia.
  - destruct H as [Heq | H].
    + exfalso; subst t; rewrite !Nat.eqb_refl in E; discriminate.
    + specialize (IH H); simpl; lia.
Qed.

(** * Coins *)

Definition cmemb (x : coin) (l : list coin) : bool := existsb (Nat.eqb x) l.

Lemma cmemb_true_iff : forall x l, cmemb x l = true <-> In x l.
Proof.
  intros x l; unfold cmemb; rewrite existsb_exists; split.
  - intros [y [Hy He]]; apply Nat.eqb_eq in He; subst; auto.
  - intros H; exists x; split; [exact H | apply Nat.eqb_refl].
Qed.

(** * States and moves *)

(** The strings still uncut, the coins not yet collected, the two scores, and
    whether the first player is to move. *)
Record scst : Type :=
  MkSC { sgr : sgraph ; cvs : list coin ; c1 : nat ; c2 : nat ; sp1 : bool }.

Definition sc_init (g : sgraph) (V : list coin) : scst := MkSC g V 0 0 true.

Definition sc_moves (t : scst) : list strng := sgr t.

(** The coins the cut sets loose. *)
Definition collect (t : scst) (s : strng) : list coin :=
  filter (fun x => freeb (cut s (sgr t)) x) (cvs t).

Definition keep (t : scst) (s : strng) : list coin :=
  filter (fun x => negb (freeb (cut s (sgr t)) x)) (cvs t).

(** Cutting a string. A player who frees a coin collects it and keeps the
    move, so the mover is written into the state rather than alternating. *)
Definition sc_play (t : scst) (s : strng) : scst :=
  let g' := cut s (sgr t) in
  let got := collect t s in
  let v' := keep t s in
  match got with
  | [] => MkSC g' v' (c1 t) (c2 t) (negb (sp1 t))
  | _ :: _ =>
      if sp1 t
      then MkSC g' v' (c1 t + length got) (c2 t) true
      else MkSC g' v' (c1 t) (c2 t + length got) false
  end.

Lemma sgr_play : forall t s, sgr (sc_play t s) = cut s (sgr t).
Proof.
  intros t s; unfold sc_play.
  destruct (collect t s); [reflexivity | destruct (sp1 t); reflexivity].
Qed.

Definition sc_amove (t : scst) : bool := sp1 t.

Definition sc_outc (t : scst) : option outcome :=
  match sc_moves t with
  | [] =>
      Some (if Nat.ltb (c2 t) (c1 t) then win true
            else if Nat.ltb (c1 t) (c2 t) then win false
            else drawn)
  | _ :: _ => None
  end.

Lemma sc_outc_none_iff : forall t, sc_outc t = None <-> sc_moves t <> [].
Proof.
  intros t; unfold sc_outc; destruct (sc_moves t); split;
    try discriminate; try reflexivity.
  intros H; contradiction.
Qed.

Lemma sc_no_stall :
  forall t, sc_outc t = None -> exists s, In s (sc_moves t).
Proof.
  intros t H; apply sc_outc_none_iff in H.
  destruct (sc_moves t) as [|s r] eqn:E; [contradiction|].
  exists s; left; reflexivity.
Qed.

(** * Termination *)

Definition sc_measure (t : scst) : nat := length (sgr t).

Lemma sc_measure_play :
  forall t s, In s (sc_moves t) -> (sc_measure (sc_play t s) < sc_measure t)%nat.
Proof.
  intros t s H; unfold sc_measure; rewrite sgr_play.
  apply cut_length_lt; exact H.
Qed.

(** * Determinacy *)

(** Strings and Coins is determined on every graph. Coins can be split
    evenly, so this is the three-way form. *)
Theorem sc_determined :
  forall fuel t,
    (sc_measure t <= fuel)%nat ->
    forces sc_moves sc_play sc_amove sc_outc true fuel t \/
    forces sc_moves sc_play sc_amove sc_outc false fuel t \/
    (nonloss sc_moves sc_play sc_amove sc_outc true fuel t /\
     nonloss sc_moves sc_play sc_amove sc_outc false fuel t).
Proof.
  intros fuel t Hf.
  apply (zermelo_three_way sc_moves sc_play sc_amove sc_outc
           (fun _ : scst => True) sc_measure).
  - intros u s _ _ _; exact I.
  - intros u s _ _ Hs; apply sc_measure_play; exact Hs.
  - intros u _ Ho; apply sc_no_stall; exact Ho.
  - exact I.
  - exact Hf.
Qed.

Corollary sc_determined_init :
  forall g V,
    forces sc_moves sc_play sc_amove sc_outc true (length g) (sc_init g V) \/
    forces sc_moves sc_play sc_amove sc_outc false (length g) (sc_init g V) \/
    (nonloss sc_moves sc_play sc_amove sc_outc true (length g) (sc_init g V) /\
     nonloss sc_moves sc_play sc_amove sc_outc false (length g) (sc_init g V)).
Proof. intros g V; apply sc_determined; unfold sc_measure; simpl; lia. Qed.

Theorem sc_not_both :
  forall fuel t,
    forces sc_moves sc_play sc_amove sc_outc true fuel t ->
    forces sc_moves sc_play sc_amove sc_outc false fuel t -> False.
Proof.
  intros fuel t H1 H2.
  exact (forces_not_both sc_moves sc_play sc_amove sc_outc fuel t H1 H2).
Qed.

(** * Boolean search *)

Definition sc_forces_b (who : bool) (fuel : nat) (t : scst) : bool :=
  forces_b sc_moves sc_play sc_amove sc_outc who fuel t.

Lemma sc_forces_b_correct :
  forall who fuel t,
    sc_forces_b who fuel t = true <->
    forces sc_moves sc_play sc_amove sc_outc who fuel t.
Proof.
  intros who fuel t; apply (forces_b_correct sc_moves sc_play sc_amove sc_outc).
Qed.

(** * Accounting *)

(** Every coin is either kept or collected, so the two lists partition the
    uncollected coins. *)
Lemma collect_keep_length :
  forall t s,
    (length (collect t s) + length (keep t s) = length (cvs t))%nat.
Proof.
  intros t s; unfold collect, keep.
  induction (cvs t) as [|x l IH]; simpl; [reflexivity|].
  destruct (freeb (cut s (sgr t)) x); simpl; lia.
Qed.

Lemma cvs_play : forall t s, cvs (sc_play t s) = keep t s.
Proof.
  intros t s; unfold sc_play.
  destruct (collect t s); [reflexivity | destruct (sp1 t); reflexivity].
Qed.

Definition sc_scored (t : scst) : nat := (c1 t + c2 t)%nat.

(** The score rises by exactly the coins the cut freed. *)
Lemma sc_scored_play :
  forall t s, sc_scored (sc_play t s) = (sc_scored t + length (collect t s))%nat.
Proof.
  intros t s; unfold sc_play, sc_scored.
  destruct (collect t s) as [|x l] eqn:E; simpl; [lia|].
  destruct (sp1 t); simpl; lia.
Qed.

(** So the coins still in play fall by exactly what was banked. *)
Theorem sc_conservation :
  forall t s,
    (sc_scored (sc_play t s) + length (cvs (sc_play t s))
     = sc_scored t + length (cvs t))%nat.
Proof.
  intros t s; rewrite sc_scored_play, cvs_play.
  pose proof (collect_keep_length t s); lia.
Qed.

(** * A solved instance *)

(** A single string joining the ground to one coin: the mover cuts it, takes
    the coin, and has no move left, so the first player wins. *)
Definition one_coin : sgraph := [(ground, 1)].

Example one_coin_first_player_wins :
  sc_forces_b true 2 (sc_init one_coin [1]) = true.
Proof. vm_compute; reflexivity. Qed.

(** Two separate coins, each on its own string to the ground: the first
    player takes both, since scoring keeps the move. *)
Definition two_coins : sgraph := [(ground, 1); (ground, 2)].

Example two_coins_first_player_wins :
  sc_forces_b true 4 (sc_init two_coins [1; 2]) = true.
Proof. vm_compute; reflexivity. Qed.

(** A chain of two coins between two ground strings: whoever cuts first hands
    both coins over, so the first player loses. *)
Definition two_chain : sgraph := [(ground, 1); (1, 2); (2, ground)].

Example two_chain_second_player_wins :
  sc_forces_b false 6 (sc_init two_chain [1; 2]) = true.
Proof. vm_compute; reflexivity. Qed.
