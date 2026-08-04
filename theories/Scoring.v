(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Scoring games, and the loony endgame as one of them.

    A scoring game is a rose tree carrying, at each node, the score a finished
    game pays to Left, the player whose turn it is, and that player's options.
    The mover is written into the node rather than alternating, because in a
    scoring game a player who scores keeps the move.

    [eg] builds the loony endgame of [GameTrees.DotsAndBoxes] as such a game,
    with the moves spelled out: the opener names a component, and the
    controller either takes it whole and becomes the opener, or leaves the
    handout and stays in control. Boxes are banked as they are taken, with the
    sign of the player taking them. [score_eg] proves the optimal score of
    that game is the [value] of the position, so [value] is the score of a
    game whose rules are written down rather than a recursion asserted to
    model one. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.

Open Scope Z_scope.

(** * Scoring games *)

(** [SG s lft opts]: with [opts] empty the game is over and pays [s] to Left;
    otherwise the player named by [lft] chooses among [opts]. *)
Inductive sgame : Type :=
| SG : Z -> bool -> list sgame -> sgame.

Definition maxl (x : Z) (l : list Z) : Z := fold_left Z.max l x.

(** The optimal score to Left, Left maximising and Right minimising. *)
Fixpoint score (g : sgame) : Z :=
  match g with
  | SG s lft opts =>
      match map score opts with
      | [] => s
      | v :: vs => if lft then maxl v vs else minl v vs
      end
  end.

Lemma score_node :
  forall s lft opts,
    score (SG s lft opts) =
    match map score opts with
    | [] => s
    | v :: vs => if lft then maxl v vs else minl v vs
    end.
Proof. reflexivity. Qed.

Lemma score_two_left :
  forall s a b, score (SG s true [a; b]) = Z.max (score a) (score b).
Proof. reflexivity. Qed.

Lemma score_two_right :
  forall s a b, score (SG s false [a; b]) = Z.min (score a) (score b).
Proof. reflexivity. Qed.

(** * Banking a constant through a game *)

Lemma minl_add_shift :
  forall l a x,
    fold_left Z.min (map (Z.add a) l) (a + x) = a + fold_left Z.min l x.
Proof.
  induction l as [|y l IH]; intros a x; simpl; [reflexivity|].
  replace (Z.min (a + x) (a + y)) with (a + Z.min x y) by lia.
  apply IH.
Qed.

Lemma maxl_sub_shift :
  forall l a x,
    fold_left Z.max (map (fun z => a - z) l) (a - x) = a - fold_left Z.min l x.
Proof.
  induction l as [|y l IH]; intros a x; simpl; [reflexivity|].
  replace (Z.max (a - x) (a - y)) with (a - Z.min x y) by lia.
  apply IH.
Qed.

(** * The loony endgame as a scoring game *)

(** Boxes taken by the player who is not the opener, banked with that
    player's sign. Left is [true]. *)
Definition bank (p : bool) (acc x : Z) : Z := if p then acc - x else acc + x.

Lemma bank_true : forall acc x, bank true acc x = acc - x.
Proof. reflexivity. Qed.

Lemma bank_false : forall acc x, bank false acc x = acc + x.
Proof. reflexivity. Qed.

(** [eg fuel acc G p]: the endgame on [G], with [acc] already banked to Left
    and the opener named by [p]. *)
Fixpoint eg (fuel : nat) (acc : Z) (G : position) (p : bool) : sgame :=
  match fuel with
  | O => SG acc p []
  | S f =>
      match selections G with
      | [] => SG acc p []
      | _ :: _ =>
          SG acc p
            (map (fun pr =>
               SG acc (negb p)
                 [ eg f (bank p acc (Z.of_nat (csize (fst pr)))) (snd pr) (negb p) ;
                   eg f (bank p acc (Z.of_nat (csize (fst pr))
                                     - 2 * Z.of_nat (hand (fst pr)))) (snd pr) p ])
             (selections G))
      end
  end.

Lemma eg_cons :
  forall f acc G p,
    selections G <> [] ->
    eg (S f) acc G p =
    SG acc p
      (map (fun pr =>
         SG acc (negb p)
           [ eg f (bank p acc (Z.of_nat (csize (fst pr)))) (snd pr) (negb p) ;
             eg f (bank p acc (Z.of_nat (csize (fst pr))
                               - 2 * Z.of_nat (hand (fst pr)))) (snd pr) p ])
       (selections G)).
Proof.
  intros f acc G p H; simpl eg.
  destruct (selections G) as [|a l] eqn:E; [contradiction | reflexivity].
Qed.

(** * The endgame scores its value *)

Theorem score_eg :
  forall fuel acc G p,
    (length G <= fuel)%nat ->
    score (eg fuel acc G p) = if p then acc - value G else acc + value G.
Proof.
  induction fuel as [|f IH]; intros acc G p Hf.
  - assert (HG : G = []) by (destruct G; simpl in Hf; [reflexivity | lia]).
    subst G; rewrite value_nil; simpl score; destruct p; lia.
  - destruct (list_eq_dec comp_eq_dec G []) as [-> | HNil].
    { simpl eg; simpl score; rewrite value_nil; destruct p; lia. }
    assert (Hsel : selections G <> [])
      by (intros Hz; apply HNil, selections_nil_iff; exact Hz).
    rewrite (eg_cons f acc G p Hsel), score_node, map_map.
    (* every option is worth the handout algebra, banked *)
    assert (Hopt : forall pr, In pr (selections G) ->
      score (SG acc (negb p)
               [ eg f (bank p acc (Z.of_nat (csize (fst pr)))) (snd pr) (negb p) ;
                 eg f (bank p acc (Z.of_nat (csize (fst pr))
                                   - 2 * Z.of_nat (hand (fst pr)))) (snd pr) p ])
      = bank p acc (value_open pr)).
    { intros pr Hpr.
      assert (Hlen : (length (snd pr) <= f)%nat)
        by (pose proof (selections_length G pr Hpr); lia).
      assert (Ht : forall a, score (eg f a (snd pr) true) = a - value (snd pr))
        by (intros a; rewrite (IH a (snd pr) true) by exact Hlen; reflexivity).
      assert (Hfa : forall a, score (eg f a (snd pr) false) = a + value (snd pr))
        by (intros a; rewrite (IH a (snd pr) false) by exact Hlen; reflexivity).
      unfold value_open.
      destruct (Z.le_gt_cases (value (snd pr)) (Z.of_nat (hand (fst pr))))
        as [Hle | Hgt].
      - rewrite (controller_gives_up (fst pr) (value (snd pr)) Hle).
        unfold give_up_control.
        destruct p; cbn [negb bank].
        + rewrite score_two_right, Hfa, Ht; lia.
        + rewrite score_two_left, Ht, Hfa; lia.
      - rewrite (controller_keeps (fst pr) (value (snd pr)) ltac:(lia)).
        unfold keep_control.
        destruct p; cbn [negb bank].
        + rewrite score_two_right, Hfa, Ht; lia.
        + rewrite score_two_left, Ht, Hfa; lia. }
    rewrite (map_ext_in _ (fun pr => bank p acc (value_open pr))
               (selections G) Hopt).
    (* now read off the opener's choice *)
    pose proof (value_unfold G) as Hval.
    destruct (selections G) as [|s0 more] eqn:Esel; [contradiction|].
    simpl map.
    assert (Hshape : map (fun pr => bank p acc (value_open pr)) more =
                     map (fun z => bank p acc z) (map value_open more))
      by (rewrite map_map; reflexivity).
    rewrite Hshape.
    destruct p; unfold bank, maxl, minl in *; rewrite Hval.
    + rewrite maxl_sub_shift; reflexivity.
    + rewrite minl_add_shift; reflexivity.
Qed.

(** The endgame value, read off the game rather than the recursion: with
    Right to open, the score Left secures is exactly [value]. *)
Corollary score_eg_root :
  forall G, score (eg (length G) 0 G false) = value G.
Proof. intros G; rewrite score_eg by lia; lia. Qed.

(** And with Left to open it is its negation, since the roles are swapped. *)
Corollary score_eg_root_left :
  forall G, score (eg (length G) 0 G true) = - value G.
Proof. intros G; rewrite score_eg by lia; lia. Qed.
