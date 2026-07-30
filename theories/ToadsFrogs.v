(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Toads and Frogs: Left moves toads rightward, Right moves frogs leftward. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.

Import ListNotations.

Require Import GameTrees.Conway.

(** * Boards *)

Inductive square : Type := Empty | Toad | Frog.

Definition board : Type := list square.

(** Left's moves at the leftmost square: a slide, or a jump over one frog. *)
Definition ltop (rest : board) : list board :=
  match rest with
  | Empty :: r => [Empty :: Toad :: r]
  | Frog :: Empty :: r => [Empty :: Frog :: Toad :: r]
  | _ => []
  end.

(** Right's moves at the leftmost square: a slide, or a jump over one toad. *)
Definition rtop (rest : board) : list board :=
  match rest with
  | Frog :: r => [Frog :: Empty :: r]
  | Toad :: Frog :: r => [Frog :: Toad :: Empty :: r]
  | _ => []
  end.

Fixpoint lmoves (b : board) : list board :=
  match b with
  | [] => []
  | Toad :: rest => ltop rest ++ map (fun r => Toad :: r) (lmoves rest)
  | x :: rest => map (fun r => x :: r) (lmoves rest)
  end.

Fixpoint rmoves (b : board) : list board :=
  match b with
  | [] => []
  | Empty :: rest => rtop rest ++ map (fun r => Empty :: r) (rmoves rest)
  | x :: rest => map (fun r => x :: r) (rmoves rest)
  end.

(** Unfolding equations for the move lists. *)

Lemma lmoves_toad :
  forall rest,
    lmoves (Toad :: rest) = ltop rest ++ map (fun r => Toad :: r) (lmoves rest).
Proof. reflexivity. Qed.

Lemma lmoves_empty :
  forall rest, lmoves (Empty :: rest) = map (fun r => Empty :: r) (lmoves rest).
Proof. reflexivity. Qed.

Lemma lmoves_frog :
  forall rest, lmoves (Frog :: rest) = map (fun r => Frog :: r) (lmoves rest).
Proof. reflexivity. Qed.

Lemma rmoves_empty :
  forall rest,
    rmoves (Empty :: rest) = rtop rest ++ map (fun r => Empty :: r) (rmoves rest).
Proof. reflexivity. Qed.

Lemma rmoves_toad :
  forall rest, rmoves (Toad :: rest) = map (fun r => Toad :: r) (rmoves rest).
Proof. reflexivity. Qed.

Lemma rmoves_frog :
  forall rest, rmoves (Frog :: rest) = map (fun r => Frog :: r) (rmoves rest).
Proof. reflexivity. Qed.

(** * The measure *)

Fixpoint frogs (b : board) : nat :=
  match b with
  | [] => 0
  | Frog :: r => S (frogs r)
  | _ :: r => frogs r
  end.

(** The distance the toads must still travel to reach the right end. *)
Fixpoint tmeasure (b : board) : nat :=
  match b with
  | [] => 0
  | Toad :: r => length r + tmeasure r
  | _ :: r => tmeasure r
  end.

(** The distance the frogs must still travel to reach the left end. *)
Fixpoint fmeasure (b : board) : nat :=
  match b with
  | [] => 0
  | _ :: r => frogs r + fmeasure r
  end.

Definition measure (b : board) : nat := tmeasure b + fmeasure b.

Lemma ltop_props :
  forall rest b',
    In b' (ltop rest) ->
    length b' = S (length rest) /\
    frogs b' = frogs (Toad :: rest) /\
    measure b' < measure (Toad :: rest).
Proof.
  intros rest b' H.
  destruct rest as [|x r]; [simpl in H; destruct H|].
  destruct x; simpl in H.
  - destruct H as [<- | []].
    unfold measure; simpl; repeat split; lia.
  - destruct H.
  - destruct r as [|y r']; [destruct H|].
    destruct y; simpl in H.
    + destruct H as [<- | []].
      unfold measure; simpl; repeat split; lia.
    + destruct H.
    + destruct H.
Qed.

Lemma rtop_props :
  forall rest b',
    In b' (rtop rest) ->
    length b' = S (length rest) /\
    frogs b' = frogs (Empty :: rest) /\
    measure b' < measure (Empty :: rest).
Proof.
  intros rest b' H.
  destruct rest as [|x r]; [simpl in H; destruct H|].
  destruct x; simpl in H.
  - destruct H.
  - destruct r as [|y r']; [destruct H|].
    destruct y; simpl in H.
    + destruct H.
    + destruct H.
    + destruct H as [<- | []].
      unfold measure; simpl; repeat split; lia.
  - destruct H as [<- | []].
    unfold measure; simpl; repeat split; lia.
Qed.

(** A move preserves the length and the frog count, and drops the measure. *)
Lemma lmoves_props :
  forall b b',
    In b' (lmoves b) ->
    length b' = length b /\ frogs b' = frogs b /\ measure b' < measure b.
Proof.
  induction b as [|x b IH]; intros b' Hb'; [destruct Hb'|].
  destruct x.
  - apply in_map_iff in Hb'; destruct Hb' as [r [<- Hr]].
    destruct (IH r Hr) as (H1 & H2 & H3).
    unfold measure in *; simpl in *; repeat split; lia.
  - apply in_app_or in Hb'; destruct Hb' as [Hb' | Hb'].
    + destruct (ltop_props b b' Hb') as (H1 & H2 & H3).
      simpl in *; repeat split; auto.
    + apply in_map_iff in Hb'; destruct Hb' as [r [<- Hr]].
      destruct (IH r Hr) as (H1 & H2 & H3).
      unfold measure in *; simpl in *; repeat split; lia.
  - apply in_map_iff in Hb'; destruct Hb' as [r [<- Hr]].
    destruct (IH r Hr) as (H1 & H2 & H3).
    unfold measure in *; simpl in *; repeat split; lia.
Qed.

Lemma rmoves_props :
  forall b b',
    In b' (rmoves b) ->
    length b' = length b /\ frogs b' = frogs b /\ measure b' < measure b.
Proof.
  induction b as [|x b IH]; intros b' Hb'; [destruct Hb'|].
  destruct x.
  - apply in_app_or in Hb'; destruct Hb' as [Hb' | Hb'].
    + destruct (rtop_props b b' Hb') as (H1 & H2 & H3).
      simpl in *; repeat split; auto.
    + apply in_map_iff in Hb'; destruct Hb' as [r [<- Hr]].
      destruct (IH r Hr) as (H1 & H2 & H3).
      unfold measure in *; simpl in *; repeat split; lia.
  - apply in_map_iff in Hb'; destruct Hb' as [r [<- Hr]].
    destruct (IH r Hr) as (H1 & H2 & H3).
    unfold measure in *; simpl in *; repeat split; lia.
  - apply in_map_iff in Hb'; destruct Hb' as [r [<- Hr]].
    destruct (IH r Hr) as (H1 & H2 & H3).
    unfold measure in *; simpl in *; repeat split; lia.
Qed.

Lemma lmoves_measure :
  forall b b', In b' (lmoves b) -> measure b' < measure b.
Proof. intros b b' H; apply (lmoves_props b b' H). Qed.

Lemma rmoves_measure :
  forall b b', In b' (rmoves b) -> measure b' < measure b.
Proof. intros b b' H; apply (rmoves_props b b' H). Qed.

(** * Counts and the mirror *)

Fixpoint toads (b : board) : nat :=
  match b with
  | [] => 0
  | Toad :: r => S (toads r)
  | _ :: r => toads r
  end.

Definition flip (x : square) : square :=
  match x with Empty => Empty | Toad => Frog | Frog => Toad end.

(** Reflecting the strip and exchanging the animals. *)
Definition mirror (b : board) : board := rev (map flip b).

Lemma flip_flip : forall x, flip (flip x) = x.
Proof. intros []; reflexivity. Qed.

Lemma mirror_app : forall b c, mirror (b ++ c) = mirror c ++ mirror b.
Proof.
  intros b c; unfold mirror.
  rewrite map_app, rev_app_distr; reflexivity.
Qed.

Lemma mirror_cons : forall x b, mirror (x :: b) = mirror b ++ [flip x].
Proof. intros x b; reflexivity. Qed.

Lemma mirror_mirror : forall b, mirror (mirror b) = b.
Proof.
  intros b; unfold mirror.
  rewrite map_rev, rev_involutive, map_map.
  rewrite (map_ext_in _ (fun x => x) b), map_id; auto.
  intros a _; apply flip_flip.
Qed.

Lemma length_mirror : forall b, length (mirror b) = length b.
Proof.
  intros b; unfold mirror; rewrite length_rev, length_map; reflexivity.
Qed.

Lemma toads_snoc :
  forall d y, toads (d ++ [y]) = toads d + (match y with Toad => 1 | _ => 0 end).
Proof.
  induction d as [|x d IH]; intros y; simpl.
  - destruct y; lia.
  - destruct x; rewrite IH; lia.
Qed.

Lemma frogs_snoc :
  forall d y, frogs (d ++ [y]) = frogs d + (match y with Frog => 1 | _ => 0 end).
Proof.
  induction d as [|x d IH]; intros y; simpl.
  - destruct y; lia.
  - destruct x; rewrite IH; lia.
Qed.

Lemma toads_mirror : forall b, toads (mirror b) = frogs b.
Proof.
  induction b as [|x b IH]; auto.
  rewrite mirror_cons, toads_snoc, IH.
  destruct x; simpl; lia.
Qed.

Lemma frogs_mirror : forall b, frogs (mirror b) = toads b.
Proof.
  induction b as [|x b IH]; auto.
  rewrite mirror_cons, frogs_snoc, IH.
  destruct x; simpl; lia.
Qed.

(** Appending a square moves every toad one step further from the right end. *)
Lemma tmeasure_snoc :
  forall d y, tmeasure (d ++ [y]) = tmeasure d + toads d.
Proof.
  induction d as [|x d IH]; intros y.
  - destruct y; reflexivity.
  - assert (Hl : length (d ++ [y]) = S (length d))
      by (rewrite length_app; simpl; lia).
    destruct x; simpl.
    + rewrite IH; lia.
    + rewrite IH, Hl; lia.
    + rewrite IH; lia.
Qed.

Lemma fmeasure_snoc :
  forall d y,
    fmeasure (d ++ [y]) =
    fmeasure d + (match y with Frog => length d | _ => 0 end).
Proof.
  induction d as [|x d IH]; intros y; simpl.
  - destruct y; reflexivity.
  - rewrite IH, frogs_snoc.
    destruct y; simpl; lia.
Qed.

Lemma tmeasure_mirror : forall b, tmeasure (mirror b) = fmeasure b.
Proof.
  induction b as [|x b IH]; auto.
  rewrite mirror_cons, tmeasure_snoc, IH, toads_mirror.
  destruct x; simpl; lia.
Qed.

Lemma fmeasure_mirror : forall b, fmeasure (mirror b) = tmeasure b.
Proof.
  induction b as [|x b IH]; auto.
  rewrite mirror_cons, fmeasure_snoc, IH, length_mirror.
  destruct x; simpl; lia.
Qed.

(** Mirroring exchanges the two travel distances, so it preserves the sum. *)
Lemma measure_mirror : forall b, measure (mirror b) = measure b.
Proof.
  intros b; unfold measure.
  rewrite tmeasure_mirror, fmeasure_mirror; lia.
Qed.

(** * The game of a board *)

Fixpoint tf (fuel : nat) (b : board) : pgame :=
  match fuel with
  | 0 => PG [] []
  | S f => PG (map (tf f) (lmoves b)) (map (tf f) (rmoves b))
  end.

Lemma measure_zero_no_lmoves :
  forall b, measure b = 0 -> lmoves b = [].
Proof.
  intros b Hz.
  destruct (lmoves b) as [|x l] eqn:E; auto.
  exfalso.
  pose proof (lmoves_measure b x) as Hlt.
  rewrite E in Hlt; specialize (Hlt (or_introl eq_refl)); lia.
Qed.

Lemma measure_zero_no_rmoves :
  forall b, measure b = 0 -> rmoves b = [].
Proof.
  intros b Hz.
  destruct (rmoves b) as [|x l] eqn:E; auto.
  exfalso.
  pose proof (rmoves_measure b x) as Hlt.
  rewrite E in Hlt; specialize (Hlt (or_introl eq_refl)); lia.
Qed.

Lemma tf_stable :
  forall N b f1 f2,
    measure b <= N -> measure b <= f1 -> measure b <= f2 ->
    tf f1 b = tf f2 b.
Proof.
  induction N as [|N IH]; intros b f1 f2 HN Hf1 Hf2.
  - assert (Hz : measure b = 0) by lia.
    pose proof (measure_zero_no_lmoves b Hz) as E1.
    pose proof (measure_zero_no_rmoves b Hz) as E2.
    destruct f1; destruct f2; simpl; rewrite ?E1, ?E2; reflexivity.
  - destruct f1 as [|f1]; destruct f2 as [|f2].
    + reflexivity.
    + assert (Hz : measure b = 0) by lia.
      pose proof (measure_zero_no_lmoves b Hz) as E1.
      pose proof (measure_zero_no_rmoves b Hz) as E2.
      simpl; rewrite E1, E2; reflexivity.
    + assert (Hz : measure b = 0) by lia.
      pose proof (measure_zero_no_lmoves b Hz) as E1.
      pose proof (measure_zero_no_rmoves b Hz) as E2.
      simpl; rewrite E1, E2; reflexivity.
    + simpl; f_equal; apply map_ext_in; intros m Hm.
      * pose proof (lmoves_measure b m Hm); apply (IH m); lia.
      * pose proof (rmoves_measure b m Hm); apply (IH m); lia.
Qed.

(** The value of a board. *)
Definition Tf (b : board) : pgame := tf (measure b) b.

Lemma tf_Tf : forall f b, measure b <= f -> tf f b = Tf b.
Proof.
  intros f b Hf; unfold Tf; apply (tf_stable (measure b)); lia.
Qed.

Lemma Tf_eq :
  forall b, Tf b = PG (map Tf (lmoves b)) (map Tf (rmoves b)).
Proof.
  intros b; unfold Tf at 1.
  destruct (measure b) as [|f] eqn:Eb.
  - pose proof (measure_zero_no_lmoves b Eb) as E1.
    pose proof (measure_zero_no_rmoves b Eb) as E2.
    rewrite E1, E2; reflexivity.
  - simpl; f_equal; apply map_ext_in; intros m Hm.
    + pose proof (lmoves_measure b m Hm); apply tf_Tf; lia.
    + pose proof (rmoves_measure b m Hm); apply tf_Tf; lia.
Qed.

Lemma lopts_Tf : forall b, lopts (Tf b) = map Tf (lmoves b).
Proof. intros b; rewrite Tf_eq; reflexivity. Qed.

Lemma ropts_Tf : forall b, ropts (Tf b) = map Tf (rmoves b).
Proof. intros b; rewrite Tf_eq; reflexivity. Qed.

(** * The moves are exactly the rules *)

(** A left move slides a toad forward or jumps it over one frog. *)
Lemma in_lmoves_iff :
  forall b b',
    In b' (lmoves b) <->
    (exists u v, b = u ++ Toad :: Empty :: v /\ b' = u ++ Empty :: Toad :: v) \/
    (exists u v,
       b = u ++ Toad :: Frog :: Empty :: v /\
       b' = u ++ Empty :: Frog :: Toad :: v).
Proof.
  induction b as [|x b IH]; intros b'; split.
  - intros H; destruct H.
  - intros [[u [v [Hb _]]] | [u [v [Hb _]]]];
      destruct u; simpl in Hb; discriminate.
  - intros H; destruct x.
    + rewrite lmoves_empty in H.
      apply in_map_iff in H; destruct H as [r [<- Hr]].
      destruct (proj1 (IH r) Hr) as [[u [v [Hb Hr']]] | [u [v [Hb Hr']]]].
      * left; exists (Empty :: u), v; subst; split; reflexivity.
      * right; exists (Empty :: u), v; subst; split; reflexivity.
    + rewrite lmoves_toad in H.
      apply in_app_or in H; destruct H as [H | H].
      * destruct b as [|y r]; [destruct H|].
        destruct y; simpl in H.
        -- destruct H as [<- | []].
           left; exists [], r; split; reflexivity.
        -- destruct H.
        -- destruct r as [|z r']; [destruct H|].
           destruct z; simpl in H.
           ++ destruct H as [<- | []].
              right; exists [], r'; split; reflexivity.
           ++ destruct H.
           ++ destruct H.
      * apply in_map_iff in H; destruct H as [r [<- Hr]].
        destruct (proj1 (IH r) Hr) as [[u [v [Hb Hr']]] | [u [v [Hb Hr']]]].
        -- left; exists (Toad :: u), v; subst; split; reflexivity.
        -- right; exists (Toad :: u), v; subst; split; reflexivity.
    + rewrite lmoves_frog in H.
      apply in_map_iff in H; destruct H as [r [<- Hr]].
      destruct (proj1 (IH r) Hr) as [[u [v [Hb Hr']]] | [u [v [Hb Hr']]]].
      * left; exists (Frog :: u), v; subst; split; reflexivity.
      * right; exists (Frog :: u), v; subst; split; reflexivity.
  - intros [[u [v [Hb Hb']]] | [u [v [Hb Hb']]]].
    + destruct u as [|y u].
      * simpl in Hb, Hb'; inversion Hb; subst.
        rewrite lmoves_toad; apply in_or_app; left.
        simpl; left; reflexivity.
      * simpl in Hb, Hb'; inversion Hb; subst.
        assert (Hin : In (u ++ Empty :: Toad :: v) (lmoves (u ++ Toad :: Empty :: v))).
        { apply IH; left; exists u, v; split; reflexivity. }
        destruct y.
        -- rewrite lmoves_empty; apply in_map_iff.
           exists (u ++ Empty :: Toad :: v); split; auto.
        -- rewrite lmoves_toad; apply in_or_app; right; apply in_map_iff.
           exists (u ++ Empty :: Toad :: v); split; auto.
        -- rewrite lmoves_frog; apply in_map_iff.
           exists (u ++ Empty :: Toad :: v); split; auto.
    + destruct u as [|y u].
      * simpl in Hb, Hb'; inversion Hb; subst.
        rewrite lmoves_toad; apply in_or_app; left.
        simpl; left; reflexivity.
      * simpl in Hb, Hb'; inversion Hb; subst.
        assert (Hin : In (u ++ Empty :: Frog :: Toad :: v)
                         (lmoves (u ++ Toad :: Frog :: Empty :: v))).
        { apply IH; right; exists u, v; split; reflexivity. }
        destruct y.
        -- rewrite lmoves_empty; apply in_map_iff.
           exists (u ++ Empty :: Frog :: Toad :: v); split; auto.
        -- rewrite lmoves_toad; apply in_or_app; right; apply in_map_iff.
           exists (u ++ Empty :: Frog :: Toad :: v); split; auto.
        -- rewrite lmoves_frog; apply in_map_iff.
           exists (u ++ Empty :: Frog :: Toad :: v); split; auto.
Qed.

(** A right move slides a frog back or jumps it over one toad. *)
Lemma in_rmoves_iff :
  forall b b',
    In b' (rmoves b) <->
    (exists u v, b = u ++ Empty :: Frog :: v /\ b' = u ++ Frog :: Empty :: v) \/
    (exists u v,
       b = u ++ Empty :: Toad :: Frog :: v /\
       b' = u ++ Frog :: Toad :: Empty :: v).
Proof.
  induction b as [|x b IH]; intros b'; split.
  - intros H; destruct H.
  - intros [[u [v [Hb _]]] | [u [v [Hb _]]]];
      destruct u; simpl in Hb; discriminate.
  - intros H; destruct x.
    + rewrite rmoves_empty in H.
      apply in_app_or in H; destruct H as [H | H].
      * destruct b as [|y r]; [destruct H|].
        destruct y; simpl in H.
        -- destruct H.
        -- destruct r as [|z r']; [destruct H|].
           destruct z; simpl in H.
           ++ destruct H.
           ++ destruct H.
           ++ destruct H as [<- | []].
              right; exists [], r'; split; reflexivity.
        -- destruct H as [<- | []].
           left; exists [], r; split; reflexivity.
      * apply in_map_iff in H; destruct H as [r [<- Hr]].
        destruct (proj1 (IH r) Hr) as [[u [v [Hb Hr']]] | [u [v [Hb Hr']]]].
        -- left; exists (Empty :: u), v; subst; split; reflexivity.
        -- right; exists (Empty :: u), v; subst; split; reflexivity.
    + rewrite rmoves_toad in H.
      apply in_map_iff in H; destruct H as [r [<- Hr]].
      destruct (proj1 (IH r) Hr) as [[u [v [Hb Hr']]] | [u [v [Hb Hr']]]].
      * left; exists (Toad :: u), v; subst; split; reflexivity.
      * right; exists (Toad :: u), v; subst; split; reflexivity.
    + rewrite rmoves_frog in H.
      apply in_map_iff in H; destruct H as [r [<- Hr]].
      destruct (proj1 (IH r) Hr) as [[u [v [Hb Hr']]] | [u [v [Hb Hr']]]].
      * left; exists (Frog :: u), v; subst; split; reflexivity.
      * right; exists (Frog :: u), v; subst; split; reflexivity.
  - intros [[u [v [Hb Hb']]] | [u [v [Hb Hb']]]].
    + destruct u as [|y u].
      * simpl in Hb, Hb'; inversion Hb; subst.
        rewrite rmoves_empty; apply in_or_app; left.
        simpl; left; reflexivity.
      * simpl in Hb, Hb'; inversion Hb; subst.
        assert (Hin : In (u ++ Frog :: Empty :: v)
                         (rmoves (u ++ Empty :: Frog :: v))).
        { apply IH; left; exists u, v; split; reflexivity. }
        destruct y.
        -- rewrite rmoves_empty; apply in_or_app; right; apply in_map_iff.
           exists (u ++ Frog :: Empty :: v); split; auto.
        -- rewrite rmoves_toad; apply in_map_iff.
           exists (u ++ Frog :: Empty :: v); split; auto.
        -- rewrite rmoves_frog; apply in_map_iff.
           exists (u ++ Frog :: Empty :: v); split; auto.
    + destruct u as [|y u].
      * simpl in Hb, Hb'; inversion Hb; subst.
        rewrite rmoves_empty; apply in_or_app; left.
        simpl; left; reflexivity.
      * simpl in Hb, Hb'; inversion Hb; subst.
        assert (Hin : In (u ++ Frog :: Toad :: Empty :: v)
                         (rmoves (u ++ Empty :: Toad :: Frog :: v))).
        { apply IH; right; exists u, v; split; reflexivity. }
        destruct y.
        -- rewrite rmoves_empty; apply in_or_app; right; apply in_map_iff.
           exists (u ++ Frog :: Toad :: Empty :: v); split; auto.
        -- rewrite rmoves_toad; apply in_map_iff.
           exists (u ++ Frog :: Toad :: Empty :: v); split; auto.
        -- rewrite rmoves_frog; apply in_map_iff.
           exists (u ++ Frog :: Toad :: Empty :: v); split; auto.
Qed.

(** * Boards on which a player is stuck *)

Fixpoint has_empty (b : board) : bool :=
  match b with
  | [] => false
  | Empty :: _ => true
  | _ :: r => has_empty r
  end.

Fixpoint has_toad (b : board) : bool :=
  match b with
  | [] => false
  | Toad :: _ => true
  | _ :: r => has_toad r
  end.

Fixpoint has_frog (b : board) : bool :=
  match b with
  | [] => false
  | Frog :: _ => true
  | _ :: r => has_frog r
  end.

Lemma ltop_no_empty :
  forall rest, has_empty rest = false -> ltop rest = [].
Proof.
  intros rest H; destruct rest as [|x r]; auto.
  destruct x; simpl in H; try discriminate; auto.
  destruct r as [|y r']; auto.
  destruct y; auto; simpl in H; discriminate.
Qed.

Lemma rtop_no_frog :
  forall rest, has_frog rest = false -> rtop rest = [].
Proof.
  intros rest H; destruct rest as [|x r]; auto.
  destruct x; simpl in H; try discriminate; auto.
  destruct r as [|y r']; auto.
  destruct y; auto; simpl in H; discriminate.
Qed.

Lemma lmoves_no_empty :
  forall b, has_empty b = false -> lmoves b = [].
Proof.
  induction b as [|x b IH]; intros H; auto.
  destruct x; simpl in H; [discriminate | |].
  - rewrite lmoves_toad, (ltop_no_empty b H), (IH H); reflexivity.
  - rewrite lmoves_frog, (IH H); reflexivity.
Qed.

Lemma rmoves_no_empty :
  forall b, has_empty b = false -> rmoves b = [].
Proof.
  induction b as [|x b IH]; intros H; auto.
  destruct x; simpl in H; [discriminate | |].
  - rewrite rmoves_toad, (IH H); reflexivity.
  - rewrite rmoves_frog, (IH H); reflexivity.
Qed.

Lemma lmoves_no_toad :
  forall b, has_toad b = false -> lmoves b = [].
Proof.
  induction b as [|x b IH]; intros H; auto.
  destruct x; simpl in H; try discriminate.
  - rewrite lmoves_empty, (IH H); reflexivity.
  - rewrite lmoves_frog, (IH H); reflexivity.
Qed.

Lemma rmoves_no_frog :
  forall b, has_frog b = false -> rmoves b = [].
Proof.
  induction b as [|x b IH]; intros H; auto.
  destruct x; simpl in H; try discriminate.
  - rewrite rmoves_empty, (rtop_no_frog b H), (IH H); reflexivity.
  - rewrite rmoves_toad, (IH H); reflexivity.
Qed.

(** A board with no empty square is zero. *)
Theorem full_board_zero :
  forall b, has_empty b = false -> Tf b = zero.
Proof.
  intros b H.
  rewrite Tf_eq, (lmoves_no_empty b H), (rmoves_no_empty b H); reflexivity.
Qed.

(** A board with no frogs is nonnegative, one with no toads nonpositive. *)
Theorem no_frogs_nonneg :
  forall b, has_frog b = false -> gle zero (Tf b) = true.
Proof.
  intros b H; apply gle_true_iff; split.
  - intros r Hr.
    rewrite ropts_Tf, (rmoves_no_frog b H) in Hr; destruct Hr.
  - intros g Hg; destruct Hg.
Qed.

Theorem no_toads_nonpos :
  forall b, has_toad b = false -> gle (Tf b) zero = true.
Proof.
  intros b H; apply gle_true_iff; split.
  - intros r Hr; destruct Hr.
  - intros g Hg.
    rewrite lopts_Tf, (lmoves_no_toad b H) in Hg; destruct Hg.
Qed.

(** * A lone toad *)

(** [tpos j i]: one toad with [j] empty squares behind it and [i] ahead. *)
Definition tpos (j i : nat) : board :=
  repeat Empty j ++ Toad :: repeat Empty i.

Lemma tpos_cons : forall j i, tpos (S j) i = Empty :: tpos j i.
Proof. reflexivity. Qed.

Lemma has_toad_empties : forall n, has_toad (repeat Empty n) = false.
Proof. induction n as [|k IH]; auto. Qed.

Lemma has_frog_empties : forall n, has_frog (repeat Empty n) = false.
Proof. induction n as [|k IH]; auto. Qed.

Lemma has_frog_tpos : forall j i, has_frog (tpos j i) = false.
Proof.
  intros j i; unfold tpos.
  induction j as [|m IH]; simpl.
  - apply has_frog_empties.
  - exact IH.
Qed.

Lemma lmoves_tpos_zero : forall j, lmoves (tpos j 0) = [].
Proof.
  induction j as [|m IH].
  - unfold tpos; simpl; reflexivity.
  - rewrite tpos_cons, lmoves_empty, IH; reflexivity.
Qed.

Lemma lmoves_tpos_succ :
  forall j k, lmoves (tpos j (S k)) = [tpos (S j) k].
Proof.
  intros j k; induction j as [|m IH].
  - unfold tpos at 1.
    change (repeat Empty 0 ++ Toad :: repeat Empty (S k))
      with (Toad :: repeat Empty (S k)).
    rewrite lmoves_toad.
    rewrite (lmoves_no_toad (repeat Empty (S k)) (has_toad_empties (S k))).
    change (map (fun r : board => Toad :: r) (@nil board)) with (@nil board).
    rewrite app_nil_r.
    change (repeat Empty (S k)) with (Empty :: repeat Empty k).
    change (ltop (Empty :: repeat Empty k))
      with [Empty :: Toad :: repeat Empty k].
    reflexivity.
  - rewrite tpos_cons, lmoves_empty, IH; reflexivity.
Qed.

Lemma rmoves_tpos : forall j i, rmoves (tpos j i) = [].
Proof.
  intros j i; apply rmoves_no_frog, has_frog_tpos.
Qed.

(** A lone toad with [i] empty squares ahead of it is the integer [i]. *)
Theorem tf_tpos : forall i j, gequiv (Tf (tpos j i)) (num i) = true.
Proof.
  induction i as [|k IH]; intros j.
  - rewrite Tf_eq, lmoves_tpos_zero, rmoves_tpos.
    apply gequiv_refl.
  - rewrite Tf_eq, lmoves_tpos_succ, rmoves_tpos.
    change (num (S k)) with (PG [num k] (@nil pgame)).
    apply gequiv_of_opts.
    + change (lopts (PG (map Tf [tpos (S j) k]) (@nil pgame)))
        with [Tf (tpos (S j) k)].
      change (lopts (PG [num k] (@nil pgame))) with [num k].
      split; intros x [<- | []].
      * exists (num k); split; [left; auto | apply IH].
      * exists (Tf (tpos (S j) k)); split; [left; auto | apply IH].
    + split; intros x [].
Qed.

(** * Mirror symmetry *)

Lemma mirror_lslide :
  forall u v,
    mirror (u ++ Toad :: Empty :: v) = mirror v ++ Empty :: Frog :: mirror u.
Proof.
  intros u v; rewrite mirror_app, !mirror_cons, <- !app_assoc; reflexivity.
Qed.

Lemma mirror_lslide_after :
  forall u v,
    mirror (u ++ Empty :: Toad :: v) = mirror v ++ Frog :: Empty :: mirror u.
Proof.
  intros u v; rewrite mirror_app, !mirror_cons, <- !app_assoc; reflexivity.
Qed.

Lemma mirror_ljump :
  forall u v,
    mirror (u ++ Toad :: Frog :: Empty :: v)
    = mirror v ++ Empty :: Toad :: Frog :: mirror u.
Proof.
  intros u v; rewrite mirror_app, !mirror_cons, <- !app_assoc; reflexivity.
Qed.

Lemma mirror_ljump_after :
  forall u v,
    mirror (u ++ Empty :: Frog :: Toad :: v)
    = mirror v ++ Frog :: Toad :: Empty :: mirror u.
Proof.
  intros u v; rewrite mirror_app, !mirror_cons, <- !app_assoc; reflexivity.
Qed.

Lemma mirror_rslide :
  forall u v,
    mirror (u ++ Empty :: Frog :: v) = mirror v ++ Toad :: Empty :: mirror u.
Proof.
  intros u v; rewrite mirror_app, !mirror_cons, <- !app_assoc; reflexivity.
Qed.

Lemma mirror_rslide_after :
  forall u v,
    mirror (u ++ Frog :: Empty :: v) = mirror v ++ Empty :: Toad :: mirror u.
Proof.
  intros u v; rewrite mirror_app, !mirror_cons, <- !app_assoc; reflexivity.
Qed.

Lemma mirror_rjump :
  forall u v,
    mirror (u ++ Empty :: Toad :: Frog :: v)
    = mirror v ++ Toad :: Frog :: Empty :: mirror u.
Proof.
  intros u v; rewrite mirror_app, !mirror_cons, <- !app_assoc; reflexivity.
Qed.

Lemma mirror_rjump_after :
  forall u v,
    mirror (u ++ Frog :: Toad :: Empty :: v)
    = mirror v ++ Empty :: Frog :: Toad :: mirror u.
Proof.
  intros u v; rewrite mirror_app, !mirror_cons, <- !app_assoc; reflexivity.
Qed.

(** Mirroring turns each player's moves into the other's. *)
Lemma lmoves_mirror :
  forall b b', In b' (lmoves b) -> In (mirror b') (rmoves (mirror b)).
Proof.
  intros b b' H; apply in_lmoves_iff in H; apply in_rmoves_iff.
  destruct H as [[u [v [-> ->]]] | [u [v [-> ->]]]].
  - left; exists (mirror v), (mirror u); split.
    + apply mirror_lslide.
    + apply mirror_lslide_after.
  - right; exists (mirror v), (mirror u); split.
    + apply mirror_ljump.
    + apply mirror_ljump_after.
Qed.

Lemma rmoves_mirror :
  forall b b', In b' (rmoves b) -> In (mirror b') (lmoves (mirror b)).
Proof.
  intros b b' H; apply in_rmoves_iff in H; apply in_lmoves_iff.
  destruct H as [[u [v [-> ->]]] | [u [v [-> ->]]]].
  - left; exists (mirror v), (mirror u); split.
    + apply mirror_rslide.
    + apply mirror_rslide_after.
  - right; exists (mirror v), (mirror u); split.
    + apply mirror_rjump.
    + apply mirror_rjump_after.
Qed.

(** Reflecting the strip and exchanging the animals negates the value. *)
Theorem tf_mirror :
  forall b, gequiv (Tf (mirror b)) (pneg (Tf b)) = true.
Proof.
  assert (Haux : forall N b,
            measure b <= N -> gequiv (Tf (mirror b)) (pneg (Tf b)) = true).
  { induction N as [|N IH]; intros b HN.
    - assert (Hz : measure b = 0) by lia.
      assert (Hzm : measure (mirror b) = 0) by (rewrite measure_mirror; lia).
      rewrite Tf_eq, (Tf_eq b).
      rewrite (measure_zero_no_lmoves _ Hz), (measure_zero_no_rmoves _ Hz).
      rewrite (measure_zero_no_lmoves _ Hzm), (measure_zero_no_rmoves _ Hzm).
      apply gequiv_refl.
    - apply gequiv_of_opts.
      + rewrite lopts_Tf.
        rewrite lopts_pneg, ropts_Tf, map_map.
        split.
        * intros x Hx; apply in_map_iff in Hx; destruct Hx as [m [<- Hm]].
          exists (pneg (Tf (mirror m))); split.
          -- apply in_map_iff; exists (mirror m); split; auto.
             pose proof (lmoves_mirror (mirror b) m Hm) as Hin.
             rewrite mirror_mirror in Hin; exact Hin.
          -- pose proof (lmoves_measure (mirror b) m Hm) as Hlt.
             rewrite measure_mirror in Hlt.
             assert (Hm' : measure (mirror m) <= N)
               by (rewrite measure_mirror; lia).
             pose proof (IH (mirror m) Hm') as He.
             rewrite mirror_mirror in He; exact He.
        * intros y Hy; apply in_map_iff in Hy; destruct Hy as [r [<- Hr]].
          exists (Tf (mirror r)); split.
          -- apply in_map_iff; exists (mirror r); split; auto.
             apply rmoves_mirror; auto.
          -- pose proof (rmoves_measure b r Hr) as Hlt.
             apply IH; lia.
      + rewrite ropts_Tf.
        rewrite ropts_pneg, lopts_Tf, map_map.
        split.
        * intros x Hx; apply in_map_iff in Hx; destruct Hx as [m [<- Hm]].
          exists (pneg (Tf (mirror m))); split.
          -- apply in_map_iff; exists (mirror m); split; auto.
             pose proof (rmoves_mirror (mirror b) m Hm) as Hin.
             rewrite mirror_mirror in Hin; exact Hin.
          -- pose proof (rmoves_measure (mirror b) m Hm) as Hlt.
             rewrite measure_mirror in Hlt.
             assert (Hm' : measure (mirror m) <= N)
               by (rewrite measure_mirror; lia).
             pose proof (IH (mirror m) Hm') as He.
             rewrite mirror_mirror in He; exact He.
        * intros y Hy; apply in_map_iff in Hy; destruct Hy as [r [<- Hr]].
          exists (Tf (mirror r)); split.
          -- apply in_map_iff; exists (mirror r); split; auto.
             apply lmoves_mirror; auto.
          -- pose proof (lmoves_measure b r Hr) as Hlt.
             apply IH; lia. }
  intros b; apply (Haux (measure b)); lia.
Qed.

(** * A lone frog *)

(** [fpos i j]: one frog with [i] empty squares ahead of it and [j] behind. *)
Definition fpos (i j : nat) : board :=
  repeat Empty i ++ Frog :: repeat Empty j.

Lemma map_flip_empties : forall n, map flip (repeat Empty n) = repeat Empty n.
Proof. induction n as [|k IH]; auto; simpl; f_equal; exact IH. Qed.

Lemma repeat_snoc :
  forall (x : square) n, repeat x n ++ [x] = repeat x (S n).
Proof. intros x n; induction n as [|k IH]; auto; simpl; f_equal; exact IH. Qed.

Lemma mirror_empties : forall n, mirror (repeat Empty n) = repeat Empty n.
Proof.
  intros n; unfold mirror; rewrite map_flip_empties.
  induction n as [|k IH]; auto.
  change (repeat Empty (S k)) with (Empty :: repeat Empty k).
  simpl rev.
  rewrite IH, repeat_snoc; reflexivity.
Qed.

(** The mirror of a lone toad is a lone frog. *)
Lemma mirror_tpos : forall j i, mirror (tpos j i) = fpos i j.
Proof.
  intros j i; unfold tpos, fpos.
  rewrite mirror_app, mirror_cons, !mirror_empties.
  change (flip Toad) with Frog.
  rewrite <- app_assoc; reflexivity.
Qed.

(** A lone frog with [i] empty squares ahead of it is the integer [-i]. *)
Theorem tf_fpos :
  forall i j, gequiv (Tf (fpos i j)) (pneg (num i)) = true.
Proof.
  intros i j.
  rewrite <- (mirror_tpos j i).
  apply (gequiv_trans _ (pneg (Tf (tpos j i)))).
  - apply tf_mirror.
  - apply gequiv_pneg, tf_tpos.
Qed.

(** * Frog-free boards *)

(** The empty squares of a board. *)
Fixpoint blanks (b : board) : nat :=
  match b with
  | [] => 0
  | Empty :: r => S (blanks r)
  | _ :: r => blanks r
  end.

(** The toad-blank pairs: each toad must pass every blank ahead of it. *)
Fixpoint slides (b : board) : nat :=
  match b with
  | [] => 0
  | Toad :: r => blanks r + slides r
  | _ :: r => slides r
  end.

Lemma frogs_zero_of_no_frog : forall b, has_frog b = false -> frogs b = 0.
Proof.
  induction b as [|x b IH]; intros H; [reflexivity|].
  destruct x.
  - change (frogs b = 0); apply IH; exact H.
  - change (frogs b = 0); apply IH; exact H.
  - discriminate H.
Qed.

Lemma fmeasure_zero_of_no_frog :
  forall b, has_frog b = false -> fmeasure b = 0.
Proof.
  induction b as [|x b IH]; intros H; [reflexivity|].
  assert (Hb : has_frog b = false)
    by (destruct x; [exact H | exact H | discriminate H]).
  change (frogs b + fmeasure b = 0).
  rewrite (frogs_zero_of_no_frog b Hb), (IH Hb); reflexivity.
Qed.

Lemma ltop_blanks :
  forall rest b', In b' (ltop rest) -> blanks b' = blanks (Toad :: rest).
Proof.
  intros rest b' H.
  destruct rest as [|y r]; [destruct H|].
  destruct y.
  - change (ltop (Empty :: r)) with [Empty :: Toad :: r] in H.
    destruct H as [<- | []]; reflexivity.
  - change (ltop (Toad :: r)) with (@nil board) in H; destruct H.
  - destruct r as [|z r0]; [destruct H|].
    destruct z.
    + change (ltop (Frog :: Empty :: r0))
        with [Empty :: Frog :: Toad :: r0] in H.
      destruct H as [<- | []]; reflexivity.
    + change (ltop (Frog :: Toad :: r0)) with (@nil board) in H; destruct H.
    + change (ltop (Frog :: Frog :: r0)) with (@nil board) in H; destruct H.
Qed.

Lemma lmoves_blanks :
  forall b b', In b' (lmoves b) -> blanks b' = blanks b.
Proof.
  induction b as [|x b IH]; intros b' H; [destruct H|].
  destruct x.
  - rewrite lmoves_empty in H.
    apply in_map_iff in H; destruct H as [r [<- Hr]].
    change (S (blanks r) = S (blanks b)); rewrite (IH r Hr); reflexivity.
  - rewrite lmoves_toad in H.
    apply in_app_or in H; destruct H as [H | H].
    + apply ltop_blanks; exact H.
    + apply in_map_iff in H; destruct H as [r [<- Hr]].
      change (blanks r = blanks b); apply IH; exact Hr.
  - rewrite lmoves_frog in H.
    apply in_map_iff in H; destruct H as [r [<- Hr]].
    change (blanks r = blanks b); apply IH; exact Hr.
Qed.

(** With no frogs on the board every left move is a slide past one blank. *)
Lemma lmoves_no_frog_slides :
  forall b b',
    has_frog b = false -> In b' (lmoves b) ->
    has_frog b' = false /\ S (slides b') = slides b.
Proof.
  induction b as [|x b IH]; intros b' Hf H; [destruct H|].
  destruct x.
  - rewrite lmoves_empty in H.
    apply in_map_iff in H; destruct H as [r [<- Hr]].
    destruct (IH r Hf Hr) as [Hfr Hsr]; split; [exact Hfr | exact Hsr].
  - rewrite lmoves_toad in H.
    apply in_app_or in H; destruct H as [H | H].
    + destruct b as [|y b0]; [destruct H|].
      destruct y.
      * change (ltop (Empty :: b0)) with [Empty :: Toad :: b0] in H.
        destruct H as [<- | []].
        split; [exact Hf|].
        change (S (blanks b0 + slides b0) =
                S (blanks b0) + slides b0); lia.
      * change (ltop (Toad :: b0)) with (@nil board) in H; destruct H.
      * discriminate Hf.
    + apply in_map_iff in H; destruct H as [r [<- Hr]].
      destruct (IH r Hf Hr) as [Hfr Hsr].
      split; [exact Hfr|].
      change (S (blanks r + slides r) = blanks b + slides b).
      rewrite (lmoves_blanks b r Hr); lia.
  - discriminate Hf.
Qed.

Lemma lmoves_no_frog_nil :
  forall b, has_frog b = false -> lmoves b = [] -> slides b = 0.
Proof.
  induction b as [|x b IH]; intros Hf Hnil; [reflexivity|].
  destruct x.
  - rewrite lmoves_empty in Hnil; apply map_eq_nil in Hnil.
    change (slides b = 0); apply IH; [exact Hf | exact Hnil].
  - rewrite lmoves_toad in Hnil.
    apply app_eq_nil in Hnil; destruct Hnil as [Htop Hin].
    apply map_eq_nil in Hin.
    assert (Hsb : slides b = 0) by (apply IH; [exact Hf | exact Hin]).
    change (blanks b + slides b = 0); rewrite Hsb, Nat.add_0_r.
    destruct b as [|y b0]; [reflexivity|].
    destruct y.
    + change (ltop (Empty :: b0)) with [Empty :: Toad :: b0] in Htop.
      discriminate Htop.
    + change (blanks b0 = 0).
      change (slides (Toad :: b0)) with (blanks b0 + slides b0) in Hsb; lia.
    + discriminate Hf.
  - discriminate Hf.
Qed.

(** A board with no frogs is the integer counting its toad-blank pairs. *)
Theorem tf_no_frog :
  forall b, has_frog b = false -> gequiv (Tf b) (num (slides b)) = true.
Proof.
  assert (Haux : forall N b,
            slides b <= N -> has_frog b = false ->
            gequiv (Tf b) (num (slides b)) = true).
  { induction N as [|N IH]; intros b HN Hf.
    - assert (Hs : slides b = 0) by lia.
      assert (Hl : lmoves b = []).
      { destruct (lmoves b) as [|m l] eqn:E; auto.
        assert (Hm : In m (lmoves b)) by (rewrite E; left; auto).
        destruct (lmoves_no_frog_slides b m Hf Hm) as [_ Hsm]; lia. }
      rewrite Tf_eq, Hl, (rmoves_no_frog b Hf), Hs; apply gequiv_refl.
    - destruct (slides b) as [|m] eqn:Es.
      + assert (Hl : lmoves b = []).
        { destruct (lmoves b) as [|m l] eqn:E; auto.
          assert (Hm : In m (lmoves b)) by (rewrite E; left; auto).
          destruct (lmoves_no_frog_slides b m Hf Hm) as [_ Hsm]; lia. }
        rewrite Tf_eq, Hl, (rmoves_no_frog b Hf); apply gequiv_refl.
      + assert (Hne : lmoves b <> []).
        { intros Hnil.
          pose proof (lmoves_no_frog_nil b Hf Hnil); lia. }
        rewrite Tf_eq, (rmoves_no_frog b Hf).
        change (num (S m)) with (PG [num m] (@nil pgame)).
        apply gequiv_of_opts.
        * split.
          -- intros x Hx.
             change (lopts (PG (map Tf (lmoves b)) (@nil pgame)))
               with (map Tf (lmoves b)) in Hx.
             apply in_map_iff in Hx; destruct Hx as [b' [<- Hb']].
             exists (num m); split; [left; auto|].
             destruct (lmoves_no_frog_slides b b' Hf Hb') as [Hfb' Hsb'].
             assert (Hsm : slides b' = m) by lia.
             rewrite <- Hsm; apply IH; [lia | exact Hfb'].
          -- intros y Hy.
             change (lopts (PG [num m] (@nil pgame))) with [num m] in Hy.
             destruct Hy as [<- | []].
             assert (Hex : exists b0, In b0 (lmoves b)).
             { destruct (lmoves b) as [|b0 l]; [exfalso; apply Hne; auto|].
               exists b0; left; auto. }
             destruct Hex as [b0 Hb0].
             exists (Tf b0); split.
             ++ change (lopts (PG (map Tf (lmoves b)) (@nil pgame)))
                  with (map Tf (lmoves b)).
                apply in_map; exact Hb0.
             ++ destruct (lmoves_no_frog_slides b b0 Hf Hb0) as [Hfb0 Hsb0].
                assert (Hsm : slides b0 = m) by lia.
                rewrite <- Hsm; apply IH; [lia | exact Hfb0].
        * split; intros x Hx; destruct Hx. }
  intros b Hf; apply (Haux (slides b) b); [lia | exact Hf].
Qed.

Lemma has_frog_app :
  forall l m, has_frog (l ++ m) = (has_frog l || has_frog m)%bool.
Proof.
  induction l as [|x l IH]; intros m; [reflexivity|].
  destruct x; [apply IH | apply IH | reflexivity].
Qed.

Lemma has_frog_rev : forall l, has_frog (rev l) = has_frog l.
Proof.
  induction l as [|x l IH]; [reflexivity|].
  change (has_frog (rev l ++ [x]) = has_frog (x :: l)).
  rewrite has_frog_app, IH.
  destruct x.
  - change (has_frog [Empty]) with false; apply orb_false_r.
  - change (has_frog [Toad]) with false; apply orb_false_r.
  - change (has_frog [Frog]) with true; apply orb_true_r.
Qed.

Lemma has_frog_map_flip : forall l, has_frog (map flip l) = has_toad l.
Proof.
  induction l as [|x l IH]; [reflexivity|].
  destruct x; [exact IH | reflexivity | exact IH].
Qed.

Lemma has_frog_mirror : forall b, has_frog (mirror b) = has_toad b.
Proof.
  intros b; unfold mirror.
  rewrite has_frog_rev; apply has_frog_map_flip.
Qed.

(** A board with no toads is the negative of its mirror's value. *)
Theorem tf_no_toad :
  forall b,
    has_toad b = false ->
    gequiv (Tf b) (pneg (num (slides (mirror b)))) = true.
Proof.
  intros b Ht.
  assert (Hf : has_frog (mirror b) = false)
    by (rewrite has_frog_mirror; exact Ht).
  pose proof (tf_mirror (mirror b)) as Hm.
  rewrite (mirror_mirror b) in Hm.
  apply (gequiv_trans _ (pneg (Tf (mirror b)))); [exact Hm|].
  apply gequiv_pneg, tf_no_frog; exact Hf.
Qed.

(** A block of toads ahead of a block of blanks is their product. *)
Lemma blanks_empties : forall k, blanks (repeat Empty k) = k.
Proof. induction k as [|k IH]; simpl; auto. Qed.

Lemma slides_empties : forall k, slides (repeat Empty k) = 0.
Proof. induction k as [|k IH]; simpl; auto. Qed.

Lemma has_frog_block :
  forall a k, has_frog (repeat Toad a ++ repeat Empty k) = false.
Proof.
  induction a as [|a IH]; intros k; simpl.
  - apply has_frog_empties.
  - apply IH.
Qed.

Lemma blanks_block :
  forall a k, blanks (repeat Toad a ++ repeat Empty k) = k.
Proof.
  induction a as [|a IH]; intros k; simpl.
  - apply blanks_empties.
  - apply IH.
Qed.

Lemma slides_block :
  forall a k, slides (repeat Toad a ++ repeat Empty k) = a * k.
Proof.
  induction a as [|a IH]; intros k.
  - change (slides (repeat Empty k) = 0); apply slides_empties.
  - change (blanks (repeat Toad a ++ repeat Empty k) +
            slides (repeat Toad a ++ repeat Empty k) = k + a * k).
    rewrite blanks_block, IH; reflexivity.
Qed.

Theorem tf_block :
  forall a k,
    gequiv (Tf (repeat Toad a ++ repeat Empty k)) (num (a * k)) = true.
Proof.
  intros a k.
  rewrite <- (slides_block a k).
  apply tf_no_frog, has_frog_block.
Qed.

(** * Positions of several strips *)

Definition position : Type := list board.

Fixpoint pmoves (f : board -> list board) (p : position) : list position :=
  match p with
  | [] => []
  | b :: rest =>
    map (fun b' => b' :: rest) (f b) ++ map (fun r => b :: r) (pmoves f rest)
  end.

Fixpoint psize (p : position) : nat :=
  match p with [] => 0 | b :: rest => measure b + psize rest end.

Fixpoint tfp (fuel : nat) (p : position) : pgame :=
  match fuel with
  | 0 => PG [] []
  | S f => PG (map (tfp f) (pmoves lmoves p)) (map (tfp f) (pmoves rmoves p))
  end.

Lemma pmoves_smaller :
  forall f p q,
    (forall b b', In b' (f b) -> measure b' < measure b) ->
    In q (pmoves f p) -> psize q < psize p.
Proof.
  intros f p; induction p as [|b rest IH]; intros q Hf Hq; [destruct Hq|].
  change (pmoves f (b :: rest))
    with (map (fun b' => b' :: rest) (f b)
          ++ map (fun r => b :: r) (pmoves f rest)) in Hq.
  apply in_app_or in Hq; destruct Hq as [Hq | Hq];
    apply in_map_iff in Hq; destruct Hq as [a [<- Ha]].
  - change (psize (a :: rest)) with (measure a + psize rest).
    change (psize (b :: rest)) with (measure b + psize rest).
    pose proof (Hf b a Ha); lia.
  - change (psize (b :: a)) with (measure b + psize a).
    change (psize (b :: rest)) with (measure b + psize rest).
    specialize (IH a Hf Ha); lia.
Qed.

Lemma pmoves_nil_of_zero :
  forall f p,
    (forall b b', In b' (f b) -> measure b' < measure b) ->
    psize p = 0 -> pmoves f p = [].
Proof.
  intros f p Hf Hz.
  destruct (pmoves f p) as [|x l] eqn:E; auto.
  exfalso.
  pose proof (pmoves_smaller f p x Hf) as Hlt.
  rewrite E in Hlt; specialize (Hlt (or_introl eq_refl)); lia.
Qed.

Lemma tfp_stable :
  forall N p f1 f2,
    psize p <= N -> psize p <= f1 -> psize p <= f2 -> tfp f1 p = tfp f2 p.
Proof.
  induction N as [|N IH]; intros p f1 f2 HN Hf1 Hf2.
  - assert (Hz : psize p = 0) by lia.
    pose proof (pmoves_nil_of_zero lmoves p lmoves_measure Hz) as E1.
    pose proof (pmoves_nil_of_zero rmoves p rmoves_measure Hz) as E2.
    destruct f1; destruct f2; simpl; rewrite ?E1, ?E2; reflexivity.
  - destruct f1 as [|f1]; destruct f2 as [|f2].
    + reflexivity.
    + assert (Hz : psize p = 0) by lia.
      pose proof (pmoves_nil_of_zero lmoves p lmoves_measure Hz) as E1.
      pose proof (pmoves_nil_of_zero rmoves p rmoves_measure Hz) as E2.
      simpl; rewrite E1, E2; reflexivity.
    + assert (Hz : psize p = 0) by lia.
      pose proof (pmoves_nil_of_zero lmoves p lmoves_measure Hz) as E1.
      pose proof (pmoves_nil_of_zero rmoves p rmoves_measure Hz) as E2.
      simpl; rewrite E1, E2; reflexivity.
    + simpl; f_equal; apply map_ext_in; intros q Hq.
      * pose proof (pmoves_smaller lmoves p q lmoves_measure Hq).
        apply (IH q); lia.
      * pose proof (pmoves_smaller rmoves p q rmoves_measure Hq).
        apply (IH q); lia.
Qed.

Definition Tfp (p : position) : pgame := tfp (psize p) p.

Lemma tfp_Tfp : forall f p, psize p <= f -> tfp f p = Tfp p.
Proof.
  intros f p Hf; unfold Tfp; apply (tfp_stable (psize p)); lia.
Qed.

Lemma Tfp_eq :
  forall p,
    Tfp p = PG (map Tfp (pmoves lmoves p)) (map Tfp (pmoves rmoves p)).
Proof.
  intros p; unfold Tfp at 1.
  destruct (psize p) as [|f] eqn:Ep.
  - pose proof (pmoves_nil_of_zero lmoves p lmoves_measure Ep) as E1.
    pose proof (pmoves_nil_of_zero rmoves p rmoves_measure Ep) as E2.
    rewrite E1, E2; reflexivity.
  - simpl; f_equal; apply map_ext_in; intros q Hq.
    + pose proof (pmoves_smaller lmoves p q lmoves_measure Hq).
      apply tfp_Tfp; lia.
    + pose proof (pmoves_smaller rmoves p q rmoves_measure Hq).
      apply tfp_Tfp; lia.
Qed.

Lemma lopts_Tfp : forall p, lopts (Tfp p) = map Tfp (pmoves lmoves p).
Proof. intros p; rewrite Tfp_eq; reflexivity. Qed.

Lemma ropts_Tfp : forall p, ropts (Tfp p) = map Tfp (pmoves rmoves p).
Proof. intros p; rewrite Tfp_eq; reflexivity. Qed.

(** A position is the sum of its strips. *)
Lemma Tfp_cons :
  forall b rest, gequiv (Tfp (b :: rest)) (padd (Tf b) (Tfp rest)) = true.
Proof.
  assert (Haux : forall N b rest,
            measure b + psize rest <= N ->
            gequiv (Tfp (b :: rest)) (padd (Tf b) (Tfp rest)) = true).
  { induction N as [|N IH]; intros b rest HN.
    - assert (Hb : measure b = 0) by lia.
      assert (Hp : psize rest = 0) by lia.
      assert (Hz : psize (b :: rest) = 0)
        by (change (psize (b :: rest)) with (measure b + psize rest); lia).
      pose proof (pmoves_nil_of_zero lmoves _ lmoves_measure Hz) as E1.
      pose proof (pmoves_nil_of_zero rmoves _ rmoves_measure Hz) as E2.
      pose proof (pmoves_nil_of_zero lmoves rest lmoves_measure Hp) as E3.
      pose proof (pmoves_nil_of_zero rmoves rest rmoves_measure Hp) as E4.
      rewrite Tf_eq, (measure_zero_no_lmoves b Hb),
              (measure_zero_no_rmoves b Hb).
      change (PG (map Tf (@nil board)) (map Tf (@nil board))) with zero.
      rewrite padd_zero_l.
      rewrite (Tfp_eq (b :: rest)), (Tfp_eq rest), E1, E2, E3, E4.
      apply gequiv_refl.
    - apply gequiv_of_opts.
      + rewrite lopts_Tfp, lopts_padd, lopts_Tf, lopts_Tfp.
        change (pmoves lmoves (b :: rest))
          with (map (fun b' => b' :: rest) (lmoves b)
                ++ map (fun r => b :: r) (pmoves lmoves rest)).
        rewrite map_app, !map_map.
        cbv beta.
        apply opts_equiv_app_map; intros x Hx.
        * apply IH; pose proof (lmoves_measure b x Hx); lia.
        * apply IH.
          pose proof (pmoves_smaller lmoves rest x lmoves_measure Hx); lia.
      + rewrite ropts_Tfp, ropts_padd, ropts_Tf, ropts_Tfp.
        change (pmoves rmoves (b :: rest))
          with (map (fun b' => b' :: rest) (rmoves b)
                ++ map (fun r => b :: r) (pmoves rmoves rest)).
        rewrite map_app, !map_map.
        cbv beta.
        apply opts_equiv_app_map; intros x Hx.
        * apply IH; pose proof (rmoves_measure b x Hx); lia.
        * apply IH.
          pose proof (pmoves_smaller rmoves rest x rmoves_measure Hx); lia. }
  intros b rest; apply (Haux (measure b + psize rest)); lia.
Qed.

Definition Tsum (p : position) : pgame :=
  fold_right (fun b acc => padd (Tf b) acc) zero p.

Theorem Tfp_sum : forall p, gequiv (Tfp p) (Tsum p) = true.
Proof.
  induction p as [|b rest IH].
  - apply gequiv_refl.
  - apply (gequiv_trans _ (padd (Tf b) (Tfp rest))).
    + apply Tfp_cons.
    + change (Tsum (b :: rest)) with (padd (Tf b) (Tsum rest)).
      apply gequiv_padd_l; auto.
Qed.

(** * Solved boards *)

Example tf_empty : Tf [] = zero.
Proof. reflexivity. Qed.

(** A toad facing a frog with no room is a stalemate. *)
Example tf_blocked : Tf [Toad; Frog] = zero.
Proof. apply full_board_zero; reflexivity. Qed.

Example tf_toad_one : gequiv (Tf [Toad; Empty]) one = true.
Proof. vm_compute; reflexivity. Qed.

Example tf_toad_two : gequiv (Tf [Toad; Empty; Empty]) (num 2) = true.
Proof. vm_compute; reflexivity. Qed.

Example tf_frog_one : gequiv (Tf [Empty; Frog]) minus_one = true.
Proof. vm_compute; reflexivity. Qed.

(** Two toads sharing one empty square are worth two moves. *)
Example tf_two_toads : gequiv (Tf [Toad; Toad; Empty]) (num 2) = true.
Proof. vm_compute; reflexivity. Qed.

(** A toad and a frog with one square between them is star. *)
Example tf_star : gequiv (Tf [Toad; Empty; Frog]) star = true.
Proof. vm_compute; reflexivity. Qed.

(** A toad touching a frog can only jump, and the position balances. *)
Example tf_jump : gequiv (Tf [Toad; Frog; Empty]) zero = true.
Proof. vm_compute; reflexivity. Qed.

Example tf_balanced : outc (Tf [Toad; Empty; Empty; Frog]) = Secondwins.
Proof. vm_compute; reflexivity. Qed.

(** Two strips add: two free moves for Left, or a toad against a frog. *)
Example tfp_two_strips :
  gequiv (Tfp [[Toad; Empty]; [Toad; Empty]]) (num 2) = true.
Proof. vm_compute; reflexivity. Qed.

Example tfp_cancel :
  gequiv (Tfp [[Toad; Empty]; [Empty; Frog]]) zero = true.
Proof. vm_compute; reflexivity. Qed.

(** Two copies of star cancel. *)
Example tfp_star_pair :
  gequiv (Tfp [[Toad; Empty; Frog]; [Toad; Empty; Frog]]) zero = true.
Proof. vm_compute; reflexivity. Qed.
