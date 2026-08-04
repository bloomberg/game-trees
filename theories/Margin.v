(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Forcing a score margin on the Dots and Boxes board.

    [DotsAndBoxesBoard.db_outc] reports only who won, so the forcing
    predicates it feeds can say that a player wins but not by how much. A
    scoring game has a margin, and the natural question is which margins a
    player can force.

    [db_outc_ge k] is the outcome map that calls a finished game a win for
    the first player exactly when the margin reaches [k]. Reading
    [GameTrees.Determinacy] against it gives [forces_margin], and the
    Zermelo theorem then says every margin is decided: either the first
    player forces it or the second player forces that it is missed.
    [forces_margin_mono] is monotone in [k], [forces_margin_win] identifies
    margin one with winning, and [margin_best] extracts the largest margin
    the first player can force on a board of known size. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.Determinacy.
Require Import GameTrees.DotsAndBoxesBoard.

Open Scope Z_scope.

Section Margin.

Variables m n : nat.

(** * The margin *)

(** The first player's lead. *)
Definition margin (s : st) : Z := Z.of_nat (s1 s) - Z.of_nat (s2 s).

Lemma margin_init : margin init = 0.
Proof. reflexivity. Qed.

(** * Outcomes indexed by a target margin *)

(** A finished game is a win for the first player exactly when the margin
    reaches [k]. Unfinished games are undecided, exactly as for [db_outc]. *)
Definition db_outc_ge (k : Z) (s : st) : option outcome :=
  match db_moves m n s with
  | [] => Some (if k <=? margin s then win true else win false)
  | _ :: _ => None
  end.

Lemma db_outc_ge_none_iff :
  forall k s, db_outc_ge k s = None <-> db_moves m n s <> [].
Proof.
  intros k s; unfold db_outc_ge; destruct (db_moves m n s); split;
    try discriminate; try reflexivity.
  intros H; contradiction.
Qed.

Lemma db_outc_ge_not_drawn : forall k s, db_outc_ge k s <> Some drawn.
Proof.
  intros k s H; unfold db_outc_ge in H.
  destruct (db_moves m n s); [|discriminate].
  destruct (k <=? margin s); discriminate.
Qed.

Lemma db_outc_ge_none_moves :
  forall k s, db_outc_ge k s = None -> exists e, In e (db_moves m n s).
Proof.
  intros k s H; apply db_outc_ge_none_iff in H.
  destruct (db_moves m n s) as [|e r] eqn:E; [contradiction|].
  exists e; left; reflexivity.
Qed.

(** * Forcing a margin *)

(** [forces_margin k fuel s]: the first player drives the finished margin to
    [k] or better within [fuel] plies. *)
Definition forces_margin (k : Z) (fuel : nat) (s : st) : Prop :=
  forces (db_moves m n) (db_play m n) db_amove (db_outc_ge k) true fuel s.

(** [denies_margin k fuel s]: the second player keeps the margin below [k]. *)
Definition denies_margin (k : Z) (fuel : nat) (s : st) : Prop :=
  forces (db_moves m n) (db_play m n) db_amove (db_outc_ge k) false fuel s.

(** * Transfer between outcome maps *)

(** Two outcome maps that agree on which states are finished, and whose
    verdicts a player reads the same way, force the same things. Both the
    monotonicity in [k] and the identification of margin one with winning are
    instances. *)
Lemma forces_in_transfer :
  forall (o1 o2 : st -> option outcome) (g1 g2 : outcome -> bool) who fuel s,
    (forall t, o1 t = None <-> o2 t = None) ->
    (forall t x y, o1 t = Some x -> o2 t = Some y -> g1 x = true -> g2 y = true) ->
    forces_in (db_moves m n) (db_play m n) db_amove o1 g1 who fuel s ->
    forces_in (db_moves m n) (db_play m n) db_amove o2 g2 who fuel s.
Proof.
  intros o1 o2 g1 g2 who fuel; induction fuel as [|f IH]; intros s Hnone Hval H.
  - apply (proj1 (forces_in_0_iff _ _ _ o1 g1 who s)) in H.
    apply (proj2 (forces_in_0_iff _ _ _ o2 g2 who s)).
    destruct (o1 s) as [x|] eqn:E1; [|destruct H].
    destruct (o2 s) as [y|] eqn:E2.
    + exact (Hval s x y E1 E2 H).
    + exfalso.
      assert (Hc : o1 s = None) by (apply Hnone; exact E2).
      rewrite E1 in Hc; discriminate.
  - apply (proj1 (forces_in_S_iff _ _ _ o1 g1 who f s)) in H.
    apply (proj2 (forces_in_S_iff _ _ _ o2 g2 who f s)).
    destruct (o1 s) as [x|] eqn:E1.
    + destruct (o2 s) as [y|] eqn:E2.
      * exact (Hval s x y E1 E2 H).
      * exfalso.
        assert (Hc : o1 s = None) by (apply Hnone; exact E2).
        rewrite E1 in Hc; discriminate.
    + assert (E2 : o2 s = None) by (apply Hnone; exact E1).
      rewrite E2.
      destruct (Bool.eqb (db_amove s) who).
      * destruct H as [e [He Hw]]; exists e; split; [exact He|].
        apply IH; assumption.
      * intros e He; apply IH; auto.
Qed.

(** A smaller target is easier to force. *)
Theorem forces_margin_mono :
  forall k k' fuel s,
    k' <= k -> forces_margin k fuel s -> forces_margin k' fuel s.
Proof.
  intros k k' fuel s Hle H; unfold forces_margin in *.
  apply (forces_in_transfer (db_outc_ge k) (db_outc_ge k')
           (goal_win true) (goal_win true) true fuel s).
  - intros t; rewrite !db_outc_ge_none_iff; reflexivity.
  - intros t x y Hx Hy Hg.
    unfold db_outc_ge in Hx, Hy.
    destruct (db_moves m n t); [|discriminate].
    destruct (k <=? margin t) eqn:Ek; injection Hx as <-;
      destruct (k' <=? margin t) eqn:Ek'; injection Hy as <-;
      try reflexivity; try discriminate.
    exfalso; apply Z.leb_le in Ek; apply Z.leb_gt in Ek'; lia.
  - exact H.
Qed.

(** Symmetrically, a larger target is easier to deny. *)
Theorem denies_margin_mono :
  forall k k' fuel s,
    k <= k' -> denies_margin k fuel s -> denies_margin k' fuel s.
Proof.
  intros k k' fuel s Hle H; unfold denies_margin in *.
  apply (forces_in_transfer (db_outc_ge k) (db_outc_ge k')
           (goal_win false) (goal_win false) false fuel s).
  - intros t; rewrite !db_outc_ge_none_iff; reflexivity.
  - intros t x y Hx Hy Hg.
    unfold db_outc_ge in Hx, Hy.
    destruct (db_moves m n t); [|discriminate].
    destruct (k <=? margin t) eqn:Ek; injection Hx as <-;
      destruct (k' <=? margin t) eqn:Ek'; injection Hy as <-;
      try reflexivity; try discriminate.
    exfalso; apply Z.leb_gt in Ek; apply Z.leb_le in Ek'; lia.
  - exact H.
Qed.

(** * Every margin is decided *)

Theorem margin_determined :
  forall k fuel s,
    wf_st m n s -> (db_measure m n s <= fuel)%nat ->
    forces_margin k fuel s \/ denies_margin k fuel s.
Proof.
  intros k fuel s Hw Hf.
  apply (zermelo (db_moves m n) (db_play m n) db_amove (db_outc_ge k)
           (wf_st m n) (db_measure m n)).
  - intros t e Hi _ He; apply wf_play; assumption.
  - intros t e _ _ He; apply db_measure_play; exact He.
  - intros t _ Ho; apply (db_outc_ge_none_moves k); exact Ho.
  - apply db_outc_ge_not_drawn.
  - exact Hw.
  - exact Hf.
Qed.

Theorem margin_not_both :
  forall k fuel s, forces_margin k fuel s -> denies_margin k fuel s -> False.
Proof.
  intros k fuel s H1 H2.
  exact (forces_not_both (db_moves m n) (db_play m n) db_amove
           (db_outc_ge k) fuel s H1 H2).
Qed.

(** * Margin one is winning *)

(** [db_outc] and [db_outc_ge 1] disagree on how they name a draw, but the
    first player reads both the same way, so forcing a margin of one is
    exactly forcing a win. *)
Theorem forces_margin_win :
  forall fuel s,
    forces_margin 1 fuel s <->
    forces (db_moves m n) (db_play m n) db_amove (db_outc m n) true fuel s.
Proof.
  intros fuel s; unfold forces_margin; split; intros H.
  - apply (forces_in_transfer (db_outc_ge 1) (db_outc m n)
             (goal_win true) (goal_win true) true fuel s);
      [| | exact H].
    + intros t; rewrite db_outc_ge_none_iff, db_outc_none_iff; reflexivity.
    + intros t x y Hx Hy Hg.
      unfold db_outc_ge in Hx; unfold db_outc in Hy.
      destruct (db_moves m n t); [|discriminate].
      unfold margin in Hx.
      destruct (1 <=? Z.of_nat (s1 t) - Z.of_nat (s2 t)) eqn:Ek;
        injection Hx as <-; [|discriminate].
      apply Z.leb_le in Ek.
      assert (Hlt : (s2 t <? s1 t)%nat = true) by (apply Nat.ltb_lt; lia).
      rewrite Hlt in Hy; injection Hy as <-; reflexivity.
  - apply (forces_in_transfer (db_outc m n) (db_outc_ge 1)
             (goal_win true) (goal_win true) true fuel s);
      [| | exact H].
    + intros t; rewrite db_outc_none_iff, db_outc_ge_none_iff; reflexivity.
    + intros t x y Hx Hy Hg.
      unfold db_outc in Hx; unfold db_outc_ge in Hy.
      destruct (db_moves m n t); [|discriminate].
      destruct (s2 t <? s1 t)%nat eqn:E1; injection Hx as <-.
      * apply Nat.ltb_lt in E1.
        assert (Hk : 1 <=? margin t = true)
          by (apply Z.leb_le; unfold margin; lia).
        rewrite Hk in Hy; injection Hy as <-; reflexivity.
      * destruct (s1 t <? s2 t)%nat; discriminate.
Qed.

(** * The best margin on a finite board *)

(** No margin above the number of boxes is ever attained, so the forced
    margins are bounded and the search below is finite. *)
Lemma margin_le_boxes :
  forall s, wf_st m n s -> margin s <= Z.of_nat (length (boxes m n)).
Proof.
  intros s [_ [_ Hsc]].
  unfold margin, scored in *.
  assert (Hle : (ndone m n (laid s) <= length (boxes m n))%nat).
  { unfold ndone; apply length_filter_le. }
  lia.
Qed.

(** The first player cannot force more than the board holds: forcing drives
    play to a finished position, and there the margin is at most the number
    of boxes. *)
Theorem forces_margin_bounded :
  forall fuel k s,
    wf_st m n s -> forces_margin k fuel s ->
    k <= Z.of_nat (length (boxes m n)).
Proof.
  induction fuel as [|f IH]; intros k s Hw H; unfold forces_margin, forces in H.
  - apply (proj1 (forces_in_0_iff _ _ _ _ _ _ s)) in H.
    unfold db_outc_ge in H.
    destruct (db_moves m n s) as [|e r]; [|destruct H].
    destruct (k <=? margin s) eqn:Ek; simpl in H; [|discriminate].
    apply Z.leb_le in Ek.
    pose proof (margin_le_boxes s Hw); lia.
  - apply (proj1 (forces_in_S_iff _ _ _ _ _ _ f s)) in H.
    destruct (db_outc_ge k s) as [o|] eqn:E.
    + unfold db_outc_ge in E.
      destruct (db_moves m n s) as [|e r]; [|discriminate].
      destruct (k <=? margin s) eqn:Ek.
      * injection E as <-.
        apply Z.leb_le in Ek.
        pose proof (margin_le_boxes s Hw); lia.
      * injection E as <-; simpl in H; discriminate.
    + destruct (db_outc_ge_none_moves k s E) as [e He].
      destruct (Bool.eqb (db_amove s) true).
      * destruct H as [x [Hx Hplay]].
        apply (IH k (db_play m n s x));
          [apply wf_play; assumption | exact Hplay].
      * apply (IH k (db_play m n s e));
          [apply wf_play; assumption | apply H; exact He].
Qed.

End Margin.
