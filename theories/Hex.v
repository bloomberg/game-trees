(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Hex with a proof of Nash's theorem: the first player wins every board. *)

Require Import Corelib.Classes.RelationClasses.
Require Import Corelib.Program.Basics.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Arith.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Relations.Relation_Operators.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.Relations.
Require Import GameTrees.Trees.
Require Import GameTrees.Cotrees.
Require Import GameTrees.Determinacy.
Require Import GameTrees.Eval.
Require Import GameTrees.AlphaBeta.
Require Export GameTrees.Y.


(** * Hex boards *)

(** The n x n Hex board, row-major: red joins top-bottom, blue left-right. *)
Definition board : Type := list (option player).

Record game : Type := MkGame { brd : board; trn : player }.

Inductive result : Type :=
| won_by : player -> result
| draw : result
| ongoing : result.

(** Hexagonal adjacency on the parallelogram board. *)
Definition adjH (p q : cell) : Prop :=
     (fst q = fst p /\ (snd q = S (snd p) \/ snd p = S (snd q)))
  \/ (fst q = S (fst p) /\ (snd q = snd p \/ snd p = S (snd q)))
  \/ (fst p = S (fst q) /\ (snd q = snd p \/ snd q = S (snd p))).

Definition adjHb (p q : cell) : bool :=
     ((fst q =? fst p) && ((snd q =? S (snd p)) || (snd p =? S (snd q))))
  || ((fst q =? S (fst p)) && ((snd q =? snd p) || (snd p =? S (snd q))))
  || ((fst p =? S (fst q)) && ((snd q =? snd p) || (snd q =? S (snd p)))).

Lemma adjH_sym : forall p q, adjH p q -> adjH q p.
Proof. unfold adjH; intros p q H; lia. Qed.

Lemma adjHb_true_iff : forall p q, adjHb p q = true <-> adjH p q.
Proof.
  intros p q; unfold adjHb, adjH.
  repeat rewrite orb_true_iff; repeat rewrite andb_true_iff;
    repeat rewrite orb_true_iff; repeat rewrite Nat.eqb_eq.
  tauto.
Qed.

Section Hex.
Variable n : nat.
Hypothesis Hn : 1 <= n.

Definition all_cells : list cell := list_prod (seq 0 n) (seq 0 n).

Lemma in_all_cells : forall p, In p all_cells <-> fst p < n /\ snd p < n.
Proof.
  intros [r c]; unfold all_cells; split.
  - intros H; apply in_prod_iff in H; rewrite !in_seq in H; simpl; lia.
  - intros [H1 H2]; apply in_prod_iff; rewrite !in_seq; simpl in *; lia.
Qed.

Lemma NoDup_map_pair :
  forall (a : nat) (l : list nat),
    NoDup l -> NoDup (map (fun y : nat => (a, y)) l).
Proof.
  intros a l H; induction H; simpl; constructor; auto.
  intros Hin; apply in_map_iff in Hin.
  destruct Hin as [y [Hy Hin]]; inversion Hy; subst; auto.
Qed.

Lemma all_cells_nodup : NoDup all_cells.
Proof.
  unfold all_cells.
  generalize (seq_NoDup n 0).
  generalize (seq 0 n) at 1 2 as l1.
  intros l1 H1.
  induction H1 as [|a l1 Hnotin H1 IH]; simpl; [constructor|].
  apply NoDup_app_disj; auto.
  - apply NoDup_map_pair, seq_NoDup.
  - intros [x y] Hin Hx.
    apply in_map_iff in Hin; destruct Hin as [y' [Hy' _]].
    inversion Hy'; subst.
    apply in_prod_iff in Hx; tauto.
Qed.

(** ** Board access *)

Definition idx (p : cell) : nat := fst p * n + snd p.

Lemma idx_bound : forall p, fst p < n -> snd p < n -> idx p < n * n.
Proof.
  intros [r c] H1 H2; unfold idx; simpl in *.
  apply Nat.lt_le_trans with ((r + 1) * n).
  - replace ((r + 1) * n) with (r * n + n) by ring; lia.
  - apply Nat.mul_le_mono_r; lia.
Qed.

Lemma idx_div : forall r c, c < n -> (r * n + c) / n = r.
Proof.
  intros r c Hc.
  rewrite Nat.div_add_l by lia.
  rewrite Nat.div_small by auto; lia.
Qed.

Lemma idx_inj :
  forall p q,
    fst p < n -> snd p < n -> fst q < n -> snd q < n ->
    idx p = idx q -> p = q.
Proof.
  intros [a b] [c d]; unfold idx; simpl; intros H1 H2 H3 H4 H5.
  assert (Hac : a = c).
  { pose proof (idx_div a b H2); pose proof (idx_div c d H4); congruence. }
  subst c.
  assert (b = d) by lia.
  subst; auto.
Qed.

Fixpoint set_nth (b : board) (i : nat) (v : option player) : board :=
  match b, i with
  | [], _ => []
  | _ :: rest, O => v :: rest
  | x :: rest, S i' => x :: set_nth rest i' v
  end.

Definition get_cell (b : board) (p : cell) : option player :=
  nth (idx p) b None.

Definition set_cell (b : board) (p : cell) (v : option player) : board :=
  set_nth b (idx p) v.

Lemma set_nth_length : forall b i v, length (set_nth b i v) = length b.
Proof.
  induction b as [|x b IH]; intros [|i] v; simpl; auto.
Qed.

Lemma nth_set_nth_same :
  forall b i v, i < length b -> nth i (set_nth b i v) None = v.
Proof.
  induction b as [|x b IH]; intros [|i] v H; simpl in *; auto; try lia.
  apply IH; lia.
Qed.

Lemma nth_set_nth_other :
  forall b i j v, i <> j -> nth j (set_nth b i v) None = nth j b None.
Proof.
  induction b as [|x b IH]; intros [|i] [|j] v H; simpl in *; auto; try lia.
Qed.

Lemma set_cell_length :
  forall b p v, length (set_cell b p v) = length b.
Proof. intros; apply set_nth_length. Qed.

Lemma get_set_same :
  forall b p v, idx p < length b -> get_cell (set_cell b p v) p = v.
Proof. intros; apply nth_set_nth_same; auto. Qed.

Lemma get_set_other :
  forall b p q v, idx p <> idx q -> get_cell (set_cell b p v) q = get_cell b q.
Proof. intros; apply nth_set_nth_other; auto. Qed.

(** ** Connectivity *)

Definition stone (b : board) (X : player) (p : cell) : Prop :=
  fst p < n /\ snd p < n /\ get_cell b p = Some X.

Definition stoneb (b : board) (X : player) (p : cell) : bool :=
  (fst p <? n) && (snd p <? n) &&
  match get_cell b p with
  | Some Y => player_eqb Y X
  | None => false
  end.

Lemma stoneb_true_iff :
  forall b X p, stoneb b X p = true <-> stone b X p.
Proof.
  intros b X p; unfold stoneb, stone.
  rewrite !andb_true_iff, !Nat.ltb_lt.
  destruct (get_cell b p) as [Y|].
  - rewrite player_eqb_true_iff; split.
    + intros [[H1 H2] ->]; auto.
    + intros (H1 & H2 & HY); inversion HY; auto.
  - split.
    + intros [_ H]; discriminate.
    + intros (_ & _ & H); discriminate.
Qed.

Lemma stoneb_in_all_cells :
  forall b X p, stoneb b X p = true -> In p all_cells.
Proof.
  intros b X p H; apply stoneb_true_iff in H.
  apply in_all_cells; destruct H as (H1 & H2 & _); auto.
Qed.

Lemma chain_bool_iff :
  forall b X p q,
    chain (Gb (stoneb b X)) (Ab adjHb) p q <-> chain (stone b X) adjH p q.
Proof.
  intros b X p q; split; apply chain_impl.
  - intros x H; apply stoneb_true_iff; auto.
  - intros x y H; apply adjHb_true_iff; auto.
  - intros x H; apply stoneb_true_iff; auto.
  - intros x y H; apply adjHb_true_iff; auto.
Qed.

(** A cell open to [X]: in bounds and not blocked by the opponent. *)
Definition openb (b : board) (X : player) (p : cell) : bool :=
  (fst p <? n) && (snd p <? n) &&
  match get_cell b p with
  | Some Y => player_eqb Y X
  | None => true
  end.

Lemma stone_open : forall b X p, stone b X p -> openb b X p = true.
Proof.
  intros b X p (H1 & H2 & Hget); unfold openb.
  rewrite Hget.
  rewrite !andb_true_iff, !Nat.ltb_lt.
  repeat split; auto.
  apply player_eqb_true_iff; auto.
Qed.

Lemma openb_in_all_cells :
  forall b X p, openb b X p = true -> In p all_cells.
Proof.
  intros b X p H; unfold openb in H.
  rewrite !andb_true_iff, !Nat.ltb_lt in H.
  apply in_all_cells; tauto.
Qed.

(** A legal placement, by either player, only shrinks openness. *)
Lemma openb_set_le :
  forall b p X C x,
    length b = n * n -> fst p < n -> snd p < n ->
    get_cell b p = None ->
    openb (set_cell b p (Some X)) C x = true ->
    openb b C x = true.
Proof.
  intros b p X C x Hlen Hp1 Hp2 Hnone H.
  unfold openb in *.
  rewrite !andb_true_iff in H; destruct H as [[H1 H2] H3].
  rewrite Nat.ltb_lt in H1, H2.
  rewrite !andb_true_iff; repeat split; try (apply Nat.ltb_lt; auto).
  destruct (cell_eq_dec x p) as [-> | Hne].
  - rewrite Hnone; auto.
  - rewrite get_set_other in H3; auto.
    intros Hidx; apply Hne; symmetry; apply idx_inj; auto.
Qed.

(** ** Connectivity, parameterized by the side projection *)

(** Red instantiates [proj] with [fst], blue with [snd]. *)

Section SideConn.
  Variable X : player.
  Variable proj : cell -> nat.
  Hypothesis proj_adj :
    forall p q, adjH p q -> proj q <= S (proj p) /\ proj p <= S (proj q).

  Definition side_seeds (b : board) : list cell :=
    filter (fun p => (proj p =? 0) && stoneb b X p) all_cells.

  Definition side_reach (b : board) : list cell :=
    reach_from all_cells (stoneb b X) adjHb (side_seeds b).

  Definition side_connb (b : board) : bool :=
    existsb (fun d => (S (proj d) =? n) && memb d (side_reach b)) all_cells.

    (** A chain of [X] stones from the [proj = 0] side to the far side. *)
  Definition side_connected (b : board) : Prop :=
    exists a d,
      proj a = 0 /\ S (proj d) = n /\ chain (stone b X) adjH a d.

  Lemma side_connb_true_iff :
    forall b, side_connb b = true <-> side_connected b.
  Proof.
    intros b; unfold side_connb; rewrite existsb_exists; split.
    - intros [d [Hd Hb]].
      apply andb_true_iff in Hb; destruct Hb as [Hbot Hm].
      apply Nat.eqb_eq in Hbot.
      apply memb_true_iff in Hm.
      destruct (reach_from_sound all_cells (stoneb b X) adjHb (side_seeds b))
        with (p := d) as [a [Ha Hch]]; auto.
      { intros a Ha; apply filter_In in Ha; destruct Ha as [_ Ha].
        apply andb_true_iff in Ha; unfold Gb; tauto. }
      apply filter_In in Ha; destruct Ha as [_ Ha].
      apply andb_true_iff in Ha; destruct Ha as [Htop _].
      apply Nat.eqb_eq in Htop.
      exists a, d; repeat split; auto.
      apply chain_bool_iff; auto.
    - intros (a & d & Htop & Hbot & Hch).
      assert (Hga : stone b X a) by (eapply chain_good_l; eauto).
      assert (Hgd : stone b X d) by (eapply chain_good_r; eauto).
      exists d; split.
      + apply in_all_cells; destruct Hgd as (H1 & H2 & _); auto.
      + apply andb_true_iff; split.
        * apply Nat.eqb_eq; auto.
        * apply memb_true_iff.
          eapply reach_from_complete with (a := a); eauto.
          -- apply all_cells_nodup.
          -- apply NoDup_filter, all_cells_nodup.
          -- intros x Hx; apply filter_In in Hx; tauto.
          -- intros x Hx; eapply stoneb_in_all_cells; eauto.
          -- apply filter_In; split.
             ++ apply in_all_cells; destruct Hga as (H1 & H2 & _); auto.
             ++ apply andb_true_iff; split.
                ** apply Nat.eqb_eq; auto.
                ** apply stoneb_true_iff; auto.
          -- apply chain_bool_iff; auto.
  Qed.

  (** *** Open reach and connection deficits *)

  (** Cells reachable from the [proj = 0] edge through open cells. *)
  Definition side_open_reach (b : board) : list cell :=
    reach_from all_cells (openb b X) adjHb
      (filter (fun p => (proj p =? 0) && openb b X p) all_cells).

    (** The projection levels the open reach touches. *)
  Definition side_levels_reached (b : board) : nat :=
    length (filter
      (fun i => existsb (fun p => (proj p =? i) && memb p (side_open_reach b))
                        all_cells)
      (seq 0 n)).

  Lemma side_open_reach_incl :
    forall b, incl (side_open_reach b) all_cells.
  Proof.
    intros b; unfold side_open_reach, reach_from.
    apply iterate_incl_U.
    intros z Hz; apply filter_In in Hz; tauto.
  Qed.

  (** A winning chain keeps every level inside the open reach. *)
  Lemma side_connected_levels :
    forall b k,
      side_connected b -> k < n ->
      exists x, proj x = k /\ In x (side_open_reach b).
  Proof.
    intros b k (a & d & Ha & Hd & Hch) Hk.
    assert (Hcho : chain (Gb (openb b X)) (Ab adjHb) a d).
    { eapply chain_impl; [| |exact Hch].
      - intros x Hx; unfold Gb; apply stone_open; auto.
      - intros x y HA; unfold Ab; apply adjHb_true_iff; auto. }
    assert (Hstep : forall x y, Ab adjHb x y ->
              proj y <= S (proj x) /\ proj x <= S (proj y)).
    { intros x y HA; apply proj_adj; apply adjHb_true_iff; auto. }
    assert (Hbet : (proj a <= k <= proj d) \/ (proj d <= k <= proj a))
      by (left; lia).
    destruct (chain_proj_intermediate proj _ _ Hstep a d k Hcho Hbet)
      as [x [Hx Hchx]].
    exists x; split; auto.
    unfold side_open_reach.
    eapply reach_from_complete with (a := a); eauto.
    - apply all_cells_nodup.
    - apply NoDup_filter, all_cells_nodup.
    - intros z Hz; apply filter_In in Hz; tauto.
    - intros z Hz; eapply openb_in_all_cells; eauto.
    - apply filter_In; split.
      + eapply openb_in_all_cells.
        exact (chain_good_l _ _ _ _ Hcho).
      + apply andb_true_iff; split.
        * apply Nat.eqb_eq; auto.
        * exact (chain_good_l _ _ _ _ Hcho).
  Qed.

  Lemma side_levels_reached_full :
    forall b, side_connected b -> side_levels_reached b = n.
  Proof.
    intros b Hconn; unfold side_levels_reached.
    rewrite filter_all.
    - apply length_seq.
    - intros k Hk; apply in_seq in Hk.
      destruct (side_connected_levels b k Hconn) as [x [Hx Hin]]; [lia|].
      apply existsb_exists; exists x; split.
      + apply (side_open_reach_incl b x); auto.
      + apply andb_true_iff; split.
        * apply Nat.eqb_eq; auto.
        * apply memb_true_iff; auto.
  Qed.

  Lemma side_open_reach_set_le :
    forall b p X' x,
      length b = n * n -> fst p < n -> snd p < n ->
      get_cell b p = None ->
      In x (side_open_reach (set_cell b p (Some X'))) ->
      In x (side_open_reach b).
  Proof.
    intros b p X' x Hlen Hp1 Hp2 Hnone Hin.
    assert (Hg : forall z,
        In z (filter (fun q => (proj q =? 0) &&
                openb (set_cell b p (Some X')) X q) all_cells) ->
        Gb (openb (set_cell b p (Some X')) X) z).
    { intros z Hz; apply filter_In in Hz; destruct Hz as [_ Hz].
      apply andb_true_iff in Hz; unfold Gb; tauto. }
    unfold side_open_reach in Hin.
    destruct (reach_from_sound _ _ _ _ Hg x Hin) as [a [Ha Hch]].
    apply filter_In in Ha; destruct Ha as [HaU Ha].
    apply andb_true_iff in Ha; destruct Ha as [Ha0 Haop].
    unfold side_open_reach.
    eapply reach_from_complete with (a := a); eauto.
    - apply all_cells_nodup.
    - apply NoDup_filter, all_cells_nodup.
    - intros z Hz; apply filter_In in Hz; tauto.
    - intros z Hz; eapply openb_in_all_cells; eauto.
    - apply filter_In; split; auto.
      apply andb_true_iff; split; auto.
      eapply openb_set_le; eauto.
    - eapply chain_impl; [| |exact Hch].
      + intros z Hz; unfold Gb in *.
        eapply openb_set_le; eauto.
      + auto.
  Qed.

  Lemma side_levels_set_le :
    forall b p X',
      length b = n * n -> fst p < n -> snd p < n ->
      get_cell b p = None ->
      side_levels_reached (set_cell b p (Some X')) <= side_levels_reached b.
  Proof.
    intros b p X' Hlen Hp1 Hp2 Hnone; unfold side_levels_reached.
    apply filter_impl_length_le.
    intros k _ Hk.
    apply existsb_exists in Hk as [x [HxU Hx]].
    apply andb_true_iff in Hx as [Hproj Hm].
    apply existsb_exists; exists x; split; auto.
    apply andb_true_iff; split; auto.
    apply memb_true_iff.
    eapply side_open_reach_set_le; eauto.
    apply memb_true_iff; exact Hm.
  Qed.
End SideConn.

(** Hexagonal adjacency moves each coordinate by at most one. *)
Lemma adjH_coord_le :
  forall p q, adjH p q ->
    (fst q <= S (fst p) /\ fst p <= S (fst q)) /\
    (snd q <= S (snd p) /\ snd p <= S (snd q)).
Proof.
  intros p q HA; unfold adjH in HA; lia.
Qed.

Lemma fst_adjH_le :
  forall p q, adjH p q -> fst q <= S (fst p) /\ fst p <= S (fst q).
Proof. intros p q HA; apply adjH_coord_le; auto. Qed.

Lemma snd_adjH_le :
  forall p q, adjH p q -> snd q <= S (snd p) /\ snd p <= S (snd q).
Proof. intros p q HA; apply adjH_coord_le; auto. Qed.

(** The red and blue instances of the side-parameterized development. *)

Definition red_seeds : board -> list cell := side_seeds red fst.
Definition red_reach : board -> list cell := side_reach red fst.
Definition red_connb : board -> bool := side_connb red fst.

(** A red chain from the top row to the bottom row. *)
Definition red_connected : board -> Prop := side_connected red fst.

Definition blue_seeds : board -> list cell := side_seeds blue snd.
Definition blue_reach : board -> list cell := side_reach blue snd.
Definition blue_connb : board -> bool := side_connb blue snd.

(** A blue chain from the left column to the right column. *)
Definition blue_connected : board -> Prop := side_connected blue snd.

Lemma red_connb_true_iff :
  forall b, red_connb b = true <-> red_connected b.
Proof. intros b; apply side_connb_true_iff. Qed.

Lemma blue_connb_true_iff :
  forall b, blue_connb b = true <-> blue_connected b.
Proof. intros b; apply side_connb_true_iff. Qed.

Definition red_open_reach : board -> list cell := side_open_reach red fst.
Definition red_rows_reached : board -> nat := side_levels_reached red fst.
Definition blue_open_reach : board -> list cell := side_open_reach blue snd.
Definition blue_cols_reached : board -> nat := side_levels_reached blue snd.

(** ** Results *)

Definition emptyb (b : board) (p : cell) : bool :=
  match get_cell b p with None => true | Some _ => false end.

Definition empties (b : board) : list cell :=
  filter (fun p => emptyb b p) all_cells.

Definition fullb (b : board) : bool :=
  forallb (fun p => negb (emptyb b p)) all_cells.

Definition get_result (g : game) : result :=
  if red_connb (brd g) then won_by red
  else if blue_connb (brd g) then won_by blue
  else if fullb (brd g) then draw
  else ongoing.

(** * The no-draw theorem *)

(** Hex(n) embeds into Y(2n-1) with two pre-filled corner regions. *)

Definition ym : nat := 2 * n - 1.

Definition inU (p : cell) : Prop := fst p < n - 1.
Definition inW (p : cell) : Prop := snd p + n <= fst p.
Definition inRh (p : cell) : Prop :=
  n - 1 <= fst p /\ fst p <= snd p + (n - 1).

Definition hexof (p : cell) : cell :=
  (fst p - (n - 1), snd p - (fst p - (n - 1))).

Definition yof (p : cell) : cell :=
  (fst p + (n - 1), fst p + snd p).

Lemma yof_hexof :
  forall p, inY ym p -> inRh p -> yof (hexof p) = p.
Proof.
  intros [i j] [HY1 HY2] [HR1 HR2]; unfold yof, hexof; simpl in *.
  f_equal; lia.
Qed.

Lemma hexof_bounds :
  forall p, inY ym p -> inRh p ->
    fst (hexof p) < n /\ snd (hexof p) < n.
Proof.
  intros [i j] [HY1 HY2] [HR1 HR2]; unfold hexof, ym in *; simpl in *; lia.
Qed.

Definition hexcolor (b : board) (p : cell) : player :=
  match get_cell b p with Some X => X | None => red end.

Definition cY (b : board) (p : cell) : player :=
  if fst p <? n - 1 then red
  else if snd p + n <=? fst p then blue
  else hexcolor b (hexof p).

Lemma regions :
  forall p, inY ym p -> inU p \/ inW p \/ inRh p.
Proof.
  intros [i j] [H1 H2]; unfold inU, inW, inRh, ym in *; simpl in *; lia.
Qed.

Lemma cY_U : forall b p, inU p -> cY b p = red.
Proof.
  intros b p H; unfold cY, inU in *.
  destruct (fst p <? n - 1) eqn:E; auto.
  apply Nat.ltb_ge in E; lia.
Qed.

Lemma cY_W : forall b p, inW p -> cY b p = blue.
Proof.
  intros b p H; unfold cY, inW in *.
  destruct (fst p <? n - 1) eqn:E1.
  - apply Nat.ltb_lt in E1; lia.
  - destruct (snd p + n <=? fst p) eqn:E2; auto.
    apply Nat.leb_gt in E2; lia.
Qed.

Lemma cY_Rh :
  forall b p, inRh p -> cY b p = hexcolor b (hexof p).
Proof.
  intros b p [H1 H2]; unfold cY.
  destruct (fst p <? n - 1) eqn:E1.
  - apply Nat.ltb_lt in E1; lia.
  - destruct (snd p + n <=? fst p) eqn:E2; auto.
    apply Nat.leb_le in E2; lia.
Qed.

Lemma adj_transfer :
  forall p q, adjH p q <-> adjY (yof p) (yof q).
Proof.
  intros [a b] [c d]; unfold adjH, adjY, yof; simpl; lia.
Qed.

Lemma adjY_Rh_adjH :
  forall p q,
    inY ym p -> inRh p -> inY ym q -> inRh q ->
    adjY p q -> adjH (hexof p) (hexof q).
Proof.
  intros p q HYp HRp HYq HRq HA.
  apply adj_transfer.
  rewrite (yof_hexof p), (yof_hexof q); auto.
Qed.

Lemma cY_stone :
  forall b X p,
    (forall q, In q all_cells -> get_cell b q <> None) ->
    inY ym p -> inRh p -> cY b p = X ->
    stone b X (hexof p).
Proof.
  intros b X p Hfull HY HR Hc.
  rewrite cY_Rh in Hc; auto.
  destruct (hexof_bounds p HY HR) as [Hb1 Hb2].
  unfold stone; repeat split; auto.
  unfold hexcolor in Hc.
  destruct (get_cell b (hexof p)) eqn:E.
  - congruence.
  - exfalso; eapply Hfull; eauto.
    apply in_all_cells; auto.
Qed.

(** A red Y-chain ending in the rhombus entered it from the top or stayed. *)
Lemma y_chain_red_extract :
  forall b,
    (forall q, In q all_cells -> get_cell b q <> None) ->
    forall x d,
      chain (goodY ym (cY b) red) adjY x d ->
      inRh d ->
      (exists t, fst t = 0 /\ chain (stone b red) adjH t (hexof d))
      \/ (inRh x /\ chain (stone b red) adjH (hexof x) (hexof d)).
Proof.
  intros b Hfull x d ch.
  induction ch as [x HG | x y d HG HA ch IH]; intros HRd.
  - right; split; auto.
    destruct HG as [HY Hc].
    apply chain_refl, cY_stone; auto.
  - destruct (IH HRd) as [Hleft | [HRy Hch]]; [left; auto|].
    destruct HG as [HYx Hcx].
    assert (HGy : goodY ym (cY b) red y) by (eapply chain_good_l; eauto).
    destruct HGy as [HYy Hcy].
    destruct (regions x HYx) as [HU | [HW | HR]].
    + (* crossing from the red top region: y is on the hex top row *)
      left; exists (hexof y); split.
      * unfold inU, inRh, hexof in *; unfold adjY in HA; simpl in *; lia.
      * auto.
    + (* impossible: the wedge is blue *)
      rewrite cY_W in Hcx; auto; discriminate.
    + right; split; auto.
      eapply chain_step; [| |eauto].
      * apply cY_stone; auto.
      * apply adjY_Rh_adjH; auto.
Qed.

(** The crossing lemma for blue, entering from the pre-filled left wedge. *)
Lemma y_chain_blue_extract :
  forall b,
    (forall q, In q all_cells -> get_cell b q <> None) ->
    forall x d,
      chain (goodY ym (cY b) blue) adjY x d ->
      inRh d ->
      (exists l, snd l = 0 /\ chain (stone b blue) adjH l (hexof d))
      \/ (inRh x /\ chain (stone b blue) adjH (hexof x) (hexof d)).
Proof.
  intros b Hfull x d ch.
  induction ch as [x HG | x y d HG HA ch IH]; intros HRd.
  - right; split; auto.
    destruct HG as [HY Hc].
    apply chain_refl, cY_stone; auto.
  - destruct (IH HRd) as [Hleft | [HRy Hch]]; [left; auto|].
    destruct HG as [HYx Hcx].
    assert (HGy : goodY ym (cY b) blue y) by (eapply chain_good_l; eauto).
    destruct HGy as [HYy Hcy].
    destruct (regions x HYx) as [HU | [HW | HR]].
    + (* impossible: the top region is red *)
      rewrite cY_U in Hcx; auto; discriminate.
    + (* crossing from the blue wedge: y is on the hex left column *)
      left; exists (hexof y); split.
      * unfold inW, inRh, inY, hexof in *; unfold adjY in HA; simpl in *; lia.
      * auto.
    + right; split; auto.
      eapply chain_step; [| |eauto].
      * apply cY_stone; auto.
      * apply adjY_Rh_adjH; auto.
Qed.

Theorem hex_no_draw :
  forall b,
    (forall q, In q all_cells -> get_cell b q <> None) ->
    red_connected b \/ blue_connected b.
Proof.
  intros b Hfull.
  destruct (y_theorem ym (cY b)) as [Hw | Hw];
    [unfold ym; lia | left | right].
  - destruct Hw as (a & b' & d & Ha & Hb' & Hd & Hab & Had).
    assert (HGd : goodY ym (cY b) red d) by (eapply chain_good_r; eauto).
    destruct HGd as [HYd Hcd].
    assert (HRd : inRh d).
    { destruct (regions d HYd) as [HU | [HW | HR]]; auto.
      - unfold inU, ym in *; destruct HYd; lia.
      - rewrite cY_W in Hcd; auto; discriminate. }
    destruct (y_chain_red_extract b Hfull a d Had HRd)
      as [[t [Ht Hch]] | [HRa Hch]].
    + exists t, (hexof d); repeat split; auto.
      unfold hexof, ym in *; destruct HYd; simpl in *; lia.
    + exists (hexof a), (hexof d).
      assert (HGa : goodY ym (cY b) red a) by (eapply chain_good_l; eauto).
      destruct HGa as [HYa _].
      repeat split; auto.
      * unfold hexof, inRh in *; simpl in *; lia.
      * unfold hexof, ym in *; destruct HYd; simpl in *; lia.
  - destruct Hw as (a & b' & d & Ha & Hb' & Hd & Hab & Had).
    assert (HGb : goodY ym (cY b) blue b') by (eapply chain_good_r; eauto).
    destruct HGb as [HYb Hcb].
    assert (HRb : inRh b').
    { destruct (regions b' HYb) as [HU | [HW | HR]]; auto.
      - rewrite cY_U in Hcb; auto; discriminate.
      - unfold inW in *; lia. }
    destruct (y_chain_blue_extract b Hfull a b' Hab HRb)
      as [[l [Hl Hch]] | [HRa Hch]].
    + exists l, (hexof b'); repeat split; auto.
      unfold hexof, inRh in *; simpl in *; lia.
    + exists (hexof a), (hexof b').
      assert (HGa : goodY ym (cY b) blue a) by (eapply chain_good_l; eauto).
      destruct HGa as [HYa _].
      repeat split; auto.
      * unfold hexof, inRh in *; simpl in *; lia.
      * unfold hexof, inRh in *; simpl in *; lia.
Qed.

Lemma fullb_spec :
  forall b, fullb b = true <->
    (forall q, In q all_cells -> get_cell b q <> None).
Proof.
  intros b; unfold fullb; rewrite forallb_forall; split.
  - intros H q Hq Hnone.
    specialize (H q Hq); unfold emptyb in H.
    rewrite Hnone in H; discriminate.
  - intros H q Hq; specialize (H q Hq); unfold emptyb.
    destruct (get_cell b q); auto; congruence.
Qed.

Lemma get_result_not_draw :
  forall g, get_result g <> draw.
Proof.
  intros g; unfold get_result.
  destruct (red_connb (brd g)) eqn:Er; [discriminate|].
  destruct (blue_connb (brd g)) eqn:Eb; [discriminate|].
  destruct (fullb (brd g)) eqn:Ef; [|discriminate].
  intros _.
  pose proof (proj1 (fullb_spec (brd g)) Ef) as Hf.
  destruct (hex_no_draw (brd g) Hf) as [H | H].
  - apply red_connb_true_iff in H; congruence.
  - apply blue_connb_true_iff in H; congruence.
Qed.

(** * The at-most-one-winner theorem *)

(** Two hex winners would put two winners on one Y board. *)

Lemma hexof_yof : forall p, hexof (yof p) = p.
Proof. intros [r c]; unfold hexof, yof; simpl; f_equal; lia. Qed.

Lemma yof_inY : forall p, fst p < n -> snd p < n -> inY ym (yof p).
Proof.
  intros [r c] H1 H2; unfold inY, yof, ym; simpl in *; split; lia.
Qed.

Lemma yof_inRh : forall p, fst p < n -> snd p < n -> inRh (yof p).
Proof.
  intros [r c] H1 H2; unfold inRh, yof; simpl in *; split; lia.
Qed.

Lemma stone_goodY :
  forall b X p, stone b X p -> goodY ym (cY b) X (yof p).
Proof.
  intros b X p Hs.
  pose proof Hs as (H1 & H2 & Hget).
  split; [apply yof_inY; auto|].
  rewrite cY_Rh by (apply yof_inRh; auto).
  unfold hexcolor; rewrite hexof_yof, Hget; auto.
Qed.

(** Transport a hex chain into the [cY] coloring of the Y board. *)
Lemma hex_chain_Y :
  forall b X p q,
    chain (stone b X) adjH p q ->
    chain (goodY ym (cY b) X) adjY (yof p) (yof q).
Proof.
  intros b X p q ch.
  eapply chain_map; [| |exact ch].
  - intros x Hx; apply stone_goodY; auto.
  - intros x y HA; apply adj_transfer; auto.
Qed.

Lemma inU_good :
  forall b i j, 2 <= n -> i < n - 1 -> j <= i -> goodY ym (cY b) red (i, j).
Proof.
  intros b i j H2 Hi Hj; split.
  - unfold inY, ym; simpl; split; lia.
  - apply cY_U; unfold inU; simpl; lia.
Qed.

Lemma inW_good :
  forall b i j, j + n <= i -> i < ym -> goodY ym (cY b) blue (i, j).
Proof.
  intros b i j Hji Hi; split.
  - unfold inY; simpl; split; lia.
  - apply cY_W; unfold inW; simpl; lia.
Qed.

(** Walks inside the pre-filled regions of the Y board. *)
Lemma chain_U_col :
  forall b, 2 <= n ->
  forall i, i <= n - 2 -> chain (goodY ym (cY b) red) adjY (0, 0) (i, 0).
Proof.
  intros b H2; induction i as [|i IHi]; intros Hi.
  - apply chain_refl, inU_good; lia.
  - eapply chain_snoc;
      [apply IHi; lia | unfold adjY; simpl; lia | apply inU_good; lia].
Qed.

Lemma chain_U_row :
  forall b i, 2 <= n -> i <= n - 2 ->
  forall j, j <= i -> chain (goodY ym (cY b) red) adjY (i, 0) (i, j).
Proof.
  intros b i H2 Hi; induction j as [|j IHj]; intros Hj.
  - apply chain_refl, inU_good; lia.
  - eapply chain_snoc;
      [apply IHj; lia | unfold adjY; simpl; lia | apply inU_good; lia].
Qed.

Lemma chain_W_col :
  forall b, 2 <= n ->
  forall k, k <= n - 2 ->
    chain (goodY ym (cY b) blue) adjY (n, 0) (n + k, 0).
Proof.
  intros b H2; induction k as [|k IHk]; intros Hk.
  - replace (n + 0) with n by lia.
    apply chain_refl, inW_good; unfold ym; lia.
  - eapply chain_snoc;
      [apply IHk; lia | unfold adjY; simpl; lia |
       apply inW_good; unfold ym; lia].
Qed.

Lemma chain_W_diag :
  forall b, 2 <= n ->
  forall k, k <= n - 2 ->
    chain (goodY ym (cY b) blue) adjY (n, 0) (n + k, k).
Proof.
  intros b H2; induction k as [|k IHk]; intros Hk.
  - replace (n + 0) with n by lia.
    apply chain_refl, inW_good; unfold ym; lia.
  - eapply chain_snoc;
      [apply IHk; lia | unfold adjY; simpl; lia |
       apply inW_good; unfold ym; lia].
Qed.

(** A red top-bottom hex connection yields a red Y-win. *)
Lemma red_Y_wins :
  forall b, 2 <= n -> red_connected b -> Y_wins ym (cY b) red.
Proof.
  intros b H2 (a & d & Ha & Hd & Hch).
  pose proof (chain_good_l _ _ _ _ Hch) as Hga.
  destruct a as [ra ca]; simpl in Ha; subst ra.
  pose proof Hga as (Ha1 & Ha2 & Hgeta); simpl in Ha1, Ha2.
  exists (0, 0), (0, 0), (yof d).
  split; [reflexivity|].
  split; [reflexivity|].
  split.
  { unfold yof, ym; simpl; lia. }
  split.
  { apply chain_refl, inU_good; lia. }
  apply chain_trans with (q := yof (0, ca)).
  - destruct (Nat.le_gt_cases ca (n - 2)) as [Hca | Hca].
    + eapply chain_snoc.
      * eapply chain_trans.
        -- apply (chain_U_col b H2 (n - 2)); lia.
        -- apply (chain_U_row b (n - 2) H2) with (j := ca); lia.
      * unfold adjY, yof; simpl; lia.
      * apply stone_goodY; exact Hga.
    + eapply chain_snoc.
      * eapply chain_trans.
        -- apply (chain_U_col b H2 (n - 2)); lia.
        -- apply (chain_U_row b (n - 2) H2) with (j := n - 2); lia.
      * unfold adjY, yof; simpl; lia.
      * apply stone_goodY; exact Hga.
  - apply (hex_chain_Y b red (0, ca) d); auto.
Qed.

(** A blue left-right hex connection yields a blue Y-win. *)
Lemma blue_Y_wins :
  forall b, 2 <= n -> blue_connected b -> Y_wins ym (cY b) blue.
Proof.
  intros b H2 (a & d & Ha & Hd & Hch).
  pose proof (chain_good_l _ _ _ _ Hch) as Hga.
  pose proof (chain_good_r _ _ _ _ Hch) as Hgd.
  destruct a as [ra ca]; simpl in Ha; subst ca.
  pose proof Hga as (Ha1 & Ha2 & Hgeta); simpl in Ha1, Ha2.
  destruct Hgd as (Hd1 & Hd2 & _).
  exists (n, 0), (yof d), (n + (n - 2), 0).
  split; [reflexivity|].
  split.
  { unfold yof; simpl; lia. }
  split.
  { simpl; unfold ym; lia. }
  split.
  - apply chain_trans with (q := yof (ra, 0)).
    + eapply chain_snoc.
      * apply (chain_W_diag b H2 (ra - 1)); lia.
      * unfold adjY, yof; simpl; lia.
      * apply stone_goodY; exact Hga.
    + apply (hex_chain_Y b blue (ra, 0) d); auto.
  - apply (chain_W_col b H2 (n - 2)); lia.
Qed.

(** No board carries both a red and a blue connection. *)
Theorem hex_at_most_one :
  forall b, red_connected b -> blue_connected b -> False.
Proof.
  intros b Hr Hb.
  destruct (Nat.le_gt_cases 2 n) as [H2 | H1].
  - exact (y_at_most_one ym (cY b)
             (red_Y_wins b H2 Hr) (blue_Y_wins b H2 Hb)).
  - destruct Hr as (a & d & _ & _ & Hch).
    destruct Hb as (a' & d' & _ & _ & Hch').
    apply chain_good_l in Hch; apply chain_good_l in Hch'.
    destruct Hch as (H1a & H2a & Hg); destruct Hch' as (H1b & H2b & Hg').
    destruct a as [x y]; destruct a' as [x' y']; simpl in *.
    assert (x = 0) by lia; assert (y = 0) by lia;
      assert (x' = 0) by lia; assert (y' = 0) by lia; subst.
    congruence.
Qed.

(** On a full board exactly one side has a connection. *)
Corollary hex_exactly_one :
  forall b,
    (forall q, In q all_cells -> get_cell b q <> None) ->
    (red_connected b /\ ~ blue_connected b) \/
    (blue_connected b /\ ~ red_connected b).
Proof.
  intros b Hfull.
  destruct (hex_no_draw b Hfull) as [H | H].
  - left; split; auto; intros Hb; exact (hex_at_most_one b H Hb).
  - right; split; auto; intros Hr; exact (hex_at_most_one b Hr H).
Qed.

(** * The Hex game *)

Definition hex_init : game := MkGame (repeat None (n * n)) red.

Definition apply_move (g : game) (p : cell) : game :=
  MkGame (set_cell (brd g) p (Some (trn g))) (other (trn g)).

Definition moves (g : game) : list cell :=
  match get_result g with
  | ongoing => empties (brd g)
  | _ => []
  end.

Lemma in_empties :
  forall b p,
    In p (empties b) <-> In p all_cells /\ get_cell b p = None.
Proof.
  intros b p; unfold empties; rewrite filter_In; unfold emptyb.
  destruct (get_cell b p); split; intros [H1 H2]; auto; discriminate.
Qed.

Lemma in_moves :
  forall g p,
    In p (moves g) <->
    get_result g = ongoing /\ In p all_cells /\ get_cell (brd g) p = None.
Proof.
  intros g p; unfold moves.
  destruct (get_result g) eqn:E; try (split; [intros [] | intros [H _]; congruence]).
  rewrite in_empties; tauto.
Qed.

Lemma apply_move_length :
  forall g p, length (brd (apply_move g p)) = length (brd g).
Proof. intros; simpl; apply set_cell_length. Qed.

Lemma forallb_false_exists :
  forall (f : cell -> bool) l,
    forallb f l = false -> exists x, In x l /\ f x = false.
Proof.
  intros f l; induction l as [|a l IH]; simpl; intros H; [discriminate|].
  destruct (f a) eqn:E; simpl in H.
  - destruct (IH H) as [x [Hx Hfx]]; eauto.
  - exists a; auto.
Qed.

Lemma moves_nonempty_of_ongoing :
  forall g, get_result g = ongoing -> exists p, In p (moves g).
Proof.
  intros g Hres.
  assert (Hfull : fullb (brd g) = false).
  { unfold get_result in Hres.
    destruct (red_connb (brd g)); [discriminate|].
    destruct (blue_connb (brd g)); [discriminate|].
    destruct (fullb (brd g)); [discriminate | auto]. }
  destruct (forallb_false_exists _ _ Hfull) as [p [Hin Hp]].
  apply negb_false_iff in Hp.
  exists p; apply in_moves; repeat split; auto.
  unfold emptyb in Hp; destruct (get_cell (brd g) p); congruence.
Qed.

(** ** The complete game tree *)

Inductive game_step : game -> game -> Prop :=
| gstep : forall g p,
    length (brd g) = n * n ->
    In p (moves g) ->
    game_step g (apply_move g p).

Definition hex_next (g : game) : list game := map (apply_move g) (moves g).

Definition later (g1 g2 : game) : Prop :=
  length (empties (brd g1)) < length (empties (brd g2)).

Instance WF_hex_later : WellFounded later.
Proof.
  unfold later.
  apply Relations.wf_inverse_image, Nat.lt_wf_0.
Defined.

Lemma filter_length_set :
  forall (f g : cell -> bool) (l : list cell) (x : cell),
    NoDup l -> In x l -> f x = true -> g x = false ->
    (forall y, In y l -> y <> x -> f y = g y) ->
    S (length (filter g l)) = length (filter f l).
Proof.
  intros f g l x Hnd Hin Hf Hg Hother.
  induction l as [|a l IH]; [destruct Hin|].
  inversion Hnd; subst.
  destruct Hin as [Heq | Hin].
  - subst a.
    simpl; rewrite Hf, Hg; simpl.
    f_equal.
    assert (Hfl : filter g l = filter f l).
    { apply filter_ext_in; intros y Hy.
      symmetry; apply Hother; [right; auto|].
      intros ->; contradiction. }
    rewrite Hfl; auto.
  - assert (Hax : a <> x) by (intros ->; contradiction).
    assert (Ega : f a = g a) by (apply Hother; [left; auto | auto]).
    simpl; rewrite <- Ega.
    destruct (f a); simpl.
    + rewrite IH; auto.
      intros y Hy Hyx; apply Hother; [right; auto | auto].
    + apply IH; auto.
      intros y Hy Hyx; apply Hother; [right; auto | auto].
Qed.

Lemma empties_decrease :
  forall b p X,
    length b = n * n ->
    In p all_cells -> get_cell b p = None ->
    S (length (empties (set_cell b p (Some X)))) = length (empties b).
Proof.
  intros b p X Hlen Hin Hnone.
  apply in_all_cells in Hin; destruct Hin as [Hb1 Hb2].
  unfold empties.
  apply filter_length_set with (x := p).
  - apply all_cells_nodup.
  - apply in_all_cells; auto.
  - unfold emptyb; rewrite Hnone; auto.
  - unfold emptyb.
    rewrite get_set_same; auto.
    rewrite Hlen; apply idx_bound; auto.
  - intros y Hy Hyp.
    apply in_all_cells in Hy; destruct Hy as [Hy1 Hy2].
    unfold emptyb.
    rewrite get_set_other; auto.
    intros Hidx.
    apply Hyp; symmetry; apply idx_inj; auto.
Qed.

Lemma later_apply_move :
  forall g p,
    length (brd g) = n * n -> In p (moves g) ->
    later (apply_move g p) g.
Proof.
  intros g p Hlen Hp.
  apply in_moves in Hp; destruct Hp as (Hres & Hin & Hnone).
  unfold later; simpl.
  rewrite <- (empties_decrease (brd g) p (trn g)); auto.
Qed.

Instance WF_flip_game_step : WellFounded (flip game_step).
Proof.
  eapply WF_subrelation, WF_hex_later.
  intros g2 g1; inversion 1; subst.
  apply later_apply_move; auto.
Defined.

Lemma hex_next_produces_steps :
  forall g, length (brd g) = n * n -> Forall (game_step g) (hex_next g).
Proof.
  intros g Hlen; unfold hex_next.
  apply Forall_map, Forall_forall.
  intros p Hp; apply gstep; auto.
Qed.

Lemma hex_next_intrinsic :
  forall g1 : game, {l : list game | Forall (game_step g1) l}.
Proof.
  intros g1.
  destruct (Nat.eq_dec (length (brd g1)) (n * n)) as [Hlen | Hlen].
  - exists (hex_next g1).
    apply hex_next_produces_steps; auto.
  - exists []; constructor.
Defined.

(** The complete game tree; type-checking it is the finiteness proof. *)
Definition complete_tree : tree game :=
  unfold_tree (flip game_step) hex_next_intrinsic hex_init.

Theorem complete_tree_sound :
  forall g,
    In_tree g complete_tree ->
    reachable hex_next_intrinsic hex_init g.
Proof.
  apply unfold_tree_sound.
Qed.

Theorem complete_tree_complete :
  forall g,
    reachable hex_next_intrinsic hex_init g ->
    In_tree g complete_tree.
Proof.
  apply unfold_tree_complete.
Qed.

(** ** Forcing predicates via the generic Zermelo interface *)

Definition hex_amove (g : game) : bool := player_eqb (trn g) red.

Definition hex_outc (g : game) : option outcome :=
  match get_result g with
  | won_by red => Some (win true)
  | won_by blue => Some (win false)
  | draw => Some drawn
  | ongoing => None
  end.

Lemma hex_outc_ongoing :
  forall g, hex_outc g = None -> get_result g = ongoing.
Proof.
  intros g H; unfold hex_outc in H.
  destruct (get_result g) as [[]| |] eqn:E; try discriminate; auto.
Qed.

(** Hex has no draws, so the kernel's drawn outcome never arises. *)
Lemma hex_outc_not_drawn : forall g, hex_outc g <> Some drawn.
Proof.
  intros g H; unfold hex_outc in H.
  destruct (get_result g) as [[]| |] eqn:E; try discriminate.
  exact (get_result_not_draw g E).
Qed.

(** The Hex forcing predicates are instances of the generic [forces]. *)
Definition red_can_force_win (fuel : nat) (g : game) : Prop :=
  forces moves apply_move hex_amove hex_outc true fuel g.

Definition blue_can_force_win (fuel : nat) (g : game) : Prop :=
  forces moves apply_move hex_amove hex_outc false fuel g.

Lemma red_can_win_0_iff :
  forall g, red_can_force_win 0 g <-> get_result g = won_by red.
Proof.
  intros g; unfold red_can_force_win.
  rewrite (forces_0_iff moves apply_move hex_amove hex_outc true g).
  unfold hex_outc; destruct (get_result g) as [[]| |]; simpl.
  - split; auto.
  - split; discriminate.
  - split; discriminate.
  - split; [intros [] | discriminate].
Qed.

Lemma blue_can_win_0_iff :
  forall g, blue_can_force_win 0 g <-> get_result g = won_by blue.
Proof.
  intros g; unfold blue_can_force_win.
  rewrite (forces_0_iff moves apply_move hex_amove hex_outc false g).
  unfold hex_outc; destruct (get_result g) as [[]| |]; simpl.
  - split; discriminate.
  - split; auto.
  - split; discriminate.
  - split; [intros [] | discriminate].
Qed.

Lemma red_can_win_S_iff :
  forall f g,
    red_can_force_win (S f) g <->
    match get_result g with
    | won_by red => True
    | won_by blue => False
    | draw => False
    | ongoing =>
      match trn g with
      | red => exists p, In p (moves g) /\ red_can_force_win f (apply_move g p)
      | blue => forall p, In p (moves g) -> red_can_force_win f (apply_move g p)
      end
    end.
Proof.
  intros f g; unfold red_can_force_win at 1.
  rewrite (forces_S_iff moves apply_move hex_amove hex_outc true f g).
  unfold hex_outc, hex_amove.
  destruct (get_result g) as [[]| |] eqn:Eg; simpl.
  - split; auto.
  - split; [discriminate | intros []].
  - split; [discriminate | intros []].
  - destruct (trn g); simpl; apply iff_refl.
Qed.

Lemma blue_can_win_S_iff :
  forall f g,
    blue_can_force_win (S f) g <->
    match get_result g with
    | won_by blue => True
    | won_by red => False
    | draw => False
    | ongoing =>
      match trn g with
      | blue => exists p, In p (moves g) /\ blue_can_force_win f (apply_move g p)
      | red => forall p, In p (moves g) -> blue_can_force_win f (apply_move g p)
      end
    end.
Proof.
  intros f g; unfold blue_can_force_win at 1.
  rewrite (forces_S_iff moves apply_move hex_amove hex_outc false f g).
  unfold hex_outc, hex_amove.
  destruct (get_result g) as [[]| |] eqn:Eg; simpl.
  - split; [discriminate | intros []].
  - split; auto.
  - split; [discriminate | intros []].
  - destruct (trn g); simpl; apply iff_refl.
Qed.

(** ** Determinacy via the generic Zermelo theorem *)

(** Determinacy of Hex, instantiating [zermelo] on the empty-cell measure. *)
Theorem hex_determined :
  forall fuel g,
    length (brd g) = n * n ->
    length (empties (brd g)) <= fuel ->
    red_can_force_win fuel g \/ blue_can_force_win fuel g.
Proof.
  intros fuel g Hlen Hfuel.
  assert (Hinv : forall (s : game) (m : cell),
      length (brd s) = n * n -> hex_outc s = None -> In m (moves s) ->
      length (brd (apply_move s m)) = n * n)
    by (intros s m Hs _ _; rewrite apply_move_length; exact Hs).
  assert (Hmeas : forall (s : game) (m : cell),
      length (brd s) = n * n -> hex_outc s = None -> In m (moves s) ->
      length (empties (brd (apply_move s m))) < length (empties (brd s))).
  { intros s m Hs _ Hm.
    apply in_moves in Hm; destruct Hm as (Hres & Hin & Hnone).
    simpl.
    pose proof (empties_decrease (brd s) m (trn s) Hs Hin Hnone); lia. }
  assert (Hstall : forall s : game,
      length (brd s) = n * n -> hex_outc s = None ->
      exists m, In m (moves s)).
  { intros s _ Ho.
    apply moves_nonempty_of_ongoing, hex_outc_ongoing; auto. }
  destruct (zermelo moves apply_move hex_amove hex_outc
              (fun h : game => length (brd h) = n * n)
              (fun h : game => length (empties (brd h)))
              Hinv Hmeas Hstall fuel g hex_outc_not_drawn Hlen Hfuel)
    as [H | H].
  - left; exact H.
  - right; exact H.
Qed.

Theorem hex_not_both :
  forall fuel g,
    red_can_force_win fuel g -> blue_can_force_win fuel g -> False.
Proof.
  intros fuel g Hr Hb.
  exact (forces_not_both moves apply_move hex_amove hex_outc fuel g Hr Hb).
Qed.

Lemma red_can_force_win_S :
  forall fuel g, red_can_force_win fuel g -> red_can_force_win (S fuel) g.
Proof.
  intros fuel g H.
  exact (forces_S moves apply_move hex_amove hex_outc true fuel g H).
Qed.

(** ** Boolean evaluation of the forcing predicates *)

Definition red_forces_b (fuel : nat) (g : game) : bool :=
  forces_b moves apply_move hex_amove hex_outc true fuel g.

Lemma red_forces_b_correct :
  forall fuel g, red_forces_b fuel g = true <-> red_can_force_win fuel g.
Proof.
  intros fuel g.
  apply (forces_b_correct moves apply_move hex_amove hex_outc true fuel g).
Qed.

(** ** Result decompositions *)

Lemma get_result_won_red_iff :
  forall g, get_result g = won_by red <-> red_connb (brd g) = true.
Proof.
  intros g; unfold get_result.
  destruct (red_connb (brd g)); [split; auto|].
  destruct (blue_connb (brd g)); [split; discriminate|].
  destruct (fullb (brd g)); split; discriminate.
Qed.

Lemma get_result_won_blue_elim :
  forall g, get_result g = won_by blue ->
    red_connb (brd g) = false /\ blue_connb (brd g) = true.
Proof.
  intros g H; unfold get_result in H.
  destruct (red_connb (brd g)); [discriminate|].
  destruct (blue_connb (brd g)); [auto|].
  destruct (fullb (brd g)); discriminate.
Qed.

Lemma get_result_ongoing_elim :
  forall g, get_result g = ongoing ->
    red_connb (brd g) = false /\ blue_connb (brd g) = false /\
    fullb (brd g) = false.
Proof.
  intros g H; unfold get_result in H.
  destruct (red_connb (brd g)); [discriminate|].
  destruct (blue_connb (brd g)); [discriminate|].
  destruct (fullb (brd g)); [discriminate | auto].
Qed.

Lemma get_result_intro_ongoing :
  forall g,
    red_connb (brd g) = false -> blue_connb (brd g) = false ->
    fullb (brd g) = false ->
    get_result g = ongoing.
Proof.
  intros g H1 H2 H3; unfold get_result; rewrite H1, H2, H3; auto.
Qed.

(** ** Extra-stone monotonicity *)

Lemma stone_set_red :
  forall b e p,
    length b = n * n -> fst e < n -> snd e < n ->
    stone b red p -> stone (set_cell b e (Some red)) red p.
Proof.
  intros b e p Hlen He1 He2 (Hp1 & Hp2 & Hget).
  destruct (cell_eq_dec p e) as [-> | Hne].
  - repeat split; auto.
    rewrite get_set_same; auto.
    rewrite Hlen; apply idx_bound; auto.
  - repeat split; auto.
    rewrite get_set_other; auto.
    intros Hidx; apply Hne; symmetry; apply idx_inj; auto.
Qed.

Lemma stone_set_blue_back :
  forall b e p,
    length b = n * n -> fst e < n -> snd e < n ->
    stone (set_cell b e (Some red)) blue p -> stone b blue p.
Proof.
  intros b e p Hlen He1 He2 (Hp1 & Hp2 & Hget).
  destruct (cell_eq_dec p e) as [-> | Hne].
  - rewrite get_set_same in Hget; [discriminate|].
    rewrite Hlen; apply idx_bound; auto.
  - repeat split; auto.
    rewrite get_set_other in Hget; auto.
    intros Hidx; apply Hne; symmetry; apply idx_inj; auto.
Qed.

Lemma red_conn_set :
  forall b e,
    length b = n * n -> fst e < n -> snd e < n ->
    red_connected b -> red_connected (set_cell b e (Some red)).
Proof.
  intros b e Hlen He1 He2 (a & d & Ha & Hd & Hch).
  exists a, d; repeat split; auto.
  eapply chain_impl; [| |exact Hch]; auto.
  intros x Hx; apply stone_set_red; auto.
Qed.

Lemma blue_conn_set_back :
  forall b e,
    length b = n * n -> fst e < n -> snd e < n ->
    blue_connected (set_cell b e (Some red)) -> blue_connected b.
Proof.
  intros b e Hlen He1 He2 (a & d & Ha & Hd & Hch).
  exists a, d; repeat split; auto.
  eapply chain_impl; [| |exact Hch]; auto.
  intros x Hx; eapply stone_set_blue_back; eauto.
Qed.

Lemma set_nth_comm :
  forall b i j u v,
    i <> j ->
    set_nth (set_nth b i u) j v = set_nth (set_nth b j v) i u.
Proof.
  induction b as [|x b IH]; intros [|i] [|j] u v H; simpl; auto; try lia.
  f_equal; apply IH; lia.
Qed.

Lemma set_cell_comm :
  forall b p q u v,
    idx p <> idx q ->
    set_cell (set_cell b p u) q v = set_cell (set_cell b q v) p u.
Proof. intros; apply set_nth_comm; auto. Qed.

Theorem red_extra_stone :
  forall fuel g e,
    length (brd g) = n * n ->
    fst e < n -> snd e < n ->
    get_cell (brd g) e = None ->
    red_can_force_win fuel g ->
    red_can_force_win fuel (MkGame (set_cell (brd g) e (Some red)) (trn g)).
Proof.
  induction fuel as [|f IH]; intros g e Hlen He1 He2 Hnone Hwin.
  - apply (proj1 (red_can_win_0_iff g)) in Hwin.
    apply (proj2 (red_can_win_0_iff _)).
    apply (proj1 (get_result_won_red_iff g)) in Hwin.
    apply (proj2 (get_result_won_red_iff _)); simpl.
    apply red_connb_true_iff, red_conn_set; auto.
    apply red_connb_true_iff; auto.
  - apply (proj1 (red_can_win_S_iff f g)) in Hwin.
    apply (proj2 (red_can_win_S_iff f _)).
    destruct (get_result g) as [[]| |] eqn:Eg; try contradiction.
    + (* g already won by red *)
      apply (proj1 (get_result_won_red_iff g)) in Eg.
      assert (Er : get_result (MkGame (set_cell (brd g) e (Some red)) (trn g))
                   = won_by red).
      { apply (proj2 (get_result_won_red_iff _)); simpl.
        apply red_connb_true_iff, red_conn_set; auto.
        apply red_connb_true_iff; auto. }
      rewrite Er; auto.
    + (* g ongoing *)
      destruct (get_result (MkGame (set_cell (brd g) e (Some red)) (trn g)))
        as [[]| |] eqn:Eg'; auto.
      * (* extra stone cannot make blue win *)
        exfalso.
        apply get_result_won_blue_elim in Eg'; simpl in Eg'.
        destruct Eg' as [_ Hbc].
        apply blue_connb_true_iff in Hbc.
        apply blue_conn_set_back in Hbc; auto.
        apply blue_connb_true_iff in Hbc.
        apply get_result_ongoing_elim in Eg.
        destruct Eg as (_ & Hb2 & _); congruence.
      * (* no draws *)
        exfalso; eapply get_result_not_draw; eauto.
      * (* both ongoing: simulate *)
        simpl.
        destruct (trn g) eqn:Et.
        -- (* red to move *)
           destruct Hwin as [y [Hy Hwin]].
           destruct (cell_eq_dec y e) as [-> | Hne].
           ++ (* the strategy plays the extra stone's cell: play anywhere *)
              destruct (moves_nonempty_of_ongoing _ Eg') as [z Hz].
              exists z; split; auto.
              pose proof Hz as Hz'.
              apply in_moves in Hz'; destruct Hz' as (_ & Hzall & Hznone).
              simpl in Hznone.
              apply in_all_cells in Hzall; destruct Hzall as [Hz1 Hz2].
              pose proof (IH (apply_move g e) z) as IHz.
              simpl in IHz.
              rewrite Et in IHz.
              rewrite set_cell_length in IHz.
              specialize (IHz Hlen Hz1 Hz2 Hznone Hwin).
              assert (Heq :
                apply_move (MkGame (set_cell (brd g) e (Some red)) red) z
                = MkGame (set_cell (set_cell (brd g) e (Some red)) z (Some red))
                         (other red)).
              { unfold apply_move; simpl; reflexivity. }
              rewrite Heq; exact IHz.
           ++ (* replay the strategy's move *)
              exists y.
              pose proof Hy as Hy'.
              apply in_moves in Hy'; destruct Hy' as (_ & Hyall & Hynone).
              apply in_all_cells in Hyall; destruct Hyall as [Hy1 Hy2].
              assert (Hidx : idx e <> idx y).
              { intros Hidx; apply Hne; symmetry; apply idx_inj; auto. }
              split.
              ** apply in_moves; repeat split; auto.
                 --- apply in_all_cells; auto.
                 --- simpl; rewrite get_set_other; auto.
              ** pose proof (IH (apply_move g y) e) as IHy.
                 simpl in IHy.
                 rewrite Et in IHy.
                 rewrite set_cell_length in IHy.
                 rewrite get_set_other in IHy by congruence.
                 specialize (IHy Hlen He1 He2 Hnone Hwin).
                 assert (Heq :
                   apply_move (MkGame (set_cell (brd g) e (Some red)) red) y
                   = MkGame (set_cell (set_cell (brd g) y (Some red)) e
                              (Some red))
                            (other red)).
                 { unfold apply_move; simpl.
                   rewrite set_cell_comm; auto. }
                 rewrite Heq; exact IHy.
        -- (* blue to move *)
           intros p Hp.
           pose proof Hp as Hp'.
           apply in_moves in Hp'; destruct Hp' as (_ & Hpall & Hpnone).
           simpl in Hpnone.
           apply in_all_cells in Hpall; destruct Hpall as [Hp1 Hp2].
           assert (Hpe : p <> e).
           { intros ->.
             rewrite get_set_same in Hpnone; [discriminate|].
             rewrite Hlen; apply idx_bound; auto. }
           assert (Hidx : idx e <> idx p).
           { intros Hidx; apply Hpe; symmetry; apply idx_inj; auto. }
           assert (Hpg : In p (moves g)).
           { apply in_moves; repeat split; auto.
             - apply in_all_cells; auto.
             - rewrite get_set_other in Hpnone; auto. }
           specialize (Hwin p Hpg).
           pose proof (IH (apply_move g p) e) as IHp.
           simpl in IHp.
           rewrite Et in IHp.
           rewrite set_cell_length in IHp.
           rewrite get_set_other in IHp by congruence.
           specialize (IHp Hlen He1 He2 Hnone Hwin).
           assert (Heq :
             apply_move (MkGame (set_cell (brd g) e (Some red)) blue) p
             = MkGame (set_cell (set_cell (brd g) p (Some blue)) e
                        (Some red))
                      (other blue)).
           { unfold apply_move; simpl.
             rewrite set_cell_comm; auto. }
           rewrite Heq; exact IHp.
Qed.

(** ** The transpose-colorswap symmetry *)

Definition swapc (p : cell) : cell := (snd p, fst p).

Lemma swapc_involutive : forall p, swapc (swapc p) = p.
Proof. intros [a b]; auto. Qed.

Definition swapo (o : option player) : option player :=
  match o with None => None | Some X => Some (other X) end.

Lemma swapo_none_iff : forall o, swapo o = None <-> o = None.
Proof.
  intros [x|]; simpl; split; intros H; auto; discriminate.
Qed.

Lemma swapo_some_iff : forall o X, swapo o = Some X <-> o = Some (other X).
Proof.
  intros [x|] X; simpl; split; intros H; try discriminate.
  - inversion H; subst; rewrite other_involutive; auto.
  - inversion H; subst; simpl; rewrite other_involutive; auto.
Qed.

Definition tau_board (b : board) : board :=
  map (fun i => swapo (get_cell b (i mod n, i / n))) (seq 0 (n * n)).

Lemma tau_board_length : forall b, length (tau_board b) = n * n.
Proof. intros; unfold tau_board; rewrite length_map, length_seq; auto. Qed.

Lemma nth_error_seq_start :
  forall m start i, i < m -> nth_error (seq start m) i = Some (start + i).
Proof.
  induction m as [|m IH]; intros start i H; [lia|].
  destruct i; simpl.
  - f_equal; lia.
  - rewrite IH by lia; f_equal; lia.
Qed.

Lemma nth_map_seq :
  forall (f : nat -> option player) m i,
    i < m -> nth i (map f (seq 0 m)) None = f i.
Proof.
  intros f m i H.
  apply nth_error_nth.
  rewrite nth_error_map, nth_error_seq_start; auto.
Qed.

Lemma get_tau :
  forall b p, fst p < n -> snd p < n ->
    get_cell (tau_board b) p = swapo (get_cell b (swapc p)).
Proof.
  intros b [r c] H1 H2; simpl in *.
  unfold get_cell at 1; unfold tau_board, idx; simpl.
  rewrite nth_map_seq.
  - assert (Hmod : (r * n + c) mod n = c).
    { rewrite Nat.add_comm, Nat.Div0.mod_add.
      apply Nat.mod_small; auto. }
    assert (Hdiv : (r * n + c) / n = r) by (apply idx_div; auto).
    rewrite Hmod, Hdiv; auto.
  - apply (idx_bound (r, c)); auto.
Qed.

Definition tau (g : game) : game :=
  MkGame (tau_board (brd g)) (other (trn g)).

Lemma stone_tau_iff :
  forall b X p, fst p < n -> snd p < n ->
    (stone (tau_board b) X p <-> stone b (other X) (swapc p)).
Proof.
  intros b X p H1 H2; unfold stone, swapc; simpl.
  rewrite get_tau; auto.
  split.
  - intros (_ & _ & Hg).
    apply swapo_some_iff in Hg; auto.
  - intros (_ & _ & Hg).
    repeat split; auto.
    apply swapo_some_iff; auto.
Qed.

Lemma adjH_swap : forall p q, adjH p q -> adjH (swapc p) (swapc q).
Proof. intros [a b] [c d]; unfold adjH, swapc; simpl; lia. Qed.

Lemma red_conn_tau_iff :
  forall b, red_connected (tau_board b) <-> blue_connected b.
Proof.
  intros b; split.
  - intros (a & d & Ha & Hd & Hch).
    exists (swapc a), (swapc d).
    repeat split.
    + unfold swapc; simpl; auto.
    + unfold swapc; simpl; auto.
    + eapply chain_map with (f := swapc); [| |exact Hch].
      * intros x Hx.
        pose proof Hx as (Hx1 & Hx2 & _).
        apply (stone_tau_iff b red x Hx1 Hx2); auto.
      * intros x y HA; apply adjH_swap; auto.
  - intros (a & d & Ha & Hd & Hch).
    exists (swapc a), (swapc d).
    repeat split.
    + unfold swapc; simpl; auto.
    + unfold swapc; simpl; auto.
    + eapply chain_map with (f := swapc); [| |exact Hch].
      * intros x Hx.
        pose proof Hx as (Hx1 & Hx2 & _).
        apply (proj2 (stone_tau_iff b red (swapc x) Hx2 Hx1)).
        rewrite swapc_involutive; auto.
      * intros x y HA; apply adjH_swap; auto.
Qed.

Lemma blue_conn_tau_iff :
  forall b, blue_connected (tau_board b) <-> red_connected b.
Proof.
  intros b; split.
  - intros (a & d & Ha & Hd & Hch).
    exists (swapc a), (swapc d).
    repeat split.
    + unfold swapc; simpl; auto.
    + unfold swapc; simpl; auto.
    + eapply chain_map with (f := swapc); [| |exact Hch].
      * intros x Hx.
        pose proof Hx as (Hx1 & Hx2 & _).
        apply (stone_tau_iff b blue x Hx1 Hx2); auto.
      * intros x y HA; apply adjH_swap; auto.
  - intros (a & d & Ha & Hd & Hch).
    exists (swapc a), (swapc d).
    repeat split.
    + unfold swapc; simpl; auto.
    + unfold swapc; simpl; auto.
    + eapply chain_map with (f := swapc); [| |exact Hch].
      * intros x Hx.
        pose proof Hx as (Hx1 & Hx2 & _).
        apply (proj2 (stone_tau_iff b blue (swapc x) Hx2 Hx1)).
        rewrite swapc_involutive; auto.
      * intros x y HA; apply adjH_swap; auto.
Qed.

Lemma fullb_tau_false :
  forall b, fullb b = false -> fullb (tau_board b) = false.
Proof.
  intros b Hf.
  destruct (fullb (tau_board b)) eqn:Et; auto.
  exfalso.
  pose proof (proj1 (fullb_spec _) Et) as Hall.
  assert (Hb : fullb b = true).
  { apply (proj2 (fullb_spec b)).
    intros q Hq.
    assert (Hqb : fst q < n /\ snd q < n) by (apply in_all_cells; auto).
    destruct Hqb as [Hq1 Hq2].
    assert (Hsw : In (swapc q) all_cells)
      by (apply in_all_cells; unfold swapc; simpl; auto).
    specialize (Hall (swapc q) Hsw).
    rewrite get_tau in Hall.
    - rewrite swapc_involutive in Hall.
      intros Hqn; apply Hall.
      apply (proj2 (swapo_none_iff _)); auto.
    - unfold swapc; simpl; auto.
    - unfold swapc; simpl; auto. }
  congruence.
Qed.

Lemma get_result_tau_blue :
  forall g, get_result g = won_by blue -> get_result (tau g) = won_by red.
Proof.
  intros g H.
  apply get_result_won_blue_elim in H; destruct H as [Hr Hb].
  apply (proj2 (get_result_won_red_iff _)); simpl.
  apply red_connb_true_iff, red_conn_tau_iff.
  apply blue_connb_true_iff; auto.
Qed.

Lemma get_result_tau_ongoing :
  forall g, get_result g = ongoing -> get_result (tau g) = ongoing.
Proof.
  intros g H.
  apply get_result_ongoing_elim in H; destruct H as (Hr & Hb & Hf).
  apply get_result_intro_ongoing; simpl.
  - destruct (red_connb (tau_board (brd g))) eqn:E; auto.
    apply red_connb_true_iff in E.
    apply red_conn_tau_iff in E.
    apply blue_connb_true_iff in E; congruence.
  - destruct (blue_connb (tau_board (brd g))) eqn:E; auto.
    apply blue_connb_true_iff in E.
    apply blue_conn_tau_iff in E.
    apply red_connb_true_iff in E; congruence.
  - apply fullb_tau_false; auto.
Qed.

Lemma in_moves_tau :
  forall g p,
    get_result g = ongoing ->
    (In p (moves (tau g)) <-> In (swapc p) (moves g)).
Proof.
  intros g p Hres.
  pose proof (get_result_tau_ongoing g Hres) as Htau.
  split.
  - intros Hp; apply in_moves in Hp; destruct Hp as (_ & Hall & Hnone).
    apply in_all_cells in Hall; destruct Hall as [H1 H2].
    simpl in Hnone.
    rewrite get_tau in Hnone; auto.
    apply (proj1 (swapo_none_iff _)) in Hnone.
    apply in_moves; repeat split; auto.
    apply in_all_cells; unfold swapc; simpl; auto.
  - intros Hp; apply in_moves in Hp; destruct Hp as (_ & Hall & Hnone).
    apply in_all_cells in Hall; destruct Hall as [H1 H2].
    unfold swapc in H1, H2; simpl in H1, H2.
    apply in_moves; repeat split; auto.
    + apply in_all_cells; auto.
    + simpl; rewrite get_tau; auto.
      apply (proj2 (swapo_none_iff _)); auto.
Qed.

Lemma tau_apply_move :
  forall g y,
    length (brd g) = n * n -> fst y < n -> snd y < n ->
    tau (apply_move g y) = apply_move (tau g) (swapc y).
Proof.
  intros g y Hlen Hy1 Hy2.
  assert (Hn0 : n <> 0) by lia.
  unfold tau, apply_move; simpl.
  f_equal.
  apply nth_ext with (d := None) (d' := None).
  - rewrite tau_board_length, set_cell_length, tau_board_length; auto.
  - intros i Hi.
    rewrite tau_board_length in Hi.
    set (pi := (i / n, i mod n)).
    assert (Hpi1 : fst pi < n)
      by (unfold pi; simpl; apply Nat.Div0.div_lt_upper_bound; auto).
    assert (Hpi2 : snd pi < n)
      by (unfold pi; simpl; apply Nat.mod_upper_bound; auto).
    assert (Hidx : idx pi = i).
    { unfold pi, idx; simpl.
      rewrite (Nat.mul_comm (i / n) n).
      pose proof (Nat.div_mod i n Hn0); lia. }
    rewrite <- Hidx.
    change (get_cell (tau_board (set_cell (brd g) y (Some (trn g)))) pi
            = get_cell (set_cell (tau_board (brd g)) (swapc y)
                          (Some (other (trn g)))) pi).
    rewrite get_tau; auto.
    destruct (cell_eq_dec (swapc pi) y) as [Hey | Hney].
    + assert (Hpiy : pi = swapc y)
        by (rewrite <- (swapc_involutive pi), Hey; auto).
      rewrite Hey.
      rewrite get_set_same by (rewrite Hlen; apply idx_bound; auto).
      rewrite Hpiy.
      rewrite get_set_same
        by (rewrite tau_board_length; apply idx_bound;
            unfold swapc; simpl; auto).
      simpl; auto.
    + rewrite get_set_other.
      * rewrite get_set_other.
        -- rewrite get_tau; auto.
        -- intros HH.
           assert (Hyeq : swapc y = pi).
           { apply idx_inj; unfold swapc; simpl; auto. }
           apply Hney.
           rewrite <- Hyeq, swapc_involutive; auto.
      * intros HH; apply Hney; symmetry.
        apply idx_inj; unfold swapc; simpl; auto.
Qed.

Theorem blue_can_tau :
  forall fuel g,
    length (brd g) = n * n ->
    blue_can_force_win fuel g ->
    red_can_force_win fuel (tau g).
Proof.
  induction fuel as [|f IH]; intros g Hlen Hb.
  - apply (proj1 (blue_can_win_0_iff g)) in Hb.
    apply (proj2 (red_can_win_0_iff _)).
    apply get_result_tau_blue; auto.
  - apply (proj1 (blue_can_win_S_iff f g)) in Hb.
    apply (proj2 (red_can_win_S_iff f (tau g))).
    destruct (get_result g) as [[]| |] eqn:Eg; try contradiction.
    + rewrite (get_result_tau_blue g Eg); auto.
    + rewrite (get_result_tau_ongoing g Eg).
      change (trn (tau g)) with (other (trn g)).
      destruct (trn g) eqn:Et; simpl.
      * (* red moved in g, so blue moves in tau g *)
        intros p Hp.
        pose proof (proj1 (in_moves_tau g p Eg) Hp) as Hpg.
        pose proof Hp as Hp'.
        apply in_moves in Hp'; destruct Hp' as (_ & Hall & _).
        apply in_all_cells in Hall; destruct Hall as [H1 H2].
        specialize (Hb (swapc p) Hpg).
        pose proof (IH (apply_move g (swapc p))) as IHp.
        rewrite apply_move_length in IHp.
        specialize (IHp Hlen Hb).
        rewrite tau_apply_move in IHp; auto.
      * (* blue moved in g, so red moves in tau g *)
        destruct Hb as [y [Hy Hwin]].
        pose proof Hy as Hy'.
        apply in_moves in Hy'; destruct Hy' as (_ & Hall & _).
        apply in_all_cells in Hall; destruct Hall as [H1 H2].
        exists (swapc y); split.
        -- apply (proj2 (in_moves_tau g (swapc y) Eg)).
           rewrite swapc_involutive; auto.
        -- pose proof (IH (apply_move g y)) as IHy.
           rewrite apply_move_length in IHy.
           specialize (IHy Hlen Hwin).
           rewrite tau_apply_move in IHy; auto.
Qed.

(** * Nash's theorem *)

Lemma hex_init_length : length (brd hex_init) = n * n.
Proof. simpl; apply repeat_length. Qed.

Lemma nth_repeat_none :
  forall m i, nth i (repeat (@None player) m) None = None.
Proof.
  induction m as [|m IH]; intros [|i]; simpl; auto.
Qed.

Lemma get_repeat_none :
  forall m p, get_cell (repeat (@None player) m) p = None.
Proof. intros; unfold get_cell; apply nth_repeat_none. Qed.

Lemma all_cells_length : length all_cells = n * n.
Proof.
  pose proof (length_prod (seq 0 n) (seq 0 n)) as H.
  rewrite !length_seq in H.
  exact H.
Qed.

Lemma empties_le_all : forall b, length (empties b) <= n * n.
Proof.
  intros b; rewrite <- all_cells_length.
  apply NoDup_incl_length.
  - apply NoDup_filter, all_cells_nodup.
  - intros x Hx; apply filter_In in Hx; tauto.
Qed.

Lemma init_result_ongoing : get_result hex_init = ongoing.
Proof.
  apply get_result_intro_ongoing; simpl.
  - destruct (red_connb (repeat None (n * n))) eqn:E; auto.
    apply red_connb_true_iff in E.
    destruct E as (a & d & _ & _ & Hch).
    apply chain_good_l in Hch.
    destruct Hch as (_ & _ & Hg).
    rewrite get_repeat_none in Hg; discriminate.
  - destruct (blue_connb (repeat None (n * n))) eqn:E; auto.
    apply blue_connb_true_iff in E.
    destruct E as (a & d & _ & _ & Hch).
    apply chain_good_l in Hch.
    destruct Hch as (_ & _ & Hg).
    rewrite get_repeat_none in Hg; discriminate.
  - destruct (fullb (repeat None (n * n))) eqn:E; auto.
    pose proof (proj1 (fullb_spec _) E) as Hall.
    exfalso; apply (Hall (0, 0)).
    + apply in_all_cells; simpl; lia.
    + apply get_repeat_none.
Qed.

Lemma tau_board_empty :
  tau_board (repeat (@None player) (n * n)) = repeat (@None player) (n * n).
Proof.
  apply nth_ext with (d := None) (d' := None).
  - rewrite tau_board_length, repeat_length; auto.
  - intros i Hi.
    rewrite tau_board_length in Hi.
    unfold tau_board.
    rewrite nth_map_seq; auto.
    rewrite get_repeat_none, nth_repeat_none; auto.
Qed.

(** Nash's theorem: from the empty n x n board the first player wins. *)
Theorem hex_first_player_wins :
  red_can_force_win (S (n * n)) hex_init.
Proof.
  destruct (hex_determined (n * n) hex_init hex_init_length
              (empties_le_all _)) as [Hred | Hblue].
  - apply red_can_force_win_S; auto.
  - pose proof (blue_can_tau (n * n) hex_init hex_init_length Hblue) as Htau.
    assert (Htau_eq : tau hex_init = MkGame (repeat None (n * n)) blue).
    { unfold tau, hex_init; simpl; rewrite tau_board_empty; auto. }
    rewrite Htau_eq in Htau.
    pose proof (red_extra_stone (n * n)
                  (MkGame (repeat None (n * n)) blue) (0, 0)) as Hext.
    simpl in Hext.
    specialize (Hext (repeat_length _ _)).
    assert (H01 : (0 < n)%nat) by lia.
    specialize (Hext H01 H01 (get_repeat_none _ _) Htau).
    apply (proj2 (red_can_win_S_iff (n * n) hex_init)).
    rewrite init_result_ongoing.
    change (trn hex_init) with red.
    exists (0, 0); split.
    + apply in_moves; repeat split.
      * apply init_result_ongoing.
      * apply in_all_cells; simpl; lia.
      * apply get_repeat_none.
    + exact Hext.
Qed.

Corollary hex_first_player_wins_ex :
  exists fuel, red_can_force_win fuel hex_init.
Proof. eexists; apply hex_first_player_wins. Qed.

(** * Rex (misere Hex) *)

(** Rex is Hex under the flipped outcome map: completing a connection loses. *)

Definition rex_outc (g : game) : option outcome :=
  match get_result g with
  | won_by red => Some (win false)
  | won_by blue => Some (win true)
  | draw => Some drawn
  | ongoing => None
  end.

Lemma rex_outc_ongoing :
  forall g, rex_outc g = None -> get_result g = ongoing.
Proof.
  intros g H; unfold rex_outc in H.
  destruct (get_result g) as [[]| |] eqn:E; try discriminate; auto.
Qed.

Lemma rex_outc_not_drawn : forall g, rex_outc g <> Some drawn.
Proof.
  intros g H; unfold rex_outc in H.
  destruct (get_result g) as [[]| |] eqn:E; try discriminate.
  exact (get_result_not_draw g E).
Qed.

(** [red_can_force_rex_win fuel g]: red forces blue to connect. *)
Definition red_can_force_rex_win (fuel : nat) (g : game) : Prop :=
  forces moves apply_move hex_amove rex_outc true fuel g.

(** [blue_can_force_rex_win fuel g]: blue forces red to connect. *)
Definition blue_can_force_rex_win (fuel : nat) (g : game) : Prop :=
  forces moves apply_move hex_amove rex_outc false fuel g.

(** Determinacy of Rex, under the flipped outcome map. *)
Theorem rex_determined :
  forall fuel g,
    length (brd g) = n * n ->
    length (empties (brd g)) <= fuel ->
    red_can_force_rex_win fuel g \/ blue_can_force_rex_win fuel g.
Proof.
  intros fuel g Hlen Hfuel.
  assert (Hinv : forall (s : game) (m : cell),
      length (brd s) = n * n -> rex_outc s = None -> In m (moves s) ->
      length (brd (apply_move s m)) = n * n)
    by (intros s m Hs _ _; rewrite apply_move_length; exact Hs).
  assert (Hmeas : forall (s : game) (m : cell),
      length (brd s) = n * n -> rex_outc s = None -> In m (moves s) ->
      length (empties (brd (apply_move s m))) < length (empties (brd s))).
  { intros s m Hs _ Hm.
    apply in_moves in Hm; destruct Hm as (Hres & Hin & Hnone).
    simpl.
    pose proof (empties_decrease (brd s) m (trn s) Hs Hin Hnone); lia. }
  assert (Hstall : forall s : game,
      length (brd s) = n * n -> rex_outc s = None ->
      exists m, In m (moves s)).
  { intros s _ Ho.
    apply moves_nonempty_of_ongoing, rex_outc_ongoing; auto. }
  destruct (zermelo moves apply_move hex_amove rex_outc
              (fun h : game => length (brd h) = n * n)
              (fun h : game => length (empties (brd h)))
              Hinv Hmeas Hstall fuel g rex_outc_not_drawn Hlen Hfuel)
    as [H | H].
  - left; exact H.
  - right; exact H.
Qed.

Theorem rex_not_both :
  forall fuel g,
    red_can_force_rex_win fuel g -> blue_can_force_rex_win fuel g -> False.
Proof.
  intros fuel g Hr Hb.
  exact (forces_not_both moves apply_move hex_amove rex_outc fuel g Hr Hb).
Qed.

(** Boolean evaluation of the Rex forcing predicates. *)

Definition red_rex_forces_b (fuel : nat) (g : game) : bool :=
  forces_b moves apply_move hex_amove rex_outc true fuel g.

Definition blue_rex_forces_b (fuel : nat) (g : game) : bool :=
  forces_b moves apply_move hex_amove rex_outc false fuel g.

Lemma red_rex_forces_b_correct :
  forall fuel g,
    red_rex_forces_b fuel g = true <-> red_can_force_rex_win fuel g.
Proof.
  intros fuel g.
  apply (forces_b_correct moves apply_move hex_amove rex_outc true fuel g).
Qed.

Lemma blue_rex_forces_b_correct :
  forall fuel g,
    blue_rex_forces_b fuel g = true <-> blue_can_force_rex_win fuel g.
Proof.
  intros fuel g.
  apply (forces_b_correct moves apply_move hex_amove rex_outc false fuel g).
Qed.

(** * Alpha-beta AI *)

Definition score (g : game) : nat :=
  match get_result g with
  | won_by red => 2
  | won_by blue => 0
  | draw => 1
  | ongoing => 1
  end.

Theorem hex_eval_ab_correct :
  forall t : tree game,
    eval_ab players_le_ge score (fun _ => false) t =
    eval_val players_le_ge score t.
Proof.
  intros t; apply eval_ab_correct.
  - exact players_le_ge_strong.
  - exact players_le_ge_adversarial.
Qed.

Definition hex_conext (g : game) : Cotrees.colist game :=
  Cotrees.colist_of_list (proj1_sig (hex_next_intrinsic g)).

Lemma costep_iff_step :
  forall g1 g2,
    Cotrees.costep hex_conext g1 g2 <-> step hex_next_intrinsic g1 g2.
Proof.
  intros g1 g2. unfold Cotrees.costep, hex_conext.
  rewrite <- Cotrees.In_colist_iff_In_colist_of_list.
  reflexivity.
Qed.

(** ** The evaluation surface *)

(** One lazy alpha-beta evaluator, parameterized by the scorer. *)

(** Hex instance of the generic cotree alpha-beta correctness theorem. *)
Corollary hex_eval_ab_co_minimax :
  forall (score' : game -> nat) (depth width : nat) (ct : cotree game),
    eval_ab_co depth width players_le_ge score' (fun _ => false) ct =
    eval_val players_le_ge score' (materialize depth width ct).
Proof.
  intros.
  apply eval_ab_co_minimax.
  - exact players_le_ge_strong.
  - exact players_le_ge_adversarial.
Qed.

(** Evaluate a game by the lazy alpha-beta evaluator under [sc]. *)
Definition co_eval (depth width : nat) (sc : game -> nat) (g : game) : nat :=
  eval_ab_co depth width players_le_ge sc (fun _ => false)
    (Cotrees.unfold_cotree hex_conext g).

(** The finite prefix of the game cotree that [co_eval] traverses. *)
Definition ai_subtree (depth width : nat) (g : game) : tree game :=
  materialize depth width (Cotrees.unfold_cotree hex_conext g).

Theorem co_eval_materialize :
  forall depth width sc g,
    co_eval depth width sc g =
    eval_ab players_le_ge sc (fun _ => false) (ai_subtree depth width g).
Proof.
  intros; unfold co_eval, ai_subtree; apply eval_ab_co_correct.
Qed.

Theorem co_eval_minimax :
  forall depth width sc g,
    co_eval depth width sc g =
    eval_val players_le_ge sc (ai_subtree depth width g).
Proof.
  intros; unfold co_eval, ai_subtree; apply hex_eval_ab_co_minimax.
Qed.

Theorem ai_subtree_coreachable :
  forall depth width g g',
    In_tree g' (ai_subtree depth width g) ->
    Cotrees.coreachable hex_conext g g'.
Proof.
  intros depth width g g' Hin.
  apply Cotrees.unfold_cotree_sound.
  eapply materialize_In_cotree; eauto.
Qed.

Theorem ai_subtree_reachable :
  forall depth width g g',
    In_tree g' (ai_subtree depth width g) ->
    reachable hex_next_intrinsic g g'.
Proof.
  intros depth width g g' Hin.
  apply (ai_subtree_coreachable depth width) in Hin.
  unfold Cotrees.coreachable in Hin.
  unfold reachable.
  induction Hin.
  - apply rt_step. apply costep_iff_step. exact H.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

(** ** The connection-distance heuristic *)

(** Clamp a signed heuristic value into the interval used by alpha-beta. *)
Definition clamp_score (z : Z) : nat :=
  Z.to_nat (Z.max 0 (Z.min 1000 z)).

(** Connection-distance evaluation: compare the players' remaining deficits. *)
Definition heuristic_score (g : game) : nat :=
  match get_result g with
  | won_by red => 1000
  | won_by blue => 0
  | draw => 500
  | ongoing =>
    let rdef := Z.of_nat (n - red_rows_reached (brd g)) in
    let bdef := Z.of_nat (n - blue_cols_reached (brd g)) in
    clamp_score (500 + 50 * (bdef - rdef))%Z
  end.

(** Score a game under the connection-distance heuristic. *)
Definition co_score_game (depth width : nat) (g : game) : nat :=
  co_eval depth width heuristic_score g.

Theorem co_score_game_minimax :
  forall depth width g,
    co_score_game depth width g =
    eval_val players_le_ge heuristic_score
      (materialize depth width (Cotrees.unfold_cotree hex_conext g)).
Proof.
  intros; unfold co_score_game, co_eval; apply hex_eval_ab_co_minimax.
Qed.

(** ** Soundness of the connection deficits *)

(** A positive deficit certifies that the player cannot win from here. *)

(** A game step, by either player, only shrinks the levels reached. *)
Lemma side_levels_step_le :
  forall X proj g g',
    step hex_next_intrinsic g g' ->
    side_levels_reached X proj (brd g') <= side_levels_reached X proj (brd g).
Proof.
  intros X proj g g' Hstep.
  revert Hstep; unfold step, hex_next_intrinsic.
  destruct (Nat.eq_dec (length (brd g)) (n * n)) as [E | E];
    simpl; intros Hstep; [| contradiction].
  unfold hex_next in Hstep.
  apply in_map_iff in Hstep as [p [Hg' Hp]].
  apply in_moves in Hp; destruct Hp as (_ & Hall & Hnone).
  apply in_all_cells in Hall; destruct Hall as [H1 H2].
  subst g'; simpl.
  apply side_levels_set_le; auto.
Qed.

Lemma side_levels_reachable_le :
  forall X proj g g',
    reachable hex_next_intrinsic g g' ->
    side_levels_reached X proj (brd g') <= side_levels_reached X proj (brd g).
Proof.
  intros X proj g g' Hr; induction Hr.
  - apply side_levels_step_le; auto.
  - lia.
  - lia.
Qed.

(** A positive level deficit is final: the side cannot ever connect. *)
Theorem side_deficit_no_conn :
  forall X proj g g',
    (forall p q, adjH p q -> proj q <= S (proj p) /\ proj p <= S (proj q)) ->
    side_levels_reached X proj (brd g) < n ->
    reachable hex_next_intrinsic g g' ->
    ~ side_connected X proj (brd g').
Proof.
  intros X proj g g' Hproj Hdef Hr Hconn.
  pose proof (side_levels_reached_full X proj Hproj (brd g') Hconn) as Hfull.
  pose proof (side_levels_reachable_le X proj g g' Hr) as Hle.
  lia.
Qed.

(** A positive red row deficit is final. *)
Theorem red_deficit_sound :
  forall g g',
    red_rows_reached (brd g) < n ->
    reachable hex_next_intrinsic g g' ->
    get_result g' <> won_by red.
Proof.
  intros g g' Hdef Hr Hwin.
  apply (proj1 (get_result_won_red_iff g')) in Hwin.
  apply red_connb_true_iff in Hwin.
  exact (side_deficit_no_conn red fst g g' fst_adjH_le Hdef Hr Hwin).
Qed.

(** A positive blue column deficit is final. *)
Theorem blue_deficit_sound :
  forall g g',
    blue_cols_reached (brd g) < n ->
    reachable hex_next_intrinsic g g' ->
    get_result g' <> won_by blue.
Proof.
  intros g g' Hdef Hr Hwin.
  apply get_result_won_blue_elim in Hwin; destruct Hwin as [_ Hwin].
  apply blue_connb_true_iff in Hwin.
  exact (side_deficit_no_conn blue snd g g' snd_adjH_le Hdef Hr Hwin).
Qed.

(** ** Move choice *)

(** Compare candidate scores from the mover's perspective. *)
Definition prefers (X : player) (best cand : nat) : bool :=
  match X with
  | red => Nat.leb best cand
  | blue => Nat.leb cand best
  end.

Fixpoint choose_best_co (depth width : nat) (sc : game -> nat) (X : player)
    (best : game) (best_score : nat) (rest : list game) : game :=
  match rest with
  | [] => best
  | h :: rest' =>
    let c := co_eval depth width sc h in
    if prefers X best_score c
    then choose_best_co depth width sc X h c rest'
    else choose_best_co depth width sc X best best_score rest'
  end.

Lemma choose_best_co_in :
  forall depth width sc X rest best bs,
    In (choose_best_co depth width sc X best bs rest) (best :: rest).
Proof.
  intros depth width sc X;
    induction rest as [|h rest IH]; intros best bs; simpl.
  - left; reflexivity.
  - destruct (prefers X bs (co_eval depth width sc h)).
    + right; apply IH.
    + destruct (IH best bs) as [Hb | Hin];
        [left; auto | right; right; auto].
Qed.

(** Move choice through the evaluator, exact-score and heuristic instances. *)
Definition ai_move_gen (depth width : nat) (sc : game -> nat) (g : game)
    : option game :=
  match hex_next g with
  | [] => None
  | h :: rest =>
    Some (choose_best_co depth width sc (trn g) h
            (co_eval depth width sc h) rest)
  end.

Definition ai_move (depth width : nat) (g : game) : option game :=
  ai_move_gen depth width score g.

Definition ai_move_co (depth width : nat) (g : game) : option game :=
  ai_move_gen depth width heuristic_score g.

Lemma ai_move_gen_in_next :
  forall depth width sc g g',
    ai_move_gen depth width sc g = Some g' -> In g' (hex_next g).
Proof.
  intros depth width sc g g' H; unfold ai_move_gen in H.
  destruct (hex_next g) as [|h rest]; [discriminate|].
  inversion H; subst.
  apply choose_best_co_in.
Qed.

(** Any move the AI selects is a legal game step. *)
Theorem ai_move_gen_step :
  forall depth width sc g g',
    length (brd g) = n * n ->
    ai_move_gen depth width sc g = Some g' ->
    step hex_next_intrinsic g g'.
Proof.
  intros depth width sc g g' Hlen H.
  unfold step, hex_next_intrinsic.
  destruct (Nat.eq_dec (length (brd g)) (n * n)) as [E | E];
    simpl; [| congruence].
  eapply ai_move_gen_in_next; eauto.
Qed.

Corollary ai_move_gen_reachable :
  forall depth width sc g g',
    length (brd g) = n * n ->
    ai_move_gen depth width sc g = Some g' ->
    reachable hex_next_intrinsic g g'.
Proof.
  intros; apply rt_step; eapply ai_move_gen_step; eauto.
Qed.

End Hex.

(** * Smoke tests *)

Example hex2_red_wins :
  get_result 2 (MkGame [Some red; Some blue; Some red; Some blue] red)
  = won_by red.
Proof. vm_compute; reflexivity. Qed.

Example hex2_blue_wins :
  get_result 2 (MkGame [Some blue; Some blue; None; None] red)
  = won_by blue.
Proof. vm_compute; reflexivity. Qed.

Example hex2_ongoing :
  get_result 2 (MkGame [Some red; None; None; None] blue) = ongoing.
Proof. vm_compute; reflexivity. Qed.

(** * Solved boards *)

(** The Boolean checker exhibits explicit winning openings. *)

Theorem hex2_opening_wins :
  red_can_force_win 2 3 (apply_move 2 (hex_init 2) (1, 0)).
Proof.
  apply (proj1 (red_forces_b_correct 2 3 _)); vm_compute; reflexivity.
Qed.

Theorem hex3_center_opening_wins :
  red_can_force_win 3 8 (apply_move 3 (hex_init 3) (1, 1)).
Proof.
  apply (proj1 (red_forces_b_correct 3 8 _)); vm_compute; reflexivity.
Qed.

(** * Solved Rex boards *)

(** The parity pattern: the second player wins the odd boards. *)

Theorem rex1_second_player_wins :
  blue_can_force_rex_win 1 1 (hex_init 1).
Proof.
  apply (proj1 (blue_rex_forces_b_correct 1 1 _)); vm_compute; reflexivity.
Qed.

Theorem rex2_first_player_wins :
  red_can_force_rex_win 2 4 (hex_init 2).
Proof.
  apply (proj1 (red_rex_forces_b_correct 2 4 _)); vm_compute; reflexivity.
Qed.

Theorem rex3_second_player_wins :
  blue_can_force_rex_win 3 9 (hex_init 3).
Proof.
  apply (proj1 (blue_rex_forces_b_correct 3 9 _)); vm_compute; reflexivity.
Qed.
