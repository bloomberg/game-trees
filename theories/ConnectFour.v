(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Connect Four with provably unbeatable AI. *)

Require Import Corelib.Classes.RelationClasses.
Require Import Corelib.Program.Basics.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Uint63.
From Stdlib Require PArray.

Import ListNotations.
Import SigTNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.Relations.
Require Import GameTrees.Trees.
Require Import GameTrees.Cotrees.
Require Import GameTrees.Eval.
Require Import GameTrees.AlphaBeta.

(** Game types. *)

Inductive player : Type := red | yellow.

Record board : Type := mkbd
  { c0 : list player
  ; c1 : list player
  ; c2 : list player
  ; c3 : list player
  ; c4 : list player
  ; c5 : list player
  ; c6 : list player
  }.

Record game : Type :=
  { current_board : board
  ; next_turn : player
  }.

(** Decidable equality. *)

Lemma dec_eq_player : forall (p1 p2 : player), {p1 = p2} + {p1 <> p2}.
Proof. decide equality. Defined.

Definition player_eqb (p1 p2 : player) : bool :=
  if dec_eq_player p1 p2 then true else false.

Lemma dec_eq_list_player : forall (l1 l2 : list player), {l1 = l2} + {l1 <> l2}.
Proof. apply list_eq_dec, dec_eq_player. Defined.

Lemma dec_eq_board : forall (b1 b2 : board), {b1 = b2} + {b1 <> b2}.
Proof. decide equality; apply dec_eq_list_player. Defined.

Lemma dec_eq_game : forall (g1 g2 : game), {g1 = g2} + {g1 <> g2}.
Proof. decide equality. apply dec_eq_player. apply dec_eq_board. Defined.

(** Board access. *)

Definition get_column (b : board) (col : nat) : list player :=
  match col with
  | 0 => c0 b | 1 => c1 b | 2 => c2 b | 3 => c3 b
  | 4 => c4 b | 5 => c5 b | 6 => c6 b | _ => []
  end.

Definition get_cell (b : board) (col row : nat) : option player :=
  nth_error (get_column b col) row.

(** Win detection. *)

Definition check_line (b : board) (p : player)
    (c1 r1 c2 r2 c3 r3 c4 r4 : nat) : bool :=
  match get_cell b c1 r1, get_cell b c2 r2,
        get_cell b c3 r3, get_cell b c4 r4 with
  | Some p1, Some p2, Some p3, Some p4 =>
    if dec_eq_player p1 p then
    if dec_eq_player p2 p then
    if dec_eq_player p3 p then
    if dec_eq_player p4 p then true
    else false else false else false else false
  | _, _, _, _ => false
  end.

(** All 69 possible lines of 4 on a 7x6 board.
   Each entry: (c1, r1, c2, r2, c3, r3, c4, r4). *)
Definition all_lines : list (nat * nat * nat * nat * nat * nat * nat * nat) :=
  (* Horizontal: 6 rows x 4 starting columns = 24 *)
  (0,0, 1,0, 2,0, 3,0) :: (1,0, 2,0, 3,0, 4,0) :: (2,0, 3,0, 4,0, 5,0) :: (3,0, 4,0, 5,0, 6,0) ::
  (0,1, 1,1, 2,1, 3,1) :: (1,1, 2,1, 3,1, 4,1) :: (2,1, 3,1, 4,1, 5,1) :: (3,1, 4,1, 5,1, 6,1) ::
  (0,2, 1,2, 2,2, 3,2) :: (1,2, 2,2, 3,2, 4,2) :: (2,2, 3,2, 4,2, 5,2) :: (3,2, 4,2, 5,2, 6,2) ::
  (0,3, 1,3, 2,3, 3,3) :: (1,3, 2,3, 3,3, 4,3) :: (2,3, 3,3, 4,3, 5,3) :: (3,3, 4,3, 5,3, 6,3) ::
  (0,4, 1,4, 2,4, 3,4) :: (1,4, 2,4, 3,4, 4,4) :: (2,4, 3,4, 4,4, 5,4) :: (3,4, 4,4, 5,4, 6,4) ::
  (0,5, 1,5, 2,5, 3,5) :: (1,5, 2,5, 3,5, 4,5) :: (2,5, 3,5, 4,5, 5,5) :: (3,5, 4,5, 5,5, 6,5) ::
  (* Vertical: 7 columns x 3 starting rows = 21 *)
  (0,0, 0,1, 0,2, 0,3) :: (0,1, 0,2, 0,3, 0,4) :: (0,2, 0,3, 0,4, 0,5) ::
  (1,0, 1,1, 1,2, 1,3) :: (1,1, 1,2, 1,3, 1,4) :: (1,2, 1,3, 1,4, 1,5) ::
  (2,0, 2,1, 2,2, 2,3) :: (2,1, 2,2, 2,3, 2,4) :: (2,2, 2,3, 2,4, 2,5) ::
  (3,0, 3,1, 3,2, 3,3) :: (3,1, 3,2, 3,3, 3,4) :: (3,2, 3,3, 3,4, 3,5) ::
  (4,0, 4,1, 4,2, 4,3) :: (4,1, 4,2, 4,3, 4,4) :: (4,2, 4,3, 4,4, 4,5) ::
  (5,0, 5,1, 5,2, 5,3) :: (5,1, 5,2, 5,3, 5,4) :: (5,2, 5,3, 5,4, 5,5) ::
  (6,0, 6,1, 6,2, 6,3) :: (6,1, 6,2, 6,3, 6,4) :: (6,2, 6,3, 6,4, 6,5) ::
  (* Diagonal up-right: 4 starting cols x 3 starting rows = 12 *)
  (0,0, 1,1, 2,2, 3,3) :: (0,1, 1,2, 2,3, 3,4) :: (0,2, 1,3, 2,4, 3,5) ::
  (1,0, 2,1, 3,2, 4,3) :: (1,1, 2,2, 3,3, 4,4) :: (1,2, 2,3, 3,4, 4,5) ::
  (2,0, 3,1, 4,2, 5,3) :: (2,1, 3,2, 4,3, 5,4) :: (2,2, 3,3, 4,4, 5,5) ::
  (3,0, 4,1, 5,2, 6,3) :: (3,1, 4,2, 5,3, 6,4) :: (3,2, 4,3, 5,4, 6,5) ::
  (* Diagonal down-right: 4 starting cols x 3 starting rows = 12 *)
  (0,3, 1,2, 2,1, 3,0) :: (0,4, 1,3, 2,2, 3,1) :: (0,5, 1,4, 2,3, 3,2) ::
  (1,3, 2,2, 3,1, 4,0) :: (1,4, 2,3, 3,2, 4,1) :: (1,5, 2,4, 3,3, 4,2) ::
  (2,3, 3,2, 4,1, 5,0) :: (2,4, 3,3, 4,2, 5,1) :: (2,5, 3,4, 4,3, 5,2) ::
  (3,3, 4,2, 5,1, 6,0) :: (3,4, 4,3, 5,2, 6,1) :: (3,5, 4,4, 5,3, 6,2) ::
  [].

(** 24 horizontal + 21 vertical + 12 diagonal-up + 12 diagonal-down = 69 *)
Lemma all_lines_length : length all_lines = 69.
Proof. vm_compute. reflexivity. Qed.

(** No duplicates in the winning lines. *)

Definition line_type := (nat * nat * nat * nat * nat * nat * nat * nat)%type.

Definition line_eq_dec : forall (a b : line_type), {a = b} + {a <> b}.
Proof. unfold line_type. repeat decide equality. Defined.

Definition line_eqb (a b : line_type) : bool :=
  if line_eq_dec a b then true else false.

Fixpoint nodup_check (l : list line_type) : bool :=
  match l with
  | [] => true
  | x :: xs => negb (existsb (line_eqb x) xs) && nodup_check xs
  end.

Lemma nodup_check_NoDup : forall l, nodup_check l = true -> NoDup l.
Proof.
  induction l as [|x xs IH]; intros H; [constructor|].
  simpl in H. apply Bool.andb_true_iff in H as [H1 H2].
  constructor.
  - intro Hin. apply negb_true_iff in H1.
    assert (existsb (line_eqb x) xs = true).
    { apply existsb_exists. exists x. split; [exact Hin|].
      unfold line_eqb. destruct (line_eq_dec x x); [reflexivity|congruence]. }
    congruence.
  - exact (IH H2).
Qed.

Lemma all_lines_NoDup : NoDup all_lines.
Proof. apply nodup_check_NoDup. vm_compute. reflexivity. Qed.

(** A winning line: 4 in-bounds equally-spaced cells along one of 4 directions
   on a 7-column, 6-row board. *)
Definition is_winning_line (t : nat * nat * nat * nat * nat * nat * nat * nat)
  : Prop :=
  let '(c1, r1, c2, r2, c3, r3, c4, r4) := t in
  (* Horizontal *)
  (c1 + 3 <= 6 /\ r1 <= 5 /\
   c2 = c1+1 /\ c3 = c1+2 /\ c4 = c1+3 /\
   r2 = r1   /\ r3 = r1   /\ r4 = r1)
  \/
  (* Vertical *)
  (c1 <= 6 /\ r1 + 3 <= 5 /\
   c2 = c1   /\ c3 = c1   /\ c4 = c1 /\
   r2 = r1+1 /\ r3 = r1+2 /\ r4 = r1+3)
  \/
  (* Diagonal up-right *)
  (c1 + 3 <= 6 /\ r1 + 3 <= 5 /\
   c2 = c1+1 /\ c3 = c1+2 /\ c4 = c1+3 /\
   r2 = r1+1 /\ r3 = r1+2 /\ r4 = r1+3)
  \/
  (* Diagonal down-right *)
  (c1 + 3 <= 6 /\ r1 <= 5 /\
   c2 = c1+1 /\ c3 = c1+2 /\ c4 = c1+3 /\
   r1 = r2+1 /\ r2 = r3+1 /\ r3 = r4+1).

(** Systematic enumeration of all winning lines. *)
Definition generate_lines
  : list (nat * nat * nat * nat * nat * nat * nat * nat) :=
  flat_map (fun r => map (fun c =>
    (c, r, c+1, r, c+2, r, c+3, r)) (seq 0 4)) (seq 0 6) ++
  flat_map (fun c => map (fun r =>
    (c, r, c, r+1, c, r+2, c, r+3)) (seq 0 3)) (seq 0 7) ++
  flat_map (fun c => map (fun r =>
    (c, r, c+1, r+1, c+2, r+2, c+3, r+3)) (seq 0 3)) (seq 0 4) ++
  flat_map (fun c => map (fun r =>
    (c, r+3, c+1, r+2, c+2, r+1, c+3, r)) (seq 0 3)) (seq 0 4).

(** The systematic enumeration equals the hand-written list. *)
Lemma generate_lines_eq : generate_lines = all_lines.
Proof. vm_compute. reflexivity. Qed.

(** Every valid winning line appears in [all_lines]. *)
Theorem all_lines_complete :
  forall t, is_winning_line t -> In t all_lines.
Proof.
  intros [[[[[[[c1 r1] c2] r2] c3] r3] c4] r4] Hwl.
  rewrite <- generate_lines_eq.
  destruct Hwl as [H | [H | [H | H]]]; decompose [and] H; subst.
  - apply in_or_app; left.
    rewrite in_flat_map.
    exists r1; split; [rewrite in_seq; lia|].
    rewrite in_map_iff; exists c1; rewrite in_seq; split; [reflexivity|lia].
  - apply in_or_app; right; apply in_or_app; left.
    rewrite in_flat_map.
    exists c1; split; [rewrite in_seq; lia|].
    rewrite in_map_iff; exists r1; rewrite in_seq; split; [reflexivity|lia].
  - do 2 (apply in_or_app; right); apply in_or_app; left.
    rewrite in_flat_map.
    exists c1; split; [rewrite in_seq; lia|].
    rewrite in_map_iff; exists r1; rewrite in_seq; split; [reflexivity|lia].
  - do 3 (apply in_or_app; right).
    rewrite in_flat_map.
    exists c1; split; [rewrite in_seq; lia|].
    rewrite in_map_iff; exists r4; rewrite in_seq.
    split; [|lia].
    simpl.
    replace (((r4 + 1) + 1) + 1) with (r4 + 3) by lia.
    replace ((r4 + 1) + 1) with (r4 + 2) by lia.
    reflexivity.
Qed.

(** Boolean decision procedure for [is_winning_line]. *)
Definition is_winning_line_b (t : line_type) : bool :=
  let '(c1, r1, c2, r2, c3, r3, c4, r4) := t in
  ((c1 + 3 <=? 6) && (r1 <=? 5) &&
   (c2 =? c1+1) && (c3 =? c1+2) && (c4 =? c1+3) &&
   (r2 =? r1) && (r3 =? r1) && (r4 =? r1))
  || ((c1 <=? 6) && (r1 + 3 <=? 5) &&
      (c2 =? c1) && (c3 =? c1) && (c4 =? c1) &&
      (r2 =? r1+1) && (r3 =? r1+2) && (r4 =? r1+3))
  || ((c1 + 3 <=? 6) && (r1 + 3 <=? 5) &&
      (c2 =? c1+1) && (c3 =? c1+2) && (c4 =? c1+3) &&
      (r2 =? r1+1) && (r3 =? r1+2) && (r4 =? r1+3))
  || ((c1 + 3 <=? 6) && (r1 <=? 5) &&
      (c2 =? c1+1) && (c3 =? c1+2) && (c4 =? c1+3) &&
      (r1 =? r2+1) && (r2 =? r3+1) && (r3 =? r4+1)).

Lemma is_winning_line_reflect :
  forall t, is_winning_line_b t = true -> is_winning_line t.
Proof.
  intros [[[[[[[c1 r1] c2] r2] c3] r3] c4] r4] H.
  unfold is_winning_line_b in H. unfold is_winning_line.
  repeat match goal with
  | H0 : (_ || _)%bool = true |- _ =>
      apply Bool.orb_true_iff in H0; destruct H0 as [H0|H0]
  end;
  repeat match goal with
  | H0 : (_ && _)%bool = true |- _ =>
      apply Bool.andb_true_iff in H0; destruct H0
  end;
  repeat match goal with
  | H0 : (_ <=? _) = true |- _ => apply Nat.leb_le in H0
  | H0 : (_ =? _) = true |- _ => apply Nat.eqb_eq in H0
  end;
  [left | right; left | right; right; left | right; right; right];
  repeat split; lia.
Qed.

(** Every line in [all_lines] is a valid winning line. *)
Theorem all_lines_sound :
  forall t, In t all_lines -> is_winning_line t.
Proof.
  intros t Hin.
  apply is_winning_line_reflect.
  assert (H : forallb is_winning_line_b all_lines = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. exact (H t Hin).
Qed.

Definition has_won (b : board) (p : player) : bool :=
  existsb (fun '(c1, r1, c2, r2, c3, r3, c4, r4) =>
             check_line b p c1 r1 c2 r2 c3 r3 c4 r4)
          all_lines.

(** Result. *)

Inductive result : Type :=
| won_by : player -> result
| draw : result
| ongoing : result.

Lemma dec_eq_result : forall (r1 r2 : result), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. apply dec_eq_player. Defined.

Definition result_eqb (r1 r2 : result) : bool :=
  if dec_eq_result r1 r2 then true else false.

Definition total_pieces (b : board) : nat :=
  length (c0 b) + length (c1 b) + length (c2 b) +
  length (c3 b) + length (c4 b) + length (c5 b) + length (c6 b).

Definition get_result (g : game) : result :=
  let b := current_board g in
  if has_won b red then won_by red
  else if has_won b yellow then won_by yellow
  else if Nat.eqb (total_pieces b) 42 then draw
  else ongoing.

(** Moves. *)

Inductive move : Type :=
| col0 | col1 | col2 | col3 | col4 | col5 | col6.

Definition column_of_move (m : move) (b : board) : list player :=
  match m with
  | col0 => c0 b | col1 => c1 b | col2 => c2 b | col3 => c3 b
  | col4 => c4 b | col5 => c5 b | col6 => c6 b
  end.

Definition set_column (b : board) (m : move) (col : list player) : board :=
  match m with
  | col0 => mkbd col   (c1 b) (c2 b) (c3 b) (c4 b) (c5 b) (c6 b)
  | col1 => mkbd (c0 b) col   (c2 b) (c3 b) (c4 b) (c5 b) (c6 b)
  | col2 => mkbd (c0 b) (c1 b) col   (c3 b) (c4 b) (c5 b) (c6 b)
  | col3 => mkbd (c0 b) (c1 b) (c2 b) col   (c4 b) (c5 b) (c6 b)
  | col4 => mkbd (c0 b) (c1 b) (c2 b) (c3 b) col   (c5 b) (c6 b)
  | col5 => mkbd (c0 b) (c1 b) (c2 b) (c3 b) (c4 b) col   (c6 b)
  | col6 => mkbd (c0 b) (c1 b) (c2 b) (c3 b) (c4 b) (c5 b) col
  end.

Definition apply_move (g : game) (m : move) : game :=
  let b := current_board g in
  let turn := next_turn g in
  let col := column_of_move m b in
  {| current_board := set_column b m (col ++ [turn])
   ; next_turn := match turn with red => yellow | yellow => red end
   |}.

Lemma dec_eq_move : forall (m1 m2 : move), {m1 = m2} + {m1 <> m2}.
Proof. decide equality. Defined.

Definition move_eqb (m1 m2 : move) : bool :=
  if dec_eq_move m1 m2 then true else false.

Definition all_moves : list move :=
  [col0; col1; col2; col3; col4; col5; col6].

Definition moves (g : game) : list move :=
  match get_result g with
  | won_by _ | draw => []
  | ongoing =>
    filter (fun m => Nat.ltb (length (column_of_move m (current_board g))) 6)
           all_moves
  end.

Inductive valid_move : game -> move -> Prop :=
| valid_move_intro : forall g m,
    get_result g = ongoing ->
    length (column_of_move m (current_board g)) < 6 ->
    valid_move g m.

Lemma valid_moves : forall g, Forall (valid_move g) (moves g).
Proof.
  intros g.
  unfold moves.
  destruct (get_result g) eqn:Hres; try constructor.
  induction all_moves as [|m ms IH]; simpl; auto.
  destruct (length (column_of_move m (current_board g)) <? 6) eqn:Hlt; simpl.
  - constructor.
    + constructor; auto. apply Nat.ltb_lt; auto.
    + apply IH.
  - apply IH.
Qed.

(** Every valid move appears in [moves g]. *)
Lemma moves_complete : forall g m, valid_move g m -> In m (moves g).
Proof.
  intros g m Hv. inversion Hv; subst.
  unfold moves. rewrite H.
  rewrite filter_In. split.
  - destruct m; simpl; tauto.
  - simpl. apply Nat.ltb_lt. exact H0.
Qed.

(** Board invariant. *)

(** All columns have at most 6 pieces. *)
Definition valid_board (b : board) : Prop :=
  length (c0 b) <= 6 /\ length (c1 b) <= 6 /\ length (c2 b) <= 6 /\
  length (c3 b) <= 6 /\ length (c4 b) <= 6 /\ length (c5 b) <= 6 /\
  length (c6 b) <= 6.

Lemma valid_board_apply_move :
  forall g m,
    valid_board (current_board g) ->
    valid_move g m ->
    valid_board (current_board (apply_move g m)).
Proof.
  intros g m Hvb Hvm.
  inversion Hvm; subst.
  destruct Hvb as (V0 & V1 & V2 & V3 & V4 & V5 & V6).
  destruct m;
    unfold apply_move, valid_board;
    simpl current_board; simpl set_column;
    simpl c0; simpl c1; simpl c2; simpl c3; simpl c4; simpl c5; simpl c6;
    (simpl column_of_move in H0);
    repeat split; try (rewrite length_app; simpl; lia); assumption.
Qed.

(** Game step. *)

Inductive game_step : game -> game -> Prop :=
| gstep : forall g m,
    get_result g = ongoing ->
    valid_move g m ->
    game_step g (apply_move g m).

Definition c4_next (g : game) : list game :=
  match get_result g with
  | ongoing => map (apply_move g) (moves g)
  | _ => []
  end.

(** Well-foundedness. *)

Definition empty_slots (g : game) : nat :=
  let b := current_board g in
  (6 - length (c0 b)) + (6 - length (c1 b)) + (6 - length (c2 b)) +
  (6 - length (c3 b)) + (6 - length (c4 b)) + (6 - length (c5 b)) +
  (6 - length (c6 b)).

Definition later (g1 g2 : game) : Prop :=
  empty_slots g1 < empty_slots g2.

Instance WF_later : WellFounded later.
Proof.
  unfold later.
  apply Relations.wf_inverse_image, Nat.lt_wf_0.
Defined.

Lemma empty_slots_decrease_column :
  forall (col : list player) (p : player),
    length col < 6 ->
    6 - length (col ++ [p]) < 6 - length col.
Proof.
  intros col p H.
  rewrite length_app. simpl length. lia.
Qed.

Lemma less_empty_slots_after_apply_move :
  forall (g : game) (m : move),
    valid_move g m ->
    later (apply_move g m) g.
Proof.
  intros g m Hv.
  inversion Hv; subst.
  unfold later, empty_slots.
  destruct m;
    (unfold apply_move; simpl current_board; simpl set_column;
     simpl c0; simpl c1; simpl c2; simpl c3; simpl c4; simpl c5; simpl c6;
     simpl column_of_move in H0;
     pose proof (empty_slots_decrease_column _ (next_turn g) H0);
     lia).
Qed.

Instance WF_flip_game_step : WellFounded (flip game_step).
Proof.
  eapply WF_subrelation, WF_later.
  intros g2 g1; inversion 1.
  apply less_empty_slots_after_apply_move; auto.
Defined.

Lemma c4_next_produces_steps :
  forall g, Forall (game_step g) (c4_next g).
Proof.
  intros g.
  unfold c4_next.
  destruct (get_result g) eqn:Hres; try constructor.
  apply Forall_map.
  unfold flip.
  unfold moves. rewrite Hres.
  induction all_moves as [|m ms IH]; simpl; auto.
  destruct (Nat.ltb (length (column_of_move m (current_board g))) 6) eqn:Hlt; simpl.
  - constructor.
    + apply gstep; auto.
      apply valid_move_intro; auto.
      apply Nat.ltb_lt; auto.
    + apply IH.
  - apply IH.
Qed.

Lemma c4_next_intrinsic :
  forall g1 : game,
    {l : list game | Forall (game_step g1) l}.
Proof.
  intros g1.
  exists (c4_next g1).
  apply c4_next_produces_steps.
Defined.

Definition c4_init : game :=
  {| current_board := mkbd [] [] [] [] [] [] []
   ; next_turn := red |}.

Lemma valid_board_init : valid_board (current_board c4_init).
Proof. unfold valid_board, c4_init; simpl; lia. Qed.

(** The complete game tree. Well-typed and total, but too large to evaluate
   (~4.5 trillion nodes). The fact that this definition type-checks IS the
   finiteness proof: [tree] is inductive, so all inhabitants are finite,
   and [unfold_tree] requires a well-founded relation to terminate. *)
Definition complete_tree : tree game :=
  unfold_tree (flip game_step) c4_next_intrinsic c4_init.

(** Every game state in [complete_tree] is reachable from [c4_init]
   via valid game steps. (Soundness.) *)
Theorem complete_tree_sound :
  forall g,
    In_tree g complete_tree ->
    reachable c4_next_intrinsic c4_init g.
Proof.
  apply unfold_tree_sound.
Qed.

(** Every game state reachable from [c4_init] via valid game steps
   appears in [complete_tree]. (Completeness.) *)
Theorem complete_tree_complete :
  forall g,
    reachable c4_next_intrinsic c4_init g ->
    In_tree g complete_tree.
Proof.
  apply unfold_tree_complete.
Qed.

(** No simultaneous winners. *)

Definition other_player (p : player) : player :=
  match p with red => yellow | yellow => red end.

Lemma other_player_ne : forall p, p <> other_player p.
Proof. destruct p; discriminate. Qed.

Definition nat_of_move (m : move) : nat :=
  match m with
  | col0 => 0 | col1 => 1 | col2 => 2 | col3 => 3
  | col4 => 4 | col5 => 5 | col6 => 6
  end.

Lemma get_column_set_column :
  forall b m new_col n,
    get_column (set_column b m new_col) n =
    if Nat.eqb n (nat_of_move m) then new_col else get_column b n.
Proof. intros; destruct m, n as [|[|[|[|[|[|[|?]]]]]]]; reflexivity. Qed.

Lemma get_column_nat_of_move :
  forall b m, get_column b (nat_of_move m) = column_of_move m b.
Proof. destruct m; reflexivity. Qed.

Lemma nth_error_app_ne :
  forall (l : list player) (x q : player) (n : nat),
    nth_error (l ++ [x]) n = Some q -> q <> x -> nth_error l n = Some q.
Proof.
  induction l as [|h t IH]; intros x q [|n'] H Hne; cbn in *.
  - congruence.
  - destruct n'; discriminate.
  - exact H.
  - eapply IH; eassumption.
Qed.

(** If a cell contains player [q] in the board after a move by someone
   other than [q], then it already contained [q] before the move. *)
Lemma get_cell_apply_move_ne :
  forall g m col row q,
    q <> next_turn g ->
    get_cell (current_board (apply_move g m)) col row = Some q ->
    get_cell (current_board g) col row = Some q.
Proof.
  intros g m col row q Hne Hcell.
  unfold get_cell in *.
  unfold apply_move in Hcell. simpl current_board in Hcell.
  rewrite get_column_set_column in Hcell.
  destruct (Nat.eqb col (nat_of_move m)) eqn:E.
  - apply Nat.eqb_eq in E. subst col.
    rewrite get_column_nat_of_move.
    eapply nth_error_app_ne; eassumption.
  - exact Hcell.
Qed.

(** Extracting cell occupancy from a true [check_line]. *)
Lemma check_line_get_cell :
  forall b p c1 r1 c2 r2 c3 r3 c4 r4,
    check_line b p c1 r1 c2 r2 c3 r3 c4 r4 = true ->
    get_cell b c1 r1 = Some p /\
    get_cell b c2 r2 = Some p /\
    get_cell b c3 r3 = Some p /\
    get_cell b c4 r4 = Some p.
Proof.
  unfold check_line.
  intros b p c1 r1 c2 r2 c3 r3 c4 r4.
  destruct (get_cell b c1 r1) as [p1|]; [|discriminate].
  destruct (get_cell b c2 r2) as [p2|]; [|discriminate].
  destruct (get_cell b c3 r3) as [p3|]; [|discriminate].
  destruct (get_cell b c4 r4) as [p4|]; [|discriminate].
  destruct (dec_eq_player p1 p); [subst|discriminate].
  destruct (dec_eq_player p2 p); [subst|discriminate].
  destruct (dec_eq_player p3 p); [subst|discriminate].
  destruct (dec_eq_player p4 p); [subst|discriminate].
  auto.
Qed.

(** Reassembling [check_line] from cell occupancy. *)
Lemma check_line_from_cells :
  forall b p c1 r1 c2 r2 c3 r3 c4 r4,
    get_cell b c1 r1 = Some p ->
    get_cell b c2 r2 = Some p ->
    get_cell b c3 r3 = Some p ->
    get_cell b c4 r4 = Some p ->
    check_line b p c1 r1 c2 r2 c3 r3 c4 r4 = true.
Proof.
  intros b p c1 r1 c2 r2 c3 r3 c4 r4 H1 H2 H3 H4.
  unfold check_line. rewrite H1, H2, H3, H4.
  destruct (dec_eq_player p p) as [_|Hp]; [|contradiction Hp; reflexivity].
  destruct (dec_eq_player p p) as [_|Hp]; [|contradiction Hp; reflexivity].
  destruct (dec_eq_player p p) as [_|Hp]; [|contradiction Hp; reflexivity].
  destruct (dec_eq_player p p) as [_|Hp]; [|contradiction Hp; reflexivity].
  reflexivity.
Qed.

(** [has_won b p] is true iff there exists a valid winning line whose
   four cells all contain [p]. *)
Theorem has_won_correct :
  forall b p,
    has_won b p = true <->
    exists c1 r1 c2 r2 c3 r3 c4 r4,
      is_winning_line (c1, r1, c2, r2, c3, r3, c4, r4) /\
      get_cell b c1 r1 = Some p /\
      get_cell b c2 r2 = Some p /\
      get_cell b c3 r3 = Some p /\
      get_cell b c4 r4 = Some p.
Proof.
  intros b p. split.
  - intros Hw.
    unfold has_won in Hw.
    apply existsb_exists in Hw as [line [Hin Hck]].
    destruct line as [[[[[[[c1' r1'] c2'] r2'] c3'] r3'] c4'] r4'].
    apply check_line_get_cell in Hck as (H1 & H2 & H3 & H4).
    exists c1', r1', c2', r2', c3', r3', c4', r4'.
    split; [exact (all_lines_sound _ Hin)|auto].
  - intros (c1' & r1' & c2' & r2' & c3' & r3' & c4' & r4' & Hwl & H1 & H2 & H3 & H4).
    unfold has_won.
    apply existsb_exists.
    exists (c1', r1', c2', r2', c3', r3', c4', r4').
    split.
    + exact (all_lines_complete _ Hwl).
    + exact (check_line_from_cells b p c1' r1' c2' r2' c3' r3' c4' r4' H1 H2 H3 H4).
Qed.

Lemma ongoing_no_winner :
  forall g,
    get_result g = ongoing ->
    has_won (current_board g) red = false /\
    has_won (current_board g) yellow = false.
Proof.
  intros g H. unfold get_result in H.
  destruct (has_won (current_board g) red) eqn:Hr; [discriminate|].
  destruct (has_won (current_board g) yellow) eqn:Hy; [discriminate|].
  auto.
Qed.

(** A move by player [p] cannot create a win for [other_player p]. *)
Lemma has_won_apply_move_ne :
  forall g m,
    has_won (current_board g) (other_player (next_turn g)) = false ->
    has_won (current_board (apply_move g m))
            (other_player (next_turn g)) = false.
Proof.
  intros g m Hbefore.
  destruct (has_won (current_board (apply_move g m))
              (other_player (next_turn g))) eqn:Hafter; [|reflexivity].
  exfalso.
  unfold has_won in Hafter.
  apply existsb_exists in Hafter as [line [Hin Hcheck]].
  destruct line as [[[[[[[c1' r1'] c2'] r2'] c3'] r3'] c4'] r4'].
  apply check_line_get_cell in Hcheck as (H1 & H2 & H3 & H4).
  assert (Hne : other_player (next_turn g) <> next_turn g)
    by (destruct (next_turn g); discriminate).
  apply get_cell_apply_move_ne in H1; [|exact Hne].
  apply get_cell_apply_move_ne in H2; [|exact Hne].
  apply get_cell_apply_move_ne in H3; [|exact Hne].
  apply get_cell_apply_move_ne in H4; [|exact Hne].
  assert (has_won (current_board g) (other_player (next_turn g)) = true).
  { unfold has_won. apply existsb_exists.
    exists (c1', r1', c2', r2', c3', r3', c4', r4').
    split; [exact Hin|]. apply check_line_from_cells; assumption. }
  congruence.
Qed.

(** [c4_next_intrinsic] projects to [c4_next]. *)
Lemma c4_step_iff :
  forall g1 g2, step c4_next_intrinsic g1 g2 <-> In g2 (c4_next g1).
Proof. split; exact (fun H => H). Qed.

Lemma has_won_init_red : has_won (mkbd [] [] [] [] [] [] []) red = false.
Proof. vm_compute. reflexivity. Qed.

Lemma has_won_init_yellow : has_won (mkbd [] [] [] [] [] [] []) yellow = false.
Proof. vm_compute. reflexivity. Qed.

(** On any board reachable from the initial position, it is impossible
   for both players to have four in a row simultaneously. *)
Lemma no_simul_winners_step :
  forall g1 g2,
    has_won (current_board g1) red = false \/
    has_won (current_board g1) yellow = false ->
    step c4_next_intrinsic g1 g2 ->
    has_won (current_board g2) red = false \/
    has_won (current_board g2) yellow = false.
Proof.
  intros g1 g2 Hdis Hstep.
  rewrite c4_step_iff in Hstep.
  unfold c4_next in Hstep.
  destruct (get_result g1) eqn:Hres; try (simpl in Hstep; contradiction).
  apply ongoing_no_winner in Hres as [Hr Hy].
  apply in_map_iff in Hstep as [m [Heq _]]. subst g2.
  destruct (next_turn g1) eqn:Hturn.
  - right. change yellow with (other_player red). rewrite <- Hturn.
    apply has_won_apply_move_ne. rewrite Hturn. exact Hy.
  - left. change red with (other_player yellow). rewrite <- Hturn.
    apply has_won_apply_move_ne. rewrite Hturn. exact Hr.
Qed.

Lemma reachable_preserves_no_simul :
  forall g1 g2,
    clos_refl_trans _ (step c4_next_intrinsic) g1 g2 ->
    (has_won (current_board g1) red = false \/
     has_won (current_board g1) yellow = false) ->
    has_won (current_board g2) red = false \/
    has_won (current_board g2) yellow = false.
Proof.
  intros g1 g2 Hrt. induction Hrt; auto.
  intros Hdis. apply (no_simul_winners_step x y Hdis H).
Qed.

Lemma reachable_no_simul :
  forall g,
    reachable c4_next_intrinsic c4_init g ->
    has_won (current_board g) red = false \/
    has_won (current_board g) yellow = false.
Proof.
  intros g Hreach.
  apply (reachable_preserves_no_simul c4_init g Hreach).
  left. exact has_won_init_red.
Qed.

Theorem at_most_one_winner :
  forall g,
    reachable c4_next_intrinsic c4_init g ->
    ~ (has_won (current_board g) red = true /\
       has_won (current_board g) yellow = true).
Proof.
  intros g Hreach [Hr Hy].
  destruct (reachable_no_simul g Hreach); congruence.
Qed.

(** When empty_slots = 0, all columns have >= 6 pieces,
   so no valid moves exist and c4_next returns []. *)
Lemma c4_terminates :
  forall g,
    empty_slots g = 0 -> c4_next g = [].
Proof.
  intros g Hslots.
  unfold c4_next.
  destruct (get_result g) eqn:Hres; auto.
  (* ongoing case: show moves g = [] because all columns are full *)
  unfold moves. rewrite Hres.
  unfold empty_slots in Hslots.
  destruct (current_board g) as [l0 l1 l2 l3 l4 l5 l6].
  simpl c0 in *. simpl c1 in *. simpl c2 in *. simpl c3 in *.
  simpl c4 in *. simpl c5 in *. simpl c6 in *.
  assert (H0 : length l0 >= 6) by lia.
  assert (H1 : length l1 >= 6) by lia.
  assert (H2 : length l2 >= 6) by lia.
  assert (H3 : length l3 >= 6) by lia.
  assert (H4 : length l4 >= 6) by lia.
  assert (H5 : length l5 >= 6) by lia.
  assert (H6 : length l6 >= 6) by lia.
  simpl.
  (* Each Nat.ltb (length li) 6 = false since length li >= 6 *)
  simpl column_of_move.
  repeat match goal with
  | |- context [Nat.ltb ?n 6] =>
      let E := fresh "E" in
      destruct (Nat.ltb n 6) eqn:E;
        [apply Nat.ltb_lt in E; lia | simpl]
  end.
  auto.
Qed.

(** Depth-limited tree for execution. *)

Definition c4_conext (g : game) : Cotrees.colist game :=
  Cotrees.colist_of_list (c4_next g).

Definition search_depth : nat := 7.

Definition ai_subtree (g : game) : tree game :=
  Cotrees.tree_of_cotree search_depth
    (Cotrees.unfold_cotree c4_conext g).

Lemma In_list_of_colist :
  forall {A : Type} (n : nat) (cl : Cotrees.colist A) (x : A),
    In x (Cotrees.list_of_colist n cl) -> Cotrees.In_colist x cl.
Proof.
  induction n as [|n IH]; intros cl x Hin; simpl in Hin.
  - contradiction.
  - destruct cl as [|y ys].
    + contradiction.
    + destruct Hin as [Heq | Hin'].
      * subst. constructor.
      * constructor. exact (IH ys x Hin').
Qed.

(** Every node in a finite prefix of a [cotree] is in the [cotree]. *)
Lemma tree_of_cotree_In_cotree :
  forall {A : Type} (n : nat) (ct : Cotrees.cotree A) (a : A),
    In_tree a (Cotrees.tree_of_cotree n ct) ->
    Cotrees.In_cotree a ct.
Proof.
  induction n as [|n IH]; intros [r f] a Hin; simpl in Hin.
  - inversion Hin; subst; [constructor|]. inversion H0.
  - inversion Hin; subst; [constructor|].
    apply Cotrees.In_cochildren.
    rename H0 into Hex.
    apply Exists_exists in Hex as [t [Hin_map Hin_t]].
    apply in_map_iff in Hin_map as [ct' [Heq Hin_list]].
    subst t.
    apply Cotrees.CoExists_exists. exists ct'. split.
    + apply In_list_of_colist with (n := S n).
      change (In ct' (Cotrees.list_of_colist (S n) f)). exact Hin_list.
    + exact (IH ct' a Hin_t).
Qed.

(** [costep c4_conext] is equivalent to [step c4_next_intrinsic]. *)
Lemma costep_iff_step :
  forall g1 g2,
    Cotrees.costep c4_conext g1 g2 <-> step c4_next_intrinsic g1 g2.
Proof.
  intros g1 g2. unfold Cotrees.costep, c4_conext.
  rewrite <- Cotrees.In_colist_iff_In_colist_of_list.
  reflexivity.
Qed.

(** Every node in the depth-limited search tree is [coreachable]
   from the root in the coinductive game tree. *)
Theorem ai_subtree_coreachable :
  forall g g',
    In_tree g' (ai_subtree g) ->
    Cotrees.coreachable c4_conext g g'.
Proof.
  intros g g' Hin.
  apply Cotrees.unfold_cotree_sound.
  apply tree_of_cotree_In_cotree in Hin. exact Hin.
Qed.

(** Every node in the depth-limited search tree is reachable
   from the root via valid game steps. *)
Theorem ai_subtree_reachable :
  forall g g',
    In_tree g' (ai_subtree g) ->
    reachable c4_next_intrinsic g g'.
Proof.
  intros g g' Hin.
  apply ai_subtree_coreachable in Hin.
  unfold Cotrees.coreachable in Hin.
  unfold reachable.
  induction Hin.
  - apply rt_step. apply costep_iff_step. exact H.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

(** Scoring. *)

Definition score (g : game) : nat :=
  match get_result g with
  | won_by red => 2
  | won_by yellow => 0
  | draw => 1
  | ongoing => 1
  end.

(** Bitboard solver (inlined from MemoSolver.v). *)

Fixpoint encode_column (col : list player) (who : player)
    (base : int) (cur mask : int) : int * int :=
  match col with
  | [] => (cur, mask)
  | p :: rest =>
    let bit := Uint63.lsl 1 base in
    let mask' := Uint63.lor mask bit in
    let cur' := if dec_eq_player p who then Uint63.lor cur bit else cur in
    encode_column rest who (Uint63.add base 1) cur' mask'
  end.

Definition encode_board (b : board) (who : player) : int * int :=
  let '(c0b, m0) := encode_column (c0 b) who 0 0 0 in
  let '(c1b, m1) := encode_column (c1 b) who 7 c0b m0 in
  let '(c2b, m2) := encode_column (c2 b) who 14 c1b m1 in
  let '(c3b, m3) := encode_column (c3 b) who 21 c2b m2 in
  let '(c4b, m4) := encode_column (c4 b) who 28 c3b m3 in
  let '(c5b, m5) := encode_column (c5 b) who 35 c4b m4 in
  encode_column (c6 b) who 42 c5b m5.

Definition BOTTOM_MASK : int :=
  Uint63.lor (Uint63.lor (Uint63.lor (Uint63.lsl 1 0)
                                     (Uint63.lsl 1 7))
                         (Uint63.lor (Uint63.lsl 1 14)
                                     (Uint63.lsl 1 21)))
             (Uint63.lor (Uint63.lor (Uint63.lsl 1 28)
                                     (Uint63.lsl 1 35))
                         (Uint63.lsl 1 42)).

Definition game_key (g : game) : int :=
  let '(cur, mask) := encode_board (current_board g) (next_turn g) in
  Uint63.add (Uint63.add cur mask) BOTTOM_MASK.

Definition TT_SIZE : int := 1048576%uint63.
Definition TT_EMPTY : int := 4611686018427387903%uint63.

Definition memo := (PArray.array int * PArray.array int)%type.

Definition memo_init : memo :=
  (PArray.make TT_SIZE TT_EMPTY, PArray.make TT_SIZE 0%uint63).

Definition memo_get (m : memo) (key : int) : option int :=
  let idx := Uint63.mod key TT_SIZE in
  let stored_key := PArray.get (fst m) idx in
  if Uint63.eqb stored_key key then Some (PArray.get (snd m) idx)
  else None.

Definition memo_put (m : memo) (key : int) (val : int) : memo :=
  let idx := Uint63.mod key TT_SIZE in
  (PArray.set (fst m) idx key, PArray.set (snd m) idx val).

Definition move_order : list move := [col3; col2; col4; col1; col5; col0; col6].

Fixpoint solve_inner (fuel : nat) (depth : int) (g : game)
    (alpha beta : int) (m : memo) : int * memo :=
  match fuel with
  | O => (42%uint63, m)
  | S fuel' =>
    match get_result g with
    | won_by red => (Uint63.sub 85 depth, m)
    | won_by yellow => (depth, m)
    | draw => (42%uint63, m)
    | ongoing =>
      let key := game_key g in
      match memo_get m key with
      | Some v => (v, m)
      | None =>
        let depth' := Uint63.add depth 1 in
        let '(best, _, _, m', cut) :=
          List.fold_left
            (fun (state : int * int * int * memo * bool) mv =>
              let '(bsf, a, b, acc, pruned) := state in
              if pruned then (bsf, a, b, acc, true)
              else if Nat.ltb (length (column_of_move mv (current_board g))) 6 then
                let g' := apply_move g mv in
                let '(sc, acc') := solve_inner fuel' depth' g' a b acc in
                match next_turn g with
                | red =>
                  let nb := if Uint63.ltb bsf sc then sc else bsf in
                  let na := if Uint63.ltb a nb then nb else a in
                  (nb, na, b, acc', Uint63.leb b na)
                | yellow =>
                  let nb := if Uint63.ltb sc bsf then sc else bsf in
                  let nbe := if Uint63.ltb nb b then nb else b in
                  (nb, a, nbe, acc', Uint63.leb nbe a)
                end
              else (bsf, a, b, acc, false))
            move_order
            (match next_turn g with
             | red => (0%uint63, alpha, beta, m, false)
             | yellow => (85%uint63, alpha, beta, m, false)
             end)
        in
        let m'' := if negb cut then memo_put m' key best else m' in
        (best, m'')
      end
    end
  end.

Definition solve (g : game) : int :=
  fst (solve_inner 42 0%uint63 g 0%uint63 85%uint63 memo_init).

(** Solver-backed perfect AI. *)

Definition score_move (g : game) (m : move) : option (move * int) :=
  if Nat.ltb (length (column_of_move m (current_board g))) 6 then
    Some (m, solve (apply_move g m))
  else
    None.

Definition perfect_ai_move (g : game) : option game :=
  let scored := List.fold_right
    (fun m acc =>
      match score_move g m with
      | Some p => p :: acc
      | None => acc
      end)
    [] all_moves in
  match scored with
  | [] => None
  | (best_m, best_s) :: rest =>
    let '(final_m, _) :=
      List.fold_left
        (fun '(bm, bs) '(m, s) =>
          match next_turn g with
          | red =>
            if Uint63.ltb bs s then (m, s) else (bm, bs)
          | yellow =>
            if Uint63.ltb s bs then (m, s) else (bm, bs)
          end)
        rest (best_m, best_s) in
    Some (apply_move g final_m)
  end.

(** Correctness of alpha-beta for Connect Four. *)

Require Import ExtLib.Core.RelDec.

(** Alpha-beta pruning computes the same minimax value as the
   unpruned reference evaluator on any Connect Four subtree. *)
Theorem c4_eval_ab_correct :
  forall (t : tree game),
    eval_ab players_le_ge score (fun _ => false) t =
    eval_val players_le_ge score t.
Proof.
  intros t.
  apply eval_ab_correct.
  - exact players_le_ge_strong.
  - exact players_le_ge_adversarial.
Qed.

(** Lazy alpha-beta on cotrees. *)

(** Alpha-beta evaluation directly on cotrees. Unlike [eval_ab] which
   requires a fully materialized [tree], this version unfolds the
   [cotree] lazily as branches are visited. In [vm_compute], cofixpoints
   are only reduced on pattern match, so pruned branches are never
   constructed — making evaluation of large game trees tractable.

   [depth] bounds the tree depth (42 for Connect Four).
   [width] bounds children per node (7 for Connect Four). *)
Fixpoint eval_ab_co
    {G S : Type}
    (depth width : nat)
    (ps : players S)
    (score : G -> S)
    (cutoff : S -> bool)
    (ct : cotree G) : S :=
  match depth with
  | O => score (match ct with conode g _ => g end)
  | S depth' =>
    match ps with
    | Streams.Cons (existT _ R D) ps' =>
      match ct with
      | conode g f =>
        match f with
        | conil => score g
        | cocons first_child rest =>
          let first_val := eval_ab_co depth' width ps' score
                             (fun _ => false) first_child in
          (fix go (fuel : nat) (best : S)
               (remaining : colist (cotree G)) : S :=
            match fuel with
            | O => best
            | S fuel' =>
              match remaining with
              | conil => best
              | cocons child rest' =>
                if cutoff best then best
                else
                  let v := eval_ab_co depth' width ps' score
                             (fun s => @rel_dec _ _ D s best) child in
                  go fuel' (max2 R best v) rest'
              end
            end) width first_val rest
        end
      end
    end
  end.

(** Materialization of a cotree matching [eval_ab_co]'s traversal pattern:
   the first child is always included, and up to [width] siblings follow.
   Unlike [tree_of_cotree] which ties depth and width to a single fuel
   parameter, this keeps them independent. *)
Fixpoint materialize {A : Type} (depth width : nat) (ct : cotree A)
    : tree A :=
  match depth with
  | O => match ct with conode a _ => node a [] end
  | S depth' =>
    match ct with
    | conode a f =>
      node a (match f with
              | conil => []
              | cocons first rest =>
                materialize depth' width first ::
                map (materialize depth' width)
                    (Cotrees.list_of_colist width rest)
              end)
    end
  end.

Theorem eval_ab_co_correct :
  forall {G S : Type} (depth width : nat) (ps : players S)
         (score : G -> S) (cutoff : S -> bool) (ct : cotree G),
    eval_ab_co depth width ps score cutoff ct =
    eval_ab ps score cutoff (materialize depth width ct).
Proof.
  induction depth as [|n IH]; intros width ps score cutoff [g f].
  - destruct ps as [[R D] ps']. reflexivity.
  - destruct ps as [[R D] ps']. simpl.
    destruct f as [|first rest].
    + reflexivity.
    + rewrite IH.
      set (init := eval_ab ps' score (fun _ : S => false)
                     (materialize n width first)).
      clearbody init.
      assert (Hgo : forall fuel init0 rest0,
        (fix go (fuel0 : nat) (best : S)
             (remaining : colist (cotree G)) : S :=
          match fuel0 with
          | O => best
          | S fuel' =>
            match remaining with
            | conil => best
            | cocons child rest' =>
              if cutoff best then best
              else
                let v := eval_ab_co n width ps' score
                           (fun s => @rel_dec _ _ D s best) child in
                go fuel' (max2 R best v) rest'
            end
          end) fuel init0 rest0
        =
        (fix go (best : S) (remaining : list (tree G)) : S :=
          match remaining with
          | [] => best
          | c' :: remaining' =>
            if cutoff best then best
            else
              let v := eval_ab ps' score
                         (fun s => @rel_dec _ _ D s best) c' in
              go (max2 R best v) remaining'
          end) init0
          (map (materialize n width) (Cotrees.list_of_colist fuel rest0))).
      { induction fuel as [|f IHf]; intros init0 rest0.
        - reflexivity.
        - destruct rest0 as [|child rest'].
          + simpl. reflexivity.
          + simpl.
            destruct (cutoff init0) eqn:Ecut.
            * reflexivity.
            * rewrite IH. apply IHf. }
      apply Hgo.
Qed.

(** Alpha-beta on cotrees computes the same minimax value as the
   reference evaluator on the materialized tree. *)
Corollary eval_ab_co_minimax :
  forall (depth width : nat) (ct : cotree game),
    eval_ab_co depth width players_le_ge score (fun _ => false) ct =
    eval_val players_le_ge score (materialize depth width ct).
Proof.
  intros.
  rewrite eval_ab_co_correct.
  apply eval_ab_correct.
  - exact players_le_ge_strong.
  - exact players_le_ge_adversarial.
Qed.

(** AI. *)

Definition ai_move (g : game) : option game :=
  let t := ai_subtree g in
  let scored :=
    map (fun c => (c, eval_ab players_le_ge score (fun _ => false) c))
        (Trees.children t) in
  match max (comparing gt snd) scored with
  | None => None
  | Some (t', _) => Some (Trees.root t')
  end.

(** Threat-based reasoning. *)

(** A threat is a winning line where one player has 3 pieces
   and the 4th cell is empty but accessible (the row below
   is occupied or it is row 0). *)

Definition cell_pos : Type := (nat * nat)%type.

Record threat : Type :=
  { threat_player : player
  ; threat_line : nat * nat * nat * nat * nat * nat * nat * nat
  ; threat_empty : cell_pos
  }.

Definition line_cells (l : nat * nat * nat * nat * nat * nat * nat * nat)
  : list cell_pos :=
  let '(c1, r1, c2, r2, c3, r3, c4, r4) := l in
  [(c1, r1); (c2, r2); (c3, r3); (c4, r4)].

Definition move_of_nat (n : nat) : option move :=
  match n with
  | 0 => Some col0 | 1 => Some col1 | 2 => Some col2 | 3 => Some col3
  | 4 => Some col4 | 5 => Some col5 | 6 => Some col6 | _ => None
  end.

Lemma move_of_nat_of_move :
  forall m, move_of_nat (nat_of_move m) = Some m.
Proof. destruct m; reflexivity. Qed.

Lemma nat_of_move_of_nat :
  forall n m, move_of_nat n = Some m -> nat_of_move m = n.
Proof.
  intros n m H.
  destruct n as [|[|[|[|[|[|[|?]]]]]]]; simpl in H; try discriminate;
    injection H; intros; subst; reflexivity.
Qed.

Lemma move_of_nat_bound :
  forall n m, move_of_nat n = Some m -> n <= 6.
Proof.
  intros n m H.
  destruct n as [|[|[|[|[|[|[|?]]]]]]]; simpl in H; try discriminate; lia.
Qed.

Definition supported (b : board) (col row : nat) : Prop :=
  row = 0 \/ exists p, get_cell b col (row - 1) = Some p.

Lemma get_cell_None_length :
  forall b col row,
    get_cell b col row = None ->
    length (get_column b col) <= row.
Proof.
  unfold get_cell.
  intros b col row H.
  apply nth_error_None in H. exact H.
Qed.

Lemma get_cell_Some_length :
  forall b col row p,
    get_cell b col row = Some p ->
    row < length (get_column b col).
Proof.
  unfold get_cell.
  intros b col row p H.
  apply nth_error_Some. congruence.
Qed.

Lemma supported_empty_height :
  forall b col row,
    get_cell b col row = None ->
    supported b col row ->
    length (get_column b col) = row.
Proof.
  intros b col row Hnone Hsupp.
  apply get_cell_None_length in Hnone.
  destruct Hsupp as [H0 | [p Hsome]].
  - subst. lia.
  - apply get_cell_Some_length in Hsome. lia.
Qed.

Lemma is_winning_line_bounds :
  forall c1 r1 c2 r2 c3 r3 c4 r4,
    is_winning_line (c1, r1, c2, r2, c3, r3, c4, r4) ->
    c1 <= 6 /\ r1 <= 5 /\
    c2 <= 6 /\ r2 <= 5 /\
    c3 <= 6 /\ r3 <= 5 /\
    c4 <= 6 /\ r4 <= 5.
Proof.
  intros c1 r1 c2 r2 c3 r3 c4 r4 H.
  unfold is_winning_line in H.
  destruct H as [H | [H | [H | H]]]; decompose [and] H; lia.
Qed.

Lemma get_cell_apply_move_new :
  forall g m,
    get_cell (current_board (apply_move g m))
             (nat_of_move m)
             (length (column_of_move m (current_board g)))
    = Some (next_turn g).
Proof.
  intros g m.
  unfold get_cell, apply_move. simpl current_board.
  rewrite get_column_set_column.
  rewrite Nat.eqb_refl.
  rewrite nth_error_app2 by lia.
  rewrite Nat.sub_diag. reflexivity.
Qed.

Lemma get_cell_apply_move_other_col :
  forall g m c r,
    c <> nat_of_move m ->
    get_cell (current_board (apply_move g m)) c r =
    get_cell (current_board g) c r.
Proof.
  intros g m c r Hne.
  unfold get_cell, apply_move. simpl current_board.
  rewrite get_column_set_column.
  destruct (Nat.eqb c (nat_of_move m)) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma get_cell_apply_move_below :
  forall g m r,
    r < length (column_of_move m (current_board g)) ->
    get_cell (current_board (apply_move g m)) (nat_of_move m) r =
    get_cell (current_board g) (nat_of_move m) r.
Proof.
  intros g m r Hlt.
  unfold get_cell, apply_move. simpl current_board.
  rewrite get_column_set_column.
  rewrite Nat.eqb_refl.
  rewrite get_column_nat_of_move.
  rewrite nth_error_app1 by exact Hlt.
  reflexivity.
Qed.

Definition has_threat (b : board) (t : threat) : Prop :=
  let p := threat_player t in
  let l := threat_line t in
  let '(ec, er) := threat_empty t in
  is_winning_line l /\
  get_cell b ec er = None /\
  In (ec, er) (line_cells l) /\
  Forall (fun '(c, r) =>
    (c, r) = (ec, er) \/ get_cell b c r = Some p)
    (line_cells l).

Definition live_threat (b : board) (t : threat) : Prop :=
  has_threat b t /\
  supported b (fst (threat_empty t)) (snd (threat_empty t)).

Lemma threat_empty_in_bounds :
  forall b t,
    has_threat b t ->
    fst (threat_empty t) <= 6 /\ snd (threat_empty t) <= 5.
Proof.
  intros b t Ht.
  destruct t as [p l [ec er]]. simpl in *.
  destruct l as [[[[[[[c1 r1] c2] r2] c3] r3] c4] r4].
  destruct Ht as [Hwl [_ [Hin _]]].
  apply is_winning_line_bounds in Hwl.
  destruct Hwl as (Hc1 & Hr1 & Hc2 & Hr2 & Hc3 & Hr3 & Hc4 & Hr4).
  simpl in Hin.
  destruct Hin as [H|[H|[H|[H|F]]]]; try contradiction;
    injection H; intros; subst; simpl; lia.
Qed.

Lemma get_cell_app_preserved :
  forall (l : list player) (x : player) (r : nat),
    r < length l ->
    nth_error (l ++ [x]) r = nth_error l r.
Proof.
  intros l x r H.
  apply nth_error_app1. exact H.
Qed.

Lemma filled_above_empty_absurd :
  forall b col r1 r2 p,
    r1 > r2 ->
    get_cell b col r2 = None ->
    get_cell b col r1 = Some p ->
    False.
Proof.
  intros b col r1 r2 p Hgt Hnone Hsome.
  apply get_cell_None_length in Hnone.
  apply get_cell_Some_length in Hsome.
  lia.
Qed.

Lemma threat_cells_after_move :
  forall g ec er p m,
    nat_of_move m = ec ->
    length (column_of_move m (current_board g)) = er ->
    next_turn g = p ->
    forall c r,
      ((c, r) = (ec, er) \/ get_cell (current_board g) c r = Some p) ->
      get_cell (current_board (apply_move g m)) c r = Some p.
Proof.
  intros g ec er p m Hm Hlen Hturn c r Hor.
  destruct Hor as [Heq | Hfilled].
  - injection Heq; intros; subst.
    apply get_cell_apply_move_new.
  - destruct (Nat.eq_dec c ec) as [Hceq | Hcne].
    + subst c. rewrite <- Hm.
      rewrite get_cell_apply_move_below.
      * rewrite Hm. exact Hfilled.
      * apply get_cell_Some_length in Hfilled.
        rewrite <- Hm in Hfilled.
        rewrite get_column_nat_of_move in Hfilled.
        exact Hfilled.
    + rewrite get_cell_apply_move_other_col.
      * exact Hfilled.
      * rewrite Hm. exact Hcne.
Qed.

Lemma fill_threat_wins :
  forall g m t,
    has_threat (current_board g) t ->
    nat_of_move m = fst (threat_empty t) ->
    length (column_of_move m (current_board g)) = snd (threat_empty t) ->
    next_turn g = threat_player t ->
    has_won (current_board (apply_move g m)) (threat_player t) = true.
Proof.
  intros g m t Ht Hm Hlen Hturn.
  destruct t as [p l [ec er]]. simpl in *.
  destruct l as [[[[[[[c1 r1] c2] r2] c3] r3] c4] r4].
  destruct Ht as [Hwl [Hnone [Hin Hall]]].
  apply has_won_correct.
  exists c1, r1, c2, r2, c3, r3, c4, r4.
  split; [exact Hwl|].
  simpl in Hall.
  inversion Hall as [|? ? H1 Hall']; subst.
  inversion Hall' as [|? ? H2 Hall'']; subst.
  inversion Hall'' as [|? ? H3 Hall''']; subst.
  inversion Hall''' as [|? ? H4 _]; subst.
  repeat split;
    (eapply threat_cells_after_move; [reflexivity | reflexivity | reflexivity | assumption]).
Qed.

Lemma move_exists_for_column :
  forall col,
    col <= 6 ->
    exists m, nat_of_move m = col.
Proof.
  intros col H.
  destruct col as [|[|[|[|[|[|[|?]]]]]]]; try lia;
    [exists col0 | exists col1 | exists col2 | exists col3
    | exists col4 | exists col5 | exists col6]; reflexivity.
Qed.

Lemma get_result_won :
  forall g p,
    has_won (current_board g) p = true ->
    has_won (current_board g) (other_player p) = false ->
    get_result g = won_by p.
Proof.
  intros g p Hwon Hother.
  unfold get_result.
  destruct p; simpl in Hother; simpl other_player in Hother.
  - rewrite Hwon. reflexivity.
  - rewrite Hother. rewrite Hwon. reflexivity.
Qed.

Theorem live_threat_wins :
  forall (g : game) (t : threat),
    live_threat (current_board g) t ->
    threat_player t = next_turn g ->
    get_result g = ongoing ->
    exists m,
      valid_move g m /\
      get_result (apply_move g m) = won_by (threat_player t).
Proof.
  intros g t [Hthreat Hsupp] Hplayer Hres.
  pose proof (threat_empty_in_bounds _ _ Hthreat) as [Hcol Hrow].
  destruct (threat_empty t) as [ec er] eqn:Ete.
  simpl fst in *. simpl snd in *.
  destruct (move_exists_for_column ec Hcol) as [m Hm].
  exists m.
  assert (Hlen : length (column_of_move m (current_board g)) = er).
  { unfold has_threat in Hthreat. rewrite Ete in Hthreat.
    destruct Hthreat as [_ [Hnone _]].
    rewrite <- get_column_nat_of_move.
    rewrite Hm.
    apply supported_empty_height; [exact Hnone | exact Hsupp]. }
  assert (Hvm : valid_move g m).
  { apply valid_move_intro; [exact Hres|]. rewrite Hlen. lia. }
  split; [exact Hvm|].
  apply get_result_won.
  - eapply fill_threat_wins; eauto.
    + rewrite Ete. simpl. exact Hm.
    + rewrite Ete. simpl. exact Hlen.
  - rewrite Hplayer.
    apply has_won_apply_move_ne.
    apply ongoing_no_winner in Hres as [Hr Hy].
    destruct (next_turn g); simpl; auto.
Qed.

(** Certificate-based winning strategy. *)

Inductive cert_node : Type :=
| cert_terminal : result -> cert_node
| cert_red_move : move -> cert_node -> cert_node
| cert_yellow_all : list (move * cert_node) -> cert_node.

Fixpoint check_cert (g : game) (c : cert_node) : bool :=
  match c with
  | cert_terminal r =>
      result_eqb (get_result g) r && result_eqb r (won_by red)
  | cert_red_move m sub =>
      player_eqb (next_turn g) red &&
      result_eqb (get_result g) ongoing &&
      Nat.ltb (length (column_of_move m (current_board g))) 6 &&
      check_cert (apply_move g m) sub
  | cert_yellow_all responses =>
      player_eqb (next_turn g) yellow &&
      result_eqb (get_result g) ongoing &&
      forallb (fun m =>
        existsb (fun '(m', sub) =>
          move_eqb m m' && check_cert (apply_move g m) sub)
        responses)
      (moves g)
  end.

Inductive red_wins : game -> cert_node -> Prop :=
| rw_terminal : forall g,
    get_result g = won_by red ->
    red_wins g (cert_terminal (won_by red))
| rw_red : forall g m sub,
    next_turn g = red -> get_result g = ongoing ->
    valid_move g m -> red_wins (apply_move g m) sub ->
    red_wins g (cert_red_move m sub)
| rw_yellow : forall g responses,
    next_turn g = yellow -> get_result g = ongoing ->
    (forall m, valid_move g m ->
      exists sub, In (m, sub) responses /\
                  red_wins (apply_move g m) sub) ->
    red_wins g (cert_yellow_all responses).

Lemma player_eqb_true : forall p1 p2, player_eqb p1 p2 = true -> p1 = p2.
Proof. intros p1 p2. unfold player_eqb. destruct (dec_eq_player p1 p2); auto. discriminate. Qed.

Lemma result_eqb_true : forall r1 r2, result_eqb r1 r2 = true -> r1 = r2.
Proof. intros r1 r2. unfold result_eqb. destruct (dec_eq_result r1 r2); auto. discriminate. Qed.

Lemma move_eqb_true : forall m1 m2, move_eqb m1 m2 = true -> m1 = m2.
Proof. intros m1 m2. unfold move_eqb. destruct (dec_eq_move m1 m2); auto. discriminate. Qed.

Lemma move_eqb_refl : forall m, move_eqb m m = true.
Proof. intro m. unfold move_eqb. destruct (dec_eq_move m m); auto. Qed.

Fixpoint cert_node_ind'
  (P : cert_node -> Prop)
  (Ht : forall r, P (cert_terminal r))
  (Hr : forall m sub, P sub -> P (cert_red_move m sub))
  (Hy : forall responses,
    Forall (fun '(_, sub) => P sub) responses ->
    P (cert_yellow_all responses))
  (c : cert_node) : P c :=
  match c with
  | cert_terminal r => Ht r
  | cert_red_move m sub => Hr m sub (cert_node_ind' P Ht Hr Hy sub)
  | cert_yellow_all responses =>
      Hy responses
        ((fix go (l : list (move * cert_node))
          : Forall (fun '(_, sub) => P sub) l :=
          match l with
          | [] => Forall_nil _
          | (m, sub) :: rest =>
              Forall_cons (m, sub)
                (cert_node_ind' P Ht Hr Hy sub) (go rest)
          end) responses)
  end.

Lemma valid_move_of_ltb : forall g m,
  get_result g = ongoing ->
  Nat.ltb (length (column_of_move m (current_board g))) 6 = true ->
  valid_move g m.
Proof.
  intros g m Hres Hltb.
  apply Nat.ltb_lt in Hltb.
  exact (valid_move_intro g m Hres Hltb).
Qed.

Theorem check_cert_sound :
  forall g c, check_cert g c = true -> red_wins g c.
Proof.
  intros g c. revert g.
  induction c as [r | m sub IH | responses IH] using cert_node_ind';
    intros g Hck; simpl in Hck.
  - apply andb_true_iff in Hck as [H1 H2].
    apply result_eqb_true in H2. subst r.
    apply result_eqb_true in H1.
    constructor. exact H1.
  - destruct (player_eqb (next_turn g) red) eqn:Ep; [|discriminate].
    destruct (result_eqb (get_result g) ongoing) eqn:Er; [|simpl in Hck; discriminate].
    destruct (Nat.ltb (length (column_of_move m (current_board g))) 6) eqn:El;
      [|simpl in Hck; discriminate].
    simpl in Hck.
    apply player_eqb_true in Ep.
    apply result_eqb_true in Er.
    apply IH in Hck.
    apply valid_move_of_ltb in El; [|exact Er].
    exact (rw_red g m sub Ep Er El Hck).
  - destruct (player_eqb (next_turn g) yellow) eqn:Ep; [|discriminate].
    destruct (result_eqb (get_result g) ongoing) eqn:Er;
      [|simpl in Hck; discriminate].
    simpl in Hck.
    apply player_eqb_true in Ep.
    apply result_eqb_true in Er.
    apply rw_yellow; [exact Ep | exact Er |].
    intros mv Hvm.
    apply moves_complete in Hvm.
    rewrite forallb_forall in Hck.
    apply Hck in Hvm.
    apply existsb_exists in Hvm as [[m' sub] [Hin Hpair]].
    apply andb_true_iff in Hpair as [Hmeq Hsub].
    apply move_eqb_true in Hmeq. subst m'.
    exists sub. split; [exact Hin|].
    rewrite Forall_forall in IH.
    exact (IH (mv, sub) Hin _ Hsub).
Qed.

(** Packed certificate checker (PArray-based). *)

From Stdlib Require Import PArray ZArith.
Open Scope uint63_scope.
Open Scope array_scope.

Definition int_to_move (n : int) : move :=
  if (n =? 0)%uint63 then col0
  else if (n =? 1)%uint63 then col1
  else if (n =? 2)%uint63 then col2
  else if (n =? 3)%uint63 then col3
  else if (n =? 4)%uint63 then col4
  else if (n =? 5)%uint63 then col5
  else col6.

(** Decode cert_node from packed PArray representation.
   This is used only in the soundness proof, not in computation. *)
Fixpoint decode (data : array int) (idx : int) (fuel : nat) : cert_node :=
  match fuel with
  | O => cert_terminal ongoing
  | S fuel' =>
    let tag := data.[idx] in
    if (tag =? 0)%uint63 then
      cert_terminal (won_by red)
    else if (tag =? 1)%uint63 then
      cert_red_move
        (int_to_move (data.[(idx + 1)%uint63]))
        (decode data (data.[(idx + 2)%uint63]) fuel')
    else if (tag =? 2)%uint63 then
      cert_yellow_all
        ((fix decode_responses (off : int) (n : nat) : list (move * cert_node) :=
          match n with
          | O => []
          | S n' =>
              (int_to_move (data.[off]),
               decode data (data.[(off + 1)%uint63]) fuel')
              :: decode_responses (off + 2)%uint63 n'
          end) (idx + 2)%uint63
          (Z.to_nat (Uint63.to_Z (data.[(idx + 1)%uint63]))))
    else cert_terminal ongoing
  end.

Definition decode_responses (data : array int) (off : int) (n : nat) (fuel : nat)
  : list (move * cert_node) :=
  (fix go (o : int) (k : nat) : list (move * cert_node) :=
    match k with
    | O => []
    | S k' =>
        (int_to_move (data.[o]),
         decode data (data.[(o + 1)%uint63]) fuel)
        :: go (o + 2)%uint63 k'
    end) off n.

(* check_packed traverses the certificate DAG stored in a PArray.
   It mirrors check_cert but operates on packed data with transposition sharing. *)

(** find_response scans n entries starting at off, looking for move m *)
Definition find_response
  (chk : game -> int -> bool)
  (g : game) (data : array int) (m : move)
  (n : nat) (offset : int) : bool :=
  (fix go (i : nat) (off : int) : bool :=
    match i with
    | O => false
    | S i' =>
        if move_eqb m (int_to_move (data.[off])) then
          chk (apply_move g m) (data.[(off + 1)%uint63])
        else go i' (off + 2)%uint63
    end) n offset.

(** check_yellow iterates over remaining moves, checking each has a response *)
Definition check_yellow
  (chk : game -> int -> bool)
  (g : game) (data : array int)
  (n : nat) (offset : int) (remaining : list move) : bool :=
  (fix go (rem : list move) : bool :=
    match rem with
    | [] => true
    | m :: rest =>
        find_response chk g data m n offset && go rest
    end) remaining.

Fixpoint check_packed
  (g : game) (data : array int) (idx : int) (fuel : nat) : bool :=
  match fuel with
  | O => false
  | S fuel' =>
    let tag := data.[idx] in
    if (tag =? 0)%uint63 then
      result_eqb (get_result g) (won_by red)
    else if (tag =? 1)%uint63 then
      let m := int_to_move (data.[(idx + 1)%uint63]) in
      player_eqb (next_turn g) red &&
      result_eqb (get_result g) ongoing &&
      Nat.ltb (List.length (column_of_move m (current_board g))) 6 &&
      check_packed (apply_move g m) data (data.[(idx + 2)%uint63]) fuel'
    else if (tag =? 2)%uint63 then
      player_eqb (next_turn g) yellow &&
      result_eqb (get_result g) ongoing &&
      check_yellow (fun g' idx' => check_packed g' data idx' fuel')
        g data
        (Z.to_nat (Uint63.to_Z (data.[(idx + 1)%uint63])))
        (idx + 2)%uint63 (moves g)
    else false
  end.

(* Soundness: check_packed = true implies check_cert (decode ...) = true.
   Then check_cert_sound gives red_wins. *)

(** Unfolding lemmas for clean proofs *)
Lemma find_response_S : forall chk g data m n offset,
  find_response chk g data m (S n) offset =
  if move_eqb m (int_to_move (data.[offset])) then
    chk (apply_move g m) (data.[(offset + 1)%uint63])
  else find_response chk g data m n (offset + 2)%uint63.
Proof. reflexivity. Qed.

Lemma find_response_O : forall chk g data m offset,
  find_response chk g data m O offset = false.
Proof. reflexivity. Qed.

Lemma decode_responses_S : forall data off n fuel,
  decode_responses data off (S n) fuel =
  (int_to_move (data.[off]), decode data (data.[(off + 1)%uint63]) fuel)
    :: decode_responses data (off + 2)%uint63 n fuel.
Proof. reflexivity. Qed.

Lemma decode_responses_O : forall data off fuel,
  decode_responses data off O fuel = [].
Proof. reflexivity. Qed.

Lemma existsb_cons : forall {A} (f : A -> bool) x xs,
  existsb f (x :: xs) = (f x || existsb f xs)%bool.
Proof. reflexivity. Qed.

(** Helper: find_response succeeding implies existsb on decode_responses *)
Lemma find_response_correct :
  forall fuel' g data m n offset,
  (forall g' idx', check_packed g' data idx' fuel' = true ->
    check_cert g' (decode data idx' fuel') = true) ->
  find_response (fun g' idx' => check_packed g' data idx' fuel') g data m n offset = true ->
  existsb (fun '(m', sub) =>
    move_eqb m m' && check_cert (apply_move g m) sub)
    (decode_responses data offset n fuel') = true.
Proof.
  intros fuel' g data m.
  induction n as [|n' IHn]; intros offset IHp Hfr.
  - rewrite find_response_O in Hfr. discriminate.
  - rewrite find_response_S in Hfr.
    rewrite decode_responses_S.
    rewrite existsb_cons.
    destruct (move_eqb m (int_to_move (data.[offset]))) eqn:Hmeq.
    + apply orb_true_iff. left.
      apply andb_true_iff. split; [reflexivity | exact (IHp _ _ Hfr)].
    + apply orb_true_iff. right. exact (IHn _ IHp Hfr).
Qed.

Lemma check_yellow_cons : forall chk g data m rest n offset,
  check_yellow chk g data n offset (m :: rest) =
  find_response chk g data m n offset &&
  check_yellow chk g data n offset rest.
Proof. reflexivity. Qed.

Lemma check_yellow_nil : forall chk g data n offset,
  check_yellow chk g data n offset [] = true.
Proof. reflexivity. Qed.

(** Helper: check_yellow succeeding implies forallb over decode_responses *)
Lemma check_yellow_correct :
  forall fuel' g data n offset mvs,
  (forall g' idx', check_packed g' data idx' fuel' = true ->
    check_cert g' (decode data idx' fuel') = true) ->
  check_yellow (fun g' idx' => check_packed g' data idx' fuel')
    g data n offset mvs = true ->
  forallb (fun m =>
    existsb (fun '(m', sub) =>
      move_eqb m m' && check_cert (apply_move g m) sub)
    (decode_responses data offset n fuel'))
  mvs = true.
Proof.
  intros fuel' g data n offset mvs IHp.
  induction mvs as [|m0 rest IHmvs]; intro Hck.
  - reflexivity.
  - rewrite check_yellow_cons in Hck.
    apply andb_true_iff in Hck as [Hfr Hrest].
    simpl. apply andb_true_iff. split.
    + exact (find_response_correct _ _ _ _ _ _ IHp Hfr).
    + exact (IHmvs Hrest).
Qed.

Lemma check_packed_implies_check_cert :
  forall fuel g data idx,
  check_packed g data idx fuel = true ->
  check_cert g (decode data idx fuel) = true.
Proof.
  induction fuel as [|fuel' IH]; intros g data idx Hck.
  - simpl in Hck. discriminate.
  - simpl in Hck. simpl.
    destruct (data.[idx] =? 0)%uint63 eqn:Htag0.
    + simpl. rewrite Hck. reflexivity.
    + destruct (data.[idx] =? 1)%uint63 eqn:Htag1.
      * destruct (player_eqb (next_turn g) red) eqn:Ep; [|discriminate].
        destruct (result_eqb (get_result g) ongoing) eqn:Er; [|simpl in Hck; discriminate].
        destruct (Nat.ltb _ 6) eqn:El; [|simpl in Hck; discriminate].
        simpl in Hck. simpl.
        rewrite Ep, Er, El. simpl.
        exact (IH _ data _ Hck).
      * destruct (data.[idx] =? 2)%uint63 eqn:Htag2; [|discriminate].
        destruct (player_eqb (next_turn g) yellow) eqn:Ep; [|discriminate].
        destruct (result_eqb (get_result g) ongoing) eqn:Er; [|simpl in Hck; discriminate].
        simpl in Hck. simpl.
        rewrite Ep, Er. simpl.
        exact (check_yellow_correct _ _ _ _ _ _ (fun g' idx' => IH g' data idx') Hck).
Qed.

Theorem check_packed_sound :
  forall fuel g data idx,
  check_packed g data idx fuel = true ->
  red_wins g (decode data idx fuel).
Proof.
  intros fuel g data idx H.
  exact (check_cert_sound _ _ (check_packed_implies_check_cert _ _ _ _ H)).
Qed.

(** Certificate tests. *)

Definition test_board : board :=
  mkbd [] [] [] [red; red; red] [] [] [].

Definition test_game : game :=
  {| current_board := test_board ; next_turn := red |}.

Definition test_cert : cert_node :=
  cert_red_move col3 (cert_terminal (won_by red)).

Lemma test_check : check_cert test_game test_cert = true.
Proof. vm_compute. reflexivity. Qed.

Lemma test_red_wins : red_wins test_game test_cert.
Proof. exact (check_cert_sound _ _ test_check). Qed.

Definition test2_board : board :=
  mkbd [red; red; red] [red] [red] [] [] [] [].

Definition test2_game : game :=
  {| current_board := test2_board ; next_turn := yellow |}.

Definition test2_cert : cert_node :=
  cert_yellow_all
    [ (col0, cert_red_move col3 (cert_terminal (won_by red)))
    ; (col1, cert_red_move col3 (cert_terminal (won_by red)))
    ; (col2, cert_red_move col3 (cert_terminal (won_by red)))
    ; (col3, cert_red_move col0 (cert_terminal (won_by red)))
    ; (col4, cert_red_move col3 (cert_terminal (won_by red)))
    ; (col5, cert_red_move col3 (cert_terminal (won_by red)))
    ; (col6, cert_red_move col3 (cert_terminal (won_by red)))
    ].

Lemma test2_check : check_cert test2_game test2_cert = true.
Proof. vm_compute. reflexivity. Qed.

Lemma test2_red_wins : red_wins test2_game test2_cert.
Proof. exact (check_cert_sound _ _ test2_check). Qed.


Close Scope uint63_scope.

(** Monolith Symmetry. *)

(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(* Symmetry infrastructure for a non-bruteforce Connect Four proof route. *)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Relations.Relation_Operators.

Import ListNotations.

Require Import GameTrees.Trees.

Definition mirror_player (p : player) : player :=
  match p with red => yellow | yellow => red end.

Lemma mirror_player_involutive :
  forall p, mirror_player (mirror_player p) = p.
Proof. intros []; reflexivity. Qed.

Definition mirror_col (c : nat) : nat :=
  match c with
  | 0 => 6 | 1 => 5 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 1 | 6 => 0
  | n => n
  end.

Lemma mirror_col_involutive :
  forall c, mirror_col (mirror_col c) = c.
Proof.
  intros [|[|[|[|[|[|[|[|c]]]]]]]]; reflexivity.
Qed.

Definition mirror_move (m : move) : move :=
  match m with
  | col0 => col6 | col1 => col5 | col2 => col4 | col3 => col3
  | col4 => col2 | col5 => col1 | col6 => col0
  end.

Lemma mirror_move_involutive :
  forall m, mirror_move (mirror_move m) = m.
Proof. intros []; reflexivity. Qed.

Definition mirror_board (b : board) : board :=
  mkbd (map mirror_player (c6 b))
       (map mirror_player (c5 b))
       (map mirror_player (c4 b))
       (map mirror_player (c3 b))
       (map mirror_player (c2 b))
       (map mirror_player (c1 b))
       (map mirror_player (c0 b)).

Lemma get_column_mirror_board :
  forall b c,
    get_column (mirror_board b) (mirror_col c) =
    map mirror_player (get_column b c).
Proof.
  intros b c.
  destruct c as [|c]; simpl; [reflexivity|].
  destruct c as [|c]; simpl; [reflexivity|].
  destruct c as [|c]; simpl; [reflexivity|].
  destruct c as [|c]; simpl; [reflexivity|].
  destruct c as [|c]; simpl; [reflexivity|].
  destruct c as [|c]; simpl; [reflexivity|].
  destruct c as [|c]; simpl; [reflexivity|].
  reflexivity.
Qed.

Lemma get_cell_mirror_board :
  forall b c r,
    get_cell (mirror_board b) (mirror_col c) r =
    option_map mirror_player (get_cell b c r).
Proof.
  intros b c r.
  unfold get_cell.
  rewrite get_column_mirror_board.
  apply nth_error_map.
Qed.

Definition mirror_line (t : line_type) : line_type :=
  let '(c1, r1, c2, r2, c3, r3, c4, r4) := t in
  if Nat.eqb c1 c2 then
    (mirror_col c1, r1,
     mirror_col c2, r2,
     mirror_col c3, r3,
     mirror_col c4, r4)
  else
    (mirror_col c4, r4,
     mirror_col c3, r3,
     mirror_col c2, r2,
     mirror_col c1, r1).

Lemma line_eqb_true :
  forall a b, line_eqb a b = true -> a = b.
Proof.
  intros a b H.
  unfold line_eqb in H.
  destruct (line_eq_dec a b); auto.
  discriminate.
Qed.

Lemma line_eqb_refl :
  forall a, line_eqb a a = true.
Proof.
  intros a.
  unfold line_eqb.
  destruct (line_eq_dec a a); auto.
Qed.

Definition mirror_lines_closed_b : bool :=
  forallb (fun l => existsb (line_eqb (mirror_line l)) all_lines) all_lines.

Lemma mirror_lines_closed_b_true :
  mirror_lines_closed_b = true.
Proof. vm_compute. reflexivity. Qed.

Lemma all_lines_mirror_closed :
  forall l, In l all_lines -> In (mirror_line l) all_lines.
Proof.
  intros l Hin.
  pose proof mirror_lines_closed_b_true as Hclosed.
  unfold mirror_lines_closed_b in Hclosed.
  rewrite forallb_forall in Hclosed.
  specialize (Hclosed l Hin).
  apply existsb_exists in Hclosed.
  destruct Hclosed as [x [Hin' Heq]].
  apply line_eqb_true in Heq.
  subst x.
  exact Hin'.
Qed.

Definition mirror_lines_involutive_b : bool :=
  forallb (fun l => line_eqb (mirror_line (mirror_line l)) l) all_lines.

Lemma mirror_lines_involutive_b_true :
  mirror_lines_involutive_b = true.
Proof. vm_compute. reflexivity. Qed.

Lemma mirror_line_involutive_on_all_lines :
  forall l, In l all_lines -> mirror_line (mirror_line l) = l.
Proof.
  intros l Hin.
  pose proof mirror_lines_involutive_b_true as H.
  unfold mirror_lines_involutive_b in H.
  rewrite forallb_forall in H.
  specialize (H l Hin).
  apply line_eqb_true in H.
  exact H.
Qed.

Lemma option_map_mirror_player_some :
  forall q p,
    option_map mirror_player q = Some (mirror_player p) ->
    q = Some p.
Proof.
  intros [x|] p H; simpl in H; try discriminate.
  destruct x, p; inversion H; reflexivity.
Qed.

Lemma check_line_mirror_true_iff :
  forall b p c1 r1 c2 r2 c3 r3 c4 r4,
    check_line (mirror_board b) (mirror_player p)
      (mirror_col c4) r4
      (mirror_col c3) r3
      (mirror_col c2) r2
      (mirror_col c1) r1 = true <->
    check_line b p c1 r1 c2 r2 c3 r3 c4 r4 = true.
Proof.
  intros b p c1 r1 c2 r2 c3 r3 c4 r4.
  split; intro H.
  - apply check_line_get_cell in H as (H1 & H2 & H3 & H4).
    rewrite get_cell_mirror_board in H1.
    rewrite get_cell_mirror_board in H2.
    rewrite get_cell_mirror_board in H3.
    rewrite get_cell_mirror_board in H4.
    pose proof (option_map_mirror_player_some _ _ H1) as E4.
    pose proof (option_map_mirror_player_some _ _ H2) as E3.
    pose proof (option_map_mirror_player_some _ _ H3) as E2.
    pose proof (option_map_mirror_player_some _ _ H4) as E1.
    apply (check_line_from_cells b p c1 r1 c2 r2 c3 r3 c4 r4); assumption.
  - apply check_line_get_cell in H as (H1 & H2 & H3 & H4).
    apply (check_line_from_cells (mirror_board b) (mirror_player p)
             (mirror_col c4) r4
             (mirror_col c3) r3
             (mirror_col c2) r2
             (mirror_col c1) r1).
    + rewrite get_cell_mirror_board. now rewrite H4.
    + rewrite get_cell_mirror_board. now rewrite H3.
    + rewrite get_cell_mirror_board. now rewrite H2.
    + rewrite get_cell_mirror_board. now rewrite H1.
Qed.

Lemma check_line_mirror_norev_true_iff :
  forall b p c1 r1 c2 r2 c3 r3 c4 r4,
    check_line (mirror_board b) (mirror_player p)
      (mirror_col c1) r1
      (mirror_col c2) r2
      (mirror_col c3) r3
      (mirror_col c4) r4 = true <->
    check_line b p c1 r1 c2 r2 c3 r3 c4 r4 = true.
Proof.
  intros b p c1 r1 c2 r2 c3 r3 c4 r4.
  split; intro H.
  - apply check_line_get_cell in H as (H1 & H2 & H3 & H4).
    rewrite get_cell_mirror_board in H1.
    rewrite get_cell_mirror_board in H2.
    rewrite get_cell_mirror_board in H3.
    rewrite get_cell_mirror_board in H4.
    pose proof (option_map_mirror_player_some _ _ H1) as E1.
    pose proof (option_map_mirror_player_some _ _ H2) as E2.
    pose proof (option_map_mirror_player_some _ _ H3) as E3.
    pose proof (option_map_mirror_player_some _ _ H4) as E4.
    apply (check_line_from_cells b p c1 r1 c2 r2 c3 r3 c4 r4); assumption.
  - apply check_line_get_cell in H as (H1 & H2 & H3 & H4).
    apply (check_line_from_cells (mirror_board b) (mirror_player p)
             (mirror_col c1) r1
             (mirror_col c2) r2
             (mirror_col c3) r3
             (mirror_col c4) r4).
    + rewrite get_cell_mirror_board. now rewrite H1.
    + rewrite get_cell_mirror_board. now rewrite H2.
    + rewrite get_cell_mirror_board. now rewrite H3.
    + rewrite get_cell_mirror_board. now rewrite H4.
Qed.

Lemma check_line_mirror_line_true_iff :
  forall b p l,
    let '(c1, r1, c2, r2, c3, r3, c4, r4) := l in
    check_line (mirror_board b) (mirror_player p)
      (let '(a1, b1, a2, b2, a3, b3, a4, b4) := mirror_line l in a1) 
      (let '(a1, b1, a2, b2, a3, b3, a4, b4) := mirror_line l in b1)
      (let '(a1, b1, a2, b2, a3, b3, a4, b4) := mirror_line l in a2)
      (let '(a1, b1, a2, b2, a3, b3, a4, b4) := mirror_line l in b2)
      (let '(a1, b1, a2, b2, a3, b3, a4, b4) := mirror_line l in a3)
      (let '(a1, b1, a2, b2, a3, b3, a4, b4) := mirror_line l in b3)
      (let '(a1, b1, a2, b2, a3, b3, a4, b4) := mirror_line l in a4)
      (let '(a1, b1, a2, b2, a3, b3, a4, b4) := mirror_line l in b4) = true <->
    check_line b p c1 r1 c2 r2 c3 r3 c4 r4 = true.
Proof.
  intros b p [[[[[[[c1 r1] c2] r2] c3] r3] c4] r4].
  unfold mirror_line.
  destruct (Nat.eqb c1 c2) eqn:E; simpl.
  - apply check_line_mirror_norev_true_iff.
  - apply check_line_mirror_true_iff.
Qed.

Lemma map_mirror_player_involutive :
  forall l : list player,
    map mirror_player (map mirror_player l) = l.
Proof.
  intro l.
  rewrite map_map.
  rewrite <- map_id.
  apply map_ext; intro x.
  apply mirror_player_involutive.
Qed.

Lemma mirror_board_involutive :
  forall b, mirror_board (mirror_board b) = b.
Proof.
  intros [c0 c1 c2 c3 c4 c5 c6].
  unfold mirror_board; simpl.
  repeat rewrite map_mirror_player_involutive.
  reflexivity.
Qed.

Lemma has_won_mirror_left :
  forall b p,
    has_won (mirror_board b) (mirror_player p) = true ->
    has_won b p = true.
Proof.
  intros b p H.
  unfold has_won in *.
  apply existsb_exists in H.
  destruct H as [l [Hin Hline]].
  destruct l as [[[[[[[c1 r1] c2] r2] c3] r3] c4] r4].
  assert (Hin_m : In (mirror_line (c1, r1, c2, r2, c3, r3, c4, r4)) all_lines).
  { apply all_lines_mirror_closed. exact Hin. }
  apply existsb_exists.
  exists (mirror_line (c1, r1, c2, r2, c3, r3, c4, r4)).
  split; [exact Hin_m|].
  unfold mirror_line.
  destruct (Nat.eqb c1 c2) eqn:E; simpl.
  - pose proof (check_line_mirror_norev_true_iff b p
                  (mirror_col c1) r1
                  (mirror_col c2) r2
                  (mirror_col c3) r3
                  (mirror_col c4) r4) as Hn.
    apply (proj1 Hn).
    repeat rewrite mirror_col_involutive.
    exact Hline.
  - pose proof (check_line_mirror_true_iff b p
                  (mirror_col c4) r4
                  (mirror_col c3) r3
                  (mirror_col c2) r2
                  (mirror_col c1) r1) as Hr.
    apply (proj1 Hr).
    repeat rewrite mirror_col_involutive.
    exact Hline.
Qed.

Lemma has_won_mirror :
  forall b p,
    has_won (mirror_board b) (mirror_player p) = has_won b p.
Proof.
  intros b p.
  destruct (has_won (mirror_board b) (mirror_player p)) eqn:Hm.
  - pose proof (has_won_mirror_left b p Hm) as Hp.
    rewrite Hp. reflexivity.
  - destruct (has_won b p) eqn:Hp.
    + pose proof (has_won_mirror_left (mirror_board b) (mirror_player p)) as Hleft.
      rewrite mirror_board_involutive in Hleft.
      rewrite mirror_player_involutive in Hleft.
      specialize (Hleft Hp).
      rewrite Hm in Hleft.
      discriminate.
    + reflexivity.
Qed.

Definition mirror_game (g : game) : game :=
  {| current_board := mirror_board (current_board g)
   ; next_turn := mirror_player (next_turn g)
   |}.

Lemma mirror_game_involutive :
  forall g, mirror_game (mirror_game g) = g.
Proof.
  intros [b t].
  unfold mirror_game; simpl.
  rewrite mirror_board_involutive.
  rewrite mirror_player_involutive.
  reflexivity.
Qed.

Lemma has_won_mirror_red :
  forall b,
    has_won (mirror_board b) red = has_won b yellow.
Proof.
  intro b.
  pose proof (has_won_mirror b yellow) as H.
  simpl in H.
  exact H.
Qed.

Lemma has_won_mirror_yellow :
  forall b,
    has_won (mirror_board b) yellow = has_won b red.
Proof.
  intro b.
  pose proof (has_won_mirror b red) as H.
  simpl in H.
  exact H.
Qed.

Lemma total_pieces_mirror_board :
  forall b,
    total_pieces (mirror_board b) = total_pieces b.
Proof.
  intros [d0 d1 d2 d3 d4 d5 d6].
  unfold mirror_board, total_pieces; simpl.
  repeat rewrite length_map.
  lia.
Qed.

Lemma get_result_ongoing_mirror :
  forall g,
    get_result g = ongoing ->
    get_result (mirror_game g) = ongoing.
Proof.
  intros g Hongoing.
  unfold get_result in Hongoing.
  destruct (has_won (current_board g) red) eqn:Hr; try discriminate.
  destruct (has_won (current_board g) yellow) eqn:Hy; try discriminate.
  destruct (Nat.eqb (total_pieces (current_board g)) 42) eqn:Hfull; try discriminate.
  unfold get_result.
  unfold mirror_game.
  simpl.
  rewrite has_won_mirror_red.
  rewrite has_won_mirror_yellow.
  rewrite total_pieces_mirror_board.
  rewrite Hy, Hr, Hfull.
  reflexivity.
Qed.

Lemma get_result_mirror_game_no_simul :
  forall g,
    ~ (has_won (current_board g) red = true /\
       has_won (current_board g) yellow = true) ->
    get_result (mirror_game g) =
    match get_result g with
    | won_by red => won_by yellow
    | won_by yellow => won_by red
    | draw => draw
    | ongoing => ongoing
    end.
Proof.
  intros g Hnosimul.
  unfold get_result.
  unfold mirror_game.
  simpl.
  rewrite has_won_mirror_red.
  rewrite has_won_mirror_yellow.
  rewrite total_pieces_mirror_board.
  destruct (has_won (current_board g) red) eqn:Hr.
  - assert (Hy : has_won (current_board g) yellow = false).
    { destruct (has_won (current_board g) yellow) eqn:Hy.
      - exfalso.
        apply Hnosimul.
        split; reflexivity.
      - reflexivity. }
    rewrite Hy.
    reflexivity.
  - destruct (has_won (current_board g) yellow) eqn:Hy.
    + reflexivity.
    + destruct (Nat.eqb (total_pieces (current_board g)) 42) eqn:Hfull;
        reflexivity.
Qed.

Lemma column_of_move_mirror_board :
  forall b m,
    column_of_move (mirror_move m) (mirror_board b) =
    map mirror_player (column_of_move m b).
Proof.
  intros b m.
  destruct m; reflexivity.
Qed.

Lemma valid_move_mirror :
  forall g m,
    valid_move g m ->
    valid_move (mirror_game g) (mirror_move m).
Proof.
  intros g m Hvm.
  inversion Hvm; subst.
  constructor.
  - apply get_result_ongoing_mirror.
    exact H.
  - unfold mirror_game.
    simpl.
    rewrite column_of_move_mirror_board.
    rewrite length_map.
    exact H0.
Qed.

Lemma apply_move_mirror_game :
  forall g m,
    mirror_game (apply_move g m) =
    apply_move (mirror_game g) (mirror_move m).
Proof.
  intros [[d0 d1 d2 d3 d4 d5 d6] t] m.
  destruct m; destruct t; unfold mirror_game, mirror_board, apply_move; simpl;
    repeat rewrite map_app;
    simpl;
    reflexivity.
Qed.

Lemma in_moves_valid :
  forall g m,
    In m (moves g) ->
    valid_move g m.
Proof.
  intros g m Hin.
  pose proof (valid_moves g) as Hvs.
  rewrite Forall_forall in Hvs.
  apply Hvs.
  exact Hin.
Qed.

Lemma c4_next_mirror_left :
  forall g g',
    In g' (c4_next g) ->
    In (mirror_game g') (c4_next (mirror_game g)).
Proof.
  intros g g' Hin.
  unfold c4_next in Hin.
  destruct (get_result g) eqn:Hres; simpl in Hin;
    try contradiction.
  apply in_map_iff in Hin.
  destruct Hin as [m [Heq Hinm]].
  subst g'.
  unfold c4_next.
  rewrite get_result_ongoing_mirror by exact Hres.
  apply in_map_iff.
  exists (mirror_move m).
  split.
  - symmetry. apply apply_move_mirror_game.
  - apply moves_complete.
    apply valid_move_mirror.
    apply in_moves_valid.
    exact Hinm.
Qed.

Lemma c4_next_mirror_right :
  forall g g',
    In g' (c4_next (mirror_game g)) ->
    In (mirror_game g') (c4_next g).
Proof.
  intros g g' Hin.
  pose proof (c4_next_mirror_left (mirror_game g) g' Hin) as H.
  rewrite mirror_game_involutive in H.
  exact H.
Qed.

Lemma reachable_mirror :
  forall g0 g,
    reachable c4_next_intrinsic g0 g ->
    reachable c4_next_intrinsic (mirror_game g0) (mirror_game g).
Proof.
  intros g0 g Hreach.
  induction Hreach.
  - apply rt_step.
    apply c4_step_iff.
    apply c4_next_mirror_left.
    apply c4_step_iff in H.
    exact H.
  - apply rt_refl.
  - eapply rt_trans; eauto.
Qed.

Lemma reachable_mirror_inv :
  forall g0 g,
    reachable c4_next_intrinsic (mirror_game g0) (mirror_game g) ->
    reachable c4_next_intrinsic g0 g.
Proof.
  intros g0 g H.
  pose proof (reachable_mirror (mirror_game g0) (mirror_game g) H) as Hm.
  rewrite !mirror_game_involutive in Hm.
  exact Hm.
Qed.

(** Monolith Unbeatable. *)

(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(* A clean, book-free, depth-indexed unbeatability framework for Connect Four.
   This file avoids certificates/opening books and reasons directly
   about a minimax-style value and policy. *)

Require Import Corelib.Classes.RelationClasses.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Relations.Relation_Operators.

Import ListNotations.

Require Import GameTrees.Relations.
Require Import GameTrees.Trees.
Require Import GameTrees.Eval.
Require Import GameTrees.AlphaBeta.

Definition nat_ge (x y : nat) : Prop := Nat.le y x.

#[local] Instance Reflexive_nat_ge : Reflexive nat_ge.
Proof. unfold Reflexive, nat_ge. intro x. apply Nat.le_refl. Qed.

#[local] Instance Transitive_nat_ge : Transitive nat_ge.
Proof.
  unfold Transitive, nat_ge.
  intros x y z Hyx Hzy.
  eapply Nat.le_trans; eauto.
Qed.

#[local] Instance StronglyConnected_nat_le : StronglyConnected Nat.le.
Proof.
  unfold StronglyConnected.
  intros a b.
  destruct (Nat.le_gt_cases a b) as [Hab | Hba].
  - left; exact Hab.
  - right; apply Nat.lt_le_incl; exact Hba.
Qed.

#[local] Instance StronglyConnected_nat_ge : StronglyConnected nat_ge.
Proof.
  unfold StronglyConnected, nat_ge.
  intros a b.
  destruct (Nat.le_gt_cases b a) as [Hba | Hab].
  - left; exact Hba.
  - right; apply Nat.lt_le_incl; exact Hab.
Qed.

#[local] Instance Reflexive_comparing
  {A B : Type} (R : B -> B -> Prop) (f : A -> B)
  (Rf : Reflexive R) : Reflexive (comparing R f).
Proof.
  unfold Reflexive, comparing.
  intros x.
  apply Rf.
Qed.

#[local] Instance Transitive_comparing
  {A B : Type} (R : B -> B -> Prop) (f : A -> B)
  (Tr : Transitive R) : Transitive (comparing R f).
Proof.
  unfold Transitive, comparing.
  intros x y z Hxy Hyz.
  eapply Tr; eauto.
Qed.

#[local] Instance StronglyConnected_comparing
  {A B : Type} (R : B -> B -> Prop) (f : A -> B)
  (SC : StronglyConnected R) : StronglyConnected (comparing R f).
Proof.
  unfold StronglyConnected, comparing.
  intros x y.
  apply SC.
Qed.

Fixpoint value_fuel (fuel : nat) (g : game) : nat :=
  match fuel with
  | O => score g
  | S fuel' =>
    match get_result g with
    | ongoing =>
      let scored :=
        map (fun g' => (g', value_fuel fuel' g')) (c4_next g) in
      match next_turn g with
      | red =>
        match max (comparing Nat.le snd) scored with
        | Some (_, v) => v
        | None => score g
        end
      | yellow =>
        match max (comparing nat_ge snd) scored with
        | Some (_, v) => v
        | None => score g
        end
      end
    | _ => score g
    end
  end.

Fixpoint red_can_force_nonloss (fuel : nat) (g : game) : Prop :=
  match fuel with
  | O => get_result g <> won_by yellow
  | S fuel' =>
    match get_result g with
    | won_by yellow => False
    | won_by red => True
    | draw => True
    | ongoing =>
      match next_turn g with
      | red =>
        exists g', In g' (c4_next g) /\ red_can_force_nonloss fuel' g'
      | yellow =>
        forall g', In g' (c4_next g) -> red_can_force_nonloss fuel' g'
      end
    end
  end.

Lemma score_ge_1_of_not_yellow_win :
  forall g,
    get_result g <> won_by yellow ->
    score g >= 1.
Proof.
  intros g H.
  unfold score.
  destruct (get_result g) as [p| |] eqn:Hr; simpl; try lia.
  destruct p.
  - lia.
  - exfalso.
    apply H.
    reflexivity.
Qed.

Theorem red_can_force_nonloss_value_ge_1 :
  forall fuel g,
    red_can_force_nonloss fuel g ->
    value_fuel fuel g >= 1.
Proof.
  induction fuel as [|fuel IH]; intros g Hsafe.
  - simpl in *.
    apply score_ge_1_of_not_yellow_win.
    exact Hsafe.
  - simpl in *.
    destruct (get_result g) as [p| |] eqn:Hres.
    + destruct p.
      * unfold score. rewrite Hres. simpl. lia.
      * contradiction.
    + unfold score. rewrite Hres. simpl. lia.
    + destruct (next_turn g) eqn:Hturn.
      * destruct Hsafe as [g' [Hin Hsafe']].
        pose proof (IH g' Hsafe') as Hchild.
        set (scored := map (fun g'' : game => (g'', value_fuel fuel g'')) (c4_next g)).
        assert (Hin_pair : In (g', value_fuel fuel g') scored).
        { unfold scored.
          apply in_map_iff.
          exists g'. split; auto. }
        change 1 with (snd (g', 1)).
        destruct (max (comparing Nat.le snd) scored) as [[gb vb]|] eqn:Hmax.
        -- assert (Hforall :
             Forall (fun p0 => (comparing Nat.le snd) p0 (gb, vb)) scored).
           { pose proof
               (@max_is_max (game * nat) (comparing Nat.le snd) _ _ _ _ _
                 scored) as Hmaxprop.
             rewrite Hmax in Hmaxprop.
             exact Hmaxprop. }
           rewrite Forall_forall in Hforall.
           specialize (Hforall _ Hin_pair).
           unfold comparing in Hforall.
           simpl in Hforall.
           assert (Hle : value_fuel fuel g' <= vb).
           { exact Hforall. }
           apply (Nat.le_trans 1 (value_fuel fuel g') vb).
           { exact Hchild. }
           { exact Hle. }
        -- exfalso.
           assert (scored = []).
           { pose proof
               (@max_is_max (game * nat) (comparing Nat.le snd) _ _ _ _ _
                 scored) as Hmaxprop.
             rewrite Hmax in Hmaxprop.
             exact Hmaxprop. }
           rewrite H in Hin_pair.
           contradiction.
      * set (scored := map (fun g'' : game => (g'', value_fuel fuel g'')) (c4_next g)).
        destruct (max (comparing nat_ge snd) scored) as [[gb vb]|] eqn:Hmax.
        -- assert (Hin_max : In (gb, vb) scored).
           { pose proof
               (@max_is_in (game * nat) (comparing nat_ge snd) _ _ _ _ _
                 scored) as Hmaxin.
             rewrite Hmax in Hmaxin.
             exact Hmaxin. }
           unfold scored in Hin_max.
           apply in_map_iff in Hin_max.
           destruct Hin_max as [gx [Heq Hin]].
           inversion Heq; subst; clear Heq.
           pose proof (Hsafe gb Hin) as Hsafe'.
           pose proof (IH gb Hsafe') as Hv.
           simpl.
           exact Hv.
        -- unfold score.
           rewrite Hres.
           simpl.
           lia.
Qed.

Fixpoint yellow_can_force_win (fuel : nat) (g : game) : Prop :=
  match fuel with
  | O => get_result g = won_by yellow
  | S fuel' =>
    match get_result g with
    | won_by yellow => True
    | won_by red => False
    | draw => False
    | ongoing =>
      match next_turn g with
      | yellow =>
        exists g', In g' (c4_next g) /\ yellow_can_force_win fuel' g'
      | red =>
        forall g', In g' (c4_next g) -> yellow_can_force_win fuel' g'
      end
    end
  end.

Fixpoint red_can_force_win (fuel : nat) (g : game) : Prop :=
  match fuel with
  | O => get_result g = won_by red
  | S fuel' =>
    match get_result g with
    | won_by red => True
    | won_by yellow => False
    | draw => False
    | ongoing =>
      match next_turn g with
      | red =>
        exists g', In g' (c4_next g) /\ red_can_force_win fuel' g'
      | yellow =>
        forall g', In g' (c4_next g) -> red_can_force_win fuel' g'
      end
      end
    end.

(** The forcing predicates and the minimax value recurse on a fuel argument
    that later statements supply as a numeral. Unfolding one of them fans out
    over every legal move sequence, so the conversion oracle is told to reach
    for them last; [simpl] still steps them where a proof asks for it. *)
Strategy 1000
  [value_fuel red_can_force_nonloss yellow_can_force_win red_can_force_win].

Lemma red_can_force_win_yellow_children :
  forall fuel g,
    get_result g = ongoing ->
    next_turn g = yellow ->
    red_can_force_win (S fuel) g ->
    forall g', In g' (c4_next g) -> red_can_force_win fuel g'.
Proof.
  intros fuel g Hres Hturn Hwin g' Hin.
  simpl in Hwin.
  rewrite Hres in Hwin.
  rewrite Hturn in Hwin.
  exact (Hwin g' Hin).
Qed.

Lemma yellow_can_force_win_red_children :
  forall fuel g,
    get_result g = ongoing ->
    next_turn g = red ->
    yellow_can_force_win (S fuel) g ->
    forall g', In g' (c4_next g) -> yellow_can_force_win fuel g'.
Proof.
  intros fuel g Hres Hturn Hy g' Hin.
  simpl in Hy.
  rewrite Hres in Hy.
  rewrite Hturn in Hy.
  exact (Hy g' Hin).
Qed.

Lemma split_exists_or_forall :
  forall (A : Type) (P Q : A -> Prop) (l : list A),
    (forall x, In x l -> P x \/ Q x) ->
    (exists x, In x l /\ P x) \/ (forall x, In x l -> Q x).
Proof.
  intros A P Q l.
  induction l as [|a l IH]; intros Hall.
  - right. intros x Hin. inversion Hin.
  - pose proof (Hall a (or_introl eq_refl)) as Hhead.
    destruct Hhead as [HaP | HaQ].
    + left. exists a. split; [left; reflexivity | exact HaP].
    + assert (Hall_tail : forall x : A, In x l -> P x \/ Q x).
      { intros x Hin.
        apply Hall.
        right; exact Hin. }
      destruct (IH Hall_tail) as [Hex | HallQ].
      * left.
        destruct Hex as [x [Hin HP]].
        exists x. split; [right; exact Hin | exact HP].
      * right.
        intros x Hin.
        destruct Hin as [Hx | Hin'].
        -- subst x. exact HaQ.
        -- apply HallQ. exact Hin'.
Qed.

Theorem red_nonloss_or_yellow_win :
  forall fuel g,
    red_can_force_nonloss fuel g \/ yellow_can_force_win fuel g.
Proof.
  induction fuel as [|fuel IH]; intros g.
  - simpl.
    destruct (get_result g) eqn:Hres.
    + destruct p.
      * left. intros H. discriminate H.
      * right. reflexivity.
    + left. intros H. discriminate H.
    + left. intros H. discriminate H.
  - simpl.
    destruct (get_result g) as [p| |] eqn:Hres.
    + destruct p.
      * left. exact I.
      * right. exact I.
    + left. exact I.
    + destruct (next_turn g) eqn:Hturn.
      * assert (Hall :
           forall x : game, In x (c4_next g) ->
             red_can_force_nonloss fuel x \/ yellow_can_force_win fuel x).
        { intros x Hin.
          apply IH. }
        destruct (split_exists_or_forall game
                    (fun x => red_can_force_nonloss fuel x)
                    (fun x => yellow_can_force_win fuel x)
                    (c4_next g) Hall) as [Hex | HallQ].
        -- left.
           destruct Hex as [x [Hin Hx]].
           exists x. split; assumption.
        -- right.
           intros x Hin.
           apply HallQ.
           exact Hin.
      * assert (Hall :
           forall x : game, In x (c4_next g) ->
             red_can_force_nonloss fuel x \/ yellow_can_force_win fuel x).
        { intros x Hin.
          apply IH. }
        assert (Hall' :
           forall x : game, In x (c4_next g) ->
             yellow_can_force_win fuel x \/ red_can_force_nonloss fuel x).
        { intros x Hin.
          specialize (Hall x Hin).
          destruct Hall as [Hr | Hy].
          - right. exact Hr.
          - left. exact Hy. }
        destruct (split_exists_or_forall game
                    (fun x => yellow_can_force_win fuel x)
                    (fun x => red_can_force_nonloss fuel x)
                    (c4_next g) Hall') as [Hex | HallR].
        -- right.
           destruct Hex as [x [Hin Hx]].
           exists x. split; assumption.
        -- left.
           intros x Hin.
           apply HallR.
           exact Hin.
Qed.

Theorem red_win_implies_red_nonloss :
  forall fuel g,
    red_can_force_win fuel g ->
    red_can_force_nonloss fuel g.
Proof.
  induction fuel as [|fuel IH]; intros g Hred.
  - simpl in *.
    rewrite Hred.
    intros Hbad.
    discriminate Hbad.
  - simpl in *.
    destruct (get_result g) as [p| |] eqn:Hres.
    + destruct p.
      * exact I.
      * contradiction.
    + contradiction.
    + destruct (next_turn g) eqn:Hturn.
      * destruct Hred as [g' [Hin Hred']].
        exists g'. split; [exact Hin|].
        apply IH.
        exact Hred'.
      * intros g' Hin.
        apply IH.
        apply Hred.
        exact Hin.
Qed.

Theorem red_win_not_yellow_win :
  forall fuel g,
    red_can_force_win fuel g ->
    ~ yellow_can_force_win fuel g.
Proof.
  induction fuel as [|fuel IH]; intros g Hred Hy.
  - simpl in *.
    rewrite Hred in Hy.
    discriminate.
  - simpl in *.
    destruct (get_result g) as [p| |] eqn:Hres.
    + destruct p.
      * exact Hy.
      * exact Hred.
    + exact Hred.
    + destruct (next_turn g) eqn:Hturn.
      * destruct Hred as [g' [Hin Hred']].
        specialize (Hy g' Hin).
        eapply IH; eauto.
      * destruct Hy as [g' [Hin Hy']].
        specialize (Hred g' Hin).
        eapply IH; eauto.
Qed.

Theorem yellow_win_not_red_win :
  forall fuel g,
    yellow_can_force_win fuel g ->
    ~ red_can_force_win fuel g.
Proof.
  intros fuel g Hy Hred.
  eapply red_win_not_yellow_win; eauto.
Qed.

Theorem not_both_force_win :
  forall fuel g,
    ~ (red_can_force_win fuel g /\ yellow_can_force_win fuel g).
Proof.
  intros fuel g [Hred Hy].
  eapply red_win_not_yellow_win; eauto.
Qed.

Lemma reachable_child :
  forall g g',
    reachable c4_next_intrinsic c4_init g ->
    In g' (c4_next g) ->
    reachable c4_next_intrinsic c4_init g'.
Proof.
  intros g g' Hreach Hin.
  eapply rt_trans.
  - exact Hreach.
  - apply rt_step.
    apply c4_step_iff.
    exact Hin.
Qed.

Lemma reachable_child_from :
  forall g0 g g',
    reachable c4_next_intrinsic g0 g ->
    In g' (c4_next g) ->
    reachable c4_next_intrinsic g0 g'.
Proof.
  intros g0 g g' Hreach Hin.
  eapply rt_trans.
  - exact Hreach.
  - apply rt_step.
    apply c4_step_iff.
    exact Hin.
Qed.

Lemma no_simul_from_start :
  forall g0 g,
    reachable c4_next_intrinsic g0 g ->
    (has_won (current_board g0) red = false \/
     has_won (current_board g0) yellow = false) ->
    ~ (has_won (current_board g) red = true /\
       has_won (current_board g) yellow = true).
Proof.
  intros g0 g Hreach Hinit.
  pose proof (reachable_preserves_no_simul g0 g Hreach Hinit) as Hnos.
  intros [Hr Hy].
  destruct Hnos as [Hrf | Hyf]; congruence.
Qed.

Theorem yellow_win_mirror_reachable_red_win_from :
  forall fuel g0 g,
    reachable c4_next_intrinsic g0 g ->
    (has_won (current_board g0) red = false \/
     has_won (current_board g0) yellow = false) ->
    yellow_can_force_win fuel g ->
    red_can_force_win fuel (mirror_game g).
Proof.
  induction fuel as [|fuel IH]; intros g0 g Hreach Hinit Hy.
  - simpl in *.
    pose proof (no_simul_from_start g0 g Hreach Hinit) as Hnosimul.
    pose proof (get_result_mirror_game_no_simul g Hnosimul) as Hmir.
    rewrite Hy in Hmir.
    simpl in Hmir.
    exact Hmir.
  - simpl in *.
    destruct (get_result g) as [p| |] eqn:Hres.
    + destruct p.
      * contradiction.
      * pose proof (no_simul_from_start g0 g Hreach Hinit) as Hnosimul.
        pose proof (get_result_mirror_game_no_simul g Hnosimul) as Hmir.
        rewrite Hres in Hmir.
        simpl in Hmir.
        rewrite Hmir.
        exact I.
    + contradiction.
    + assert (Hresm : get_result (mirror_game g) = ongoing).
      { apply get_result_ongoing_mirror.
        exact Hres. }
      rewrite Hresm.
      destruct (next_turn g) eqn:Hturn.
      * intros h Hinh.
        pose proof (c4_next_mirror_right g h Hinh) as Hin_pre.
        specialize (Hy (mirror_game h) Hin_pre).
        specialize (IH g0 (mirror_game h)).
        assert (Hreach_pre : reachable c4_next_intrinsic g0 (mirror_game h)).
        { eapply reachable_child_from; eauto. }
        specialize (IH Hreach_pre Hinit Hy).
        rewrite mirror_game_involutive in IH.
        exact IH.
      * destruct Hy as [g' [Hin Hy']].
        exists (mirror_game g').
        split.
        -- apply c4_next_mirror_left.
           exact Hin.
        -- eapply (IH g0 g').
           ++ eapply reachable_child_from; eauto.
           ++ exact Hinit.
           ++ exact Hy'.
Qed.

Theorem red_win_mirror_reachable_yellow_win_from :
  forall fuel g0 g,
    reachable c4_next_intrinsic g0 g ->
    (has_won (current_board g0) red = false \/
     has_won (current_board g0) yellow = false) ->
    red_can_force_win fuel g ->
    yellow_can_force_win fuel (mirror_game g).
Proof.
  induction fuel as [|fuel IH]; intros g0 g Hreach Hinit Hred.
  - simpl in *.
    pose proof (no_simul_from_start g0 g Hreach Hinit) as Hnosimul.
    pose proof (get_result_mirror_game_no_simul g Hnosimul) as Hmir.
    rewrite Hred in Hmir.
    simpl in Hmir.
    exact Hmir.
  - simpl in *.
    destruct (get_result g) as [p| |] eqn:Hres.
    + destruct p.
      * pose proof (no_simul_from_start g0 g Hreach Hinit) as Hnosimul.
        pose proof (get_result_mirror_game_no_simul g Hnosimul) as Hmir.
        rewrite Hres in Hmir.
        simpl in Hmir.
        rewrite Hmir.
        exact I.
      * contradiction.
    + contradiction.
    + assert (Hresm : get_result (mirror_game g) = ongoing).
      { apply get_result_ongoing_mirror.
        exact Hres. }
      rewrite Hresm.
      destruct (next_turn g) eqn:Hturn.
      * destruct Hred as [g' [Hin Hred']].
        exists (mirror_game g').
        split.
        -- apply c4_next_mirror_left.
           exact Hin.
        -- eapply (IH g0 g').
           ++ eapply reachable_child_from; eauto.
           ++ exact Hinit.
           ++ exact Hred'.
      * intros h Hinh.
        pose proof (c4_next_mirror_right g h Hinh) as Hin_pre.
        specialize (Hred (mirror_game h) Hin_pre).
        specialize (IH g0 (mirror_game h)).
        assert (Hreach_pre : reachable c4_next_intrinsic g0 (mirror_game h)).
        { eapply reachable_child_from; eauto. }
        specialize (IH Hreach_pre Hinit Hred).
        rewrite mirror_game_involutive in IH.
        exact IH.
Qed.

Theorem yellow_win_mirror_reachable_red_win :
  forall fuel g,
    reachable c4_next_intrinsic c4_init g ->
    yellow_can_force_win fuel g ->
    red_can_force_win fuel (mirror_game g).
Proof.
  intros fuel g Hreach Hy.
  eapply yellow_win_mirror_reachable_red_win_from.
  - exact Hreach.
  - left. exact has_won_init_red.
  - exact Hy.
Qed.

Theorem red_win_mirror_reachable_yellow_win :
  forall fuel g,
    reachable c4_next_intrinsic c4_init g ->
    red_can_force_win fuel g ->
    yellow_can_force_win fuel (mirror_game g).
Proof.
  intros fuel g Hreach Hred.
  eapply red_win_mirror_reachable_yellow_win_from.
  - exact Hreach.
  - left. exact has_won_init_red.
  - exact Hred.
Qed.

Corollary mirror_win_equiv_reachable :
  forall fuel g,
    reachable c4_next_intrinsic c4_init g ->
    yellow_can_force_win fuel g <-> red_can_force_win fuel (mirror_game g).
Proof.
  intros fuel g Hreach.
  split.
  - intro Hy.
    eapply yellow_win_mirror_reachable_red_win; eauto.
  - intro Hred.
    pose proof (reachable_mirror c4_init g Hreach) as Hreachm.
    pose proof
      (red_win_mirror_reachable_yellow_win_from fuel (mirror_game c4_init) (mirror_game g)
         Hreachm (or_introl has_won_init_red) Hred)
      as Hy.
    rewrite mirror_game_involutive in Hy.
    exact Hy.
Qed.

Definition tempo_monotone_red_win : Prop :=
  forall fuel b,
    red_can_force_win fuel
      {| current_board := b; next_turn := yellow |} ->
    red_can_force_win fuel
      {| current_board := b; next_turn := red |}.

Lemma get_result_turn_irrelevant :
  forall b t1 t2,
    get_result {| current_board := b; next_turn := t1 |} =
    get_result {| current_board := b; next_turn := t2 |}.
Proof.
  intros b t1 t2.
  reflexivity.
Qed.

Lemma tempo_monotone_red_win_ongoing_suffices :
  (forall fuel b,
    get_result {| current_board := b; next_turn := yellow |} = ongoing ->
    red_can_force_win fuel
      {| current_board := b; next_turn := yellow |} ->
    red_can_force_win fuel
      {| current_board := b; next_turn := red |}) ->
  tempo_monotone_red_win.
Proof.
  intros Hongo fuel b Hwin.
  destruct (get_result {| current_board := b; next_turn := yellow |}) as [p| |] eqn:Hres.
  - destruct p.
    + destruct fuel as [|fuel'].
      * simpl in Hwin.
        simpl.
        rewrite (get_result_turn_irrelevant b red yellow).
        exact Hwin.
      * simpl.
        rewrite (get_result_turn_irrelevant b red yellow).
        rewrite Hres.
        exact I.
    + destruct fuel as [|fuel'].
      * simpl in Hwin.
        rewrite Hres in Hwin.
        discriminate.
      * simpl in Hwin.
        rewrite Hres in Hwin.
        contradiction.
  - destruct fuel as [|fuel'].
    + simpl in Hwin.
      rewrite Hres in Hwin.
      discriminate.
    + simpl in Hwin.
      rewrite Hres in Hwin.
      contradiction.
  - apply Hongo; assumption.
Qed.

Lemma reachable_c4_init_refl :
  reachable c4_next_intrinsic c4_init c4_init.
Proof.
  apply rt_refl.
Qed.

Definition c4_init_mirror : game := mirror_game c4_init.

Lemma c4_init_mirror_shape :
  c4_init_mirror =
  {| current_board := mkbd [] [] [] [] [] [] []
   ; next_turn := yellow |}.
Proof.
  reflexivity.
Qed.

Lemma get_result_c4_init_ongoing :
  get_result c4_init = ongoing.
Proof.
  unfold c4_init, get_result.
  simpl.
  reflexivity.
Qed.

Lemma get_result_c4_init_mirror_ongoing :
  get_result c4_init_mirror = ongoing.
Proof.
  rewrite c4_init_mirror_shape.
  rewrite (get_result_turn_irrelevant (mkbd [] [] [] [] [] [] []) yellow red).
  unfold c4_init.
  exact get_result_c4_init_ongoing.
Qed.

Lemma in_c4_next_c4_init_mirror_col0 :
  In (apply_move c4_init_mirror col0) (c4_next c4_init_mirror).
Proof.
  unfold c4_next.
  rewrite get_result_c4_init_mirror_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact get_result_c4_init_mirror_ongoing.
  - rewrite c4_init_mirror_shape.
    simpl.
    lia.
Qed.

Lemma in_c4_next_c4_init_col6 :
  In (apply_move c4_init col6) (c4_next c4_init).
Proof.
  unfold c4_next.
  rewrite get_result_c4_init_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact get_result_c4_init_ongoing.
  - unfold c4_init.
    simpl.
    lia.
Qed.

Lemma in_c4_next_c4_init_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move c4_init m) (c4_next c4_init).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite get_result_c4_init_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact get_result_c4_init_ongoing.
  - unfold c4_init.
    destruct m; simpl; lia.
Qed.

Theorem no_yellow_root_win_if_red_has_winning_opening :
  forall m,
    In m all_moves ->
    red_can_force_win 41 (apply_move c4_init m) ->
    ~ yellow_can_force_win 42 c4_init.
Proof.
  intros m Hinm Hredm Hy.
  assert (Hturn : next_turn c4_init = red).
  { unfold c4_init. reflexivity. }
  pose proof
    (yellow_can_force_win_red_children 41 c4_init
      get_result_c4_init_ongoing Hturn Hy
      (apply_move c4_init m)
      (in_c4_next_c4_init_of_all_moves m Hinm)) as Hym.
  apply (not_both_force_win 41 (apply_move c4_init m)).
  split; assumption.
Qed.

Corollary yellow_root_win_implies_red_mirror_win :
  yellow_can_force_win 42 c4_init ->
  red_can_force_win 42 c4_init_mirror.
Proof.
  intro Hy.
  unfold c4_init_mirror.
  eapply yellow_win_mirror_reachable_red_win.
  - apply reachable_c4_init_refl.
  - exact Hy.
Qed.

Theorem no_yellow_root_win_if_tempo_monotone :
  tempo_monotone_red_win ->
  ~ yellow_can_force_win 42 c4_init.
Proof.
  intros Htempo Hy.
  pose proof (yellow_root_win_implies_red_mirror_win Hy) as Hredm.
  specialize (Htempo 42 (mkbd [] [] [] [] [] [] [])).
  assert (Hredm_empty :
    red_can_force_win 42
      {| current_board := mkbd [] [] [] [] [] [] []
       ; next_turn := yellow |}).
  { exact (eq_ind_r (fun g => red_can_force_win 42 g) Hredm
             (eq_sym c4_init_mirror_shape)). }
  assert (Hred_root : red_can_force_win 42 c4_init).
  { apply Htempo.
    exact Hredm_empty. }
  apply (not_both_force_win 42 c4_init).
  split; assumption.
Qed.

Theorem red_nonloss_not_yellow_win :
  forall fuel g,
    red_can_force_nonloss fuel g ->
    ~ yellow_can_force_win fuel g.
Proof.
  induction fuel as [|fuel IH]; intros g Hred Hy.
  - simpl in *.
    apply Hred.
    exact Hy.
  - simpl in *.
    destruct (get_result g) as [p| |] eqn:Hres.
    + destruct p.
      * exact Hy.
      * exact Hred.
    + exact Hy.
    + destruct (next_turn g) eqn:Hturn.
      * destruct Hred as [g' [Hin Hred']].
        specialize (Hy g' Hin).
        eapply IH; eauto.
      * destruct Hy as [g' [Hin Hy']].
        specialize (Hred g' Hin).
        eapply IH; eauto.
Qed.

Theorem red_nonloss_of_not_yellow_win :
  forall fuel g,
    ~ yellow_can_force_win fuel g ->
    red_can_force_nonloss fuel g.
Proof.
  intros fuel g Hnot.
  destruct (red_nonloss_or_yellow_win fuel g) as [Hred | Hy].
  - exact Hred.
  - exfalso.
    apply Hnot.
    exact Hy.
Qed.

Theorem root_nonloss_value_ge_1_if_not_yellow_win :
  ~ yellow_can_force_win 42 c4_init ->
  value_fuel 42 c4_init >= 1.
Proof.
  intros Hnot.
  apply red_can_force_nonloss_value_ge_1.
  apply red_nonloss_of_not_yellow_win.
  exact Hnot.
Qed.

Theorem no_yellow_root_win_if_red_has_nonlosing_opening :
  forall m,
    In m all_moves ->
    red_can_force_nonloss 41 (apply_move c4_init m) ->
    ~ yellow_can_force_win 42 c4_init.
Proof.
  intros m Hinm Hsafe Hy.
  assert (Hturn : next_turn c4_init = red).
  { unfold c4_init. reflexivity. }
  pose proof
    (yellow_can_force_win_red_children 41 c4_init
      get_result_c4_init_ongoing Hturn Hy
      (apply_move c4_init m)
      (in_c4_next_c4_init_of_all_moves m Hinm)) as Hym.
  exact (red_nonloss_not_yellow_win 41 (apply_move c4_init m) Hsafe Hym).
Qed.

Theorem root_nonloss_value_ge_1_if_red_has_winning_opening :
  forall m,
    In m all_moves ->
    red_can_force_win 41 (apply_move c4_init m) ->
    value_fuel 42 c4_init >= 1.
Proof.
  intros m Hinm Hredm.
  apply root_nonloss_value_ge_1_if_not_yellow_win.
  eapply no_yellow_root_win_if_red_has_winning_opening; eauto.
Qed.

Theorem root_nonloss_value_ge_1_if_red_has_nonlosing_opening :
  forall m,
    In m all_moves ->
    red_can_force_nonloss 41 (apply_move c4_init m) ->
    value_fuel 42 c4_init >= 1.
Proof.
  intros m Hinm Hsafe.
  apply root_nonloss_value_ge_1_if_not_yellow_win.
  eapply no_yellow_root_win_if_red_has_nonlosing_opening; eauto.
Qed.


Definition opening_col6_target : Prop :=
  red_can_force_win 41 (apply_move c4_init col6).

Definition opening_col6_nonloss_target : Prop :=
  red_can_force_nonloss 41 (apply_move c4_init col6).

Lemma opening_col6_target_implies_nonloss_target :
  opening_col6_target ->
  opening_col6_nonloss_target.
Proof.
  intros H.
  unfold opening_col6_target, opening_col6_nonloss_target.
  apply red_win_implies_red_nonloss.
  exact H.
Qed.

Theorem root_nonloss_value_ge_1_if_opening_col6_nonloss_target :
  opening_col6_nonloss_target ->
  value_fuel 42 c4_init >= 1.
Proof.
  intros Hnl.
  apply (root_nonloss_value_ge_1_if_red_has_nonlosing_opening col6).
  - simpl. tauto.
  - exact Hnl.
Qed.

Definition opening_col6_state : game :=
  apply_move c4_init col6.

Lemma red_can_force_win_unfold_ongoing_yellow :
  forall fuel g,
    get_result g = ongoing ->
    next_turn g = yellow ->
    (red_can_force_win (S fuel) g <->
     forall g', In g' (c4_next g) -> red_can_force_win fuel g').
Proof.
  intros fuel g Hres Hturn.
  simpl.
  rewrite Hres.
  rewrite Hturn.
  tauto.
Qed.

Lemma red_can_force_win_unfold_ongoing_red :
  forall fuel g,
    get_result g = ongoing ->
    next_turn g = red ->
    (red_can_force_win (S fuel) g <->
     exists g', In g' (c4_next g) /\ red_can_force_win fuel g').
Proof.
  intros fuel g Hres Hturn.
  simpl.
  rewrite Hres.
  rewrite Hturn.
  tauto.
Qed.

Definition red_col6_vertical_threat_0123 : threat :=
  {| threat_player := red
   ; threat_line := (6, 0, 6, 1, 6, 2, 6, 3)
   ; threat_empty := (6, 3)
  |}.

Lemma has_threat_red_col6_vertical_0123_if_cells :
  forall b,
    get_cell b 6 0 = Some red ->
    get_cell b 6 1 = Some red ->
    get_cell b 6 2 = Some red ->
    get_cell b 6 3 = None ->
    has_threat b red_col6_vertical_threat_0123.
Proof.
  intros b H60 H61 H62 H63.
  unfold has_threat, red_col6_vertical_threat_0123, line_cells.
  repeat split.
  - right. left. repeat split; simpl; lia.
  - exact H63.
  - simpl. tauto.
  - constructor.
    + right. exact H60.
    + constructor.
      * right. exact H61.
      * constructor.
        { right. exact H62. }
        constructor.
        { left. reflexivity. }
        constructor.
Qed.

Lemma live_threat_red_col6_vertical_0123_if_cells :
  forall b,
    get_cell b 6 0 = Some red ->
    get_cell b 6 1 = Some red ->
    get_cell b 6 2 = Some red ->
    get_cell b 6 3 = None ->
    live_threat b red_col6_vertical_threat_0123.
Proof.
  intros b H60 H61 H62 H63.
  split.
  - apply has_threat_red_col6_vertical_0123_if_cells; assumption.
  - right.
    exists red.
    exact H62.
Qed.

Lemma red_can_force_win_if_col6_vertical_threat :
  forall fuel g,
    get_result g = ongoing ->
    next_turn g = red ->
    get_cell (current_board g) 6 0 = Some red ->
    get_cell (current_board g) 6 1 = Some red ->
    get_cell (current_board g) 6 2 = Some red ->
    get_cell (current_board g) 6 3 = None ->
    red_can_force_win (S fuel) g.
Proof.
  intros fuel g Hres Hturn H60 H61 H62 H63.
  assert (Hlive : live_threat (current_board g) red_col6_vertical_threat_0123).
  { apply live_threat_red_col6_vertical_0123_if_cells; assumption. }
  assert (Htp : threat_player red_col6_vertical_threat_0123 = next_turn g).
  { unfold red_col6_vertical_threat_0123. simpl. rewrite Hturn. reflexivity. }
  destruct (live_threat_wins g red_col6_vertical_threat_0123 Hlive Htp Hres)
    as [m [Hvm Hwin]].
  apply (proj2 (red_can_force_win_unfold_ongoing_red fuel g Hres Hturn)).
  exists (apply_move g m).
  split.
  - unfold c4_next.
    rewrite Hres.
    apply in_map.
    apply moves_complete.
    exact Hvm.
  - destruct fuel as [|fuel'].
    + simpl.
      exact Hwin.
    + simpl.
      rewrite Hwin.
      exact I.
Qed.

Lemma red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat :
  forall g m,
    nat_of_move m <> 6 ->
    get_result (apply_move g m) = ongoing ->
    next_turn (apply_move g m) = red ->
    get_cell (current_board g) 6 0 = Some red ->
    get_cell (current_board g) 6 1 = Some red ->
    get_cell (current_board g) 6 2 = Some red ->
    get_cell (current_board g) 6 3 = None ->
    red_can_force_win 36 (apply_move g m).
Proof.
  intros g m Hneq Hres Hturn H60 H61 H62 H63.
  apply (red_can_force_win_if_col6_vertical_threat 35 (apply_move g m));
    try assumption.
  - rewrite get_cell_apply_move_other_col; [exact H60|lia].
  - rewrite get_cell_apply_move_other_col; [exact H61|lia].
  - rewrite get_cell_apply_move_other_col; [exact H62|lia].
  - rewrite get_cell_apply_move_other_col; [exact H63|lia].
Qed.

Definition red_col6_vertical_threat_2345 : threat :=
  {| threat_player := red
   ; threat_line := (6, 2, 6, 3, 6, 4, 6, 5)
   ; threat_empty := (6, 5)
  |}.

Lemma has_threat_red_col6_vertical_2345_if_cells :
  forall b,
    get_cell b 6 2 = Some red ->
    get_cell b 6 3 = Some red ->
    get_cell b 6 4 = Some red ->
    get_cell b 6 5 = None ->
    has_threat b red_col6_vertical_threat_2345.
Proof.
  intros b H62 H63 H64 H65.
  unfold has_threat, red_col6_vertical_threat_2345, line_cells.
  repeat split.
  - right. left. repeat split; simpl; lia.
  - exact H65.
  - simpl. tauto.
  - constructor.
    + right. exact H62.
    + constructor.
      * right. exact H63.
      * constructor.
        { right. exact H64. }
        constructor.
        { left. reflexivity. }
        constructor.
Qed.

Lemma live_threat_red_col6_vertical_2345_if_cells :
  forall b,
    get_cell b 6 2 = Some red ->
    get_cell b 6 3 = Some red ->
    get_cell b 6 4 = Some red ->
    get_cell b 6 5 = None ->
    live_threat b red_col6_vertical_threat_2345.
Proof.
  intros b H62 H63 H64 H65.
  split.
  - apply has_threat_red_col6_vertical_2345_if_cells; assumption.
  - right.
    exists red.
    exact H64.
Qed.

Lemma red_can_force_win_if_col6_vertical_threat_2345 :
  forall fuel g,
    get_result g = ongoing ->
    next_turn g = red ->
    get_cell (current_board g) 6 2 = Some red ->
    get_cell (current_board g) 6 3 = Some red ->
    get_cell (current_board g) 6 4 = Some red ->
    get_cell (current_board g) 6 5 = None ->
    red_can_force_win (S fuel) g.
Proof.
  intros fuel g Hres Hturn H62 H63 H64 H65.
  assert (Hlive : live_threat (current_board g) red_col6_vertical_threat_2345).
  { apply live_threat_red_col6_vertical_2345_if_cells; assumption. }
  assert (Htp : threat_player red_col6_vertical_threat_2345 = next_turn g).
  { unfold red_col6_vertical_threat_2345. simpl. rewrite Hturn. reflexivity. }
  destruct (live_threat_wins g red_col6_vertical_threat_2345 Hlive Htp Hres)
    as [m [Hvm Hwin]].
  apply (proj2 (red_can_force_win_unfold_ongoing_red fuel g Hres Hturn)).
  exists (apply_move g m).
  split.
  - unfold c4_next.
    rewrite Hres.
    apply in_map.
    apply moves_complete.
    exact Hvm.
  - destruct fuel as [|fuel'].
    + simpl.
      exact Hwin.
    + simpl.
      rewrite Hwin.
      exact I.
Qed.

Lemma in_c4_next_if_valid_move :
  forall g m,
    get_result g = ongoing ->
    valid_move g m ->
    In (apply_move g m) (c4_next g).
Proof.
  intros g m Hres Hvm.
  unfold c4_next.
  rewrite Hres.
  apply in_map.
  apply moves_complete.
  exact Hvm.
Qed.

Lemma red_can_force_win_36_if_col6_upper_setup :
  forall g,
    get_result g = ongoing ->
    next_turn g = red ->
    get_cell (current_board g) 6 5 = None ->
    red_can_force_win 35 (apply_move g col6) ->
    red_can_force_win 36 g.
Proof.
  intros g Hres Hturn H65 Hchild.
  apply (proj2 (red_can_force_win_unfold_ongoing_red 35 g Hres Hturn)).
  exists (apply_move g col6).
  split.
  - assert (Hvm : valid_move g col6).
    { apply valid_move_intro.
      - exact Hres.
      - apply get_cell_None_length in H65.
        assert (Hle5 : length (column_of_move col6 (current_board g)) <= 5).
        { rewrite <- (get_column_nat_of_move (current_board g) col6).
          exact H65. }
        lia. }
    apply in_c4_next_if_valid_move; assumption.
  - exact Hchild.
Qed.

Lemma opening_col6_turn_yellow :
  next_turn opening_col6_state = yellow.
Proof.
  unfold opening_col6_state, c4_init.
  simpl.
  unfold apply_move.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_result_ongoing :
  get_result opening_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_target_unfold :
  opening_col6_target <->
  forall g,
    In g (c4_next opening_col6_state) ->
    red_can_force_win 40 g.
Proof.
  unfold opening_col6_target, opening_col6_state.
  change (red_can_force_win (S 40) (apply_move c4_init col6) <->
    forall g, In g (c4_next (apply_move c4_init col6)) -> red_can_force_win 40 g).
  apply red_can_force_win_unfold_ongoing_yellow.
  - apply opening_col6_result_ongoing.
  - apply opening_col6_turn_yellow.
Qed.

Lemma in_c4_next_opening_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_state m) (c4_next opening_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_result_ongoing.
  - unfold opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_target_move_form :
  opening_col6_target <->
  forall m,
    In m all_moves ->
    red_can_force_win 40 (apply_move opening_col6_state m).
Proof.
  split.
  - intros Htarget m Hinm.
    apply (proj1 opening_col6_target_unfold Htarget).
    apply in_c4_next_opening_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 opening_col6_target_unfold).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_subgoals : Prop :=
  red_can_force_win 40 (apply_move opening_col6_state col0) /\
  red_can_force_win 40 (apply_move opening_col6_state col1) /\
  red_can_force_win 40 (apply_move opening_col6_state col2) /\
  red_can_force_win 40 (apply_move opening_col6_state col3) /\
  red_can_force_win 40 (apply_move opening_col6_state col4) /\
  red_can_force_win 40 (apply_move opening_col6_state col5) /\
  red_can_force_win 40 (apply_move opening_col6_state col6).

Lemma opening_col6_target_implies_reply_subgoals :
  opening_col6_target ->
  opening_col6_reply_subgoals.
Proof.
  intro Htarget.
  pose proof (proj1 opening_col6_target_move_form Htarget) as Hm.
  repeat split;
    apply Hm;
    simpl; tauto.
Qed.

Lemma opening_col6_target_if_reply_subgoals :
  opening_col6_reply_subgoals ->
  opening_col6_target.
Proof.
  intro Hsubs.
  apply (proj2 opening_col6_target_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Definition opening_col6_reply_col0_state : game :=
  apply_move opening_col6_state col0.

Definition opening_col6_reply_col0_goal : Prop :=
  red_can_force_win 40 opening_col6_reply_col0_state.

Lemma opening_col6_reply_subgoals_if_col0_and_rest_raw :
  red_can_force_win 40 (apply_move opening_col6_state col0) ->
  red_can_force_win 40 (apply_move opening_col6_state col1) ->
  red_can_force_win 40 (apply_move opening_col6_state col2) ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_reply_subgoals.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  split.
  - exact H0.
  - split.
    + exact H1.
    + split.
      * exact H2.
      * split.
        -- exact H3.
        -- split.
           ++ exact H4.
           ++ split.
              ** exact H5.
              ** exact H6.
Qed.

Lemma opening_col6_reply_col0_turn_red :
  next_turn opening_col6_reply_col0_state = red.
Proof.
  unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_result_ongoing :
  get_result opening_col6_reply_col0_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_goal_unfold :
  opening_col6_reply_col0_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col0_state) /\
    red_can_force_win 39 g.
Proof.
  unfold opening_col6_reply_col0_goal.
  change 40 with (S 39).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col0_result_ongoing.
  - apply opening_col6_reply_col0_turn_red.
Qed.

Definition opening_col6_reply_col0_red_col6_state : game :=
  apply_move opening_col6_reply_col0_state col6.

Lemma in_c4_next_opening_col6_reply_col0_red_col6 :
  In opening_col6_reply_col0_red_col6_state
     (c4_next opening_col6_reply_col0_state).
Proof.
  unfold opening_col6_reply_col0_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col0_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col0_result_ongoing.
  - unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col0_goal_if_red_col6_child :
  red_can_force_win 39 opening_col6_reply_col0_red_col6_state ->
  opening_col6_reply_col0_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col0_goal_unfold).
  exists opening_col6_reply_col0_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col0_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col0_red_col6_turn_yellow :
  next_turn opening_col6_reply_col0_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_result_ongoing :
  get_result opening_col6_reply_col0_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col0_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col0_red_col6_state m)
       (c4_next opening_col6_reply_col0_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col0_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col0_red_col6_result_ongoing.
  - unfold opening_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col0_red_col6_move_form :
  red_can_force_win 39 opening_col6_reply_col0_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 38
      (apply_move opening_col6_reply_col0_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col0_red_col6_state
                    opening_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col0_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col0_red_col6_state
                    opening_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col0_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col0_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_subgoals : Prop :=
  red_can_force_win 38 (apply_move opening_col6_reply_col0_red_col6_state col0) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col0_red_col6_state col1) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col0_red_col6_state col2) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col0_red_col6_state col3) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col0_red_col6_state col4) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col0_red_col6_state col5) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col0_red_col6_state col6).

Lemma opening_col6_reply_col0_red_col6_subgoals_imply_child :
  opening_col6_reply_col0_red_col6_reply_subgoals ->
  red_can_force_win 39 opening_col6_reply_col0_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col0_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col0_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col0_goal_if_red_col6_child.
  apply opening_col6_reply_col0_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col0_state : game :=
  apply_move opening_col6_reply_col0_red_col6_state col0.

Definition opening_col6_reply_col0_red_col6_reply_col0_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col0_red_col6_reply_col0_state.

Lemma opening_col6_reply_col0_red_col6_reply_col0_turn_red :
  next_turn opening_col6_reply_col0_red_col6_reply_col0_state = red.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col0_state.
  unfold opening_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col0_result_ongoing :
  get_result opening_col6_reply_col0_red_col6_reply_col0_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col0_goal_unfold :
  opening_col6_reply_col0_red_col6_reply_col0_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col0_red_col6_reply_col0_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col0_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col0_red_col6_reply_col0_result_ongoing.
  - apply opening_col6_reply_col0_red_col6_reply_col0_turn_red.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col0_red_col6_state : game :=
  apply_move opening_col6_reply_col0_red_col6_reply_col0_state col6.

Lemma in_c4_next_opening_col6_reply_col0_red_col6_reply_col0_red_col6 :
  In opening_col6_reply_col0_red_col6_reply_col0_red_col6_state
     (c4_next opening_col6_reply_col0_red_col6_reply_col0_state).
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col0_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col0_red_col6_reply_col0_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col0_red_col6_reply_col0_result_ongoing.
  - unfold opening_col6_reply_col0_red_col6_reply_col0_state.
    unfold opening_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col0_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col0_red_col6_state ->
  opening_col6_reply_col0_red_col6_reply_col0_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col0_red_col6_reply_col0_goal_unfold).
  exists opening_col6_reply_col0_red_col6_reply_col0_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col0_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col0_red_col6_turn_yellow :
  next_turn opening_col6_reply_col0_red_col6_reply_col0_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col0_red_col6_reply_col0_state.
  unfold opening_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col0_red_col6_result_ongoing :
  get_result opening_col6_reply_col0_red_col6_reply_col0_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col0_red_col6_reply_col0_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state m)
       (c4_next opening_col6_reply_col0_red_col6_reply_col0_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col0_red_col6_reply_col0_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col0_red_col6_reply_col0_red_col6_result_ongoing.
  - unfold opening_col6_reply_col0_red_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col0_red_col6_reply_col0_state.
    unfold opening_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col0_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col0_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col0_red_col6_reply_col0_red_col6_state
                    opening_col6_reply_col0_red_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_reply_col0_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col0_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col0_red_col6_reply_col0_red_col6_state
                    opening_col6_reply_col0_red_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_reply_col0_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col0_red_col6_reply_col0_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col0_red_col6_reply_col0_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6).

Lemma opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col0_red_col6_subgoals_imply_child :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col0_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col0_red_col6_reply_col0_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col0_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col0_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col0_red_col6_reply_col0_goal_if_red_col6_child.
  apply opening_col6_reply_col0_red_col6_reply_col0_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col1_state : game :=
  apply_move opening_col6_reply_col0_red_col6_state col1.

Definition opening_col6_reply_col0_red_col6_reply_col1_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col0_red_col6_reply_col1_state.

Lemma opening_col6_reply_col0_red_col6_reply_col1_turn_red :
  next_turn opening_col6_reply_col0_red_col6_reply_col1_state = red.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col1_state.
  unfold opening_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col1_result_ongoing :
  get_result opening_col6_reply_col0_red_col6_reply_col1_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col1_goal_unfold :
  opening_col6_reply_col0_red_col6_reply_col1_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col0_red_col6_reply_col1_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col1_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col0_red_col6_reply_col1_result_ongoing.
  - apply opening_col6_reply_col0_red_col6_reply_col1_turn_red.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col1_red_col6_state : game :=
  apply_move opening_col6_reply_col0_red_col6_reply_col1_state col6.

Lemma in_c4_next_opening_col6_reply_col0_red_col6_reply_col1_red_col6 :
  In opening_col6_reply_col0_red_col6_reply_col1_red_col6_state
     (c4_next opening_col6_reply_col0_red_col6_reply_col1_state).
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col1_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col0_red_col6_reply_col1_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col0_red_col6_reply_col1_result_ongoing.
  - unfold opening_col6_reply_col0_red_col6_reply_col1_state.
    unfold opening_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col1_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col1_red_col6_state ->
  opening_col6_reply_col0_red_col6_reply_col1_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col0_red_col6_reply_col1_goal_unfold).
  exists opening_col6_reply_col0_red_col6_reply_col1_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col1_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col1_red_col6_turn_yellow :
  next_turn opening_col6_reply_col0_red_col6_reply_col1_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col0_red_col6_reply_col1_state.
  unfold opening_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col1_red_col6_result_ongoing :
  get_result opening_col6_reply_col0_red_col6_reply_col1_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col0_red_col6_reply_col1_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state m)
       (c4_next opening_col6_reply_col0_red_col6_reply_col1_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col0_red_col6_reply_col1_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col0_red_col6_reply_col1_red_col6_result_ongoing.
  - unfold opening_col6_reply_col0_red_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col0_red_col6_reply_col1_state.
    unfold opening_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col1_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col1_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col0_red_col6_reply_col1_red_col6_state
                    opening_col6_reply_col0_red_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_reply_col1_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col1_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col0_red_col6_reply_col1_red_col6_state
                    opening_col6_reply_col0_red_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_reply_col1_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col0_red_col6_reply_col1_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col0_red_col6_reply_col1_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6).

Lemma opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col1_red_col6_subgoals_imply_child :
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col1_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col0_red_col6_reply_col1_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col1_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col0_red_col6_reply_col1_goal_if_red_col6_child.
  apply opening_col6_reply_col0_red_col6_reply_col1_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col2_state : game :=
  apply_move opening_col6_reply_col0_red_col6_state col2.

Definition opening_col6_reply_col0_red_col6_reply_col2_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col0_red_col6_reply_col2_state.

Lemma opening_col6_reply_col0_red_col6_reply_col2_turn_red :
  next_turn opening_col6_reply_col0_red_col6_reply_col2_state = red.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col2_state.
  unfold opening_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col2_result_ongoing :
  get_result opening_col6_reply_col0_red_col6_reply_col2_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col2_goal_unfold :
  opening_col6_reply_col0_red_col6_reply_col2_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col0_red_col6_reply_col2_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col2_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col0_red_col6_reply_col2_result_ongoing.
  - apply opening_col6_reply_col0_red_col6_reply_col2_turn_red.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col2_red_col6_state : game :=
  apply_move opening_col6_reply_col0_red_col6_reply_col2_state col6.

Lemma in_c4_next_opening_col6_reply_col0_red_col6_reply_col2_red_col6 :
  In opening_col6_reply_col0_red_col6_reply_col2_red_col6_state
     (c4_next opening_col6_reply_col0_red_col6_reply_col2_state).
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col2_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col0_red_col6_reply_col2_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col0_red_col6_reply_col2_result_ongoing.
  - unfold opening_col6_reply_col0_red_col6_reply_col2_state.
    unfold opening_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col2_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col2_red_col6_state ->
  opening_col6_reply_col0_red_col6_reply_col2_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col0_red_col6_reply_col2_goal_unfold).
  exists opening_col6_reply_col0_red_col6_reply_col2_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col2_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col2_red_col6_turn_yellow :
  next_turn opening_col6_reply_col0_red_col6_reply_col2_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col0_red_col6_reply_col2_state.
  unfold opening_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col2_red_col6_result_ongoing :
  get_result opening_col6_reply_col0_red_col6_reply_col2_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col0_red_col6_reply_col2_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state m)
       (c4_next opening_col6_reply_col0_red_col6_reply_col2_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col0_red_col6_reply_col2_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col0_red_col6_reply_col2_red_col6_result_ongoing.
  - unfold opening_col6_reply_col0_red_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col0_red_col6_reply_col2_state.
    unfold opening_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col2_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col2_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col0_red_col6_reply_col2_red_col6_state
                    opening_col6_reply_col0_red_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_reply_col2_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col2_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col0_red_col6_reply_col2_red_col6_state
                    opening_col6_reply_col0_red_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_reply_col2_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col0_red_col6_reply_col2_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col0_red_col6_reply_col2_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6).

Lemma opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col2_red_col6_subgoals_imply_child :
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col2_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col0_red_col6_reply_col2_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col2_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col0_red_col6_reply_col2_goal_if_red_col6_child.
  apply opening_col6_reply_col0_red_col6_reply_col2_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col3_state : game :=
  apply_move opening_col6_reply_col0_red_col6_state col3.

Definition opening_col6_reply_col0_red_col6_reply_col3_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col0_red_col6_reply_col3_state.

Lemma opening_col6_reply_col0_red_col6_reply_col3_turn_red :
  next_turn opening_col6_reply_col0_red_col6_reply_col3_state = red.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col3_state.
  unfold opening_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col3_result_ongoing :
  get_result opening_col6_reply_col0_red_col6_reply_col3_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col3_goal_unfold :
  opening_col6_reply_col0_red_col6_reply_col3_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col0_red_col6_reply_col3_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col3_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col0_red_col6_reply_col3_result_ongoing.
  - apply opening_col6_reply_col0_red_col6_reply_col3_turn_red.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col3_red_col6_state : game :=
  apply_move opening_col6_reply_col0_red_col6_reply_col3_state col6.

Lemma in_c4_next_opening_col6_reply_col0_red_col6_reply_col3_red_col6 :
  In opening_col6_reply_col0_red_col6_reply_col3_red_col6_state
     (c4_next opening_col6_reply_col0_red_col6_reply_col3_state).
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col3_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col0_red_col6_reply_col3_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col0_red_col6_reply_col3_result_ongoing.
  - unfold opening_col6_reply_col0_red_col6_reply_col3_state.
    unfold opening_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col3_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col3_red_col6_state ->
  opening_col6_reply_col0_red_col6_reply_col3_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col0_red_col6_reply_col3_goal_unfold).
  exists opening_col6_reply_col0_red_col6_reply_col3_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col3_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col3_red_col6_turn_yellow :
  next_turn opening_col6_reply_col0_red_col6_reply_col3_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col0_red_col6_reply_col3_state.
  unfold opening_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col3_red_col6_result_ongoing :
  get_result opening_col6_reply_col0_red_col6_reply_col3_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col0_red_col6_reply_col3_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state m)
       (c4_next opening_col6_reply_col0_red_col6_reply_col3_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col0_red_col6_reply_col3_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col0_red_col6_reply_col3_red_col6_result_ongoing.
  - unfold opening_col6_reply_col0_red_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col0_red_col6_reply_col3_state.
    unfold opening_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col3_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col3_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col0_red_col6_reply_col3_red_col6_state
                    opening_col6_reply_col0_red_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_reply_col3_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col3_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col0_red_col6_reply_col3_red_col6_state
                    opening_col6_reply_col0_red_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_reply_col3_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col0_red_col6_reply_col3_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col0_red_col6_reply_col3_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6).

Lemma opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col3_red_col6_subgoals_imply_child :
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col3_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col0_red_col6_reply_col3_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col3_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col0_red_col6_reply_col3_goal_if_red_col6_child.
  apply opening_col6_reply_col0_red_col6_reply_col3_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col4_state : game :=
  apply_move opening_col6_reply_col0_red_col6_state col4.

Definition opening_col6_reply_col0_red_col6_reply_col4_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col0_red_col6_reply_col4_state.

Lemma opening_col6_reply_col0_red_col6_reply_col4_turn_red :
  next_turn opening_col6_reply_col0_red_col6_reply_col4_state = red.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col4_state.
  unfold opening_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col4_result_ongoing :
  get_result opening_col6_reply_col0_red_col6_reply_col4_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col4_goal_unfold :
  opening_col6_reply_col0_red_col6_reply_col4_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col0_red_col6_reply_col4_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col4_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col0_red_col6_reply_col4_result_ongoing.
  - apply opening_col6_reply_col0_red_col6_reply_col4_turn_red.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col4_red_col6_state : game :=
  apply_move opening_col6_reply_col0_red_col6_reply_col4_state col6.

Lemma in_c4_next_opening_col6_reply_col0_red_col6_reply_col4_red_col6 :
  In opening_col6_reply_col0_red_col6_reply_col4_red_col6_state
     (c4_next opening_col6_reply_col0_red_col6_reply_col4_state).
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col4_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col0_red_col6_reply_col4_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col0_red_col6_reply_col4_result_ongoing.
  - unfold opening_col6_reply_col0_red_col6_reply_col4_state.
    unfold opening_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col4_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col4_red_col6_state ->
  opening_col6_reply_col0_red_col6_reply_col4_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col0_red_col6_reply_col4_goal_unfold).
  exists opening_col6_reply_col0_red_col6_reply_col4_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col4_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col4_red_col6_turn_yellow :
  next_turn opening_col6_reply_col0_red_col6_reply_col4_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col0_red_col6_reply_col4_state.
  unfold opening_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col4_red_col6_result_ongoing :
  get_result opening_col6_reply_col0_red_col6_reply_col4_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col0_red_col6_reply_col4_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state m)
       (c4_next opening_col6_reply_col0_red_col6_reply_col4_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col0_red_col6_reply_col4_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col0_red_col6_reply_col4_red_col6_result_ongoing.
  - unfold opening_col6_reply_col0_red_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col0_red_col6_reply_col4_state.
    unfold opening_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col4_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col4_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col0_red_col6_reply_col4_red_col6_state
                    opening_col6_reply_col0_red_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_reply_col4_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col4_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col0_red_col6_reply_col4_red_col6_state
                    opening_col6_reply_col0_red_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_reply_col4_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col0_red_col6_reply_col4_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col0_red_col6_reply_col4_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6).

Lemma opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col4_red_col6_subgoals_imply_child :
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col4_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col0_red_col6_reply_col4_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col4_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col0_red_col6_reply_col4_goal_if_red_col6_child.
  apply opening_col6_reply_col0_red_col6_reply_col4_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col5_state : game :=
  apply_move opening_col6_reply_col0_red_col6_state col5.

Definition opening_col6_reply_col0_red_col6_reply_col5_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col0_red_col6_reply_col5_state.

Lemma opening_col6_reply_col0_red_col6_reply_col5_turn_red :
  next_turn opening_col6_reply_col0_red_col6_reply_col5_state = red.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col5_state.
  unfold opening_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col5_result_ongoing :
  get_result opening_col6_reply_col0_red_col6_reply_col5_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col5_goal_unfold :
  opening_col6_reply_col0_red_col6_reply_col5_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col0_red_col6_reply_col5_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col5_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col0_red_col6_reply_col5_result_ongoing.
  - apply opening_col6_reply_col0_red_col6_reply_col5_turn_red.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col5_red_col6_state : game :=
  apply_move opening_col6_reply_col0_red_col6_reply_col5_state col6.

Lemma in_c4_next_opening_col6_reply_col0_red_col6_reply_col5_red_col6 :
  In opening_col6_reply_col0_red_col6_reply_col5_red_col6_state
     (c4_next opening_col6_reply_col0_red_col6_reply_col5_state).
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col5_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col0_red_col6_reply_col5_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col0_red_col6_reply_col5_result_ongoing.
  - unfold opening_col6_reply_col0_red_col6_reply_col5_state.
    unfold opening_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col5_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col5_red_col6_state ->
  opening_col6_reply_col0_red_col6_reply_col5_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col0_red_col6_reply_col5_goal_unfold).
  exists opening_col6_reply_col0_red_col6_reply_col5_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col5_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col5_red_col6_turn_yellow :
  next_turn opening_col6_reply_col0_red_col6_reply_col5_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col0_red_col6_reply_col5_state.
  unfold opening_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col5_red_col6_result_ongoing :
  get_result opening_col6_reply_col0_red_col6_reply_col5_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col0_red_col6_reply_col5_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state m)
       (c4_next opening_col6_reply_col0_red_col6_reply_col5_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col0_red_col6_reply_col5_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col0_red_col6_reply_col5_red_col6_result_ongoing.
  - unfold opening_col6_reply_col0_red_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col0_red_col6_reply_col5_state.
    unfold opening_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col5_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col5_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col0_red_col6_reply_col5_red_col6_state
                    opening_col6_reply_col0_red_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_reply_col5_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col5_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col0_red_col6_reply_col5_red_col6_state
                    opening_col6_reply_col0_red_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_reply_col5_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col0_red_col6_reply_col5_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col0_red_col6_reply_col5_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6).

Lemma opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col5_red_col6_subgoals_imply_child :
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col5_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col0_red_col6_reply_col5_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col5_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col0_red_col6_reply_col5_goal_if_red_col6_child.
  apply opening_col6_reply_col0_red_col6_reply_col5_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col6_state : game :=
  apply_move opening_col6_reply_col0_red_col6_state col6.

Definition opening_col6_reply_col0_red_col6_reply_col6_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col0_red_col6_reply_col6_state.

Lemma opening_col6_reply_col0_red_col6_reply_col6_turn_red :
  next_turn opening_col6_reply_col0_red_col6_reply_col6_state = red.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col6_state.
  unfold opening_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col6_result_ongoing :
  get_result opening_col6_reply_col0_red_col6_reply_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col6_goal_unfold :
  opening_col6_reply_col0_red_col6_reply_col6_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col0_red_col6_reply_col6_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col6_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col0_red_col6_reply_col6_result_ongoing.
  - apply opening_col6_reply_col0_red_col6_reply_col6_turn_red.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col6_red_col6_state : game :=
  apply_move opening_col6_reply_col0_red_col6_reply_col6_state col6.

Lemma in_c4_next_opening_col6_reply_col0_red_col6_reply_col6_red_col6 :
  In opening_col6_reply_col0_red_col6_reply_col6_red_col6_state
     (c4_next opening_col6_reply_col0_red_col6_reply_col6_state).
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col6_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col0_red_col6_reply_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col0_red_col6_reply_col6_result_ongoing.
  - unfold opening_col6_reply_col0_red_col6_reply_col6_state.
    unfold opening_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col6_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col6_red_col6_state ->
  opening_col6_reply_col0_red_col6_reply_col6_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col0_red_col6_reply_col6_goal_unfold).
  exists opening_col6_reply_col0_red_col6_reply_col6_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col6_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col6_red_col6_turn_yellow :
  next_turn opening_col6_reply_col0_red_col6_reply_col6_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col0_red_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col0_red_col6_reply_col6_state.
  unfold opening_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col6_red_col6_result_ongoing :
  get_result opening_col6_reply_col0_red_col6_reply_col6_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col0_red_col6_reply_col6_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state m)
       (c4_next opening_col6_reply_col0_red_col6_reply_col6_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col0_red_col6_reply_col6_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col0_red_col6_reply_col6_red_col6_result_ongoing.
  - unfold opening_col6_reply_col0_red_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col0_red_col6_reply_col6_state.
    unfold opening_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col0_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col6_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col6_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col0_red_col6_reply_col6_red_col6_state
                    opening_col6_reply_col0_red_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_reply_col6_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col6_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col0_red_col6_reply_col6_red_col6_state
                    opening_col6_reply_col0_red_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_reply_col6_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col0_red_col6_reply_col6_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col0_red_col6_reply_col6_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col6).

Lemma opening_col6_reply_col0_red_col6_reply_col6_red_col6_subgoals_imply_child :
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col0_red_col6_reply_col6_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col0_red_col6_reply_col6_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col6_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col0_red_col6_reply_col6_goal_if_red_col6_child.
  apply opening_col6_reply_col0_red_col6_reply_col6_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col0_raw_if_subgoals :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col0_red_col6_state col0).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col0_red_col6_reply_col0_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col0_red_col6_reply_col0_state
                  opening_col6_reply_col0_red_col6_reply_col0_result_ongoing
                  opening_col6_reply_col0_red_col6_reply_col0_turn_red)).
  exists opening_col6_reply_col0_red_col6_reply_col0_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col0_red_col6.
  - apply opening_col6_reply_col0_red_col6_reply_col0_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col1_raw_if_subgoals :
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col0_red_col6_state col1).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col0_red_col6_reply_col1_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col0_red_col6_reply_col1_state
                  opening_col6_reply_col0_red_col6_reply_col1_result_ongoing
                  opening_col6_reply_col0_red_col6_reply_col1_turn_red)).
  exists opening_col6_reply_col0_red_col6_reply_col1_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col1_red_col6.
  - apply opening_col6_reply_col0_red_col6_reply_col1_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col2_raw_if_subgoals :
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col0_red_col6_state col2).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col0_red_col6_reply_col2_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col0_red_col6_reply_col2_state
                  opening_col6_reply_col0_red_col6_reply_col2_result_ongoing
                  opening_col6_reply_col0_red_col6_reply_col2_turn_red)).
  exists opening_col6_reply_col0_red_col6_reply_col2_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col2_red_col6.
  - apply opening_col6_reply_col0_red_col6_reply_col2_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col3_raw_if_subgoals :
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col0_red_col6_state col3).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col0_red_col6_reply_col3_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col0_red_col6_reply_col3_state
                  opening_col6_reply_col0_red_col6_reply_col3_result_ongoing
                  opening_col6_reply_col0_red_col6_reply_col3_turn_red)).
  exists opening_col6_reply_col0_red_col6_reply_col3_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col3_red_col6.
  - apply opening_col6_reply_col0_red_col6_reply_col3_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col4_raw_if_subgoals :
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col0_red_col6_state col4).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col0_red_col6_reply_col4_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col0_red_col6_reply_col4_state
                  opening_col6_reply_col0_red_col6_reply_col4_result_ongoing
                  opening_col6_reply_col0_red_col6_reply_col4_turn_red)).
  exists opening_col6_reply_col0_red_col6_reply_col4_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col4_red_col6.
  - apply opening_col6_reply_col0_red_col6_reply_col4_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col5_raw_if_subgoals :
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col0_red_col6_state col5).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col0_red_col6_reply_col5_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col0_red_col6_reply_col5_state
                  opening_col6_reply_col0_red_col6_reply_col5_result_ongoing
                  opening_col6_reply_col0_red_col6_reply_col5_turn_red)).
  exists opening_col6_reply_col0_red_col6_reply_col5_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col5_red_col6.
  - apply opening_col6_reply_col0_red_col6_reply_col5_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col0_red_col6_reply_col6_raw_if_subgoals :
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col0_red_col6_state col6).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col0_red_col6_reply_col6_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col0_red_col6_reply_col6_state
                  opening_col6_reply_col0_red_col6_reply_col6_result_ongoing
                  opening_col6_reply_col0_red_col6_reply_col6_turn_red)).
  exists opening_col6_reply_col0_red_col6_reply_col6_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col0_red_col6_reply_col6_red_col6.
  - apply opening_col6_reply_col0_red_col6_reply_col6_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col0_raw_if_all_reply_subgoal_blocks :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 opening_col6_reply_col0_state.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  apply (proj2 (red_can_force_win_unfold_ongoing_red 39
                  opening_col6_reply_col0_state
                  opening_col6_reply_col0_result_ongoing
                  opening_col6_reply_col0_turn_red)).
  exists opening_col6_reply_col0_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col0_red_col6.
  - apply (proj2 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col0_red_col6_state
                    opening_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col0_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col0_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col0_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    destruct m.
    + apply opening_col6_reply_col0_red_col6_reply_col0_raw_if_subgoals; exact H0.
    + apply opening_col6_reply_col0_red_col6_reply_col1_raw_if_subgoals; exact H1.
    + apply opening_col6_reply_col0_red_col6_reply_col2_raw_if_subgoals; exact H2.
    + apply opening_col6_reply_col0_red_col6_reply_col3_raw_if_subgoals; exact H3.
    + apply opening_col6_reply_col0_red_col6_reply_col4_raw_if_subgoals; exact H4.
    + apply opening_col6_reply_col0_red_col6_reply_col5_raw_if_subgoals; exact H5.
    + apply opening_col6_reply_col0_red_col6_reply_col6_raw_if_subgoals; exact H6.
Qed.

Lemma opening_col6_reply_col0_goal_if_all_reply_subgoal_blocks :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col0_goal.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  apply opening_col6_reply_col0_raw_if_all_reply_subgoal_blocks; assumption.
Qed.

Lemma opening_col6_reply_col0_firstconj_if_all_reply_subgoal_blocks :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col0).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  change (red_can_force_win 40 opening_col6_reply_col0_state).
  apply opening_col6_reply_col0_raw_if_all_reply_subgoal_blocks; assumption.
Qed.

Lemma opening_col6_reply_col0_firstconj_if_col0col0_col6_and_other_reply_subgoal_blocks :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col0).
Proof.
  intros H00c6 H1 H2 H3 H4 H5 H6.
  apply opening_col6_reply_col0_firstconj_if_all_reply_subgoal_blocks.
  - apply opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals_if_col6.
    exact H00c6.
  - exact H1.
  - exact H2.
  - exact H3.
  - exact H4.
  - exact H5.
  - exact H6.
Qed.

Lemma opening_col6_reply_col0_firstconj_if_col0col0_col6_and_col0col1_col6_and_other_reply_subgoal_blocks :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col0).
Proof.
  intros H00c6 H01c6 H2 H3 H4 H5 H6.
  apply opening_col6_reply_col0_firstconj_if_col0col0_col6_and_other_reply_subgoal_blocks.
  - exact H00c6.
  - apply opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals_if_col6.
    exact H01c6.
  - exact H2.
  - exact H3.
  - exact H4.
  - exact H5.
  - exact H6.
Qed.

Lemma opening_col6_reply_col0_firstconj_if_col0col0to5_col6_and_col0col6_block :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col0).
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H6.
  apply opening_col6_reply_col0_firstconj_if_col0col0_col6_and_col0col1_col6_and_other_reply_subgoal_blocks.
  - exact H00c6.
  - exact H01c6.
  - apply opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals_if_col6.
    exact H02c6.
  - apply opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals_if_col6.
    exact H03c6.
  - apply opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals_if_col6.
    exact H04c6.
  - apply opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals_if_col6.
    exact H05c6.
  - exact H6.
Qed.

Lemma opening_col6_reply_subgoals_if_col0_all_reply_subgoal_blocks_and_rest_raw :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col1) ->
  red_can_force_win 40 (apply_move opening_col6_state col2) ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_reply_subgoals.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 Hr1 Hr2 Hr3 Hr4 Hr5 Hr6.
  apply opening_col6_reply_subgoals_if_col0_and_rest_raw.
  - apply opening_col6_reply_col0_firstconj_if_all_reply_subgoal_blocks; assumption.
  - exact Hr1.
  - exact Hr2.
  - exact Hr3.
  - exact Hr4.
  - exact Hr5.
  - exact Hr6.
Qed.

Lemma opening_col6_reply_subgoals_if_col0col0_col6_and_other_reply_subgoal_blocks_and_rest_raw :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col1) ->
  red_can_force_win 40 (apply_move opening_col6_state col2) ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_reply_subgoals.
Proof.
  intros H00c6 H1 H2 H3 H4 H5 H6 Hr1 Hr2 Hr3 Hr4 Hr5 Hr6.
  apply opening_col6_reply_subgoals_if_col0_and_rest_raw.
  - apply opening_col6_reply_col0_firstconj_if_col0col0_col6_and_other_reply_subgoal_blocks;
      assumption.
  - exact Hr1.
  - exact Hr2.
  - exact Hr3.
  - exact Hr4.
  - exact Hr5.
  - exact Hr6.
Qed.

Lemma opening_col6_reply_subgoals_if_col0col0_col6_and_col0col1_col6_and_other_reply_subgoal_blocks_and_rest_raw :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col1) ->
  red_can_force_win 40 (apply_move opening_col6_state col2) ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_reply_subgoals.
Proof.
  intros H00c6 H01c6 H2 H3 H4 H5 H6 Hr1 Hr2 Hr3 Hr4 Hr5 Hr6.
  apply opening_col6_reply_subgoals_if_col0_and_rest_raw.
  - apply opening_col6_reply_col0_firstconj_if_col0col0_col6_and_col0col1_col6_and_other_reply_subgoal_blocks;
      assumption.
  - exact Hr1.
  - exact Hr2.
  - exact Hr3.
  - exact Hr4.
  - exact Hr5.
  - exact Hr6.
Qed.

Lemma opening_col6_reply_subgoals_if_col0col0to5_col6_and_col0col6_block_and_rest_raw :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col1) ->
  red_can_force_win 40 (apply_move opening_col6_state col2) ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_reply_subgoals.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H6 Hr1 Hr2 Hr3 Hr4 Hr5 Hr6.
  apply opening_col6_reply_subgoals_if_col0_and_rest_raw.
  - apply opening_col6_reply_col0_firstconj_if_col0col0to5_col6_and_col0col6_block;
      assumption.
  - exact Hr1.
  - exact Hr2.
  - exact Hr3.
  - exact Hr4.
  - exact Hr5.
  - exact Hr6.
Qed.

Lemma opening_col6_target_if_col0_all_reply_subgoal_blocks_and_rest_raw :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col1) ->
  red_can_force_win 40 (apply_move opening_col6_state col2) ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_target.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6 Hr1 Hr2 Hr3 Hr4 Hr5 Hr6.
  apply opening_col6_target_if_reply_subgoals.
  apply opening_col6_reply_subgoals_if_col0_all_reply_subgoal_blocks_and_rest_raw;
    assumption.
Qed.

Lemma opening_col6_target_if_col0col0_col6_and_other_reply_subgoal_blocks_and_rest_raw :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col1) ->
  red_can_force_win 40 (apply_move opening_col6_state col2) ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_target.
Proof.
  intros H00c6 H1 H2 H3 H4 H5 H6 Hr1 Hr2 Hr3 Hr4 Hr5 Hr6.
  apply opening_col6_target_if_reply_subgoals.
  apply opening_col6_reply_subgoals_if_col0col0_col6_and_other_reply_subgoal_blocks_and_rest_raw;
    assumption.
Qed.

Lemma opening_col6_target_if_col0col0_col6_and_col0col1_col6_and_other_reply_subgoal_blocks_and_rest_raw :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col1) ->
  red_can_force_win 40 (apply_move opening_col6_state col2) ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_target.
Proof.
  intros H00c6 H01c6 H2 H3 H4 H5 H6 Hr1 Hr2 Hr3 Hr4 Hr5 Hr6.
  apply opening_col6_target_if_reply_subgoals.
  apply opening_col6_reply_subgoals_if_col0col0_col6_and_col0col1_col6_and_other_reply_subgoal_blocks_and_rest_raw;
    assumption.
Qed.

Lemma opening_col6_target_if_col0col0to5_col6_and_col0col6_block_and_rest_raw :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col1) ->
  red_can_force_win 40 (apply_move opening_col6_state col2) ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_target.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H6 Hr1 Hr2 Hr3 Hr4 Hr5 Hr6.
  apply opening_col6_target_if_reply_subgoals.
  apply opening_col6_reply_subgoals_if_col0col0to5_col6_and_col0col6_block_and_rest_raw;
    assumption.
Qed.

Definition opening_col6_reply_col1_state : game :=
  apply_move opening_col6_state col1.

Definition opening_col6_reply_col1_goal : Prop :=
  red_can_force_win 40 opening_col6_reply_col1_state.

Lemma opening_col6_reply_col1_turn_red :
  next_turn opening_col6_reply_col1_state = red.
Proof.
  unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_result_ongoing :
  get_result opening_col6_reply_col1_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_goal_unfold :
  opening_col6_reply_col1_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col1_state) /\
    red_can_force_win 39 g.
Proof.
  unfold opening_col6_reply_col1_goal.
  change 40 with (S 39).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col1_result_ongoing.
  - apply opening_col6_reply_col1_turn_red.
Qed.

Definition opening_col6_reply_col1_red_col6_state : game :=
  apply_move opening_col6_reply_col1_state col6.

Lemma in_c4_next_opening_col6_reply_col1_red_col6 :
  In opening_col6_reply_col1_red_col6_state
     (c4_next opening_col6_reply_col1_state).
Proof.
  unfold opening_col6_reply_col1_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col1_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col1_result_ongoing.
  - unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col1_goal_if_red_col6_child :
  red_can_force_win 39 opening_col6_reply_col1_red_col6_state ->
  opening_col6_reply_col1_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col1_goal_unfold).
  exists opening_col6_reply_col1_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col1_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col1_red_col6_turn_yellow :
  next_turn opening_col6_reply_col1_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_result_ongoing :
  get_result opening_col6_reply_col1_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col1_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col1_red_col6_state m)
       (c4_next opening_col6_reply_col1_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col1_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col1_red_col6_result_ongoing.
  - unfold opening_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col1_red_col6_move_form :
  red_can_force_win 39 opening_col6_reply_col1_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 38
      (apply_move opening_col6_reply_col1_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col1_red_col6_state
                    opening_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col1_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col1_red_col6_state
                    opening_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col1_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col1_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_subgoals : Prop :=
  red_can_force_win 38 (apply_move opening_col6_reply_col1_red_col6_state col0) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col1_red_col6_state col1) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col1_red_col6_state col2) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col1_red_col6_state col3) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col1_red_col6_state col4) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col1_red_col6_state col5) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col1_red_col6_state col6).

Lemma opening_col6_reply_col1_red_col6_subgoals_imply_child :
  opening_col6_reply_col1_red_col6_reply_subgoals ->
  red_can_force_win 39 opening_col6_reply_col1_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col1_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col1_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col1_goal_if_red_col6_child.
  apply opening_col6_reply_col1_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col0_state : game :=
  apply_move opening_col6_reply_col1_red_col6_state col0.

Definition opening_col6_reply_col1_red_col6_reply_col0_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col1_red_col6_reply_col0_state.

Lemma opening_col6_reply_col1_red_col6_reply_col0_turn_red :
  next_turn opening_col6_reply_col1_red_col6_reply_col0_state = red.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col0_state.
  unfold opening_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col0_result_ongoing :
  get_result opening_col6_reply_col1_red_col6_reply_col0_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col0_goal_unfold :
  opening_col6_reply_col1_red_col6_reply_col0_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col1_red_col6_reply_col0_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col0_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col1_red_col6_reply_col0_result_ongoing.
  - apply opening_col6_reply_col1_red_col6_reply_col0_turn_red.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col0_red_col6_state : game :=
  apply_move opening_col6_reply_col1_red_col6_reply_col0_state col6.

Lemma in_c4_next_opening_col6_reply_col1_red_col6_reply_col0_red_col6 :
  In opening_col6_reply_col1_red_col6_reply_col0_red_col6_state
     (c4_next opening_col6_reply_col1_red_col6_reply_col0_state).
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col0_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col1_red_col6_reply_col0_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col1_red_col6_reply_col0_result_ongoing.
  - unfold opening_col6_reply_col1_red_col6_reply_col0_state.
    unfold opening_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col0_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col0_red_col6_state ->
  opening_col6_reply_col1_red_col6_reply_col0_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col1_red_col6_reply_col0_goal_unfold).
  exists opening_col6_reply_col1_red_col6_reply_col0_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col0_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col0_red_col6_turn_yellow :
  next_turn opening_col6_reply_col1_red_col6_reply_col0_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col1_red_col6_reply_col0_state.
  unfold opening_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col0_red_col6_result_ongoing :
  get_result opening_col6_reply_col1_red_col6_reply_col0_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col1_red_col6_reply_col0_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state m)
       (c4_next opening_col6_reply_col1_red_col6_reply_col0_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col1_red_col6_reply_col0_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col1_red_col6_reply_col0_red_col6_result_ongoing.
  - unfold opening_col6_reply_col1_red_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col1_red_col6_reply_col0_state.
    unfold opening_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col0_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col0_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col1_red_col6_reply_col0_red_col6_state
                    opening_col6_reply_col1_red_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_reply_col0_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col0_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col1_red_col6_reply_col0_red_col6_state
                    opening_col6_reply_col1_red_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_reply_col0_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col1_red_col6_reply_col0_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col1_red_col6_reply_col0_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col6).

Lemma opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col0_red_col6_subgoals_imply_child :
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col0_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col1_red_col6_reply_col0_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col0_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col0_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col1_red_col6_reply_col0_goal_if_red_col6_child.
  apply opening_col6_reply_col1_red_col6_reply_col0_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col1_state : game :=
  apply_move opening_col6_reply_col1_red_col6_state col1.

Definition opening_col6_reply_col1_red_col6_reply_col1_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col1_red_col6_reply_col1_state.

Lemma opening_col6_reply_col1_red_col6_reply_col1_turn_red :
  next_turn opening_col6_reply_col1_red_col6_reply_col1_state = red.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col1_state.
  unfold opening_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col1_result_ongoing :
  get_result opening_col6_reply_col1_red_col6_reply_col1_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col1_goal_unfold :
  opening_col6_reply_col1_red_col6_reply_col1_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col1_red_col6_reply_col1_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col1_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col1_red_col6_reply_col1_result_ongoing.
  - apply opening_col6_reply_col1_red_col6_reply_col1_turn_red.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col1_red_col6_state : game :=
  apply_move opening_col6_reply_col1_red_col6_reply_col1_state col6.

Lemma in_c4_next_opening_col6_reply_col1_red_col6_reply_col1_red_col6 :
  In opening_col6_reply_col1_red_col6_reply_col1_red_col6_state
     (c4_next opening_col6_reply_col1_red_col6_reply_col1_state).
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col1_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col1_red_col6_reply_col1_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col1_red_col6_reply_col1_result_ongoing.
  - unfold opening_col6_reply_col1_red_col6_reply_col1_state.
    unfold opening_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col1_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col1_red_col6_state ->
  opening_col6_reply_col1_red_col6_reply_col1_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col1_red_col6_reply_col1_goal_unfold).
  exists opening_col6_reply_col1_red_col6_reply_col1_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col1_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col1_red_col6_turn_yellow :
  next_turn opening_col6_reply_col1_red_col6_reply_col1_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col1_red_col6_reply_col1_state.
  unfold opening_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col1_red_col6_result_ongoing :
  get_result opening_col6_reply_col1_red_col6_reply_col1_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col1_red_col6_reply_col1_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state m)
       (c4_next opening_col6_reply_col1_red_col6_reply_col1_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col1_red_col6_reply_col1_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col1_red_col6_reply_col1_red_col6_result_ongoing.
  - unfold opening_col6_reply_col1_red_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col1_red_col6_reply_col1_state.
    unfold opening_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col1_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col1_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col1_red_col6_reply_col1_red_col6_state
                    opening_col6_reply_col1_red_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_reply_col1_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col1_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col1_red_col6_reply_col1_red_col6_state
                    opening_col6_reply_col1_red_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_reply_col1_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col1_red_col6_reply_col1_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col1_red_col6_reply_col1_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6).

Lemma opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col1_red_col6_subgoals_imply_child :
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col1_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col1_red_col6_reply_col1_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col1_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col1_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col1_red_col6_reply_col1_goal_if_red_col6_child.
  apply opening_col6_reply_col1_red_col6_reply_col1_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col2_state : game :=
  apply_move opening_col6_reply_col1_red_col6_state col2.

Definition opening_col6_reply_col1_red_col6_reply_col2_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col1_red_col6_reply_col2_state.

Lemma opening_col6_reply_col1_red_col6_reply_col2_turn_red :
  next_turn opening_col6_reply_col1_red_col6_reply_col2_state = red.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col2_state.
  unfold opening_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col2_result_ongoing :
  get_result opening_col6_reply_col1_red_col6_reply_col2_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col2_goal_unfold :
  opening_col6_reply_col1_red_col6_reply_col2_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col1_red_col6_reply_col2_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col2_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col1_red_col6_reply_col2_result_ongoing.
  - apply opening_col6_reply_col1_red_col6_reply_col2_turn_red.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col2_red_col6_state : game :=
  apply_move opening_col6_reply_col1_red_col6_reply_col2_state col6.

Lemma in_c4_next_opening_col6_reply_col1_red_col6_reply_col2_red_col6 :
  In opening_col6_reply_col1_red_col6_reply_col2_red_col6_state
     (c4_next opening_col6_reply_col1_red_col6_reply_col2_state).
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col2_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col1_red_col6_reply_col2_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col1_red_col6_reply_col2_result_ongoing.
  - unfold opening_col6_reply_col1_red_col6_reply_col2_state.
    unfold opening_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col2_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col2_red_col6_state ->
  opening_col6_reply_col1_red_col6_reply_col2_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col1_red_col6_reply_col2_goal_unfold).
  exists opening_col6_reply_col1_red_col6_reply_col2_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col2_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col2_red_col6_turn_yellow :
  next_turn opening_col6_reply_col1_red_col6_reply_col2_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col1_red_col6_reply_col2_state.
  unfold opening_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col2_red_col6_result_ongoing :
  get_result opening_col6_reply_col1_red_col6_reply_col2_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col1_red_col6_reply_col2_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state m)
       (c4_next opening_col6_reply_col1_red_col6_reply_col2_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col1_red_col6_reply_col2_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col1_red_col6_reply_col2_red_col6_result_ongoing.
  - unfold opening_col6_reply_col1_red_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col1_red_col6_reply_col2_state.
    unfold opening_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col2_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col2_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col1_red_col6_reply_col2_red_col6_state
                    opening_col6_reply_col1_red_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_reply_col2_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col2_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col1_red_col6_reply_col2_red_col6_state
                    opening_col6_reply_col1_red_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_reply_col2_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col1_red_col6_reply_col2_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col1_red_col6_reply_col2_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6).

Lemma opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col2_red_col6_subgoals_imply_child :
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col2_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col1_red_col6_reply_col2_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col2_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col2_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col1_red_col6_reply_col2_goal_if_red_col6_child.
  apply opening_col6_reply_col1_red_col6_reply_col2_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col3_state : game :=
  apply_move opening_col6_reply_col1_red_col6_state col3.

Definition opening_col6_reply_col1_red_col6_reply_col3_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col1_red_col6_reply_col3_state.

Lemma opening_col6_reply_col1_red_col6_reply_col3_turn_red :
  next_turn opening_col6_reply_col1_red_col6_reply_col3_state = red.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col3_state.
  unfold opening_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col3_result_ongoing :
  get_result opening_col6_reply_col1_red_col6_reply_col3_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col3_goal_unfold :
  opening_col6_reply_col1_red_col6_reply_col3_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col1_red_col6_reply_col3_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col3_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col1_red_col6_reply_col3_result_ongoing.
  - apply opening_col6_reply_col1_red_col6_reply_col3_turn_red.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col3_red_col6_state : game :=
  apply_move opening_col6_reply_col1_red_col6_reply_col3_state col6.

Lemma in_c4_next_opening_col6_reply_col1_red_col6_reply_col3_red_col6 :
  In opening_col6_reply_col1_red_col6_reply_col3_red_col6_state
     (c4_next opening_col6_reply_col1_red_col6_reply_col3_state).
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col3_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col1_red_col6_reply_col3_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col1_red_col6_reply_col3_result_ongoing.
  - unfold opening_col6_reply_col1_red_col6_reply_col3_state.
    unfold opening_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col3_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col3_red_col6_state ->
  opening_col6_reply_col1_red_col6_reply_col3_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col1_red_col6_reply_col3_goal_unfold).
  exists opening_col6_reply_col1_red_col6_reply_col3_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col3_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col3_red_col6_turn_yellow :
  next_turn opening_col6_reply_col1_red_col6_reply_col3_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col1_red_col6_reply_col3_state.
  unfold opening_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col3_red_col6_result_ongoing :
  get_result opening_col6_reply_col1_red_col6_reply_col3_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col1_red_col6_reply_col3_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state m)
       (c4_next opening_col6_reply_col1_red_col6_reply_col3_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col1_red_col6_reply_col3_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col1_red_col6_reply_col3_red_col6_result_ongoing.
  - unfold opening_col6_reply_col1_red_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col1_red_col6_reply_col3_state.
    unfold opening_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col3_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col3_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col1_red_col6_reply_col3_red_col6_state
                    opening_col6_reply_col1_red_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_reply_col3_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col3_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col1_red_col6_reply_col3_red_col6_state
                    opening_col6_reply_col1_red_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_reply_col3_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col1_red_col6_reply_col3_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col1_red_col6_reply_col3_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6).

Lemma opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col3_red_col6_subgoals_imply_child :
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col3_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col1_red_col6_reply_col3_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col3_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col3_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col1_red_col6_reply_col3_goal_if_red_col6_child.
  apply opening_col6_reply_col1_red_col6_reply_col3_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col4_state : game :=
  apply_move opening_col6_reply_col1_red_col6_state col4.

Definition opening_col6_reply_col1_red_col6_reply_col4_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col1_red_col6_reply_col4_state.

Lemma opening_col6_reply_col1_red_col6_reply_col4_turn_red :
  next_turn opening_col6_reply_col1_red_col6_reply_col4_state = red.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col4_state.
  unfold opening_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col4_result_ongoing :
  get_result opening_col6_reply_col1_red_col6_reply_col4_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col4_goal_unfold :
  opening_col6_reply_col1_red_col6_reply_col4_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col1_red_col6_reply_col4_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col4_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col1_red_col6_reply_col4_result_ongoing.
  - apply opening_col6_reply_col1_red_col6_reply_col4_turn_red.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col4_red_col6_state : game :=
  apply_move opening_col6_reply_col1_red_col6_reply_col4_state col6.

Lemma in_c4_next_opening_col6_reply_col1_red_col6_reply_col4_red_col6 :
  In opening_col6_reply_col1_red_col6_reply_col4_red_col6_state
     (c4_next opening_col6_reply_col1_red_col6_reply_col4_state).
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col4_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col1_red_col6_reply_col4_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col1_red_col6_reply_col4_result_ongoing.
  - unfold opening_col6_reply_col1_red_col6_reply_col4_state.
    unfold opening_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col4_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col4_red_col6_state ->
  opening_col6_reply_col1_red_col6_reply_col4_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col1_red_col6_reply_col4_goal_unfold).
  exists opening_col6_reply_col1_red_col6_reply_col4_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col4_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col4_red_col6_turn_yellow :
  next_turn opening_col6_reply_col1_red_col6_reply_col4_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col1_red_col6_reply_col4_state.
  unfold opening_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col4_red_col6_result_ongoing :
  get_result opening_col6_reply_col1_red_col6_reply_col4_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col1_red_col6_reply_col4_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state m)
       (c4_next opening_col6_reply_col1_red_col6_reply_col4_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col1_red_col6_reply_col4_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col1_red_col6_reply_col4_red_col6_result_ongoing.
  - unfold opening_col6_reply_col1_red_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col1_red_col6_reply_col4_state.
    unfold opening_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col4_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col4_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col1_red_col6_reply_col4_red_col6_state
                    opening_col6_reply_col1_red_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_reply_col4_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col4_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col1_red_col6_reply_col4_red_col6_state
                    opening_col6_reply_col1_red_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_reply_col4_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col1_red_col6_reply_col4_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col1_red_col6_reply_col4_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6).

Lemma opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col4_red_col6_subgoals_imply_child :
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col4_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col1_red_col6_reply_col4_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col4_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col4_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col1_red_col6_reply_col4_goal_if_red_col6_child.
  apply opening_col6_reply_col1_red_col6_reply_col4_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col5_state : game :=
  apply_move opening_col6_reply_col1_red_col6_state col5.

Definition opening_col6_reply_col1_red_col6_reply_col5_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col1_red_col6_reply_col5_state.

Lemma opening_col6_reply_col1_red_col6_reply_col5_turn_red :
  next_turn opening_col6_reply_col1_red_col6_reply_col5_state = red.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col5_state.
  unfold opening_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col5_result_ongoing :
  get_result opening_col6_reply_col1_red_col6_reply_col5_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col5_goal_unfold :
  opening_col6_reply_col1_red_col6_reply_col5_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col1_red_col6_reply_col5_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col5_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col1_red_col6_reply_col5_result_ongoing.
  - apply opening_col6_reply_col1_red_col6_reply_col5_turn_red.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col5_red_col6_state : game :=
  apply_move opening_col6_reply_col1_red_col6_reply_col5_state col6.

Lemma in_c4_next_opening_col6_reply_col1_red_col6_reply_col5_red_col6 :
  In opening_col6_reply_col1_red_col6_reply_col5_red_col6_state
     (c4_next opening_col6_reply_col1_red_col6_reply_col5_state).
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col5_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col1_red_col6_reply_col5_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col1_red_col6_reply_col5_result_ongoing.
  - unfold opening_col6_reply_col1_red_col6_reply_col5_state.
    unfold opening_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col5_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col5_red_col6_state ->
  opening_col6_reply_col1_red_col6_reply_col5_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col1_red_col6_reply_col5_goal_unfold).
  exists opening_col6_reply_col1_red_col6_reply_col5_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col5_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col5_red_col6_turn_yellow :
  next_turn opening_col6_reply_col1_red_col6_reply_col5_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col1_red_col6_reply_col5_state.
  unfold opening_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col5_red_col6_result_ongoing :
  get_result opening_col6_reply_col1_red_col6_reply_col5_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col1_red_col6_reply_col5_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state m)
       (c4_next opening_col6_reply_col1_red_col6_reply_col5_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col1_red_col6_reply_col5_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col1_red_col6_reply_col5_red_col6_result_ongoing.
  - unfold opening_col6_reply_col1_red_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col1_red_col6_reply_col5_state.
    unfold opening_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col5_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col5_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col1_red_col6_reply_col5_red_col6_state
                    opening_col6_reply_col1_red_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_reply_col5_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col5_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col1_red_col6_reply_col5_red_col6_state
                    opening_col6_reply_col1_red_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_reply_col5_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col1_red_col6_reply_col5_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col1_red_col6_reply_col5_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6).

Lemma opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col5_red_col6_subgoals_imply_child :
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col5_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col1_red_col6_reply_col5_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col5_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col5_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col1_red_col6_reply_col5_goal_if_red_col6_child.
  apply opening_col6_reply_col1_red_col6_reply_col5_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col6_state : game :=
  apply_move opening_col6_reply_col1_red_col6_state col6.

Definition opening_col6_reply_col1_red_col6_reply_col6_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col1_red_col6_reply_col6_state.

Lemma opening_col6_reply_col1_red_col6_reply_col6_turn_red :
  next_turn opening_col6_reply_col1_red_col6_reply_col6_state = red.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col6_state.
  unfold opening_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col6_result_ongoing :
  get_result opening_col6_reply_col1_red_col6_reply_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col6_goal_unfold :
  opening_col6_reply_col1_red_col6_reply_col6_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col1_red_col6_reply_col6_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col6_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col1_red_col6_reply_col6_result_ongoing.
  - apply opening_col6_reply_col1_red_col6_reply_col6_turn_red.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col6_red_col6_state : game :=
  apply_move opening_col6_reply_col1_red_col6_reply_col6_state col6.

Lemma in_c4_next_opening_col6_reply_col1_red_col6_reply_col6_red_col6 :
  In opening_col6_reply_col1_red_col6_reply_col6_red_col6_state
     (c4_next opening_col6_reply_col1_red_col6_reply_col6_state).
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col6_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col1_red_col6_reply_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col1_red_col6_reply_col6_result_ongoing.
  - unfold opening_col6_reply_col1_red_col6_reply_col6_state.
    unfold opening_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col6_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col6_red_col6_state ->
  opening_col6_reply_col1_red_col6_reply_col6_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col1_red_col6_reply_col6_goal_unfold).
  exists opening_col6_reply_col1_red_col6_reply_col6_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col6_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col6_red_col6_turn_yellow :
  next_turn opening_col6_reply_col1_red_col6_reply_col6_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col1_red_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col1_red_col6_reply_col6_state.
  unfold opening_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col6_red_col6_result_ongoing :
  get_result opening_col6_reply_col1_red_col6_reply_col6_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col1_red_col6_reply_col6_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state m)
       (c4_next opening_col6_reply_col1_red_col6_reply_col6_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col1_red_col6_reply_col6_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col1_red_col6_reply_col6_red_col6_result_ongoing.
  - unfold opening_col6_reply_col1_red_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col1_red_col6_reply_col6_state.
    unfold opening_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col1_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col6_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col6_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col1_red_col6_reply_col6_red_col6_state
                    opening_col6_reply_col1_red_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_reply_col6_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col6_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col1_red_col6_reply_col6_red_col6_state
                    opening_col6_reply_col1_red_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_reply_col6_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col1_red_col6_reply_col6_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col1_red_col6_reply_col6_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col6).

Lemma opening_col6_reply_col1_red_col6_reply_col6_red_col6_subgoals_imply_child :
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col1_red_col6_reply_col6_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col1_red_col6_reply_col6_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col6_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col6_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col1_red_col6_reply_col6_goal_if_red_col6_child.
  apply opening_col6_reply_col1_red_col6_reply_col6_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col0_raw_if_subgoals :
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col1_red_col6_state col0).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col1_red_col6_reply_col0_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col1_red_col6_reply_col0_state
                  opening_col6_reply_col1_red_col6_reply_col0_result_ongoing
                  opening_col6_reply_col1_red_col6_reply_col0_turn_red)).
  exists opening_col6_reply_col1_red_col6_reply_col0_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col0_red_col6.
  - apply opening_col6_reply_col1_red_col6_reply_col0_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col1_raw_if_subgoals :
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col1_red_col6_state col1).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col1_red_col6_reply_col1_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col1_red_col6_reply_col1_state
                  opening_col6_reply_col1_red_col6_reply_col1_result_ongoing
                  opening_col6_reply_col1_red_col6_reply_col1_turn_red)).
  exists opening_col6_reply_col1_red_col6_reply_col1_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col1_red_col6.
  - apply opening_col6_reply_col1_red_col6_reply_col1_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col2_raw_if_subgoals :
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col1_red_col6_state col2).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col1_red_col6_reply_col2_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col1_red_col6_reply_col2_state
                  opening_col6_reply_col1_red_col6_reply_col2_result_ongoing
                  opening_col6_reply_col1_red_col6_reply_col2_turn_red)).
  exists opening_col6_reply_col1_red_col6_reply_col2_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col2_red_col6.
  - apply opening_col6_reply_col1_red_col6_reply_col2_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col3_raw_if_subgoals :
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col1_red_col6_state col3).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col1_red_col6_reply_col3_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col1_red_col6_reply_col3_state
                  opening_col6_reply_col1_red_col6_reply_col3_result_ongoing
                  opening_col6_reply_col1_red_col6_reply_col3_turn_red)).
  exists opening_col6_reply_col1_red_col6_reply_col3_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col3_red_col6.
  - apply opening_col6_reply_col1_red_col6_reply_col3_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col4_raw_if_subgoals :
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col1_red_col6_state col4).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col1_red_col6_reply_col4_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col1_red_col6_reply_col4_state
                  opening_col6_reply_col1_red_col6_reply_col4_result_ongoing
                  opening_col6_reply_col1_red_col6_reply_col4_turn_red)).
  exists opening_col6_reply_col1_red_col6_reply_col4_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col4_red_col6.
  - apply opening_col6_reply_col1_red_col6_reply_col4_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col5_raw_if_subgoals :
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col1_red_col6_state col5).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col1_red_col6_reply_col5_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col1_red_col6_reply_col5_state
                  opening_col6_reply_col1_red_col6_reply_col5_result_ongoing
                  opening_col6_reply_col1_red_col6_reply_col5_turn_red)).
  exists opening_col6_reply_col1_red_col6_reply_col5_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col5_red_col6.
  - apply opening_col6_reply_col1_red_col6_reply_col5_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col1_red_col6_reply_col6_raw_if_subgoals :
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col1_red_col6_state col6).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col1_red_col6_reply_col6_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col1_red_col6_reply_col6_state
                  opening_col6_reply_col1_red_col6_reply_col6_result_ongoing
                  opening_col6_reply_col1_red_col6_reply_col6_turn_red)).
  exists opening_col6_reply_col1_red_col6_reply_col6_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col1_red_col6_reply_col6_red_col6.
  - apply opening_col6_reply_col1_red_col6_reply_col6_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col1_raw_if_all_reply_subgoal_blocks :
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 opening_col6_reply_col1_state.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  apply (proj2 (red_can_force_win_unfold_ongoing_red 39
                  opening_col6_reply_col1_state
                  opening_col6_reply_col1_result_ongoing
                  opening_col6_reply_col1_turn_red)).
  exists opening_col6_reply_col1_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col1_red_col6.
  - apply (proj2 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col1_red_col6_state
                    opening_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col1_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col1_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col1_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    destruct m.
    + apply opening_col6_reply_col1_red_col6_reply_col0_raw_if_subgoals; exact H0.
    + apply opening_col6_reply_col1_red_col6_reply_col1_raw_if_subgoals; exact H1.
    + apply opening_col6_reply_col1_red_col6_reply_col2_raw_if_subgoals; exact H2.
    + apply opening_col6_reply_col1_red_col6_reply_col3_raw_if_subgoals; exact H3.
    + apply opening_col6_reply_col1_red_col6_reply_col4_raw_if_subgoals; exact H4.
    + apply opening_col6_reply_col1_red_col6_reply_col5_raw_if_subgoals; exact H5.
    + apply opening_col6_reply_col1_red_col6_reply_col6_raw_if_subgoals; exact H6.
Qed.

Lemma opening_col6_reply_col1_goal_if_all_reply_subgoal_blocks :
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col1_goal.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  apply opening_col6_reply_col1_raw_if_all_reply_subgoal_blocks; assumption.
Qed.

Lemma opening_col6_reply_col1_firstconj_if_all_reply_subgoal_blocks :
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col1).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  change (red_can_force_win 40 opening_col6_reply_col1_state).
  apply opening_col6_reply_col1_raw_if_all_reply_subgoal_blocks; assumption.
Qed.

Lemma opening_col6_reply_col1_firstconj_if_col1col0to5_col6_and_col1col6_block :
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col1).
Proof.
  intros H10c6 H11c6 H12c6 H13c6 H14c6 H15c6 H16.
  apply opening_col6_reply_col1_firstconj_if_all_reply_subgoal_blocks.
  - apply opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals_if_col6.
    exact H10c6.
  - apply opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals_if_col6.
    exact H11c6.
  - apply opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals_if_col6.
    exact H12c6.
  - apply opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals_if_col6.
    exact H13c6.
  - apply opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals_if_col6.
    exact H14c6.
  - apply opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals_if_col6.
    exact H15c6.
  - exact H16.
Qed.

Definition opening_col6_reply_col2_state : game :=
  apply_move opening_col6_state col2.

Definition opening_col6_reply_col2_goal : Prop :=
  red_can_force_win 40 opening_col6_reply_col2_state.

Lemma opening_col6_reply_col2_turn_red :
  next_turn opening_col6_reply_col2_state = red.
Proof.
  unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_result_ongoing :
  get_result opening_col6_reply_col2_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_goal_unfold :
  opening_col6_reply_col2_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col2_state) /\
    red_can_force_win 39 g.
Proof.
  unfold opening_col6_reply_col2_goal.
  change 40 with (S 39).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col2_result_ongoing.
  - apply opening_col6_reply_col2_turn_red.
Qed.

Definition opening_col6_reply_col2_red_col6_state : game :=
  apply_move opening_col6_reply_col2_state col6.

Lemma in_c4_next_opening_col6_reply_col2_red_col6 :
  In opening_col6_reply_col2_red_col6_state
     (c4_next opening_col6_reply_col2_state).
Proof.
  unfold opening_col6_reply_col2_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col2_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col2_result_ongoing.
  - unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col2_goal_if_red_col6_child :
  red_can_force_win 39 opening_col6_reply_col2_red_col6_state ->
  opening_col6_reply_col2_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col2_goal_unfold).
  exists opening_col6_reply_col2_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col2_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col2_red_col6_turn_yellow :
  next_turn opening_col6_reply_col2_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_result_ongoing :
  get_result opening_col6_reply_col2_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col2_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col2_red_col6_state m)
       (c4_next opening_col6_reply_col2_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col2_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col2_red_col6_result_ongoing.
  - unfold opening_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col2_red_col6_move_form :
  red_can_force_win 39 opening_col6_reply_col2_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 38
      (apply_move opening_col6_reply_col2_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col2_red_col6_state
                    opening_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col2_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col2_red_col6_state
                    opening_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col2_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col2_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_subgoals : Prop :=
  red_can_force_win 38 (apply_move opening_col6_reply_col2_red_col6_state col0) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col2_red_col6_state col1) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col2_red_col6_state col2) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col2_red_col6_state col3) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col2_red_col6_state col4) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col2_red_col6_state col5) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col2_red_col6_state col6).

Lemma opening_col6_reply_col2_red_col6_subgoals_imply_child :
  opening_col6_reply_col2_red_col6_reply_subgoals ->
  red_can_force_win 39 opening_col6_reply_col2_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col2_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col2_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col2_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col2_goal_if_red_col6_child.
  apply opening_col6_reply_col2_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col0_state : game :=
  apply_move opening_col6_reply_col2_red_col6_state col0.

Definition opening_col6_reply_col2_red_col6_reply_col0_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col2_red_col6_reply_col0_state.

Lemma opening_col6_reply_col2_red_col6_reply_col0_turn_red :
  next_turn opening_col6_reply_col2_red_col6_reply_col0_state = red.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col0_state.
  unfold opening_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col0_result_ongoing :
  get_result opening_col6_reply_col2_red_col6_reply_col0_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col0_goal_unfold :
  opening_col6_reply_col2_red_col6_reply_col0_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col2_red_col6_reply_col0_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col0_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col2_red_col6_reply_col0_result_ongoing.
  - apply opening_col6_reply_col2_red_col6_reply_col0_turn_red.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col0_red_col6_state : game :=
  apply_move opening_col6_reply_col2_red_col6_reply_col0_state col6.

Lemma in_c4_next_opening_col6_reply_col2_red_col6_reply_col0_red_col6 :
  In opening_col6_reply_col2_red_col6_reply_col0_red_col6_state
     (c4_next opening_col6_reply_col2_red_col6_reply_col0_state).
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col0_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col2_red_col6_reply_col0_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col2_red_col6_reply_col0_result_ongoing.
  - unfold opening_col6_reply_col2_red_col6_reply_col0_state.
    unfold opening_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col0_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col0_red_col6_state ->
  opening_col6_reply_col2_red_col6_reply_col0_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col2_red_col6_reply_col0_goal_unfold).
  exists opening_col6_reply_col2_red_col6_reply_col0_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col0_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col0_red_col6_turn_yellow :
  next_turn opening_col6_reply_col2_red_col6_reply_col0_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col2_red_col6_reply_col0_state.
  unfold opening_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col0_red_col6_result_ongoing :
  get_result opening_col6_reply_col2_red_col6_reply_col0_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col2_red_col6_reply_col0_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state m)
       (c4_next opening_col6_reply_col2_red_col6_reply_col0_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col2_red_col6_reply_col0_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col2_red_col6_reply_col0_red_col6_result_ongoing.
  - unfold opening_col6_reply_col2_red_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col2_red_col6_reply_col0_state.
    unfold opening_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col0_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col0_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col2_red_col6_reply_col0_red_col6_state
                    opening_col6_reply_col2_red_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_reply_col0_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col0_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col2_red_col6_reply_col0_red_col6_state
                    opening_col6_reply_col2_red_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_reply_col0_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col2_red_col6_reply_col0_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col2_red_col6_reply_col0_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col6).

Lemma opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col0_red_col6_subgoals_imply_child :
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col0_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col2_red_col6_reply_col0_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col0_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col0_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col2_red_col6_reply_col0_goal_if_red_col6_child.
  apply opening_col6_reply_col2_red_col6_reply_col0_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col1_state : game :=
  apply_move opening_col6_reply_col2_red_col6_state col1.

Definition opening_col6_reply_col2_red_col6_reply_col1_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col2_red_col6_reply_col1_state.

Lemma opening_col6_reply_col2_red_col6_reply_col1_turn_red :
  next_turn opening_col6_reply_col2_red_col6_reply_col1_state = red.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col1_state.
  unfold opening_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col1_result_ongoing :
  get_result opening_col6_reply_col2_red_col6_reply_col1_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col1_goal_unfold :
  opening_col6_reply_col2_red_col6_reply_col1_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col2_red_col6_reply_col1_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col1_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col2_red_col6_reply_col1_result_ongoing.
  - apply opening_col6_reply_col2_red_col6_reply_col1_turn_red.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col1_red_col6_state : game :=
  apply_move opening_col6_reply_col2_red_col6_reply_col1_state col6.

Lemma in_c4_next_opening_col6_reply_col2_red_col6_reply_col1_red_col6 :
  In opening_col6_reply_col2_red_col6_reply_col1_red_col6_state
     (c4_next opening_col6_reply_col2_red_col6_reply_col1_state).
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col1_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col2_red_col6_reply_col1_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col2_red_col6_reply_col1_result_ongoing.
  - unfold opening_col6_reply_col2_red_col6_reply_col1_state.
    unfold opening_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col1_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col1_red_col6_state ->
  opening_col6_reply_col2_red_col6_reply_col1_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col2_red_col6_reply_col1_goal_unfold).
  exists opening_col6_reply_col2_red_col6_reply_col1_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col1_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col1_red_col6_turn_yellow :
  next_turn opening_col6_reply_col2_red_col6_reply_col1_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col2_red_col6_reply_col1_state.
  unfold opening_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col1_red_col6_result_ongoing :
  get_result opening_col6_reply_col2_red_col6_reply_col1_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col2_red_col6_reply_col1_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state m)
       (c4_next opening_col6_reply_col2_red_col6_reply_col1_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col2_red_col6_reply_col1_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col2_red_col6_reply_col1_red_col6_result_ongoing.
  - unfold opening_col6_reply_col2_red_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col2_red_col6_reply_col1_state.
    unfold opening_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col1_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col1_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col2_red_col6_reply_col1_red_col6_state
                    opening_col6_reply_col2_red_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_reply_col1_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col1_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col2_red_col6_reply_col1_red_col6_state
                    opening_col6_reply_col2_red_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_reply_col1_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col2_red_col6_reply_col1_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col2_red_col6_reply_col1_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col6).

Lemma opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col1_red_col6_subgoals_imply_child :
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col1_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col2_red_col6_reply_col1_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col1_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col1_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col2_red_col6_reply_col1_goal_if_red_col6_child.
  apply opening_col6_reply_col2_red_col6_reply_col1_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col2_state : game :=
  apply_move opening_col6_reply_col2_red_col6_state col2.

Definition opening_col6_reply_col2_red_col6_reply_col2_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col2_red_col6_reply_col2_state.

Lemma opening_col6_reply_col2_red_col6_reply_col2_turn_red :
  next_turn opening_col6_reply_col2_red_col6_reply_col2_state = red.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col2_state.
  unfold opening_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col2_result_ongoing :
  get_result opening_col6_reply_col2_red_col6_reply_col2_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col2_goal_unfold :
  opening_col6_reply_col2_red_col6_reply_col2_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col2_red_col6_reply_col2_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col2_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col2_red_col6_reply_col2_result_ongoing.
  - apply opening_col6_reply_col2_red_col6_reply_col2_turn_red.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col2_red_col6_state : game :=
  apply_move opening_col6_reply_col2_red_col6_reply_col2_state col6.

Lemma in_c4_next_opening_col6_reply_col2_red_col6_reply_col2_red_col6 :
  In opening_col6_reply_col2_red_col6_reply_col2_red_col6_state
     (c4_next opening_col6_reply_col2_red_col6_reply_col2_state).
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col2_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col2_red_col6_reply_col2_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col2_red_col6_reply_col2_result_ongoing.
  - unfold opening_col6_reply_col2_red_col6_reply_col2_state.
    unfold opening_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col2_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col2_red_col6_state ->
  opening_col6_reply_col2_red_col6_reply_col2_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col2_red_col6_reply_col2_goal_unfold).
  exists opening_col6_reply_col2_red_col6_reply_col2_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col2_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col2_red_col6_turn_yellow :
  next_turn opening_col6_reply_col2_red_col6_reply_col2_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col2_red_col6_reply_col2_state.
  unfold opening_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col2_red_col6_result_ongoing :
  get_result opening_col6_reply_col2_red_col6_reply_col2_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col2_red_col6_reply_col2_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state m)
       (c4_next opening_col6_reply_col2_red_col6_reply_col2_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col2_red_col6_reply_col2_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col2_red_col6_reply_col2_red_col6_result_ongoing.
  - unfold opening_col6_reply_col2_red_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col2_red_col6_reply_col2_state.
    unfold opening_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col2_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col2_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col2_red_col6_reply_col2_red_col6_state
                    opening_col6_reply_col2_red_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_reply_col2_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col2_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col2_red_col6_reply_col2_red_col6_state
                    opening_col6_reply_col2_red_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_reply_col2_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col2_red_col6_reply_col2_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col2_red_col6_reply_col2_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col6).

Lemma opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col2_red_col6_subgoals_imply_child :
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col2_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col2_red_col6_reply_col2_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col2_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col2_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col2_red_col6_reply_col2_goal_if_red_col6_child.
  apply opening_col6_reply_col2_red_col6_reply_col2_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col3_state : game :=
  apply_move opening_col6_reply_col2_red_col6_state col3.

Definition opening_col6_reply_col2_red_col6_reply_col3_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col2_red_col6_reply_col3_state.

Lemma opening_col6_reply_col2_red_col6_reply_col3_turn_red :
  next_turn opening_col6_reply_col2_red_col6_reply_col3_state = red.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col3_state.
  unfold opening_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col3_result_ongoing :
  get_result opening_col6_reply_col2_red_col6_reply_col3_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col3_goal_unfold :
  opening_col6_reply_col2_red_col6_reply_col3_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col2_red_col6_reply_col3_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col3_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col2_red_col6_reply_col3_result_ongoing.
  - apply opening_col6_reply_col2_red_col6_reply_col3_turn_red.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col3_red_col6_state : game :=
  apply_move opening_col6_reply_col2_red_col6_reply_col3_state col6.

Lemma in_c4_next_opening_col6_reply_col2_red_col6_reply_col3_red_col6 :
  In opening_col6_reply_col2_red_col6_reply_col3_red_col6_state
     (c4_next opening_col6_reply_col2_red_col6_reply_col3_state).
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col3_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col2_red_col6_reply_col3_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col2_red_col6_reply_col3_result_ongoing.
  - unfold opening_col6_reply_col2_red_col6_reply_col3_state.
    unfold opening_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col3_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col3_red_col6_state ->
  opening_col6_reply_col2_red_col6_reply_col3_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col2_red_col6_reply_col3_goal_unfold).
  exists opening_col6_reply_col2_red_col6_reply_col3_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col3_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col3_red_col6_turn_yellow :
  next_turn opening_col6_reply_col2_red_col6_reply_col3_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col2_red_col6_reply_col3_state.
  unfold opening_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col3_red_col6_result_ongoing :
  get_result opening_col6_reply_col2_red_col6_reply_col3_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col2_red_col6_reply_col3_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state m)
       (c4_next opening_col6_reply_col2_red_col6_reply_col3_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col2_red_col6_reply_col3_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col2_red_col6_reply_col3_red_col6_result_ongoing.
  - unfold opening_col6_reply_col2_red_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col2_red_col6_reply_col3_state.
    unfold opening_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col3_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col3_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col2_red_col6_reply_col3_red_col6_state
                    opening_col6_reply_col2_red_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_reply_col3_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col3_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col2_red_col6_reply_col3_red_col6_state
                    opening_col6_reply_col2_red_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_reply_col3_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col2_red_col6_reply_col3_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col2_red_col6_reply_col3_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6).

Lemma opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col3_red_col6_subgoals_imply_child :
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col3_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col2_red_col6_reply_col3_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col3_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col3_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col2_red_col6_reply_col3_goal_if_red_col6_child.
  apply opening_col6_reply_col2_red_col6_reply_col3_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col4_state : game :=
  apply_move opening_col6_reply_col2_red_col6_state col4.

Definition opening_col6_reply_col2_red_col6_reply_col4_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col2_red_col6_reply_col4_state.

Lemma opening_col6_reply_col2_red_col6_reply_col4_turn_red :
  next_turn opening_col6_reply_col2_red_col6_reply_col4_state = red.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col4_state.
  unfold opening_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col4_result_ongoing :
  get_result opening_col6_reply_col2_red_col6_reply_col4_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col4_goal_unfold :
  opening_col6_reply_col2_red_col6_reply_col4_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col2_red_col6_reply_col4_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col4_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col2_red_col6_reply_col4_result_ongoing.
  - apply opening_col6_reply_col2_red_col6_reply_col4_turn_red.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col4_red_col6_state : game :=
  apply_move opening_col6_reply_col2_red_col6_reply_col4_state col6.

Lemma in_c4_next_opening_col6_reply_col2_red_col6_reply_col4_red_col6 :
  In opening_col6_reply_col2_red_col6_reply_col4_red_col6_state
     (c4_next opening_col6_reply_col2_red_col6_reply_col4_state).
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col4_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col2_red_col6_reply_col4_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col2_red_col6_reply_col4_result_ongoing.
  - unfold opening_col6_reply_col2_red_col6_reply_col4_state.
    unfold opening_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col4_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col4_red_col6_state ->
  opening_col6_reply_col2_red_col6_reply_col4_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col2_red_col6_reply_col4_goal_unfold).
  exists opening_col6_reply_col2_red_col6_reply_col4_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col4_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col4_red_col6_turn_yellow :
  next_turn opening_col6_reply_col2_red_col6_reply_col4_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col2_red_col6_reply_col4_state.
  unfold opening_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col4_red_col6_result_ongoing :
  get_result opening_col6_reply_col2_red_col6_reply_col4_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col2_red_col6_reply_col4_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state m)
       (c4_next opening_col6_reply_col2_red_col6_reply_col4_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col2_red_col6_reply_col4_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col2_red_col6_reply_col4_red_col6_result_ongoing.
  - unfold opening_col6_reply_col2_red_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col2_red_col6_reply_col4_state.
    unfold opening_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col4_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col4_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col2_red_col6_reply_col4_red_col6_state
                    opening_col6_reply_col2_red_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_reply_col4_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col4_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col2_red_col6_reply_col4_red_col6_state
                    opening_col6_reply_col2_red_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_reply_col4_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col2_red_col6_reply_col4_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col2_red_col6_reply_col4_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6).

Lemma opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col4_red_col6_subgoals_imply_child :
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col4_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col2_red_col6_reply_col4_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col4_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col4_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col2_red_col6_reply_col4_goal_if_red_col6_child.
  apply opening_col6_reply_col2_red_col6_reply_col4_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col5_state : game :=
  apply_move opening_col6_reply_col2_red_col6_state col5.

Definition opening_col6_reply_col2_red_col6_reply_col5_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col2_red_col6_reply_col5_state.

Lemma opening_col6_reply_col2_red_col6_reply_col5_turn_red :
  next_turn opening_col6_reply_col2_red_col6_reply_col5_state = red.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col5_state.
  unfold opening_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col5_result_ongoing :
  get_result opening_col6_reply_col2_red_col6_reply_col5_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col5_goal_unfold :
  opening_col6_reply_col2_red_col6_reply_col5_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col2_red_col6_reply_col5_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col5_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col2_red_col6_reply_col5_result_ongoing.
  - apply opening_col6_reply_col2_red_col6_reply_col5_turn_red.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col5_red_col6_state : game :=
  apply_move opening_col6_reply_col2_red_col6_reply_col5_state col6.

Lemma in_c4_next_opening_col6_reply_col2_red_col6_reply_col5_red_col6 :
  In opening_col6_reply_col2_red_col6_reply_col5_red_col6_state
     (c4_next opening_col6_reply_col2_red_col6_reply_col5_state).
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col5_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col2_red_col6_reply_col5_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col2_red_col6_reply_col5_result_ongoing.
  - unfold opening_col6_reply_col2_red_col6_reply_col5_state.
    unfold opening_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col5_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col5_red_col6_state ->
  opening_col6_reply_col2_red_col6_reply_col5_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col2_red_col6_reply_col5_goal_unfold).
  exists opening_col6_reply_col2_red_col6_reply_col5_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col5_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col5_red_col6_turn_yellow :
  next_turn opening_col6_reply_col2_red_col6_reply_col5_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col2_red_col6_reply_col5_state.
  unfold opening_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col5_red_col6_result_ongoing :
  get_result opening_col6_reply_col2_red_col6_reply_col5_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col2_red_col6_reply_col5_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state m)
       (c4_next opening_col6_reply_col2_red_col6_reply_col5_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col2_red_col6_reply_col5_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col2_red_col6_reply_col5_red_col6_result_ongoing.
  - unfold opening_col6_reply_col2_red_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col2_red_col6_reply_col5_state.
    unfold opening_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col5_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col5_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col2_red_col6_reply_col5_red_col6_state
                    opening_col6_reply_col2_red_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_reply_col5_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col5_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col2_red_col6_reply_col5_red_col6_state
                    opening_col6_reply_col2_red_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_reply_col5_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col2_red_col6_reply_col5_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col2_red_col6_reply_col5_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6).

Lemma opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col5_red_col6_subgoals_imply_child :
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col5_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col2_red_col6_reply_col5_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col5_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col5_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col2_red_col6_reply_col5_goal_if_red_col6_child.
  apply opening_col6_reply_col2_red_col6_reply_col5_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col6_state : game :=
  apply_move opening_col6_reply_col2_red_col6_state col6.

Definition opening_col6_reply_col2_red_col6_reply_col6_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col2_red_col6_reply_col6_state.

Lemma opening_col6_reply_col2_red_col6_reply_col6_turn_red :
  next_turn opening_col6_reply_col2_red_col6_reply_col6_state = red.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col6_state.
  unfold opening_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col6_result_ongoing :
  get_result opening_col6_reply_col2_red_col6_reply_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col6_goal_unfold :
  opening_col6_reply_col2_red_col6_reply_col6_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col2_red_col6_reply_col6_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col6_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col2_red_col6_reply_col6_result_ongoing.
  - apply opening_col6_reply_col2_red_col6_reply_col6_turn_red.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col6_red_col6_state : game :=
  apply_move opening_col6_reply_col2_red_col6_reply_col6_state col6.

Lemma in_c4_next_opening_col6_reply_col2_red_col6_reply_col6_red_col6 :
  In opening_col6_reply_col2_red_col6_reply_col6_red_col6_state
     (c4_next opening_col6_reply_col2_red_col6_reply_col6_state).
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col6_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col2_red_col6_reply_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col2_red_col6_reply_col6_result_ongoing.
  - unfold opening_col6_reply_col2_red_col6_reply_col6_state.
    unfold opening_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col6_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col6_red_col6_state ->
  opening_col6_reply_col2_red_col6_reply_col6_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col2_red_col6_reply_col6_goal_unfold).
  exists opening_col6_reply_col2_red_col6_reply_col6_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col6_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col6_red_col6_turn_yellow :
  next_turn opening_col6_reply_col2_red_col6_reply_col6_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col2_red_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col2_red_col6_reply_col6_state.
  unfold opening_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col6_red_col6_result_ongoing :
  get_result opening_col6_reply_col2_red_col6_reply_col6_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col2_red_col6_reply_col6_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state m)
       (c4_next opening_col6_reply_col2_red_col6_reply_col6_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col2_red_col6_reply_col6_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col2_red_col6_reply_col6_red_col6_result_ongoing.
  - unfold opening_col6_reply_col2_red_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col2_red_col6_reply_col6_state.
    unfold opening_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col2_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col6_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col6_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col2_red_col6_reply_col6_red_col6_state
                    opening_col6_reply_col2_red_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_reply_col6_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col6_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col2_red_col6_reply_col6_red_col6_state
                    opening_col6_reply_col2_red_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_reply_col6_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col2_red_col6_reply_col6_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col2_red_col6_reply_col6_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col6).

Lemma opening_col6_reply_col2_red_col6_reply_col6_red_col6_subgoals_imply_child :
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col2_red_col6_reply_col6_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col2_red_col6_reply_col6_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col6_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col6_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col2_red_col6_reply_col6_goal_if_red_col6_child.
  apply opening_col6_reply_col2_red_col6_reply_col6_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col0_raw_if_subgoals :
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col2_red_col6_state col0).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col2_red_col6_reply_col0_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col2_red_col6_reply_col0_state
                  opening_col6_reply_col2_red_col6_reply_col0_result_ongoing
                  opening_col6_reply_col2_red_col6_reply_col0_turn_red)).
  exists opening_col6_reply_col2_red_col6_reply_col0_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col0_red_col6.
  - apply opening_col6_reply_col2_red_col6_reply_col0_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col1_raw_if_subgoals :
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col2_red_col6_state col1).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col2_red_col6_reply_col1_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col2_red_col6_reply_col1_state
                  opening_col6_reply_col2_red_col6_reply_col1_result_ongoing
                  opening_col6_reply_col2_red_col6_reply_col1_turn_red)).
  exists opening_col6_reply_col2_red_col6_reply_col1_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col1_red_col6.
  - apply opening_col6_reply_col2_red_col6_reply_col1_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col2_raw_if_subgoals :
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col2_red_col6_state col2).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col2_red_col6_reply_col2_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col2_red_col6_reply_col2_state
                  opening_col6_reply_col2_red_col6_reply_col2_result_ongoing
                  opening_col6_reply_col2_red_col6_reply_col2_turn_red)).
  exists opening_col6_reply_col2_red_col6_reply_col2_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col2_red_col6.
  - apply opening_col6_reply_col2_red_col6_reply_col2_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col3_raw_if_subgoals :
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col2_red_col6_state col3).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col2_red_col6_reply_col3_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col2_red_col6_reply_col3_state
                  opening_col6_reply_col2_red_col6_reply_col3_result_ongoing
                  opening_col6_reply_col2_red_col6_reply_col3_turn_red)).
  exists opening_col6_reply_col2_red_col6_reply_col3_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col3_red_col6.
  - apply opening_col6_reply_col2_red_col6_reply_col3_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col4_raw_if_subgoals :
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col2_red_col6_state col4).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col2_red_col6_reply_col4_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col2_red_col6_reply_col4_state
                  opening_col6_reply_col2_red_col6_reply_col4_result_ongoing
                  opening_col6_reply_col2_red_col6_reply_col4_turn_red)).
  exists opening_col6_reply_col2_red_col6_reply_col4_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col4_red_col6.
  - apply opening_col6_reply_col2_red_col6_reply_col4_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col5_raw_if_subgoals :
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col2_red_col6_state col5).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col2_red_col6_reply_col5_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col2_red_col6_reply_col5_state
                  opening_col6_reply_col2_red_col6_reply_col5_result_ongoing
                  opening_col6_reply_col2_red_col6_reply_col5_turn_red)).
  exists opening_col6_reply_col2_red_col6_reply_col5_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col5_red_col6.
  - apply opening_col6_reply_col2_red_col6_reply_col5_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col2_red_col6_reply_col6_raw_if_subgoals :
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col2_red_col6_state col6).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col2_red_col6_reply_col6_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col2_red_col6_reply_col6_state
                  opening_col6_reply_col2_red_col6_reply_col6_result_ongoing
                  opening_col6_reply_col2_red_col6_reply_col6_turn_red)).
  exists opening_col6_reply_col2_red_col6_reply_col6_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col2_red_col6_reply_col6_red_col6.
  - apply opening_col6_reply_col2_red_col6_reply_col6_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col2_raw_if_all_reply_subgoal_blocks :
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 opening_col6_reply_col2_state.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  apply (proj2 (red_can_force_win_unfold_ongoing_red 39
                  opening_col6_reply_col2_state
                  opening_col6_reply_col2_result_ongoing
                  opening_col6_reply_col2_turn_red)).
  exists opening_col6_reply_col2_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col2_red_col6.
  - apply (proj2 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col2_red_col6_state
                    opening_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col2_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col2_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col2_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    destruct m.
    + apply opening_col6_reply_col2_red_col6_reply_col0_raw_if_subgoals; exact H0.
    + apply opening_col6_reply_col2_red_col6_reply_col1_raw_if_subgoals; exact H1.
    + apply opening_col6_reply_col2_red_col6_reply_col2_raw_if_subgoals; exact H2.
    + apply opening_col6_reply_col2_red_col6_reply_col3_raw_if_subgoals; exact H3.
    + apply opening_col6_reply_col2_red_col6_reply_col4_raw_if_subgoals; exact H4.
    + apply opening_col6_reply_col2_red_col6_reply_col5_raw_if_subgoals; exact H5.
    + apply opening_col6_reply_col2_red_col6_reply_col6_raw_if_subgoals; exact H6.
Qed.

Lemma opening_col6_reply_col2_goal_if_all_reply_subgoal_blocks :
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col2_goal.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  apply opening_col6_reply_col2_raw_if_all_reply_subgoal_blocks; assumption.
Qed.

Lemma opening_col6_reply_col2_firstconj_if_all_reply_subgoal_blocks :
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col2).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  change (red_can_force_win 40 opening_col6_reply_col2_state).
  apply opening_col6_reply_col2_raw_if_all_reply_subgoal_blocks; assumption.
Qed.

Lemma opening_col6_reply_col2_firstconj_if_col2col0to5_col6_and_col2col6_block :
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col2).
Proof.
  intros H20c6 H21c6 H22c6 H23c6 H24c6 H25c6 H26.
  apply opening_col6_reply_col2_firstconj_if_all_reply_subgoal_blocks.
  - apply opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals_if_col6.
    exact H20c6.
  - apply opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals_if_col6.
    exact H21c6.
  - apply opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals_if_col6.
    exact H22c6.
  - apply opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals_if_col6.
    exact H23c6.
  - apply opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals_if_col6.
    exact H24c6.
  - apply opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals_if_col6.
    exact H25c6.
  - exact H26.
Qed.

Definition opening_col6_reply_col3_state : game :=
  apply_move opening_col6_state col3.

Definition opening_col6_reply_col3_goal : Prop :=
  red_can_force_win 40 opening_col6_reply_col3_state.

Lemma opening_col6_reply_col3_turn_red :
  next_turn opening_col6_reply_col3_state = red.
Proof.
  unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_result_ongoing :
  get_result opening_col6_reply_col3_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_goal_unfold :
  opening_col6_reply_col3_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col3_state) /\
    red_can_force_win 39 g.
Proof.
  unfold opening_col6_reply_col3_goal.
  change 40 with (S 39).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col3_result_ongoing.
  - apply opening_col6_reply_col3_turn_red.
Qed.

Definition opening_col6_reply_col3_red_col6_state : game :=
  apply_move opening_col6_reply_col3_state col6.

Lemma in_c4_next_opening_col6_reply_col3_red_col6 :
  In opening_col6_reply_col3_red_col6_state
     (c4_next opening_col6_reply_col3_state).
Proof.
  unfold opening_col6_reply_col3_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col3_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col3_result_ongoing.
  - unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col3_goal_if_red_col6_child :
  red_can_force_win 39 opening_col6_reply_col3_red_col6_state ->
  opening_col6_reply_col3_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col3_goal_unfold).
  exists opening_col6_reply_col3_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col3_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col3_red_col6_turn_yellow :
  next_turn opening_col6_reply_col3_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_result_ongoing :
  get_result opening_col6_reply_col3_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col3_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col3_red_col6_state m)
       (c4_next opening_col6_reply_col3_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col3_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col3_red_col6_result_ongoing.
  - unfold opening_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col3_red_col6_move_form :
  red_can_force_win 39 opening_col6_reply_col3_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 38
      (apply_move opening_col6_reply_col3_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col3_red_col6_state
                    opening_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col3_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col3_red_col6_state
                    opening_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col3_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col3_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_subgoals : Prop :=
  red_can_force_win 38 (apply_move opening_col6_reply_col3_red_col6_state col0) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col3_red_col6_state col1) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col3_red_col6_state col2) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col3_red_col6_state col3) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col3_red_col6_state col4) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col3_red_col6_state col5) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col3_red_col6_state col6).

Lemma opening_col6_reply_col3_red_col6_subgoals_imply_child :
  opening_col6_reply_col3_red_col6_reply_subgoals ->
  red_can_force_win 39 opening_col6_reply_col3_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col3_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col3_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col3_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col3_goal_if_red_col6_child.
  apply opening_col6_reply_col3_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col0_state : game :=
  apply_move opening_col6_reply_col3_red_col6_state col0.

Definition opening_col6_reply_col3_red_col6_reply_col0_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col3_red_col6_reply_col0_state.

Lemma opening_col6_reply_col3_red_col6_reply_col0_turn_red :
  next_turn opening_col6_reply_col3_red_col6_reply_col0_state = red.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col0_state.
  unfold opening_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col0_result_ongoing :
  get_result opening_col6_reply_col3_red_col6_reply_col0_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col0_goal_unfold :
  opening_col6_reply_col3_red_col6_reply_col0_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col3_red_col6_reply_col0_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col0_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col3_red_col6_reply_col0_result_ongoing.
  - apply opening_col6_reply_col3_red_col6_reply_col0_turn_red.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col0_red_col6_state : game :=
  apply_move opening_col6_reply_col3_red_col6_reply_col0_state col6.

Lemma in_c4_next_opening_col6_reply_col3_red_col6_reply_col0_red_col6 :
  In opening_col6_reply_col3_red_col6_reply_col0_red_col6_state
     (c4_next opening_col6_reply_col3_red_col6_reply_col0_state).
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col0_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col3_red_col6_reply_col0_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col3_red_col6_reply_col0_result_ongoing.
  - unfold opening_col6_reply_col3_red_col6_reply_col0_state.
    unfold opening_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col0_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col0_red_col6_state ->
  opening_col6_reply_col3_red_col6_reply_col0_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col3_red_col6_reply_col0_goal_unfold).
  exists opening_col6_reply_col3_red_col6_reply_col0_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col0_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col0_red_col6_turn_yellow :
  next_turn opening_col6_reply_col3_red_col6_reply_col0_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col3_red_col6_reply_col0_state.
  unfold opening_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col0_red_col6_result_ongoing :
  get_result opening_col6_reply_col3_red_col6_reply_col0_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col3_red_col6_reply_col0_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state m)
       (c4_next opening_col6_reply_col3_red_col6_reply_col0_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col3_red_col6_reply_col0_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col3_red_col6_reply_col0_red_col6_result_ongoing.
  - unfold opening_col6_reply_col3_red_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col3_red_col6_reply_col0_state.
    unfold opening_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col0_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col0_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col3_red_col6_reply_col0_red_col6_state
                    opening_col6_reply_col3_red_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_reply_col0_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col0_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col3_red_col6_reply_col0_red_col6_state
                    opening_col6_reply_col3_red_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_reply_col0_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col3_red_col6_reply_col0_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col3_red_col6_reply_col0_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col6).

Lemma opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col0_red_col6_subgoals_imply_child :
  opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col0_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col3_red_col6_reply_col0_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col0_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col0_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col3_red_col6_reply_col0_goal_if_red_col6_child.
  apply opening_col6_reply_col3_red_col6_reply_col0_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col1_state : game :=
  apply_move opening_col6_reply_col3_red_col6_state col1.

Definition opening_col6_reply_col3_red_col6_reply_col1_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col3_red_col6_reply_col1_state.

Lemma opening_col6_reply_col3_red_col6_reply_col1_turn_red :
  next_turn opening_col6_reply_col3_red_col6_reply_col1_state = red.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col1_state.
  unfold opening_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col1_result_ongoing :
  get_result opening_col6_reply_col3_red_col6_reply_col1_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col1_goal_unfold :
  opening_col6_reply_col3_red_col6_reply_col1_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col3_red_col6_reply_col1_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col1_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col3_red_col6_reply_col1_result_ongoing.
  - apply opening_col6_reply_col3_red_col6_reply_col1_turn_red.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col1_red_col6_state : game :=
  apply_move opening_col6_reply_col3_red_col6_reply_col1_state col6.

Lemma in_c4_next_opening_col6_reply_col3_red_col6_reply_col1_red_col6 :
  In opening_col6_reply_col3_red_col6_reply_col1_red_col6_state
     (c4_next opening_col6_reply_col3_red_col6_reply_col1_state).
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col1_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col3_red_col6_reply_col1_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col3_red_col6_reply_col1_result_ongoing.
  - unfold opening_col6_reply_col3_red_col6_reply_col1_state.
    unfold opening_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col1_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col1_red_col6_state ->
  opening_col6_reply_col3_red_col6_reply_col1_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col3_red_col6_reply_col1_goal_unfold).
  exists opening_col6_reply_col3_red_col6_reply_col1_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col1_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col1_red_col6_turn_yellow :
  next_turn opening_col6_reply_col3_red_col6_reply_col1_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col3_red_col6_reply_col1_state.
  unfold opening_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col1_red_col6_result_ongoing :
  get_result opening_col6_reply_col3_red_col6_reply_col1_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col3_red_col6_reply_col1_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state m)
       (c4_next opening_col6_reply_col3_red_col6_reply_col1_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col3_red_col6_reply_col1_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col3_red_col6_reply_col1_red_col6_result_ongoing.
  - unfold opening_col6_reply_col3_red_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col3_red_col6_reply_col1_state.
    unfold opening_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col1_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col1_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col3_red_col6_reply_col1_red_col6_state
                    opening_col6_reply_col3_red_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_reply_col1_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col1_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col3_red_col6_reply_col1_red_col6_state
                    opening_col6_reply_col3_red_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_reply_col1_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col3_red_col6_reply_col1_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col3_red_col6_reply_col1_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col6).

Lemma opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col1_red_col6_subgoals_imply_child :
  opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col1_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col3_red_col6_reply_col1_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col1_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col1_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col3_red_col6_reply_col1_goal_if_red_col6_child.
  apply opening_col6_reply_col3_red_col6_reply_col1_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col2_state : game :=
  apply_move opening_col6_reply_col3_red_col6_state col2.

Definition opening_col6_reply_col3_red_col6_reply_col2_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col3_red_col6_reply_col2_state.

Lemma opening_col6_reply_col3_red_col6_reply_col2_turn_red :
  next_turn opening_col6_reply_col3_red_col6_reply_col2_state = red.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col2_state.
  unfold opening_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col2_result_ongoing :
  get_result opening_col6_reply_col3_red_col6_reply_col2_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col2_goal_unfold :
  opening_col6_reply_col3_red_col6_reply_col2_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col3_red_col6_reply_col2_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col2_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col3_red_col6_reply_col2_result_ongoing.
  - apply opening_col6_reply_col3_red_col6_reply_col2_turn_red.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col2_red_col6_state : game :=
  apply_move opening_col6_reply_col3_red_col6_reply_col2_state col6.

Lemma in_c4_next_opening_col6_reply_col3_red_col6_reply_col2_red_col6 :
  In opening_col6_reply_col3_red_col6_reply_col2_red_col6_state
     (c4_next opening_col6_reply_col3_red_col6_reply_col2_state).
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col2_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col3_red_col6_reply_col2_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col3_red_col6_reply_col2_result_ongoing.
  - unfold opening_col6_reply_col3_red_col6_reply_col2_state.
    unfold opening_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col2_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col2_red_col6_state ->
  opening_col6_reply_col3_red_col6_reply_col2_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col3_red_col6_reply_col2_goal_unfold).
  exists opening_col6_reply_col3_red_col6_reply_col2_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col2_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col2_red_col6_turn_yellow :
  next_turn opening_col6_reply_col3_red_col6_reply_col2_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col3_red_col6_reply_col2_state.
  unfold opening_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col2_red_col6_result_ongoing :
  get_result opening_col6_reply_col3_red_col6_reply_col2_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col3_red_col6_reply_col2_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state m)
       (c4_next opening_col6_reply_col3_red_col6_reply_col2_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col3_red_col6_reply_col2_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col3_red_col6_reply_col2_red_col6_result_ongoing.
  - unfold opening_col6_reply_col3_red_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col3_red_col6_reply_col2_state.
    unfold opening_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col2_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col2_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col3_red_col6_reply_col2_red_col6_state
                    opening_col6_reply_col3_red_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_reply_col2_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col2_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col3_red_col6_reply_col2_red_col6_state
                    opening_col6_reply_col3_red_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_reply_col2_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col3_red_col6_reply_col2_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col3_red_col6_reply_col2_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col6).

Lemma opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col2_red_col6_subgoals_imply_child :
  opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col2_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col3_red_col6_reply_col2_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col2_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col2_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col3_red_col6_reply_col2_goal_if_red_col6_child.
  apply opening_col6_reply_col3_red_col6_reply_col2_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col3_state : game :=
  apply_move opening_col6_reply_col3_red_col6_state col3.

Definition opening_col6_reply_col3_red_col6_reply_col3_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col3_red_col6_reply_col3_state.

Lemma opening_col6_reply_col3_red_col6_reply_col3_turn_red :
  next_turn opening_col6_reply_col3_red_col6_reply_col3_state = red.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col3_state.
  unfold opening_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col3_result_ongoing :
  get_result opening_col6_reply_col3_red_col6_reply_col3_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col3_goal_unfold :
  opening_col6_reply_col3_red_col6_reply_col3_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col3_red_col6_reply_col3_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col3_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col3_red_col6_reply_col3_result_ongoing.
  - apply opening_col6_reply_col3_red_col6_reply_col3_turn_red.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col3_red_col6_state : game :=
  apply_move opening_col6_reply_col3_red_col6_reply_col3_state col6.

Lemma in_c4_next_opening_col6_reply_col3_red_col6_reply_col3_red_col6 :
  In opening_col6_reply_col3_red_col6_reply_col3_red_col6_state
     (c4_next opening_col6_reply_col3_red_col6_reply_col3_state).
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col3_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col3_red_col6_reply_col3_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col3_red_col6_reply_col3_result_ongoing.
  - unfold opening_col6_reply_col3_red_col6_reply_col3_state.
    unfold opening_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col3_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col3_red_col6_state ->
  opening_col6_reply_col3_red_col6_reply_col3_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col3_red_col6_reply_col3_goal_unfold).
  exists opening_col6_reply_col3_red_col6_reply_col3_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col3_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col3_red_col6_turn_yellow :
  next_turn opening_col6_reply_col3_red_col6_reply_col3_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col3_red_col6_reply_col3_state.
  unfold opening_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col3_red_col6_result_ongoing :
  get_result opening_col6_reply_col3_red_col6_reply_col3_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col3_red_col6_reply_col3_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state m)
       (c4_next opening_col6_reply_col3_red_col6_reply_col3_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col3_red_col6_reply_col3_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col3_red_col6_reply_col3_red_col6_result_ongoing.
  - unfold opening_col6_reply_col3_red_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col3_red_col6_reply_col3_state.
    unfold opening_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col3_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col3_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col3_red_col6_reply_col3_red_col6_state
                    opening_col6_reply_col3_red_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_reply_col3_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col3_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col3_red_col6_reply_col3_red_col6_state
                    opening_col6_reply_col3_red_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_reply_col3_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col3_red_col6_reply_col3_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col3_red_col6_reply_col3_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col6).

Lemma opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col3_red_col6_subgoals_imply_child :
  opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col3_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col3_red_col6_reply_col3_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col3_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col3_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col3_red_col6_reply_col3_goal_if_red_col6_child.
  apply opening_col6_reply_col3_red_col6_reply_col3_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col4_state : game :=
  apply_move opening_col6_reply_col3_red_col6_state col4.

Definition opening_col6_reply_col3_red_col6_reply_col4_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col3_red_col6_reply_col4_state.

Lemma opening_col6_reply_col3_red_col6_reply_col4_turn_red :
  next_turn opening_col6_reply_col3_red_col6_reply_col4_state = red.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col4_state.
  unfold opening_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col4_result_ongoing :
  get_result opening_col6_reply_col3_red_col6_reply_col4_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col4_goal_unfold :
  opening_col6_reply_col3_red_col6_reply_col4_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col3_red_col6_reply_col4_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col4_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col3_red_col6_reply_col4_result_ongoing.
  - apply opening_col6_reply_col3_red_col6_reply_col4_turn_red.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col4_red_col6_state : game :=
  apply_move opening_col6_reply_col3_red_col6_reply_col4_state col6.

Lemma in_c4_next_opening_col6_reply_col3_red_col6_reply_col4_red_col6 :
  In opening_col6_reply_col3_red_col6_reply_col4_red_col6_state
     (c4_next opening_col6_reply_col3_red_col6_reply_col4_state).
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col4_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col3_red_col6_reply_col4_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col3_red_col6_reply_col4_result_ongoing.
  - unfold opening_col6_reply_col3_red_col6_reply_col4_state.
    unfold opening_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col4_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col4_red_col6_state ->
  opening_col6_reply_col3_red_col6_reply_col4_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col3_red_col6_reply_col4_goal_unfold).
  exists opening_col6_reply_col3_red_col6_reply_col4_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col4_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col4_red_col6_turn_yellow :
  next_turn opening_col6_reply_col3_red_col6_reply_col4_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col3_red_col6_reply_col4_state.
  unfold opening_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col4_red_col6_result_ongoing :
  get_result opening_col6_reply_col3_red_col6_reply_col4_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col3_red_col6_reply_col4_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state m)
       (c4_next opening_col6_reply_col3_red_col6_reply_col4_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col3_red_col6_reply_col4_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col3_red_col6_reply_col4_red_col6_result_ongoing.
  - unfold opening_col6_reply_col3_red_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col3_red_col6_reply_col4_state.
    unfold opening_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col4_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col4_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col3_red_col6_reply_col4_red_col6_state
                    opening_col6_reply_col3_red_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_reply_col4_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col4_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col3_red_col6_reply_col4_red_col6_state
                    opening_col6_reply_col3_red_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_reply_col4_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col3_red_col6_reply_col4_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col3_red_col6_reply_col4_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col6).

Lemma opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col4_red_col6_subgoals_imply_child :
  opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col4_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col3_red_col6_reply_col4_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col4_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col4_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col3_red_col6_reply_col4_goal_if_red_col6_child.
  apply opening_col6_reply_col3_red_col6_reply_col4_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col5_state : game :=
  apply_move opening_col6_reply_col3_red_col6_state col5.

Definition opening_col6_reply_col3_red_col6_reply_col5_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col3_red_col6_reply_col5_state.

Lemma opening_col6_reply_col3_red_col6_reply_col5_turn_red :
  next_turn opening_col6_reply_col3_red_col6_reply_col5_state = red.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col5_state.
  unfold opening_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col5_result_ongoing :
  get_result opening_col6_reply_col3_red_col6_reply_col5_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col5_goal_unfold :
  opening_col6_reply_col3_red_col6_reply_col5_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col3_red_col6_reply_col5_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col5_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col3_red_col6_reply_col5_result_ongoing.
  - apply opening_col6_reply_col3_red_col6_reply_col5_turn_red.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col5_red_col6_state : game :=
  apply_move opening_col6_reply_col3_red_col6_reply_col5_state col6.

Lemma in_c4_next_opening_col6_reply_col3_red_col6_reply_col5_red_col6 :
  In opening_col6_reply_col3_red_col6_reply_col5_red_col6_state
     (c4_next opening_col6_reply_col3_red_col6_reply_col5_state).
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col5_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col3_red_col6_reply_col5_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col3_red_col6_reply_col5_result_ongoing.
  - unfold opening_col6_reply_col3_red_col6_reply_col5_state.
    unfold opening_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col5_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col5_red_col6_state ->
  opening_col6_reply_col3_red_col6_reply_col5_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col3_red_col6_reply_col5_goal_unfold).
  exists opening_col6_reply_col3_red_col6_reply_col5_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col5_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col5_red_col6_turn_yellow :
  next_turn opening_col6_reply_col3_red_col6_reply_col5_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col3_red_col6_reply_col5_state.
  unfold opening_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col5_red_col6_result_ongoing :
  get_result opening_col6_reply_col3_red_col6_reply_col5_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col3_red_col6_reply_col5_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state m)
       (c4_next opening_col6_reply_col3_red_col6_reply_col5_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col3_red_col6_reply_col5_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col3_red_col6_reply_col5_red_col6_result_ongoing.
  - unfold opening_col6_reply_col3_red_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col3_red_col6_reply_col5_state.
    unfold opening_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col5_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col5_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col3_red_col6_reply_col5_red_col6_state
                    opening_col6_reply_col3_red_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_reply_col5_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col5_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col3_red_col6_reply_col5_red_col6_state
                    opening_col6_reply_col3_red_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_reply_col5_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col3_red_col6_reply_col5_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col3_red_col6_reply_col5_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col6).

Lemma opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col5_red_col6_subgoals_imply_child :
  opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col5_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col3_red_col6_reply_col5_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col5_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col5_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col3_red_col6_reply_col5_goal_if_red_col6_child.
  apply opening_col6_reply_col3_red_col6_reply_col5_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col6_state : game :=
  apply_move opening_col6_reply_col3_red_col6_state col6.

Definition opening_col6_reply_col3_red_col6_reply_col6_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col3_red_col6_reply_col6_state.

Lemma opening_col6_reply_col3_red_col6_reply_col6_turn_red :
  next_turn opening_col6_reply_col3_red_col6_reply_col6_state = red.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col6_state.
  unfold opening_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col6_result_ongoing :
  get_result opening_col6_reply_col3_red_col6_reply_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col6_goal_unfold :
  opening_col6_reply_col3_red_col6_reply_col6_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col3_red_col6_reply_col6_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col6_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col3_red_col6_reply_col6_result_ongoing.
  - apply opening_col6_reply_col3_red_col6_reply_col6_turn_red.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col6_red_col6_state : game :=
  apply_move opening_col6_reply_col3_red_col6_reply_col6_state col6.

Lemma in_c4_next_opening_col6_reply_col3_red_col6_reply_col6_red_col6 :
  In opening_col6_reply_col3_red_col6_reply_col6_red_col6_state
     (c4_next opening_col6_reply_col3_red_col6_reply_col6_state).
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col6_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col3_red_col6_reply_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col3_red_col6_reply_col6_result_ongoing.
  - unfold opening_col6_reply_col3_red_col6_reply_col6_state.
    unfold opening_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col6_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col6_red_col6_state ->
  opening_col6_reply_col3_red_col6_reply_col6_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col3_red_col6_reply_col6_goal_unfold).
  exists opening_col6_reply_col3_red_col6_reply_col6_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col6_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col6_red_col6_turn_yellow :
  next_turn opening_col6_reply_col3_red_col6_reply_col6_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col3_red_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col3_red_col6_reply_col6_state.
  unfold opening_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col6_red_col6_result_ongoing :
  get_result opening_col6_reply_col3_red_col6_reply_col6_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col3_red_col6_reply_col6_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state m)
       (c4_next opening_col6_reply_col3_red_col6_reply_col6_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col3_red_col6_reply_col6_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col3_red_col6_reply_col6_red_col6_result_ongoing.
  - unfold opening_col6_reply_col3_red_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col3_red_col6_reply_col6_state.
    unfold opening_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col3_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col6_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col6_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col3_red_col6_reply_col6_red_col6_state
                    opening_col6_reply_col3_red_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_reply_col6_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col6_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col3_red_col6_reply_col6_red_col6_state
                    opening_col6_reply_col3_red_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_reply_col6_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col3_red_col6_reply_col6_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col3_red_col6_reply_col6_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state col6).

Lemma opening_col6_reply_col3_red_col6_reply_col6_red_col6_subgoals_imply_child :
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col3_red_col6_reply_col6_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col3_red_col6_reply_col6_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col6_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col6_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col3_red_col6_reply_col6_goal_if_red_col6_child.
  apply opening_col6_reply_col3_red_col6_reply_col6_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col0_raw_if_subgoals :
  opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col3_red_col6_state col0).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col3_red_col6_reply_col0_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col3_red_col6_reply_col0_state
                  opening_col6_reply_col3_red_col6_reply_col0_result_ongoing
                  opening_col6_reply_col3_red_col6_reply_col0_turn_red)).
  exists opening_col6_reply_col3_red_col6_reply_col0_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col0_red_col6.
  - apply opening_col6_reply_col3_red_col6_reply_col0_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col1_raw_if_subgoals :
  opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col3_red_col6_state col1).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col3_red_col6_reply_col1_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col3_red_col6_reply_col1_state
                  opening_col6_reply_col3_red_col6_reply_col1_result_ongoing
                  opening_col6_reply_col3_red_col6_reply_col1_turn_red)).
  exists opening_col6_reply_col3_red_col6_reply_col1_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col1_red_col6.
  - apply opening_col6_reply_col3_red_col6_reply_col1_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col2_raw_if_subgoals :
  opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col3_red_col6_state col2).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col3_red_col6_reply_col2_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col3_red_col6_reply_col2_state
                  opening_col6_reply_col3_red_col6_reply_col2_result_ongoing
                  opening_col6_reply_col3_red_col6_reply_col2_turn_red)).
  exists opening_col6_reply_col3_red_col6_reply_col2_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col2_red_col6.
  - apply opening_col6_reply_col3_red_col6_reply_col2_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col3_raw_if_subgoals :
  opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col3_red_col6_state col3).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col3_red_col6_reply_col3_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col3_red_col6_reply_col3_state
                  opening_col6_reply_col3_red_col6_reply_col3_result_ongoing
                  opening_col6_reply_col3_red_col6_reply_col3_turn_red)).
  exists opening_col6_reply_col3_red_col6_reply_col3_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col3_red_col6.
  - apply opening_col6_reply_col3_red_col6_reply_col3_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col4_raw_if_subgoals :
  opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col3_red_col6_state col4).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col3_red_col6_reply_col4_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col3_red_col6_reply_col4_state
                  opening_col6_reply_col3_red_col6_reply_col4_result_ongoing
                  opening_col6_reply_col3_red_col6_reply_col4_turn_red)).
  exists opening_col6_reply_col3_red_col6_reply_col4_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col4_red_col6.
  - apply opening_col6_reply_col3_red_col6_reply_col4_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col5_raw_if_subgoals :
  opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col3_red_col6_state col5).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col3_red_col6_reply_col5_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col3_red_col6_reply_col5_state
                  opening_col6_reply_col3_red_col6_reply_col5_result_ongoing
                  opening_col6_reply_col3_red_col6_reply_col5_turn_red)).
  exists opening_col6_reply_col3_red_col6_reply_col5_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col5_red_col6.
  - apply opening_col6_reply_col3_red_col6_reply_col5_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col3_red_col6_reply_col6_raw_if_subgoals :
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col3_red_col6_state col6).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col3_red_col6_reply_col6_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col3_red_col6_reply_col6_state
                  opening_col6_reply_col3_red_col6_reply_col6_result_ongoing
                  opening_col6_reply_col3_red_col6_reply_col6_turn_red)).
  exists opening_col6_reply_col3_red_col6_reply_col6_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col3_red_col6_reply_col6_red_col6.
  - apply opening_col6_reply_col3_red_col6_reply_col6_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col3_raw_if_all_reply_subgoal_blocks :
  opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 opening_col6_reply_col3_state.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  apply (proj2 (red_can_force_win_unfold_ongoing_red 39
                  opening_col6_reply_col3_state
                  opening_col6_reply_col3_result_ongoing
                  opening_col6_reply_col3_turn_red)).
  exists opening_col6_reply_col3_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col3_red_col6.
  - apply (proj2 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col3_red_col6_state
                    opening_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col3_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col3_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col3_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    destruct m.
    + apply opening_col6_reply_col3_red_col6_reply_col0_raw_if_subgoals; exact H0.
    + apply opening_col6_reply_col3_red_col6_reply_col1_raw_if_subgoals; exact H1.
    + apply opening_col6_reply_col3_red_col6_reply_col2_raw_if_subgoals; exact H2.
    + apply opening_col6_reply_col3_red_col6_reply_col3_raw_if_subgoals; exact H3.
    + apply opening_col6_reply_col3_red_col6_reply_col4_raw_if_subgoals; exact H4.
    + apply opening_col6_reply_col3_red_col6_reply_col5_raw_if_subgoals; exact H5.
    + apply opening_col6_reply_col3_red_col6_reply_col6_raw_if_subgoals; exact H6.
Qed.

Lemma opening_col6_reply_col3_goal_if_all_reply_subgoal_blocks :
  opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col3_goal.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  apply opening_col6_reply_col3_raw_if_all_reply_subgoal_blocks; assumption.
Qed.

Lemma opening_col6_reply_col3_firstconj_if_all_reply_subgoal_blocks :
  opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col3).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  change (red_can_force_win 40 opening_col6_reply_col3_state).
  apply opening_col6_reply_col3_raw_if_all_reply_subgoal_blocks; assumption.
Qed.

Lemma opening_col6_reply_col3_firstconj_if_col3col0to5_col6_and_col3col6_block :
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col3).
Proof.
  intros H30c6 H31c6 H32c6 H33c6 H34c6 H35c6 H36.
  apply opening_col6_reply_col3_firstconj_if_all_reply_subgoal_blocks.
  - apply opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals_if_col6.
    exact H30c6.
  - apply opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals_if_col6.
    exact H31c6.
  - apply opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals_if_col6.
    exact H32c6.
  - apply opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals_if_col6.
    exact H33c6.
  - apply opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals_if_col6.
    exact H34c6.
  - apply opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals_if_col6.
    exact H35c6.
  - exact H36.
Qed.

Definition opening_col6_reply_col4_state : game :=
  apply_move opening_col6_state col4.

Definition opening_col6_reply_col4_goal : Prop :=
  red_can_force_win 40 opening_col6_reply_col4_state.

Lemma opening_col6_reply_col4_turn_red :
  next_turn opening_col6_reply_col4_state = red.
Proof.
  unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_result_ongoing :
  get_result opening_col6_reply_col4_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_goal_unfold :
  opening_col6_reply_col4_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col4_state) /\
    red_can_force_win 39 g.
Proof.
  unfold opening_col6_reply_col4_goal.
  change 40 with (S 39).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col4_result_ongoing.
  - apply opening_col6_reply_col4_turn_red.
Qed.

Definition opening_col6_reply_col4_red_col6_state : game :=
  apply_move opening_col6_reply_col4_state col6.

Lemma in_c4_next_opening_col6_reply_col4_red_col6 :
  In opening_col6_reply_col4_red_col6_state
     (c4_next opening_col6_reply_col4_state).
Proof.
  unfold opening_col6_reply_col4_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col4_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col4_result_ongoing.
  - unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col4_goal_if_red_col6_child :
  red_can_force_win 39 opening_col6_reply_col4_red_col6_state ->
  opening_col6_reply_col4_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col4_goal_unfold).
  exists opening_col6_reply_col4_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col4_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col4_red_col6_turn_yellow :
  next_turn opening_col6_reply_col4_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_result_ongoing :
  get_result opening_col6_reply_col4_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col4_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col4_red_col6_state m)
       (c4_next opening_col6_reply_col4_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col4_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col4_red_col6_result_ongoing.
  - unfold opening_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col4_red_col6_move_form :
  red_can_force_win 39 opening_col6_reply_col4_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 38
      (apply_move opening_col6_reply_col4_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col4_red_col6_state
                    opening_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col4_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col4_red_col6_state
                    opening_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col4_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col4_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_subgoals : Prop :=
  red_can_force_win 38 (apply_move opening_col6_reply_col4_red_col6_state col0) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col4_red_col6_state col1) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col4_red_col6_state col2) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col4_red_col6_state col3) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col4_red_col6_state col4) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col4_red_col6_state col5) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col4_red_col6_state col6).

Lemma opening_col6_reply_col4_red_col6_subgoals_imply_child :
  opening_col6_reply_col4_red_col6_reply_subgoals ->
  red_can_force_win 39 opening_col6_reply_col4_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col4_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col4_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col4_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col4_goal_if_red_col6_child.
  apply opening_col6_reply_col4_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col0_state : game :=
  apply_move opening_col6_reply_col4_red_col6_state col0.

Definition opening_col6_reply_col4_red_col6_reply_col0_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col4_red_col6_reply_col0_state.

Lemma opening_col6_reply_col4_red_col6_reply_col0_turn_red :
  next_turn opening_col6_reply_col4_red_col6_reply_col0_state = red.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col0_state.
  unfold opening_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col0_result_ongoing :
  get_result opening_col6_reply_col4_red_col6_reply_col0_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col0_goal_unfold :
  opening_col6_reply_col4_red_col6_reply_col0_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col4_red_col6_reply_col0_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col0_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col4_red_col6_reply_col0_result_ongoing.
  - apply opening_col6_reply_col4_red_col6_reply_col0_turn_red.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col0_red_col6_state : game :=
  apply_move opening_col6_reply_col4_red_col6_reply_col0_state col6.

Lemma in_c4_next_opening_col6_reply_col4_red_col6_reply_col0_red_col6 :
  In opening_col6_reply_col4_red_col6_reply_col0_red_col6_state
     (c4_next opening_col6_reply_col4_red_col6_reply_col0_state).
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col0_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col4_red_col6_reply_col0_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col4_red_col6_reply_col0_result_ongoing.
  - unfold opening_col6_reply_col4_red_col6_reply_col0_state.
    unfold opening_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col0_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col0_red_col6_state ->
  opening_col6_reply_col4_red_col6_reply_col0_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col4_red_col6_reply_col0_goal_unfold).
  exists opening_col6_reply_col4_red_col6_reply_col0_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col0_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col0_red_col6_turn_yellow :
  next_turn opening_col6_reply_col4_red_col6_reply_col0_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col4_red_col6_reply_col0_state.
  unfold opening_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col0_red_col6_result_ongoing :
  get_result opening_col6_reply_col4_red_col6_reply_col0_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col4_red_col6_reply_col0_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state m)
       (c4_next opening_col6_reply_col4_red_col6_reply_col0_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col4_red_col6_reply_col0_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col4_red_col6_reply_col0_red_col6_result_ongoing.
  - unfold opening_col6_reply_col4_red_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col4_red_col6_reply_col0_state.
    unfold opening_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col0_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col0_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col4_red_col6_reply_col0_red_col6_state
                    opening_col6_reply_col4_red_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_reply_col0_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col0_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col4_red_col6_reply_col0_red_col6_state
                    opening_col6_reply_col4_red_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_reply_col0_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col4_red_col6_reply_col0_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col4_red_col6_reply_col0_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col0_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col6).

Lemma opening_col6_reply_col4_red_col6_reply_col0_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col6) ->
  opening_col6_reply_col4_red_col6_reply_col0_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col0_red_col6_subgoals_imply_child :
  opening_col6_reply_col4_red_col6_reply_col0_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col0_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col4_red_col6_reply_col0_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col0_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col4_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col0_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col4_red_col6_reply_col0_goal_if_red_col6_child.
  apply opening_col6_reply_col4_red_col6_reply_col0_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col1_state : game :=
  apply_move opening_col6_reply_col4_red_col6_state col1.

Definition opening_col6_reply_col4_red_col6_reply_col1_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col4_red_col6_reply_col1_state.

Lemma opening_col6_reply_col4_red_col6_reply_col1_turn_red :
  next_turn opening_col6_reply_col4_red_col6_reply_col1_state = red.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col1_state.
  unfold opening_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col1_result_ongoing :
  get_result opening_col6_reply_col4_red_col6_reply_col1_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col1_goal_unfold :
  opening_col6_reply_col4_red_col6_reply_col1_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col4_red_col6_reply_col1_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col1_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col4_red_col6_reply_col1_result_ongoing.
  - apply opening_col6_reply_col4_red_col6_reply_col1_turn_red.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col1_red_col6_state : game :=
  apply_move opening_col6_reply_col4_red_col6_reply_col1_state col6.

Lemma in_c4_next_opening_col6_reply_col4_red_col6_reply_col1_red_col6 :
  In opening_col6_reply_col4_red_col6_reply_col1_red_col6_state
     (c4_next opening_col6_reply_col4_red_col6_reply_col1_state).
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col1_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col4_red_col6_reply_col1_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col4_red_col6_reply_col1_result_ongoing.
  - unfold opening_col6_reply_col4_red_col6_reply_col1_state.
    unfold opening_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col1_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col1_red_col6_state ->
  opening_col6_reply_col4_red_col6_reply_col1_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col4_red_col6_reply_col1_goal_unfold).
  exists opening_col6_reply_col4_red_col6_reply_col1_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col1_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col1_red_col6_turn_yellow :
  next_turn opening_col6_reply_col4_red_col6_reply_col1_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col4_red_col6_reply_col1_state.
  unfold opening_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col1_red_col6_result_ongoing :
  get_result opening_col6_reply_col4_red_col6_reply_col1_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col4_red_col6_reply_col1_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state m)
       (c4_next opening_col6_reply_col4_red_col6_reply_col1_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col4_red_col6_reply_col1_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col4_red_col6_reply_col1_red_col6_result_ongoing.
  - unfold opening_col6_reply_col4_red_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col4_red_col6_reply_col1_state.
    unfold opening_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col1_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col1_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col4_red_col6_reply_col1_red_col6_state
                    opening_col6_reply_col4_red_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_reply_col1_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col1_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col4_red_col6_reply_col1_red_col6_state
                    opening_col6_reply_col4_red_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_reply_col1_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col4_red_col6_reply_col1_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col4_red_col6_reply_col1_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col1_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col6).

Lemma opening_col6_reply_col4_red_col6_reply_col1_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col6) ->
  opening_col6_reply_col4_red_col6_reply_col1_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col1_red_col6_subgoals_imply_child :
  opening_col6_reply_col4_red_col6_reply_col1_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col1_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col4_red_col6_reply_col1_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col1_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col4_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col1_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col4_red_col6_reply_col1_goal_if_red_col6_child.
  apply opening_col6_reply_col4_red_col6_reply_col1_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col2_state : game :=
  apply_move opening_col6_reply_col4_red_col6_state col2.

Definition opening_col6_reply_col4_red_col6_reply_col2_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col4_red_col6_reply_col2_state.

Lemma opening_col6_reply_col4_red_col6_reply_col2_turn_red :
  next_turn opening_col6_reply_col4_red_col6_reply_col2_state = red.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col2_state.
  unfold opening_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col2_result_ongoing :
  get_result opening_col6_reply_col4_red_col6_reply_col2_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col2_goal_unfold :
  opening_col6_reply_col4_red_col6_reply_col2_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col4_red_col6_reply_col2_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col2_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col4_red_col6_reply_col2_result_ongoing.
  - apply opening_col6_reply_col4_red_col6_reply_col2_turn_red.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col2_red_col6_state : game :=
  apply_move opening_col6_reply_col4_red_col6_reply_col2_state col6.

Lemma in_c4_next_opening_col6_reply_col4_red_col6_reply_col2_red_col6 :
  In opening_col6_reply_col4_red_col6_reply_col2_red_col6_state
     (c4_next opening_col6_reply_col4_red_col6_reply_col2_state).
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col2_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col4_red_col6_reply_col2_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col4_red_col6_reply_col2_result_ongoing.
  - unfold opening_col6_reply_col4_red_col6_reply_col2_state.
    unfold opening_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col2_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col2_red_col6_state ->
  opening_col6_reply_col4_red_col6_reply_col2_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col4_red_col6_reply_col2_goal_unfold).
  exists opening_col6_reply_col4_red_col6_reply_col2_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col2_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col2_red_col6_turn_yellow :
  next_turn opening_col6_reply_col4_red_col6_reply_col2_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col4_red_col6_reply_col2_state.
  unfold opening_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col2_red_col6_result_ongoing :
  get_result opening_col6_reply_col4_red_col6_reply_col2_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col4_red_col6_reply_col2_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state m)
       (c4_next opening_col6_reply_col4_red_col6_reply_col2_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col4_red_col6_reply_col2_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col4_red_col6_reply_col2_red_col6_result_ongoing.
  - unfold opening_col6_reply_col4_red_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col4_red_col6_reply_col2_state.
    unfold opening_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col2_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col2_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col4_red_col6_reply_col2_red_col6_state
                    opening_col6_reply_col4_red_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_reply_col2_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col2_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col4_red_col6_reply_col2_red_col6_state
                    opening_col6_reply_col4_red_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_reply_col2_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col4_red_col6_reply_col2_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col4_red_col6_reply_col2_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col2_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col6).

Lemma opening_col6_reply_col4_red_col6_reply_col2_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col6) ->
  opening_col6_reply_col4_red_col6_reply_col2_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col2_red_col6_subgoals_imply_child :
  opening_col6_reply_col4_red_col6_reply_col2_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col2_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col4_red_col6_reply_col2_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col2_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col4_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col2_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col4_red_col6_reply_col2_goal_if_red_col6_child.
  apply opening_col6_reply_col4_red_col6_reply_col2_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col3_state : game :=
  apply_move opening_col6_reply_col4_red_col6_state col3.

Definition opening_col6_reply_col4_red_col6_reply_col3_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col4_red_col6_reply_col3_state.

Lemma opening_col6_reply_col4_red_col6_reply_col3_turn_red :
  next_turn opening_col6_reply_col4_red_col6_reply_col3_state = red.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col3_state.
  unfold opening_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col3_result_ongoing :
  get_result opening_col6_reply_col4_red_col6_reply_col3_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col3_goal_unfold :
  opening_col6_reply_col4_red_col6_reply_col3_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col4_red_col6_reply_col3_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col3_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col4_red_col6_reply_col3_result_ongoing.
  - apply opening_col6_reply_col4_red_col6_reply_col3_turn_red.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col3_red_col6_state : game :=
  apply_move opening_col6_reply_col4_red_col6_reply_col3_state col6.

Lemma in_c4_next_opening_col6_reply_col4_red_col6_reply_col3_red_col6 :
  In opening_col6_reply_col4_red_col6_reply_col3_red_col6_state
     (c4_next opening_col6_reply_col4_red_col6_reply_col3_state).
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col3_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col4_red_col6_reply_col3_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col4_red_col6_reply_col3_result_ongoing.
  - unfold opening_col6_reply_col4_red_col6_reply_col3_state.
    unfold opening_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col3_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col3_red_col6_state ->
  opening_col6_reply_col4_red_col6_reply_col3_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col4_red_col6_reply_col3_goal_unfold).
  exists opening_col6_reply_col4_red_col6_reply_col3_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col3_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col3_red_col6_turn_yellow :
  next_turn opening_col6_reply_col4_red_col6_reply_col3_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col4_red_col6_reply_col3_state.
  unfold opening_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col3_red_col6_result_ongoing :
  get_result opening_col6_reply_col4_red_col6_reply_col3_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col4_red_col6_reply_col3_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state m)
       (c4_next opening_col6_reply_col4_red_col6_reply_col3_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col4_red_col6_reply_col3_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col4_red_col6_reply_col3_red_col6_result_ongoing.
  - unfold opening_col6_reply_col4_red_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col4_red_col6_reply_col3_state.
    unfold opening_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col3_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col3_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col4_red_col6_reply_col3_red_col6_state
                    opening_col6_reply_col4_red_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_reply_col3_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col3_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col4_red_col6_reply_col3_red_col6_state
                    opening_col6_reply_col4_red_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_reply_col3_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col4_red_col6_reply_col3_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col4_red_col6_reply_col3_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col3_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col6).

Lemma opening_col6_reply_col4_red_col6_reply_col3_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col6) ->
  opening_col6_reply_col4_red_col6_reply_col3_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col3_red_col6_subgoals_imply_child :
  opening_col6_reply_col4_red_col6_reply_col3_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col3_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col4_red_col6_reply_col3_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col3_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col4_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col3_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col4_red_col6_reply_col3_goal_if_red_col6_child.
  apply opening_col6_reply_col4_red_col6_reply_col3_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col4_state : game :=
  apply_move opening_col6_reply_col4_red_col6_state col4.

Definition opening_col6_reply_col4_red_col6_reply_col4_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col4_red_col6_reply_col4_state.

Lemma opening_col6_reply_col4_red_col6_reply_col4_turn_red :
  next_turn opening_col6_reply_col4_red_col6_reply_col4_state = red.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col4_state.
  unfold opening_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col4_result_ongoing :
  get_result opening_col6_reply_col4_red_col6_reply_col4_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col4_goal_unfold :
  opening_col6_reply_col4_red_col6_reply_col4_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col4_red_col6_reply_col4_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col4_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col4_red_col6_reply_col4_result_ongoing.
  - apply opening_col6_reply_col4_red_col6_reply_col4_turn_red.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col4_red_col6_state : game :=
  apply_move opening_col6_reply_col4_red_col6_reply_col4_state col6.

Lemma in_c4_next_opening_col6_reply_col4_red_col6_reply_col4_red_col6 :
  In opening_col6_reply_col4_red_col6_reply_col4_red_col6_state
     (c4_next opening_col6_reply_col4_red_col6_reply_col4_state).
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col4_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col4_red_col6_reply_col4_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col4_red_col6_reply_col4_result_ongoing.
  - unfold opening_col6_reply_col4_red_col6_reply_col4_state.
    unfold opening_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col4_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col4_red_col6_state ->
  opening_col6_reply_col4_red_col6_reply_col4_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col4_red_col6_reply_col4_goal_unfold).
  exists opening_col6_reply_col4_red_col6_reply_col4_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col4_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col4_red_col6_turn_yellow :
  next_turn opening_col6_reply_col4_red_col6_reply_col4_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col4_red_col6_reply_col4_state.
  unfold opening_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col4_red_col6_result_ongoing :
  get_result opening_col6_reply_col4_red_col6_reply_col4_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col4_red_col6_reply_col4_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state m)
       (c4_next opening_col6_reply_col4_red_col6_reply_col4_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col4_red_col6_reply_col4_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col4_red_col6_reply_col4_red_col6_result_ongoing.
  - unfold opening_col6_reply_col4_red_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col4_red_col6_reply_col4_state.
    unfold opening_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col4_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col4_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col4_red_col6_reply_col4_red_col6_state
                    opening_col6_reply_col4_red_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_reply_col4_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col4_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col4_red_col6_reply_col4_red_col6_state
                    opening_col6_reply_col4_red_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_reply_col4_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col4_red_col6_reply_col4_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col4_red_col6_reply_col4_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col4_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col6).

Lemma opening_col6_reply_col4_red_col6_reply_col4_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col6) ->
  opening_col6_reply_col4_red_col6_reply_col4_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col4_red_col6_subgoals_imply_child :
  opening_col6_reply_col4_red_col6_reply_col4_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col4_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col4_red_col6_reply_col4_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col4_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col4_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col4_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col4_red_col6_reply_col4_goal_if_red_col6_child.
  apply opening_col6_reply_col4_red_col6_reply_col4_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col5_state : game :=
  apply_move opening_col6_reply_col4_red_col6_state col5.

Definition opening_col6_reply_col4_red_col6_reply_col5_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col4_red_col6_reply_col5_state.

Lemma opening_col6_reply_col4_red_col6_reply_col5_turn_red :
  next_turn opening_col6_reply_col4_red_col6_reply_col5_state = red.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col5_state.
  unfold opening_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col5_result_ongoing :
  get_result opening_col6_reply_col4_red_col6_reply_col5_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col5_goal_unfold :
  opening_col6_reply_col4_red_col6_reply_col5_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col4_red_col6_reply_col5_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col5_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col4_red_col6_reply_col5_result_ongoing.
  - apply opening_col6_reply_col4_red_col6_reply_col5_turn_red.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col5_red_col6_state : game :=
  apply_move opening_col6_reply_col4_red_col6_reply_col5_state col6.

Lemma in_c4_next_opening_col6_reply_col4_red_col6_reply_col5_red_col6 :
  In opening_col6_reply_col4_red_col6_reply_col5_red_col6_state
     (c4_next opening_col6_reply_col4_red_col6_reply_col5_state).
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col5_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col4_red_col6_reply_col5_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col4_red_col6_reply_col5_result_ongoing.
  - unfold opening_col6_reply_col4_red_col6_reply_col5_state.
    unfold opening_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col5_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col5_red_col6_state ->
  opening_col6_reply_col4_red_col6_reply_col5_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col4_red_col6_reply_col5_goal_unfold).
  exists opening_col6_reply_col4_red_col6_reply_col5_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col5_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col5_red_col6_turn_yellow :
  next_turn opening_col6_reply_col4_red_col6_reply_col5_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col4_red_col6_reply_col5_state.
  unfold opening_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col5_red_col6_result_ongoing :
  get_result opening_col6_reply_col4_red_col6_reply_col5_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col4_red_col6_reply_col5_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state m)
       (c4_next opening_col6_reply_col4_red_col6_reply_col5_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col4_red_col6_reply_col5_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col4_red_col6_reply_col5_red_col6_result_ongoing.
  - unfold opening_col6_reply_col4_red_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col4_red_col6_reply_col5_state.
    unfold opening_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col5_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col5_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col4_red_col6_reply_col5_red_col6_state
                    opening_col6_reply_col4_red_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_reply_col5_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col5_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col4_red_col6_reply_col5_red_col6_state
                    opening_col6_reply_col4_red_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_reply_col5_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col4_red_col6_reply_col5_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col4_red_col6_reply_col5_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col5_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col6).

Lemma opening_col6_reply_col4_red_col6_reply_col5_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col4_red_col6_reply_col5_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col5_red_col6_subgoals_imply_child :
  opening_col6_reply_col4_red_col6_reply_col5_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col5_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col4_red_col6_reply_col5_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col5_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col4_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col5_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col4_red_col6_reply_col5_goal_if_red_col6_child.
  apply opening_col6_reply_col4_red_col6_reply_col5_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col6_state : game :=
  apply_move opening_col6_reply_col4_red_col6_state col6.

Definition opening_col6_reply_col4_red_col6_reply_col6_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col4_red_col6_reply_col6_state.

Lemma opening_col6_reply_col4_red_col6_reply_col6_turn_red :
  next_turn opening_col6_reply_col4_red_col6_reply_col6_state = red.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col6_state.
  unfold opening_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col6_result_ongoing :
  get_result opening_col6_reply_col4_red_col6_reply_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col6_goal_unfold :
  opening_col6_reply_col4_red_col6_reply_col6_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col4_red_col6_reply_col6_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col6_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col4_red_col6_reply_col6_result_ongoing.
  - apply opening_col6_reply_col4_red_col6_reply_col6_turn_red.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col6_red_col6_state : game :=
  apply_move opening_col6_reply_col4_red_col6_reply_col6_state col6.

Lemma in_c4_next_opening_col6_reply_col4_red_col6_reply_col6_red_col6 :
  In opening_col6_reply_col4_red_col6_reply_col6_red_col6_state
     (c4_next opening_col6_reply_col4_red_col6_reply_col6_state).
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col6_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col4_red_col6_reply_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col4_red_col6_reply_col6_result_ongoing.
  - unfold opening_col6_reply_col4_red_col6_reply_col6_state.
    unfold opening_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col6_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col6_red_col6_state ->
  opening_col6_reply_col4_red_col6_reply_col6_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col4_red_col6_reply_col6_goal_unfold).
  exists opening_col6_reply_col4_red_col6_reply_col6_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col6_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col6_red_col6_turn_yellow :
  next_turn opening_col6_reply_col4_red_col6_reply_col6_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col4_red_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col4_red_col6_reply_col6_state.
  unfold opening_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col6_red_col6_result_ongoing :
  get_result opening_col6_reply_col4_red_col6_reply_col6_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col4_red_col6_reply_col6_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state m)
       (c4_next opening_col6_reply_col4_red_col6_reply_col6_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col4_red_col6_reply_col6_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col4_red_col6_reply_col6_red_col6_result_ongoing.
  - unfold opening_col6_reply_col4_red_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col4_red_col6_reply_col6_state.
    unfold opening_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col4_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col6_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col6_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col4_red_col6_reply_col6_red_col6_state
                    opening_col6_reply_col4_red_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_reply_col6_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col6_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col4_red_col6_reply_col6_red_col6_state
                    opening_col6_reply_col4_red_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_reply_col6_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col4_red_col6_reply_col6_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col4_red_col6_reply_col6_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state col6).

Lemma opening_col6_reply_col4_red_col6_reply_col6_red_col6_subgoals_imply_child :
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col4_red_col6_reply_col6_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col4_red_col6_reply_col6_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col6_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col6_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col4_red_col6_reply_col6_goal_if_red_col6_child.
  apply opening_col6_reply_col4_red_col6_reply_col6_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col0_raw_if_subgoals :
  opening_col6_reply_col4_red_col6_reply_col0_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col4_red_col6_state col0).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col4_red_col6_reply_col0_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col4_red_col6_reply_col0_state
                  opening_col6_reply_col4_red_col6_reply_col0_result_ongoing
                  opening_col6_reply_col4_red_col6_reply_col0_turn_red)).
  exists opening_col6_reply_col4_red_col6_reply_col0_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col0_red_col6.
  - apply opening_col6_reply_col4_red_col6_reply_col0_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col1_raw_if_subgoals :
  opening_col6_reply_col4_red_col6_reply_col1_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col4_red_col6_state col1).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col4_red_col6_reply_col1_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col4_red_col6_reply_col1_state
                  opening_col6_reply_col4_red_col6_reply_col1_result_ongoing
                  opening_col6_reply_col4_red_col6_reply_col1_turn_red)).
  exists opening_col6_reply_col4_red_col6_reply_col1_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col1_red_col6.
  - apply opening_col6_reply_col4_red_col6_reply_col1_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col2_raw_if_subgoals :
  opening_col6_reply_col4_red_col6_reply_col2_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col4_red_col6_state col2).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col4_red_col6_reply_col2_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col4_red_col6_reply_col2_state
                  opening_col6_reply_col4_red_col6_reply_col2_result_ongoing
                  opening_col6_reply_col4_red_col6_reply_col2_turn_red)).
  exists opening_col6_reply_col4_red_col6_reply_col2_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col2_red_col6.
  - apply opening_col6_reply_col4_red_col6_reply_col2_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col3_raw_if_subgoals :
  opening_col6_reply_col4_red_col6_reply_col3_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col4_red_col6_state col3).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col4_red_col6_reply_col3_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col4_red_col6_reply_col3_state
                  opening_col6_reply_col4_red_col6_reply_col3_result_ongoing
                  opening_col6_reply_col4_red_col6_reply_col3_turn_red)).
  exists opening_col6_reply_col4_red_col6_reply_col3_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col3_red_col6.
  - apply opening_col6_reply_col4_red_col6_reply_col3_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col4_raw_if_subgoals :
  opening_col6_reply_col4_red_col6_reply_col4_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col4_red_col6_state col4).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col4_red_col6_reply_col4_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col4_red_col6_reply_col4_state
                  opening_col6_reply_col4_red_col6_reply_col4_result_ongoing
                  opening_col6_reply_col4_red_col6_reply_col4_turn_red)).
  exists opening_col6_reply_col4_red_col6_reply_col4_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col4_red_col6.
  - apply opening_col6_reply_col4_red_col6_reply_col4_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col5_raw_if_subgoals :
  opening_col6_reply_col4_red_col6_reply_col5_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col4_red_col6_state col5).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col4_red_col6_reply_col5_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col4_red_col6_reply_col5_state
                  opening_col6_reply_col4_red_col6_reply_col5_result_ongoing
                  opening_col6_reply_col4_red_col6_reply_col5_turn_red)).
  exists opening_col6_reply_col4_red_col6_reply_col5_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col5_red_col6.
  - apply opening_col6_reply_col4_red_col6_reply_col5_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col4_red_col6_reply_col6_raw_if_subgoals :
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col4_red_col6_state col6).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col4_red_col6_reply_col6_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col4_red_col6_reply_col6_state
                  opening_col6_reply_col4_red_col6_reply_col6_result_ongoing
                  opening_col6_reply_col4_red_col6_reply_col6_turn_red)).
  exists opening_col6_reply_col4_red_col6_reply_col6_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col4_red_col6_reply_col6_red_col6.
  - apply opening_col6_reply_col4_red_col6_reply_col6_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col4_raw_if_all_reply_subgoal_blocks :
  opening_col6_reply_col4_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 opening_col6_reply_col4_state.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  apply (proj2 (red_can_force_win_unfold_ongoing_red 39
                  opening_col6_reply_col4_state
                  opening_col6_reply_col4_result_ongoing
                  opening_col6_reply_col4_turn_red)).
  exists opening_col6_reply_col4_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col4_red_col6.
  - apply (proj2 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col4_red_col6_state
                    opening_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col4_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col4_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col4_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    destruct m.
    + apply opening_col6_reply_col4_red_col6_reply_col0_raw_if_subgoals; exact H0.
    + apply opening_col6_reply_col4_red_col6_reply_col1_raw_if_subgoals; exact H1.
    + apply opening_col6_reply_col4_red_col6_reply_col2_raw_if_subgoals; exact H2.
    + apply opening_col6_reply_col4_red_col6_reply_col3_raw_if_subgoals; exact H3.
    + apply opening_col6_reply_col4_red_col6_reply_col4_raw_if_subgoals; exact H4.
    + apply opening_col6_reply_col4_red_col6_reply_col5_raw_if_subgoals; exact H5.
    + apply opening_col6_reply_col4_red_col6_reply_col6_raw_if_subgoals; exact H6.
Qed.

Lemma opening_col6_reply_col4_goal_if_all_reply_subgoal_blocks :
  opening_col6_reply_col4_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col4_goal.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  apply opening_col6_reply_col4_raw_if_all_reply_subgoal_blocks; assumption.
Qed.

Lemma opening_col6_reply_col4_firstconj_if_all_reply_subgoal_blocks :
  opening_col6_reply_col4_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col4).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  change (red_can_force_win 40 opening_col6_reply_col4_state).
  apply opening_col6_reply_col4_raw_if_all_reply_subgoal_blocks; assumption.
Qed.

Lemma opening_col6_reply_col4_firstconj_if_col4col0to5_col6_and_col4col6_block :
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col4).
Proof.
  intros H40c6 H41c6 H42c6 H43c6 H44c6 H45c6 H46.
  apply opening_col6_reply_col4_firstconj_if_all_reply_subgoal_blocks.
  - apply opening_col6_reply_col4_red_col6_reply_col0_red_col6_reply_subgoals_if_col6.
    exact H40c6.
  - apply opening_col6_reply_col4_red_col6_reply_col1_red_col6_reply_subgoals_if_col6.
    exact H41c6.
  - apply opening_col6_reply_col4_red_col6_reply_col2_red_col6_reply_subgoals_if_col6.
    exact H42c6.
  - apply opening_col6_reply_col4_red_col6_reply_col3_red_col6_reply_subgoals_if_col6.
    exact H43c6.
  - apply opening_col6_reply_col4_red_col6_reply_col4_red_col6_reply_subgoals_if_col6.
    exact H44c6.
  - apply opening_col6_reply_col4_red_col6_reply_col5_red_col6_reply_subgoals_if_col6.
    exact H45c6.
  - exact H46.
Qed.

Definition opening_col6_reply_col5_state : game :=
  apply_move opening_col6_state col5.

Definition opening_col6_reply_col5_goal : Prop :=
  red_can_force_win 40 opening_col6_reply_col5_state.

Lemma opening_col6_reply_col5_turn_red :
  next_turn opening_col6_reply_col5_state = red.
Proof.
  unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_result_ongoing :
  get_result opening_col6_reply_col5_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_goal_unfold :
  opening_col6_reply_col5_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col5_state) /\
    red_can_force_win 39 g.
Proof.
  unfold opening_col6_reply_col5_goal.
  change 40 with (S 39).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col5_result_ongoing.
  - apply opening_col6_reply_col5_turn_red.
Qed.

Definition opening_col6_reply_col5_red_col6_state : game :=
  apply_move opening_col6_reply_col5_state col6.

Lemma in_c4_next_opening_col6_reply_col5_red_col6 :
  In opening_col6_reply_col5_red_col6_state
     (c4_next opening_col6_reply_col5_state).
Proof.
  unfold opening_col6_reply_col5_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col5_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col5_result_ongoing.
  - unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col5_goal_if_red_col6_child :
  red_can_force_win 39 opening_col6_reply_col5_red_col6_state ->
  opening_col6_reply_col5_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col5_goal_unfold).
  exists opening_col6_reply_col5_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col5_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col5_red_col6_turn_yellow :
  next_turn opening_col6_reply_col5_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_result_ongoing :
  get_result opening_col6_reply_col5_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col5_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col5_red_col6_state m)
       (c4_next opening_col6_reply_col5_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col5_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col5_red_col6_result_ongoing.
  - unfold opening_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col5_red_col6_move_form :
  red_can_force_win 39 opening_col6_reply_col5_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 38
      (apply_move opening_col6_reply_col5_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col5_red_col6_state
                    opening_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col5_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col5_red_col6_state
                    opening_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col5_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col5_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_subgoals : Prop :=
  red_can_force_win 38 (apply_move opening_col6_reply_col5_red_col6_state col0) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col5_red_col6_state col1) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col5_red_col6_state col2) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col5_red_col6_state col3) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col5_red_col6_state col4) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col5_red_col6_state col5) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col5_red_col6_state col6).

Lemma opening_col6_reply_col5_red_col6_subgoals_imply_child :
  opening_col6_reply_col5_red_col6_reply_subgoals ->
  red_can_force_win 39 opening_col6_reply_col5_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col5_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col5_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col5_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col5_goal_if_red_col6_child.
  apply opening_col6_reply_col5_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col0_state : game :=
  apply_move opening_col6_reply_col5_red_col6_state col0.

Definition opening_col6_reply_col5_red_col6_reply_col0_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col5_red_col6_reply_col0_state.

Lemma opening_col6_reply_col5_red_col6_reply_col0_turn_red :
  next_turn opening_col6_reply_col5_red_col6_reply_col0_state = red.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col0_state.
  unfold opening_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col0_result_ongoing :
  get_result opening_col6_reply_col5_red_col6_reply_col0_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col0_goal_unfold :
  opening_col6_reply_col5_red_col6_reply_col0_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col5_red_col6_reply_col0_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col0_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col5_red_col6_reply_col0_result_ongoing.
  - apply opening_col6_reply_col5_red_col6_reply_col0_turn_red.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col0_red_col6_state : game :=
  apply_move opening_col6_reply_col5_red_col6_reply_col0_state col6.

Lemma in_c4_next_opening_col6_reply_col5_red_col6_reply_col0_red_col6 :
  In opening_col6_reply_col5_red_col6_reply_col0_red_col6_state
     (c4_next opening_col6_reply_col5_red_col6_reply_col0_state).
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col0_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col5_red_col6_reply_col0_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col5_red_col6_reply_col0_result_ongoing.
  - unfold opening_col6_reply_col5_red_col6_reply_col0_state.
    unfold opening_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col0_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col0_red_col6_state ->
  opening_col6_reply_col5_red_col6_reply_col0_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col5_red_col6_reply_col0_goal_unfold).
  exists opening_col6_reply_col5_red_col6_reply_col0_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col0_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col0_red_col6_turn_yellow :
  next_turn opening_col6_reply_col5_red_col6_reply_col0_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col5_red_col6_reply_col0_state.
  unfold opening_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col0_red_col6_result_ongoing :
  get_result opening_col6_reply_col5_red_col6_reply_col0_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col5_red_col6_reply_col0_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col5_red_col6_reply_col0_red_col6_state m)
       (c4_next opening_col6_reply_col5_red_col6_reply_col0_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col5_red_col6_reply_col0_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col5_red_col6_reply_col0_red_col6_result_ongoing.
  - unfold opening_col6_reply_col5_red_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col5_red_col6_reply_col0_state.
    unfold opening_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col0_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col0_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col5_red_col6_reply_col0_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col5_red_col6_reply_col0_red_col6_state
                    opening_col6_reply_col5_red_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_reply_col0_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col0_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col5_red_col6_reply_col0_red_col6_state
                    opening_col6_reply_col5_red_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_reply_col0_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col5_red_col6_reply_col0_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col5_red_col6_reply_col0_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col0_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col6).

Lemma opening_col6_reply_col5_red_col6_reply_col0_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col6) ->
  opening_col6_reply_col5_red_col6_reply_col0_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col0_red_col6_subgoals_imply_child :
  opening_col6_reply_col5_red_col6_reply_col0_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col0_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col5_red_col6_reply_col0_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col0_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col5_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col0_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col5_red_col6_reply_col0_goal_if_red_col6_child.
  apply opening_col6_reply_col5_red_col6_reply_col0_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col1_state : game :=
  apply_move opening_col6_reply_col5_red_col6_state col1.

Definition opening_col6_reply_col5_red_col6_reply_col1_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col5_red_col6_reply_col1_state.

Lemma opening_col6_reply_col5_red_col6_reply_col1_turn_red :
  next_turn opening_col6_reply_col5_red_col6_reply_col1_state = red.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col1_state.
  unfold opening_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col1_result_ongoing :
  get_result opening_col6_reply_col5_red_col6_reply_col1_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col1_goal_unfold :
  opening_col6_reply_col5_red_col6_reply_col1_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col5_red_col6_reply_col1_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col1_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col5_red_col6_reply_col1_result_ongoing.
  - apply opening_col6_reply_col5_red_col6_reply_col1_turn_red.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col1_red_col6_state : game :=
  apply_move opening_col6_reply_col5_red_col6_reply_col1_state col6.

Lemma in_c4_next_opening_col6_reply_col5_red_col6_reply_col1_red_col6 :
  In opening_col6_reply_col5_red_col6_reply_col1_red_col6_state
     (c4_next opening_col6_reply_col5_red_col6_reply_col1_state).
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col1_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col5_red_col6_reply_col1_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col5_red_col6_reply_col1_result_ongoing.
  - unfold opening_col6_reply_col5_red_col6_reply_col1_state.
    unfold opening_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col1_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col1_red_col6_state ->
  opening_col6_reply_col5_red_col6_reply_col1_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col5_red_col6_reply_col1_goal_unfold).
  exists opening_col6_reply_col5_red_col6_reply_col1_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col1_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col1_red_col6_turn_yellow :
  next_turn opening_col6_reply_col5_red_col6_reply_col1_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col5_red_col6_reply_col1_state.
  unfold opening_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col1_red_col6_result_ongoing :
  get_result opening_col6_reply_col5_red_col6_reply_col1_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col5_red_col6_reply_col1_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col5_red_col6_reply_col1_red_col6_state m)
       (c4_next opening_col6_reply_col5_red_col6_reply_col1_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col5_red_col6_reply_col1_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col5_red_col6_reply_col1_red_col6_result_ongoing.
  - unfold opening_col6_reply_col5_red_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col5_red_col6_reply_col1_state.
    unfold opening_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col1_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col1_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col5_red_col6_reply_col1_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col5_red_col6_reply_col1_red_col6_state
                    opening_col6_reply_col5_red_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_reply_col1_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col1_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col5_red_col6_reply_col1_red_col6_state
                    opening_col6_reply_col5_red_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_reply_col1_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col5_red_col6_reply_col1_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col5_red_col6_reply_col1_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col1_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col6).

Lemma opening_col6_reply_col5_red_col6_reply_col1_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col6) ->
  opening_col6_reply_col5_red_col6_reply_col1_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col1_red_col6_subgoals_imply_child :
  opening_col6_reply_col5_red_col6_reply_col1_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col1_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col5_red_col6_reply_col1_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col1_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col5_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col1_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col5_red_col6_reply_col1_goal_if_red_col6_child.
  apply opening_col6_reply_col5_red_col6_reply_col1_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col2_state : game :=
  apply_move opening_col6_reply_col5_red_col6_state col2.

Definition opening_col6_reply_col5_red_col6_reply_col2_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col5_red_col6_reply_col2_state.

Lemma opening_col6_reply_col5_red_col6_reply_col2_turn_red :
  next_turn opening_col6_reply_col5_red_col6_reply_col2_state = red.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col2_state.
  unfold opening_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col2_result_ongoing :
  get_result opening_col6_reply_col5_red_col6_reply_col2_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col2_goal_unfold :
  opening_col6_reply_col5_red_col6_reply_col2_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col5_red_col6_reply_col2_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col2_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col5_red_col6_reply_col2_result_ongoing.
  - apply opening_col6_reply_col5_red_col6_reply_col2_turn_red.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col2_red_col6_state : game :=
  apply_move opening_col6_reply_col5_red_col6_reply_col2_state col6.

Lemma in_c4_next_opening_col6_reply_col5_red_col6_reply_col2_red_col6 :
  In opening_col6_reply_col5_red_col6_reply_col2_red_col6_state
     (c4_next opening_col6_reply_col5_red_col6_reply_col2_state).
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col2_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col5_red_col6_reply_col2_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col5_red_col6_reply_col2_result_ongoing.
  - unfold opening_col6_reply_col5_red_col6_reply_col2_state.
    unfold opening_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col2_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col2_red_col6_state ->
  opening_col6_reply_col5_red_col6_reply_col2_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col5_red_col6_reply_col2_goal_unfold).
  exists opening_col6_reply_col5_red_col6_reply_col2_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col2_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col2_red_col6_turn_yellow :
  next_turn opening_col6_reply_col5_red_col6_reply_col2_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col5_red_col6_reply_col2_state.
  unfold opening_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col2_red_col6_result_ongoing :
  get_result opening_col6_reply_col5_red_col6_reply_col2_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col5_red_col6_reply_col2_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col5_red_col6_reply_col2_red_col6_state m)
       (c4_next opening_col6_reply_col5_red_col6_reply_col2_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col5_red_col6_reply_col2_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col5_red_col6_reply_col2_red_col6_result_ongoing.
  - unfold opening_col6_reply_col5_red_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col5_red_col6_reply_col2_state.
    unfold opening_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col2_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col2_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col5_red_col6_reply_col2_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col5_red_col6_reply_col2_red_col6_state
                    opening_col6_reply_col5_red_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_reply_col2_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col2_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col5_red_col6_reply_col2_red_col6_state
                    opening_col6_reply_col5_red_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_reply_col2_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col5_red_col6_reply_col2_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col5_red_col6_reply_col2_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col2_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col6).

Lemma opening_col6_reply_col5_red_col6_reply_col2_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col6) ->
  opening_col6_reply_col5_red_col6_reply_col2_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col2_red_col6_subgoals_imply_child :
  opening_col6_reply_col5_red_col6_reply_col2_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col2_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col5_red_col6_reply_col2_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col2_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col5_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col2_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col5_red_col6_reply_col2_goal_if_red_col6_child.
  apply opening_col6_reply_col5_red_col6_reply_col2_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col3_state : game :=
  apply_move opening_col6_reply_col5_red_col6_state col3.

Definition opening_col6_reply_col5_red_col6_reply_col3_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col5_red_col6_reply_col3_state.

Lemma opening_col6_reply_col5_red_col6_reply_col3_turn_red :
  next_turn opening_col6_reply_col5_red_col6_reply_col3_state = red.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col3_state.
  unfold opening_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col3_result_ongoing :
  get_result opening_col6_reply_col5_red_col6_reply_col3_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col3_goal_unfold :
  opening_col6_reply_col5_red_col6_reply_col3_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col5_red_col6_reply_col3_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col3_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col5_red_col6_reply_col3_result_ongoing.
  - apply opening_col6_reply_col5_red_col6_reply_col3_turn_red.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col3_red_col6_state : game :=
  apply_move opening_col6_reply_col5_red_col6_reply_col3_state col6.

Lemma in_c4_next_opening_col6_reply_col5_red_col6_reply_col3_red_col6 :
  In opening_col6_reply_col5_red_col6_reply_col3_red_col6_state
     (c4_next opening_col6_reply_col5_red_col6_reply_col3_state).
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col3_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col5_red_col6_reply_col3_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col5_red_col6_reply_col3_result_ongoing.
  - unfold opening_col6_reply_col5_red_col6_reply_col3_state.
    unfold opening_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col3_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col3_red_col6_state ->
  opening_col6_reply_col5_red_col6_reply_col3_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col5_red_col6_reply_col3_goal_unfold).
  exists opening_col6_reply_col5_red_col6_reply_col3_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col3_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col3_red_col6_turn_yellow :
  next_turn opening_col6_reply_col5_red_col6_reply_col3_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col5_red_col6_reply_col3_state.
  unfold opening_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col3_red_col6_result_ongoing :
  get_result opening_col6_reply_col5_red_col6_reply_col3_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col5_red_col6_reply_col3_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col5_red_col6_reply_col3_red_col6_state m)
       (c4_next opening_col6_reply_col5_red_col6_reply_col3_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col5_red_col6_reply_col3_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col5_red_col6_reply_col3_red_col6_result_ongoing.
  - unfold opening_col6_reply_col5_red_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col5_red_col6_reply_col3_state.
    unfold opening_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col3_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col3_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col5_red_col6_reply_col3_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col5_red_col6_reply_col3_red_col6_state
                    opening_col6_reply_col5_red_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_reply_col3_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col3_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col5_red_col6_reply_col3_red_col6_state
                    opening_col6_reply_col5_red_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_reply_col3_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col5_red_col6_reply_col3_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col5_red_col6_reply_col3_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col3_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col6).

Lemma opening_col6_reply_col5_red_col6_reply_col3_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col6) ->
  opening_col6_reply_col5_red_col6_reply_col3_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col3_red_col6_subgoals_imply_child :
  opening_col6_reply_col5_red_col6_reply_col3_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col3_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col5_red_col6_reply_col3_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col3_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col5_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col3_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col5_red_col6_reply_col3_goal_if_red_col6_child.
  apply opening_col6_reply_col5_red_col6_reply_col3_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col4_state : game :=
  apply_move opening_col6_reply_col5_red_col6_state col4.

Definition opening_col6_reply_col5_red_col6_reply_col4_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col5_red_col6_reply_col4_state.

Lemma opening_col6_reply_col5_red_col6_reply_col4_turn_red :
  next_turn opening_col6_reply_col5_red_col6_reply_col4_state = red.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col4_state.
  unfold opening_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col4_result_ongoing :
  get_result opening_col6_reply_col5_red_col6_reply_col4_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col4_goal_unfold :
  opening_col6_reply_col5_red_col6_reply_col4_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col5_red_col6_reply_col4_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col4_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col5_red_col6_reply_col4_result_ongoing.
  - apply opening_col6_reply_col5_red_col6_reply_col4_turn_red.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col4_red_col6_state : game :=
  apply_move opening_col6_reply_col5_red_col6_reply_col4_state col6.

Lemma in_c4_next_opening_col6_reply_col5_red_col6_reply_col4_red_col6 :
  In opening_col6_reply_col5_red_col6_reply_col4_red_col6_state
     (c4_next opening_col6_reply_col5_red_col6_reply_col4_state).
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col4_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col5_red_col6_reply_col4_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col5_red_col6_reply_col4_result_ongoing.
  - unfold opening_col6_reply_col5_red_col6_reply_col4_state.
    unfold opening_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col4_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col4_red_col6_state ->
  opening_col6_reply_col5_red_col6_reply_col4_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col5_red_col6_reply_col4_goal_unfold).
  exists opening_col6_reply_col5_red_col6_reply_col4_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col4_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col4_red_col6_turn_yellow :
  next_turn opening_col6_reply_col5_red_col6_reply_col4_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col5_red_col6_reply_col4_state.
  unfold opening_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col4_red_col6_result_ongoing :
  get_result opening_col6_reply_col5_red_col6_reply_col4_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col5_red_col6_reply_col4_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col5_red_col6_reply_col4_red_col6_state m)
       (c4_next opening_col6_reply_col5_red_col6_reply_col4_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col5_red_col6_reply_col4_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col5_red_col6_reply_col4_red_col6_result_ongoing.
  - unfold opening_col6_reply_col5_red_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col5_red_col6_reply_col4_state.
    unfold opening_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col4_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col4_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col5_red_col6_reply_col4_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col5_red_col6_reply_col4_red_col6_state
                    opening_col6_reply_col5_red_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_reply_col4_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col4_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col5_red_col6_reply_col4_red_col6_state
                    opening_col6_reply_col5_red_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_reply_col4_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col5_red_col6_reply_col4_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col5_red_col6_reply_col4_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col4_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col6).

Lemma opening_col6_reply_col5_red_col6_reply_col4_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col6) ->
  opening_col6_reply_col5_red_col6_reply_col4_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col4_red_col6_subgoals_imply_child :
  opening_col6_reply_col5_red_col6_reply_col4_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col4_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col5_red_col6_reply_col4_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col4_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col5_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col4_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col5_red_col6_reply_col4_goal_if_red_col6_child.
  apply opening_col6_reply_col5_red_col6_reply_col4_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col5_state : game :=
  apply_move opening_col6_reply_col5_red_col6_state col5.

Definition opening_col6_reply_col5_red_col6_reply_col5_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col5_red_col6_reply_col5_state.

Lemma opening_col6_reply_col5_red_col6_reply_col5_turn_red :
  next_turn opening_col6_reply_col5_red_col6_reply_col5_state = red.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col5_state.
  unfold opening_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col5_result_ongoing :
  get_result opening_col6_reply_col5_red_col6_reply_col5_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col5_goal_unfold :
  opening_col6_reply_col5_red_col6_reply_col5_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col5_red_col6_reply_col5_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col5_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col5_red_col6_reply_col5_result_ongoing.
  - apply opening_col6_reply_col5_red_col6_reply_col5_turn_red.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col5_red_col6_state : game :=
  apply_move opening_col6_reply_col5_red_col6_reply_col5_state col6.

Lemma in_c4_next_opening_col6_reply_col5_red_col6_reply_col5_red_col6 :
  In opening_col6_reply_col5_red_col6_reply_col5_red_col6_state
     (c4_next opening_col6_reply_col5_red_col6_reply_col5_state).
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col5_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col5_red_col6_reply_col5_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col5_red_col6_reply_col5_result_ongoing.
  - unfold opening_col6_reply_col5_red_col6_reply_col5_state.
    unfold opening_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col5_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col5_red_col6_state ->
  opening_col6_reply_col5_red_col6_reply_col5_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col5_red_col6_reply_col5_goal_unfold).
  exists opening_col6_reply_col5_red_col6_reply_col5_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col5_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col5_red_col6_turn_yellow :
  next_turn opening_col6_reply_col5_red_col6_reply_col5_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col5_red_col6_reply_col5_state.
  unfold opening_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col5_red_col6_result_ongoing :
  get_result opening_col6_reply_col5_red_col6_reply_col5_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col5_red_col6_reply_col5_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state m)
       (c4_next opening_col6_reply_col5_red_col6_reply_col5_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col5_red_col6_reply_col5_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col5_red_col6_reply_col5_red_col6_result_ongoing.
  - unfold opening_col6_reply_col5_red_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col5_red_col6_reply_col5_state.
    unfold opening_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col5_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col5_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col5_red_col6_reply_col5_red_col6_state
                    opening_col6_reply_col5_red_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_reply_col5_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col5_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col5_red_col6_reply_col5_red_col6_state
                    opening_col6_reply_col5_red_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_reply_col5_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col5_red_col6_reply_col5_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col5_red_col6_reply_col5_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col5_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col6).

Lemma opening_col6_reply_col5_red_col6_reply_col5_red_col6_reply_subgoals_if_col6 :
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col5_red_col6_reply_col5_red_col6_reply_subgoals.
Proof.
  intro H6.
  repeat split.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col0);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col1);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col2);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col3);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col4);
      simpl; try lia; reflexivity.
  - apply (red_can_force_win_36_after_non_col6_if_parent_col6_vertical_threat
             opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col5);
      simpl; try lia; reflexivity.
  - exact H6.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col5_red_col6_subgoals_imply_child :
  opening_col6_reply_col5_red_col6_reply_col5_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col5_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col5_red_col6_reply_col5_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col5_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col5_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col5_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col5_red_col6_reply_col5_goal_if_red_col6_child.
  apply opening_col6_reply_col5_red_col6_reply_col5_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col6_state : game :=
  apply_move opening_col6_reply_col5_red_col6_state col6.

Definition opening_col6_reply_col5_red_col6_reply_col6_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col5_red_col6_reply_col6_state.

Lemma opening_col6_reply_col5_red_col6_reply_col6_turn_red :
  next_turn opening_col6_reply_col5_red_col6_reply_col6_state = red.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col6_state.
  unfold opening_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col6_result_ongoing :
  get_result opening_col6_reply_col5_red_col6_reply_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col6_goal_unfold :
  opening_col6_reply_col5_red_col6_reply_col6_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col5_red_col6_reply_col6_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col6_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col5_red_col6_reply_col6_result_ongoing.
  - apply opening_col6_reply_col5_red_col6_reply_col6_turn_red.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col6_red_col6_state : game :=
  apply_move opening_col6_reply_col5_red_col6_reply_col6_state col6.

Lemma in_c4_next_opening_col6_reply_col5_red_col6_reply_col6_red_col6 :
  In opening_col6_reply_col5_red_col6_reply_col6_red_col6_state
     (c4_next opening_col6_reply_col5_red_col6_reply_col6_state).
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col6_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col5_red_col6_reply_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col5_red_col6_reply_col6_result_ongoing.
  - unfold opening_col6_reply_col5_red_col6_reply_col6_state.
    unfold opening_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col6_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col6_red_col6_state ->
  opening_col6_reply_col5_red_col6_reply_col6_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col5_red_col6_reply_col6_goal_unfold).
  exists opening_col6_reply_col5_red_col6_reply_col6_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col6_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col6_red_col6_turn_yellow :
  next_turn opening_col6_reply_col5_red_col6_reply_col6_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col5_red_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col5_red_col6_reply_col6_state.
  unfold opening_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col6_red_col6_result_ongoing :
  get_result opening_col6_reply_col5_red_col6_reply_col6_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col5_red_col6_reply_col6_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col5_red_col6_reply_col6_red_col6_state m)
       (c4_next opening_col6_reply_col5_red_col6_reply_col6_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col5_red_col6_reply_col6_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col5_red_col6_reply_col6_red_col6_result_ongoing.
  - unfold opening_col6_reply_col5_red_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col5_red_col6_reply_col6_state.
    unfold opening_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col5_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col6_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col6_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col5_red_col6_reply_col6_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col5_red_col6_reply_col6_red_col6_state
                    opening_col6_reply_col5_red_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_reply_col6_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col6_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col5_red_col6_reply_col6_red_col6_state
                    opening_col6_reply_col5_red_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_reply_col6_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col5_red_col6_reply_col6_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col5_red_col6_reply_col6_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col6_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col6_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col6_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col6_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col6_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col6_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col5_red_col6_reply_col6_red_col6_state col6).

Lemma opening_col6_reply_col5_red_col6_reply_col6_red_col6_subgoals_imply_child :
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col5_red_col6_reply_col6_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col5_red_col6_reply_col6_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col6_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col6_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col5_red_col6_reply_col6_goal_if_red_col6_child.
  apply opening_col6_reply_col5_red_col6_reply_col6_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col0_raw_if_subgoals :
  opening_col6_reply_col5_red_col6_reply_col0_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col5_red_col6_state col0).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col5_red_col6_reply_col0_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col5_red_col6_reply_col0_state
                  opening_col6_reply_col5_red_col6_reply_col0_result_ongoing
                  opening_col6_reply_col5_red_col6_reply_col0_turn_red)).
  exists opening_col6_reply_col5_red_col6_reply_col0_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col0_red_col6.
  - apply opening_col6_reply_col5_red_col6_reply_col0_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col1_raw_if_subgoals :
  opening_col6_reply_col5_red_col6_reply_col1_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col5_red_col6_state col1).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col5_red_col6_reply_col1_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col5_red_col6_reply_col1_state
                  opening_col6_reply_col5_red_col6_reply_col1_result_ongoing
                  opening_col6_reply_col5_red_col6_reply_col1_turn_red)).
  exists opening_col6_reply_col5_red_col6_reply_col1_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col1_red_col6.
  - apply opening_col6_reply_col5_red_col6_reply_col1_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col2_raw_if_subgoals :
  opening_col6_reply_col5_red_col6_reply_col2_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col5_red_col6_state col2).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col5_red_col6_reply_col2_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col5_red_col6_reply_col2_state
                  opening_col6_reply_col5_red_col6_reply_col2_result_ongoing
                  opening_col6_reply_col5_red_col6_reply_col2_turn_red)).
  exists opening_col6_reply_col5_red_col6_reply_col2_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col2_red_col6.
  - apply opening_col6_reply_col5_red_col6_reply_col2_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col3_raw_if_subgoals :
  opening_col6_reply_col5_red_col6_reply_col3_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col5_red_col6_state col3).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col5_red_col6_reply_col3_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col5_red_col6_reply_col3_state
                  opening_col6_reply_col5_red_col6_reply_col3_result_ongoing
                  opening_col6_reply_col5_red_col6_reply_col3_turn_red)).
  exists opening_col6_reply_col5_red_col6_reply_col3_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col3_red_col6.
  - apply opening_col6_reply_col5_red_col6_reply_col3_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col4_raw_if_subgoals :
  opening_col6_reply_col5_red_col6_reply_col4_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col5_red_col6_state col4).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col5_red_col6_reply_col4_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col5_red_col6_reply_col4_state
                  opening_col6_reply_col5_red_col6_reply_col4_result_ongoing
                  opening_col6_reply_col5_red_col6_reply_col4_turn_red)).
  exists opening_col6_reply_col5_red_col6_reply_col4_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col4_red_col6.
  - apply opening_col6_reply_col5_red_col6_reply_col4_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col5_raw_if_subgoals :
  opening_col6_reply_col5_red_col6_reply_col5_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col5_red_col6_state col5).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col5_red_col6_reply_col5_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col5_red_col6_reply_col5_state
                  opening_col6_reply_col5_red_col6_reply_col5_result_ongoing
                  opening_col6_reply_col5_red_col6_reply_col5_turn_red)).
  exists opening_col6_reply_col5_red_col6_reply_col5_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col5_red_col6.
  - apply opening_col6_reply_col5_red_col6_reply_col5_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col5_red_col6_reply_col6_raw_if_subgoals :
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col5_red_col6_state col6).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col5_red_col6_reply_col6_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col5_red_col6_reply_col6_state
                  opening_col6_reply_col5_red_col6_reply_col6_result_ongoing
                  opening_col6_reply_col5_red_col6_reply_col6_turn_red)).
  exists opening_col6_reply_col5_red_col6_reply_col6_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col5_red_col6_reply_col6_red_col6.
  - apply opening_col6_reply_col5_red_col6_reply_col6_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col5_raw_if_all_reply_subgoal_blocks :
  opening_col6_reply_col5_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 opening_col6_reply_col5_state.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  apply (proj2 (red_can_force_win_unfold_ongoing_red 39
                  opening_col6_reply_col5_state
                  opening_col6_reply_col5_result_ongoing
                  opening_col6_reply_col5_turn_red)).
  exists opening_col6_reply_col5_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col5_red_col6.
  - apply (proj2 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col5_red_col6_state
                    opening_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col5_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col5_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col5_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    destruct m.
    + apply opening_col6_reply_col5_red_col6_reply_col0_raw_if_subgoals; exact H0.
    + apply opening_col6_reply_col5_red_col6_reply_col1_raw_if_subgoals; exact H1.
    + apply opening_col6_reply_col5_red_col6_reply_col2_raw_if_subgoals; exact H2.
    + apply opening_col6_reply_col5_red_col6_reply_col3_raw_if_subgoals; exact H3.
    + apply opening_col6_reply_col5_red_col6_reply_col4_raw_if_subgoals; exact H4.
    + apply opening_col6_reply_col5_red_col6_reply_col5_raw_if_subgoals; exact H5.
    + apply opening_col6_reply_col5_red_col6_reply_col6_raw_if_subgoals; exact H6.
Qed.

Lemma opening_col6_reply_col5_goal_if_all_reply_subgoal_blocks :
  opening_col6_reply_col5_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col5_goal.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  apply opening_col6_reply_col5_raw_if_all_reply_subgoal_blocks; assumption.
Qed.

Lemma opening_col6_reply_col5_firstconj_if_all_reply_subgoal_blocks :
  opening_col6_reply_col5_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col5).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  change (red_can_force_win 40 opening_col6_reply_col5_state).
  apply opening_col6_reply_col5_raw_if_all_reply_subgoal_blocks; assumption.
Qed.

Lemma opening_col6_reply_col5_firstconj_if_col5col0to5_col6_and_col5col6_block :
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col5).
Proof.
  intros H50c6 H51c6 H52c6 H53c6 H54c6 H55c6 H56.
  apply opening_col6_reply_col5_firstconj_if_all_reply_subgoal_blocks.
  - apply opening_col6_reply_col5_red_col6_reply_col0_red_col6_reply_subgoals_if_col6.
    exact H50c6.
  - apply opening_col6_reply_col5_red_col6_reply_col1_red_col6_reply_subgoals_if_col6.
    exact H51c6.
  - apply opening_col6_reply_col5_red_col6_reply_col2_red_col6_reply_subgoals_if_col6.
    exact H52c6.
  - apply opening_col6_reply_col5_red_col6_reply_col3_red_col6_reply_subgoals_if_col6.
    exact H53c6.
  - apply opening_col6_reply_col5_red_col6_reply_col4_red_col6_reply_subgoals_if_col6.
    exact H54c6.
  - apply opening_col6_reply_col5_red_col6_reply_col5_red_col6_reply_subgoals_if_col6.
    exact H55c6.
  - exact H56.
Qed.

Definition opening_col6_reply_col6_state : game :=
  apply_move opening_col6_state col6.

Definition opening_col6_reply_col6_goal : Prop :=
  red_can_force_win 40 opening_col6_reply_col6_state.

Lemma opening_col6_reply_col6_turn_red :
  next_turn opening_col6_reply_col6_state = red.
Proof.
  unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_result_ongoing :
  get_result opening_col6_reply_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_goal_unfold :
  opening_col6_reply_col6_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col6_state) /\
    red_can_force_win 39 g.
Proof.
  unfold opening_col6_reply_col6_goal.
  change 40 with (S 39).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col6_result_ongoing.
  - apply opening_col6_reply_col6_turn_red.
Qed.

Definition opening_col6_reply_col6_red_col6_state : game :=
  apply_move opening_col6_reply_col6_state col6.

Lemma in_c4_next_opening_col6_reply_col6_red_col6 :
  In opening_col6_reply_col6_red_col6_state
     (c4_next opening_col6_reply_col6_state).
Proof.
  unfold opening_col6_reply_col6_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col6_result_ongoing.
  - unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col6_goal_if_red_col6_child :
  red_can_force_win 39 opening_col6_reply_col6_red_col6_state ->
  opening_col6_reply_col6_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col6_goal_unfold).
  exists opening_col6_reply_col6_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col6_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col6_red_col6_turn_yellow :
  next_turn opening_col6_reply_col6_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_result_ongoing :
  get_result opening_col6_reply_col6_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col6_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col6_red_col6_state m)
       (c4_next opening_col6_reply_col6_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col6_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col6_red_col6_result_ongoing.
  - unfold opening_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col6_red_col6_move_form :
  red_can_force_win 39 opening_col6_reply_col6_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 38
      (apply_move opening_col6_reply_col6_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col6_red_col6_state
                    opening_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col6_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col6_red_col6_state
                    opening_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col6_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col6_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_subgoals : Prop :=
  red_can_force_win 38 (apply_move opening_col6_reply_col6_red_col6_state col0) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col6_red_col6_state col1) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col6_red_col6_state col2) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col6_red_col6_state col3) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col6_red_col6_state col4) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col6_red_col6_state col5) /\
  red_can_force_win 38 (apply_move opening_col6_reply_col6_red_col6_state col6).

Lemma opening_col6_reply_col6_red_col6_subgoals_imply_child :
  opening_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 39 opening_col6_reply_col6_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col6_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col6_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col6_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col6_goal_if_red_col6_child.
  apply opening_col6_reply_col6_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col0_state : game :=
  apply_move opening_col6_reply_col6_red_col6_state col0.

Definition opening_col6_reply_col6_red_col6_reply_col0_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col6_red_col6_reply_col0_state.

Lemma opening_col6_reply_col6_red_col6_reply_col0_turn_red :
  next_turn opening_col6_reply_col6_red_col6_reply_col0_state = red.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col0_state.
  unfold opening_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col0_result_ongoing :
  get_result opening_col6_reply_col6_red_col6_reply_col0_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col0_goal_unfold :
  opening_col6_reply_col6_red_col6_reply_col0_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col6_red_col6_reply_col0_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col0_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col6_red_col6_reply_col0_result_ongoing.
  - apply opening_col6_reply_col6_red_col6_reply_col0_turn_red.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col0_red_col6_state : game :=
  apply_move opening_col6_reply_col6_red_col6_reply_col0_state col6.

Lemma in_c4_next_opening_col6_reply_col6_red_col6_reply_col0_red_col6 :
  In opening_col6_reply_col6_red_col6_reply_col0_red_col6_state
     (c4_next opening_col6_reply_col6_red_col6_reply_col0_state).
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col0_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col6_red_col6_reply_col0_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col6_red_col6_reply_col0_result_ongoing.
  - unfold opening_col6_reply_col6_red_col6_reply_col0_state.
    unfold opening_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col0_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col0_red_col6_state ->
  opening_col6_reply_col6_red_col6_reply_col0_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col6_red_col6_reply_col0_goal_unfold).
  exists opening_col6_reply_col6_red_col6_reply_col0_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col0_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col0_red_col6_turn_yellow :
  next_turn opening_col6_reply_col6_red_col6_reply_col0_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col0_red_col6_state.
  unfold opening_col6_reply_col6_red_col6_reply_col0_state.
  unfold opening_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col0_red_col6_result_ongoing :
  get_result opening_col6_reply_col6_red_col6_reply_col0_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col6_red_col6_reply_col0_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state m)
       (c4_next opening_col6_reply_col6_red_col6_reply_col0_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col6_red_col6_reply_col0_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col6_red_col6_reply_col0_red_col6_result_ongoing.
  - unfold opening_col6_reply_col6_red_col6_reply_col0_red_col6_state.
    unfold opening_col6_reply_col6_red_col6_reply_col0_state.
    unfold opening_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col0_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col0_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col6_red_col6_reply_col0_red_col6_state
                    opening_col6_reply_col6_red_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_reply_col0_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col0_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col6_red_col6_reply_col0_red_col6_state
                    opening_col6_reply_col6_red_col6_reply_col0_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_reply_col0_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col6_red_col6_reply_col0_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col6_red_col6_reply_col0_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col0_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col6).

Lemma opening_col6_reply_col6_red_col6_reply_col0_red_col6_subgoals_imply_child :
  opening_col6_reply_col6_red_col6_reply_col0_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col0_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col6_red_col6_reply_col0_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col0_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col6_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col0_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col6_red_col6_reply_col0_goal_if_red_col6_child.
  apply opening_col6_reply_col6_red_col6_reply_col0_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col1_state : game :=
  apply_move opening_col6_reply_col6_red_col6_state col1.

Definition opening_col6_reply_col6_red_col6_reply_col1_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col6_red_col6_reply_col1_state.

Lemma opening_col6_reply_col6_red_col6_reply_col1_turn_red :
  next_turn opening_col6_reply_col6_red_col6_reply_col1_state = red.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col1_state.
  unfold opening_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col1_result_ongoing :
  get_result opening_col6_reply_col6_red_col6_reply_col1_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col1_goal_unfold :
  opening_col6_reply_col6_red_col6_reply_col1_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col6_red_col6_reply_col1_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col1_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col6_red_col6_reply_col1_result_ongoing.
  - apply opening_col6_reply_col6_red_col6_reply_col1_turn_red.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col1_red_col6_state : game :=
  apply_move opening_col6_reply_col6_red_col6_reply_col1_state col6.

Lemma in_c4_next_opening_col6_reply_col6_red_col6_reply_col1_red_col6 :
  In opening_col6_reply_col6_red_col6_reply_col1_red_col6_state
     (c4_next opening_col6_reply_col6_red_col6_reply_col1_state).
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col1_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col6_red_col6_reply_col1_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col6_red_col6_reply_col1_result_ongoing.
  - unfold opening_col6_reply_col6_red_col6_reply_col1_state.
    unfold opening_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col1_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col1_red_col6_state ->
  opening_col6_reply_col6_red_col6_reply_col1_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col6_red_col6_reply_col1_goal_unfold).
  exists opening_col6_reply_col6_red_col6_reply_col1_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col1_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col1_red_col6_turn_yellow :
  next_turn opening_col6_reply_col6_red_col6_reply_col1_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col1_red_col6_state.
  unfold opening_col6_reply_col6_red_col6_reply_col1_state.
  unfold opening_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col1_red_col6_result_ongoing :
  get_result opening_col6_reply_col6_red_col6_reply_col1_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col6_red_col6_reply_col1_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state m)
       (c4_next opening_col6_reply_col6_red_col6_reply_col1_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col6_red_col6_reply_col1_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col6_red_col6_reply_col1_red_col6_result_ongoing.
  - unfold opening_col6_reply_col6_red_col6_reply_col1_red_col6_state.
    unfold opening_col6_reply_col6_red_col6_reply_col1_state.
    unfold opening_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col1_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col1_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col6_red_col6_reply_col1_red_col6_state
                    opening_col6_reply_col6_red_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_reply_col1_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col1_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col6_red_col6_reply_col1_red_col6_state
                    opening_col6_reply_col6_red_col6_reply_col1_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_reply_col1_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col6_red_col6_reply_col1_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col6_red_col6_reply_col1_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col1_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col6).

Lemma opening_col6_reply_col6_red_col6_reply_col1_red_col6_subgoals_imply_child :
  opening_col6_reply_col6_red_col6_reply_col1_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col1_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col6_red_col6_reply_col1_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col1_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col6_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col1_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col6_red_col6_reply_col1_goal_if_red_col6_child.
  apply opening_col6_reply_col6_red_col6_reply_col1_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col2_state : game :=
  apply_move opening_col6_reply_col6_red_col6_state col2.

Definition opening_col6_reply_col6_red_col6_reply_col2_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col6_red_col6_reply_col2_state.

Lemma opening_col6_reply_col6_red_col6_reply_col2_turn_red :
  next_turn opening_col6_reply_col6_red_col6_reply_col2_state = red.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col2_state.
  unfold opening_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col2_result_ongoing :
  get_result opening_col6_reply_col6_red_col6_reply_col2_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col2_goal_unfold :
  opening_col6_reply_col6_red_col6_reply_col2_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col6_red_col6_reply_col2_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col2_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col6_red_col6_reply_col2_result_ongoing.
  - apply opening_col6_reply_col6_red_col6_reply_col2_turn_red.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col2_red_col6_state : game :=
  apply_move opening_col6_reply_col6_red_col6_reply_col2_state col6.

Lemma in_c4_next_opening_col6_reply_col6_red_col6_reply_col2_red_col6 :
  In opening_col6_reply_col6_red_col6_reply_col2_red_col6_state
     (c4_next opening_col6_reply_col6_red_col6_reply_col2_state).
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col2_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col6_red_col6_reply_col2_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col6_red_col6_reply_col2_result_ongoing.
  - unfold opening_col6_reply_col6_red_col6_reply_col2_state.
    unfold opening_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col2_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col2_red_col6_state ->
  opening_col6_reply_col6_red_col6_reply_col2_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col6_red_col6_reply_col2_goal_unfold).
  exists opening_col6_reply_col6_red_col6_reply_col2_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col2_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col2_red_col6_turn_yellow :
  next_turn opening_col6_reply_col6_red_col6_reply_col2_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col2_red_col6_state.
  unfold opening_col6_reply_col6_red_col6_reply_col2_state.
  unfold opening_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col2_red_col6_result_ongoing :
  get_result opening_col6_reply_col6_red_col6_reply_col2_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col6_red_col6_reply_col2_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state m)
       (c4_next opening_col6_reply_col6_red_col6_reply_col2_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col6_red_col6_reply_col2_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col6_red_col6_reply_col2_red_col6_result_ongoing.
  - unfold opening_col6_reply_col6_red_col6_reply_col2_red_col6_state.
    unfold opening_col6_reply_col6_red_col6_reply_col2_state.
    unfold opening_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col2_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col2_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col6_red_col6_reply_col2_red_col6_state
                    opening_col6_reply_col6_red_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_reply_col2_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col2_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col6_red_col6_reply_col2_red_col6_state
                    opening_col6_reply_col6_red_col6_reply_col2_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_reply_col2_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col6_red_col6_reply_col2_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col6_red_col6_reply_col2_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col2_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col6).

Lemma opening_col6_reply_col6_red_col6_reply_col2_red_col6_subgoals_imply_child :
  opening_col6_reply_col6_red_col6_reply_col2_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col2_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col6_red_col6_reply_col2_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col2_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col6_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col2_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col6_red_col6_reply_col2_goal_if_red_col6_child.
  apply opening_col6_reply_col6_red_col6_reply_col2_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col3_state : game :=
  apply_move opening_col6_reply_col6_red_col6_state col3.

Definition opening_col6_reply_col6_red_col6_reply_col3_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col6_red_col6_reply_col3_state.

Lemma opening_col6_reply_col6_red_col6_reply_col3_turn_red :
  next_turn opening_col6_reply_col6_red_col6_reply_col3_state = red.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col3_state.
  unfold opening_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col3_result_ongoing :
  get_result opening_col6_reply_col6_red_col6_reply_col3_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col3_goal_unfold :
  opening_col6_reply_col6_red_col6_reply_col3_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col6_red_col6_reply_col3_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col3_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col6_red_col6_reply_col3_result_ongoing.
  - apply opening_col6_reply_col6_red_col6_reply_col3_turn_red.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col3_red_col6_state : game :=
  apply_move opening_col6_reply_col6_red_col6_reply_col3_state col6.

Lemma in_c4_next_opening_col6_reply_col6_red_col6_reply_col3_red_col6 :
  In opening_col6_reply_col6_red_col6_reply_col3_red_col6_state
     (c4_next opening_col6_reply_col6_red_col6_reply_col3_state).
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col3_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col6_red_col6_reply_col3_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col6_red_col6_reply_col3_result_ongoing.
  - unfold opening_col6_reply_col6_red_col6_reply_col3_state.
    unfold opening_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col3_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col3_red_col6_state ->
  opening_col6_reply_col6_red_col6_reply_col3_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col6_red_col6_reply_col3_goal_unfold).
  exists opening_col6_reply_col6_red_col6_reply_col3_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col3_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col3_red_col6_turn_yellow :
  next_turn opening_col6_reply_col6_red_col6_reply_col3_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col3_red_col6_state.
  unfold opening_col6_reply_col6_red_col6_reply_col3_state.
  unfold opening_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col3_red_col6_result_ongoing :
  get_result opening_col6_reply_col6_red_col6_reply_col3_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col6_red_col6_reply_col3_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state m)
       (c4_next opening_col6_reply_col6_red_col6_reply_col3_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col6_red_col6_reply_col3_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col6_red_col6_reply_col3_red_col6_result_ongoing.
  - unfold opening_col6_reply_col6_red_col6_reply_col3_red_col6_state.
    unfold opening_col6_reply_col6_red_col6_reply_col3_state.
    unfold opening_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col3_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col3_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col6_red_col6_reply_col3_red_col6_state
                    opening_col6_reply_col6_red_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_reply_col3_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col3_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col6_red_col6_reply_col3_red_col6_state
                    opening_col6_reply_col6_red_col6_reply_col3_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_reply_col3_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col6_red_col6_reply_col3_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col6_red_col6_reply_col3_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col3_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col6).

Lemma opening_col6_reply_col6_red_col6_reply_col3_red_col6_subgoals_imply_child :
  opening_col6_reply_col6_red_col6_reply_col3_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col3_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col6_red_col6_reply_col3_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col3_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col6_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col3_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col6_red_col6_reply_col3_goal_if_red_col6_child.
  apply opening_col6_reply_col6_red_col6_reply_col3_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col4_state : game :=
  apply_move opening_col6_reply_col6_red_col6_state col4.

Definition opening_col6_reply_col6_red_col6_reply_col4_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col6_red_col6_reply_col4_state.

Lemma opening_col6_reply_col6_red_col6_reply_col4_turn_red :
  next_turn opening_col6_reply_col6_red_col6_reply_col4_state = red.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col4_state.
  unfold opening_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col4_result_ongoing :
  get_result opening_col6_reply_col6_red_col6_reply_col4_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col4_goal_unfold :
  opening_col6_reply_col6_red_col6_reply_col4_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col6_red_col6_reply_col4_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col4_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col6_red_col6_reply_col4_result_ongoing.
  - apply opening_col6_reply_col6_red_col6_reply_col4_turn_red.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col4_red_col6_state : game :=
  apply_move opening_col6_reply_col6_red_col6_reply_col4_state col6.

Lemma in_c4_next_opening_col6_reply_col6_red_col6_reply_col4_red_col6 :
  In opening_col6_reply_col6_red_col6_reply_col4_red_col6_state
     (c4_next opening_col6_reply_col6_red_col6_reply_col4_state).
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col4_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col6_red_col6_reply_col4_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col6_red_col6_reply_col4_result_ongoing.
  - unfold opening_col6_reply_col6_red_col6_reply_col4_state.
    unfold opening_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col4_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col4_red_col6_state ->
  opening_col6_reply_col6_red_col6_reply_col4_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col6_red_col6_reply_col4_goal_unfold).
  exists opening_col6_reply_col6_red_col6_reply_col4_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col4_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col4_red_col6_turn_yellow :
  next_turn opening_col6_reply_col6_red_col6_reply_col4_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col4_red_col6_state.
  unfold opening_col6_reply_col6_red_col6_reply_col4_state.
  unfold opening_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col4_red_col6_result_ongoing :
  get_result opening_col6_reply_col6_red_col6_reply_col4_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col6_red_col6_reply_col4_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state m)
       (c4_next opening_col6_reply_col6_red_col6_reply_col4_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col6_red_col6_reply_col4_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col6_red_col6_reply_col4_red_col6_result_ongoing.
  - unfold opening_col6_reply_col6_red_col6_reply_col4_red_col6_state.
    unfold opening_col6_reply_col6_red_col6_reply_col4_state.
    unfold opening_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col4_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col4_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col6_red_col6_reply_col4_red_col6_state
                    opening_col6_reply_col6_red_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_reply_col4_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col4_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col6_red_col6_reply_col4_red_col6_state
                    opening_col6_reply_col6_red_col6_reply_col4_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_reply_col4_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col6_red_col6_reply_col4_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col6_red_col6_reply_col4_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col4_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col6).

Lemma opening_col6_reply_col6_red_col6_reply_col4_red_col6_subgoals_imply_child :
  opening_col6_reply_col6_red_col6_reply_col4_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col4_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col6_red_col6_reply_col4_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col4_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col6_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col4_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col6_red_col6_reply_col4_goal_if_red_col6_child.
  apply opening_col6_reply_col6_red_col6_reply_col4_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col5_state : game :=
  apply_move opening_col6_reply_col6_red_col6_state col5.

Definition opening_col6_reply_col6_red_col6_reply_col5_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col6_red_col6_reply_col5_state.

Lemma opening_col6_reply_col6_red_col6_reply_col5_turn_red :
  next_turn opening_col6_reply_col6_red_col6_reply_col5_state = red.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col5_state.
  unfold opening_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col5_result_ongoing :
  get_result opening_col6_reply_col6_red_col6_reply_col5_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col5_goal_unfold :
  opening_col6_reply_col6_red_col6_reply_col5_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col6_red_col6_reply_col5_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col5_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col6_red_col6_reply_col5_result_ongoing.
  - apply opening_col6_reply_col6_red_col6_reply_col5_turn_red.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col5_red_col6_state : game :=
  apply_move opening_col6_reply_col6_red_col6_reply_col5_state col6.

Lemma in_c4_next_opening_col6_reply_col6_red_col6_reply_col5_red_col6 :
  In opening_col6_reply_col6_red_col6_reply_col5_red_col6_state
     (c4_next opening_col6_reply_col6_red_col6_reply_col5_state).
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col5_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col6_red_col6_reply_col5_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col6_red_col6_reply_col5_result_ongoing.
  - unfold opening_col6_reply_col6_red_col6_reply_col5_state.
    unfold opening_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col5_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col5_red_col6_state ->
  opening_col6_reply_col6_red_col6_reply_col5_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col6_red_col6_reply_col5_goal_unfold).
  exists opening_col6_reply_col6_red_col6_reply_col5_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col5_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col5_red_col6_turn_yellow :
  next_turn opening_col6_reply_col6_red_col6_reply_col5_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col5_red_col6_state.
  unfold opening_col6_reply_col6_red_col6_reply_col5_state.
  unfold opening_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col5_red_col6_result_ongoing :
  get_result opening_col6_reply_col6_red_col6_reply_col5_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col6_red_col6_reply_col5_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state m)
       (c4_next opening_col6_reply_col6_red_col6_reply_col5_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col6_red_col6_reply_col5_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col6_red_col6_reply_col5_red_col6_result_ongoing.
  - unfold opening_col6_reply_col6_red_col6_reply_col5_red_col6_state.
    unfold opening_col6_reply_col6_red_col6_reply_col5_state.
    unfold opening_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col5_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col5_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col6_red_col6_reply_col5_red_col6_state
                    opening_col6_reply_col6_red_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_reply_col5_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col5_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col6_red_col6_reply_col5_red_col6_state
                    opening_col6_reply_col6_red_col6_reply_col5_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_reply_col5_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col6_red_col6_reply_col5_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col6_red_col6_reply_col5_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col5_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state col6).

Lemma opening_col6_reply_col6_red_col6_reply_col5_red_col6_subgoals_imply_child :
  opening_col6_reply_col6_red_col6_reply_col5_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col5_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col6_red_col6_reply_col5_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col5_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col6_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col5_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col6_red_col6_reply_col5_goal_if_red_col6_child.
  apply opening_col6_reply_col6_red_col6_reply_col5_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col6_state : game :=
  apply_move opening_col6_reply_col6_red_col6_state col6.

Definition opening_col6_reply_col6_red_col6_reply_col6_goal : Prop :=
  red_can_force_win 38 opening_col6_reply_col6_red_col6_reply_col6_state.

Lemma opening_col6_reply_col6_red_col6_reply_col6_turn_red :
  next_turn opening_col6_reply_col6_red_col6_reply_col6_state = red.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col6_state.
  unfold opening_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col6_result_ongoing :
  get_result opening_col6_reply_col6_red_col6_reply_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col6_goal_unfold :
  opening_col6_reply_col6_red_col6_reply_col6_goal <->
  exists g,
    In g (c4_next opening_col6_reply_col6_red_col6_reply_col6_state) /\
    red_can_force_win 37 g.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col6_goal.
  change 38 with (S 37).
  apply red_can_force_win_unfold_ongoing_red.
  - apply opening_col6_reply_col6_red_col6_reply_col6_result_ongoing.
  - apply opening_col6_reply_col6_red_col6_reply_col6_turn_red.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col6_red_col6_state : game :=
  apply_move opening_col6_reply_col6_red_col6_reply_col6_state col6.

Lemma in_c4_next_opening_col6_reply_col6_red_col6_reply_col6_red_col6 :
  In opening_col6_reply_col6_red_col6_reply_col6_red_col6_state
     (c4_next opening_col6_reply_col6_red_col6_reply_col6_state).
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col6_red_col6_state.
  unfold c4_next.
  rewrite opening_col6_reply_col6_red_col6_reply_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col6_red_col6_reply_col6_result_ongoing.
  - unfold opening_col6_reply_col6_red_col6_reply_col6_state.
    unfold opening_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
    simpl.
    lia.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col6_goal_if_red_col6_child :
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col6_red_col6_state ->
  opening_col6_reply_col6_red_col6_reply_col6_goal.
Proof.
  intro Hchild.
  apply (proj2 opening_col6_reply_col6_red_col6_reply_col6_goal_unfold).
  exists opening_col6_reply_col6_red_col6_reply_col6_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col6_red_col6.
  - exact Hchild.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col6_red_col6_turn_yellow :
  next_turn opening_col6_reply_col6_red_col6_reply_col6_red_col6_state = yellow.
Proof.
  unfold opening_col6_reply_col6_red_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col6_red_col6_reply_col6_state.
  unfold opening_col6_reply_col6_red_col6_state.
  unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
  simpl.
  reflexivity.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col6_red_col6_result_ongoing :
  get_result opening_col6_reply_col6_red_col6_reply_col6_red_col6_state = ongoing.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma in_c4_next_opening_col6_reply_col6_red_col6_reply_col6_red_col6_of_all_moves :
  forall m,
    In m all_moves ->
    In (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state m)
       (c4_next opening_col6_reply_col6_red_col6_reply_col6_red_col6_state).
Proof.
  intros m Hinm.
  unfold c4_next.
  rewrite opening_col6_reply_col6_red_col6_reply_col6_red_col6_result_ongoing.
  apply in_map.
  apply moves_complete.
  constructor.
  - exact opening_col6_reply_col6_red_col6_reply_col6_red_col6_result_ongoing.
  - unfold opening_col6_reply_col6_red_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col6_red_col6_reply_col6_state.
    unfold opening_col6_reply_col6_red_col6_state.
    unfold opening_col6_reply_col6_state, opening_col6_state, c4_init.
    destruct m; simpl; lia.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col6_red_col6_move_form :
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col6_red_col6_state <->
  forall m,
    In m all_moves ->
    red_can_force_win 36
      (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state m).
Proof.
  split.
  - intros Hwin m Hinm.
    apply (proj1 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col6_red_col6_reply_col6_red_col6_state
                    opening_col6_reply_col6_red_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_reply_col6_red_col6_turn_yellow) Hwin).
    apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col6_red_col6_of_all_moves.
    exact Hinm.
  - intros Hmoves.
    apply (proj2 (red_can_force_win_unfold_ongoing_yellow 36
                    opening_col6_reply_col6_red_col6_reply_col6_red_col6_state
                    opening_col6_reply_col6_red_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_reply_col6_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col6_red_col6_reply_col6_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col6_red_col6_reply_col6_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    apply Hmoves.
    exact Hinall.
Qed.

Definition opening_col6_reply_col6_red_col6_reply_col6_red_col6_reply_subgoals : Prop :=
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col0) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col1) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col2) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col3) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col4) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col5) /\
  red_can_force_win 36 (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col6).

Lemma opening_col6_reply_col6_red_col6_reply_col6_red_col6_subgoals_imply_child :
  opening_col6_reply_col6_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 37 opening_col6_reply_col6_red_col6_reply_col6_red_col6_state.
Proof.
  intros Hsubs.
  apply (proj2 opening_col6_reply_col6_red_col6_reply_col6_red_col6_move_form).
  intros m _.
  destruct Hsubs as [H0 [H1 [H2 [H3 [H4 [H5 H6]]]]]].
  destruct m; assumption.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col6_goal_if_red_col6_reply_subgoals :
  opening_col6_reply_col6_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col6_goal.
Proof.
  intro Hsubs.
  apply opening_col6_reply_col6_red_col6_reply_col6_goal_if_red_col6_child.
  apply opening_col6_reply_col6_red_col6_reply_col6_red_col6_subgoals_imply_child.
  exact Hsubs.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col0_raw_if_subgoals :
  opening_col6_reply_col6_red_col6_reply_col0_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col6_red_col6_state col0).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col6_red_col6_reply_col0_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col6_red_col6_reply_col0_state
                  opening_col6_reply_col6_red_col6_reply_col0_result_ongoing
                  opening_col6_reply_col6_red_col6_reply_col0_turn_red)).
  exists opening_col6_reply_col6_red_col6_reply_col0_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col0_red_col6.
  - apply opening_col6_reply_col6_red_col6_reply_col0_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col1_raw_if_subgoals :
  opening_col6_reply_col6_red_col6_reply_col1_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col6_red_col6_state col1).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col6_red_col6_reply_col1_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col6_red_col6_reply_col1_state
                  opening_col6_reply_col6_red_col6_reply_col1_result_ongoing
                  opening_col6_reply_col6_red_col6_reply_col1_turn_red)).
  exists opening_col6_reply_col6_red_col6_reply_col1_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col1_red_col6.
  - apply opening_col6_reply_col6_red_col6_reply_col1_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col2_raw_if_subgoals :
  opening_col6_reply_col6_red_col6_reply_col2_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col6_red_col6_state col2).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col6_red_col6_reply_col2_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col6_red_col6_reply_col2_state
                  opening_col6_reply_col6_red_col6_reply_col2_result_ongoing
                  opening_col6_reply_col6_red_col6_reply_col2_turn_red)).
  exists opening_col6_reply_col6_red_col6_reply_col2_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col2_red_col6.
  - apply opening_col6_reply_col6_red_col6_reply_col2_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col3_raw_if_subgoals :
  opening_col6_reply_col6_red_col6_reply_col3_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col6_red_col6_state col3).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col6_red_col6_reply_col3_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col6_red_col6_reply_col3_state
                  opening_col6_reply_col6_red_col6_reply_col3_result_ongoing
                  opening_col6_reply_col6_red_col6_reply_col3_turn_red)).
  exists opening_col6_reply_col6_red_col6_reply_col3_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col3_red_col6.
  - apply opening_col6_reply_col6_red_col6_reply_col3_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col4_raw_if_subgoals :
  opening_col6_reply_col6_red_col6_reply_col4_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col6_red_col6_state col4).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col6_red_col6_reply_col4_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col6_red_col6_reply_col4_state
                  opening_col6_reply_col6_red_col6_reply_col4_result_ongoing
                  opening_col6_reply_col6_red_col6_reply_col4_turn_red)).
  exists opening_col6_reply_col6_red_col6_reply_col4_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col4_red_col6.
  - apply opening_col6_reply_col6_red_col6_reply_col4_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col5_raw_if_subgoals :
  opening_col6_reply_col6_red_col6_reply_col5_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col6_red_col6_state col5).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col6_red_col6_reply_col5_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col6_red_col6_reply_col5_state
                  opening_col6_reply_col6_red_col6_reply_col5_result_ongoing
                  opening_col6_reply_col6_red_col6_reply_col5_turn_red)).
  exists opening_col6_reply_col6_red_col6_reply_col5_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col5_red_col6.
  - apply opening_col6_reply_col6_red_col6_reply_col5_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col6_red_col6_reply_col6_raw_if_subgoals :
  opening_col6_reply_col6_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 38 (apply_move opening_col6_reply_col6_red_col6_state col6).
Proof.
  intro Hsubs.
  change (red_can_force_win 38 opening_col6_reply_col6_red_col6_reply_col6_state).
  apply (proj2 (red_can_force_win_unfold_ongoing_red 37
                  opening_col6_reply_col6_red_col6_reply_col6_state
                  opening_col6_reply_col6_red_col6_reply_col6_result_ongoing
                  opening_col6_reply_col6_red_col6_reply_col6_turn_red)).
  exists opening_col6_reply_col6_red_col6_reply_col6_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col6_red_col6_reply_col6_red_col6.
  - apply opening_col6_reply_col6_red_col6_reply_col6_red_col6_subgoals_imply_child.
    exact Hsubs.
Qed.

Lemma opening_col6_reply_col6_raw_if_all_reply_subgoal_blocks :
  opening_col6_reply_col6_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 opening_col6_reply_col6_state.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  apply (proj2 (red_can_force_win_unfold_ongoing_red 39
                  opening_col6_reply_col6_state
                  opening_col6_reply_col6_result_ongoing
                  opening_col6_reply_col6_turn_red)).
  exists opening_col6_reply_col6_red_col6_state.
  split.
  - apply in_c4_next_opening_col6_reply_col6_red_col6.
  - apply (proj2 (red_can_force_win_unfold_ongoing_yellow 38
                    opening_col6_reply_col6_red_col6_state
                    opening_col6_reply_col6_red_col6_result_ongoing
                    opening_col6_reply_col6_red_col6_turn_yellow)).
    intros g Hin.
    unfold c4_next in Hin.
    rewrite opening_col6_reply_col6_red_col6_result_ongoing in Hin.
    apply in_map_iff in Hin.
    destruct Hin as [m [Hg Hinm]].
    unfold moves in Hinm.
    rewrite opening_col6_reply_col6_red_col6_result_ongoing in Hinm.
    apply filter_In in Hinm as [Hinall _].
    rewrite <- Hg.
    destruct m.
    + apply opening_col6_reply_col6_red_col6_reply_col0_raw_if_subgoals; exact H0.
    + apply opening_col6_reply_col6_red_col6_reply_col1_raw_if_subgoals; exact H1.
    + apply opening_col6_reply_col6_red_col6_reply_col2_raw_if_subgoals; exact H2.
    + apply opening_col6_reply_col6_red_col6_reply_col3_raw_if_subgoals; exact H3.
    + apply opening_col6_reply_col6_red_col6_reply_col4_raw_if_subgoals; exact H4.
    + apply opening_col6_reply_col6_red_col6_reply_col5_raw_if_subgoals; exact H5.
    + apply opening_col6_reply_col6_red_col6_reply_col6_raw_if_subgoals; exact H6.
Qed.

Lemma opening_col6_reply_col6_goal_if_all_reply_subgoal_blocks :
  opening_col6_reply_col6_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col6_goal.
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  apply opening_col6_reply_col6_raw_if_all_reply_subgoal_blocks; assumption.
Qed.

Lemma opening_col6_reply_col6_firstconj_if_all_reply_subgoal_blocks :
  opening_col6_reply_col6_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col6).
Proof.
  intros H0 H1 H2 H3 H4 H5 H6.
  change (red_can_force_win 40 opening_col6_reply_col6_state).
  apply opening_col6_reply_col6_raw_if_all_reply_subgoal_blocks; assumption.
Qed.

Lemma opening_col6_reply_subgoals_if_col01_all_reply_subgoal_blocks_and_rest_raw :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col2) ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_reply_subgoals.
Proof.
  intros H00 H01 H02 H03 H04 H05 H06
         H10 H11 H12 H13 H14 H15 H16
         Hr2 Hr3 Hr4 Hr5 Hr6.
  apply opening_col6_reply_subgoals_if_col0_and_rest_raw.
  - apply opening_col6_reply_col0_firstconj_if_all_reply_subgoal_blocks;
      assumption.
  - apply opening_col6_reply_col1_firstconj_if_all_reply_subgoal_blocks;
      assumption.
  - exact Hr2.
  - exact Hr3.
  - exact Hr4.
  - exact Hr5.
  - exact Hr6.
Qed.

Lemma opening_col6_target_if_col01_all_reply_subgoal_blocks_and_rest_raw :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col2) ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_target.
Proof.
  intros H00 H01 H02 H03 H04 H05 H06
         H10 H11 H12 H13 H14 H15 H16
         Hr2 Hr3 Hr4 Hr5 Hr6.
  apply opening_col6_target_if_reply_subgoals.
  apply opening_col6_reply_subgoals_if_col01_all_reply_subgoal_blocks_and_rest_raw;
    assumption.
Qed.

Lemma opening_col6_reply_subgoals_if_col0col0to5_col6_and_col0col6_block_and_col1col0to5_col6_and_col1col6_block_and_rest_raw :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col2) ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_reply_subgoals.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H06
         H10c6 H11c6 H12c6 H13c6 H14c6 H15c6 H16
         Hr2 Hr3 Hr4 Hr5 Hr6.
  apply opening_col6_reply_subgoals_if_col0_and_rest_raw.
  - apply opening_col6_reply_col0_firstconj_if_col0col0to5_col6_and_col0col6_block;
      assumption.
  - apply opening_col6_reply_col1_firstconj_if_col1col0to5_col6_and_col1col6_block;
      assumption.
  - exact Hr2.
  - exact Hr3.
  - exact Hr4.
  - exact Hr5.
  - exact Hr6.
Qed.

Lemma opening_col6_target_if_col0col0to5_col6_and_col0col6_block_and_col1col0to5_col6_and_col1col6_block_and_rest_raw :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col2) ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_target.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H06
         H10c6 H11c6 H12c6 H13c6 H14c6 H15c6 H16
         Hr2 Hr3 Hr4 Hr5 Hr6.
  apply opening_col6_target_if_reply_subgoals.
  apply opening_col6_reply_subgoals_if_col0col0to5_col6_and_col0col6_block_and_col1col0to5_col6_and_col1col6_block_and_rest_raw;
    assumption.
Qed.

Lemma opening_col6_reply_subgoals_if_col0col0to5_col6_and_col0col6_block_and_col1col0to5_col6_and_col1col6_block_and_col2col0to5_col6_and_col2col6_block_and_rest_raw :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_reply_subgoals.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H06
         H10c6 H11c6 H12c6 H13c6 H14c6 H15c6 H16
         H20c6 H21c6 H22c6 H23c6 H24c6 H25c6 H26
         Hr3 Hr4 Hr5 Hr6.
  apply opening_col6_reply_subgoals_if_col0_and_rest_raw.
  - apply opening_col6_reply_col0_firstconj_if_col0col0to5_col6_and_col0col6_block;
      assumption.
  - apply opening_col6_reply_col1_firstconj_if_col1col0to5_col6_and_col1col6_block;
      assumption.
  - apply opening_col6_reply_col2_firstconj_if_col2col0to5_col6_and_col2col6_block;
      assumption.
  - exact Hr3.
  - exact Hr4.
  - exact Hr5.
  - exact Hr6.
Qed.

Lemma opening_col6_target_if_col0col0to5_col6_and_col0col6_block_and_col1col0to5_col6_and_col1col6_block_and_col2col0to5_col6_and_col2col6_block_and_rest_raw :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_target.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H06
         H10c6 H11c6 H12c6 H13c6 H14c6 H15c6 H16
         H20c6 H21c6 H22c6 H23c6 H24c6 H25c6 H26
         Hr3 Hr4 Hr5 Hr6.
  apply opening_col6_target_if_reply_subgoals.
  apply opening_col6_reply_subgoals_if_col0col0to5_col6_and_col0col6_block_and_col1col0to5_col6_and_col1col6_block_and_col2col0to5_col6_and_col2col6_block_and_rest_raw;
    assumption.
Qed.

Lemma opening_col6_reply_subgoals_if_col012_all_reply_subgoal_blocks_and_rest_raw :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_reply_subgoals.
Proof.
  intros H00 H01 H02 H03 H04 H05 H06
         H10 H11 H12 H13 H14 H15 H16
         H20 H21 H22 H23 H24 H25 H26
         Hr3 Hr4 Hr5 Hr6.
  apply opening_col6_reply_subgoals_if_col01_all_reply_subgoal_blocks_and_rest_raw.
  - exact H00.
  - exact H01.
  - exact H02.
  - exact H03.
  - exact H04.
  - exact H05.
  - exact H06.
  - exact H10.
  - exact H11.
  - exact H12.
  - exact H13.
  - exact H14.
  - exact H15.
  - exact H16.
  - apply opening_col6_reply_col2_firstconj_if_all_reply_subgoal_blocks;
      assumption.
  - exact Hr3.
  - exact Hr4.
  - exact Hr5.
  - exact Hr6.
Qed.

Lemma opening_col6_target_if_col012_all_reply_subgoal_blocks_and_rest_raw :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col3) ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_target.
Proof.
  intros H00 H01 H02 H03 H04 H05 H06
         H10 H11 H12 H13 H14 H15 H16
         H20 H21 H22 H23 H24 H25 H26
         Hr3 Hr4 Hr5 Hr6.
  apply opening_col6_target_if_reply_subgoals.
  apply opening_col6_reply_subgoals_if_col012_all_reply_subgoal_blocks_and_rest_raw;
    assumption.
Qed.

Lemma opening_col6_reply_subgoals_if_col0col0to5_col6_and_col0col6_block_and_col1col0to5_col6_and_col1col6_block_and_col2col0to5_col6_and_col2col6_block_and_col3col0to5_col6_and_col3col6_block_and_rest_raw :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_reply_subgoals.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H06
         H10c6 H11c6 H12c6 H13c6 H14c6 H15c6 H16
         H20c6 H21c6 H22c6 H23c6 H24c6 H25c6 H26
         H30c6 H31c6 H32c6 H33c6 H34c6 H35c6 H36
         Hr4 Hr5 Hr6.
  apply opening_col6_reply_subgoals_if_col0_and_rest_raw.
  - apply opening_col6_reply_col0_firstconj_if_col0col0to5_col6_and_col0col6_block;
      assumption.
  - apply opening_col6_reply_col1_firstconj_if_col1col0to5_col6_and_col1col6_block;
      assumption.
  - apply opening_col6_reply_col2_firstconj_if_col2col0to5_col6_and_col2col6_block;
      assumption.
  - apply opening_col6_reply_col3_firstconj_if_col3col0to5_col6_and_col3col6_block;
      assumption.
  - exact Hr4.
  - exact Hr5.
  - exact Hr6.
Qed.

Lemma opening_col6_target_if_col0col0to5_col6_and_col0col6_block_and_col1col0to5_col6_and_col1col6_block_and_col2col0to5_col6_and_col2col6_block_and_col3col0to5_col6_and_col3col6_block_and_rest_raw :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_target.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H06
         H10c6 H11c6 H12c6 H13c6 H14c6 H15c6 H16
         H20c6 H21c6 H22c6 H23c6 H24c6 H25c6 H26
         H30c6 H31c6 H32c6 H33c6 H34c6 H35c6 H36
         Hr4 Hr5 Hr6.
  apply opening_col6_target_if_reply_subgoals.
  apply opening_col6_reply_subgoals_if_col0col0to5_col6_and_col0col6_block_and_col1col0to5_col6_and_col1col6_block_and_col2col0to5_col6_and_col2col6_block_and_col3col0to5_col6_and_col3col6_block_and_rest_raw;
    assumption.
Qed.

Lemma opening_col6_reply_subgoals_if_col0123_all_reply_subgoal_blocks_and_rest_raw :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_reply_subgoals.
Proof.
  intros H00 H01 H02 H03 H04 H05 H06
         H10 H11 H12 H13 H14 H15 H16
         H20 H21 H22 H23 H24 H25 H26
         H30 H31 H32 H33 H34 H35 H36
         Hr4 Hr5 Hr6.
  apply opening_col6_reply_subgoals_if_col012_all_reply_subgoal_blocks_and_rest_raw.
  - exact H00.
  - exact H01.
  - exact H02.
  - exact H03.
  - exact H04.
  - exact H05.
  - exact H06.
  - exact H10.
  - exact H11.
  - exact H12.
  - exact H13.
  - exact H14.
  - exact H15.
  - exact H16.
  - exact H20.
  - exact H21.
  - exact H22.
  - exact H23.
  - exact H24.
  - exact H25.
  - exact H26.
  - apply opening_col6_reply_col3_firstconj_if_all_reply_subgoal_blocks;
      assumption.
  - exact Hr4.
  - exact Hr5.
  - exact Hr6.
Qed.

Lemma opening_col6_target_if_col0123_all_reply_subgoal_blocks_and_rest_raw :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col4) ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_target.
Proof.
  intros H00 H01 H02 H03 H04 H05 H06
         H10 H11 H12 H13 H14 H15 H16
         H20 H21 H22 H23 H24 H25 H26
         H30 H31 H32 H33 H34 H35 H36
         Hr4 Hr5 Hr6.
  apply opening_col6_target_if_reply_subgoals.
  apply opening_col6_reply_subgoals_if_col0123_all_reply_subgoal_blocks_and_rest_raw;
    assumption.
Qed.

Lemma opening_col6_reply_subgoals_if_col0col0to5_col6_and_col0col6_block_and_col1col0to5_col6_and_col1col6_block_and_col2col0to5_col6_and_col2col6_block_and_col3col0to5_col6_and_col3col6_block_and_col4col0to5_col6_and_col4col6_block_and_rest_raw :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_reply_subgoals.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H06
         H10c6 H11c6 H12c6 H13c6 H14c6 H15c6 H16
         H20c6 H21c6 H22c6 H23c6 H24c6 H25c6 H26
         H30c6 H31c6 H32c6 H33c6 H34c6 H35c6 H36
         H40c6 H41c6 H42c6 H43c6 H44c6 H45c6 H46
         Hr5 Hr6.
  apply opening_col6_reply_subgoals_if_col0_and_rest_raw.
  - apply opening_col6_reply_col0_firstconj_if_col0col0to5_col6_and_col0col6_block;
      assumption.
  - apply opening_col6_reply_col1_firstconj_if_col1col0to5_col6_and_col1col6_block;
      assumption.
  - apply opening_col6_reply_col2_firstconj_if_col2col0to5_col6_and_col2col6_block;
      assumption.
  - apply opening_col6_reply_col3_firstconj_if_col3col0to5_col6_and_col3col6_block;
      assumption.
  - apply opening_col6_reply_col4_firstconj_if_col4col0to5_col6_and_col4col6_block;
      assumption.
  - exact Hr5.
  - exact Hr6.
Qed.

Lemma opening_col6_target_if_col0col0to5_col6_and_col0col6_block_and_col1col0to5_col6_and_col1col6_block_and_col2col0to5_col6_and_col2col6_block_and_col3col0to5_col6_and_col3col6_block_and_col4col0to5_col6_and_col4col6_block_and_rest_raw :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_target.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H06
         H10c6 H11c6 H12c6 H13c6 H14c6 H15c6 H16
         H20c6 H21c6 H22c6 H23c6 H24c6 H25c6 H26
         H30c6 H31c6 H32c6 H33c6 H34c6 H35c6 H36
         H40c6 H41c6 H42c6 H43c6 H44c6 H45c6 H46
         Hr5 Hr6.
  apply opening_col6_target_if_reply_subgoals.
  apply opening_col6_reply_subgoals_if_col0col0to5_col6_and_col0col6_block_and_col1col0to5_col6_and_col1col6_block_and_col2col0to5_col6_and_col2col6_block_and_col3col0to5_col6_and_col3col6_block_and_col4col0to5_col6_and_col4col6_block_and_rest_raw;
    assumption.
Qed.

Lemma opening_col6_reply_subgoals_if_col01234_all_reply_subgoal_blocks_and_rest_raw :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_reply_subgoals.
Proof.
  intros H00 H01 H02 H03 H04 H05 H06
         H10 H11 H12 H13 H14 H15 H16
         H20 H21 H22 H23 H24 H25 H26
         H30 H31 H32 H33 H34 H35 H36
         H40 H41 H42 H43 H44 H45 H46
         Hr5 Hr6.
  apply opening_col6_reply_subgoals_if_col0123_all_reply_subgoal_blocks_and_rest_raw.
  - exact H00.
  - exact H01.
  - exact H02.
  - exact H03.
  - exact H04.
  - exact H05.
  - exact H06.
  - exact H10.
  - exact H11.
  - exact H12.
  - exact H13.
  - exact H14.
  - exact H15.
  - exact H16.
  - exact H20.
  - exact H21.
  - exact H22.
  - exact H23.
  - exact H24.
  - exact H25.
  - exact H26.
  - exact H30.
  - exact H31.
  - exact H32.
  - exact H33.
  - exact H34.
  - exact H35.
  - exact H36.
  - apply opening_col6_reply_col4_firstconj_if_all_reply_subgoal_blocks;
      assumption.
  - exact Hr5.
  - exact Hr6.
Qed.

Lemma opening_col6_target_if_col01234_all_reply_subgoal_blocks_and_rest_raw :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col5) ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_target.
Proof.
  intros H00 H01 H02 H03 H04 H05 H06
         H10 H11 H12 H13 H14 H15 H16
         H20 H21 H22 H23 H24 H25 H26
         H30 H31 H32 H33 H34 H35 H36
         H40 H41 H42 H43 H44 H45 H46
         Hr5 Hr6.
  apply opening_col6_target_if_reply_subgoals.
  apply opening_col6_reply_subgoals_if_col01234_all_reply_subgoal_blocks_and_rest_raw;
    assumption.
Qed.

Lemma opening_col6_reply_subgoals_if_col0col0to5_col6_and_col0col6_block_and_col1col0to5_col6_and_col1col6_block_and_col2col0to5_col6_and_col2col6_block_and_col3col0to5_col6_and_col3col6_block_and_col4col0to5_col6_and_col4col6_block_and_col5col0to5_col6_and_col5col6_block_and_rest_raw :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_reply_subgoals.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H06
         H10c6 H11c6 H12c6 H13c6 H14c6 H15c6 H16
         H20c6 H21c6 H22c6 H23c6 H24c6 H25c6 H26
         H30c6 H31c6 H32c6 H33c6 H34c6 H35c6 H36
         H40c6 H41c6 H42c6 H43c6 H44c6 H45c6 H46
         H50c6 H51c6 H52c6 H53c6 H54c6 H55c6 H56
         Hr6.
  apply opening_col6_reply_subgoals_if_col0_and_rest_raw.
  - apply opening_col6_reply_col0_firstconj_if_col0col0to5_col6_and_col0col6_block;
      assumption.
  - apply opening_col6_reply_col1_firstconj_if_col1col0to5_col6_and_col1col6_block;
      assumption.
  - apply opening_col6_reply_col2_firstconj_if_col2col0to5_col6_and_col2col6_block;
      assumption.
  - apply opening_col6_reply_col3_firstconj_if_col3col0to5_col6_and_col3col6_block;
      assumption.
  - apply opening_col6_reply_col4_firstconj_if_col4col0to5_col6_and_col4col6_block;
      assumption.
  - apply opening_col6_reply_col5_firstconj_if_col5col0to5_col6_and_col5col6_block;
      assumption.
  - exact Hr6.
Qed.

Lemma opening_col6_target_if_col0col0to5_col6_and_col0col6_block_and_col1col0to5_col6_and_col1col6_block_and_col2col0to5_col6_and_col2col6_block_and_col3col0to5_col6_and_col3col6_block_and_col4col0to5_col6_and_col4col6_block_and_col5col0to5_col6_and_col5col6_block_and_rest_raw :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_target.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H06
         H10c6 H11c6 H12c6 H13c6 H14c6 H15c6 H16
         H20c6 H21c6 H22c6 H23c6 H24c6 H25c6 H26
         H30c6 H31c6 H32c6 H33c6 H34c6 H35c6 H36
         H40c6 H41c6 H42c6 H43c6 H44c6 H45c6 H46
         H50c6 H51c6 H52c6 H53c6 H54c6 H55c6 H56
         Hr6.
  apply opening_col6_target_if_reply_subgoals.
  apply opening_col6_reply_subgoals_if_col0col0to5_col6_and_col0col6_block_and_col1col0to5_col6_and_col1col6_block_and_col2col0to5_col6_and_col2col6_block_and_col3col0to5_col6_and_col3col6_block_and_col4col0to5_col6_and_col4col6_block_and_col5col0to5_col6_and_col5col6_block_and_rest_raw;
    assumption.
Qed.

Lemma opening_col6_reply_subgoals_if_col012345_all_reply_subgoal_blocks_and_rest_raw :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_reply_subgoals.
Proof.
  intros H00 H01 H02 H03 H04 H05 H06
         H10 H11 H12 H13 H14 H15 H16
         H20 H21 H22 H23 H24 H25 H26
         H30 H31 H32 H33 H34 H35 H36
         H40 H41 H42 H43 H44 H45 H46
         H50 H51 H52 H53 H54 H55 H56
         Hr6.
  apply opening_col6_reply_subgoals_if_col01234_all_reply_subgoal_blocks_and_rest_raw.
  - exact H00.
  - exact H01.
  - exact H02.
  - exact H03.
  - exact H04.
  - exact H05.
  - exact H06.
  - exact H10.
  - exact H11.
  - exact H12.
  - exact H13.
  - exact H14.
  - exact H15.
  - exact H16.
  - exact H20.
  - exact H21.
  - exact H22.
  - exact H23.
  - exact H24.
  - exact H25.
  - exact H26.
  - exact H30.
  - exact H31.
  - exact H32.
  - exact H33.
  - exact H34.
  - exact H35.
  - exact H36.
  - exact H40.
  - exact H41.
  - exact H42.
  - exact H43.
  - exact H44.
  - exact H45.
  - exact H46.
  - apply opening_col6_reply_col5_firstconj_if_all_reply_subgoal_blocks;
      assumption.
  - exact Hr6.
Qed.

Lemma opening_col6_target_if_col012345_all_reply_subgoal_blocks_and_rest_raw :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 40 (apply_move opening_col6_state col6) ->
  opening_col6_target.
Proof.
  intros H00 H01 H02 H03 H04 H05 H06
         H10 H11 H12 H13 H14 H15 H16
         H20 H21 H22 H23 H24 H25 H26
         H30 H31 H32 H33 H34 H35 H36
         H40 H41 H42 H43 H44 H45 H46
         H50 H51 H52 H53 H54 H55 H56
         Hr6.
  apply opening_col6_target_if_reply_subgoals.
  apply opening_col6_reply_subgoals_if_col012345_all_reply_subgoal_blocks_and_rest_raw;
    assumption.
Qed.

Lemma opening_col6_reply_subgoals_if_all_reply_subgoal_blocks :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_subgoals.
Proof.
  intros H00 H01 H02 H03 H04 H05 H06
         H10 H11 H12 H13 H14 H15 H16
         H20 H21 H22 H23 H24 H25 H26
         H30 H31 H32 H33 H34 H35 H36
         H40 H41 H42 H43 H44 H45 H46
         H50 H51 H52 H53 H54 H55 H56
         H60 H61 H62 H63 H64 H65 H66.
  apply opening_col6_reply_subgoals_if_col012345_all_reply_subgoal_blocks_and_rest_raw.
  - exact H00.
  - exact H01.
  - exact H02.
  - exact H03.
  - exact H04.
  - exact H05.
  - exact H06.
  - exact H10.
  - exact H11.
  - exact H12.
  - exact H13.
  - exact H14.
  - exact H15.
  - exact H16.
  - exact H20.
  - exact H21.
  - exact H22.
  - exact H23.
  - exact H24.
  - exact H25.
  - exact H26.
  - exact H30.
  - exact H31.
  - exact H32.
  - exact H33.
  - exact H34.
  - exact H35.
  - exact H36.
  - exact H40.
  - exact H41.
  - exact H42.
  - exact H43.
  - exact H44.
  - exact H45.
  - exact H46.
  - exact H50.
  - exact H51.
  - exact H52.
  - exact H53.
  - exact H54.
  - exact H55.
  - exact H56.
  - apply opening_col6_reply_col6_firstconj_if_all_reply_subgoal_blocks;
      assumption.
Qed.

Lemma opening_col6_target_if_all_reply_subgoal_blocks :
  opening_col6_reply_col0_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_target.
Proof.
  intros H00 H01 H02 H03 H04 H05 H06
         H10 H11 H12 H13 H14 H15 H16
         H20 H21 H22 H23 H24 H25 H26
         H30 H31 H32 H33 H34 H35 H36
         H40 H41 H42 H43 H44 H45 H46
         H50 H51 H52 H53 H54 H55 H56
         H60 H61 H62 H63 H64 H65 H66.
  apply opening_col6_target_if_reply_subgoals.
  apply opening_col6_reply_subgoals_if_all_reply_subgoal_blocks;
    assumption.
Qed.

Lemma opening_col6_reply_subgoals_if_col0to5_reduced_and_col6_all_reply_subgoal_blocks :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_subgoals.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H06
         H10c6 H11c6 H12c6 H13c6 H14c6 H15c6 H16
         H20c6 H21c6 H22c6 H23c6 H24c6 H25c6 H26
         H30c6 H31c6 H32c6 H33c6 H34c6 H35c6 H36
         H40c6 H41c6 H42c6 H43c6 H44c6 H45c6 H46
         H50c6 H51c6 H52c6 H53c6 H54c6 H55c6 H56
         H60 H61 H62 H63 H64 H65 H66.
  apply opening_col6_reply_subgoals_if_col0_and_rest_raw.
  - apply opening_col6_reply_col0_firstconj_if_col0col0to5_col6_and_col0col6_block;
      assumption.
  - apply opening_col6_reply_col1_firstconj_if_col1col0to5_col6_and_col1col6_block;
      assumption.
  - apply opening_col6_reply_col2_firstconj_if_col2col0to5_col6_and_col2col6_block;
      assumption.
  - apply opening_col6_reply_col3_firstconj_if_col3col0to5_col6_and_col3col6_block;
      assumption.
  - apply opening_col6_reply_col4_firstconj_if_col4col0to5_col6_and_col4col6_block;
      assumption.
  - apply opening_col6_reply_col5_firstconj_if_col5col0to5_col6_and_col5col6_block;
      assumption.
  - apply opening_col6_reply_col6_firstconj_if_all_reply_subgoal_blocks;
      assumption.
Qed.

Lemma opening_col6_target_if_col0to5_reduced_and_col6_all_reply_subgoal_blocks :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_target.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H06
         H10c6 H11c6 H12c6 H13c6 H14c6 H15c6 H16
         H20c6 H21c6 H22c6 H23c6 H24c6 H25c6 H26
         H30c6 H31c6 H32c6 H33c6 H34c6 H35c6 H36
         H40c6 H41c6 H42c6 H43c6 H44c6 H45c6 H46
         H50c6 H51c6 H52c6 H53c6 H54c6 H55c6 H56
         H60 H61 H62 H63 H64 H65 H66.
  apply opening_col6_target_if_reply_subgoals.
  apply opening_col6_reply_subgoals_if_col0to5_reduced_and_col6_all_reply_subgoal_blocks;
    assumption.
Qed.

Lemma opening_col6_hard_c6_sym_10_01 :
  apply_move opening_col6_reply_col1_red_col6_reply_col0_red_col6_state col6 =
  apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_hard_c6_sym_20_02 :
  apply_move opening_col6_reply_col2_red_col6_reply_col0_red_col6_state col6 =
  apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_hard_c6_sym_30_03 :
  apply_move opening_col6_reply_col3_red_col6_reply_col0_red_col6_state col6 =
  apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_hard_c6_sym_40_04 :
  apply_move opening_col6_reply_col4_red_col6_reply_col0_red_col6_state col6 =
  apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_hard_c6_sym_50_05 :
  apply_move opening_col6_reply_col5_red_col6_reply_col0_red_col6_state col6 =
  apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_hard_c6_sym_21_12 :
  apply_move opening_col6_reply_col2_red_col6_reply_col1_red_col6_state col6 =
  apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_hard_c6_sym_31_13 :
  apply_move opening_col6_reply_col3_red_col6_reply_col1_red_col6_state col6 =
  apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_hard_c6_sym_41_14 :
  apply_move opening_col6_reply_col4_red_col6_reply_col1_red_col6_state col6 =
  apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_hard_c6_sym_51_15 :
  apply_move opening_col6_reply_col5_red_col6_reply_col1_red_col6_state col6 =
  apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_hard_c6_sym_32_23 :
  apply_move opening_col6_reply_col3_red_col6_reply_col2_red_col6_state col6 =
  apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_hard_c6_sym_42_24 :
  apply_move opening_col6_reply_col4_red_col6_reply_col2_red_col6_state col6 =
  apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_hard_c6_sym_52_25 :
  apply_move opening_col6_reply_col5_red_col6_reply_col2_red_col6_state col6 =
  apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_hard_c6_sym_43_34 :
  apply_move opening_col6_reply_col4_red_col6_reply_col3_red_col6_state col6 =
  apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col6.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_hard_c6_sym_53_35 :
  apply_move opening_col6_reply_col5_red_col6_reply_col3_red_col6_state col6 =
  apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col6.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_hard_c6_sym_54_45 :
  apply_move opening_col6_reply_col5_red_col6_reply_col4_red_col6_state col6 =
  apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col6.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_target_if_col0to5_sym_reduced_and_col6_all_reply_subgoal_blocks :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col0_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col1_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col2_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col3_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col4_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col5_red_col6_reply_subgoals ->
  opening_col6_reply_col6_red_col6_reply_col6_red_col6_reply_subgoals ->
  opening_col6_target.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H06
         H11c6 H12c6 H13c6 H14c6 H15c6 H16
         H22c6 H23c6 H24c6 H25c6 H26
         H33c6 H34c6 H35c6 H36
         H44c6 H45c6 H46
         H55c6 H56
         H60 H61 H62 H63 H64 H65 H66.
  apply opening_col6_target_if_col0to5_reduced_and_col6_all_reply_subgoal_blocks.
  - exact H00c6.
  - exact H01c6.
  - exact H02c6.
  - exact H03c6.
  - exact H04c6.
  - exact H05c6.
  - exact H06.
  - rewrite opening_col6_hard_c6_sym_10_01. exact H01c6.
  - exact H11c6.
  - exact H12c6.
  - exact H13c6.
  - exact H14c6.
  - exact H15c6.
  - exact H16.
  - rewrite opening_col6_hard_c6_sym_20_02. exact H02c6.
  - rewrite opening_col6_hard_c6_sym_21_12. exact H12c6.
  - exact H22c6.
  - exact H23c6.
  - exact H24c6.
  - exact H25c6.
  - exact H26.
  - rewrite opening_col6_hard_c6_sym_30_03. exact H03c6.
  - rewrite opening_col6_hard_c6_sym_31_13. exact H13c6.
  - rewrite opening_col6_hard_c6_sym_32_23. exact H23c6.
  - exact H33c6.
  - exact H34c6.
  - exact H35c6.
  - exact H36.
  - rewrite opening_col6_hard_c6_sym_40_04. exact H04c6.
  - rewrite opening_col6_hard_c6_sym_41_14. exact H14c6.
  - rewrite opening_col6_hard_c6_sym_42_24. exact H24c6.
  - rewrite opening_col6_hard_c6_sym_43_34. exact H34c6.
  - exact H44c6.
  - exact H45c6.
  - exact H46.
  - rewrite opening_col6_hard_c6_sym_50_05. exact H05c6.
  - rewrite opening_col6_hard_c6_sym_51_15. exact H15c6.
  - rewrite opening_col6_hard_c6_sym_52_25. exact H25c6.
  - rewrite opening_col6_hard_c6_sym_53_35. exact H35c6.
  - rewrite opening_col6_hard_c6_sym_54_45. exact H45c6.
  - exact H55c6.
  - exact H56.
  - exact H60.
  - exact H61.
  - exact H62.
  - exact H63.
  - exact H64.
  - exact H65.
  - exact H66.
Qed.

Lemma opening_col6_branch_c6_sym_10_01 :
  apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col0 =
  apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col1.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_branch_c6_sym_20_02 :
  apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col0 =
  apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col2.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_branch_c6_sym_30_03 :
  apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col0 =
  apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col3.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_branch_c6_sym_40_04 :
  apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col0 =
  apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col4.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_branch_c6_sym_50_05 :
  apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state col0 =
  apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col5.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_branch_c6_sym_21_12 :
  apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col1 =
  apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col2.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_branch_c6_sym_31_13 :
  apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col1 =
  apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col3.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_branch_c6_sym_41_14 :
  apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col1 =
  apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col4.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_branch_c6_sym_51_15 :
  apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state col1 =
  apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col5.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_branch_c6_sym_32_23 :
  apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col2 =
  apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col3.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_branch_c6_sym_42_24 :
  apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col2 =
  apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col4.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_branch_c6_sym_52_25 :
  apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state col2 =
  apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col5.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_branch_c6_sym_43_34 :
  apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col3 =
  apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col4.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_branch_c6_sym_53_35 :
  apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state col3 =
  apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col5.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_branch_c6_sym_54_45 :
  apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state col4 =
  apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col5.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_target_if_col0to5_sym_reduced_and_col0to5_col6_blocks_and_col6_branch_triangular_terms :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col6) ->
  opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col0) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col1) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col2) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col3) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col1) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col2) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col3) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col2) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col3) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col3) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col0) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col1) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col2) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col3) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col6) ->
  opening_col6_target.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6 H06
         H11c6 H12c6 H13c6 H14c6 H15c6 H16
         H22c6 H23c6 H24c6 H25c6 H26
         H33c6 H34c6 H35c6 H36
         H44c6 H45c6 H46
         H55c6 H56
         B00 B01 B02 B03 B04 B05 B06
         B11 B12 B13 B14 B15 B16
         B22 B23 B24 B25 B26
         B33 B34 B35 B36
         B44 B45 B46
         B55 B56
         B60 B61 B62 B63 B64 B65 B66.
  assert (H60 : opening_col6_reply_col6_red_col6_reply_col0_red_col6_reply_subgoals).
  { unfold opening_col6_reply_col6_red_col6_reply_col0_red_col6_reply_subgoals.
    repeat split; assumption. }
  assert (H61 : opening_col6_reply_col6_red_col6_reply_col1_red_col6_reply_subgoals).
  { unfold opening_col6_reply_col6_red_col6_reply_col1_red_col6_reply_subgoals.
    repeat split.
    - rewrite opening_col6_branch_c6_sym_10_01. exact B01.
    - exact B11.
    - exact B12.
    - exact B13.
    - exact B14.
    - exact B15.
    - exact B16. }
  assert (H62 : opening_col6_reply_col6_red_col6_reply_col2_red_col6_reply_subgoals).
  { unfold opening_col6_reply_col6_red_col6_reply_col2_red_col6_reply_subgoals.
    repeat split.
    - rewrite opening_col6_branch_c6_sym_20_02. exact B02.
    - rewrite opening_col6_branch_c6_sym_21_12. exact B12.
    - exact B22.
    - exact B23.
    - exact B24.
    - exact B25.
    - exact B26. }
  assert (H63 : opening_col6_reply_col6_red_col6_reply_col3_red_col6_reply_subgoals).
  { unfold opening_col6_reply_col6_red_col6_reply_col3_red_col6_reply_subgoals.
    repeat split.
    - rewrite opening_col6_branch_c6_sym_30_03. exact B03.
    - rewrite opening_col6_branch_c6_sym_31_13. exact B13.
    - rewrite opening_col6_branch_c6_sym_32_23. exact B23.
    - exact B33.
    - exact B34.
    - exact B35.
    - exact B36. }
  assert (H64 : opening_col6_reply_col6_red_col6_reply_col4_red_col6_reply_subgoals).
  { unfold opening_col6_reply_col6_red_col6_reply_col4_red_col6_reply_subgoals.
    repeat split.
    - rewrite opening_col6_branch_c6_sym_40_04. exact B04.
    - rewrite opening_col6_branch_c6_sym_41_14. exact B14.
    - rewrite opening_col6_branch_c6_sym_42_24. exact B24.
    - rewrite opening_col6_branch_c6_sym_43_34. exact B34.
    - exact B44.
    - exact B45.
    - exact B46. }
  assert (H65 : opening_col6_reply_col6_red_col6_reply_col5_red_col6_reply_subgoals).
  { unfold opening_col6_reply_col6_red_col6_reply_col5_red_col6_reply_subgoals.
    repeat split.
    - rewrite opening_col6_branch_c6_sym_50_05. exact B05.
    - rewrite opening_col6_branch_c6_sym_51_15. exact B15.
    - rewrite opening_col6_branch_c6_sym_52_25. exact B25.
    - rewrite opening_col6_branch_c6_sym_53_35. exact B35.
    - rewrite opening_col6_branch_c6_sym_54_45. exact B45.
    - exact B55.
    - exact B56. }
  assert (H66 : opening_col6_reply_col6_red_col6_reply_col6_red_col6_reply_subgoals).
  { unfold opening_col6_reply_col6_red_col6_reply_col6_red_col6_reply_subgoals.
    repeat split; assumption. }
  apply opening_col6_target_if_col0to5_sym_reduced_and_col6_all_reply_subgoal_blocks;
    assumption.
Qed.

Lemma opening_col6_mid_c6_sym_10_01 :
  apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col0 =
  apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col1.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_mid_c6_sym_20_02 :
  apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col0 =
  apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col2.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_mid_c6_sym_30_03 :
  apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state col0 =
  apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col3.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_mid_c6_sym_40_04 :
  apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state col0 =
  apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col4.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_mid_c6_sym_50_05 :
  apply_move opening_col6_reply_col5_red_col6_reply_col6_red_col6_state col0 =
  apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col5.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_mid_c6_sym_21_12 :
  apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col1 =
  apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col2.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_mid_c6_sym_31_13 :
  apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state col1 =
  apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col3.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_mid_c6_sym_41_14 :
  apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state col1 =
  apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col4.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_mid_c6_sym_51_15 :
  apply_move opening_col6_reply_col5_red_col6_reply_col6_red_col6_state col1 =
  apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col5.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_mid_c6_sym_32_23 :
  apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state col2 =
  apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col3.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_mid_c6_sym_42_24 :
  apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state col2 =
  apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col4.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_mid_c6_sym_52_25 :
  apply_move opening_col6_reply_col5_red_col6_reply_col6_red_col6_state col2 =
  apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col5.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_mid_c6_sym_43_34 :
  apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state col3 =
  apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state col4.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_mid_c6_sym_53_35 :
  apply_move opening_col6_reply_col5_red_col6_reply_col6_red_col6_state col3 =
  apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state col5.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_mid_c6_sym_54_45 :
  apply_move opening_col6_reply_col5_red_col6_reply_col6_red_col6_state col4 =
  apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state col5.
Proof. vm_compute. reflexivity. Qed.

Lemma opening_col6_target_if_all_frontier_terms_triangular :
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col5_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col5_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col5_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col5_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col5_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col5_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col0) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col1) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col2) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col3) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col0_red_col6_reply_col6_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col1) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col2) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col3) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col1_red_col6_reply_col6_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col2) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col3) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col2_red_col6_reply_col6_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state col3) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col3_red_col6_reply_col6_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col4_red_col6_reply_col6_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col6_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col5_red_col6_reply_col6_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col0) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col1) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col2) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col3) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col0_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col1) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col2) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col3) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col1_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col2) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col3) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col2_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col3) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col3_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col4_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col5_red_col6_state col6) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col0) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col1) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col2) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col3) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col4) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col5) ->
  red_can_force_win 36
    (apply_move opening_col6_reply_col6_red_col6_reply_col6_red_col6_state col6) ->
  opening_col6_target.
Proof.
  intros H00c6 H01c6 H02c6 H03c6 H04c6 H05c6
         H11c6 H12c6 H13c6 H14c6 H15c6
         H22c6 H23c6 H24c6 H25c6
         H33c6 H34c6 H35c6
         H44c6 H45c6
         H55c6
         C00 C01 C02 C03 C04 C05 C06
         C11 C12 C13 C14 C15 C16
         C22 C23 C24 C25 C26
         C33 C34 C35 C36
         C44 C45 C46
         C55 C56
         B00 B01 B02 B03 B04 B05 B06
         B11 B12 B13 B14 B15 B16
         B22 B23 B24 B25 B26
         B33 B34 B35 B36
         B44 B45 B46
         B55 B56
         B60 B61 B62 B63 B64 B65 B66.
  assert (H06 : opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals).
  { unfold opening_col6_reply_col0_red_col6_reply_col6_red_col6_reply_subgoals.
    repeat split; assumption. }
  assert (H16 : opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals).
  { unfold opening_col6_reply_col1_red_col6_reply_col6_red_col6_reply_subgoals.
    repeat split.
    - rewrite opening_col6_mid_c6_sym_10_01. exact C01.
    - exact C11.
    - exact C12.
    - exact C13.
    - exact C14.
    - exact C15.
    - exact C16. }
  assert (H26 : opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals).
  { unfold opening_col6_reply_col2_red_col6_reply_col6_red_col6_reply_subgoals.
    repeat split.
    - rewrite opening_col6_mid_c6_sym_20_02. exact C02.
    - rewrite opening_col6_mid_c6_sym_21_12. exact C12.
    - exact C22.
    - exact C23.
    - exact C24.
    - exact C25.
    - exact C26. }
  assert (H36 : opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals).
  { unfold opening_col6_reply_col3_red_col6_reply_col6_red_col6_reply_subgoals.
    repeat split.
    - rewrite opening_col6_mid_c6_sym_30_03. exact C03.
    - rewrite opening_col6_mid_c6_sym_31_13. exact C13.
    - rewrite opening_col6_mid_c6_sym_32_23. exact C23.
    - exact C33.
    - exact C34.
    - exact C35.
    - exact C36. }
  assert (H46 : opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals).
  { unfold opening_col6_reply_col4_red_col6_reply_col6_red_col6_reply_subgoals.
    repeat split.
    - rewrite opening_col6_mid_c6_sym_40_04. exact C04.
    - rewrite opening_col6_mid_c6_sym_41_14. exact C14.
    - rewrite opening_col6_mid_c6_sym_42_24. exact C24.
    - rewrite opening_col6_mid_c6_sym_43_34. exact C34.
    - exact C44.
    - exact C45.
    - exact C46. }
  assert (H56 : opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals).
  { unfold opening_col6_reply_col5_red_col6_reply_col6_red_col6_reply_subgoals.
    repeat split.
    - rewrite opening_col6_mid_c6_sym_50_05. exact C05.
    - rewrite opening_col6_mid_c6_sym_51_15. exact C15.
    - rewrite opening_col6_mid_c6_sym_52_25. exact C25.
    - rewrite opening_col6_mid_c6_sym_53_35. exact C35.
    - rewrite opening_col6_mid_c6_sym_54_45. exact C45.
    - exact C55.
    - exact C56. }
  apply opening_col6_target_if_col0to5_sym_reduced_and_col0to5_col6_blocks_and_col6_branch_triangular_terms;
    assumption.
Qed.

Theorem root_nonloss_value_ge_1_if_tempo_monotone :
  tempo_monotone_red_win ->
  value_fuel 42 c4_init >= 1.
Proof.
  intro Htempo.
  apply root_nonloss_value_ge_1_if_not_yellow_win.
  apply no_yellow_root_win_if_tempo_monotone.
  exact Htempo.
Qed.

Definition tempo_monotone_red_win_empty_42 : Prop :=
  red_can_force_win 42 c4_init_mirror ->
  red_can_force_win 42 c4_init.

Definition opening_child_mirror_redwin_transfer_41 : Prop :=
  forall g,
    In g (c4_next c4_init_mirror) ->
    red_can_force_win 41 g ->
    red_can_force_win 41 (mirror_game g).

Lemma opening_child_is_apply_move :
  forall g,
    In g (c4_next c4_init_mirror) ->
    exists m, In m all_moves /\ g = apply_move c4_init_mirror m.
Proof.
  intros g Hin.
  unfold c4_next in Hin.
  rewrite get_result_c4_init_mirror_ongoing in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [m [Hg Hinm]].
  unfold moves in Hinm.
  rewrite get_result_c4_init_mirror_ongoing in Hinm.
  apply filter_In in Hinm as [Hinall _].
  exists m.
  split.
  - exact Hinall.
  - symmetry.
    exact Hg.
Qed.

Lemma mirror_opening_apply_move :
  forall m,
    mirror_game (apply_move c4_init_mirror m) =
    apply_move c4_init (mirror_move m).
Proof.
  intro m.
  unfold c4_init_mirror.
  rewrite apply_move_mirror_game.
  rewrite mirror_game_involutive.
  reflexivity.
Qed.

Lemma opening_child_transfer_41_move_form :
  opening_child_mirror_redwin_transfer_41 <->
  forall m,
    In m all_moves ->
    red_can_force_win 41 (apply_move c4_init_mirror m) ->
    red_can_force_win 41 (apply_move c4_init (mirror_move m)).
Proof.
  split.
  - intros Hall m Hinall Hred.
    rewrite <- mirror_opening_apply_move.
    apply Hall.
    + unfold c4_next.
      rewrite get_result_c4_init_mirror_ongoing.
      apply in_map_iff.
      exists m.
      split; [reflexivity|].
      unfold moves.
      rewrite get_result_c4_init_mirror_ongoing.
      apply filter_In.
      split.
      * exact Hinall.
      * destruct m; simpl; reflexivity.
    + exact Hred.
  - intros Hmove g Hin Hred.
    destruct (opening_child_is_apply_move g Hin) as [m [Hinall Hg]].
    rewrite Hg in Hred.
    rewrite Hg.
    rewrite mirror_opening_apply_move.
    apply Hmove; assumption.
Qed.

Theorem no_yellow_root_win_if_tempo_empty_42 :
  tempo_monotone_red_win_empty_42 ->
  ~ yellow_can_force_win 42 c4_init.
Proof.
  intros Htempo Hy.
  pose proof (yellow_root_win_implies_red_mirror_win Hy) as Hredm.
  pose proof (Htempo Hredm) as Hred.
  apply (not_both_force_win 42 c4_init).
  split; assumption.
Qed.

Theorem root_nonloss_value_ge_1_if_tempo_empty_42 :
  tempo_monotone_red_win_empty_42 ->
  value_fuel 42 c4_init >= 1.
Proof.
  intro Htempo.
  apply root_nonloss_value_ge_1_if_not_yellow_win.
  apply no_yellow_root_win_if_tempo_empty_42.
  exact Htempo.
Qed.

Theorem no_yellow_root_win_if_opening_child_transfer :
  opening_child_mirror_redwin_transfer_41 ->
  ~ yellow_can_force_win 42 c4_init.
Proof.
  intros Htransfer Hy.
  pose proof (yellow_root_win_implies_red_mirror_win Hy) as Hredm.
  assert (Hturnm : next_turn c4_init_mirror = yellow).
  { rewrite c4_init_mirror_shape. reflexivity. }
  assert (Hchild : red_can_force_win 41 (apply_move c4_init_mirror col0)).
  { apply (red_can_force_win_yellow_children 41 c4_init_mirror
             get_result_c4_init_mirror_ongoing Hturnm Hredm).
    apply in_c4_next_c4_init_mirror_col0. }
  pose proof
    (Htransfer (apply_move c4_init_mirror col0)
      in_c4_next_c4_init_mirror_col0 Hchild) as Hred6.
  rewrite mirror_opening_apply_move in Hred6.
  change (red_can_force_win 41 (apply_move c4_init col6)) in Hred6.
  assert (Hin6 : In col6 all_moves).
  { simpl. tauto. }
  exact (no_yellow_root_win_if_red_has_winning_opening col6 Hin6 Hred6 Hy).
Qed.

Theorem root_nonloss_value_ge_1_if_opening_child_transfer :
  opening_child_mirror_redwin_transfer_41 ->
  value_fuel 42 c4_init >= 1.
Proof.
  intro Htransfer.
  apply root_nonloss_value_ge_1_if_not_yellow_win.
  apply no_yellow_root_win_if_opening_child_transfer.
  exact Htransfer.
Qed.

Theorem yellow_win_iff_not_red_nonloss :
  forall fuel g,
    yellow_can_force_win fuel g <-> ~ red_can_force_nonloss fuel g.
Proof.
  intros fuel g.
  split.
  - intros Hy Hred.
    eapply red_nonloss_not_yellow_win; eauto.
  - intros Hnot.
    destruct (red_nonloss_or_yellow_win fuel g) as [Hred | Hy].
    + exfalso.
      apply Hnot.
      exact Hred.
    + exact Hy.
Qed.

Definition scored_children (fuel : nat) (g : game) : list (game * nat) :=
  map (fun g' => (g', value_fuel fuel g')) (c4_next g).

Definition best_red_pair (fuel : nat) (g : game) : option (game * nat) :=
  max (comparing Nat.le snd) (scored_children fuel g).

Definition best_red_child (fuel : nat) (g : game) : option game :=
  option_map fst (best_red_pair fuel g).

Lemma best_red_pair_in :
  forall fuel g g' v,
    best_red_pair fuel g = Some (g', v) ->
    In (g', v) (scored_children fuel g).
Proof.
  intros fuel g g' v H.
  unfold best_red_pair, scored_children in *.
  pose proof
    (@max_is_in (game * nat) (comparing Nat.le snd) _ _ _ _ _
      (map (fun g' : game => (g', value_fuel fuel g')) (c4_next g)))
    as Hmaxin.
  rewrite H in Hmaxin.
  exact Hmaxin.
Qed.

Lemma best_red_child_value_eq_parent :
  forall fuel g g',
    get_result g = ongoing ->
    next_turn g = red ->
    best_red_child fuel g = Some g' ->
    value_fuel fuel g' = value_fuel (S fuel) g.
Proof.
  intros fuel g g' Hres Hturn Hbest.
  unfold best_red_child in Hbest.
  unfold option_map in Hbest.
  unfold best_red_pair in Hbest.
  destruct (max (comparing Nat.le snd) (scored_children fuel g))
    as [[gb vb]|] eqn:Hmax; try discriminate.
  inversion Hbest; subst gb; clear Hbest.
  assert (Hin : In (g', vb) (scored_children fuel g)).
  { unfold scored_children.
    unfold scored_children in Hmax.
    pose proof
      (@max_is_in (game * nat) (comparing Nat.le snd) _ _ _ _ _
        (map (fun g'0 : game => (g'0, value_fuel fuel g'0)) (c4_next g)))
      as Hmaxin.
    rewrite Hmax in Hmaxin.
    exact Hmaxin. }
  unfold scored_children in Hin.
  apply in_map_iff in Hin.
  destruct Hin as [gc [Heq Hin]].
  inversion Heq; subst; clear Heq.
  simpl.
  rewrite Hres.
  rewrite Hturn.
  unfold scored_children in Hmax.
  unfold scored_children.
  rewrite Hmax.
  reflexivity.
Qed.

Lemma yellow_child_value_ge_parent :
  forall fuel g g',
    get_result g = ongoing ->
    next_turn g = yellow ->
    In g' (c4_next g) ->
    value_fuel fuel g' >= value_fuel (S fuel) g.
Proof.
  intros fuel g g' Hres Hturn Hin.
  simpl.
  rewrite Hres.
  rewrite Hturn.
  set (scored := scored_children fuel g).
  destruct (max (comparing nat_ge snd) scored) as [[gb vb]|] eqn:Hmax.
  - assert (Hforall :
      Forall (fun p => (comparing nat_ge snd) p (gb, vb)) scored).
    { pose proof
        (@max_is_max (game * nat) (comparing nat_ge snd) _ _ _ _ _
          scored) as Hmaxprop.
      rewrite Hmax in Hmaxprop.
      exact Hmaxprop. }
    assert (Hin_pair : In (g', value_fuel fuel g') scored).
    { unfold scored, scored_children.
      apply in_map_iff.
      exists g'. split; auto. }
    rewrite Forall_forall in Hforall.
    specialize (Hforall _ Hin_pair).
    unfold comparing, nat_ge in Hforall.
    simpl in Hforall.
    subst scored.
    unfold scored_children in Hmax.
    rewrite Hmax.
    simpl.
    exact Hforall.
  - exfalso.
    assert (Hne : scored <> []).
    { intro Hnil.
      subst scored.
      apply map_eq_nil in Hnil.
      rewrite Hnil in Hin.
      contradiction. }
    destruct scored as [|p ps].
    + contradiction.
    + simpl in Hmax.
      destruct (max (comparing nat_ge snd) ps); discriminate.
Qed.

Inductive guided_step : nat -> game -> game -> Prop :=
| gs_red :
    forall fuel g g',
      get_result g = ongoing ->
      next_turn g = red ->
      best_red_child fuel g = Some g' ->
      guided_step (S fuel) g g'
| gs_yellow :
    forall fuel g g',
      get_result g = ongoing ->
      next_turn g = yellow ->
      In g' (c4_next g) ->
      guided_step (S fuel) g g'.

Inductive guided_path_upto : nat -> game -> game -> Prop :=
| gpu_stop :
    forall fuel g,
      guided_path_upto fuel g g
| gpu_step :
    forall fuel g g' h,
      guided_step (S fuel) g g' ->
      guided_path_upto fuel g' h ->
      guided_path_upto (S fuel) g h.

Lemma value_fuel_yellow_win_zero :
  forall fuel g,
    get_result g = won_by yellow ->
    value_fuel fuel g = 0.
Proof.
  induction fuel as [|fuel IH]; intros g Hwin; simpl.
  - unfold score. rewrite Hwin. reflexivity.
  - rewrite Hwin. unfold score. rewrite Hwin. reflexivity.
Qed.

Lemma value_fuel_ge_1_not_yellow_win :
  forall fuel g,
    value_fuel fuel g >= 1 ->
    get_result g <> won_by yellow.
Proof.
  intros fuel g Hge Hcontra.
  pose proof (value_fuel_yellow_win_zero fuel g Hcontra).
  lia.
Qed.

Lemma guided_step_preserves_nonloss_value :
  forall fuel g g',
    guided_step (S fuel) g g' ->
    value_fuel (S fuel) g >= 1 ->
    value_fuel fuel g' >= 1.
Proof.
  intros fuel g g' Hstep Hval.
  dependent destruction Hstep.
  - pose proof (best_red_child_value_eq_parent fuel g g' H H0 H1) as Heq.
    rewrite <- Heq in Hval.
    exact Hval.
  - pose proof (yellow_child_value_ge_parent fuel g g' H H0 H1) as Hge.
    lia.
Qed.

Theorem guided_path_upto_no_yellow_loss :
  forall fuel g h,
    guided_path_upto fuel g h ->
    value_fuel fuel g >= 1 ->
    get_result h <> won_by yellow.
Proof.
  intros fuel g h Hpath.
  induction Hpath.
  - intros Hval.
    eapply value_fuel_ge_1_not_yellow_win.
    exact Hval.
  - intros Hval Hbad.
    eapply IHHpath.
    + eapply guided_step_preserves_nonloss_value; eauto.
    + exact Hbad.
Qed.

(** If the 42-ply root value is non-losing (>= draw), then this policy
   cannot end in a yellow win in any prefix of a guided play. *)
Theorem red_policy_unbeatable_if_root_nonloss :
  value_fuel 42 c4_init >= 1 ->
  forall h,
    guided_path_upto 42 c4_init h ->
    get_result h <> won_by yellow.
Proof.
  intros Hroot h Hpath.
  eapply guided_path_upto_no_yellow_loss; eauto.
Qed.
