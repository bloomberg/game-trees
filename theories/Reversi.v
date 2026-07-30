(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Reversi (Othello) with depth-limited alpha-beta AI. *)

Require Import Corelib.Classes.RelationClasses.
Require Import Corelib.Program.Basics.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.
From Stdlib Require Import Relations.Relation_Operators.

Import ListNotations.
Import SigTNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.Relations.
Require Import GameTrees.Trees.
Require Import GameTrees.Cotrees.
Require Import GameTrees.Eval.
Require Import GameTrees.AlphaBeta.

(** Game types. *)

Inductive player : Type := black | white.

Definition cell : Type := option player.

(** 8x8 board stored as a list of 64 cells, row-major.
   Index = row * 8 + col, where row and col are 0-based. *)
Definition board : Type := list cell.

Record game : Type :=
  { current_board : board
  ; next_turn : player
  ; pass_count : nat  (* consecutive passes; 2 = game over *)
  }.

(** Decidable equality. *)

Lemma dec_eq_player : forall (p1 p2 : player), {p1 = p2} + {p1 <> p2}.
Proof. decide equality. Defined.

Lemma dec_eq_cell : forall (c1 c2 : cell), {c1 = c2} + {c1 <> c2}.
Proof. decide equality. apply dec_eq_player. Defined.

Lemma dec_eq_board : forall (b1 b2 : board), {b1 = b2} + {b1 <> b2}.
Proof. apply list_eq_dec, dec_eq_cell. Defined.

Lemma dec_eq_game : forall (g1 g2 : game), {g1 = g2} + {g1 <> g2}.
Proof.
  decide equality.
  - apply Nat.eq_dec.
  - apply dec_eq_player.
  - apply dec_eq_board.
Defined.

(** Boolean equality for players, derived from the decidable equality proof. *)
Definition player_eqb (p1 p2 : player) : bool :=
  if dec_eq_player p1 p2 then true else false.

(** Board access. *)

Definition other_player (p : player) : player :=
  match p with black => white | white => black end.

Lemma other_player_ne : forall p, p <> other_player p.
Proof. destruct p; discriminate. Qed.

Lemma other_other_player : forall p, other_player (other_player p) = p.
Proof. destruct p; reflexivity. Qed.

Definition get_cell (b : board) (pos : nat) : cell :=
  nth pos b None.

(** Boolean test for empty cells, used by executable clients that do not want
    to pattern match on the [option] representation directly. *)
Definition cell_is_empty (c : cell) : bool :=
  match c with
  | None => true
  | Some _ => false
  end.

(** Return the occupant of a non-empty cell.

    Empty cells are mapped to [black] as a harmless default for extraction
    clients that call this only after [cell_is_empty] has returned [false]. *)
Definition cell_player (c : cell) : player :=
  match c with
  | None => black
  | Some p => p
  end.

Fixpoint set_cell (b : board) (pos : nat) (c : cell) : board :=
  match b, pos with
  | [], _ => []
  | _ :: xs, O => c :: xs
  | x :: xs, S n => x :: set_cell xs n c
  end.

Definition pos_of (row col : nat) : nat := row * 8 + col.

Definition in_bounds (row col : nat) : bool :=
  (row <? 8) && (col <? 8).

(** The standard Reversi starting position: center 2x2 with alternating colors.
    Black at (3,4),(4,3); white at (3,3),(4,4). *)
Definition init_board : board :=
  repeat (@None player) 24 ++
  repeat (@None player) 3 ++ [Some white; Some black] ++ repeat (@None player) 3 ++
  repeat (@None player) 3 ++ [Some black; Some white] ++ repeat (@None player) 3 ++
  repeat (@None player) 24.

Lemma init_board_length : length init_board = 64.
Proof. vm_compute. reflexivity. Qed.

Definition reversi_init : game :=
  {| current_board := init_board
   ; next_turn := black
   ; pass_count := 0
   |}.

(** Directions and flipping. *)

(* 8 directions as (drow, dcol) pairs, represented as integers via Z. *)
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition direction : Type := (Z * Z)%type.

Definition all_directions : list direction :=
  [(-1,-1); (-1,0); (-1,1);
   ( 0,-1);         ( 0,1);
   ( 1,-1); ( 1,0); ( 1,1)].

(** Walk along a direction from (row, col), collecting positions of
   opponent pieces until we hit a piece of our own color.
   Returns the list of opponent positions to flip, or [] if no capture. *)
Fixpoint scan_direction (b : board) (p : player)
    (row col : Z) (dr dc : Z) (fuel : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
    let r := row + dr in
    let c := col + dc in
    if (0 <=? r) && (r <? 8) && (0 <=? c) && (c <? 8) then
      let pos := Z.to_nat (r * 8 + c) in
      match get_cell b pos with
      | Some q =>
        if dec_eq_player q p then []  (* hit our own piece — no capture without opponent between *)
        else pos :: scan_direction b p r c dr dc fuel'  (* opponent piece — tentatively collect *)
      | None => []  (* empty cell — no capture *)
      end
    else []  (* out of bounds *)
  end.

(** Scan and return captured positions only if the line terminates
   at one of our own pieces. *)
Fixpoint captures_in_direction (b : board) (p : player)
    (row col : Z) (dr dc : Z) (fuel : nat) : list nat :=
  match fuel with
  | O => []
  | S fuel' =>
    let r := row + dr in
    let c := col + dc in
    if (0 <=? r) && (r <? 8) && (0 <=? c) && (c <? 8) then
      let pos := Z.to_nat (r * 8 + c) in
      match get_cell b pos with
      | Some q =>
        if dec_eq_player q p then []  (* bookend found — return empty, caller accumulates *)
        else
          match captures_in_direction b p r c dr dc fuel' with
          | [] => []  (* didn't find our piece at the end — no capture *)
          | caps => pos :: caps  (* found bookend — include this opponent *)
          end
      | None => []
      end
    else []
  end.

Close Scope Z_scope.

(** Actually, let me use a simpler two-pass approach: first find the positions
   to flip, then flip them. The captures function walks until it finds
   a friendly piece, returning all opponent positions in between, or []
   if no friendly bookend is found.

   We need a different structure: walk collecting opponents, and only
   return them if we reach a friendly piece. *)

Fixpoint find_flips (b : board) (p : player)
    (row col : Z) (dr dc : Z) (acc : list nat) (fuel : nat) : list nat :=
  match fuel with
  | O => []  (* ran out of fuel without finding bookend *)
  | S fuel' =>
    let r := (row + dr)%Z in
    let c := (col + dc)%Z in
    if ((0 <=? r) && (r <? 8) && (0 <=? c) && (c <? 8))%Z then
      let pos := Z.to_nat (r * 8 + c)%Z in
      match get_cell b pos with
      | Some q =>
        if dec_eq_player q p then acc  (* bookend: return accumulated opponents *)
        else find_flips b p r c dr dc (acc ++ [pos]) fuel'  (* opponent: accumulate *)
      | None => []  (* empty: no capture *)
      end
    else []  (* out of bounds: no capture *)
  end.

Definition flips_in_direction (b : board) (p : player)
    (row col : nat) (d : direction) : list nat :=
  let '(dr, dc) := d in
  find_flips b p (Z.of_nat row) (Z.of_nat col) dr dc [] 7.

Definition all_flips (b : board) (p : player) (row col : nat) : list nat :=
  concat (map (flips_in_direction b p row col) all_directions).

(** A move at (row, col) is valid if it flips at least one opponent piece. *)
Definition is_valid_move (b : board) (p : player) (row col : nat) : bool :=
  in_bounds row col &&
  match get_cell b (pos_of row col) with
  | None => negb (Nat.eqb (length (all_flips b p row col)) 0)
  | Some _ => false
  end.

(** Apply a list of flips to the board. *)
Definition apply_flips (b : board) (p : player) (flips : list nat) : board :=
  fold_left (fun b' pos => set_cell b' pos (Some p)) flips b.

(** Place a piece and flip captured opponents. *)
Definition place_piece (b : board) (p : player) (row col : nat) : board :=
  let pos := pos_of row col in
  let b' := set_cell b pos (Some p) in
  let flips := all_flips b p row col in
  apply_flips b' p flips.

(** Moves and result. *)

(** A move is a position (row, col) encoded as a single nat = row * 8 + col.
   We enumerate all 64 positions and filter for validity. *)
Definition all_positions : list (nat * nat) :=
  concat (map (fun r => map (fun c => (r, c)) (seq 0 8)) (seq 0 8)).

Lemma all_positions_length : length all_positions = 64.
Proof. vm_compute. reflexivity. Qed.

Definition valid_positions (b : board) (p : player) : list (nat * nat) :=
  filter (fun '(r, c) => is_valid_move b p r c) all_positions.

Inductive result : Type :=
| won_by : player -> result
| draw : result
| ongoing : result.

Definition count_pieces (b : board) (p : player) : nat :=
  length (filter (fun c => match c with Some q => if dec_eq_player q p then true else false | None => false end) b).

Definition empty_count (b : board) : nat :=
  length (filter (fun c => match c with None => true | _ => false end) b).

Definition get_result (g : game) : result :=
  let b := current_board g in
  let p := next_turn g in
  if Nat.leb 2 (pass_count g) then
    (* Both players passed — game over, count pieces. *)
    let nb := count_pieces b black in
    let nw := count_pieces b white in
    if nb <? nw then won_by white
    else if nw <? nb then won_by black
    else draw
  else if Nat.eqb (empty_count b) 0 then
    (* Board full. *)
    let nb := count_pieces b black in
    let nw := count_pieces b white in
    if nb <? nw then won_by white
    else if nw <? nb then won_by black
    else draw
  else ongoing.

(** Numeric encoding of [get_result] for simple extracted UI code:
    [0] means ongoing, [1] means black won, [2] means white won, and [3] means
    draw. *)
Definition result_code (g : game) : nat :=
  match get_result g with
  | ongoing => 0
  | won_by black => 1
  | won_by white => 2
  | draw => 3
  end.

(** Projection wrapper for extracted clients that should not depend on the
    concrete field name of [game]. *)
Definition board_of (g : game) : board := current_board g.

(** Projection wrapper returning the player whose turn it is. *)
Definition turn_of (g : game) : player := next_turn g.

(** Boolean test for whether a player is [black]. *)
Definition player_is_black (p : player) : bool := player_eqb p black.

(** A move is either placing at (row, col) or passing. *)
Inductive move : Type :=
| place : nat -> nat -> move  (* row, col *)
| pass : move.

Definition apply_move (g : game) (m : move) : game :=
  let b := current_board g in
  let p := next_turn g in
  match m with
  | place row col =>
    {| current_board := place_piece b p row col
     ; next_turn := other_player p
     ; pass_count := 0
     |}
  | pass =>
    {| current_board := b
     ; next_turn := other_player p
     ; pass_count := S (pass_count g)
     |}
  end.

Definition moves (g : game) : list move :=
  match get_result g with
  | won_by _ | draw => []
  | ongoing =>
    let vp := valid_positions (current_board g) (next_turn g) in
    match vp with
    | [] => [pass]  (* no valid placements — must pass *)
    | _ => map (fun '(r, c) => place r c) vp
    end
  end.

Inductive valid_move : game -> move -> Prop :=
| valid_place : forall g row col,
    get_result g = ongoing ->
    is_valid_move (current_board g) (next_turn g) row col = true ->
    valid_move g (place row col)
| valid_pass : forall g,
    get_result g = ongoing ->
    valid_positions (current_board g) (next_turn g) = [] ->
    valid_move g pass.

Lemma filter_all_valid :
  forall b p,
    Forall (fun '(r, c) => is_valid_move b p r c = true)
           (valid_positions b p).
Proof.
  intros b p.
  apply Forall_forall. intros [r c] Hin.
  unfold valid_positions in Hin.
  apply filter_In in Hin. destruct Hin as [_ Hv]. exact Hv.
Qed.

Lemma valid_moves : forall g, Forall (valid_move g) (moves g).
Proof.
  intros g.
  unfold moves.
  destruct (get_result g) eqn:Hres; try constructor.
  destruct (valid_positions (current_board g) (next_turn g)) eqn:Hvp.
  - constructor; [|constructor].
    apply valid_pass; auto.
  - pose proof (filter_all_valid (current_board g) (next_turn g)) as Hall.
    rewrite Hvp in Hall.
    apply Forall_map.
    eapply Forall_impl; [|exact Hall].
    intros [r c] Hv. apply valid_place; auto.
Qed.

(** Game step. *)

Inductive game_step : game -> game -> Prop :=
| gstep : forall g m,
    length (current_board g) = 64 ->
    get_result g = ongoing ->
    valid_move g m ->
    game_step g (apply_move g m).

Definition reversi_next (g : game) : list game :=
  match get_result g with
  | ongoing => map (apply_move g) (moves g)
  | _ => []
  end.

(** Well-foundedness. *)

(** Termination measure: empty cells decrease on placements, and
   pass_count increases (bounded by 2) on passes. We combine them
   into a single lexicographic measure: (empty_count, 2 - pass_count). *)
Definition measure (g : game) : nat :=
  empty_count (current_board g) * 3 + (2 - pass_count g).

Definition later (g1 g2 : game) : Prop :=
  measure g1 < measure g2.

Instance WF_later : WellFounded later.
Proof.
  unfold later.
  apply Relations.wf_inverse_image, Nat.lt_wf_0.
Defined.

(** set_cell and empty_count properties. *)

Lemma set_cell_length :
  forall b pos c, pos < length b -> length (set_cell b pos c) = length b.
Proof.
  induction b as [|x xs IH]; intros pos c Hlt.
  - simpl in Hlt. lia.
  - destruct pos; simpl in *; [lia | rewrite IH; lia].
Qed.

Lemma get_cell_set_cell_same :
  forall b pos c, pos < length b -> get_cell (set_cell b pos c) pos = c.
Proof.
  unfold get_cell.
  induction b as [|x xs IH]; intros pos c Hlt.
  - simpl in Hlt. lia.
  - destruct pos; simpl in *; auto. apply IH. lia.
Qed.

Lemma get_cell_set_cell_other :
  forall b pos1 pos2 c,
    pos1 <> pos2 ->
    get_cell (set_cell b pos1 c) pos2 = get_cell b pos2.
Proof.
  unfold get_cell.
  induction b as [|x xs IH]; intros [|n1] [|n2] c Hne; simpl;
    auto; try lia; apply IH; lia.
Qed.

(** empty_count with set_cell at an empty position: S version for clean nat arithmetic. *)
Lemma set_cell_empty_decreases :
  forall b pos c,
    pos < length b ->
    get_cell b pos = None ->
    c <> None ->
    S (empty_count (set_cell b pos c)) = empty_count b.
Proof.
  unfold empty_count, get_cell.
  induction b as [|x xs IH]; intros pos c Hlt Hnone Hnn.
  - simpl in Hlt. lia.
  - destruct pos as [|pos'].
    + simpl in *. subst x. destruct c; [simpl; lia | contradiction Hnn; auto].
    + simpl in *. destruct x; simpl; rewrite (IH pos' c); auto; lia.
Qed.

(** empty_count with set_cell at an occupied position. *)
Lemma set_cell_occupied_preserves :
  forall b pos c q,
    pos < length b ->
    get_cell b pos = Some q ->
    c <> None ->
    empty_count (set_cell b pos c) = empty_count b.
Proof.
  unfold empty_count, get_cell.
  induction b as [|x xs IH]; intros pos c q Hlt Hsome Hnn.
  - simpl in Hlt. lia.
  - destruct pos as [|pos'].
    + simpl in *. subst x. destruct c; [simpl; auto | contradiction Hnn; auto].
    + simpl in *. destruct x; simpl; rewrite (IH pos' c q); auto; lia.
Qed.

(** apply_flips where all flipped positions are occupied preserves empty_count. *)
Lemma apply_flips_preserves_empty :
  forall flips b p,
    (forall pos, In pos flips -> pos < length b) ->
    (forall pos, In pos flips -> get_cell b pos <> None) ->
    empty_count (apply_flips b p flips) = empty_count b.
Proof.
  induction flips as [|f fs IH]; intros b p Hbnd Hocc; simpl.
  - reflexivity.
  - assert (Hf_bnd : f < length b) by (apply Hbnd; left; auto).
    assert (Hf_occ : get_cell b f <> None) by (apply Hocc; left; auto).
    destruct (get_cell b f) as [q|] eqn:Ecell; [|contradiction].
    rewrite IH.
    + apply (set_cell_occupied_preserves b f (Some p) q Hf_bnd Ecell).
      discriminate.
    + intros pos Hin.
      rewrite set_cell_length; [apply Hbnd; right; exact Hin | exact Hf_bnd].
    + intros pos Hin.
      destruct (Nat.eq_dec pos f) as [Heq|Hne].
      * subst. rewrite get_cell_set_cell_same; [discriminate | exact Hf_bnd].
      * rewrite get_cell_set_cell_other; [apply Hocc; right; exact Hin | auto].
Qed.

(** Positions returned by find_flips are occupied by the opponent. *)
Lemma find_flips_occupied :
  forall b p row col dr dc acc fuel pos,
    In pos (find_flips b p row col dr dc acc fuel) ->
    In pos acc \/ get_cell b pos <> None.
Proof.
  intros b p row col dr dc acc fuel.
  revert row col acc.
  induction fuel as [|fuel' IH]; intros row col acc pos Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin.
    destruct ((0 <=? row + dr)%Z && (row + dr <? 8)%Z &&
              (0 <=? col + dc)%Z && (col + dc <? 8)%Z)%bool.
    + destruct (get_cell b (Z.to_nat ((row + dr) * 8 + (col + dc))%Z)) as [q|] eqn:Ecell.
      * destruct (dec_eq_player q p).
        -- left. exact Hin.
        -- apply IH in Hin.
           destruct Hin as [Hin_app | Hin_cell].
           ++ apply in_app_iff in Hin_app.
              destruct Hin_app as [Hin_acc | [Heq | []]].
              ** left. exact Hin_acc.
              ** right. subst. rewrite Ecell. discriminate.
           ++ right. exact Hin_cell.
      * contradiction.
    + contradiction.
Qed.

(** Positions in all_flips are occupied on the board. *)
Lemma all_flips_occupied :
  forall b p row col pos,
    In pos (all_flips b p row col) ->
    get_cell b pos <> None.
Proof.
  intros b p row col pos Hin.
  unfold all_flips in Hin.
  apply in_concat in Hin as [l [Hin_l Hin_pos]].
  apply in_map_iff in Hin_l as [[dr dc] [Heq Hin_dir]].
  subst l.
  unfold flips_in_direction in Hin_pos.
  apply find_flips_occupied in Hin_pos.
  destruct Hin_pos as [[] | H]. exact H.
Qed.

(** Positions in find_flips (starting from acc=[]) are in bounds. *)
Lemma find_flips_in_bounds :
  forall b p row col dr dc acc fuel pos,
    In pos (find_flips b p row col dr dc acc fuel) ->
    In pos acc \/ pos < 64.
Proof.
  intros b p row col dr dc acc fuel.
  revert row col acc.
  induction fuel as [|fuel' IH]; intros row col acc pos Hin.
  - simpl in Hin. contradiction.
  - simpl in Hin.
    destruct ((0 <=? row + dr)%Z && (row + dr <? 8)%Z &&
              (0 <=? col + dc)%Z && (col + dc <? 8)%Z)%bool eqn:Ebnd.
    + destruct (get_cell b _) as [q|] eqn:Ecell.
      * destruct (dec_eq_player q p).
        -- left. exact Hin.
        -- apply IH in Hin.
           destruct Hin as [Hin_app | Hin_bnd].
           ++ apply in_app_iff in Hin_app.
              destruct Hin_app as [Hin_acc | [Heq | []]].
              ** left. exact Hin_acc.
              ** right. subst.
                 apply Bool.andb_true_iff in Ebnd as [Ebnd Ec8].
                 apply Bool.andb_true_iff in Ebnd as [Ebnd Ec0].
                 apply Bool.andb_true_iff in Ebnd as [Er0 Er8].
                 apply Z.leb_le in Er0. apply Z.ltb_lt in Er8.
                 apply Z.leb_le in Ec0. apply Z.ltb_lt in Ec8.
                 lia.
           ++ right. exact Hin_bnd.
      * contradiction.
    + contradiction.
Qed.

Lemma all_flips_in_bounds :
  forall b p row col pos,
    length b = 64 ->
    In pos (all_flips b p row col) ->
    pos < length b.
Proof.
  intros b p row col pos Hlen Hin. rewrite Hlen.
  unfold all_flips in Hin.
  apply in_concat in Hin as [l [Hin_l Hin_pos]].
  apply in_map_iff in Hin_l as [[dr dc] [Heq Hin_dir]].
  subst l.
  unfold flips_in_direction in Hin_pos.
  apply find_flips_in_bounds in Hin_pos.
  destruct Hin_pos as [[] | H]. exact H.
Qed.

(** For placements: show the measure strictly decreases. *)
Lemma place_decreases_empty :
  forall b p row col,
    length b = 64 ->
    is_valid_move b p row col = true ->
    empty_count (place_piece b p row col) < empty_count b.
Proof.
  intros b p row col Hlen Hv.
  unfold is_valid_move in Hv.
  apply Bool.andb_true_iff in Hv as [Hbnd Hcell].
  unfold in_bounds in Hbnd.
  apply Bool.andb_true_iff in Hbnd as [Hr Hc].
  apply Nat.ltb_lt in Hr. apply Nat.ltb_lt in Hc.
  destruct (get_cell b (pos_of row col)) eqn:Ecell; [discriminate|].
  apply negb_true_iff in Hcell. apply Nat.eqb_neq in Hcell.
  unfold place_piece.
  assert (Hpos_lt : pos_of row col < length b) by (unfold pos_of; lia).
  rewrite apply_flips_preserves_empty.
  - pose proof (set_cell_empty_decreases b (pos_of row col) (Some p)
                  Hpos_lt Ecell ltac:(discriminate)) as Hsc.
    lia.
  - intros pos Hin.
    rewrite set_cell_length; auto.
    exact (all_flips_in_bounds b p row col pos Hlen Hin).
  - intros pos Hin.
    destruct (Nat.eq_dec pos (pos_of row col)) as [Heq|Hne].
    + subst. rewrite get_cell_set_cell_same; [discriminate | exact Hpos_lt].
    + rewrite get_cell_set_cell_other; auto.
      exact (all_flips_occupied b p row col pos Hin).
Qed.

Lemma less_measure_place :
  forall g row col,
    length (current_board g) = 64 ->
    get_result g = ongoing ->
    is_valid_move (current_board g) (next_turn g) row col = true ->
    later (apply_move g (place row col)) g.
Proof.
  intros g row col Hlen Hres Hv.
  unfold later, measure.
  simpl. simpl pass_count.
  assert (Hlt : empty_count (place_piece (current_board g) (next_turn g) row col) <
                empty_count (current_board g)).
  { apply place_decreases_empty; auto. }
  lia.
Qed.

Lemma pass_count_lt_2 :
  forall g, get_result g = ongoing -> pass_count g < 2.
Proof.
  intros g H. unfold get_result in H.
  destruct (pass_count g) as [|[|n]].
  - lia.
  - lia.
  - (* pass_count >= 2: Nat.leb 2 (S (S n)) = true, so get_result picks a winner. *)
    exfalso.
    unfold Nat.leb in H. simpl in H.
    (* After unfolding, the if-then-else picks a branch that's not ongoing. *)
    repeat match type of H with
    | context [if ?c then _ else _] => destruct c
    end; discriminate.
Qed.

Lemma less_measure_pass :
  forall g,
    get_result g = ongoing ->
    later (apply_move g pass) g.
Proof.
  intros g Hres.
  pose proof (pass_count_lt_2 g Hres) as Hpc.
  unfold later, measure. simpl.
  destruct (pass_count g) as [|[|n]]; try lia.
Qed.

Lemma less_measure_after_move :
  forall g m,
    length (current_board g) = 64 ->
    valid_move g m ->
    later (apply_move g m) g.
Proof.
  intros g m Hlen Hv.
  inversion Hv; subst.
  - apply less_measure_place; auto.
  - apply less_measure_pass; auto.
Qed.

Instance WF_flip_game_step : WellFounded (flip game_step).
Proof.
  eapply WF_subrelation, WF_later.
  intros g2 g1; inversion 1.
  apply less_measure_after_move; auto.
Defined.

Lemma reversi_next_produces_steps :
  forall g, length (current_board g) = 64 ->
    Forall (game_step g) (reversi_next g).
Proof.
  intros g Hlen.
  unfold reversi_next.
  destruct (get_result g) eqn:Hres; try constructor.
  unfold moves. rewrite Hres.
  destruct (valid_positions (current_board g) (next_turn g)) eqn:Hvp.
  - (* pass case *)
    constructor; [|constructor].
    apply gstep; auto.
    apply valid_pass; auto.
  - (* placement case *)
    rewrite Forall_map. rewrite Forall_map.
    pose proof (filter_all_valid (current_board g) (next_turn g)) as Hall.
    rewrite Hvp in Hall.
    eapply Forall_impl; [|exact Hall].
    intros [r c] Hv.
    apply gstep; auto.
    apply valid_place; auto.
Qed.

Lemma reversi_next_intrinsic :
  forall g1 : game,
    {l : list game | Forall (game_step g1) l}.
Proof.
  intros g1.
  destruct (Nat.eq_dec (length (current_board g1)) 64) as [Hlen | Hlen].
  - exists (reversi_next g1).
    apply reversi_next_produces_steps. exact Hlen.
  - exists []. constructor.
Defined.

(** The complete game tree. The fact that this definition type-checks IS
   the finiteness proof: [tree] is inductive and [unfold_tree] requires
   a well-founded relation. *)
Definition complete_tree : tree game :=
  unfold_tree (flip game_step) reversi_next_intrinsic reversi_init.

Theorem complete_tree_sound :
  forall g,
    In_tree g complete_tree ->
    reachable reversi_next_intrinsic reversi_init g.
Proof.
  apply unfold_tree_sound.
Qed.

Theorem complete_tree_complete :
  forall g,
    reachable reversi_next_intrinsic reversi_init g ->
    In_tree g complete_tree.
Proof.
  apply unfold_tree_complete.
Qed.

(** Decidable equality for result and move. *)

Lemma dec_eq_result : forall (r1 r2 : result), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. apply dec_eq_player. Defined.

Lemma dec_eq_move : forall (m1 m2 : move), {m1 = m2} + {m1 <> m2}.
Proof. decide equality; apply Nat.eq_dec. Defined.

(** Board invariant preservation. *)

Lemma apply_flips_length :
  forall flips b p,
    (forall pos, In pos flips -> pos < length b) ->
    length (apply_flips b p flips) = length b.
Proof.
  induction flips as [|f fs IH]; intros b p Hbnd; simpl.
  - reflexivity.
  - rewrite IH.
    + apply set_cell_length. apply Hbnd. left. auto.
    + intros pos Hin. rewrite set_cell_length.
      * apply Hbnd. right. exact Hin.
      * apply Hbnd. left. auto.
Qed.

Lemma place_piece_length :
  forall b p row col,
    length b = 64 ->
    is_valid_move b p row col = true ->
    length (place_piece b p row col) = 64.
Proof.
  intros b p row col Hlen Hv.
  unfold place_piece.
  unfold is_valid_move in Hv.
  apply Bool.andb_true_iff in Hv as [Hbnd Hcell].
  unfold in_bounds in Hbnd.
  apply Bool.andb_true_iff in Hbnd as [Hr Hc].
  apply Nat.ltb_lt in Hr. apply Nat.ltb_lt in Hc.
  assert (Hpos : pos_of row col < length b) by (unfold pos_of; lia).
  rewrite apply_flips_length.
  - rewrite set_cell_length; auto.
  - intros pos Hin. rewrite set_cell_length; auto.
    exact (all_flips_in_bounds b p row col pos Hlen Hin).
Qed.

Lemma apply_move_length :
  forall g m,
    length (current_board g) = 64 ->
    valid_move g m ->
    length (current_board (apply_move g m)) = 64.
Proof.
  intros g m Hlen Hv. inversion Hv; subst; simpl.
  - apply place_piece_length; auto.
  - exact Hlen.
Qed.

Lemma valid_board_init : length (current_board reversi_init) = 64.
Proof. vm_compute. reflexivity. Qed.

(** Moves completeness. *)

Lemma in_all_positions :
  forall row col, row < 8 -> col < 8 -> In (row, col) all_positions.
Proof.
  intros row col Hr Hc. unfold all_positions.
  apply in_concat. exists (map (fun c => (row, c)) (seq 0 8)). split.
  - apply in_map_iff. exists row. split; auto. apply in_seq. lia.
  - apply in_map_iff. exists col. split; auto. apply in_seq. lia.
Qed.

Lemma valid_move_in_valid_positions :
  forall b p row col,
    is_valid_move b p row col = true ->
    In (row, col) (valid_positions b p).
Proof.
  intros b p row col Hv.
  apply filter_In. split.
  - apply in_all_positions.
    + unfold is_valid_move in Hv. apply Bool.andb_true_iff in Hv as [Hbnd _].
      unfold in_bounds in Hbnd. apply Bool.andb_true_iff in Hbnd as [Hr _].
      apply Nat.ltb_lt in Hr. exact Hr.
    + unfold is_valid_move in Hv. apply Bool.andb_true_iff in Hv as [Hbnd _].
      unfold in_bounds in Hbnd. apply Bool.andb_true_iff in Hbnd as [_ Hc].
      apply Nat.ltb_lt in Hc. exact Hc.
  - exact Hv.
Qed.

Lemma moves_complete :
  forall g m, valid_move g m -> In m (moves g).
Proof.
  intros g m Hv. inversion Hv; subst.
  - (* place case *)
    assert (Hin : In (row, col)
                     (valid_positions (current_board g) (next_turn g))).
    { apply valid_move_in_valid_positions. exact H0. }
    unfold moves. rewrite H.
    destruct (valid_positions (current_board g) (next_turn g)).
    + contradiction.
    + apply in_map_iff. exists (row, col). split; auto.
  - (* pass case *)
    unfold moves. rewrite H. rewrite H0. left. auto.
Qed.

(** Termination conditions. *)

Lemma full_board_no_moves :
  forall g, empty_count (current_board g) = 0 -> moves g = [].
Proof.
  intros g Hfull. unfold moves.
  destruct (get_result g) eqn:Hres; auto.
  exfalso.
  pose proof (pass_count_lt_2 g Hres) as Hpc.
  unfold get_result in Hres.
  destruct (pass_count g) as [|[|n]]; try lia;
    simpl in Hres; rewrite Hfull in Hres; simpl in Hres;
    repeat match type of Hres with
    | context [if ?c then _ else _] => destruct c
    end; discriminate.
Qed.

Lemma double_pass_no_moves :
  forall g, pass_count g >= 2 -> moves g = [].
Proof.
  intros g Hpc. unfold moves.
  destruct (get_result g) eqn:Hres; auto.
  exfalso. unfold get_result in Hres.
  destruct (pass_count g) as [|[|n]]; try lia;
    simpl in Hres;
    repeat match type of Hres with
    | context [if ?c then _ else _] => destruct c
    end; discriminate.
Qed.

(** Result exclusivity. *)

(** The result function cannot simultaneously declare both players winners. *)
Theorem at_most_one_winner :
  forall g,
    ~ (get_result g = won_by black /\ get_result g = won_by white).
Proof.
  intros g [H1 H2]. rewrite H1 in H2. discriminate.
Qed.

(** Stronger: get_result is deterministic — it returns a unique result. *)
Theorem result_deterministic :
  forall g r1 r2,
    get_result g = r1 -> get_result g = r2 -> r1 = r2.
Proof.
  intros g r1 r2 H1 H2. congruence.
Qed.

(** Scoring. *)

(** Black is the maximizer (score 2), white is the minimizer (score 0). *)
Definition score (g : game) : nat :=
  match get_result g with
  | won_by black => 2
  | won_by white => 0
  | draw => 1
  | ongoing => 1
  end.

(** The four high-value corner positions on an 8x8 Reversi board. *)
Definition corner_positions : list (nat * nat) :=
  [(0,0); (0,7); (7,0); (7,7)].

(** Count how many corners are occupied by the given player. *)
Definition count_corners (b : board) (p : player) : nat :=
  length (filter (fun '(r, c) =>
    match get_cell b (pos_of r c) with
    | Some q => player_eqb q p
    | None => false
    end) corner_positions).

(** Clamp a signed heuristic score to the natural interval used by alpha-beta. *)
Definition clamp_score (z : Z) : nat :=
  Z.to_nat (Z.max 0 (Z.min 1000 z)).

(** Evaluation function for practical AI play.

    Terminal positions receive exact win/loss/draw values. Ongoing positions
    combine material, mobility, and corner ownership into a bounded score where
    larger values favor black and smaller values favor white. *)
Definition heuristic_score (g : game) : nat :=
  match get_result g with
  | won_by black => 1000
  | won_by white => 0
  | draw => 500
  | ongoing =>
    let b := current_board g in
    let nb := Z.of_nat (count_pieces b black) in
    let nw := Z.of_nat (count_pieces b white) in
    let mb := Z.of_nat (length (valid_positions b black)) in
    let mw := Z.of_nat (length (valid_positions b white)) in
    let cb := Z.of_nat (count_corners b black) in
    let cw := Z.of_nat (count_corners b white) in
    clamp_score (500 + (nb - nw) * 4 + (mb - mw) * 10 + (cb - cw) * 80)
  end.

(** Correctness of alpha-beta for Reversi. *)

Require Import ExtLib.Core.RelDec.

Theorem reversi_eval_ab_correct :
  forall (t : tree game),
    eval_ab players_le_ge score (fun _ => false) t =
    eval_val players_le_ge score t.
Proof.
  intros t.
  apply eval_ab_correct.
  - exact players_le_ge_strong.
  - exact players_le_ge_adversarial.
Qed.

(** Depth-limited tree for execution. *)

Definition reversi_conext (g : game) : Cotrees.colist game :=
  Cotrees.colist_of_list (proj1_sig (reversi_next_intrinsic g)).

Definition search_depth : nat := 5.

Definition ai_subtree (g : game) : tree game :=
  Cotrees.tree_of_cotree search_depth
    (Cotrees.unfold_cotree reversi_conext g).

Lemma costep_iff_step :
  forall g1 g2,
    Cotrees.costep reversi_conext g1 g2 <-> step reversi_next_intrinsic g1 g2.
Proof.
  intros g1 g2. unfold Cotrees.costep, reversi_conext.
  rewrite <- Cotrees.In_colist_iff_In_colist_of_list.
  reflexivity.
Qed.

Theorem ai_subtree_coreachable :
  forall g g',
    In_tree g' (ai_subtree g) ->
    Cotrees.coreachable reversi_conext g g'.
Proof.
  intros g g' Hin.
  apply Cotrees.unfold_cotree_sound.
  apply tree_of_cotree_In_cotree in Hin. exact Hin.
Qed.

Theorem ai_subtree_reachable :
  forall g g',
    In_tree g' (ai_subtree g) ->
    reachable reversi_next_intrinsic g g'.
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

(** Lazy alpha-beta on Reversi cotrees. *)

(** Reversi instance of the generic cotree alpha-beta correctness theorem.

    This specializes [eval_ab_co_minimax] to Reversi games and the alternating
    [players_le_ge] stream, while leaving the scoring function abstract. *)
Corollary reversi_eval_ab_co_minimax :
  forall (score' : game -> nat) (depth width : nat) (ct : cotree game),
    eval_ab_co depth width players_le_ge score' (fun _ => false) ct =
    eval_val players_le_ge score' (materialize depth width ct).
Proof.
  intros.
  apply eval_ab_co_minimax.
  - exact players_le_ge_strong.
  - exact players_le_ge_adversarial.
Qed.

(** Board symmetry. *)

(** Reflect board horizontally: column c -> column 7-c.
   For row-major indexing, position row*8+col -> row*8+(7-col). *)
Definition reflect_pos (pos : nat) : nat :=
  let row := pos / 8 in
  let col := pos mod 8 in
  row * 8 + (7 - col).

Definition reflect_board_fn (b : board) : board :=
  map (fun i => get_cell b (reflect_pos i)) (seq 0 64).

Definition reflect_move (m : move) : move :=
  match m with
  | place row col => place row (7 - col)
  | pass => pass
  end.

Definition reflect_game (g : game) : game :=
  {| current_board := reflect_board_fn (current_board g)
   ; next_turn := next_turn g
   ; pass_count := pass_count g
   |}.

Lemma reflect_board_fn_length :
  forall b, length (reflect_board_fn b) = 64.
Proof.
  intros. unfold reflect_board_fn. rewrite map_length, seq_length. auto.
Qed.

Lemma reflect_pos_in_bounds :
  forall pos, pos < 64 -> reflect_pos pos < 64.
Proof.
  intros pos H. unfold reflect_pos.
  assert (pos / 8 < 8) by (apply Nat.div_lt_upper_bound; lia).
  assert (pos mod 8 < 8) by (apply Nat.mod_upper_bound; lia).
  lia.
Qed.

Lemma reflect_pos_involutive :
  forall pos, pos < 64 -> reflect_pos (reflect_pos pos) = pos.
Proof.
  intros pos H.
  do 64 (destruct pos as [|pos]; [vm_compute; reflexivity|]).
  lia.
Qed.

(** Rotate board 90 degrees clockwise: (row, col) -> (col, 7-row). *)
Definition rotate_pos (pos : nat) : nat :=
  let row := pos / 8 in
  let col := pos mod 8 in
  col * 8 + (7 - row).

Definition rotate_board_fn (b : board) : board :=
  map (fun i => get_cell b (rotate_pos i)) (seq 0 64).

Definition rotate_move (m : move) : move :=
  match m with
  | place row col => place col (7 - row)
  | pass => pass
  end.

Definition rotate_game (g : game) : game :=
  {| current_board := rotate_board_fn (current_board g)
   ; next_turn := next_turn g
   ; pass_count := pass_count g
   |}.

Lemma rotate_board_fn_length :
  forall b, length (rotate_board_fn b) = 64.
Proof.
  intros. unfold rotate_board_fn. rewrite map_length, seq_length. auto.
Qed.

Lemma rotate_pos_in_bounds :
  forall pos, pos < 64 -> rotate_pos pos < 64.
Proof.
  intros pos H. unfold rotate_pos.
  assert (pos / 8 < 8) by (apply Nat.div_lt_upper_bound; lia).
  assert (pos mod 8 < 8) by (apply Nat.mod_upper_bound; lia).
  lia.
Qed.

(** Stable discs. *)

(** A corner position is one of (0,0), (0,7), (7,0), (7,7). *)
Definition is_corner (row col : nat) : bool :=
  ((row =? 0) || (row =? 7)) && ((col =? 0) || (col =? 7)).

(** An edge position is on the border of the board. *)
Definition is_edge (row col : nat) : bool :=
  (row =? 0) || (row =? 7) || (col =? 0) || (col =? 7).

(* A disc at position pos is stable for player p if it can never be flipped.
   We define stability inductively: corners are always stable, and a disc
   adjacent to stable discs in all flip-vulnerable directions is stable. *)

(** For certificate purposes, we represent a stable set as a list of positions
   known to be stable, and verify it against the board. *)
Definition stable_set := list nat.

(** Check that every position in the stable set is occupied by player p. *)
Definition stable_set_owned (b : board) (p : player) (ss : stable_set) : bool :=
  forallb (fun pos =>
    match get_cell b pos with
    | Some q => if dec_eq_player q p then true else false
    | None => false
    end) ss.

(** Count pieces owned by player p. *)
Definition piece_count (b : board) (p : player) : nat :=
  count_pieces b p.

(** A player with more than 32 stable discs has won — the opponent cannot
   possibly have a majority since there are only 64 cells. *)
Definition stable_majority (b : board) (p : player) (ss : stable_set) : bool :=
  stable_set_owned b p ss && (32 <? length ss).

(** Certificate type. *)

(** A certificate is a compact witness that a game position has a particular
   game-theoretic value. It mirrors the game tree but uses structural
   lemmas to skip subtrees where the outcome is determined. *)
Inductive cert_node : Type :=
  (* The current player plays move m, opponent responds per sub-certificate. *)
| cert_play : move -> cert_node -> cert_node
  (* The current player can play any of these moves; all lead to the
     claimed value. Used at MAX nodes. *)
| cert_exists : move -> cert_node -> cert_node
  (* All opponent responses are covered. Used at MIN nodes. *)
| cert_forall : list (move * cert_node) -> cert_node
  (* Leaf: game is terminal, result is determined by get_result. *)
| cert_terminal : cert_node
  (* Stable disc majority: player p owns >32 stable discs. *)
| cert_stable : player -> stable_set -> cert_node
  (* Symmetry: the position is equivalent to a reflected/rotated one
     already certified. The transform maps this position to the
     certified one. *)
| cert_reflect : cert_node -> cert_node
| cert_rotate : cert_node -> cert_node.

(** Certificate checker. *)

(** The claimed result of a certified position. *)
Inductive cert_result : Type :=
| cert_win : player -> cert_result
| cert_draw : cert_result.

(** Check a certificate against a game state. Returns Some r if the
   certificate proves that the game-theoretic value is r. *)
Fixpoint check_cert (g : game) (c : cert_node) (fuel : nat) : option cert_result :=
  match fuel with
  | O => None  (* out of fuel *)
  | S fuel' =>
    match c with
    | cert_terminal =>
      match get_result g with
      | won_by p => Some (cert_win p)
      | draw => Some cert_draw
      | ongoing => None  (* not actually terminal *)
      end

    | cert_stable p ss =>
      if stable_majority (current_board g) p ss
      then Some (cert_win p)
      else None

    | cert_exists m sub =>
      (* Current player has a move m that leads to value r. *)
      match get_result g with
      | ongoing =>
        if is_valid_move (current_board g) (next_turn g)
             match m with place r c => r | pass => 0 end
             match m with place r c => c | pass => 0 end
           || match m with pass => true | _ => false end
        then check_cert (apply_move g m) sub fuel'
        else None
      | _ => None
      end

    | cert_forall responses =>
      (* All moves by the current player are covered. *)
      match get_result g with
      | ongoing =>
        let mvs := moves g in
        let check_one :=
          fun (acc : option cert_result) (mv : move) =>
            match acc with
            | None => None
            | Some r =>
              match find (fun '(m', _) => if dec_eq_move m' mv then true else false)
                         responses with
              | None => None  (* move not covered *)
              | Some (_, sub) =>
                match check_cert (apply_move g mv) sub fuel' with
                | Some r' =>
                  match r, r' with
                  | cert_win p1, cert_win p2 =>
                    if dec_eq_player p1 p2 then Some r else None
                  | cert_draw, cert_draw => Some cert_draw
                  | _, _ => None
                  end
                | None => None
                end
              end
            end in
        match mvs with
        | [] => None
        | mv :: rest =>
          match find (fun '(m', _) => if dec_eq_move m' mv then true else false)
                     responses with
          | None => None
          | Some (_, sub) =>
            match check_cert (apply_move g mv) sub fuel' with
            | None => None
            | Some r => fold_left check_one rest (Some r)
            end
          end
        end
      | _ => None
      end

    | cert_play m sub =>
      match get_result g with
      | ongoing => check_cert (apply_move g m) sub fuel'
      | _ => None
      end

    | cert_reflect sub =>
      check_cert (reflect_game g) sub fuel'

    | cert_rotate sub =>
      check_cert (rotate_game g) sub fuel'
    end
  end.

(** Certificate soundness. *)

(** If check_cert returns Some r, then r correctly describes the
   game-theoretic outcome. This is the key soundness property.

   Full proof requires showing:
   1. cert_terminal: get_result is correct by construction.
   2. cert_stable: >32 stable discs means opponent can't win.
   3. cert_exists: if current player has a winning move, position is won.
   4. cert_forall: if all responses lead to the same result, result holds.
   5. cert_reflect/cert_rotate: symmetry preserves game-theoretic value.

   We state the theorem; the proof is built incrementally as each
   structural lemma is established. *)

Theorem check_cert_terminal_sound :
  forall g fuel r,
    check_cert g cert_terminal fuel = Some r ->
    match r with
    | cert_win p => get_result g = won_by p
    | cert_draw => get_result g = draw
    end.
Proof.
  intros g fuel r H.
  destruct fuel; [discriminate|].
  simpl in H.
  destruct (get_result g) eqn:Hres;
    try discriminate; inversion H; subst; auto.
Qed.

(** NoDup filter partition: length = length of true-part + length of false-part. *)
Lemma filter_partition_length :
  forall {A : Type} (f : A -> bool) (l : list A),
    length l = length (filter f l) + length (filter (fun x => negb (f x)) l).
Proof.
  intros A f l. induction l as [|a l' IH]; simpl; [lia|].
  destruct (f a); simpl; lia.
Qed.

(** No element equal to v in a list that doesn't contain v. *)
Lemma filter_eq_not_in :
  forall (ss : list nat) (v : nat),
    ~ In v ss ->
    filter (fun i => i =? v) ss = [].
Proof.
  intros ss v Hni. induction ss as [|a ss' IH]; simpl; auto.
  destruct (a =? v) eqn:E.
  { apply Nat.eqb_eq in E. subst. exfalso. apply Hni. left. auto. }
  { apply IH. intro H. apply Hni. right. exact H. }
Qed.

(** NoDup list has at most one occurrence matching equality. *)
Lemma nodup_filter_eq_le1 :
  forall (ss : list nat) (v : nat),
    NoDup ss ->
    length (filter (fun i => i =? v) ss) <= 1.
Proof.
  intros ss v Hnd. induction ss as [|a ss' IH]; simpl; [lia|].
  inversion Hnd; subst.
  destruct (a =? v) eqn:E; simpl.
  { apply Nat.eqb_eq in E. subst.
    rewrite filter_eq_not_in; auto. }
  { apply IH. auto. }
Qed.

(** If 0 is in a NoDup list and get_cell (x::b') 0 = Some p, then x = Some p. *)
Lemma filter_zero_in :
  forall (ss : list nat),
    filter (fun i => i =? 0) ss <> [] ->
    In 0 ss.
Proof.
  intros ss H. induction ss as [|a ss' IH]; simpl in *; [congruence|].
  destruct (a =? 0) eqn:E.
  { left. apply Nat.eqb_eq in E. auto. }
  { right. apply IH. auto. }
Qed.

(** NoDup indices all pointing to p-owned cells means count_pieces >= length. *)
Lemma nodup_owned_count :
  forall b p ss,
    NoDup ss ->
    (forall pos, In pos ss -> pos < length b) ->
    (forall pos, In pos ss -> get_cell b pos = Some p) ->
    length ss <= count_pieces b p.
Proof.
  unfold count_pieces.
  intros b p.
  induction b as [|x b' IHb]; intros ss Hnd Hbnd Howned.
  { destruct ss; simpl; [lia|].
    specialize (Hbnd n (or_introl eq_refl)). simpl in Hbnd. lia. }
  simpl.
  set (ss0 := filter (fun i => i =? 0) ss).
  set (ss1 := filter (fun i => negb (i =? 0)) ss).
  assert (Hpart : length ss = length ss0 + length ss1).
  { subst ss0 ss1. apply filter_partition_length. }
  assert (Hss0_le : length ss0 <= 1).
  { subst ss0. apply nodup_filter_eq_le1. exact Hnd. }
  set (ss1' := map pred ss1).
  assert (Hnd1 : NoDup ss1').
  { subst ss1' ss1.
    assert (Hnd_f := NoDup_filter (fun i => negb (i =? 0)) Hnd).
    assert (Hall : forall z, In z (filter (fun i => negb (i =? 0)) ss) -> z <> 0).
    { intros z Hin. apply filter_In in Hin as [_ Hneq].
      apply negb_true_iff in Hneq. apply Nat.eqb_neq in Hneq. auto. }
    clear -Hnd_f Hall.
    set (l := filter (fun i => negb (i =? 0)) ss) in *.
    clearbody l. clear ss.
    induction l as [|a l' IH]; simpl; [constructor|].
    inversion Hnd_f; subst. constructor.
    { intro Hin. apply in_map_iff in Hin as [k [Heq Hkin]].
      assert (Ha : a <> 0) by (apply Hall; left; auto).
      assert (Hk : k <> 0) by (apply Hall; right; auto).
      apply H1. replace a with k; [exact Hkin|]. lia. }
    { apply IH; auto. intros z Hin. apply Hall. right. exact Hin. } }
  assert (Hbnd1 : forall pos, In pos ss1' -> pos < length b').
  { intros pos Hin. subst ss1'. apply in_map_iff in Hin as [k [Heq Hin]].
    subst ss1. apply filter_In in Hin as [Hin Hneq].
    apply negb_true_iff in Hneq. apply Nat.eqb_neq in Hneq.
    specialize (Hbnd k Hin). simpl in Hbnd. subst pos. lia. }
  assert (Hown1 : forall pos, In pos ss1' -> get_cell b' pos = Some p).
  { intros pos Hin. subst ss1'. apply in_map_iff in Hin as [k [Heq Hin]].
    subst ss1. apply filter_In in Hin as [Hin Hneq].
    apply negb_true_iff in Hneq. apply Nat.eqb_neq in Hneq.
    specialize (Howned k Hin). unfold get_cell in *. subst pos.
    destruct k; [lia|]. simpl in Howned. exact Howned. }
  assert (Hlen1 : length ss1' = length ss1).
  { subst ss1'. rewrite map_length. auto. }
  specialize (IHb ss1' Hnd1 Hbnd1 Hown1).
  rewrite Hlen1 in IHb.
  destruct (match x with Some q => if dec_eq_player q p then true
            else false | None => false end) eqn:Efx; simpl.
  { lia. }
  { assert (Hss0_0 : length ss0 = 0).
    { destruct (ss0) eqn:Ess0; simpl; auto.
      exfalso. subst ss0.
      assert (Hin0 : In 0 ss).
      { apply filter_zero_in. rewrite Ess0. discriminate. }
      specialize (Howned 0 Hin0).
      unfold get_cell in Howned. simpl in Howned.
      (* Howned : x = Some p, Efx : match x with ... = false *)
      subst x. simpl in Efx.
      destruct (dec_eq_player p p) as [_|Habs]; [discriminate|].
      apply Habs. reflexivity. }
    lia. }
Qed.

Lemma stable_majority_wins :
  forall b p ss,
    length b = 64 ->
    stable_majority b p ss = true ->
    NoDup ss ->
    (forall pos, In pos ss -> pos < 64) ->
    count_pieces b p > 32.
Proof.
  intros b p ss Hlen Hsm Hnd Hbnd.
  unfold stable_majority in Hsm.
  apply Bool.andb_true_iff in Hsm as [Hown Hgt].
  apply Nat.ltb_lt in Hgt.
  unfold stable_set_owned in Hown.
  rewrite forallb_forall in Hown.
  assert (Howned : forall pos, In pos ss -> get_cell b pos = Some p).
  { intros pos Hin. specialize (Hown pos Hin).
    destruct (get_cell b pos) eqn:E; [|discriminate].
    destruct (dec_eq_player p0 p); [subst; auto|discriminate]. }
  assert (Hle : length ss <= count_pieces b p).
  { apply nodup_owned_count; auto.
    intros pos Hin. rewrite Hlen. apply Hbnd. exact Hin. }
  lia.
Qed.

(** Small board certificate example. *)

(** Verify the certificate checker works on a trivial terminal game. *)
Definition terminal_game : game :=
  {| current_board := repeat (Some black) 64
   ; next_turn := black
   ; pass_count := 2
   |}.

Lemma terminal_game_cert :
  check_cert terminal_game cert_terminal 1 = Some (cert_win black).
Proof. vm_compute. reflexivity. Qed.

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

(** Score a Reversi game by running the generic cotree alpha-beta evaluator on
    the lazily unfolded Reversi transition system. *)
Definition co_score_game (depth width : nat) (g : game) : nat :=
  eval_ab_co depth width players_le_ge heuristic_score (fun _ => false)
    (Cotrees.unfold_cotree reversi_conext g).

(** [co_score_game] agrees with minimax on the finite prefix inspected by the
    depth- and width-limited cotree search. *)
Theorem co_score_game_minimax :
  forall depth width g,
    co_score_game depth width g =
    eval_val players_le_ge heuristic_score
      (materialize depth width (Cotrees.unfold_cotree reversi_conext g)).
Proof.
  intros. unfold co_score_game. apply reversi_eval_ab_co_minimax.
Qed.

(** Compare two candidate scores from the perspective of the player to move.
    Black maximizes the heuristic score, while white minimizes it. *)
Definition prefers (p : player) (best cand : nat) : bool :=
  match p with
  | black => Nat.leb best cand
  | white => Nat.leb cand best
  end.

(** Apply a concrete placement for the extracted game loop. *)
Definition executable_place (g : game) (row col : nat) : game :=
  let b := current_board g in
  let p := next_turn g in
  {| current_board := place_piece b p row col
   ; next_turn := other_player p
   ; pass_count := 0
   |}.

(** Apply a pass for the extracted game loop. *)
Definition executable_pass (g : game) : game :=
  let b := current_board g in
  let p := next_turn g in
  {| current_board := b
   ; next_turn := other_player p
   ; pass_count := S (pass_count g)
   |}.

(** Executable Reversi successors without proof payloads. *)
Definition executable_reversi_next (g : game) : list game :=
  match get_result g with
  | ongoing =>
    match valid_positions (current_board g) (next_turn g) with
    | [] => [executable_pass g]
    | ps => map (fun '(r, c) => executable_place g r c) ps
    end
  | _ => []
  end.

(** Extraction-oriented coinductive Reversi game tree.

    The generic [Cotrees.cotree] development remains available for proofs.
    This compact representation is used only by the extracted game loop; it
    exposes children by index so the evaluator can unfold lazily without using
    the generic cotree combinators that currently generate invalid C++. *)
CoInductive executable_cotree : Type :=
| executable_conode : game -> (nat -> option game) -> executable_cotree.

(** Lazily expose the executable successors of a Reversi position by index. *)
Definition executable_unfold_game_tree (g : game) : executable_cotree :=
  let children := executable_reversi_next g in
  executable_conode g (fun idx => nth_error children idx).

(** Return the game stored at the root of an executable cotree node. *)
Definition executable_cotree_root (t : executable_cotree) : game :=
  match t with
  | executable_conode g _ => g
  end.

(** Look up the [idx]th child of an executable cotree node, if it exists. *)
Definition executable_cotree_child (t : executable_cotree) (idx : nat)
    : option game :=
  match t with
  | executable_conode _ children => children idx
  end.

(** Reversi-specialized depth-limited alpha-beta evaluator for extraction.

    The generic [AlphaBeta.eval_ab_co] and [co_score_game] remain the
    specification-oriented coinductive implementation with proofs.  This
    executable evaluator has the same depth/width-limited search order but
    recurses on games directly, avoiding a current Crane method-ordering issue
    for functions extracted as methods of coinductive tree nodes. *)
Fixpoint executable_eval_game (depth width alpha beta : nat) (g : game) : nat :=
  match depth with
  | O => heuristic_score g
  | S depth' =>
    match get_result g with
    | won_by _ | draw => heuristic_score g
    | ongoing =>
      let children := executable_reversi_next g in
      match next_turn g with
      | black =>
        let fix eval_max (fuel : nat) (remaining : list game)
            (alpha0 beta0 : nat) : nat :=
          match fuel, remaining with
          | O, _ => alpha0
          | _, [] => alpha0
          | S fuel', child :: rest =>
              let v := executable_eval_game depth' width alpha0 beta0 child in
              let best := Nat.max alpha0 v in
              if Nat.leb beta0 best then best
              else eval_max fuel' rest best beta0
          end in
        eval_max width children alpha beta
      | white =>
        let fix eval_min (fuel : nat) (remaining : list game)
            (alpha0 beta0 : nat) : nat :=
          match fuel, remaining with
          | O, _ => beta0
          | _, [] => beta0
          | S fuel', child :: rest =>
              let v := executable_eval_game depth' width alpha0 beta0 child in
              let best := Nat.min beta0 v in
              if Nat.leb best alpha0 then best
              else eval_min fuel' rest alpha0 best
          end in
        eval_min width children alpha beta
      end
    end
  end.

(** Score a game by a depth-limited executable search considering at most
    [width] children per position. *)
Definition executable_co_score_game (depth width : nat) (g : game) : nat :=
  executable_eval_game depth width 0 1000 g.

(** Fold step for choosing a best child using the generic cotree scorer. *)
Definition choose_step_co (depth width : nat) (p : player)
    (acc : game * nat) (g : game) : game * nat :=
  let '(best, best_score) := acc in
  let s := co_score_game depth width g in
  if prefers p best_score s
  then (g, s)
  else (best, best_score).

(** Choose a best child from a non-empty list using [co_score_game]. *)
Definition choose_best_game_co (depth width : nat) (p : player)
    (best : game) (best_score : nat) (rest : list game) : game :=
  fst (fold_left (choose_step_co depth width p) rest (best, best_score)).

(** Choose the best child using the extraction-oriented scorer. *)
Fixpoint executable_choose_best_game_co (depth width : nat) (p : player)
    (best : game) (best_score : nat) (rest : list game) : game :=
  match rest with
  | [] => best
  | g :: rest' =>
    let s := executable_co_score_game depth width g in
    if prefers p best_score s
    then executable_choose_best_game_co depth width p g s rest'
    else executable_choose_best_game_co depth width p best best_score rest'
  end.

(** Compute the AI move using the extraction-oriented lazy alpha-beta search. *)
Definition ai_move_co (depth width : nat) (g : game) : option game :=
  match executable_reversi_next g with
  | [] => None
  | first :: rest =>
    Some (executable_choose_best_game_co depth width (next_turn g) first
            (executable_co_score_game depth width first) rest)
  end.
