(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(* Reversi (Othello) with depth-limited alpha-beta AI. *)

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

(* ---------- Game types ---------- *)

Inductive player : Type := black | white.

Definition cell : Type := option player.

(* 8x8 board stored as a list of 64 cells, row-major.
   Index = row * 8 + col, where row and col are 0-based. *)
Definition board : Type := list cell.

Record game : Type :=
  { current_board : board
  ; next_turn : player
  ; pass_count : nat  (* consecutive passes; 2 = game over *)
  }.

(* ---------- Decidable equality ---------- *)

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

(* ---------- Board access ---------- *)

Definition other_player (p : player) : player :=
  match p with black => white | white => black end.

Lemma other_player_ne : forall p, p <> other_player p.
Proof. destruct p; discriminate. Qed.

Lemma other_other_player : forall p, other_player (other_player p) = p.
Proof. destruct p; reflexivity. Qed.

Definition get_cell (b : board) (pos : nat) : cell :=
  nth pos b None.

Fixpoint set_cell (b : board) (pos : nat) (c : cell) : board :=
  match b, pos with
  | [], _ => []
  | _ :: xs, O => c :: xs
  | x :: xs, S n => x :: set_cell xs n c
  end.

Definition pos_of (row col : nat) : nat := row * 8 + col.

Definition in_bounds (row col : nat) : bool :=
  (row <? 8) && (col <? 8).

(* The standard Reversi starting position: center 2x2 with alternating colors.
   Black at (3,4),(4,3); white at (3,3),(4,4). *)
Definition init_board : board :=
  let e := @None player in
  let rows_0_2 := repeat e 24 in
  let row_3 := repeat e 3 ++ [Some white; Some black] ++ repeat e 3 in
  let row_4 := repeat e 3 ++ [Some black; Some white] ++ repeat e 3 in
  let rows_5_7 := repeat e 24 in
  rows_0_2 ++ row_3 ++ row_4 ++ rows_5_7.

Lemma init_board_length : length init_board = 64.
Proof. vm_compute. reflexivity. Qed.

Definition reversi_init : game :=
  {| current_board := init_board
   ; next_turn := black
   ; pass_count := 0
   |}.

(* ---------- Directions and flipping ---------- *)

(* 8 directions as (drow, dcol) pairs, represented as integers via Z. *)
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition direction : Type := (Z * Z)%type.

Definition all_directions : list direction :=
  [(-1,-1); (-1,0); (-1,1);
   ( 0,-1);         ( 0,1);
   ( 1,-1); ( 1,0); ( 1,1)].

(* Walk along a direction from (row, col), collecting positions of
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

(* Scan and return captured positions only if the line terminates
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

(* Actually, let me use a simpler two-pass approach: first find the positions
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

(* A move at (row, col) is valid if it flips at least one opponent piece. *)
Definition is_valid_move (b : board) (p : player) (row col : nat) : bool :=
  in_bounds row col &&
  match get_cell b (pos_of row col) with
  | None => negb (Nat.eqb (length (all_flips b p row col)) 0)
  | Some _ => false
  end.

(* Apply a list of flips to the board. *)
Definition apply_flips (b : board) (p : player) (flips : list nat) : board :=
  fold_left (fun b' pos => set_cell b' pos (Some p)) flips b.

(* Place a piece and flip captured opponents. *)
Definition place_piece (b : board) (p : player) (row col : nat) : board :=
  let pos := pos_of row col in
  let b' := set_cell b pos (Some p) in
  let flips := all_flips b p row col in
  apply_flips b' p flips.

(* ---------- Moves and result ---------- *)

(* A move is a position (row, col) encoded as a single nat = row * 8 + col.
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

(* A move is either placing at (row, col) or passing. *)
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

(* ---------- Game step ---------- *)

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

(* ---------- Well-foundedness ---------- *)

(* Termination measure: empty cells decrease on placements, and
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

(* ---------- set_cell and empty_count properties ---------- *)

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

(* empty_count with set_cell at an empty position: S version for clean nat arithmetic. *)
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

(* empty_count with set_cell at an occupied position. *)
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

(* apply_flips where all flipped positions are occupied preserves empty_count. *)
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

(* Positions returned by find_flips are occupied by the opponent. *)
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

(* Positions in all_flips are occupied on the board. *)
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

(* Positions in find_flips (starting from acc=[]) are in bounds. *)
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

(* For placements: show the measure strictly decreases. *)
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

(* The complete game tree. The fact that this definition type-checks IS
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

(* ---------- Decidable equality for result and move ---------- *)

Lemma dec_eq_result : forall (r1 r2 : result), {r1 = r2} + {r1 <> r2}.
Proof. decide equality. apply dec_eq_player. Defined.

Lemma dec_eq_move : forall (m1 m2 : move), {m1 = m2} + {m1 <> m2}.
Proof. decide equality; apply Nat.eq_dec. Defined.

(* ---------- Board invariant preservation ---------- *)

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

(* ---------- Moves completeness ---------- *)

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

(* ---------- Termination conditions ---------- *)

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

(* ---------- Result exclusivity ---------- *)

(* The result function cannot simultaneously declare both players winners. *)
Theorem at_most_one_winner :
  forall g,
    ~ (get_result g = won_by black /\ get_result g = won_by white).
Proof.
  intros g [H1 H2]. rewrite H1 in H2. discriminate.
Qed.

(* Stronger: get_result is deterministic — it returns a unique result. *)
Theorem result_deterministic :
  forall g r1 r2,
    get_result g = r1 -> get_result g = r2 -> r1 = r2.
Proof.
  intros g r1 r2 H1 H2. congruence.
Qed.

(* ---------- Scoring ---------- *)

(* Black is the maximizer (score 2), white is the minimizer (score 0). *)
Definition score (g : game) : nat :=
  match get_result g with
  | won_by black => 2
  | won_by white => 0
  | draw => 1
  | ongoing => 1
  end.

(* ---------- Correctness of alpha-beta for Reversi ---------- *)

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

(* ---------- Depth-limited tree for execution ---------- *)

Definition reversi_conext (g : game) : Cotrees.colist game :=
  Cotrees.colist_of_list (proj1_sig (reversi_next_intrinsic g)).

Definition search_depth : nat := 5.

Definition ai_subtree (g : game) : tree game :=
  Cotrees.tree_of_cotree search_depth
    (Cotrees.unfold_cotree reversi_conext g).

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

(* ---------- Lazy alpha-beta on cotrees ---------- *)

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

(* ---------- AI ---------- *)

Definition ai_move (g : game) : option game :=
  let t := ai_subtree g in
  let scored :=
    map (fun c => (c, eval_ab players_le_ge score (fun _ => false) c))
        (Trees.children t) in
  match max (comparing gt snd) scored with
  | None => None
  | Some (t', _) => Some (Trees.root t')
  end.

(* ---------- IO ---------- *)

From Stdlib Require Import String.
#[local] Open Scope string_scope.

Require Import SimpleIO.SimpleIO.
Import IO.Notations.

Definition print_cell (c : cell) : IO unit :=
  print_string (match c with
                | None => ". "
                | Some black => "B "
                | Some white => "W "
                end).

Definition print_row (b : board) (r : nat) : IO unit :=
  print_cell (get_cell b (pos_of r 0)) ;;
  print_cell (get_cell b (pos_of r 1)) ;;
  print_cell (get_cell b (pos_of r 2)) ;;
  print_cell (get_cell b (pos_of r 3)) ;;
  print_cell (get_cell b (pos_of r 4)) ;;
  print_cell (get_cell b (pos_of r 5)) ;;
  print_cell (get_cell b (pos_of r 6)) ;;
  print_cell (get_cell b (pos_of r 7)) ;;
  print_newline.

Definition print_board (b : board) : IO unit :=
  print_endline "  0 1 2 3 4 5 6 7" ;;
  print_string "0 " ;; print_row b 0 ;;
  print_string "1 " ;; print_row b 1 ;;
  print_string "2 " ;; print_row b 2 ;;
  print_string "3 " ;; print_row b 3 ;;
  print_string "4 " ;; print_row b 4 ;;
  print_string "5 " ;; print_row b 5 ;;
  print_string "6 " ;; print_row b 6 ;;
  print_string "7 " ;; print_row b 7.

Definition exit_failure {A : Type} : IO A :=
  exit (ExtrOcamlIntConv.int_of_nat 1).

Definition exit_success {A : Type} : IO A :=
  exit (ExtrOcamlIntConv.int_of_nat 0).

Definition parse_digit (s : string) : option nat :=
  match s with
  | "0" => Some 0 | "1" => Some 1 | "2" => Some 2 | "3" => Some 3
  | "4" => Some 4 | "5" => Some 5 | "6" => Some 6 | "7" => Some 7
  | _ => None
  end.

Definition play (g : game) : IO game :=
  print_board (current_board g) ;;
  match get_result g with
  | won_by black => print_endline "Black wins!" ;; exit_success
  | won_by white => print_endline "White wins!" ;; exit_success
  | draw => print_endline "It's a draw!" ;; exit_success
  | ongoing =>
    print_endline "Enter row (0-7):" ;;
    r <- read_line ;;
    print_endline "Enter col (0-7):" ;;
    c <- read_line ;;
    match parse_digit (from_ostring r), parse_digit (from_ostring c) with
    | Some row, Some col =>
      if is_valid_move (current_board g) (next_turn g) row col then
        let g' := apply_move g (place row col) in
        match get_result g' with
        | ongoing =>
          match ai_move g' with
          | Some g'' => IO.ret g''
          | None => IO.ret g'
          end
        | _ => IO.ret g'
        end
      else
        print_endline "Invalid move, try again." ;; IO.ret g
    | _, _ =>
        print_endline "Invalid input, try again." ;; IO.ret g
    end
  end.

Definition unsafe_main : io_unit :=
  IO.unsafe_run (IO.loop play reversi_init).

(* ---------- Extraction ---------- *)

From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlString.
From Stdlib Require Import ExtrOcamlNatInt.

Module Extraction.
Extract Inductive sigT => "( * )" [""].
Extract Inlined Constant negb => "not".
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
Extract Inlined Constant app => "(@)".
Extract Inlined Constant concat => "List.concat".
Extract Inlined Constant map => "List.map".
Extract Inlined Constant filter => "List.filter".
Extract Inlined Constant find => "List.find_opt".
Extract Inlined Constant existsb => "List.exists".
Extract Inlined Constant ltb => "(<)".
Extraction Inline zip_proofs.
Extraction Inline unfold_tree_aux.
Extraction "reversi.ml" unsafe_main.
End Extraction.
