(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

Require Import Corelib.Classes.RelationClasses.
Require Import Corelib.Program.Basics.
From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Psatz.
From Stdlib Require Import Program.Equality.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.Relations.
Require Import GameTrees.Trees.
Require GameTrees.Cotrees.
Require Import GameTrees.Eval.

Inductive player : Type := x | o.

Definition cell : Type := option player.

Inductive board : Type :=
| mkbd : cell -> cell -> cell ->
         cell -> cell -> cell ->
         cell -> cell -> cell ->
         board.

Record game : Type :=
  { current_board : board
  ; next_turn : player
  }.

Lemma dec_eq_player : forall (p1 p2 : player), {p1 = p2} + {p1 <> p2}.
Proof. decide equality. Defined.

Lemma dec_eq_cell : forall (c1 c2 : cell), {c1 = c2} + {c1 <> c2}.
Proof. decide equality. eapply dec_eq_player. Defined.

Lemma dec_eq_board : forall (b1 b2 : board), {b1 = b2} + {b1 <> b2}.
Proof. decide equality. all: eapply dec_eq_cell. Defined.

Lemma dec_eq_game : forall (g1 g2 : game), {g1 = g2} + {g1 <> g2}.
Proof. decide equality. eapply dec_eq_player. eapply dec_eq_board. Defined.

Inductive result : Type :=
| won_by : player -> result
| draw : result
| ongoing : result.

Definition get_result (g : game) : result :=
  match current_board g with
  | mkbd (Some x) (Some x) (Some x) _ _ _ _ _ _ => won_by x
  | mkbd _ _ _ (Some x) (Some x) (Some x) _ _ _ => won_by x
  | mkbd _ _ _ _ _ _ (Some x) (Some x) (Some x) => won_by x
  | mkbd (Some x) _ _ (Some x) _ _ (Some x) _ _ => won_by x
  | mkbd _ (Some x) _ _ (Some x) _ _ (Some x) _ => won_by x
  | mkbd _ _ (Some x) _ _ (Some x) _ _ (Some x) => won_by x
  | mkbd (Some x) _ _ _ (Some x) _ _ _ (Some x) => won_by x
  | mkbd _ _ (Some x) _ (Some x) _ (Some x) _ _ => won_by x
  | mkbd (Some o) (Some o) (Some o) _ _ _ _ _ _ => won_by o
  | mkbd _ _ _ (Some o) (Some o) (Some o) _ _ _ => won_by o
  | mkbd _ _ _ _ _ _ (Some o) (Some o) (Some o) => won_by o
  | mkbd (Some o) _ _ (Some o) _ _ (Some o) _ _ => won_by o
  | mkbd _ (Some o) _ _ (Some o) _ _ (Some o) _ => won_by o
  | mkbd _ _ (Some o) _ _ (Some o) _ _ (Some o) => won_by o
  | mkbd (Some o) _ _ _ (Some o) _ _ _ (Some o) => won_by o
  | mkbd _ _ (Some o) _ (Some o) _ (Some o) _ _ => won_by o
  | mkbd (Some _) (Some _) (Some _) (Some _) (Some _) (Some _) (Some _) (Some _) (Some _) => draw
  | _ => ongoing
  end.

Definition ttt_init : game :=
  {| current_board := (mkbd None None None None None None None None None)
   ; next_turn := x
   |}.

Inductive move : Type :=
| move_a : move
| move_b : move
| move_c : move
| move_d : move
| move_e : move
| move_f : move
| move_g : move
| move_h : move
| move_i : move.

Inductive valid_move : game -> move -> Prop :=
| valid_move_a : forall {b c d e f g h i t},
    valid_move {| current_board := mkbd None b c d e f g h i ; next_turn := t |} move_a
| valid_move_b : forall {a c d e f g h i t},
    valid_move {| current_board := mkbd a None c d e f g h i ; next_turn := t |} move_b
| valid_move_c : forall {a b d e f g h i t},
    valid_move {| current_board := mkbd a b None d e f g h i ; next_turn := t |} move_c
| valid_move_d : forall {a b c e f g h i t},
    valid_move {| current_board := mkbd a b c None e f g h i ; next_turn := t |} move_d
| valid_move_e : forall {a b c d f g h i t},
    valid_move {| current_board := mkbd a b c d None f g h i ; next_turn := t |} move_e
| valid_move_f : forall {a b c d e g h i t},
    valid_move {| current_board := mkbd a b c d e None g h i ; next_turn := t |} move_f
| valid_move_g : forall {a b c d e f h i t},
    valid_move {| current_board := mkbd a b c d e f None h i ; next_turn := t |} move_g
| valid_move_h : forall {a b c d e f g i t},
    valid_move {| current_board := mkbd a b c d e f g None i ; next_turn := t |} move_h
| valid_move_i : forall {a b c d e f g h t},
    valid_move {| current_board := mkbd a b c d e f g h None ; next_turn := t |} move_i.

Arguments valid_move_a {_ _ _ _ _ _ _ _ _}.
Arguments valid_move_b {_ _ _ _ _ _ _ _ _}.
Arguments valid_move_c {_ _ _ _ _ _ _ _ _}.
Arguments valid_move_d {_ _ _ _ _ _ _ _ _}.
Arguments valid_move_e {_ _ _ _ _ _ _ _ _}.
Arguments valid_move_f {_ _ _ _ _ _ _ _ _}.
Arguments valid_move_g {_ _ _ _ _ _ _ _ _}.
Arguments valid_move_h {_ _ _ _ _ _ _ _ _}.
Arguments valid_move_i {_ _ _ _ _ _ _ _ _}.

Definition moves (g : game) : list move :=
  match get_result g with
  | won_by _ | draw => []
  | ongoing =>
    let b : board := current_board g in
    let boards : list (list move) :=
      [ match b with mkbd None _ _ _ _ _ _ _ _ => [move_a] | _ => [] end
      ; match b with mkbd _ None _ _ _ _ _ _ _ => [move_b] | _ => [] end
      ; match b with mkbd _ _ None _ _ _ _ _ _ => [move_c] | _ => [] end
      ; match b with mkbd _ _ _ None _ _ _ _ _ => [move_d] | _ => [] end
      ; match b with mkbd _ _ _ _ None _ _ _ _ => [move_e] | _ => [] end
      ; match b with mkbd _ _ _ _ _ None _ _ _ => [move_f] | _ => [] end
      ; match b with mkbd _ _ _ _ _ _ None _ _ => [move_g] | _ => [] end
      ; match b with mkbd _ _ _ _ _ _ _ None _ => [move_h] | _ => [] end
      ; match b with mkbd _ _ _ _ _ _ _ _ None => [move_i] | _ => [] end
      ] in concat boards
  end.

Definition valid_moves (g : game) : Forall (valid_move g) (moves g).
  destruct g as [[a b c d e f g h i] turn].
  unfold moves.
  destruct (get_result {| current_board := mkbd a b c d e f g h i ; next_turn := turn |}); auto; simpl.
  repeat (rewrite -> Forall_app); repeat split; auto;
  match goal with
  | |- context G [match ?m with Some _ => _ | None => _ end]  => destruct m; repeat constructor
  end.
Qed.

Definition apply_move (g : game) (m : move) : game :=
  let turn := next_turn g in
  match current_board g with
  | mkbd a b c d e f g h i =>
      {| current_board :=
         match m with
         | move_a => mkbd (Some turn) b c d e f g h i
         | move_b => mkbd a (Some turn) c d e f g h i
         | move_c => mkbd a b (Some turn) d e f g h i
         | move_d => mkbd a b c (Some turn) e f g h i
         | move_e => mkbd a b c d (Some turn) f g h i
         | move_f => mkbd a b c d e (Some turn) g h i
         | move_g => mkbd a b c d e f (Some turn) h i
         | move_h => mkbd a b c d e f g (Some turn) i
         | move_i => mkbd a b c d e f g h (Some turn)
         end
       ; next_turn := match turn with x => o | o => x end
       |}
  end.

Inductive game_step : game -> game -> Prop :=
| gstep : forall g m, get_result g = ongoing -> valid_move g m -> game_step g (apply_move g m).

Definition ttt_next (g : game) : list game :=
  match get_result g with
  | ongoing => map (apply_move g) (moves g)
  | _ => []
  end.

Definition empty_cell {A : Type} (o : option A) : nat :=
  match o with
  | Some _ => 0
  | None => 1
  end.

Definition empty_cells (g : game) : nat :=
  match current_board g with
  | mkbd a b c d e f g h i =>
      empty_cell a +
      empty_cell b +
      empty_cell c +
      empty_cell d +
      empty_cell e +
      empty_cell f +
      empty_cell g +
      empty_cell h +
      empty_cell i
  end.

Definition list_bind
           {A B : Type} (ys : list A) (f : A -> list B) : list B :=
  concat (map f ys).

Definition all_cells : list (option player) := [None; Some x; Some o].
Definition all_turns : list player := [x; o].
Definition all_games : list game :=
  map (fun '(turn, (a, (b, (c, (d, (e, (f, (g, (h, i))))))))) =>
         {| current_board := mkbd a b c d e f g h i ; next_turn := turn |})
    (list_prod all_turns
      (list_prod all_cells (list_prod all_cells (list_prod all_cells
        (list_prod all_cells (list_prod all_cells (list_prod all_cells
          (list_prod all_cells (list_prod all_cells all_cells))))))))).

Lemma all_cells_are_in_all_cells : forall (c : option player), In c all_cells.
Proof.
  unfold all_cells.
  destruct c; intuition (auto with *).
  destruct p; intuition (auto with *).
Qed.

Lemma all_turns_are_in_all_turns : forall (p : player), In p all_turns.
Proof.
  unfold all_turns.
  destruct p; intuition (auto with *).
Qed.

(* Includes invalid games too, but we don't care at the moment *)
Lemma all_games_are_in_all_games : forall (g : game), In g all_games.
Proof.
  intros [[a b c d e f g h i] turn].
  unfold all_games.
  change {| current_board := mkbd a b c d e f g h i ; next_turn := turn |}
    with
    ((fun '(turn, (a, (b, (c, (d, (e, (f, (g, (h, i))))))))) =>
        {| current_board := mkbd a b c d e f g h i ; next_turn := turn |})
     (turn, (a, (b, (c, (d, (e, (f, (g, (h, i)))))))))).
  eapply in_map.
  repeat eapply in_prod.
  eapply all_turns_are_in_all_turns.
  all: eapply all_cells_are_in_all_cells.
Qed.

(* The next moves function,
   where the next moves are guaranteed by [game_step] to be legal moves. *)
Lemma ttt_next_intrinsic :
  forall g1 : game,
    {l : list game | Forall (game_step g1) l}.
Proof.
  intros g1.
  exists (ttt_next g1).
  unfold ttt_next.
  apply Forall_map.
  destruct (get_result g1) eqn:eq; try constructor.
  unfold flip.
  pose proof (H := valid_moves g1).
  induction (moves g1) as [|mv mvs IH]; constructor; auto;
  inversion H; subst; auto.
  constructor; auto.
Defined.

(* A relation on game states, where [g1] is a later board in the game then [g2]. *)
Definition later (g1 g2 : game) : Prop :=
  empty_cells g1 < empty_cells g2.

Instance WF_later : WellFounded later.
Proof.
  unfold later.
  apply Relations.wf_inverse_image, Nat.lt_wf_0.
Defined.

Lemma less_empty_cells_after_apply_move :
  forall (g : game) (m : move),
    valid_move g m ->
    later (apply_move g m) g.
Proof.
  intros [board turn] m v.
  unfold apply_move, later, empty_cells.
  destruct board as [a b c d e f g h i]; simpl.
  dependent induction v; simpl; lia.
Qed.

Instance WF_flip_game_step : WellFounded (flip game_step).
Proof.
  eapply WF_subrelation, WF_later.
  intros g2 g1; inversion 1.
  apply less_empty_cells_after_apply_move; auto.
Defined.

Definition complete_tree : tree game :=
  unfold_tree (flip game_step) ttt_next_intrinsic ttt_init.

(* True theorem but it takes too long (about a minute on my machine) to run! *)
Definition ttt_conext (g : game) : Cotrees.colist game :=
  Cotrees.colist_of_list (ttt_next g).

Theorem ttt_is_finite : Cotrees.finite_game ttt_conext ttt_init.
Proof.
  exists 10; vm_compute; reflexivity.
Defined.

(* Alternatively, you can define [complete_tree] through the coinductive unfold function. *)
Definition complete_tree_again : tree game :=
  Cotrees.tree_of_cotree ttt_is_finite.1 (Cotrees.unfold_cotree ttt_conext ttt_init).

From Stdlib Require Import String.
#[local] Open Scope string_scope.

Require Import SimpleIO.SimpleIO.
Require Import ExtLib.Core.RelDec.
Import IO.Notations.

(* Here we have a tic-tac-toe implementation with an unbeatable AI,
   to showcase our game tree generation
   and minimax algorithm implementation. *)

Definition score (g : game) : nat :=
  match get_result g with
  | won_by x => 2
  | won_by o => 0
  | draw => 1
  | ongoing => 1
  end.

Definition scored_tree : tree (game * nat) :=
  eval_tree (two_players lt gt) score complete_tree.

Definition print_cell (x : cell) : IO unit :=
  print_string (match x with | None => "." | Some x => "X" | Some o => "O" end).

Definition print_game (g : game) : IO unit :=
  let '(mkbd a b c d e f g h i) := current_board g in
  print_cell a ;;
  print_cell b ;;
  print_cell c ;;
  print_newline ;;
  print_cell d ;;
  print_cell e ;;
  print_cell f ;;
  print_newline ;;
  print_cell g ;;
  print_cell h ;;
  print_cell i ;;
  print_newline.

Definition exit_failure {A : Type} : IO A :=
  exit (ExtrOcamlIntConv.int_of_nat 1).

Definition exit_success {A : Type} : IO A :=
  exit (ExtrOcamlIntConv.int_of_nat 0).

Definition play (t : tree (game * nat)) : IO (tree (game * nat)) :=
  let '(g, _) := root t in
  print_game g ;;
  match get_result g with
  | won_by x => print_endline "You won the game!" ;; exit_success
  | won_by o => print_endline "You lost the game!" ;; exit_success
  | draw => print_endline "It's a draw!" ;; exit_success
  | ongoing =>
    print_endline "Enter your move (1-9):" ;;
    m <- read_line ;;
    let m' : option move :=
      match from_ostring m with
      | "1" => Some move_a | "2" => Some move_b | "3" => Some move_c
      | "4" => Some move_d | "5" => Some move_e | "6" => Some move_f
      | "7" => Some move_g | "8" => Some move_h | "9" => Some move_i
      | _ => None
      end in
    match m' with
    | None =>
        print_endline "Invalid input, try again." ;; IO.ret t
    | Some m'' =>
      let g' := apply_move g m'' in
      match List.find
              (fun t' => if dec_eq_game (fst (root t')) g' then true else false)
              (children t) with
      | None =>
          print_endline "Invalid move, try again." ;; IO.ret t
      | Some t' =>
        match max (comparing gt (fun t => snd (root t))) (children t') with
        | None => IO.ret t'
        | Some t'' => IO.ret t''
        end
      end
    end
  end.

Definition unsafe_main : io_unit :=
  IO.unsafe_run (IO.loop play scored_tree).

From Stdlib Require Import ExtrOcamlBasic.
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
Extract Inlined Constant find => "List.find_opt".
Extract Inlined Constant ltb => "(<)".
Extraction Inline zip_proofs.
Extraction Inline unfold_tree_aux.
Extraction "tictactoe.ml" unsafe_main.
End Extraction.
