(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Command-line IO driver for the pure Reversi formalization. *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlString.
From Stdlib Require Import ExtrOcamlNatInt.
Require Import GameTrees.Reversi.
Require Import GameTrees.Helpers.
Require Import GameTrees.Trees.
Require Import SimpleIO.SimpleIO.

Import IO.Notations.

#[local] Open Scope string_scope.

(** Print one Reversi cell using a compact command-line glyph. *)
Definition print_cell (c : cell) : IO unit :=
  print_string (match c with
                | None => ". "
                | Some black => "B "
                | Some white => "W "
                end).

(** Print row [r] of a board in column order. *)
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

(** Print the full board with row and column labels. *)
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

(** Terminate the command-line driver with a failing status. *)
Definition exit_failure {A : Type} : IO A :=
  exit (ExtrOcamlIntConv.int_of_nat 1).

(** Terminate the command-line driver with a successful status. *)
Definition exit_success {A : Type} : IO A :=
  exit (ExtrOcamlIntConv.int_of_nat 0).

(** Parse a single board-coordinate digit. *)
Definition parse_digit (s : string) : option nat :=
  match s with
  | "0" => Some 0 | "1" => Some 1 | "2" => Some 2 | "3" => Some 3
  | "4" => Some 4 | "5" => Some 5 | "6" => Some 6 | "7" => Some 7
  | _ => None
  end.

(** Run one text-mode interaction step: print the board, accept a user move,
    and, when possible, advance the AI reply. *)
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

(** Extracted command-line entry point for the text-mode Reversi driver. *)
Definition unsafe_main : io_unit :=
  IO.unsafe_run (IO.loop play reversi_init).

(** OCaml extraction directives for the text-mode Reversi driver. *)
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
