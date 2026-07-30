(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Command-line IO driver for the pure Hex formalization. *)

From Stdlib Require Import String.
From Stdlib Require Import List.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlString.
From Stdlib Require Import ExtrOcamlNatInt.
Require Import GameTrees.Helpers.
Require Import GameTrees.Trees.
Require Import GameTrees.Hex.
Require Import SimpleIO.SimpleIO.

Import ListNotations.
Import IO.Notations.

#[local] Open Scope string_scope.

(** Board size of the command-line game. *)
Definition N : nat := 5.

(** Search depth and width of the AI's lazy alpha-beta evaluation. *)
Definition ai_depth : nat := 2.
Definition ai_width : nat := N * N.

(** Print one Hex cell using a compact command-line glyph. *)
Definition print_cell (c : option player) : IO unit :=
  print_string (match c with
                | None => ". "
                | Some red => "R "
                | Some blue => "B "
                end).

Fixpoint print_cells (b : board) (r : nat) (cols : list nat) : IO unit :=
  match cols with
  | [] => print_newline
  | c :: rest => print_cell (get_cell N b (r, c)) ;; print_cells b r rest
  end.

Fixpoint print_spaces (k : nat) : IO unit :=
  match k with
  | O => IO.ret tt
  | S k' => print_string " " ;; print_spaces k'
  end.

(** Print row [r] with a hex-style indent. *)
Definition print_row (b : board) (r : nat) : IO unit :=
  print_spaces r ;;
  print_int (ExtrOcamlIntConv.int_of_nat r) ;;
  print_string " " ;;
  print_cells b r (seq 0 N).

Fixpoint print_rows (b : board) (rows : list nat) : IO unit :=
  match rows with
  | [] => IO.ret tt
  | r :: rest => print_row b r ;; print_rows b rest
  end.

(** Print the board; red connects top to bottom, blue left to right. *)
Definition print_board (b : board) : IO unit :=
  print_endline "  0 1 2 3 4" ;;
  print_rows b (seq 0 N).

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
  | "8" => Some 8 | "9" => Some 9
  | _ => None
  end.

(** The board size is positive, as every Hex theorem requires. *)
Lemma N_pos : 1 <= N.
Proof. unfold N; repeat constructor. Qed.

(** One interaction step: the human plays red, the AI answers as blue.

    The [draw] branch is discharged rather than handled: [get_result_not_draw]
    refutes it, so the case carries no code. *)
Definition play (g : game) : IO game :=
  print_board (brd g) ;;
  match get_result N g as r return get_result N g = r -> IO game with
  | won_by red => fun _ => print_endline "Red wins!" ;; exit_success
  | won_by blue => fun _ => print_endline "Blue wins!" ;; exit_success
  | draw => fun Hd => match get_result_not_draw N N_pos g Hd with end
  | ongoing => fun _ =>
    print_endline "Enter row (0-4):" ;;
    r <- read_line ;;
    print_endline "Enter col (0-4):" ;;
    c <- read_line ;;
    match parse_digit (from_ostring r), parse_digit (from_ostring c) with
    | Some row, Some col =>
      if andb (andb (Nat.ltb row N) (Nat.ltb col N))
              (emptyb N (brd g) (row, col)) then
        let g' := apply_move N g (row, col) in
        match get_result N g' with
        | ongoing =>
          match ai_move_co N ai_depth ai_width g' with
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
  end eq_refl.

(** Extracted command-line entry point for the text-mode Hex driver. *)
Definition unsafe_main : io_unit :=
  IO.unsafe_run (IO.loop play (hex_init N)).

(** OCaml extraction directives for the text-mode Hex driver. *)
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
Extraction "hex.ml" unsafe_main.
End Extraction.
