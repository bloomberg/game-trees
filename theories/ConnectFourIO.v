(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Command-line IO driver for the pure Connect Four formalization. *)

From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlString.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOCamlInt63.
From Stdlib Require Import ExtrOCamlPArray.
Require Import GameTrees.Helpers.
Require Import GameTrees.Trees.
Require Import GameTrees.ConnectFour.
Require Import SimpleIO.SimpleIO.

Import IO.Notations.

#[local] Open Scope string_scope.

(** Print one Connect Four cell using a compact command-line glyph. *)
Definition print_cell (c : option player) : IO unit :=
  print_string (match c with
                | None => ". "
                | Some red => "R "
                | Some yellow => "Y "
                end).

(** Print row [r] of a Connect Four board. *)
Definition print_row (b : board) (r : nat) : IO unit :=
  print_cell (get_cell b 0 r) ;;
  print_cell (get_cell b 1 r) ;;
  print_cell (get_cell b 2 r) ;;
  print_cell (get_cell b 3 r) ;;
  print_cell (get_cell b 4 r) ;;
  print_cell (get_cell b 5 r) ;;
  print_cell (get_cell b 6 r) ;;
  print_newline.

(** Print the full Connect Four board from top row to bottom row. *)
Definition print_board (b : board) : IO unit :=
  print_row b 5 ;;
  print_row b 4 ;;
  print_row b 3 ;;
  print_row b 2 ;;
  print_row b 1 ;;
  print_row b 0 ;;
  print_endline "1 2 3 4 5 6 7".

(** Terminate the command-line driver with a failing status. *)
Definition exit_failure {A : Type} : IO A :=
  exit (ExtrOcamlIntConv.int_of_nat 1).

(** Terminate the command-line driver with a successful status. *)
Definition exit_success {A : Type} : IO A :=
  exit (ExtrOcamlIntConv.int_of_nat 0).

(** Run one text-mode interaction step: accept a user column and, when possible,
    advance the AI reply. *)
Definition play (g : game) : IO game :=
  print_board (current_board g) ;;
  match get_result g with
  | won_by red => print_endline "Red wins!" ;; exit_success
  | won_by yellow => print_endline "Yellow wins!" ;; exit_success
  | draw => print_endline "It's a draw!" ;; exit_success
  | ongoing =>
    print_endline "Enter column (1-7):" ;;
    m <- read_line ;;
    let m' : option move :=
      match from_ostring m with
      | "1" => Some col0 | "2" => Some col1 | "3" => Some col2
      | "4" => Some col3 | "5" => Some col4 | "6" => Some col5
      | "7" => Some col6 | _ => None
      end in
    match m' with
    | None =>
        print_endline "Invalid input, try again." ;; IO.ret g
    | Some mv =>
      if Nat.ltb (List.length (column_of_move mv (current_board g))) 6 then
        let g' := apply_move g mv in
        match get_result g' with
        | ongoing =>
          match ai_move g' with
          | Some g'' => IO.ret g''
          | None => IO.ret g'
          end
        | _ => IO.ret g'
        end
      else
        print_endline "Column full, try again." ;; IO.ret g
    end
  end.

(** Extracted command-line entry point for Connect Four. *)
Definition unsafe_main : io_unit :=
  IO.unsafe_run (IO.loop play c4_init).

(** OCaml extraction directives for the text-mode Connect Four driver. *)
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
Extraction Inline memo.
Extraction "connectfour.ml" unsafe_main.
End Extraction.
