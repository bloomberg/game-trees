(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Command-line IO driver for the pure tic-tac-toe formalization. *)

From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlString.
From Stdlib Require Import ExtrOcamlNatInt.
Require Import ExtLib.Core.RelDec.
Require Import GameTrees.Helpers.
Require Import GameTrees.Relations.
Require Import GameTrees.Trees.
Require Import GameTrees.Eval.
Require Import GameTrees.AlphaBeta.
Require Import GameTrees.TicTacToe.
Require Import SimpleIO.SimpleIO.

Import IO.Notations.

#[local] Open Scope string_scope.

(** Print one tic-tac-toe cell using a compact command-line glyph. *)
Definition print_cell (x : cell) : IO unit :=
  print_string (match x with | None => "." | Some x => "X" | Some o => "O" end).

(** Print the current tic-tac-toe board as three text rows. *)
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

(** Terminate the command-line driver with a failing status. *)
Definition exit_failure {A : Type} : IO A :=
  exit (ExtrOcamlIntConv.int_of_nat 1).

(** Terminate the command-line driver with a successful status. *)
Definition exit_success {A : Type} : IO A :=
  exit (ExtrOcamlIntConv.int_of_nat 0).

(** Run one text-mode interaction step and let the AI answer using alpha-beta
    scores for the current subtree's children. *)
Definition play (t : tree game) : IO (tree game) :=
  let g := root t in
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
              (fun t' => if dec_eq_game (root t') g' then true else false)
              (children t) with
      | None =>
          print_endline "Invalid move, try again." ;; IO.ret t
      | Some t' =>
        let scored := map (fun c => (c, eval_ab players_le_ge score
                                          (fun _ => false) c))
                          (children t') in
        match max (comparing gt snd) scored with
        | None => IO.ret t'
        | Some (t'', _) => IO.ret t''
        end
      end
    end
  end.

(** Extracted command-line entry point for tic-tac-toe. *)
Definition unsafe_main : io_unit :=
  IO.unsafe_run (IO.loop play complete_tree).

(** OCaml extraction directives for the text-mode tic-tac-toe driver. *)
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
