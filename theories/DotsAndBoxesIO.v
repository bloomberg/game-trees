(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** A driver for the Dots and Boxes board.

    The board is drawn as a grid of dots joined by the edges already taken.
    The operator names an edge as a letter and two numbers, [h r c] for the
    horizontal edge from dot [(r, c)], [v r c] for the vertical one. The
    machine replies with the first legal edge.

    The driver is stated for an arbitrary [m] by [n] board and the size is
    read at startup rather than fixed at compile time. Every move the driver
    makes is a member of [db_moves], so [db_play] is only ever applied to a
    legal move. *)

From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlString.
From Stdlib Require Import ExtrOcamlNatInt.

Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxesBoard.
Require Import SimpleIO.SimpleIO.

Import ListNotations.
Import IO.Notations.

#[local] Open Scope string_scope.

(** * Small IO helpers *)

Fixpoint iter_io {A : Type} (f : A -> IO unit) (l : list A) : IO unit :=
  match l with
  | [] => IO.ret tt
  | x :: r => f x ;; iter_io f r
  end.

Definition print_nat (k : nat) : IO unit :=
  print_int (ExtrOcamlIntConv.int_of_nat k).

Definition print_edge (e : edge) : IO unit :=
  match e with
  | EH r c => print_string "h " ;; print_nat r ;; print_string " " ;; print_nat c
  | EV r c => print_string "v " ;; print_nat r ;; print_string " " ;; print_nat c
  end.

Definition exit_success {A : Type} : IO A :=
  exit (ExtrOcamlIntConv.int_of_nat 0).

(** * Parsing *)

Definition digit_of (s : string) : option nat :=
  if String.eqb s "0" then Some 0 else
  if String.eqb s "1" then Some 1 else
  if String.eqb s "2" then Some 2 else
  if String.eqb s "3" then Some 3 else
  if String.eqb s "4" then Some 4 else
  if String.eqb s "5" then Some 5 else
  if String.eqb s "6" then Some 6 else
  if String.eqb s "7" then Some 7 else
  if String.eqb s "8" then Some 8 else
  if String.eqb s "9" then Some 9 else None.

(** Read a move of the form [h r c] or [v r c] from a three-token line. *)
Definition parse_move (str : string) : option edge :=
  match digit_of (substring 2 1 str), digit_of (substring 4 1 str) with
  | Some r, Some c =>
      if String.eqb (substring 0 1 str) "h" then Some (EH r c)
      else if String.eqb (substring 0 1 str) "v" then Some (EV r c)
      else None
  | _, _ => None
  end.

(** Read a board size of the form [r c] from a two-token line. *)
Definition parse_dims (str : string) : option (nat * nat) :=
  match digit_of (substring 0 1 str), digit_of (substring 2 1 str) with
  | Some r, Some c => Some (r, c)
  | _, _ => None
  end.

(** * The driver, for an arbitrary board *)

Section Driver.

Variables m n : nat.

Definition drawnb (s : st) (e : edge) : bool := emem e (laid s).

(** The row of dots at height [r], with the horizontal edges between them. *)
Definition print_dot_row (s : st) (r : nat) : IO unit :=
  iter_io (fun c => print_string "." ;;
                    print_string (if drawnb s (EH r c) then "-" else " "))
          (seq 0 n) ;;
  print_string "." ;; print_newline.

(** The gap below the dots at height [r], holding the vertical edges. *)
Definition print_gap_row (s : st) (r : nat) : IO unit :=
  iter_io (fun c => print_string (if drawnb s (EV r c) then "|" else " ") ;;
                    print_string " ")
          (seq 0 (S n)) ;;
  print_newline.

Definition print_board (s : st) : IO unit :=
  iter_io (fun r => print_dot_row s r ;; print_gap_row s r) (seq 0 m) ;;
  print_dot_row s m.

Definition print_state (s : st) : IO unit :=
  print_board s ;;
  print_string "you " ;; print_nat (s1 s) ;;
  print_string "   machine " ;; print_nat (s2 s) ;;
  print_newline.

Definition edge_in_moves (s : st) (e : edge) : bool :=
  emem e (db_moves m n s).

(** The machine takes the first open edge. *)
Definition machine_move (s : st) : option edge :=
  match db_moves m n s with [] => None | e :: _ => Some e end.

Lemma machine_move_legal :
  forall s e, machine_move s = Some e -> In e (db_moves m n s).
Proof.
  intros s e H; unfold machine_move in H.
  destruct (db_moves m n s) as [|f r] eqn:E; [discriminate|].
  injection H as <-; left; reflexivity.
Qed.

(** The operator's move is only played when it is open. *)
Lemma edge_in_moves_legal :
  forall s e, edge_in_moves s e = true -> In e (db_moves m n s).
Proof.
  intros s e H; unfold edge_in_moves in H; apply emem_true_iff; exact H.
Qed.

Definition finished (s : st) : bool :=
  match db_moves m n s with [] => true | _ :: _ => false end.

Lemma finished_complete : forall s, finished s = true -> complete m n s.
Proof.
  intros s H; unfold finished, complete in *.
  destruct (db_moves m n s); [reflexivity | discriminate].
Qed.

Definition report (s : st) : IO unit :=
  if Nat.ltb (s2 s) (s1 s) then print_endline "You won."
  else if Nat.ltb (s1 s) (s2 s) then print_endline "You lost."
  else print_endline "A draw.".

Definition step (s : st) : IO st :=
  print_state s ;;
  if finished s then report s ;; exit_success
  else
    print_endline "Your edge:" ;;
    line <- read_line ;;
    match parse_move (from_ostring line) with
    | None => print_endline "Unreadable." ;; IO.ret s
    | Some e =>
        if edge_in_moves s e
        then
          let s' := db_play m n s e in
          match machine_move s' with
          | None => IO.ret s'
          | Some f => print_string "machine: " ;; print_edge f ;; print_newline ;;
                      IO.ret (db_play m n s' f)
          end
        else print_endline "Not an open edge." ;; IO.ret s
    end.

Definition play_board : IO unit := IO.loop step init.

End Driver.

(** * Entry point *)

(** The size is read from the first line; anything unreadable falls back to
    the two by two board. *)
Definition main : IO unit :=
  print_endline "Board size (rows cols), e.g. 3 3:" ;;
  line <- read_line ;;
  match parse_dims (from_ostring line) with
  | Some (r, c) => play_board r c
  | None => play_board 2 2
  end.

Definition unsafe_main : io_unit := IO.unsafe_run main.

Module Extraction.
Extract Inductive sigT => "( * )" [""].
Extract Inlined Constant negb => "not".
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
Extract Inlined Constant app => "(@)".
Extract Inlined Constant concat => "List.concat".
Extract Inlined Constant map => "List.map".
Extract Inlined Constant filter => "List.filter".
Extraction "dotsandboxes.ml" unsafe_main.
End Extraction.
