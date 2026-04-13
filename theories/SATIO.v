(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Command-line IO driver for the pure SAT game-tree formalization. *)

From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlString.
Require Import GameTrees.Helpers.
Require Import GameTrees.Trees.
Require Import GameTrees.SAT.
Require Import SimpleIO.SimpleIO.

Import ListNotations.
Import IO.Notations.

#[local] Open Scope string_scope.

(** Print one Boolean assignment. *)
Definition print_assignment (f : name * bool) : IO unit :=
  let '(n, b) := f in
  print_int (ExtrOcamlIntConv.int_of_nat n) ;;
  print_string " = " ;;
  print_string (if b then "true" else "false") ;;
  print_newline.

(** Run an IO action over every element of a list. *)
Fixpoint iter {A : Type} (f : A -> IO unit) (l : list A) : IO unit :=
  match l with
  | [] => IO.ret tt
  | x :: xs => f x ;; iter f xs
  end.

(** Print the result of the SAT search. *)
Definition print_solution (o : option (list (name * bool))) : IO unit :=
  match o with
  | None => print_string "unsat"
  | Some l =>
      print_string "sat" ;;
      print_newline ;;
      iter print_assignment l
  end.

(** Text-mode SAT example entry point. *)
Definition main : IO unit :=
  print_solution (find_sat (f_not (fimplies (f_var 0) (f_var 1)))).

(** Extracted command-line entry point for the SAT example. *)
Definition unsafe_main : io_unit :=
  IO.unsafe_run main.

(** OCaml extraction directives for the text-mode SAT driver. *)
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
Extraction "sat.ml" unsafe_main.
End Extraction.
