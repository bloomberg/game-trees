(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

Require Import Streams.
Require Import List.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Logic.Decidable.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Require Import ExtLib.Core.RelDec.

Require Import GameTrees.Helpers.
Require Import GameTrees.Relations.
Require Import GameTrees.Trees.

Import ListNotations.
Import SigTNotations.

Definition max2
           {A : Type}
           (R : relation A) `{RelDec A R}
           (x y : A) : A :=
  if rel_dec x y then y else x.

Definition max
           {A : Type}
           (R : relation A) `{RelDec A R}
           (l : list A) : option A :=
  fold_right (fun x o => match o with
                         | None => Some x
                         | Some y => Some (max2 R x y)
                         end) None l.

Definition players (S : Type) :=
  Stream {R : relation S & RelDec R}.

CoInductive Each {A : Type} (P : A -> Prop) : Stream A -> Prop :=
| EachCons : forall x l, P x -> Each P l -> Each P (Cons x l).

CoFixpoint one_player
           {S : Type}
           (R : relation S) `{D : RelDec S R} : players S :=
  Cons (R; D) (one_player R).

CoFixpoint two_players
           {S : Type}
           (R1 : relation S) `{D1 : RelDec S R1}
           (R2 : relation S) `{D2 : RelDec S R2} : players S :=
  Cons (R1; D1)
    (Cons (R2; D2) (two_players R1 R2)).

CoFixpoint three_players
           {S : Type}
           (R1 : relation S) `{D1 : RelDec S R1}
           (R2 : relation S) `{D2 : RelDec S R2}
           (R3 : relation S) `{D3 : RelDec S R3} : players S :=
  Cons (R1; D1)
    (Cons (R2; D2)
       (Cons (R3; D3) (three_players R1 R2 R3))).

Fixpoint eval_tree
         {G S : Type}
         (ps : players S)
         (score : G -> S)
         (t : tree G) : tree (G * S) :=
  match ps with
  | Cons (R; D) ps' =>
    match t with
    | node a f =>
        let f' := map (eval_tree ps' score) f in
        node (a, match max R (map snd (map root f')) with
                 | Some new_score => new_score
                 | None => score a
                 end) f'
    end
  end.
