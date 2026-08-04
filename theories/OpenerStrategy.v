(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Allcock's opener strategy.

    The standard move opens a three-chain if one is present, otherwise a
    shortest loop if a loop is present, otherwise a shortest chain. Allcock's
    Theorem 1.1 says that opening the shortest loop is optimal in three named
    cases and that the standard move is optimal in every other, the three
    cases being

      (i)   c(G) >= 2 and G is a three-chain together with one or more loops;
      (ii)  c(G) in {0, 1, -1} and G holds a four-loop, and what is left after
            removing one four-loop is not exactly three three-chains;
      (iii) c(G) <= -2 and G holds a four-loop and a three-chain, and what is
            left after removing one of each has size divisible by four and no
            three-chains.

    [allcock_move] is that strategy. It is stated here and checked by
    computation through [allcock_okb], which compares the move it names
    against the value; the theorem itself is not proved. [example_1_2] is
    Allcock's own worked example, machine-checked. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.

Open Scope Z_scope.

(** * Choosing a component *)

Fixpoint pick_min (best : comp * position) (l : list (comp * position))
  : comp * position :=
  match l with
  | [] => best
  | q :: r =>
      pick_min (if (csize (fst q) <? csize (fst best))%nat then q else best) r
  end.

Lemma pick_min_In :
  forall l b, In (pick_min b l) (b :: l).
Proof.
  induction l as [|q l IH]; intros b; simpl; [left; reflexivity|].
  destruct ((csize (fst q) <? csize (fst b))%nat).
  - destruct (IH q) as [H | H]; [right; left; exact H | right; right; exact H].
  - destruct (IH b) as [H | H]; [left; exact H | right; right; exact H].
Qed.

(** The shortest component passing a test, if there is one. *)
Definition shortest_of (f : comp -> bool) (G : position)
  : option (comp * position) :=
  match filter (fun p => f (fst p)) (selections G) with
  | [] => None
  | p :: r => Some (pick_min p r)
  end.

Lemma shortest_of_In :
  forall f G p, shortest_of f G = Some p -> In p (selections G).
Proof.
  intros f G p H; unfold shortest_of in H.
  destruct (filter (fun q => f (fst q)) (selections G)) as [|b l] eqn:E;
    [discriminate|].
  injection H as <-.
  assert (Hin : In (pick_min b l) (b :: l)) by apply pick_min_In.
  rewrite <- E in Hin.
  apply filter_In in Hin; tauto.
Qed.

Definition any_comp (_ : comp) : bool := true.

(** Open a three-chain if there is one, otherwise a shortest loop, otherwise
    a shortest chain. *)
Definition standard_move (G : position) : option (comp * position) :=
  match shortest_of is_3chain_b G with
  | Some p => Some p
  | None =>
      match shortest_of is_loop_b G with
      | Some p => Some p
      | None => shortest_of any_comp G
      end
  end.

Lemma standard_move_In :
  forall G p, standard_move G = Some p -> In p (selections G).
Proof.
  intros G p H; unfold standard_move in H.
  destruct (shortest_of is_3chain_b G) eqn:E3;
    [injection H as <-; apply (shortest_of_In is_3chain_b G); exact E3|].
  destruct (shortest_of is_loop_b G) eqn:EL;
    [injection H as <-; apply (shortest_of_In is_loop_b G); exact EL|].
  apply (shortest_of_In any_comp G); exact H.
Qed.

(** * The three cases *)

Definition count_loops (G : position) : nat := length (filter is_loop_b G).
Definition count4 (G : position) : nat := length (filter is_4loop_b G).

Definition drop_first (f : comp -> bool) (G : position) : position :=
  match filter (fun p => f (fst p)) (selections G) with
  | [] => G
  | p :: _ => snd p
  end.

(** [G] is one three-chain together with one or more loops. *)
Definition three_plus_loops_b (G : position) : bool :=
  ((count3 G =? 1)%nat && (1 <=? count_loops G)%nat &&
   ((count_loops G + 1)%nat =? length G)%nat)%bool.

(** After removing one four-loop, exactly three three-chains remain. *)
Definition rest_is_three_threes_b (G : position) : bool :=
  let H := drop_first is_4loop_b G in
  ((count3 H =? 3)%nat && (length H =? 3)%nat)%bool.

Definition case_i (G : position) : bool :=
  ((2 <=? cval G) && three_plus_loops_b G)%bool.

Definition case_ii (G : position) : bool :=
  ((cval G <=? 1) && (-1 <=? cval G) && (1 <=? count4 G)%nat &&
   negb (rest_is_three_threes_b G))%bool.

Definition case_iii (G : position) : bool :=
  let H := drop_first is_3chain_b (drop_first is_4loop_b G) in
  ((cval G <=? -2) && (1 <=? count4 G)%nat && (1 <=? count3 G)%nat &&
   ((Z.of_nat (size H) mod 4) =? 0) && (count3 H =? 0)%nat)%bool.

(** * The strategy *)

Definition allcock_move (G : position) : option (comp * position) :=
  if (case_i G || case_ii G || case_iii G)%bool
  then shortest_of is_loop_b G
  else standard_move G.

Lemma allcock_move_In :
  forall G p, allcock_move G = Some p -> In p (selections G).
Proof.
  intros G p H; unfold allcock_move in H.
  destruct (case_i G || case_ii G || case_iii G)%bool;
    [apply (shortest_of_In is_loop_b G); exact H
     | apply standard_move_In; exact H].
Qed.

(** Whenever the strategy names a move on a nonempty position, that move is
    legal and, if it attains the value, no opening is better. *)
Theorem allcock_move_optimal_iff :
  forall G p,
    G <> [] -> allcock_move G = Some p ->
    (value G = value_open p <->
     forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p HNil H.
  apply opener_optimal_iff; [exact HNil | apply allcock_move_In; exact H].
Qed.

(** * Checking the strategy on a position *)

Definition allcock_okb (G : position) : bool :=
  match allcock_move G with
  | None => true
  | Some p => Z.eqb (value G) (value_open p)
  end.

Theorem allcock_okb_sound :
  forall G p,
    allcock_okb G = true -> allcock_move G = Some p ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hok Hm.
  assert (HNil : G <> []).
  { intros ->; unfold allcock_move, shortest_of, standard_move in Hm;
      simpl in Hm; discriminate. }
  unfold allcock_okb in Hok; rewrite Hm in Hok.
  apply Z.eqb_eq in Hok.
  split; [exact Hok|].
  apply (allcock_move_optimal_iff G p HNil Hm); exact Hok.
Qed.

(** * Allcock's Lemma 3.1 *)

(** A three-chain and a loop: opening the loop attains the value and opening
    the chain costs exactly two. This is the base the case analysis of
    Theorem 1.1 bottoms out on. *)
Theorem open_loop_optimal_3_loop :
  forall l, (4 <= l)%nat ->
    value_open (Loop l, [Chain 3]) = value [Chain 3; Loop l] /\
    value_open (Chain 3, [Loop l]) = value [Chain 3; Loop l] + 2.
Proof.
  intros l Hl.
  rewrite (value_three_loop l Hl), cval_three_loop.
  unfold value_open; cbn [fst snd].
  rewrite !value_single; cbn [csize].
  split.
  - rewrite controller_gives_up by (cbn [hand]; lia).
    unfold give_up_control; cbn [csize]; lia.
  - rewrite controller_keeps by (cbn [hand]; lia).
    unfold keep_control; cbn [csize hand]; lia.
Qed.

(** So on those positions the loop is strictly the better opening. *)
Corollary loop_strictly_better :
  forall l, (4 <= l)%nat ->
    value_open (Loop l, [Chain 3]) < value_open (Chain 3, [Loop l]).
Proof.
  intros l Hl; destruct (open_loop_optimal_3_loop l Hl) as [H1 H2].
  rewrite H1, H2; lia.
Qed.

(** * Allcock's Example 1.2 *)

(** Five three-chains, a four-loop and an eight-loop. The controlled value is
    [27 - 4*5 - 8*2 + 6 = -3], so case (iii) is the only candidate and it
    fails because what is left has three-chains; the standard move applies
    and opens a three-chain. *)
Definition example_G : position :=
  [Chain 3; Chain 3; Chain 3; Chain 3; Chain 3; Loop 4; Loop 8].

Example example_cval : cval example_G = -3.
Proof. vm_compute; reflexivity. Qed.

Example example_cases :
  (case_i example_G, case_ii example_G, case_iii example_G)
  = (false, false, false).
Proof. vm_compute; reflexivity. Qed.

Example example_opens_three_chain :
  match allcock_move example_G with
  | Some p => fst p = Chain 3
  | None => False
  end.
Proof. vm_compute; reflexivity. Qed.

(** The move the strategy names attains the value, so it is optimal. *)
Example example_1_2 : allcock_okb example_G = true.
Proof. vm_compute; reflexivity. Qed.
