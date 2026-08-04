(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** What the opener strategy actually names.

    [DotsAndBoxes.shortest_of] carries only a membership lemma, which says the
    move it names is legal but not that it is shortest. Every branch of
    Allcock's Theorem 1.1 turns on the length of the component opened, so the
    minimality is needed before any of them can be proved.

    [shortest_loop_is_four] is the first consequence: on a position holding a
    four-loop, the shortest loop is a four-loop, since no loop is shorter. That
    identifies the move named in Allcock's cases (ii) and (iii). *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.

Import ListNotations.

Open Scope Z_scope.

(** * The chosen component is shortest *)

Lemma pick_min_le :
  forall l b q,
    In q (b :: l) -> (csize (fst (pick_min b l)) <= csize (fst q))%nat.
Proof.
  induction l as [|q0 l IH]; intros b q Hin.
  - simpl in Hin; destruct Hin as [<- | []]; simpl; lia.
  - simpl pick_min.
    assert (Hb1 : (csize (fst (if (csize (fst q0) <? csize (fst b))%nat
                               then q0 else b)) <= csize (fst b))%nat).
    { destruct ((csize (fst q0) <? csize (fst b))%nat) eqn:E;
        [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E]; lia. }
    assert (Hb2 : (csize (fst (if (csize (fst q0) <? csize (fst b))%nat
                               then q0 else b)) <= csize (fst q0))%nat).
    { destruct ((csize (fst q0) <? csize (fst b))%nat) eqn:E;
        [apply Nat.ltb_lt in E | apply Nat.ltb_ge in E]; lia. }
    simpl in Hin; destruct Hin as [<- | [<- | Hin]].
    + eapply Nat.le_trans; [apply IH; left; reflexivity | exact Hb1].
    + eapply Nat.le_trans; [apply IH; left; reflexivity | exact Hb2].
    + apply IH; right; exact Hin.
Qed.

Theorem shortest_of_min :
  forall f G p,
    shortest_of f G = Some p ->
    f (fst p) = true /\
    (forall q, In q (selections G) -> f (fst q) = true ->
       (csize (fst p) <= csize (fst q))%nat).
Proof.
  intros f G p H; unfold shortest_of in H.
  destruct (filter (fun q => f (fst q)) (selections G)) as [|b l] eqn:E;
    [discriminate|].
  injection H as <-.
  split.
  - assert (Hin : In (pick_min b l) (b :: l)) by apply pick_min_In.
    rewrite <- E in Hin; apply filter_In in Hin; tauto.
  - intros q Hq Hfq.
    assert (Hin : In q (b :: l))
      by (rewrite <- E; apply filter_In; split; assumption).
    apply pick_min_le; exact Hin.
Qed.

(** The strategy names a move exactly when some component passes the test. *)
Lemma shortest_of_none :
  forall f G, shortest_of f G = None -> forall C, In C G -> f C = false.
Proof.
  intros f G H C HC; unfold shortest_of in H.
  destruct (filter (fun q => f (fst q)) (selections G)) as [|b l] eqn:E;
    [|discriminate].
  destruct (f C) eqn:Ef; [|reflexivity].
  exfalso.
  destruct (In_selections G C HC) as [rest Hsel].
  assert (Hin : In (C, rest) (filter (fun q => f (fst q)) (selections G)))
    by (apply filter_In; split; [exact Hsel | exact Ef]).
  rewrite E in Hin; destruct Hin.
Qed.

(** * Identifying the four-loop *)

Lemma is_4loop_b_eq : forall C, is_4loop_b C = true -> C = Loop 4.
Proof.
  intros [n | n] H; [discriminate|].
  destruct n as [|[|[|[|[|n]]]]]; try discriminate; reflexivity.
Qed.

Lemma count4_pos_In : forall G, (1 <= count4 G)%nat -> In (Loop 4) G.
Proof.
  intros G H; unfold count4 in H.
  destruct (filter is_4loop_b G) as [|C l] eqn:E; simpl in H; [lia|].
  assert (Hin : In C (filter is_4loop_b G)) by (rewrite E; left; reflexivity).
  apply filter_In in Hin; destruct Hin as [HinG Hf].
  rewrite (is_4loop_b_eq C Hf) in HinG; exact HinG.
Qed.

(** A wellformed loop holds at least four boxes, so on a position with a
    four-loop the shortest loop is one. *)
Theorem shortest_loop_is_four :
  forall G p,
    wf G -> (1 <= count4 G)%nat ->
    shortest_of is_loop_b G = Some p -> fst p = Loop 4.
Proof.
  intros G p Hw H4 Hs.
  destruct (shortest_of_min is_loop_b G p Hs) as [Hloop Hmin].
  destruct (In_selections G (Loop 4) (count4_pos_In G H4)) as [rest Hsel].
  assert (Hle : (csize (fst p) <= csize (Loop 4))%nat)
    by (apply (Hmin (Loop 4, rest) Hsel); reflexivity).
  assert (Hinp : In p (selections G))
    by (apply (shortest_of_In is_loop_b); exact Hs).
  assert (Hin : In (fst p) G) by (apply selections_In; exact Hinp).
  unfold wf in Hw; rewrite Forall_forall in Hw; specialize (Hw (fst p) Hin).
  destruct (fst p) as [n | n]; [discriminate|].
  cbn [wf_comp] in Hw; destruct Hw as [Hn4 _].
  cbn [csize] in Hle; assert (Hn : n = 4%nat) by lia; subst n; reflexivity.
Qed.

(** * Identifying the three-chain *)

Lemma is_3chain_b_eq : forall C, is_3chain_b C = true -> C = Chain 3.
Proof.
  intros [n | n] H; [|discriminate].
  destruct n as [|[|[|[|n]]]]; try discriminate; reflexivity.
Qed.

Lemma count3_pos_In : forall G, (1 <= count3 G)%nat -> In (Chain 3) G.
Proof.
  intros G H; unfold count3 in H.
  destruct (filter is_3chain_b G) as [|C l] eqn:E; simpl in H; [lia|].
  assert (Hin : In C (filter is_3chain_b G)) by (rewrite E; left; reflexivity).
  apply filter_In in Hin; destruct Hin as [HinG Hf].
  rewrite (is_3chain_b_eq C Hf) in HinG; exact HinG.
Qed.

(** The standard move opens a three-chain whenever one is present, and it is
    the shortest such, hence a three-chain itself. *)
Theorem standard_move_three :
  forall G p,
    (1 <= count3 G)%nat -> standard_move G = Some p -> fst p = Chain 3.
Proof.
  intros G p H3 Hm; unfold standard_move in Hm.
  destruct (shortest_of is_3chain_b G) as [q|] eqn:E.
  - injection Hm as <-.
    destruct (shortest_of_min is_3chain_b G q E) as [Hq _].
    apply is_3chain_b_eq; exact Hq.
  - exfalso.
    pose proof (shortest_of_none is_3chain_b G E (Chain 3)
                  (count3_pos_In G H3)) as Hc.
    discriminate Hc.
Qed.
