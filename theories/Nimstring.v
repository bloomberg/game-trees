(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Nimstring on a loony position.

    Nimstring is Strings and Coins under normal play: the player who cannot
    move loses, and completing a coin still grants another move. On a loony
    position, where every component is a long chain or a loop, a turn consumes
    exactly one component, so the game tree is the tree of component removals
    and the position is an impartial game in the sense of [GameTrees.Grundy].

    [nimstring_grundy] computes its Grundy value: it is the parity of the
    number of components. So the opener of a loony Nimstring position wins
    exactly when the component count is odd, which is the same parity that
    [DotsAndBoxesBoard.long_chain_identity] tracks through the doublecrosses. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.Trees.
Require Import GameTrees.Grundy.
Require Import GameTrees.DotsAndBoxes.

(** * The Nimstring tree of a loony position *)

(** One turn removes one component. The fuel bounds the number of turns, and
    a turn always removes a component, so the position's own length is
    enough. *)
Fixpoint nstree (fuel : nat) (G : position) : Grundy.game :=
  match fuel with
  | O => node tt []
  | S f => node tt (map (fun p => nstree f (snd p)) (selections G))
  end.

Lemma nstree_nil : forall fuel, nstree fuel [] = node tt [].
Proof. intros [|f]; reflexivity. Qed.

(** * Everything a turn can leave has the same Grundy value *)

Lemma mex_all_zero :
  forall l, l <> [] -> (forall x, In x l -> x = 0%nat) -> mex l = 1%nat.
Proof.
  intros l Hne Hall; apply mex_unique.
  - intros Hin; pose proof (Hall 1%nat Hin); discriminate.
  - intros x Hx.
    assert (Hx0 : x = 0%nat) by lia; subst x.
    destruct l as [|a l]; [contradiction|].
    rewrite <- (Hall a (or_introl eq_refl)); left; reflexivity.
Qed.

Lemma mex_all_one :
  forall l, (forall x, In x l -> x = 1%nat) -> mex l = 0%nat.
Proof.
  intros l Hall; apply mex_unique.
  - intros Hin; pose proof (Hall 0%nat Hin); discriminate.
  - intros x Hx; lia.
Qed.

(** * The Grundy value *)

Definition parity (k : nat) : nat := if Nat.even k then 0 else 1.

Lemma parity_succ : forall k, parity (S k) = (if Nat.even k then 1 else 0)%nat.
Proof.
  intros k; unfold parity; rewrite Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even k); reflexivity.
Qed.

(** The value of a loony Nimstring position is the parity of its component
    count. *)
Theorem nimstring_grundy :
  forall fuel G,
    (length G <= fuel)%nat -> grundy (nstree fuel G) = parity (length G).
Proof.
  induction fuel as [|f IH]; intros G Hf.
  - assert (HG : G = []) by (destruct G; simpl in Hf; [reflexivity | lia]).
    subst G; reflexivity.
  - simpl nstree; rewrite grundy_eq, map_map.
    destruct G as [|C G].
    + simpl; reflexivity.
    + simpl length in Hf.
      assert (Hchild : forall x,
        In x (map (fun p => grundy (nstree f (snd p))) (selections (C :: G))) ->
        x = parity (length G)).
      { intros x Hx; apply in_map_iff in Hx; destruct Hx as [p [<- Hp]].
        pose proof (selections_length (C :: G) p Hp) as Hl; simpl in Hl.
        rewrite (IH (snd p)) by lia.
        f_equal; lia. }
      assert (Hne : map (fun p => grundy (nstree f (snd p)))
                        (selections (C :: G)) <> []).
      { simpl selections; simpl map; discriminate. }
      simpl length; rewrite parity_succ.
      destruct (Nat.even (length G)) eqn:Ev.
      * apply mex_all_zero; [exact Hne|].
        intros x Hx; rewrite (Hchild x Hx); unfold parity; rewrite Ev;
          reflexivity.
      * apply mex_all_one.
        intros x Hx; rewrite (Hchild x Hx); unfold parity; rewrite Ev;
          reflexivity.
Qed.

Definition nimstring (G : position) : Grundy.game := nstree (length G) G.

Corollary nimstring_value :
  forall G, grundy (nimstring G) = parity (length G).
Proof. intros G; apply nimstring_grundy; lia. Qed.

(** So the player to move wins exactly on an odd number of components. *)
Theorem nimstring_opener_wins :
  forall G, winb (nimstring G) = true <-> Nat.odd (length G) = true.
Proof.
  intros G; rewrite winb_grundy, nimstring_value.
  unfold parity; rewrite <- Nat.negb_even.
  destruct (Nat.even (length G)); simpl; split;
    solve [intros H; exfalso; apply H; reflexivity
          | discriminate | intros _; discriminate | intros _; reflexivity].
Qed.

(** A single component is a first player win, and two are a second player
    win: the alternation the long chain rule counts. *)
Example nimstring_one : forall C, winb (nimstring [C]) = true.
Proof. intros C; apply nimstring_opener_wins; reflexivity. Qed.

Example nimstring_two : forall C D, winb (nimstring [C; D]) = false.
Proof.
  intros C D; destruct (winb (nimstring [C; D])) eqn:E; [|reflexivity].
  apply nimstring_opener_wins in E; discriminate.
Qed.
