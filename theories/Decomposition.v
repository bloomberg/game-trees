(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Board components as a loony position.

    A component of an unfinished board is a run of open boxes joined by
    undrawn edges. A run that closes on itself is a loop; one that does not is
    a chain. [comps_position] turns a decomposition into a
    [GameTrees.DotsAndBoxes.position] and [comps_position_wf] proves the
    result wellformed.

    The point is the loop case. [DotsAndBoxes.wf_comp] asks a [Loop] to have
    even length at least four, and that is not assumed here: evenness comes
    from [StringsAndCoins.cyclic_even], since the grid dual is bipartite, and
    the bound to four follows because an even cycle cannot have three boxes.
    So the hypothesis the endgame theory rests on is discharged by the
    geometry of the board. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Lia.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.StringsAndCoins.
Require Import GameTrees.DotsAndBoxes.

(** * A cycle of boxes is a wellformed loop *)

(** A genuine cycle has at least three boxes; being even, it therefore has at
    least four. *)
Theorem loop_comp_wf :
  forall bs,
    cyclic bs -> (3 <= length bs)%nat ->
    wf_comp (Loop (length bs)).
Proof.
  intros bs Hcyc H3; simpl.
  pose proof (cyclic_even bs Hcyc) as Hev.
  split; [|exact Hev].
  destruct (Nat.eq_dec (length bs) 3) as [Heq | Hne]; [|lia].
  exfalso; rewrite Heq in Hev; discriminate.
Qed.

(** A run of three or more boxes is a wellformed chain. *)
Theorem chain_comp_wf :
  forall bs : list (nat * nat),
    (3 <= length bs)%nat -> wf_comp (Chain (length bs)).
Proof. intros bs H; simpl; exact H. Qed.

(** * Checking a decomposition by computation *)

Definition cadjb (b1 b2 : nat * nat) : bool :=
  (((fst b1 =? fst b2) &&
    ((snd b1 =? S (snd b2)) || (snd b2 =? S (snd b1))))
   || ((snd b1 =? snd b2) &&
       ((fst b1 =? S (fst b2)) || (fst b2 =? S (fst b1)))))%bool.

Lemma cadjb_cadj : forall b1 b2, cadjb b1 b2 = true -> cadj b1 b2.
Proof.
  intros b1 b2 H; unfold cadjb, cadj in *.
  apply orb_true_iff in H; destruct H as [H | H];
    apply andb_true_iff in H; destruct H as [H1 H2];
    apply Nat.eqb_eq in H1; apply orb_true_iff in H2.
  - left; split; [exact H1|].
    destruct H2 as [H2 | H2]; apply Nat.eqb_eq in H2; auto.
  - right; split; [exact H1|].
    destruct H2 as [H2 | H2]; apply Nat.eqb_eq in H2; auto.
Qed.

Fixpoint chain_walkb (b : nat * nat) (bs : list (nat * nat)) : bool :=
  match bs with
  | [] => true
  | c :: r => (cadjb b c && chain_walkb c r)%bool
  end.

Lemma chain_walkb_chain_walk :
  forall bs b, chain_walkb b bs = true -> chain_walk b bs.
Proof.
  induction bs as [|c r IH]; intros b H; simpl in *; [exact I|].
  apply andb_true_iff in H; destruct H as [H1 H2].
  split; [apply cadjb_cadj; exact H1 | apply IH; exact H2].
Qed.

Definition cyclicb (bs : list (nat * nat)) : bool :=
  match bs with
  | [] => false
  | b :: r => (chain_walkb b r && cadjb (last r b) b)%bool
  end.

Lemma cyclicb_cyclic : forall bs, cyclicb bs = true -> cyclic bs.
Proof.
  intros [|b r] H; simpl in *; [discriminate|].
  apply andb_true_iff in H; destruct H as [H1 H2].
  split; [apply chain_walkb_chain_walk; exact H1 | apply cadjb_cadj; exact H2].
Qed.

(** A decomposition passes when every loop closes and is long enough and
    every chain is long enough. *)
Definition decomp_okb (loops chains : list (list (nat * nat))) : bool :=
  (forallb (fun bs => cyclicb bs && (3 <=? length bs))%bool loops
   && forallb (fun bs => 3 <=? length bs) chains)%bool.

(** * A decomposition as a position *)

Definition comps_position
    (loops chains : list (list (nat * nat))) : position :=
  map (fun bs => Loop (length bs)) loops
  ++ map (fun bs => Chain (length bs)) chains.

(** Whatever decomposition a board yields, the multiset of components it names
    is a wellformed loony position, so the whole of [GameTrees.DotsAndBoxes]
    applies to it. *)
Theorem comps_position_wf :
  forall loops chains,
    (forall bs, In bs loops -> cyclic bs /\ (3 <= length bs)%nat) ->
    (forall bs, In bs chains -> (3 <= length bs)%nat) ->
    wf (comps_position loops chains).
Proof.
  intros loops chains Hl Hc; unfold wf, comps_position.
  apply Forall_app; split; rewrite Forall_map, Forall_forall.
  - intros bs Hbs; destruct (Hl bs Hbs) as [Hcyc H3].
    apply loop_comp_wf; assumption.
  - intros bs Hbs; apply chain_comp_wf, Hc, Hbs.
Qed.

(** So a checked decomposition yields a wellformed position by computation
    alone, with no hypothesis left for the caller to discharge. *)
Theorem decomp_okb_wf :
  forall loops chains,
    decomp_okb loops chains = true -> wf (comps_position loops chains).
Proof.
  intros loops chains H; unfold decomp_okb in H.
  apply andb_true_iff in H; destruct H as [Hl Hc].
  rewrite forallb_forall in Hl, Hc.
  apply comps_position_wf.
  - intros bs Hbs; specialize (Hl bs Hbs).
    apply andb_true_iff in Hl; destruct Hl as [H1 H2].
    split; [apply cyclicb_cyclic; exact H1 | apply Nat.leb_le; exact H2].
  - intros bs Hbs; apply Nat.leb_le, Hc, Hbs.
Qed.

Lemma list_sum_app_nat :
  forall l1 l2, (list_sum (l1 ++ l2) = list_sum l1 + list_sum l2)%nat.
Proof.
  induction l1 as [|a l1 IH]; intros l2; simpl; [reflexivity|].
  rewrite IH; lia.
Qed.

(** The boxes are accounted for exactly: the size of the position is the
    number of boxes in the components. *)
Lemma size_comps_position :
  forall loops chains,
    (size (comps_position loops chains)
     = list_sum (map (@length (nat * nat)) loops)
       + list_sum (map (@length (nat * nat)) chains))%nat.
Proof.
  intros loops chains; unfold size, comps_position.
  rewrite map_app, !map_map, list_sum_app_nat; reflexivity.
Qed.

Lemma list_sum_length_concat :
  forall l : list (list (nat * nat)),
    (list_sum (map (@length (nat * nat)) l) = length (concat l))%nat.
Proof.
  induction l as [|x l IH]; simpl; [reflexivity|].
  rewrite length_app, IH; reflexivity.
Qed.

(** A decomposition that partitions the open boxes accounts for every one of
    them: the size of the position it names is the number of boxes still in
    play. Together with [comps_position_wf] this is what licenses treating a
    board as a [DotsAndBoxes.position]. *)
Theorem decomp_size :
  forall loops chains open,
    Permutation (concat (loops ++ chains)) open ->
    (size (comps_position loops chains) = length open)%nat.
Proof.
  intros loops chains open Hperm.
  rewrite size_comps_position, !list_sum_length_concat.
  rewrite <- length_app, <- concat_app.
  apply Permutation_length; exact Hperm.
Qed.

(** With no loops the position is one of chains alone, which is where
    [DotsAndBoxes.value_all_chains] applies. *)
Corollary comps_no_loops :
  forall chains,
    (forall bs, In bs chains -> (3 <= length bs)%nat) ->
    wf (comps_position [] chains) /\
    existsb is_loop_b (comps_position [] chains) = false.
Proof.
  intros chains Hc; split.
  - apply comps_position_wf; [intros bs [] | exact Hc].
  - unfold comps_position; simpl app.
    rewrite existsb_map.
    clear Hc; induction chains as [|bs cs IH]; simpl; [reflexivity | exact IH].
Qed.

(** And with no chains it is loops alone, where [value_all_loops] applies. *)
Corollary comps_no_chains :
  forall loops,
    (forall bs, In bs loops -> cyclic bs /\ (3 <= length bs)%nat) ->
    wf (comps_position loops []) /\
    forallb is_loop_b (comps_position loops []) = true.
Proof.
  intros loops Hl; split.
  - apply comps_position_wf; [exact Hl | intros bs []].
  - unfold comps_position; rewrite app_nil_r, forallb_map.
    clear Hl; induction loops as [|bs ls IH]; simpl; [reflexivity | exact IH].
Qed.
