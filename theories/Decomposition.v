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
Require Import GameTrees.Helpers.
Require Import GameTrees.StringsAndCoins.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.DotsAndBoxesBoard.
Require Import GameTrees.Nimstring.
Require Import GameTrees.Grundy.

Import ListNotations.

Import ListNotations.

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

(** ****************************************************************** *)
(** Extracting a decomposition from a board.

    [GameTrees.Decomposition] turns lists of loops and chains into a loony
    position and checks them, but the lists have to be supplied: nothing
    computes them from a board. This file computes them.

    [comp_from] walks from a box to a neighbour not yet visited and keeps
    going. [comp_from_walk] proves the run it returns is a [chain_walk], so a
    run of three or more boxes is a wellformed [Chain] by
    [Decomposition.chain_comp_wf], and one that closes back on its start is a
    wellformed [Loop] by [loop_comp_wf]. [comp_from_nodup] proves it visits no
    box twice, so peeling components off terminates and the pieces are
    disjoint.

    The adjacency is a parameter: any Boolean relation refining [cadj] will
    do, so the same extractor serves the undrawn-wall graph of a board and any
    other neighbour test. *)

Definition box : Type := (nat * nat)%type.

Definition beqb (b c : box) : bool :=
  ((fst b =? fst c) && (snd b =? snd c))%bool.

Lemma beqb_true_iff : forall b c, beqb b c = true <-> b = c.
Proof.
  intros [a b] [c d]; unfold beqb; simpl; split.
  - intros H; apply andb_true_iff in H; destruct H as [H1 H2].
    apply Nat.eqb_eq in H1; apply Nat.eqb_eq in H2; subst; reflexivity.
  - intros H; injection H as -> ->; rewrite !Nat.eqb_refl; reflexivity.
Qed.

Lemma beqb_refl : forall b, beqb b b = true.
Proof. intros b; apply beqb_true_iff; reflexivity. Qed.

Definition bmem (b : box) (l : list box) : bool := existsb (beqb b) l.

Lemma bmem_true_iff : forall b l, bmem b l = true <-> In b l.
Proof.
  intros b l; unfold bmem; rewrite existsb_exists; split.
  - intros [x [Hx He]]; apply beqb_true_iff in He; subst; auto.
  - intros H; exists b; split; [exact H | apply beqb_refl].
Qed.

Lemma bmem_false_iff : forall b l, bmem b l = false <-> ~ In b l.
Proof.
  intros b l; split.
  - intros H Hin; apply bmem_true_iff in Hin; congruence.
  - intros H; destruct (bmem b l) eqn:E;
      [apply bmem_true_iff in E; contradiction | reflexivity].
Qed.

Section Extract.

(** The boxes still in play, and a neighbour test refining board adjacency. *)
Variable U : list box.
Variable A : box -> box -> bool.
Hypothesis A_cadj : forall b c, A b c = true -> cadj b c.

(** The first unvisited neighbour, if there is one. *)
Definition pick (vis : list box) (b : box) : option box :=
  match filter (fun c => A b c && negb (bmem c vis))%bool U with
  | [] => None
  | c :: _ => Some c
  end.

Lemma pick_spec :
  forall vis b c,
    pick vis b = Some c -> In c U /\ A b c = true /\ ~ In c vis.
Proof.
  intros vis b c H; unfold pick in H.
  destruct (filter (fun x => A b x && negb (bmem x vis))%bool U) as [|d r] eqn:E;
    [discriminate|].
  injection H as ->.
  assert (Hin : In c (filter (fun x => A b x && negb (bmem x vis))%bool U))
    by (rewrite E; left; reflexivity).
  apply filter_In in Hin; destruct Hin as [HU Hb].
  apply andb_true_iff in Hb; destruct Hb as [HA Hv].
  apply negb_true_iff, bmem_false_iff in Hv.
  repeat split; assumption.
Qed.

(** The boxes after [b] along the walk. *)
Fixpoint tail_of (fuel : nat) (vis : list box) (b : box) : list box :=
  match fuel with
  | O => []
  | S f =>
      match pick vis b with
      | None => []
      | Some c => c :: tail_of f (c :: vis) c
      end
  end.

(** The component reached from [b]. The start is visited from the outset, so
    the walk cannot return to it. *)
Definition comp_from (b : box) : list box := b :: tail_of (length U) [b] b.

(** * The run is a walk *)

Lemma tail_of_walk :
  forall fuel vis b, chain_walk b (tail_of fuel vis b).
Proof.
  induction fuel as [|f IH]; intros vis b; simpl; [exact I|].
  destruct (pick vis b) as [c|] eqn:E; [|exact I].
  destruct (pick_spec vis b c E) as [_ [HA _]].
  split; [apply A_cadj; exact HA | apply IH].
Qed.

(** So the extracted component is a run of neighbouring boxes. *)
Theorem comp_from_walk :
  forall b, chain_walk b (tail_of (length U) [b] b).
Proof. intros b; apply tail_of_walk. Qed.

(** * The run repeats no box *)

(** Nothing already visited appears further along. *)
Lemma tail_of_avoids :
  forall fuel vis b x, In x vis -> ~ In x (tail_of fuel vis b).
Proof.
  induction fuel as [|f IH]; intros vis b x Hx; simpl; [intros []|].
  destruct (pick vis b) as [c|] eqn:E; [|intros []].
  destruct (pick_spec vis b c E) as [_ [_ Hc]].
  intros [Heq | Hin].
  - subst c; contradiction.
  - apply (IH (c :: vis) c x); [right; exact Hx | exact Hin].
Qed.

Lemma tail_of_nodup :
  forall fuel vis b, NoDup (tail_of fuel vis b).
Proof.
  induction fuel as [|f IH]; intros vis b; simpl; [constructor|].
  destruct (pick vis b) as [c|] eqn:E; [|constructor].
  constructor; [| apply IH].
  apply (tail_of_avoids f (c :: vis) c c); left; reflexivity.
Qed.

(** The start does not recur either, so the whole component is repeat-free. *)
Theorem comp_from_nodup : forall b, NoDup (comp_from b).
Proof.
  intros b; unfold comp_from; constructor.
  - apply (tail_of_avoids (length U) [b] b b); left; reflexivity.
  - apply tail_of_nodup.
Qed.

(** * The run stays on the board *)

Lemma tail_of_incl :
  forall fuel vis b, incl (tail_of fuel vis b) U.
Proof.
  induction fuel as [|f IH]; intros vis b x Hx; simpl in Hx; [destruct Hx|].
  destruct (pick vis b) as [c|] eqn:E; [|destruct Hx].
  destruct (pick_spec vis b c E) as [HU _].
  destruct Hx as [<- | Hx]; [exact HU | apply (IH (c :: vis) c); exact Hx].
Qed.

Theorem comp_from_incl : forall b, In b U -> incl (comp_from b) U.
Proof.
  intros b Hb x Hx; destruct Hx as [<- | Hx];
    [exact Hb | apply (tail_of_incl (length U) [b] b); exact Hx].
Qed.

(** A component is no longer than the board. *)
Theorem comp_from_length :
  forall b, In b U -> (length (comp_from b) <= length U)%nat.
Proof.
  intros b Hb; apply NoDup_incl_length;
    [apply comp_from_nodup | apply comp_from_incl; exact Hb].
Qed.

(** * Feeding the endgame theory *)

(** A component of three or more boxes that does not close is a wellformed
    chain. *)
Theorem comp_chain_wf :
  forall b, (3 <= length (comp_from b))%nat -> wf_comp (Chain (length (comp_from b))).
Proof. intros b H; apply chain_comp_wf; exact H. Qed.

(** One that closes back on its start is a wellformed loop, its even length
    coming from the board rather than from any assumption. *)
Theorem comp_loop_wf :
  forall b,
    cyclic (comp_from b) -> (3 <= length (comp_from b))%nat ->
    wf_comp (Loop (length (comp_from b))).
Proof. intros b Hc H; apply loop_comp_wf; assumption. Qed.

(** The Boolean form, so a caller checks a component by computation. *)
Definition comp_is_loop (b : box) : bool :=
  (cyclicb (comp_from b) && (3 <=? length (comp_from b)))%bool.

Definition comp_is_chain (b : box) : bool :=
  (negb (cyclicb (comp_from b)) && (3 <=? length (comp_from b)))%bool.

Lemma comp_is_loop_wf :
  forall b, comp_is_loop b = true -> wf_comp (Loop (length (comp_from b))).
Proof.
  intros b H; unfold comp_is_loop in H.
  apply andb_true_iff in H; destruct H as [H1 H2].
  apply comp_loop_wf; [apply cyclicb_cyclic; exact H1 | apply Nat.leb_le; exact H2].
Qed.

Lemma comp_is_chain_wf :
  forall b, comp_is_chain b = true -> wf_comp (Chain (length (comp_from b))).
Proof.
  intros b H; unfold comp_is_chain in H.
  apply andb_true_iff in H; destruct H as [_ H2].
  apply comp_chain_wf; apply Nat.leb_le; exact H2.
Qed.

(** * Peeling the board into components *)

Definition drop_all (c : list box) (l : list box) : list box :=
  filter (fun x => negb (bmem x c)) l.

Lemma drop_all_incl : forall c l, incl (drop_all c l) l.
Proof. intros c l x Hx; apply filter_In in Hx; tauto. Qed.

Lemma drop_all_not_in :
  forall c l x, In x c -> ~ In x (drop_all c l).
Proof.
  intros c l x Hx Hin; apply filter_In in Hin; destruct Hin as [_ H].
  apply negb_true_iff, bmem_false_iff in H; contradiction.
Qed.

(** Removing a component that meets the list shortens it. *)
Lemma drop_all_shorter :
  forall c l x, In x c -> In x l -> (length (drop_all c l) < length l)%nat.
Proof.
  intros c l x Hx Hl; unfold drop_all.
  induction l as [|a l IH]; [destruct Hl|]; simpl.
  destruct Hl as [<- | Hl].
  - rewrite (proj2 (bmem_true_iff a c) Hx); simpl.
    pose proof (length_filter_le (fun y => negb (bmem y c)) l); lia.
  - specialize (IH Hl); destruct (negb (bmem a c)); simpl; lia.
Qed.

End Extract.

(** * The decomposition *)

Section Decompose.

Variable A : box -> box -> bool.
Hypothesis A_cadj : forall b c, A b c = true -> cadj b c.

(** Peel one component at a time off the remaining boxes. The fuel is the
    number of boxes, and each round removes at least the box it started
    from. *)
Fixpoint peel (fuel : nat) (rem : list box) : list (list box) :=
  match fuel with
  | O => []
  | S f =>
      match rem with
      | [] => []
      | b :: _ =>
          let c := comp_from rem A b in
          c :: peel f (drop_all c rem)
      end
  end.

Definition decompose (U : list box) : list (list box) := peel (length U) U.

(** Every piece the peeling returns is a run of neighbouring boxes with no
    repeats. *)
Theorem peel_walk :
  forall fuel rem c,
    In c (peel fuel rem) ->
    exists b l, c = b :: l /\ chain_walk b l /\ NoDup c.
Proof.
  induction fuel as [|f IH]; intros rem c Hc; simpl in Hc; [destruct Hc|].
  destruct rem as [|b rest]; [destruct Hc|].
  destruct Hc as [<- | Hc].
  - exists b, (tail_of (b :: rest) A (length (b :: rest)) [b] b).
    repeat split.
    + apply (comp_from_walk (b :: rest) A A_cadj).
    + apply (comp_from_nodup (b :: rest) A).
  - apply (IH (drop_all (comp_from (b :: rest) A b) (b :: rest)) c); exact Hc.
Qed.

(** The pieces are made of boxes that were on the board. *)
Theorem peel_incl :
  forall fuel rem c,
    In c (peel fuel rem) -> incl c rem.
Proof.
  induction fuel as [|f IH]; intros rem c Hc; simpl in Hc; [destruct Hc|].
  destruct rem as [|b rest]; [destruct Hc|].
  destruct Hc as [<- | Hc].
  - apply (comp_from_incl (b :: rest) A b); left; reflexivity.
  - eapply incl_tran.
    + apply (IH (drop_all (comp_from (b :: rest) A b) (b :: rest)) c); exact Hc.
    + apply drop_all_incl.
Qed.

(** Splitting the pieces by whether they close. *)
Definition loops_of (U : list box) : list (list box) :=
  filter (fun c => cyclicb c && (3 <=? length c))%bool (decompose U).

Definition chains_of (U : list box) : list (list box) :=
  filter (fun c => negb (cyclicb c) && (3 <=? length c))%bool (decompose U).

(** Whatever the board, the position the extractor names is wellformed: the
    loops close and are long enough, and the chains are long enough, both by
    computation on the extracted runs. *)
Theorem decompose_wf :
  forall U, wf (comps_position (loops_of U) (chains_of U)).
Proof.
  intros U; apply decomp_okb_wf; unfold decomp_okb.
  apply andb_true_iff; split; rewrite forallb_forall.
  - intros c Hc; unfold loops_of in Hc; apply filter_In in Hc; tauto.
  - intros c Hc; unfold chains_of in Hc; apply filter_In in Hc.
    destruct Hc as [_ H]; apply andb_true_iff in H; tauto.
Qed.

(** And it is a genuine loony position of the host theory, so the whole of
    [GameTrees.DotsAndBoxes] applies to what the extractor returns. *)
Corollary decompose_position :
  forall U,
    wf (comps_position (loops_of U) (chains_of U)) /\
    (size (comps_position (loops_of U) (chains_of U))
     = list_sum (map (@length box) (loops_of U))
       + list_sum (map (@length box) (chains_of U)))%nat.
Proof.
  intros U; split; [apply decompose_wf | apply size_comps_position].
Qed.

End Decompose.

(** * The decomposition of an actual board *)

(** The wall between two neighbouring boxes: the edges they share. *)
Definition shared (b c : box) : list edge :=
  filter (fun e => existsb (edge_eqb e) (box_edges c)) (box_edges b).

(** Two boxes are joined when both are still open and the wall between them is
    still undrawn. This is the graph the endgame lives on. *)
Definition adj_board (d : list edge) (b c : box) : bool :=
  (cadjb b c && negb (box_done d b) && negb (box_done d c)
   && existsb (fun e => negb (emem e d)) (shared b c))%bool.

Lemma adj_board_cadj :
  forall d b c, adj_board d b c = true -> cadj b c.
Proof.
  intros d b c H; unfold adj_board in H.
  apply andb_true_iff in H; destruct H as [H _].
  apply andb_true_iff in H; destruct H as [H _].
  apply andb_true_iff in H; destruct H as [H _].
  apply cadjb_cadj; exact H.
Qed.

(** The boxes still in play. *)
Definition open_boxes (m n : nat) (d : list edge) : list box :=
  filter (fun b => negb (box_done d b)) (boxes m n).

Lemma open_boxes_incl :
  forall m n d, incl (open_boxes m n d) (boxes m n).
Proof. intros m n d x Hx; apply filter_In in Hx; tauto. Qed.

Lemma open_boxes_open :
  forall m n d b, In b (open_boxes m n d) -> box_done d b = false.
Proof.
  intros m n d b H; apply filter_In in H; destruct H as [_ H].
  apply negb_true_iff; exact H.
Qed.

(** The loops and chains a board breaks into. *)
Definition board_loops (m n : nat) (d : list edge) : list (list box) :=
  loops_of (adj_board d) (open_boxes m n d).

Definition board_chains (m n : nat) (d : list edge) : list (list box) :=
  chains_of (adj_board d) (open_boxes m n d).

Definition board_position (m n : nat) (d : list edge) : position :=
  comps_position (board_loops m n d) (board_chains m n d).

(** Whatever has been drawn, the components the extractor finds on the board
    form a wellformed loony position, so the whole of
    [GameTrees.DotsAndBoxes] applies to a real board. *)
Theorem board_position_wf :
  forall m n d, wf (board_position m n d).
Proof.
  intros m n d; unfold board_position, board_loops, board_chains.
  apply (decompose_wf (adj_board d) (open_boxes m n d)).
Qed.

(** Each extracted run is a walk of neighbouring boxes with no repeats, so the
    components are genuine chains and cycles of the board rather than
    arbitrary box lists. *)
Theorem board_components_walk :
  forall m n d c,
    In c (decompose (adj_board d) (open_boxes m n d)) ->
    exists b l, c = b :: l /\ chain_walk b l /\ NoDup c.
Proof.
  intros m n d c H; unfold decompose in H.
  apply (peel_walk (adj_board d) (adj_board_cadj d)
           (length (open_boxes m n d)) (open_boxes m n d) c H).
Qed.

(** And every box a component names was open on the board. *)
Theorem board_components_open :
  forall m n d c b,
    In c (decompose (adj_board d) (open_boxes m n d)) -> In b c ->
    box_done d b = false.
Proof.
  intros m n d c b Hc Hb.
  apply (open_boxes_open m n d).
  apply (peel_incl (adj_board d)
           (length (open_boxes m n d)) (open_boxes m n d) c Hc); exact Hb.
Qed.

(** ****************************************************************** *)
(** The long chain rule.

    [DotsAndBoxesBoard.long_chain_identity] counts: over a completed game the
    turns taken exceed the dots by the doublecrosses. That is arithmetic, not
    yet a statement about players. What turns it into one is [p1_run]: since
    a move that scores keeps the move and a move that does not ends the turn,
    the player to move after any legal prefix is the first player exactly when
    an even number of turns has been taken. Parity of turns is therefore
    parity of the mover.

    Putting the two together, [long_chain_rule] fixes the parity of the turn
    count from the dots and the doublecrosses alone, and [mover_at_end] reads
    off which player the board hands the move to when it is full. That is the
    rule in the form it is used: the first player controls the count of dots
    plus doublecrosses, and that count decides who is on move at every later
    parity checkpoint.

    The other half of the rule is about components rather than turns, and
    lives in [GameTrees.Nimstring]: a loony position is won by its opener
    exactly when the number of components is odd. [loony_opener_parity] says
    this of a board decomposition, so the long chains and loops a board breaks
    into decide the endgame by their number.

    What is not proved here is the bridge between the two halves, that the
    turns remaining once the loony endgame begins are exactly the components.
    That needs a model of when the opening ends, which this development does
    not have. *)

Section LongChain.

Variables m n : nat.

(** * Unfoldings *)

Lemma run_cons :
  forall s e ms, run m n s (e :: ms) = run m n (db_play m n s e) ms.
Proof. reflexivity. Qed.

Lemma turns_cons :
  forall s e ms,
    turns m n s (e :: ms) =
    ((match ngain m n (laid s) e with O => 1 | S _ => 0 end)
     + turns m n (db_play m n s e) ms)%nat.
Proof. reflexivity. Qed.

(** A move that takes no box ends the turn; one that takes a box keeps it. *)
Lemma p1_play :
  forall s e,
    p1 (db_play m n s e) =
    match ngain m n (laid s) e with
    | O => negb (p1 s)
    | S _ => p1 s
    end.
Proof.
  intros s e; unfold db_play.
  destruct (ngain m n (laid s) e); [reflexivity | destruct (p1 s); reflexivity].
Qed.

(** * The mover is the parity of the turns *)

(** After any sequence of moves the mover has flipped exactly once per turn,
    so it is determined by the parity of the turn count. *)
Theorem p1_run :
  forall ms s, p1 (run m n s ms) = xorb (p1 s) (Nat.odd (turns m n s ms)).
Proof.
  induction ms as [|e ms IH]; intros s.
  - simpl run; simpl turns; destruct (p1 s); reflexivity.
  - rewrite run_cons, turns_cons, (IH (db_play m n s e)), p1_play.
    destruct (ngain m n (laid s) e).
    + simpl Nat.add.
      rewrite Nat.odd_succ, <- Nat.negb_odd.
      destruct (p1 s); destruct (Nat.odd (turns m n (db_play m n s e) ms));
        reflexivity.
    + simpl Nat.add; reflexivity.
Qed.

(** From the empty board the mover is the first player exactly on an even
    number of turns. *)
Corollary p1_run_init :
  forall ms, p1 (run m n init ms) = negb (Nat.odd (turns m n init ms)).
Proof.
  intros ms; rewrite (p1_run ms init).
  change (p1 init) with true.
  destruct (Nat.odd (turns m n init ms)); reflexivity.
Qed.

(** * The rule *)

(** The parity of the turn count is fixed by the dots and the doublecrosses,
    and by nothing else about the play. *)
Theorem long_chain_rule :
  forall ms,
    legal m n init ms ->
    complete m n (run m n init ms) ->
    Nat.odd (turns m n init ms) = Nat.even (dots m n + extra m n init ms).
Proof.
  intros ms Hl Hc.
  rewrite <- (long_chain_identity m n ms Hl Hc).
  rewrite Nat.even_succ, <- Nat.negb_even, <- Nat.negb_odd, negb_involutive.
  reflexivity.
Qed.

(** So the board hands the move back to the first player, once full, exactly
    when the dots and doublecrosses together are odd. *)
Theorem mover_at_end :
  forall ms,
    legal m n init ms ->
    complete m n (run m n init ms) ->
    p1 (run m n init ms) = Nat.odd (dots m n + extra m n init ms).
Proof.
  intros ms Hl Hc.
  rewrite p1_run_init, (long_chain_rule ms Hl Hc), <- Nat.negb_odd,
          negb_involutive.
  reflexivity.
Qed.

(** With no doublecrosses the rule is about the dots alone. *)
Corollary mover_at_end_no_doublecross :
  forall ms,
    legal m n init ms ->
    complete m n (run m n init ms) ->
    extra m n init ms = 0%nat ->
    p1 (run m n init ms) = Nat.odd (dots m n).
Proof.
  intros ms Hl Hc H0.
  rewrite (mover_at_end ms Hl Hc), H0, Nat.add_0_r; reflexivity.
Qed.

(** A player who takes every box scores every one of them, so the
    doublecrosses are what the loser gives away: the parity the first player
    steers is [dots + extra] and nothing else. *)
Corollary turns_determined_mod2 :
  forall ms ms',
    legal m n init ms -> complete m n (run m n init ms) ->
    legal m n init ms' -> complete m n (run m n init ms') ->
    extra m n init ms = extra m n init ms' ->
    Nat.odd (turns m n init ms) = Nat.odd (turns m n init ms').
Proof.
  intros ms ms' Hl Hc Hl' Hc' He.
  rewrite (long_chain_rule ms Hl Hc), (long_chain_rule ms' Hl' Hc'), He.
  reflexivity.
Qed.

End LongChain.

(** * The component half of the rule *)

(** A board decomposition names one component per long chain and per loop, so
    the Nimstring endgame it presents is won by its opener exactly when their
    number is odd. *)
Theorem loony_opener_parity :
  forall loops chains,
    winb (nimstring (comps_position loops chains)) = true <->
    Nat.odd (length loops + length chains) = true.
Proof.
  intros loops chains.
  rewrite nimstring_opener_wins.
  unfold comps_position; rewrite length_app, !length_map; reflexivity.
Qed.

(** With no loops it is the long chains alone that decide. *)
Corollary loony_opener_chains :
  forall chains,
    winb (nimstring (comps_position [] chains)) = true <->
    Nat.odd (length chains) = true.
Proof.
  intros chains; rewrite loony_opener_parity; reflexivity.
Qed.

(** * Turns in the endgame are components *)

(** A run of openings: each turn of a loony endgame takes one component, and
    the run ends when nothing is left. *)
Fixpoint opening_run (G : position) (ps : list (comp * position)) : Prop :=
  match ps with
  | [] => G = []
  | p :: r => In p (selections G) /\ opening_run (snd p) r
  end.

(** So a run that empties the position takes exactly one turn per component.
    This is the half of the long chain rule that counts components rather
    than dots. *)
Theorem opening_run_length :
  forall ps G, opening_run G ps -> length ps = length G.
Proof.
  induction ps as [|p ps IH]; intros G H; simpl in H.
  - subst G; reflexivity.
  - destruct H as [Hp Hr].
    simpl length; rewrite (IH (snd p) Hr).
    pose proof (selections_length G p Hp); lia.
Qed.

(** Every loony position admits such a run, so the count is attained. *)
Theorem opening_run_exists :
  forall G, exists ps, opening_run G ps /\ length ps = length G.
Proof.
  assert (Haux : forall k G, (length G <= k)%nat -> exists ps, opening_run G ps).
  { induction k as [|k IH]; intros G Hk.
    - assert (HG : G = []) by (destruct G; simpl in Hk; [reflexivity | lia]).
      subst G; exists []; reflexivity.
    - destruct G as [|C G]; [exists []; reflexivity|].
      destruct (IH G) as [ps Hps]; [simpl in Hk; lia|].
      exists ((C, G) :: ps); split; [left; reflexivity | exact Hps]. }
  intros G; destruct (Haux (length G) G ltac:(lia)) as [ps Hps].
  exists ps; split; [exact Hps | apply opening_run_length; exact Hps].
Qed.

(** Putting the two halves together: the opener of a loony endgame wins
    exactly when the endgame runs for an odd number of turns. *)
Corollary endgame_opener_parity :
  forall G ps,
    opening_run G ps ->
    (winb (nimstring G) = true <-> Nat.odd (length ps) = true).
Proof.
  intros G ps H; rewrite nimstring_opener_wins, (opening_run_length ps G H).
  reflexivity.
Qed.

(** And on a board decomposition the turn count is the number of long chains
    and loops. *)
Corollary decomp_endgame_turns :
  forall loops chains ps,
    opening_run (comps_position loops chains) ps ->
    length ps = (length loops + length chains)%nat.
Proof.
  intros loops chains ps H.
  rewrite (opening_run_length ps _ H).
  unfold comps_position; rewrite length_app, !length_map; reflexivity.
Qed.

(** ****************************************************************** *)
(** Coverage.

    The peeling not only produces walks, it exhausts the board: every open box
    lies in one of the components, and no box lies in two. Each round removes
    the component it just found, so the remainder strictly shrinks and the
    pieces are pairwise disjoint. *)

Section Coverage.

Variable A : box -> box -> bool.

Lemma In_drop_all :
  forall c l x, In x l -> ~ In x c -> In x (drop_all c l).
Proof.
  intros c l x Hl Hc; unfold drop_all; apply filter_In; split;
    [exact Hl | apply negb_true_iff, bmem_false_iff; exact Hc].
Qed.

(** Every box of the remainder ends up in some component. *)
Lemma peel_covers :
  forall fuel rem x,
    (length rem <= fuel)%nat -> In x rem ->
    exists c, In c (peel A fuel rem) /\ In x c.
Proof.
  induction fuel as [|f IH]; intros rem x Hlen Hx.
  - destruct rem as [|b r]; [destruct Hx | simpl in Hlen; lia].
  - destruct rem as [|b r]; [destruct Hx|].
    set (c := comp_from (b :: r) A b).
    destruct (bmem x c) eqn:Ex.
    + exists c; split; [left; reflexivity | apply bmem_true_iff; exact Ex].
    + apply bmem_false_iff in Ex.
      assert (Hin : In x (drop_all c (b :: r)))
        by (apply In_drop_all; assumption).
      assert (Hb : In b c) by (unfold c, comp_from; left; reflexivity).
      assert (Hshort : (length (drop_all c (b :: r)) < length (b :: r))%nat)
        by (apply (drop_all_shorter c (b :: r) b); [exact Hb | left; reflexivity]).
      assert (Hle : (length (drop_all c (b :: r)) <= f)%nat)
        by lia.
      destruct (IH (drop_all c (b :: r)) x Hle Hin) as [c' [Hc' Hx']].
      exists c'; split; [right; exact Hc' | exact Hx'].
Qed.

(** So the decomposition of a board accounts for every box still in play. *)
Theorem decompose_covers :
  forall U x, In x U -> exists c, In c (decompose A U) /\ In x c.
Proof. intros U x Hx; apply peel_covers; [lia | exact Hx]. Qed.

(** No box is claimed twice: once a component is peeled off, its boxes are
    gone from the remainder, so nothing later can name them. *)
Lemma peel_head_disjoint :
  forall fuel b r c x,
    In c (peel A fuel (drop_all (comp_from (b :: r) A b) (b :: r))) ->
    In x (comp_from (b :: r) A b) -> ~ In x c.
Proof.
  intros fuel b r c x Hc Hx Hin.
  assert (Hsub : incl c (drop_all (comp_from (b :: r) A b) (b :: r)))
    by (apply (peel_incl A fuel); exact Hc).
  exact (drop_all_not_in (comp_from (b :: r) A b) (b :: r) x Hx (Hsub x Hin)).
Qed.

Theorem peel_disjoint :
  forall fuel rem c1 c2 x,
    In c1 (peel A fuel rem) -> In c2 (peel A fuel rem) ->
    In x c1 -> In x c2 -> c1 = c2.
Proof.
  induction fuel as [|f IH]; intros rem c1 c2 x H1 H2 Hx1 Hx2;
    simpl in H1, H2; [destruct H1|].
  destruct rem as [|b r]; [destruct H1|].
  destruct H1 as [<- | H1]; destruct H2 as [<- | H2].
  - reflexivity.
  - exfalso; exact (peel_head_disjoint f b r c2 x H2 Hx1 Hx2).
  - exfalso; exact (peel_head_disjoint f b r c1 x H1 Hx2 Hx1).
  - exact (IH (drop_all (comp_from (b :: r) A b) (b :: r)) c1 c2 x
            H1 H2 Hx1 Hx2).
Qed.

(** Every open box lies in exactly one component. *)
Theorem decompose_partition :
  forall U x,
    In x U ->
    exists c, In c (decompose A U) /\ In x c /\
              (forall c', In c' (decompose A U) -> In x c' -> c' = c).
Proof.
  intros U x Hx.
  destruct (decompose_covers U x Hx) as [c [Hc Hxc]].
  exists c; repeat split; [exact Hc | exact Hxc |].
  intros c' Hc' Hx'; apply (peel_disjoint (length U) U c' c x); assumption.
Qed.

End Coverage.

(** At the board, the components of an open position partition the boxes still
    in play. *)
Theorem board_decompose_partition :
  forall m n d b,
    In b (open_boxes m n d) ->
    exists c,
      In c (decompose (adj_board d) (open_boxes m n d)) /\ In b c /\
      (forall c', In c' (decompose (adj_board d) (open_boxes m n d)) ->
                  In b c' -> c' = c).
Proof. intros m n d b Hb; apply decompose_partition; exact Hb. Qed.


(** ****************************************************************** *)
(** Legal play reaches a loony position.

    The components partition the open boxes, but [loops_of] and [chains_of]
    drop anything shorter than three, so the extracted position need not hold
    them all. A board is loony when nothing is dropped, and there
    [board_position_covers] says the position carries exactly the boxes still
    in play. [reachable_loony] is the bridge: at any state legal play reaches,
    once the board is loony the rest of the game is a wellformed loony
    position of [GameTrees.DotsAndBoxes] on precisely the open boxes. *)

Lemma peel_cons :
  forall A f b rest,
    peel A (S f) (b :: rest) =
    comp_from (b :: rest) A b
      :: peel A f (drop_all (comp_from (b :: rest) A b) (b :: rest)).
Proof. reflexivity. Qed.

Lemma peel_concat_nodup :
  forall A fuel rem, NoDup (concat (peel A fuel rem)).
Proof.
  intros A; induction fuel as [|f IH]; intros rem; [simpl; constructor|].
  destruct rem as [|b rest]; [simpl; constructor|].
  rewrite peel_cons, concat_cons.
  apply NoDup_app_disj.
  - apply (comp_from_nodup (b :: rest) A).
  - apply IH.
  - intros x Hx Hc.
    apply in_concat in Hc; destruct Hc as [c' [Hc' Hx']].
    apply (drop_all_not_in (comp_from (b :: rest) A b) (b :: rest) x Hx).
    apply (peel_incl A f (drop_all (comp_from (b :: rest) A b) (b :: rest))
             c' Hc'); exact Hx'.
Qed.

Lemma peel_concat_incl :
  forall A fuel rem, incl (concat (peel A fuel rem)) rem.
Proof.
  intros A fuel rem x Hx.
  apply in_concat in Hx; destruct Hx as [c [Hc Hxc]].
  apply (peel_incl A fuel rem c Hc); exact Hxc.
Qed.

(** The components, taken together, are the boxes they were peeled from. *)
Theorem decompose_perm :
  forall A U, NoDup U -> Permutation (concat (decompose A U)) U.
Proof.
  intros A U HU; apply NoDup_Permutation.
  - apply peel_concat_nodup.
  - exact HU.
  - intros x; split.
    + intros Hx; apply (peel_concat_incl A (length U) U); exact Hx.
    + intros Hx.
      destruct (decompose_covers A U x Hx) as [c [Hc Hxc]].
      apply in_concat; exists c; split; [exact Hc | exact Hxc].
Qed.

(** * Loony boards *)

(** No component shorter than three, so the split into loops and chains keeps
    everything. *)
Definition loony_boardb (A : box -> box -> bool) (U : list box) : bool :=
  forallb (fun c => 3 <=? length c) (decompose A U).

Lemma filter_cons_eq :
  forall {X : Type} (f : X -> bool) (x : X) (l : list X),
    filter f (x :: l) = if f x then x :: filter f l else filter f l.
Proof. reflexivity. Qed.

(** Two tests that between them accept everything and never both accept split
    a list in two. *)
Lemma filter_split_perm :
  forall {X : Type} (p q : X -> bool) (l : list X),
    (forall x, In x l -> p x = true \/ q x = true) ->
    (forall x, In x l -> p x = true -> q x = false) ->
    Permutation (filter p l ++ filter q l) l.
Proof.
  intros X p q l; induction l as [|a l IH]; intros H1 H2; [apply Permutation_refl|].
  assert (Hl1 : forall x, In x l -> p x = true \/ q x = true)
    by (intros x Hx; apply H1; right; exact Hx).
  assert (Hl2 : forall x, In x l -> p x = true -> q x = false)
    by (intros x Hx; apply H2; right; exact Hx).
  specialize (IH Hl1 Hl2).
  rewrite !filter_cons_eq.
  destruct (p a) eqn:Ep.
  - rewrite (H2 a (or_introl eq_refl) Ep).
    apply perm_skip; exact IH.
  - destruct (q a) eqn:Eq.
    + eapply Permutation_trans;
        [apply Permutation_sym, Permutation_middle
        | apply perm_skip; exact IH].
    + exfalso; destruct (H1 a (or_introl eq_refl)) as [E|E]; congruence.
Qed.

Lemma loony_split :
  forall A U,
    loony_boardb A U = true ->
    Permutation (loops_of A U ++ chains_of A U) (decompose A U).
Proof.
  intros A U H; unfold loops_of, chains_of, loony_boardb in *.
  rewrite forallb_forall in H.
  apply filter_split_perm.
  - intros x Hx; specialize (H x Hx); cbv beta in H |- *.
    destruct (cyclicb x); [left | right]; cbn [andb negb]; exact H.
  - intros x Hx Hp; cbv beta in Hp |- *.
    apply andb_true_iff in Hp; destruct Hp as [Ec _].
    rewrite Ec; reflexivity.
Qed.

Lemma perm_concat :
  forall {X : Type} (l l' : list (list X)),
    Permutation l l' -> Permutation (concat l) (concat l').
Proof.
  intros X l l' H; induction H; simpl.
  - apply Permutation_refl.
  - apply Permutation_app_head; exact IHPermutation.
  - rewrite !app_assoc; apply Permutation_app_tail, Permutation_app_comm.
  - eapply Permutation_trans; eassumption.
Qed.

Theorem decompose_size :
  forall A U,
    NoDup U -> loony_boardb A U = true ->
    (size (comps_position (loops_of A U) (chains_of A U)) = length U)%nat.
Proof.
  intros A U HU Hl; apply decomp_size.
  eapply Permutation_trans; [| apply decompose_perm; exact HU].
  apply perm_concat, loony_split; exact Hl.
Qed.

(** * On the board *)

Lemma NoDup_brow_dec :
  forall (r n : nat), NoDup (map (fun c : nat => (r, c)) (seq 0 n)).
Proof.
  intros r n; apply NoDup_map_inj; [| apply seq_NoDup].
  intros x y Hxy; injection Hxy as Hxy; exact Hxy.
Qed.

Lemma NoDup_boxes : forall m n, NoDup (boxes m n).
Proof.
  intros m n; unfold boxes; apply NoDup_concat_map.
  - apply seq_NoDup.
  - intros r _; apply NoDup_brow_dec.
  - intros r r' _ _ Hne b Hb Hb'.
    apply in_map_iff in Hb; destruct Hb as [c [<- _]].
    apply in_map_iff in Hb'; destruct Hb' as [c' [Heq _]].
    injection Heq as Heq _; congruence.
Qed.

Lemma NoDup_open_boxes : forall m n d, NoDup (open_boxes m n d).
Proof. intros m n d; apply NoDup_filter, NoDup_boxes. Qed.

Definition board_loony (m n : nat) (d : list edge) : bool :=
  loony_boardb (adj_board d) (open_boxes m n d).

(** The position extracted from a loony board is wellformed and accounts for
    every box still in play. *)
Theorem board_position_covers :
  forall m n d,
    board_loony m n d = true ->
    wf (board_position m n d) /\
    (size (board_position m n d) = length (open_boxes m n d))%nat.
Proof.
  intros m n d H; split; [apply board_position_wf|].
  unfold board_position, board_loops, board_chains.
  apply decompose_size; [apply NoDup_open_boxes | exact H].
Qed.

(** The bridge. At any state legal play reaches, once the board is loony the
    remainder of the game is a wellformed loony position of
    [GameTrees.DotsAndBoxes] carrying exactly the boxes still open, so [value]
    is the margin on the rest of the game. *)
Theorem reachable_loony :
  forall m n s ms,
    legal m n s ms ->
    board_loony m n (laid (run m n s ms)) = true ->
    wf (board_position m n (laid (run m n s ms))) /\
    (size (board_position m n (laid (run m n s ms)))
     = length (open_boxes m n (laid (run m n s ms))))%nat.
Proof. intros m n s ms _ H; apply board_position_covers; exact H. Qed.

Corollary reachable_loony_init :
  forall m n ms,
    legal m n init ms ->
    board_loony m n (laid (run m n init ms)) = true ->
    wf (board_position m n (laid (run m n init ms))) /\
    (size (board_position m n (laid (run m n init ms)))
     = length (open_boxes m n (laid (run m n init ms))))%nat.
Proof. intros m n ms Hl H; apply (reachable_loony m n init ms Hl H). Qed.
