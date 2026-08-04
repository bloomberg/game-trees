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
From Stdlib Require Import ZArith.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Lia.
Require Import GameTrees.Helpers.
Require Import GameTrees.StringsAndCoins.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.DotsAndBoxesBoard.
Require Import GameTrees.Nimstring.
Require Import GameTrees.Grundy.

Import ListNotations.

Open Scope nat_scope.

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
    going, in both directions: a single walk leaves the start in one direction
    only, so a run whose start box is interior would come back cut in half.
    [comp_from_walk] proves the run it returns is a [chain_walk], so a run of
    three or more boxes is a wellformed [Chain] by [chain_comp_wf], and one
    that closes back on its start is a wellformed [Loop] by [loop_comp_wf].
    [comp_from_nodup] proves it visits no box twice, so peeling components off
    terminates and the pieces are disjoint.

    [comp_from_closed] is what makes the run the whole component rather than
    part of one: nothing adjacent to it is left outside. It asks each box for
    at most two neighbours, which is what a chain or a loop gives, and
    [board_comp_from_closed] reads that off the board through [loony_degrees].

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

(** Neighbouring boxes are neighbours in either order. *)
Lemma cadj_sym : forall b c, cadj b c -> cadj c b.
Proof.
  intros [r1 c1] [r2 c2] H; unfold cadj in H |- *; cbn [fst snd] in *.
  destruct H as [[H1 [H2 | H2]] | [H1 [H2 | H2]]].
  - left; split; [lia | right; lia].
  - left; split; [lia | left; lia].
  - right; split; [lia | right; lia].
  - right; split; [lia | left; lia].
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

(** The two arms of the run through [b]. A single walk leaves [b] in one
    direction only, so a run whose start box is interior would be cut in half:
    on the three boxes [(0,1)], [(0,0)], [(1,0)] a walk from [(0,0)] returns two
    of them and the third is peeled off separately. [arm_back] takes the other
    direction, with the first arm already visited so the walk cannot retrace
    it, and [comp_from] glues the two together through [b]. *)
Definition arm_fwd (b : box) : list box := tail_of (length U) [b] b.

Definition arm_back (b : box) : list box :=
  tail_of (length U) (b :: arm_fwd b) b.

Definition comp_from (b : box) : list box :=
  rev (arm_back b) ++ b :: arm_fwd b.

(** * The run is a walk *)

Lemma tail_of_walk :
  forall fuel vis b, chain_walk b (tail_of fuel vis b).
Proof.
  induction fuel as [|f IH]; intros vis b; simpl; [exact I|].
  destruct (pick vis b) as [c|] eqn:E; [|exact I].
  destruct (pick_spec vis b c E) as [_ [HA _]].
  split; [apply A_cadj; exact HA | apply IH].
Qed.

(** A walk read from its own head, so that the two arms can be glued. *)
Definition chain_walk_list (l : list box) : Prop :=
  match l with [] => True | b :: r => chain_walk b r end.

(** Reversing one arm and running the other from the join is again a walk,
    since neighbouring boxes are neighbours in either order. *)
Lemma chain_walk_rev_app :
  forall l b m,
    chain_walk b l -> chain_walk b m ->
    chain_walk_list (rev l ++ b :: m).
Proof.
  induction l as [|x l IH]; intros b m Hl Hm; [exact Hm|].
  destruct Hl as [Hbx Hxl].
  cbn [rev]; rewrite <- app_assoc; cbn [app].
  apply (IH x (b :: m) Hxl).
  split; [apply cadj_sym; exact Hbx | exact Hm].
Qed.

(** So the extracted component is a run of neighbouring boxes. *)
Theorem comp_from_walk : forall b, chain_walk_list (comp_from b).
Proof.
  intros b; unfold comp_from.
  apply chain_walk_rev_app; apply tail_of_walk.
Qed.

(** It is never empty, since it runs through its own start. *)
Lemma comp_from_cons :
  forall b, exists b0 l, comp_from b = b0 :: l.
Proof.
  intros b; unfold comp_from.
  destruct (rev (arm_back b)) as [|x r] eqn:E.
  - exists b, (arm_fwd b); reflexivity.
  - exists x, (r ++ b :: arm_fwd b); reflexivity.
Qed.

Lemma In_comp_from_start : forall b, In b (comp_from b).
Proof.
  intros b; unfold comp_from; apply in_or_app; right; left; reflexivity.
Qed.

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

Lemma In_rev_arm_back :
  forall b x, In x (rev (arm_back b)) -> In x (arm_back b).
Proof.
  intros b x Hx.
  apply (Permutation_in x (Permutation_sym (Permutation_rev (arm_back b))));
    exact Hx.
Qed.

(** Neither arm revisits the start or the other arm, so the whole component is
    repeat-free. *)
Theorem comp_from_nodup : forall b, NoDup (comp_from b).
Proof.
  intros b; unfold comp_from; apply NoDup_app_disj.
  - apply (Permutation_NoDup (Permutation_rev (arm_back b))).
    apply tail_of_nodup.
  - constructor;
      [apply (tail_of_avoids (length U) [b] b b); left; reflexivity
       | apply tail_of_nodup].
  - intros x Hx Hy.
    exact (tail_of_avoids (length U) (b :: arm_fwd b) b x Hy
             (In_rev_arm_back b x Hx)).
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
  intros b Hb x Hx; unfold comp_from in Hx.
  apply in_app_or in Hx; destruct Hx as [Hx | Hx].
  - apply (tail_of_incl (length U) (b :: arm_fwd b) b).
    exact (In_rev_arm_back b x Hx).
  - destruct Hx as [<- | Hx];
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

(** * The run is maximal *)

(** A walk can only be the whole component when no box has a third neighbour to
    branch into. On a loony board that is automatic: a box in a chain or a loop
    has exactly two of its four walls undrawn. Under that bound the extracted
    run is closed under adjacency, and since it holds the box it started from
    it is the entire connected component. *)

Lemma pick_none :
  forall vis b,
    pick vis b = None ->
    forall c, In c U -> A b c = true -> In c vis.
Proof.
  intros vis b H c HU HA.
  destruct (bmem c vis) eqn:E; [apply bmem_true_iff; exact E|].
  exfalso; unfold pick in H.
  destruct (filter (fun x => A b x && negb (bmem x vis))%bool U) eqn:Ef;
    [|discriminate].
  assert (Hin : In c (filter (fun x => A b x && negb (bmem x vis))%bool U))
    by (apply filter_In; split; [exact HU | rewrite HA, E; reflexivity]).
  rewrite Ef in Hin; destruct Hin.
Qed.

(** With at most two neighbours, a third one has to coincide with one of the
    first two. *)
Lemma nbr_pigeonhole :
  forall b x y z,
    NoDup U ->
    (length (filter (A b) U) <= 2)%nat ->
    In x U -> In y U -> In z U ->
    A b x = true -> A b y = true -> A b z = true ->
    x <> y -> x <> z -> y = z.
Proof.
  intros b x y z HU Hdeg Hx Hy Hz Hax Hay Haz Hxy Hxz.
  destruct (beqb y z) eqn:Eyz; [apply beqb_true_iff; exact Eyz|].
  exfalso.
  assert (Hyz : y <> z)
    by (intros ->; rewrite beqb_refl in Eyz; discriminate).
  assert (Hnd : NoDup [x; y; z]).
  { constructor; [cbn; intros [H | [H | []]]; congruence|].
    constructor; [cbn; intros [H | []]; congruence|].
    constructor; [cbn; intros [] | constructor]. }
  assert (Hincl : incl [x; y; z] (filter (A b) U)).
  { intros w Hw; apply filter_In.
    destruct Hw as [<- | [<- | [<- | []]]]; split; assumption. }
  pose proof (NoDup_incl_length Hnd Hincl) as Hlen; cbn [length] in Hlen; lia.
Qed.

(** The fuel outlasts the walk: each step banks a fresh box of the board, so a
    walk that still has somewhere to go still has fuel to get there. *)
Lemma fuel_remains :
  forall vis d,
    NoDup vis -> incl vis U -> In d U -> ~ In d vis ->
    (length vis < length U)%nat.
Proof.
  intros vis d Hnd Hincl HdU Hdv.
  destruct (Nat.le_gt_cases (length U) (length vis)) as [Hle | Hlt]; [|lia].
  exfalso; apply Hdv.
  apply (NoDup_length_incl Hnd Hle Hincl); exact HdU.
Qed.

(** The forward walk leaves nothing adjacent to it outside what it has seen. *)
Lemma tail_of_closed :
  forall fuel vis b,
    NoDup U ->
    (forall c, In c U -> (length (filter (A c) U) <= 2)%nat) ->
    (forall x y, A x y = A y x) ->
    NoDup vis -> incl vis U ->
    (length U < length vis + fuel)%nat ->
    In b U -> In b vis ->
    forall x y,
      In x (tail_of fuel vis b) -> In y U -> A x y = true ->
      In y (vis ++ tail_of fuel vis b).
Proof.
  induction fuel as [|f IH];
    intros vis b HU Hdeg Hsym Hnd Hincl Hfuel HbU Hbv x y Hx Hy HA;
    cbn [tail_of] in Hx |- *; [destruct Hx|].
  destruct (pick vis b) as [c|] eqn:Ep; [|destruct Hx].
  destruct (pick_spec vis b c Ep) as [HcU [HAbc Hcv]].
  assert (Hnd' : NoDup (c :: vis)) by (constructor; assumption).
  assert (Hincl' : incl (c :: vis) U)
    by (intros w [<- | Hw]; [exact HcU | apply Hincl; exact Hw]).
  assert (Hfuel' : (length U < length (c :: vis) + f)%nat)
    by (cbn [length]; lia).
  destruct Hx as [<- | Hx].
  - (* the box just picked: its neighbours are the one behind and the next *)
    destruct (pick (c :: vis) c) as [d|] eqn:Ed.
    + destruct (pick_spec (c :: vis) c d Ed) as [HdU [HAcd Hdv]].
      assert (Hbd : b <> d) by (intros <-; apply Hdv; right; exact Hbv).
      assert (HAcb : A c b = true) by (rewrite Hsym; exact HAbc).
      destruct (beqb y b) eqn:Eyb.
      * apply beqb_true_iff in Eyb; subst y.
        apply in_or_app; left; exact Hbv.
      * assert (Hyb : b <> y)
          by (intros <-; rewrite beqb_refl in Eyb; discriminate).
        assert (Hyd : d = y)
          by (apply (nbr_pigeonhole c b d y HU (Hdeg c HcU) HbU HdU Hy
                       HAcb HAcd HA Hbd Hyb)).
        subst d.
        (* the walk still has fuel, so it really does step to [y] *)
        destruct f as [|f'].
        -- exfalso.
           pose proof (fuel_remains (c :: vis) y Hnd' Hincl' Hy Hdv) as Hlt.
           cbn [length] in Hlt, Hfuel; lia.
        -- apply in_or_app; right; right.
           cbn [tail_of]; rewrite Ed; left; reflexivity.
    + assert (Hin : In y (c :: vis))
        by (apply (pick_none (c :: vis) c Ed y Hy); exact HA).
      destruct Hin as [<- | Hin].
      * apply in_or_app; right; left; reflexivity.
      * apply in_or_app; left; exact Hin.
  - (* further along: the induction hypothesis covers it *)
    assert (Hrec : In y ((c :: vis) ++ tail_of f (c :: vis) c))
      by (apply (IH (c :: vis) c HU Hdeg Hsym Hnd' Hincl' Hfuel' HcU
                   (or_introl eq_refl) x y Hx Hy HA)).
    apply in_app_or in Hrec; destruct Hrec as [Hrec | Hrec].
    + destruct Hrec as [<- | Hrec].
      * apply in_or_app; right; left; reflexivity.
      * apply in_or_app; left; exact Hrec.
    + apply in_or_app; right; right; exact Hrec.
Qed.

(** * The component is closed under adjacency *)

Lemma tail_of_head :
  forall fuel vis b d,
    (1 <= fuel)%nat -> pick vis b = Some d ->
    exists r, tail_of fuel vis b = d :: r.
Proof.
  intros [|f] vis b d Hf Hp; [lia|].
  cbn [tail_of]; rewrite Hp; eexists; reflexivity.
Qed.

Lemma In_length_pos : forall b, In b U -> (1 <= length U)%nat.
Proof. intros b H; destruct U; [destruct H | cbn [length]; lia]. Qed.

Theorem comp_from_closed :
  forall b,
    NoDup U ->
    (forall c, In c U -> (length (filter (A c) U) <= 2)%nat) ->
    (forall x y, A x y = A y x) ->
    In b U ->
    forall x y,
      In x (comp_from b) -> In y U -> A x y = true -> In y (comp_from b).
Proof.
  intros b HU Hdeg Hsym HbU x y Hx Hy HA.
  assert (Hfwd : forall z, In z (arm_fwd b) -> In z (comp_from b)).
  { intros z Hz; unfold comp_from; apply in_or_app; right; right; exact Hz. }
  assert (Hback : forall z, In z (arm_back b) -> In z (comp_from b)).
  { intros z Hz; unfold comp_from; apply in_or_app; left.
    apply (Permutation_in z (Permutation_rev (arm_back b))); exact Hz. }
  assert (Hb1 : NoDup [b]) by (constructor; [intros [] | constructor]).
  assert (Hi1 : incl [b] U) by (intros w [<- | []]; exact HbU).
  assert (Hf1 : (length U < length [b] + length U)%nat) by (cbn [length]; lia).
  assert (HndF : NoDup (b :: arm_fwd b)).
  { constructor;
      [apply (tail_of_avoids (length U) [b] b b); left; reflexivity
       | apply tail_of_nodup]. }
  assert (HiF : incl (b :: arm_fwd b) U).
  { intros w [<- | Hw];
      [exact HbU | apply (tail_of_incl (length U) [b] b); exact Hw]. }
  assert (HfF : (length U < length (b :: arm_fwd b) + length U)%nat)
    by (cbn [length]; lia).
  unfold comp_from in Hx; apply in_app_or in Hx; destruct Hx as [Hx | Hx].
  - (* x lies on the backward arm *)
    assert (Hx' : In x (arm_back b)) by (apply In_rev_arm_back; exact Hx).
    assert (Hin : In y ((b :: arm_fwd b) ++ arm_back b)).
    { unfold arm_back in Hx' |- *.
      apply (tail_of_closed (length U) (b :: arm_fwd b) b HU Hdeg Hsym
               HndF HiF HfF HbU (or_introl eq_refl) x y Hx' Hy HA). }
    apply in_app_or in Hin; destruct Hin as [Hin | Hin];
      [| apply Hback; exact Hin].
    destruct Hin as [<- | Hin];
      [apply In_comp_from_start | apply Hfwd; exact Hin].
  - destruct Hx as [<- | Hx].
    + (* x is the box the walk started from *)
      destruct (pick (b :: arm_fwd b) b) as [d|] eqn:Ed.
      * destruct (pick_spec (b :: arm_fwd b) b d Ed) as [HdU [HAbd Hdv]].
        assert (HL1 : (1 <= length U)%nat) by (apply (In_length_pos b); exact HbU).
        assert (Hdin : In d (arm_back b)).
        { unfold arm_back.
          destruct (tail_of_head (length U) (b :: arm_fwd b) b d HL1 Ed)
            as [r Hr]; rewrite Hr; left; reflexivity. }
        destruct (pick [b] b) as [c|] eqn:Ec.
        -- destruct (pick_spec [b] b c Ec) as [HcU [HAbc _]].
           assert (Hcin : In c (arm_fwd b)).
           { unfold arm_fwd.
             destruct (tail_of_head (length U) [b] b c HL1 Ec) as [r Hr];
               rewrite Hr; left; reflexivity. }
           assert (Hcd : c <> d)
             by (intros <-; apply Hdv; right; exact Hcin).
           destruct (beqb y c) eqn:Eyc.
           ++ apply beqb_true_iff in Eyc; subst y; apply Hfwd; exact Hcin.
           ++ assert (Hyc : c <> y)
                by (intros <-; rewrite beqb_refl in Eyc; discriminate).
              assert (Hyd : d = y)
                by (apply (nbr_pigeonhole b c d y HU (Hdeg b HbU) HcU HdU Hy
                             HAbc HAbd HA Hcd Hyc)).
              subst d; apply Hback; exact Hdin.
        -- (* nothing leaves the start at all *)
           assert (Hin : In y [b])
             by (apply (pick_none [b] b Ec y Hy HA)).
           destruct Hin as [<- | []]; apply In_comp_from_start.
      * assert (Hin : In y (b :: arm_fwd b))
          by (apply (pick_none (b :: arm_fwd b) b Ed y Hy HA)).
        destruct Hin as [<- | Hin];
          [apply In_comp_from_start | apply Hfwd; exact Hin].
    + (* x lies on the forward arm *)
      assert (Hin : In y ([b] ++ arm_fwd b)).
      { unfold arm_fwd in Hx |- *.
        apply (tail_of_closed (length U) [b] b HU Hdeg Hsym
                 Hb1 Hi1 Hf1 HbU (or_introl eq_refl) x y Hx Hy HA). }
      apply in_app_or in Hin; destruct Hin as [Hin | Hin].
      * destruct Hin as [<- | []]; apply In_comp_from_start.
      * apply Hfwd; exact Hin.
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
  - destruct (comp_from_cons (b :: rest) A b) as [b0 [l Hb0]].
    exists b0, l; split; [exact Hb0 | split].
    + pose proof (comp_from_walk (b :: rest) A A_cadj b) as Hw.
      rewrite Hb0 in Hw; exact Hw.
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

    The bridge between the two halves is the last section of this file. The
    turns remaining once the loony endgame begins are not the components: a
    controller who declines spends a second turn-ending move on the handout,
    and [eturns_components] is the corrected count. *)

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
      assert (Hb : In b c) by (unfold c; apply In_comp_from_start).
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

(** * Keeping the short components *)

(** [loops_of] and [chains_of] drop anything under three boxes, so a board
    holding a chain of one or two presents a position that accounts for fewer
    boxes than are open. [schains_of] keeps them: everything that is not a
    genuine loop is a chain, however short, and [decompose_ssize] then accounts
    for every open box with no hypothesis on the board at all. What comes out
    is [swf] rather than [wf], which is exactly the class [ShortChains] settles. *)

Definition schains_of (A : box -> box -> bool) (U : list box)
  : list (list box) :=
  filter (fun c => negb (cyclicb c && (3 <=? length c)) && (1 <=? length c))%bool
         (decompose A U).

Lemma comps_position_swf :
  forall loops chains,
    (forall bs, In bs loops -> cyclic bs /\ (3 <= length bs)%nat) ->
    (forall bs, In bs chains -> (1 <= length bs)%nat) ->
    swf (comps_position loops chains).
Proof.
  intros loops chains Hl Hc; unfold swf, comps_position.
  apply Forall_app; split; rewrite Forall_map, Forall_forall.
  - intros bs Hbs; destruct (Hl bs Hbs) as [Hcyc H3].
    cbn [swf_comp]; destruct (loop_comp_wf bs Hcyc H3) as [H4 Hev].
    split; assumption.
  - intros bs Hbs; cbn [swf_comp]; apply Hc; exact Hbs.
Qed.

(** Every piece the peeling returns holds at least the box it started from. *)
Lemma peel_nonnil :
  forall A fuel rem c, In c (peel A fuel rem) -> c <> [].
Proof.
  intros A; induction fuel as [|f IH]; intros rem c Hc; simpl in Hc;
    [destruct Hc|].
  destruct rem as [|b rest]; [destruct Hc|].
  destruct Hc as [<- | Hc].
  - intros Hnil.
    pose proof (In_comp_from_start (b :: rest) A b) as Hin.
    rewrite Hnil in Hin; destruct Hin.
  - apply (IH (drop_all (comp_from (b :: rest) A b) (b :: rest)) c); exact Hc.
Qed.

Theorem decompose_swf :
  forall A U, swf (comps_position (loops_of A U) (schains_of A U)).
Proof.
  intros A U; apply comps_position_swf.
  - intros c Hc; unfold loops_of in Hc; apply filter_In in Hc.
    destruct Hc as [_ H]; apply andb_true_iff in H; destruct H as [H1 H2].
    split; [apply cyclicb_cyclic; exact H1 | apply Nat.leb_le; exact H2].
  - intros c Hc; unfold schains_of in Hc; apply filter_In in Hc.
    destruct Hc as [_ H]; apply andb_true_iff in H; destruct H as [_ H2].
    apply Nat.leb_le; exact H2.
Qed.

(** Nothing is dropped now, so the two lists split the decomposition. *)
Lemma sloony_split :
  forall A U,
    Permutation (loops_of A U ++ schains_of A U) (decompose A U).
Proof.
  intros A U; unfold loops_of, schains_of.
  apply filter_split_perm.
  - intros x Hx.
    assert (Hne : x <> []) by (apply (peel_nonnil A (length U) U); exact Hx).
    assert (Hlen : (1 <=? length x)%nat = true)
      by (destruct x; [contradiction | apply Nat.leb_le; cbn [length]; lia]).
    destruct (cyclicb x && (3 <=? length x))%bool eqn:E.
    + left; exact E.
    + right; cbv beta.
      apply andb_true_iff; split;
        [apply negb_true_iff; exact E | exact Hlen].
  - intros x Hx Hp; cbv beta in Hp |- *.
    apply andb_false_iff; left; apply negb_false_iff; exact Hp.
Qed.

(** So the position accounts for every open box, whatever the board looks
    like. *)
Theorem decompose_ssize :
  forall A U,
    NoDup U ->
    (size (comps_position (loops_of A U) (schains_of A U)) = length U)%nat.
Proof.
  intros A U HU; apply decomp_size.
  eapply Permutation_trans; [| apply decompose_perm; exact HU].
  apply perm_concat, sloony_split.
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

(** * The board adjacency is symmetric *)

Lemma cadjb_sym : forall b c, cadjb b c = cadjb c b.
Proof.
  intros [r1 c1] [r2 c2]; unfold cadjb; cbn [fst snd].
  rewrite (Nat.eqb_sym r2 r1), (Nat.eqb_sym c2 c1).
  rewrite (orb_comm (c2 =? S c1) (c1 =? S c2)).
  rewrite (orb_comm (r2 =? S r1) (r1 =? S r2)).
  reflexivity.
Qed.

Lemma In_shared :
  forall b c e, In e (shared b c) <-> In e (box_edges b) /\ In e (box_edges c).
Proof.
  intros b c e; unfold shared; rewrite filter_In; split.
  - intros [H1 H2]; split; [exact H1|].
    apply existsb_exists in H2; destruct H2 as [f [Hf He]].
    apply edge_eqb_true_iff in He; subst f; exact Hf.
  - intros [H1 H2]; split; [exact H1|].
    apply existsb_exists; exists e; split; [exact H2 | apply edge_eqb_refl].
Qed.

Lemma existsb_same_elems :
  forall (f : edge -> bool) l1 l2,
    (forall x, In x l1 <-> In x l2) -> existsb f l1 = existsb f l2.
Proof.
  intros f l1 l2 H.
  destruct (existsb f l1) eqn:E1; destruct (existsb f l2) eqn:E2;
    try reflexivity.
  - apply existsb_exists in E1; destruct E1 as [x [Hx Hf]].
    assert (Hbad : existsb f l2 = true)
      by (apply existsb_exists; exists x; split; [apply H; exact Hx | exact Hf]).
    congruence.
  - apply existsb_exists in E2; destruct E2 as [x [Hx Hf]].
    assert (Hbad : existsb f l1 = true)
      by (apply existsb_exists; exists x; split; [apply H; exact Hx | exact Hf]).
    congruence.
Qed.

(** Two boxes are joined by the same wall whichever way round they are named. *)
Lemma adj_board_sym : forall d b c, adj_board d b c = adj_board d c b.
Proof.
  intros d b c; unfold adj_board.
  rewrite (cadjb_sym b c).
  rewrite (existsb_same_elems (fun e => negb (emem e d))
             (shared b c) (shared c b))
    by (intros x; rewrite !In_shared; tauto).
  destruct (cadjb c b), (box_done d b), (box_done d c),
           (existsb (fun e => negb (emem e d)) (shared c b)); reflexivity.
Qed.

(** * Components of a board are whole *)

(** A box of a chain or a loop has exactly two of its four walls undrawn, so on
    a position the endgame theory applies to, every open box has at most two
    open neighbours. Under that bound the extracted run is closed under
    adjacency: nothing joined to it was left outside. *)
Definition loony_degrees (m n : nat) (d : list edge) : Prop :=
  forall c, In c (open_boxes m n d) ->
    (length (filter (adj_board d c) (open_boxes m n d)) <= 2)%nat.

Theorem board_comp_from_closed :
  forall m n d b,
    loony_degrees m n d ->
    In b (open_boxes m n d) ->
    forall x y,
      In x (comp_from (open_boxes m n d) (adj_board d) b) ->
      In y (open_boxes m n d) -> adj_board d x y = true ->
      In y (comp_from (open_boxes m n d) (adj_board d) b).
Proof.
  intros m n d b Hdeg Hb x y Hx Hy HA.
  apply (comp_from_closed (open_boxes m n d) (adj_board d) b
           (NoDup_open_boxes m n d) Hdeg (adj_board_sym d) Hb x y Hx Hy HA).
Qed.

(** And it holds the box it started from, so it is exactly the set of boxes
    joined to that one: the extractor returns whole components, not fragments
    of them. *)
Corollary board_comp_from_component :
  forall m n d b,
    loony_degrees m n d ->
    In b (open_boxes m n d) ->
    In b (comp_from (open_boxes m n d) (adj_board d) b) /\
    incl (comp_from (open_boxes m n d) (adj_board d) b) (open_boxes m n d) /\
    (forall x y,
       In x (comp_from (open_boxes m n d) (adj_board d) b) ->
       In y (open_boxes m n d) -> adj_board d x y = true ->
       In y (comp_from (open_boxes m n d) (adj_board d) b)).
Proof.
  intros m n d b Hdeg Hb; repeat split.
  - apply In_comp_from_start.
  - apply comp_from_incl; exact Hb.
  - apply (board_comp_from_closed m n d b Hdeg Hb).
Qed.

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

(** * The board, with its short components kept *)

(** [board_position] drops any component under three boxes, so it accounts for
    every open box only on a board where none is that short. [sboard_position]
    keeps them, and accounts for every open box on any board at all. It is
    [swf] rather than [wf], which is the class [GameTrees.ShortChains] settles:
    [ShortChains.svalue_closed] computes its value and
    [ShortChains.svalue_gt4_iff] answers the controller's loop test on it. *)
Definition sboard_chains (m n : nat) (d : list edge) : list (list box) :=
  schains_of (adj_board d) (open_boxes m n d).

Definition sboard_position (m n : nat) (d : list edge) : position :=
  comps_position (board_loops m n d) (sboard_chains m n d).

Theorem sboard_position_swf : forall m n d, swf (sboard_position m n d).
Proof.
  intros m n d; unfold sboard_position, board_loops, sboard_chains.
  apply decompose_swf.
Qed.

(** No hypothesis on the board is needed: every open box is accounted for. *)
Theorem sboard_position_covers :
  forall m n d,
    (size (sboard_position m n d) = length (open_boxes m n d))%nat.
Proof.
  intros m n d; unfold sboard_position, board_loops, sboard_chains.
  apply decompose_ssize, NoDup_open_boxes.
Qed.

(** So at any state legal play reaches, the rest of the game is a position the
    capped theory computes, carrying exactly the boxes still open. *)
Corollary reachable_short :
  forall m n s ms,
    legal m n s ms ->
    swf (sboard_position m n (laid (run m n s ms))) /\
    (size (sboard_position m n (laid (run m n s ms)))
     = length (open_boxes m n (laid (run m n s ms))))%nat.
Proof.
  intros m n s ms _; split;
    [apply sboard_position_swf | apply sboard_position_covers].
Qed.

(** ****************************************************************** *)
(** The bridge between the two halves of the long chain rule.

    [long_chain_rule] gives the turn count of a completed game from the dots
    and the doublecrosses, and [loony_opener_parity] gives that a loony
    position of [k] components is won by its opener exactly when [k] is odd.
    Read together they suggest that the turns remaining once the endgame begins
    are the components.

    That is false. A turn of the endgame is an opening, and the controller who
    declines spends a second turn-ending move on the handout, which is also
    where the doublecrosses come from. This section models the endgame play
    with the controller's decision recorded, and proves
    [eturns_components]: the turns are the components plus the declines.
    [eturns_eq_components_iff] is the exact condition under which the reading
    holds, and [decline_can_be_strict] shows it fails already on two
    three-chains, where declining is strictly better than taking all.

    What the parity of the components really governs is [etakealls]: control
    passes exactly on a component taken whole, so [opener_after] is the parity
    of those, not of the turns. *)

(** * The controller's decision *)

(** Handed an open component the controller either takes it whole, giving up
    control, or leaves the handout and keeps it. *)
Inductive decision : Type := TakeAll | Decline.

Definition estep : Type := (comp * decision)%type.

Definition is_decline (p : estep) : bool :=
  match snd p with Decline => true | TakeAll => false end.

Definition declines (ps : list estep) : nat :=
  length (filter is_decline ps).

Definition takealls (ps : list estep) : nat :=
  length (filter (fun p => negb (is_decline p)) ps).

Lemma declines_takealls :
  forall ps, (takealls ps + declines ps = length ps)%nat.
Proof.
  induction ps as [|p ps IH]; [reflexivity|].
  unfold declines, takealls in *; simpl.
  destruct (is_decline p); simpl; lia.
Qed.

(** * A play of the endgame *)

(** Each turn opens one component of what is left; the play ends when nothing
    remains. *)
Fixpoint eplay (G : position) (ps : list estep) : Prop :=
  match ps with
  | [] => G = []
  | p :: r => exists rest, In (fst p, rest) (selections G) /\ eplay rest r
  end.

Lemma eplay_nil : forall G, eplay G [] <-> G = [].
Proof. intros G; simpl; split; auto. Qed.

(** A play removes one component per turn, so it has as many turns as the
    position has components. *)
Theorem eplay_length :
  forall ps G, eplay G ps -> length ps = length G.
Proof.
  induction ps as [|p ps IH]; intros G H; simpl in H.
  - subst G; reflexivity.
  - destruct H as [rest [Hin Hr]].
    simpl length; rewrite (IH rest Hr).
    pose proof (selections_length G (fst p, rest) Hin) as Hl; simpl in Hl; lia.
Qed.

(** Every position admits a play, whatever the controller decides. *)
Theorem eplay_exists :
  forall G (d : comp -> decision),
    exists ps, eplay G ps /\ length ps = length G.
Proof.
  assert (Haux : forall n G (d : comp -> decision),
            (length G <= n)%nat -> exists ps, eplay G ps).
  { induction n as [|n IH]; intros G d Hn.
    - assert (HG : G = []) by (destruct G; simpl in Hn; [reflexivity | lia]).
      subst G; exists []; reflexivity.
    - destruct G as [|C G]; [exists []; reflexivity|].
      destruct (IH G d ltac:(simpl in Hn; lia)) as [ps Hps].
      exists ((C, d C) :: ps); simpl.
      exists G; split; [left; reflexivity | exact Hps]. }
  intros G d; destruct (Haux (length G) G d ltac:(lia)) as [ps Hps].
  exists ps; split; [exact Hps | apply eplay_length; exact Hps].
Qed.

(** * Counting the turns *)

(** A turn ends on a move that takes no box. Opening a component is such a
    move, and so is the handout a declining controller leaves; taking a
    component whole is not, since the last box keeps the move. *)
Definition eturns (ps : list estep) : nat := (length ps + declines ps)%nat.

(** The corrected bridge: the turns of an endgame are its components together
    with its declines. *)
Theorem eturns_components :
  forall ps G, eplay G ps -> eturns ps = (length G + declines ps)%nat.
Proof.
  intros ps G H; unfold eturns; rewrite (eplay_length ps G H); reflexivity.
Qed.

(** So the turns are the components exactly when nothing is declined, which is
    the condition the two halves above leave unstated. *)
Theorem eturns_eq_components_iff :
  forall ps G, eplay G ps -> (eturns ps = length G <-> declines ps = 0%nat).
Proof.
  intros ps G H; rewrite (eturns_components ps G H); lia.
Qed.

Corollary eturns_ge_components :
  forall ps G, eplay G ps -> (length G <= eturns ps)%nat.
Proof.
  intros ps G H; rewrite (eturns_components ps G H); lia.
Qed.

(** * Control *)

(** Control passes exactly when a component is taken whole. *)
Fixpoint opener_after (start : bool) (ps : list estep) : bool :=
  match ps with
  | [] => start
  | p :: r => opener_after (if is_decline p then start else negb start) r
  end.

Lemma opener_after_parity :
  forall ps start, opener_after start ps = xorb start (Nat.odd (takealls ps)).
Proof.
  induction ps as [|p ps IH]; intros start; simpl.
  - unfold takealls; simpl; destruct start; reflexivity.
  - unfold takealls in *; simpl.
    destruct (is_decline p); simpl.
    + rewrite IH; reflexivity.
    + rewrite IH, Nat.odd_succ, <- Nat.negb_odd.
      destruct start; destruct (Nat.odd (length (filter (fun q => negb (is_decline q)) ps)));
        reflexivity.
Qed.

(** So the player left to open at the end of the endgame is fixed by the parity
    of the components taken whole, and not by the parity of the turns. *)
Theorem opener_after_takealls :
  forall ps start, opener_after start ps = xorb start (Nat.odd (takealls ps)).
Proof. exact opener_after_parity. Qed.

(** When nothing is declined the two parities agree, and only then. *)
Theorem opener_after_of_no_decline :
  forall ps G start,
    eplay G ps -> declines ps = 0%nat ->
    opener_after start ps = xorb start (Nat.odd (length G)).
Proof.
  intros ps G start Hp Hd.
  rewrite opener_after_parity.
  pose proof (declines_takealls ps) as Ht.
  rewrite (eplay_length ps G Hp) in Ht; rewrite Hd in Ht.
  replace (takealls ps) with (length G) by lia; reflexivity.
Qed.

(** * Doublecrosses *)

(** A declined chain hands over two boxes, taken by one move that completes
    both: one doublecross. A declined loop hands over four, taken by two such
    moves. *)
Definition edx (C : comp) : nat := Nat.div2 (hand C).

Lemma edx_chain : forall k, edx (Chain k) = 1%nat.
Proof. reflexivity. Qed.

Lemma edx_loop : forall k, edx (Loop k) = 2%nat.
Proof. reflexivity. Qed.

Fixpoint eextra (ps : list estep) : nat :=
  match ps with
  | [] => 0%nat
  | p :: r => ((if is_decline p then edx (fst p) else 0) + eextra r)%nat
  end.

(** A component taken whole yields no doublecross, and a declined one yields
    one or two, so the doublecrosses bracket the declines. *)
Theorem eextra_bounds :
  forall ps, (declines ps <= eextra ps <= 2 * declines ps)%nat.
Proof.
  induction ps as [|p ps IH]; [simpl; unfold declines; simpl; lia|].
  unfold declines in *; simpl.
  destruct (is_decline p) eqn:E; simpl.
  - destruct (fst p) as [k | k]; simpl; lia.
  - lia.
Qed.

(** In particular the endgame doublecrosses vanish exactly when nothing is
    declined, which by [eturns_eq_components_iff] is exactly when the turns are
    the components. *)
Theorem eextra_zero_iff :
  forall ps, eextra ps = 0%nat <-> declines ps = 0%nat.
Proof.
  intros ps; pose proof (eextra_bounds ps); lia.
Qed.

Corollary eturns_eq_components_iff_no_doublecross :
  forall ps G, eplay G ps -> (eturns ps = length G <-> eextra ps = 0%nat).
Proof.
  intros ps G H; rewrite (eturns_eq_components_iff ps G H), eextra_zero_iff.
  reflexivity.
Qed.

(** With no doublecrosses the endgame turns are the components and control is
    read off their parity: this is the reading the two halves suggest, with the
    hypothesis it needs made explicit. *)
Theorem bridge_when_no_doublecross :
  forall ps G start,
    eplay G ps -> eextra ps = 0%nat ->
    eturns ps = length G /\
    opener_after start ps = xorb start (Nat.odd (length G)).
Proof.
  intros ps G start Hp He.
  apply eextra_zero_iff in He.
  split.
  - apply (eturns_eq_components_iff ps G Hp); exact He.
  - apply (opener_after_of_no_decline ps G start Hp He).
Qed.

(** * Declining is not exceptional *)

Open Scope Z_scope.

(** On two three-chains the controller strictly prefers to decline: taking the
    opened chain whole is worth nothing to her, declining is worth two. *)
Theorem decline_can_be_strict :
  give_up_control (Chain 3) (value [Chain 3]) = 0 /\
  keep_control (Chain 3) (value [Chain 3]) = 2 /\
  give_up_control (Chain 3) (value [Chain 3])
    < keep_control (Chain 3) (value [Chain 3]).
Proof.
  rewrite value_single; cbn [csize].
  unfold give_up_control, keep_control; cbn [csize hand].
  repeat split; lia.
Qed.

(** And that preference is the value: opening either component of two
    three-chains is worth two, which is what declining secures. *)
Theorem two_three_chains_declines :
  value [Chain 3; Chain 3] = 2 /\
  vopen (Chain 3) (value [Chain 3]) = keep_control (Chain 3) (value [Chain 3]).
Proof.
  split.
  - vm_compute; reflexivity.
  - apply controller_keeps.
    rewrite value_single; cbn [csize hand]; lia.
Qed.

(** So the play the endgame actually takes on that position declines, its turns
    exceed its components, and the proposal fails there. *)
Theorem proposal_fails :
  exists (G : position) (ps : list estep),
    eplay G ps /\ declines ps <> 0%nat /\ eturns ps <> length G.
Proof.
  exists [Chain 3; Chain 3], [(Chain 3, Decline); (Chain 3, TakeAll)].
  repeat split.
  - simpl; exists [Chain 3]; split; [left; reflexivity|].
    exists (@nil comp); split; [left; reflexivity | reflexivity].
  - unfold declines; simpl; discriminate.
  - unfold eturns, declines; simpl; discriminate.
Qed.

(** * What survives *)

(** The half of the rule that does hold without qualification: the components
    are the turns of the Nimstring game, where nothing is scored and so nothing
    can be declined. That is [Decomposition.opening_run], and every [eplay] in
    which the controller always takes whole is one. *)
Theorem eplay_all_takeall_is_opening_run :
  forall ps G,
    eplay G ps -> declines ps = 0%nat ->
    (length ps = length G /\ eturns ps = length ps).
Proof.
  intros ps G Hp Hd; split.
  - apply eplay_length; exact Hp.
  - unfold eturns; lia.
Qed.

(** And the corrected statement of the whole rule at the level of the endgame:
    the turns are the components plus the declines, the doublecrosses bracket
    the declines, and control is the parity of what was taken whole. *)
Theorem long_chain_bridge :
  forall ps G start,
    eplay G ps ->
    eturns ps = (length G + declines ps)%nat /\
    (declines ps <= eextra ps <= 2 * declines ps)%nat /\
    opener_after start ps = xorb start (Nat.odd (takealls ps)) /\
    (takealls ps + declines ps = length G)%nat.
Proof.
  intros ps G start Hp; repeat split.
  - apply (eturns_components ps G Hp).
  - apply eextra_bounds.
  - apply eextra_bounds.
  - apply opener_after_parity.
  - pose proof (declines_takealls ps) as H.
    rewrite (eplay_length ps G Hp) in H; exact H.
Qed.
