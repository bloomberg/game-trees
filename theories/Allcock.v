(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Allcock's Theorem 1.1.

    The standard move opens a three-chain if one is present, otherwise a
    shortest loop, otherwise a shortest chain. The strategy departs from it and
    opens the shortest loop in three named cases:

      (i)   c(G) >= 2 and G is a three-chain together with one or more loops;
      (ii)  c(G) in {0, 1, -1} and G holds a four-loop, and what is left after
            removing one four-loop is not exactly three three-chains;
      (iii) c(G) <= -2 and G holds a four-loop and a three-chain, and what is
            left after removing one of each has size divisible by four and no
            three-chains.

    [GameTrees.DotsAndBoxes] states the strategy and checks it a position at a
    time through [allcock_okb]. This file proves it.

    [shortest_of_min] is what the original development leaves out and every
    branch needs: the move [shortest_of] names really is a shortest one. On that
    footing [allcock_case_i_optimal], [allcock_case_ii_complete] and
    [allcock_case_iii_optimal] settle the three named cases, and
    [allcock_named_cases_optimal] is the three together, so the computational
    check is redundant wherever one of them fires.

    Outside them the standard move applies. [standard_move_no3_complete] proves
    it optimal on every position holding no three-chain, with no hypothesis
    beyond wellformedness. Where a three-chain is present the block reduces by
    [standard_move_reduces] to an identity between the closed form at the
    position and the opening of the closed form at what the move leaves behind,
    and [allcock_move_optimal] is the strategy stated against that identity. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Sorting.Permutation.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.ShortChains.

Import ListNotations.

Open Scope Z_scope.

(** ****************************************************************** *)
(** What the opener strategy actually names.

    [DotsAndBoxes.shortest_of] carries only a membership lemma, which says the
    move it names is legal but not that it is shortest. Every branch of
    Allcock's Theorem 1.1 turns on the length of the component opened, so the
    minimality is needed before any of them can be proved.

    [shortest_loop_is_four] is the first consequence: on a position holding a
    four-loop, the shortest loop is a four-loop, since no loop is shorter. That
    identifies the move named in Allcock's cases (ii) and (iii). *)

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

(** ****************************************************************** *)
(** Two further cases of Allcock's Theorem 1.1.

    [GameTrees.DotsAndBoxes] proves case (i) of Theorem 1.1 and the criterion
    [open_optimal_of_step] behind it, and leaves the rest checked position by
    position. [open_4loop_optimal] settles the regime of case (ii): where a
    four-loop sits beside a component that is neither a three-chain nor a
    four-loop, and the controlled value is at least minus two, opening the
    four-loop is optimal. [open_3chain_optimal] settles the standard move
    wherever two three-chains are present. *)

(** * Case (ii): opening a four-loop *)

(** A four-loop beside a component that is neither a three-chain nor a
    four-loop leaves the terminal bonus alone when it is removed, so the
    controlled value of the remainder is four higher. *)
Lemma four_loop_rest :
  forall G rest,
    wf G -> In (Loop 4, rest) (selections G) ->
    only34 G = false ->
    tb (Loop 4 :: rest) = tb rest /\ cval rest = cval G + 4.
Proof.
  intros G rest Hw Hsel Honly.
  assert (Hex : existsb (fun C => negb (is_3chain_b C || is_4loop_b C)%bool) G
                = true)
    by (unfold only34 in Honly; rewrite <- negb_forallb, Honly; reflexivity).
  apply existsb_exists in Hex; destruct Hex as [D [HD HDn]].
  apply negb_true_iff, orb_false_iff in HDn; destruct HDn as [HD3 HD4].
  assert (HwD : wf_comp D)
    by (unfold wf in Hw; rewrite Forall_forall in Hw; apply Hw; exact HD).
  pose proof (selections_perm G (Loop 4, rest) Hsel) as Hperm;
    cbn [fst snd] in Hperm.
  assert (HDrest : In D rest).
  { assert (HDG : In D (Loop 4 :: rest))
      by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact HD]).
    destruct HDG as [HDeq | HDr]; [|exact HDr].
    exfalso; rewrite <- HDeq in HD4; discriminate. }
  assert (Htb : tb (Loop 4 :: rest) = tb rest)
    by (apply (tb_remove_4loop rest D); assumption).
  split; [exact Htb|].
  pose proof (selections_cval G (Loop 4, rest) Hsel) as Hcv;
    cbn [fst snd] in Hcv.
  rewrite weight_loop_len, Htb in Hcv.
  unfold cval in *; simpl Z.of_nat in Hcv; lia.
Qed.

(** Case (ii) of Allcock's Theorem 1.1, in the regime where the closed form is
    the absolute controlled value: opening the four-loop attains the value, so
    no opening is better. *)
Theorem open_4loop_optimal :
  forall G rest,
    wf G -> In (Loop 4, rest) (selections G) ->
    existsb is_4loop_b G = true ->
    only34 G = false ->
    -2 <= cval G ->
    value_open (Loop 4, rest) = value G /\
    (forall q, In q (selections G) -> value_open (Loop 4, rest) <= value_open q).
Proof.
  intros G rest Hw Hsel H4 Honly Hge.
  destruct (four_loop_rest G rest Hw Hsel Honly) as [Htb Hcr].
  assert (HNil : G <> []) by (intros ->; simpl in Hsel; destruct Hsel).
  assert (Hwr : wf rest)
    by exact (proj2 (selections_wf G (Loop 4, rest) Hw Hsel)).
  assert (Hvr : value rest = cval G + 4)
    by (rewrite (value_cval_ge2 rest Hwr) by lia; exact Hcr).
  assert (Hop : value_open (Loop 4, rest) = Z.abs (cval G)).
  { unfold value_open; cbn [fst snd]; rewrite Hvr, vopen_loop4.
    f_equal; lia. }
  assert (HvG : value G = Z.abs (cval G))
    by (apply value_with_4loop; assumption).
  split; [rewrite Hop, HvG; reflexivity|].
  apply (proj1 (opener_optimal_iff G (Loop 4, rest) HNil Hsel)).
  rewrite Hop, HvG; reflexivity.
Qed.

(** * The standard move where three-chains abound *)

(** With another three-chain left behind, removing a three-chain leaves the
    terminal bonus alone, so the criterion applies and the standard move is
    optimal. *)
Theorem open_3chain_optimal :
  forall G rest,
    wf G -> In (Chain 3, rest) (selections G) ->
    existsb is_3chain_b rest = true ->
    2 <= cval rest ->
    value_open (Chain 3, rest) = cval G /\
    (forall q, In q (selections G) -> value_open (Chain 3, rest) <= value_open q).
Proof.
  intros G rest Hw Hsel H3 Hc.
  apply (open_chain_optimal_ge2 G 3 rest Hw Hsel);
    [apply tb_cons_3chain_with3; exact H3 | exact Hc].
Qed.

(** So on a position of two or more three-chains whose controlled value stays
    at two after one is removed, the standard move is provably optimal. *)
Corollary standard_move_optimal_two_threes :
  forall G rest,
    wf G -> In (Chain 3, rest) (selections G) ->
    (1 <= count3 rest)%nat ->
    2 <= cval rest ->
    value G = value_open (Chain 3, rest).
Proof.
  intros G rest Hw Hsel H3 Hc.
  assert (Hex : existsb is_3chain_b rest = true)
    by (apply count3_pos_iff; lia).
  destruct (open_3chain_optimal G rest Hw Hsel Hex Hc) as [Hop Hmin].
  assert (HNil : G <> []) by (intros ->; simpl in Hsel; destruct Hsel).
  apply (proj2 (opener_optimal_iff G (Chain 3, rest) HNil Hsel)); exact Hmin.
Qed.

(** ****************************************************************** *)
(** Positions of three-chains and four-loops, in canonical order.

    These are the positions Allcock's case (ii) leaves over, and they are
    determined by their two counts: [only34_perm] sorts any of them into
    three-chains followed by four-loops.

    [value_perm] is what makes that useful. It follows from
    [ShortChains.svalue_perm] through [DotsAndBoxes.svalue_wf], since the capped
    value agrees with the original on wellformed positions. The original
    development does not carry it. *)

(** * Wellformedness and the value are permutation invariant *)

Lemma wf_perm : forall G H, Permutation G H -> wf G -> wf H.
Proof.
  intros G H Hp Hw; unfold wf in *; rewrite Forall_forall in *.
  intros C HC; apply Hw.
  apply (Permutation_in _ (Permutation_sym Hp)); exact HC.
Qed.

Theorem value_perm :
  forall G H, wf G -> Permutation G H -> value G = value H.
Proof.
  intros G H Hw Hp.
  assert (HwH : wf H) by (apply (wf_perm G H Hp Hw)).
  rewrite <- (svalue_wf G Hw), <- (svalue_wf H HwH).
  apply svalue_perm; exact Hp.
Qed.

(** * Sorting a position of three-chains and four-loops *)

Lemma only34_cons :
  forall C G, only34 (C :: G) = true ->
    (is_3chain_b C = true \/ is_4loop_b C = true) /\ only34 G = true.
Proof.
  intros C G H; unfold only34 in H; simpl in H.
  apply andb_true_iff in H; destruct H as [HC HG].
  split; [apply orb_true_iff; exact HC | exact HG].
Qed.

(** [DotsAndBoxes.perm_mix_of_only34] already sorts such a position into
    [mix], and [DotsAndBoxes.value_mix] computes that. With [value_perm] the
    two combine: a position of three-chains and four-loops is worth what its
    counts say, whatever order it is written in. *)
Corollary only34_value :
  forall G, wf G -> only34 G = true ->
    value G = v36 (count3 G) (count4 G).
Proof.
  intros G Hw H34.
  rewrite (value_perm G (mix (count3 G) (count4 G)) Hw
             (perm_mix_of_only34 G H34)).
  apply value_mix.
Qed.

(** * What is left after opening a four-loop *)

Lemma only34_perm_inv :
  forall G H, Permutation G H -> only34 G = true -> only34 H = true.
Proof.
  intros G H Hp H34; unfold only34 in *; rewrite forallb_forall in *.
  intros C HC; apply H34.
  apply (Permutation_in _ (Permutation_sym Hp)); exact HC.
Qed.

Theorem only34_rest :
  forall G rest,
    only34 G = true -> In (Loop 4, rest) (selections G) ->
    only34 rest = true /\
    count3 rest = count3 G /\ S (count4 rest) = count4 G.
Proof.
  intros G rest H34 Hsel.
  pose proof (selections_perm G (Loop 4, rest) Hsel) as Hp; simpl in Hp.
  assert (Hr : only34 (Loop 4 :: rest) = true)
    by (apply (only34_perm_inv G); [apply Permutation_sym; exact Hp | exact H34]).
  destruct (only34_cons (Loop 4) rest Hr) as [_ Hrest].
  split; [exact Hrest|].
  split.
  - rewrite <- (count3_perm _ _ Hp); reflexivity.
  - rewrite <- (count4_perm _ _ Hp); reflexivity.
Qed.

(** And what remains is again in canonical form, so its value is computable
    from the counts alone. *)
Corollary only34_rest_value :
  forall G rest,
    wf G -> only34 G = true -> In (Loop 4, rest) (selections G) ->
    value rest = v36 (count3 G) (pred (count4 G)).
Proof.
  intros G rest Hw H34 Hsel.
  destruct (only34_rest G rest H34 Hsel) as [Hr [H3 H4]].
  pose proof (selections_perm G (Loop 4, rest) Hsel) as Hp; simpl in Hp.
  assert (Hwr : wf rest).
  { assert (Hwc : wf (Loop 4 :: rest))
      by (apply (wf_perm G); [apply Permutation_sym; exact Hp | exact Hw]).
    inversion Hwc; assumption. }
  rewrite (only34_value rest Hwr Hr), H3.
  replace (pred (count4 G)) with (count4 rest) by lia; reflexivity.
Qed.

(** * Opening a four-loop, on such a position *)

(** The value and the option are both read off the counts, so the comparison
    Allcock's case (ii) needs is arithmetic in [v36]. *)
Theorem only34_open_four :
  forall G rest,
    wf G -> only34 G = true -> In (Loop 4, rest) (selections G) ->
    value G = v36 (count3 G) (count4 G) /\
    value_open (Loop 4, rest) = vopen (Loop 4) (v36 (count3 G)
                                                   (pred (count4 G))).
Proof.
  intros G rest Hw H34 Hsel.
  split; [apply only34_value; assumption|].
  unfold value_open; cbn [fst snd].
  rewrite (only34_rest_value G rest Hw H34 Hsel); reflexivity.
Qed.

(** * The controlled value of such a position *)

Lemma cbase_mix : forall t f, cbase (mix t f) = - Z.of_nat t - 4 * Z.of_nat f.
Proof.
  induction t as [|t IH]; intros f.
  - change (mix 0 f) with (repeat (Loop 4) f).
    rewrite cbase_repeat_loop4; lia.
  - rewrite mix_chain_cons, cbase_cons, weight_chain, (IH f); lia.
Qed.

Lemma In_mix_three : forall t f, (1 <= t)%nat -> In (Chain 3) (mix t f).
Proof.
  intros t f Ht; destruct t as [|t']; [lia|].
  rewrite mix_chain_cons; left; reflexivity.
Qed.

Lemma In_mix_four : forall t f, (1 <= f)%nat -> In (Loop 4) (mix t f).
Proof.
  intros t f Hf; unfold mix; apply in_or_app; right.
  destruct f as [|f']; [lia|]; left; reflexivity.
Qed.

(** With both kinds present the terminal bonus is six. *)
Lemma tb_mix : forall t f, (1 <= t)%nat -> (1 <= f)%nat -> tb (mix t f) = 6.
Proof.
  intros t f Ht Hf; apply tb_six.
  - apply existsb_exists; exists (Loop 4).
    split; [apply In_mix_four; exact Hf | reflexivity].
  - apply existsb_exists; exists (Chain 3).
    split; [apply In_mix_three; exact Ht | reflexivity].
  - apply forallb_forall; intros C HC.
    destruct (In_mix t f C HC) as [-> | ->]; reflexivity.
Qed.

Theorem cval_mix :
  forall t f, (1 <= t)%nat -> (1 <= f)%nat ->
    cval (mix t f) = 6 - Z.of_nat t - 4 * Z.of_nat f.
Proof.
  intros t f Ht Hf; unfold cval.
  rewrite cbase_mix, (tb_mix t f Ht Hf); lia.
Qed.

(** * Which counts Allcock's case (ii) admits *)

Theorem case_ii_only34_counts :
  forall G,
    only34 G = true -> (1 <= count4 G)%nat ->
    -1 <= cval G -> cval G <= 1 ->
    (count3 G = 0 /\ count4 G = 2)%nat \/
    (count3 G = 1 /\ count4 G = 1)%nat \/
    (count3 G = 2 /\ count4 G = 1)%nat \/
    (count3 G = 3 /\ count4 G = 1)%nat.
Proof.
  intros G H34 H4 Hge Hle.
  rewrite (cval_perm G (mix (count3 G) (count4 G))
             (perm_mix_of_only34 G H34)) in Hge, Hle.
  destruct (count3 G) as [|t] eqn:E3.
  - rewrite (cval_mix0 (count4 G) H4) in Hge, Hle; left; split; lia.
  - rewrite (cval_mix (S t) (count4 G) ltac:(lia) H4) in Hge, Hle.
    assert (Ht : (t = 0 \/ t = 1 \/ t = 2)%nat) by lia.
    destruct Ht as [-> | [-> | ->]];
      [right; left | right; right; left | right; right; right];
      split; lia.
Qed.

(** * Excluding three three-chains beside a four-loop *)

Lemma only34_counts_length :
  forall G, only34 G = true -> (count3 G + count4 G)%nat = length G.
Proof.
  induction G as [|C G IH]; intros H; [reflexivity|].
  destruct (only34_cons C G H) as [HC HG]; specialize (IH HG).
  destruct HC as [H3 | H4].
  - assert (E : C = Chain 3) by (apply is_3chain_b_eq; exact H3); subst C.
    assert (E3 : count3 (Chain 3 :: G) = S (count3 G)) by reflexivity.
    assert (E4 : count4 (Chain 3 :: G) = count4 G) by reflexivity.
    rewrite E3, E4; simpl length; lia.
  - assert (E : C = Loop 4) by (apply is_4loop_b_eq; exact H4); subst C.
    assert (E3 : count3 (Loop 4 :: G) = count3 G) by reflexivity.
    assert (E4 : count4 (Loop 4 :: G) = S (count4 G)) by reflexivity.
    rewrite E3, E4; simpl length; lia.
Qed.

(** [DotsAndBoxes.drop_first] really does remove a four-loop. *)
Lemma drop_first_4loop_sel :
  forall G, (1 <= count4 G)%nat ->
    In (Loop 4, drop_first is_4loop_b G) (selections G).
Proof.
  intros G H4; unfold drop_first.
  destruct (filter (fun p => is_4loop_b (fst p)) (selections G))
    as [|p l] eqn:E.
  - exfalso.
    destruct (In_selections G (Loop 4) (count4_pos_In G H4)) as [rest Hsel].
    assert (Hin : In (Loop 4, rest)
                    (filter (fun q => is_4loop_b (fst q)) (selections G)))
      by (apply filter_In; split; [exact Hsel | reflexivity]).
    rewrite E in Hin; destruct Hin.
  - assert (Hin : In p (filter (fun q => is_4loop_b (fst q)) (selections G)))
      by (rewrite E; left; reflexivity).
    apply filter_In in Hin; destruct Hin as [Hsel Hf].
    assert (Hp : fst p = Loop 4) by (apply is_4loop_b_eq; exact Hf).
    destruct p as [C rest]; cbn [fst snd] in *; subst C; exact Hsel.
Qed.

(** Three three-chains beside one four-loop is exactly the position the case
    sets aside, so that pair cannot arise. *)
Theorem only34_three_threes :
  forall G,
    only34 G = true -> count3 G = 3%nat -> count4 G = 1%nat ->
    rest_is_three_threes_b G = true.
Proof.
  intros G H34 H3 H4; unfold rest_is_three_threes_b.
  assert (Hsel : In (Loop 4, drop_first is_4loop_b G) (selections G))
    by (apply drop_first_4loop_sel; lia).
  destruct (only34_rest G (drop_first is_4loop_b G) H34 Hsel) as [Hr [E3 E4]].
  assert (Hlen : (count3 (drop_first is_4loop_b G)
                  + count4 (drop_first is_4loop_b G))%nat
                 = length (drop_first is_4loop_b G))
    by (apply only34_counts_length; exact Hr).
  apply andb_true_iff; split; apply Nat.eqb_eq; lia.
Qed.

(** ****************************************************************** *)
(** Case (i): the arithmetic.

    The case names the shortest loop on a three-chain together with loops,
    when the controlled value is at least two. There the value is the
    controlled value, and opening a loop leaves a position whose controlled
    value is higher by the loop's own deficit, so the comparison reduces to
    [vopen_loop_eq]: taking the loop is worth exactly the controlled value
    provided the loop is not too long.

    [cbase_loops_lower] is what supplies that proviso. A shortest loop of
    eight boxes or more leaves every loop with a nonnegative weight, so the
    base is at least the one loop's own; a shorter one is covered by the
    case's own bound directly. *)

(** * Opening a loop when the value is the controlled value *)

Lemma vopen_loop_eq :
  forall m c,
    Z.of_nat m - 4 <= c ->
    vopen (Loop m) (c - Z.of_nat m + 8) = c.
Proof.
  intros m c H; rewrite vopen_max; cbn [csize hand].
  rewrite Z.max_r by lia; lia.
Qed.

(** * A shortest loop of eight or more forces a nonnegative base *)

Lemma weight_loop : forall m, weight (Loop m) = Z.of_nat m - 8.
Proof. intros m; unfold weight; cbn [csize hand]; lia. Qed.

Lemma cbase_loops_nonneg :
  forall L,
    forallb is_loop_b L = true ->
    (forall C, In C L -> (8 <= csize C)%nat) ->
    0 <= cbase L.
Proof.
  induction L as [|C L IH]; intros HL Hm; [reflexivity|].
  simpl in HL; apply andb_true_iff in HL; destruct HL as [HC HLs].
  destruct C as [n | n]; [discriminate|].
  rewrite cbase_cons, weight_loop.
  assert (Hn : (8 <= n)%nat).
  { pose proof (Hm (Loop n) (or_introl eq_refl)) as H; cbn [csize] in H;
      exact H. }
  assert (Hrest : 0 <= cbase L)
    by (apply IH; [exact HLs | intros D HD; apply Hm; right; exact HD]).
  cbn [csize] in *; lia.
Qed.

Theorem cbase_loops_lower :
  forall L m,
    forallb is_loop_b L = true ->
    (forall C, In C L -> (m <= csize C)%nat) ->
    (8 <= m)%nat -> L <> [] ->
    Z.of_nat m - 8 <= cbase L.
Proof.
  intros [|C L] m HL Hm H8 HNil; [contradiction|].
  simpl in HL; apply andb_true_iff in HL; destruct HL as [HC HLs].
  destruct C as [n | n]; [discriminate|].
  rewrite cbase_cons, weight_loop.
  assert (Hn : (m <= n)%nat).
  { pose proof (Hm (Loop n) (or_introl eq_refl)) as H; cbn [csize] in H;
      exact H. }
  assert (Hrest : 0 <= cbase L).
  { apply cbase_loops_nonneg; [exact HLs|].
    intros D HD; pose proof (Hm D (or_intror HD)); lia. }
  cbn [csize] in *; lia.
Qed.

(** * A three-chain together with loops *)

Lemma filter_le :
  forall (f : comp -> bool) l, (length (filter f l) <= length l)%nat.
Proof.
  induction l as [|x l IH]; simpl; [lia|].
  destruct (f x); simpl; lia.
Qed.

Lemma filter_full :
  forall (f : comp -> bool) l,
    length (filter f l) = length l -> forallb f l = true.
Proof.
  induction l as [|x l IH]; intros H; [reflexivity|].
  simpl in H |- *; destruct (f x) eqn:E.
  - simpl in H; rewrite (IH ltac:(lia)); reflexivity.
  - exfalso; pose proof (filter_le f l); lia.
Qed.

Theorem three_plus_loops_decomp :
  forall G, three_plus_loops_b G = true ->
    exists L, Permutation G (Chain 3 :: L)
              /\ forallb is_loop_b L = true /\ L <> [].
Proof.
  intros G H; unfold three_plus_loops_b in H.
  apply andb_true_iff in H; destruct H as [H Hlen].
  apply andb_true_iff in H; destruct H as [H3 Hl1].
  apply Nat.eqb_eq in H3; apply Nat.leb_le in Hl1; apply Nat.eqb_eq in Hlen.
  destruct (norm_3chain G ltac:(lia)) as [L Hp]; exists L.
  assert (Hcl : count_loops G = length (filter is_loop_b L)).
  { unfold count_loops.
    rewrite (Permutation_length
               (Permutation_filter is_loop_b G (Chain 3 :: L) Hp)).
    reflexivity. }
  assert (HlenL : length G = S (length L))
    by (rewrite (Permutation_length Hp); reflexivity).
  assert (Hfull : length (filter is_loop_b L) = length L) by lia.
  split; [exact Hp|].
  split; [apply filter_full; exact Hfull|].
  intros ->; simpl in Hcl; lia.
Qed.

(** * The shortest loop is short enough *)

(** Either it holds six boxes or fewer, when the case's own bound gives the
    inequality outright, or eight or more, when every loop weighs nothing
    against the controller and the base carries it. *)
Theorem case_i_shortest_bound :
  forall G p,
    wf G -> case_i G = true -> shortest_of is_loop_b G = Some p ->
    Z.of_nat (csize (fst p)) - 4 <= cval G.
Proof.
  intros G p Hw Hci Hs.
  apply andb_true_iff in Hci; destruct Hci as [Hcv Htp].
  apply Z.leb_le in Hcv.
  destruct (shortest_of_min is_loop_b G p Hs) as [Hloop Hmin].
  destruct (Z.le_gt_cases (Z.of_nat (csize (fst p))) 6) as [Hsm | Hbig];
    [lia|].
  (* a loop is even, so longer than six means eight or more *)
  assert (H8 : (8 <= csize (fst p))%nat).
  { assert (Hinp : In p (selections G))
      by (apply (shortest_of_In is_loop_b); exact Hs).
    assert (Hin : In (fst p) G) by (apply selections_In; exact Hinp).
    unfold wf in Hw; rewrite Forall_forall in Hw; specialize (Hw (fst p) Hin).
    destruct (fst p) as [n | n]; [discriminate Hloop|].
    cbn [wf_comp] in Hw; destruct Hw as [Hn4 Hev].
    apply Nat.even_spec in Hev; destruct Hev as [k Hk].
    cbn [csize] in *; lia. }
  destruct (three_plus_loops_decomp G Htp) as [L [Hp [HL HNil]]].
  assert (Hcb : cbase G = -1 + cbase L).
  { rewrite (cbase_perm G (Chain 3 :: L) Hp), cbase_cons, weight_chain; lia. }
  assert (Hlow : Z.of_nat (csize (fst p)) - 8 <= cbase L).
  { apply cbase_loops_lower; [exact HL | | exact H8 | exact HNil].
    intros C HC.
    assert (HinG : In C G)
      by (apply (Permutation_in _ (Permutation_sym Hp)); right; exact HC).
    destruct (In_selections G C HinG) as [rest Hsel].
    assert (Hlp : is_loop_b C = true).
    { rewrite forallb_forall in HL; apply HL; exact HC. }
    exact (Hmin (C, rest) Hsel Hlp). }
  assert (Htb : tb G = 6).
  { apply tb_six.
    - apply existsb_exists.
      destruct L as [|D L']; [contradiction|].
      exists D; split.
      + apply (Permutation_in _ (Permutation_sym Hp)); right; left; reflexivity.
      + simpl in HL; apply andb_true_iff in HL; tauto.
    - apply existsb_exists; exists (Chain 3); split; [|reflexivity].
      apply (Permutation_in _ (Permutation_sym Hp)); left; reflexivity.
    - apply forallb_forall; intros C HC.
      assert (HC' : In C (Chain 3 :: L))
        by (apply (Permutation_in _ Hp); exact HC).
      destruct HC' as [<- | HC']; [reflexivity|].
      rewrite forallb_forall in HL; rewrite (HL C HC'); reflexivity. }
  unfold cval; rewrite Hcb, Htb; lia.
Qed.

(** * Opening the shortest loop *)

Lemma vopen_loop_eq' :
  forall C c,
    is_loop_b C = true -> Z.of_nat (csize C) - 4 <= c ->
    vopen C (c - Z.of_nat (csize C) + 8) = c.
Proof.
  intros [n | n] c HC Hc; [discriminate|].
  rewrite vopen_max; cbn [csize hand] in *.
  rewrite Z.max_r by lia; lia.
Qed.

Lemma singleton_three :
  forall l, length l = 1%nat -> count3 l = 1%nat -> l = [Chain 3].
Proof.
  intros [|C [|D l]] Hl Hc; simpl in Hl; try discriminate.
  f_equal; apply is_3chain_b_eq.
  unfold count3 in Hc; simpl in Hc.
  destruct (is_3chain_b C); [reflexivity | simpl in Hc; discriminate].
Qed.

Lemma count_loops_perm :
  forall G H, Permutation G H -> count_loops G = count_loops H.
Proof.
  intros G H Hp; unfold count_loops.
  apply Permutation_length, Permutation_filter; exact Hp.
Qed.

(** Every component is the three-chain or a loop. *)
Lemma three_plus_loops_members :
  forall G, three_plus_loops_b G = true ->
    forall C, In C G -> is_loop_b C = true \/ C = Chain 3.
Proof.
  intros G Htp C HC.
  destruct (three_plus_loops_decomp G Htp) as [L [Hp [HL _]]].
  assert (HC' : In C (Chain 3 :: L)) by (apply (Permutation_in _ Hp); exact HC).
  destruct HC' as [<- | HC']; [right; reflexivity|].
  left; rewrite forallb_forall in HL; apply HL; exact HC'.
Qed.

(** * Case (i) *)

Theorem allcock_case_i_optimal :
  forall G p,
    wf G -> case_i G = true -> allcock_move G = Some p ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hci Hm.
  assert (Hd : (case_i G || case_ii G || case_iii G)%bool = true)
    by (rewrite Hci; destruct (case_ii G), (case_iii G); reflexivity).
  assert (Hs : shortest_of is_loop_b G = Some p)
    by (unfold allcock_move in Hm; rewrite Hd in Hm; exact Hm).
  pose proof Hci as Hci'.
  apply andb_true_iff in Hci'; destruct Hci' as [Hcv Htp].
  apply Z.leb_le in Hcv.
  assert (Hc3G : (1 <= count3 G)%nat).
  { pose proof Htp as Ht; apply andb_true_iff in Ht; destruct Ht as [Ht _].
    apply andb_true_iff in Ht; destruct Ht as [H3 _].
    apply Nat.eqb_eq in H3; lia. }
  destruct (shortest_of_min is_loop_b G p Hs) as [Hloop _].
  assert (Hin : In p (selections G))
    by (apply (shortest_of_In is_loop_b); exact Hs).
  pose proof (selections_perm G p Hin) as Hperm.
  pose proof (case_i_shortest_bound G p Hw Hci Hs) as Hbound.
  assert (HvG : value G = cval G) by (apply value_cval_ge2; assumption).
  assert (Hwr : wf (snd p)).
  { destruct (selections_wf G p Hw Hin) as [_ H]; exact H. }
  (* the three-chain is left behind *)
  assert (Hc3 : count3 (snd p) = 1%nat).
  { assert (E : count3 G = count3 (fst p :: snd p))
      by (apply count3_perm; apply Permutation_sym; exact Hperm).
    assert (E3 : is_3chain_b (fst p) = false)
      by (destruct (fst p) as [n | n]; [discriminate Hloop | reflexivity]).
    apply andb_true_iff in Htp; destruct Htp as [Htp Hlen].
    apply andb_true_iff in Htp; destruct Htp as [H3 _].
    apply Nat.eqb_eq in H3.
    unfold count3 in *; simpl in E; rewrite E3 in E; lia. }
  assert (Hcb : cbase (snd p) = cval G - 6 - (Z.of_nat (csize (fst p)) - 8)).
  { assert (Etb : tb G = 6).
    { apply tb_six.
      - apply existsb_exists; exists (fst p); split; [|exact Hloop].
        apply (Permutation_in _ Hperm); left; reflexivity.
      - apply existsb_exists; exists (Chain 3); split; [|reflexivity].
        apply count3_pos_In; exact Hc3G.
      - apply forallb_forall; intros C HC.
        destruct (three_plus_loops_members G Htp C HC) as [HL | ->];
          [rewrite HL; reflexivity | reflexivity]. }
    assert (Ecb : cbase G = weight (fst p) + cbase (snd p))
      by (rewrite (cbase_perm G (fst p :: snd p) (Permutation_sym Hperm));
          reflexivity).
    assert (Ew : weight (fst p) = Z.of_nat (csize (fst p)) - 8)
      by (destruct (fst p) as [n | n]; [discriminate Hloop | apply weight_loop]).
    unfold cval in *; lia. }
  assert (Hval : value G = value_open p).
  { unfold value_open.
    destruct (Nat.eq_dec (count_loops (snd p)) 0) as [Hnl | Hnl].
    - (* the loop was the only one: a lone three-chain is left *)
      assert (Hlen1 : length (snd p) = 1%nat).
      { assert (E : count_loops G = S (count_loops (snd p))).
        { rewrite (count_loops_perm G (fst p :: snd p) (Permutation_sym Hperm)).
          unfold count_loops; simpl; rewrite Hloop; reflexivity. }
        pose proof (selections_length G p Hin) as Hl.
        apply andb_true_iff in Htp; destruct Htp as [_ Hlen].
        apply Nat.eqb_eq in Hlen; lia. }
      rewrite (singleton_three (snd p) Hlen1 Hc3), value_single.
      cbn [csize].
      assert (Hcv3 : cval G = Z.of_nat (csize (fst p)) - 3).
      { rewrite (singleton_three (snd p) Hlen1 Hc3) in Hcb.
        assert (Ecb3 : cbase [Chain 3] = -1) by reflexivity.
        rewrite Ecb3 in Hcb; lia. }
      rewrite HvG.
      destruct (fst p) as [n | n]; [discriminate Hloop|].
      rewrite vopen_max; cbn [csize hand] in *.
      rewrite Z.max_l by lia; lia.
    - (* a loop survives, so the bonus stays at six *)
      assert (Htbr : tb (snd p) = 6).
      { apply tb_six.
        - apply existsb_exists.
          unfold count_loops in Hnl.
          destruct (filter is_loop_b (snd p)) as [|D l] eqn:Ef;
            [simpl in Hnl; lia|].
          exists D; assert (HD : In D (filter is_loop_b (snd p)))
            by (rewrite Ef; left; reflexivity).
          apply filter_In in HD; tauto.
        - apply existsb_exists; exists (Chain 3); split; [|reflexivity].
          apply count3_pos_In; lia.
        - apply forallb_forall; intros C HC.
          assert (HCG : In C G)
            by (apply (Permutation_in _ Hperm); right; exact HC).
          destruct (three_plus_loops_members G Htp C HCG) as [HL | ->];
            [rewrite HL; reflexivity | reflexivity]. }
      assert (Hcr : cval (snd p) = cval G - Z.of_nat (csize (fst p)) + 8)
        by (unfold cval at 1; rewrite Hcb, Htbr; lia).
      assert (Hvr : value (snd p) = cval (snd p))
        by (apply value_cval_ge2; [exact Hwr | lia]).
      rewrite Hvr, Hcr, HvG.
      symmetry; apply vopen_loop_eq'; [exact Hloop | exact Hbound]. }
  split; [exact Hval|].
  assert (HNil : G <> []) by (intros ->; simpl in Hin; destruct Hin).
  apply (allcock_move_optimal_iff G p HNil Hm); exact Hval.
Qed.

(** ****************************************************************** *)
(** Case (ii).

    The case names the shortest loop on a position whose controlled value lies
    in [-1, 1] and which holds a four-loop, provided what is left after
    removing one four-loop is not exactly three three-chains.

    [shortest_loop_is_four] identifies that move as a four-loop, and
    [open_4loop_optimal] shows opening a four-loop attains the value
    whenever the position is not made of three-chains and four-loops alone.
    [allcock_case_ii_optimal] is the two composed.

    The positions the composition misses are exactly those made of
    three-chains and four-loops. [case_ii_only34_shape] pins them down: the
    case's own bounds leave three, up to order. *)

(** * The strategy opens the shortest loop in this case *)

Lemma allcock_move_case_ii :
  forall G, case_ii G = true -> allcock_move G = shortest_of is_loop_b G.
Proof.
  intros G H; unfold allcock_move.
  assert (Hd : (case_i G || case_ii G || case_iii G)%bool = true)
    by (rewrite H; destruct (case_i G), (case_iii G); reflexivity).
  rewrite Hd; reflexivity.
Qed.

Lemma case_ii_parts :
  forall G, case_ii G = true ->
    cval G <= 1 /\ -1 <= cval G /\ (1 <= count4 G)%nat /\
    rest_is_three_threes_b G = false.
Proof.
  intros G H; unfold case_ii in H.
  apply andb_true_iff in H; destruct H as [H Hnr].
  apply negb_true_iff in Hnr.
  apply andb_true_iff in H; destruct H as [H H4].
  apply andb_true_iff in H; destruct H as [Hle Hge].
  apply Z.leb_le in Hle; apply Z.leb_le in Hge; apply Nat.leb_le in H4.
  repeat split; assumption.
Qed.

(** * The case, where the position is not all three-chains and four-loops *)

Theorem allcock_case_ii_optimal :
  forall G p,
    wf G -> case_ii G = true -> only34 G = false ->
    allcock_move G = Some p ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hii Honly Hm.
  destruct (case_ii_parts G Hii) as [Hle [Hge [H4 Hnr]]].
  rewrite (allcock_move_case_ii G Hii) in Hm.
  assert (Hp4 : fst p = Loop 4)
    by (apply (shortest_loop_is_four G p Hw H4); exact Hm).
  assert (Hin : In p (selections G))
    by (apply (shortest_of_In is_loop_b); exact Hm).
  destruct p as [C rest]; cbn [fst] in Hp4; subst C.
  assert (H4b : existsb is_4loop_b G = true)
    by (apply (proj2 (count4_pos_iff G)); lia).
  destruct (open_4loop_optimal G rest Hw Hin H4b Honly ltac:(lia))
    as [Hval Hmin].
  split; [symmetry; exact Hval | exact Hmin].
Qed.

(** * The case, where the position is all three-chains and four-loops *)

(** Here the value and the option are both read off the two counts, and the
    case's bounds admit only three pairs: the fourth, three three-chains
    beside one four-loop, is exactly what the case sets aside. *)
Theorem allcock_case_ii_only34 :
  forall G p,
    wf G -> case_ii G = true -> only34 G = true ->
    allcock_move G = Some p ->
    value G = value_open p.
Proof.
  intros G p Hw Hii H34 Hm.
  destruct (case_ii_parts G Hii) as [Hle [Hge [H4 Hnr]]].
  rewrite (allcock_move_case_ii G Hii) in Hm.
  assert (Hp4 : fst p = Loop 4)
    by (apply (shortest_loop_is_four G p Hw H4); exact Hm).
  assert (Hin : In p (selections G))
    by (apply (shortest_of_In is_loop_b); exact Hm).
  destruct p as [C rest]; cbn [fst] in Hp4; subst C.
  destruct (only34_open_four G rest Hw H34 Hin) as [Hv Ho].
  rewrite Hv, Ho.
  destruct (case_ii_only34_counts G H34 H4 Hge Hle)
    as [[E3 E4] | [[E3 E4] | [[E3 E4] | [E3 E4]]]];
    try (rewrite E3, E4; reflexivity).
  exfalso; rewrite (only34_three_threes G H34 E3 E4) in Hnr; discriminate.
Qed.

(** * Case (ii), complete *)

Theorem allcock_case_ii_complete :
  forall G p,
    wf G -> case_ii G = true -> allcock_move G = Some p ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hii Hm.
  assert (Hval : value G = value_open p).
  { destruct (only34 G) eqn:E34.
    - apply (allcock_case_ii_only34 G p Hw Hii E34 Hm).
    - destruct (allcock_case_ii_optimal G p Hw Hii E34 Hm) as [Hv _];
        exact Hv. }
  assert (HNil : G <> []).
  { destruct (case_ii_parts G Hii) as [_ [_ [H4 _]]].
    intros ->; unfold count4 in H4; simpl in H4; lia. }
  split; [exact Hval|].
  apply (allcock_move_optimal_iff G p HNil Hm); exact Hval.
Qed.

(** ****************************************************************** *)
(** Case (iii): the arithmetic.

    The case asks for exactly one three-chain, a four-loop, a controlled value
    of at most minus two, and a board of size three modulo four. Those are
    precisely the conditions under which [DotsAndBoxes.v41] reports
    [w310 (cval G) (count4 G)], so both the position and what a four-loop
    leaves behind are read from the same table.

    Removing a four-loop raises the controlled value by four and leaves the
    loop count one shorter, and [DotsAndBoxes.w310_step] already records what
    that does to the table. What is missing is the reading of the case itself:
    [case_iii_shape] recovers from the two nested drops that the three-chain is
    unique and the board has size three modulo four, which is exactly the
    hypothesis [DotsAndBoxes.value_theta1_odd] wants. *)

(** * What the case says, in the position's own terms *)

Lemma case_iii_parts :
  forall G, case_iii G = true ->
    cval G <= -2 /\ (1 <= count4 G)%nat /\ (1 <= count3 G)%nat /\
    Z.of_nat (size (drop_first is_3chain_b (drop_first is_4loop_b G)))
      mod 4 = 0 /\
    count3 (drop_first is_3chain_b (drop_first is_4loop_b G)) = 0%nat.
Proof.
  intros G H; unfold case_iii in H.
  apply andb_true_iff in H; destruct H as [H Hc3].
  apply andb_true_iff in H; destruct H as [H Hsz].
  apply andb_true_iff in H; destruct H as [H H3].
  apply andb_true_iff in H; destruct H as [Hcv H4].
  apply Z.leb_le in Hcv; apply Nat.leb_le in H4; apply Nat.leb_le in H3.
  apply Z.eqb_eq in Hsz; apply Nat.eqb_eq in Hc3.
  repeat split; assumption.
Qed.

(** [drop_first] removes a three-chain when there is one. *)
Lemma drop_first_3chain_sel :
  forall G, (1 <= count3 G)%nat ->
    In (Chain 3, drop_first is_3chain_b G) (selections G).
Proof.
  intros G H3; unfold drop_first.
  destruct (filter (fun p => is_3chain_b (fst p)) (selections G))
    as [|p l] eqn:E.
  - exfalso.
    destruct (In_selections G (Chain 3) (count3_pos_In G H3)) as [rest Hsel].
    assert (Hin : In (Chain 3, rest)
                    (filter (fun q => is_3chain_b (fst q)) (selections G)))
      by (apply filter_In; split; [exact Hsel | reflexivity]).
    rewrite E in Hin; destruct Hin.
  - assert (Hin : In p (filter (fun q => is_3chain_b (fst q)) (selections G)))
      by (rewrite E; left; reflexivity).
    apply filter_In in Hin; destruct Hin as [Hsel Hf].
    assert (Hp : fst p = Chain 3) by (apply is_3chain_b_eq; exact Hf).
    destruct p as [C rest]; cbn [fst snd] in *; subst C; exact Hsel.
Qed.

(** * Reading the two drops back *)

(** Removing a four-loop then a three-chain takes seven boxes and the only
    three-chain, so the case pins the board's size modulo four and forces the
    three-chain to be unique. *)
Theorem case_iii_shape :
  forall G, case_iii G = true ->
    count3 G = 1%nat /\ Z.of_nat (size G) mod 4 = 3.
Proof.
  intros G Hc.
  destruct (case_iii_parts G Hc) as [Hcv [H4 [H3 [Hsz Hc3]]]].
  set (H1 := drop_first is_4loop_b G) in *.
  assert (Hs1 : In (Loop 4, H1) (selections G))
    by (apply drop_first_4loop_sel; exact H4).
  pose proof (selections_perm G (Loop 4, H1) Hs1) as Hp1; simpl in Hp1.
  assert (Hsz1 : (4 + size H1)%nat = size G)
    by (exact (selections_size G (Loop 4, H1) Hs1)).
  assert (Hc31 : count3 H1 = count3 G).
  { rewrite <- (count3_perm _ _ Hp1); reflexivity. }
  set (H2 := drop_first is_3chain_b H1) in *.
  assert (Hs2 : In (Chain 3, H2) (selections H1))
    by (apply drop_first_3chain_sel; lia).
  pose proof (selections_perm H1 (Chain 3, H2) Hs2) as Hp2; simpl in Hp2.
  assert (Hsz2 : (3 + size H2)%nat = size H1)
    by (exact (selections_size H1 (Chain 3, H2) Hs2)).
  assert (Hc32 : count3 H1 = S (count3 H2)).
  { rewrite <- (count3_perm _ _ Hp2); reflexivity. }
  split; [lia|].
  assert (Hsize : size G = (size H2 + 7)%nat) by lia.
  rewrite Hsize, Nat2Z.inj_add.
  replace (Z.of_nat 7) with 7 by reflexivity.
  rewrite Zplus_mod, Hsz; reflexivity.
Qed.

(** * The terminal bonus survives the opening *)

Lemma forallb_false_ex :
  forall (f : comp -> bool) l,
    forallb f l = false -> exists x, In x l /\ f x = false.
Proof.
  induction l as [|x l IH]; intros H; [discriminate|].
  simpl in H; destruct (f x) eqn:E.
  - simpl in H; destruct (IH H) as [y [Hy Hfy]].
    exists y; split; [right; exact Hy | exact Hfy].
  - exists x; split; [left; reflexivity | exact E].
Qed.

(** Removing the four-loop leaves the bonus alone. Either something longer
    remains, or what remains is three-chains and four-loops with a loop still
    among them; the only other shape, a lone three-chain, is worth one and so
    is excluded by the case's own bound. *)
Theorem case_iii_tb_stable :
  forall G rest,
    wf G -> case_iii G = true -> In (Loop 4, rest) (selections G) ->
    tb rest = tb G.
Proof.
  intros G rest Hw Hc Hsel.
  destruct (case_iii_parts G Hc) as [Hcv [H4 [H3 _]]].
  pose proof (selections_perm G (Loop 4, rest) Hsel) as Hp; simpl in Hp.
  rewrite <- (tb_perm _ _ Hp); symmetry.
  destruct (case_iii_shape G Hc) as [Hc3 _].
  assert (Hc3r : count3 rest = 1%nat).
  { rewrite <- Hc3, <- (count3_perm _ _ Hp); reflexivity. }
  destruct (forallb (fun C => (is_3chain_b C || is_4loop_b C)%bool) rest)
    eqn:E34.
  - (* what remains is three-chains and four-loops *)
    destruct (existsb is_loop_b rest) eqn:EL.
    + apply tb_remove_4loop_only34; [exact EL|].
      apply forallb_forall; intros C HC.
      rewrite forallb_forall in E34; specialize (E34 C HC).
      apply orb_true_iff in E34; destruct E34 as [H | H].
      * rewrite H, orb_true_r; reflexivity.
      * rewrite (is_4loop_b_eq C H); reflexivity.
    + (* no loop left: a lone three-chain, which the bound excludes *)
      exfalso.
      assert (Hno4 : count4 rest = 0%nat).
      { unfold count4; destruct (filter is_4loop_b rest) as [|D l] eqn:Ef;
          [reflexivity|].
        exfalso.
        assert (HD : In D (filter is_4loop_b rest))
          by (rewrite Ef; left; reflexivity).
        apply filter_In in HD; destruct HD as [HDin HDf].
        rewrite (is_4loop_b_eq D HDf) in HDin.
        assert (existsb is_loop_b rest = true)
          by (apply existsb_exists; exists (Loop 4); split;
              [exact HDin | reflexivity]).
        congruence. }
      assert (Honly : only34 rest = true) by exact E34.
      assert (Hlen : length rest = 1%nat)
        by (pose proof (only34_counts_length rest Honly); lia).
      assert (Hrest : rest = [Chain 3])
        by (apply singleton_three; assumption).
      rewrite Hrest in Hp.
      assert (Hcv1 : cval G = 1)
        by (rewrite <- (cval_perm _ _ Hp); reflexivity).
      lia.
  - (* something longer remains *)
    destruct (forallb_false_ex _ rest E34) as [D [HD HDf]].
    apply orb_false_iff in HDf; destruct HDf as [HD3 HD4].
    apply (tb_remove_4loop rest D HD HD3 HD4).
    assert (HDG : In D G)
      by (apply (Permutation_in _ Hp); right; exact HD).
    unfold wf in Hw; rewrite Forall_forall in Hw; apply Hw; exact HDG.
Qed.

(** * Case (iii) *)

Theorem allcock_case_iii_optimal :
  forall G p,
    wf G -> case_iii G = true -> allcock_move G = Some p ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hc Hm.
  destruct (case_iii_parts G Hc) as [Hcv [H4 [H3 _]]].
  destruct (case_iii_shape G Hc) as [Hc3 Hmod].
  assert (Hd : (case_i G || case_ii G || case_iii G)%bool = true)
    by (rewrite Hc, orb_true_r; reflexivity).
  assert (Hs : shortest_of is_loop_b G = Some p)
    by (unfold allcock_move in Hm; rewrite Hd in Hm; exact Hm).
  assert (Hp4 : fst p = Loop 4)
    by (apply (shortest_loop_is_four G p Hw H4); exact Hs).
  assert (Hin : In p (selections G))
    by (apply (shortest_of_In is_loop_b); exact Hs).
  destruct p as [C rest]; cbn [fst] in Hp4; subst C.
  pose proof (selections_perm G (Loop 4, rest) Hin) as Hp; simpl in Hp.
  (* the board is odd here, so the controlled value is too *)
  assert (Hodd : Z.even (cval G) = false)
    by (rewrite cval_parity, (even_mod4 (Z.of_nat (size G))), Hmod;
        reflexivity).
  assert (HvG : value G = w310 (cval G) (count4 G))
    by (apply value_theta1_odd; [exact Hw | exact Hc3 | exact Hmod | lia]).
  (* the remainder keeps the shape and gains four *)
  assert (Hwr : wf rest)
    by (destruct (selections_wf G (Loop 4, rest) Hw Hin) as [_ H]; exact H).
  assert (Hc3r : count3 rest = 1%nat)
    by (rewrite <- Hc3, <- (count3_perm _ _ Hp); reflexivity).
  assert (Hszr : (4 + size rest)%nat = size G)
    by (exact (selections_size G (Loop 4, rest) Hin)).
  assert (Hmodr : Z.of_nat (size rest) mod 4 = 3).
  { assert (E : Z.of_nat (size G) = 4 + Z.of_nat (size rest)) by lia.
    rewrite E in Hmod; rewrite <- Hmod.
    rewrite <- (Z.add_mod_idemp_l 4 (Z.of_nat (size rest)) 4) by lia.
    reflexivity. }
  assert (Hc4r : count4 G = S (count4 rest))
    by (rewrite <- (count4_perm _ _ Hp), count4_cons; reflexivity).
  assert (Hcvr : cval rest = cval G + 4).
  { assert (Etb : tb rest = tb G)
      by (apply (case_iii_tb_stable G rest Hw Hc Hin)).
    assert (Ecb : cbase G = weight (Loop 4) + cbase rest)
      by (rewrite (cbase_perm G (Loop 4 :: rest) (Permutation_sym Hp));
          reflexivity).
    assert (Ew : weight (Loop 4) = -4) by reflexivity.
    unfold cval in *; lia. }
  assert (Hoddr : Z.even (cval rest) = false)
    by (rewrite cval_parity, (even_mod4 (Z.of_nat (size rest))), Hmodr;
        reflexivity).
  assert (Hcvr2 : cval rest < 2)
    by (destruct (Z.eq_dec (cval rest) 2) as [E | Hne];
        [rewrite E in Hoddr; discriminate | lia]).
  assert (Hvr : value rest = w310 (cval rest) (count4 rest))
    by (apply value_theta1_odd; assumption).
  assert (Hval : value G = value_open (Loop 4, rest)).
  { unfold value_open; cbn [fst snd].
    rewrite Hvr, vopen_loop4, HvG, Hcvr.
    pose proof (w310_bounds (cval G + 4) (count4 rest)) as Hb.
    rewrite Z.abs_neq by lia.
    rewrite Hc4r; pose proof (w310_step (cval G) (count4 rest) Hodd); lia. }
  split; [exact Hval|].
  assert (HNil : G <> []) by (intros ->; simpl in Hin; destruct Hin).
  apply (allcock_move_optimal_iff G (Loop 4, rest) HNil Hm); exact Hval.
Qed.

(** ****************************************************************** *)
(** The standard move.

    Outside the three named cases the strategy opens a three-chain if there is
    one, otherwise a shortest loop, otherwise a shortest chain.

    [DotsAndBoxes.open_optimal_of_cval] already says when an opening is
    optimal: the terminal bonus survives it, what is left is worth at least the
    handout given away, and what is left is above the threshold.
    [standard_move_optimal_of_criterion] is that criterion applied to the
    standard move, whichever of the three components it names.

    [value_of_min_option] is the small step the criterion leaves out: a legal
    opening that no other opening beats is the value. *)

(** * A minimal opening is the value *)

Lemma value_of_min_option :
  forall G p,
    In p (selections G) ->
    (forall q, In q (selections G) -> value_open p <= value_open q) ->
    value G = value_open p.
Proof.
  intros G p Hp Hmin.
  apply Z.le_antisymm; [apply value_le_open; exact Hp|].
  assert (HNil : G <> []) by (intros ->; simpl in Hp; destruct Hp).
  destruct (value_attained G HNil) as [q [Hq Hv]].
  rewrite Hv; apply Hmin; exact Hq.
Qed.

(** * The criterion, applied to the standard move *)

Theorem standard_move_optimal_of_criterion :
  forall G p,
    wf G -> standard_move G = Some p ->
    tb (fst p :: snd p) = tb (snd p) ->
    Z.of_nat (hand (fst p)) <= cval (snd p) ->
    2 <= cval (snd p) ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hm Htb Hh Hc.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  destruct (open_optimal_of_cval G p Hw Hin Htb Hh Hc) as [_ Hmin].
  split; [apply value_of_min_option; assumption | exact Hmin].
Qed.

(** * Where a three-chain remains, the bonus looks after itself *)

(** Opening one three-chain out of several leaves the terminal bonus alone, so
    only the threshold has to be checked. *)
Theorem standard_move_3chain_optimal :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p ->
    existsb is_3chain_b (snd p) = true ->
    2 <= cval (snd p) ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm H3r Hc.
  assert (Hp3 : fst p = Chain 3)
    by (apply (standard_move_three G p H3); exact Hm).
  apply (standard_move_optimal_of_criterion G p Hw Hm).
  - rewrite Hp3; apply tb_cons_3chain_with3; exact H3r.
  - rewrite Hp3; cbn [hand]; lia.
  - exact Hc.
Qed.

(** * The threshold, from the position rather than the remainder *)

(** Removing a three-chain raises the controlled value by exactly one, since
    the chain weighs minus one and the bonus is unmoved. So the remainder
    clears the threshold as soon as the position itself reaches one. *)
Theorem standard_move_3chain_ge1 :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p ->
    existsb is_3chain_b (snd p) = true ->
    1 <= cval G ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm H3r Hcv.
  assert (Hp3 : fst p = Chain 3)
    by (apply (standard_move_three G p H3); exact Hm).
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  pose proof (selections_perm G p Hin) as Hperm.
  assert (Htb : tb (fst p :: snd p) = tb (snd p))
    by (rewrite Hp3; apply tb_cons_3chain_with3; exact H3r).
  assert (Hcr : cval (snd p) = cval G + 1).
  { rewrite <- (cval_perm _ _ Hperm).
    unfold cval; rewrite cbase_cons, Htb, Hp3, weight_chain; cbn [Z.of_nat].
    unfold cval; lia. }
  apply (standard_move_3chain_optimal G p Hw H3 Hm H3r); lia.
Qed.

(** * When opening a three-chain leaves the bonus alone *)

(** The bonus can only move if what remains is loops and nothing else: in every
    other shape the three-chain neither creates nor destroys the conditions the
    bonus is read from. This is weaker than asking a second three-chain to
    remain, and covers the positions where the only three-chain is opened. *)
Theorem tb_cons_3chain_not_all_loops :
  forall rest,
    forallb is_loop_b rest = false -> tb (Chain 3 :: rest) = tb rest.
Proof.
  intros rest H.
  destruct rest as [|D rest']; [discriminate|].
  rewrite (tb_cons_form (Chain 3) (D :: rest')).
  assert (Hnl : forallb is_loop_b (Chain 3 :: D :: rest') = false)
    by reflexivity.
  rewrite Hnl.
  assert (He : existsb is_loop_b (Chain 3 :: D :: rest')
               = existsb is_loop_b (D :: rest')) by reflexivity.
  assert (Hf : forallb (fun C => (is_loop_b C || is_3chain_b C)%bool)
                 (Chain 3 :: D :: rest')
               = forallb (fun C => (is_loop_b C || is_3chain_b C)%bool)
                   (D :: rest')) by reflexivity.
  rewrite He, Hf.
  rewrite (tb_cons_form D rest'), H; reflexivity.
Qed.

(** * The standard move on a three-chain, in its widest form *)

Theorem standard_move_3chain_stable :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p ->
    forallb is_loop_b (snd p) = false ->
    1 <= cval G ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnl Hcv.
  assert (Hp3 : fst p = Chain 3)
    by (apply (standard_move_three G p H3); exact Hm).
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  pose proof (selections_perm G p Hin) as Hperm.
  assert (Htb : tb (fst p :: snd p) = tb (snd p))
    by (rewrite Hp3; apply tb_cons_3chain_not_all_loops; exact Hnl).
  assert (Hcr : cval (snd p) = cval G + 1).
  { rewrite <- (cval_perm _ _ Hperm).
    unfold cval; rewrite cbase_cons, Htb, Hp3, weight_chain; cbn [Z.of_nat].
    unfold cval; lia. }
  apply (standard_move_optimal_of_criterion G p Hw Hm Htb);
    [rewrite Hp3; cbn [hand]; lia | lia].
Qed.

(** * With no three-chain, the standard move opens a loop *)

Lemma shortest_of_none_of_no_witness :
  forall f G, (forall C, In C G -> f C = false) -> shortest_of f G = None.
Proof.
  intros f G H; unfold shortest_of.
  destruct (filter (fun p => f (fst p)) (selections G)) as [|p l] eqn:E;
    [reflexivity|].
  exfalso.
  assert (Hin : In p (filter (fun q => f (fst q)) (selections G)))
    by (rewrite E; left; reflexivity).
  apply filter_In in Hin; destruct Hin as [Hsel Hf].
  assert (HinG : In (fst p) G) by (apply selections_In; exact Hsel).
  rewrite (H (fst p) HinG) in Hf; discriminate.
Qed.

Lemma no_3chain_of_count0 :
  forall G, count3 G = 0%nat -> forall C, In C G -> is_3chain_b C = false.
Proof.
  intros G H C HC; destruct (is_3chain_b C) eqn:E; [|reflexivity].
  exfalso; unfold count3 in H.
  assert (Hin : In C (filter is_3chain_b G))
    by (apply filter_In; split; assumption).
  destruct (filter is_3chain_b G); [destruct Hin | simpl in H; lia].
Qed.

Lemma standard_move_loop :
  forall G p,
    count3 G = 0%nat -> standard_move G = Some p ->
    is_loop_b (fst p) = true \/ shortest_of is_loop_b G = None.
Proof.
  intros G p H3 Hm; unfold standard_move in Hm.
  rewrite (shortest_of_none_of_no_witness is_3chain_b G
             (no_3chain_of_count0 G H3)) in Hm.
  destruct (shortest_of is_loop_b G) as [q|] eqn:EL; [|right; reflexivity].
  injection Hm as <-; left.
  destruct (shortest_of_min is_loop_b G q EL) as [Hq _]; exact Hq.
Qed.

(** * The standard move on a loop *)

(** With no three-chain anywhere the bonus is unmoved, so only the remainder's
    controlled value has to clear four, and that is a bound on the loop's own
    length against the position. *)
Theorem standard_move_loop_optimal :
  forall G p,
    wf G -> count3 G = 0%nat -> standard_move G = Some p ->
    is_loop_b (fst p) = true -> snd p <> [] ->
    Z.of_nat (csize (fst p)) - 4 <= cval G ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hloop Hnil Hb.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  pose proof (selections_perm G p Hin) as Hperm.
  assert (H3c : existsb is_3chain_b (fst p :: snd p) = false).
  { apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    assert (HDG : In D G) by (apply (Permutation_in _ Hperm); exact HD).
    rewrite (no_3chain_of_count0 G H3 D HDG) in HDf; discriminate. }
  assert (Htb : tb (fst p :: snd p) = tb (snd p))
    by (apply tb_remove_loop_no3; assumption).
  assert (Hcr : cval (snd p) = cval G - Z.of_nat (csize (fst p)) + 8).
  { rewrite <- (cval_perm _ _ Hperm).
    assert (Ew : weight (fst p) = Z.of_nat (csize (fst p)) - 8)
      by (destruct (fst p) as [n | n]; [discriminate Hloop | apply weight_loop]).
    unfold cval; rewrite cbase_cons, Htb, Ew; unfold cval; lia. }
  apply (standard_move_optimal_of_criterion G p Hw Hm Htb).
  - destruct (fst p) as [n | n]; [discriminate Hloop|].
    cbn [hand csize] in *; lia.
  - lia.
Qed.

(** * The standard move on a chain *)

Lemma no_member_of_count0 :
  forall (f : comp -> bool) G,
    length (filter f G) = 0%nat -> forall C, In C G -> f C = false.
Proof.
  intros f G H C HC; destruct (f C) eqn:E; [|reflexivity].
  exfalso.
  assert (Hin : In C (filter f G)) by (apply filter_In; split; assumption).
  destruct (filter f G); [destruct Hin | simpl in H; lia].
Qed.

Lemma cbase_nonneg_of_weights :
  forall G, (forall D, In D G -> 0 <= weight D) -> 0 <= cbase G.
Proof.
  induction G as [|D G IH]; intros Hw; [reflexivity|].
  rewrite cbase_cons.
  pose proof (Hw D (or_introl eq_refl)).
  pose proof (IH (fun E HE => Hw E (or_intror HE))); lia.
Qed.

Lemma cbase_ge_member :
  forall G C,
    In C G -> (forall D, In D G -> 0 <= weight D) -> weight C <= cbase G.
Proof.
  induction G as [|D G IH]; intros C HC Hw; [destruct HC|].
  rewrite cbase_cons; destruct HC as [<- | HC].
  - pose proof (cbase_nonneg_of_weights G (fun E HE => Hw E (or_intror HE)));
      lia.
  - pose proof (IH C HC (fun E HE => Hw E (or_intror HE))).
    pose proof (Hw D (or_introl eq_refl)); lia.
Qed.

(** With neither a three-chain nor a loop every component is a chain of at
    least four boxes, so every weight is nonnegative and the position's
    controlled value already exceeds the chain that is opened. The bonus is
    four on both sides, so the criterion needs nothing further. *)
Theorem standard_move_chain_optimal :
  forall G p,
    wf G -> count3 G = 0%nat -> count_loops G = 0%nat ->
    standard_move G = Some p -> snd p <> [] ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 HL Hm Hnil.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  pose proof (selections_perm G p Hin) as Hperm.
  assert (Hnl : forall C, In C G -> is_loop_b C = false)
    by (apply (no_member_of_count0 is_loop_b G); exact HL).
  assert (Hn3 : forall C, In C G -> is_3chain_b C = false)
    by (apply no_3chain_of_count0; exact H3).
  (* every component is a chain of at least four boxes *)
  assert (Hbig : forall C, In C G -> (4 <= csize C)%nat).
  { intros C HC; pose proof (Hnl C HC) as H1; pose proof (Hn3 C HC) as H2.
    unfold wf in Hw; rewrite Forall_forall in Hw; specialize (Hw C HC).
    destruct C as [n | n]; [|discriminate H1].
    cbn [wf_comp] in Hw; cbn [csize].
    destruct (Nat.eq_dec n 3) as [-> | Hne]; [discriminate H2 | lia]. }
  assert (Hwt : forall D, In D G -> 0 <= weight D).
  { intros D HD; pose proof (Hbig D HD); pose proof (Hnl D HD).
    destruct D as [n | n]; [|discriminate].
    rewrite weight_chain; cbn [csize] in *; lia. }
  (* the bonus is four on both sides *)
  assert (HeG : existsb is_loop_b G = false).
  { apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    rewrite (Hnl D HD) in HDf; discriminate. }
  assert (HeR : existsb is_loop_b (snd p) = false).
  { apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    assert (HDG : In D G)
      by (apply (Permutation_in _ Hperm); right; exact HD).
    rewrite (Hnl D HDG) in HDf; discriminate. }
  assert (HNil : G <> []) by (intros ->; simpl in Hin; destruct Hin).
  assert (HtbG : tb G = 4) by (apply tb_no_loops; assumption).
  assert (HtbR : tb (snd p) = 4) by (apply tb_no_loops; assumption).
  assert (Htb : tb (fst p :: snd p) = tb (snd p)).
  { rewrite HtbR, <- HtbG; apply tb_perm; exact Hperm. }
  (* the controlled value already exceeds the opened chain *)
  assert (HinC : In (fst p) G) by (apply selections_In; exact Hin).
  assert (Hge : weight (fst p) <= cbase G)
    by (apply cbase_ge_member; assumption).
  assert (Hcr : cval (snd p) = cval G - weight (fst p)).
  { rewrite <- (cval_perm _ _ Hperm).
    unfold cval; rewrite cbase_cons, Htb; unfold cval; lia. }
  assert (HcG : cval G = cbase G + 4) by (unfold cval; rewrite HtbG; lia).
  apply (standard_move_optimal_of_criterion G p Hw Hm Htb).
  - assert (Hlp : is_loop_b (fst p) = false) by (apply Hnl; exact HinC).
    assert (Hh : (hand (fst p) = 2)%nat)
      by (destruct (fst p) as [n | n]; [reflexivity | discriminate Hlp]).
    rewrite Hh; cbn [Z.of_nat]; lia.
  - lia.
Qed.

(** * Below the threshold: opening a four-loop *)

(** With no three-chain and the controlled value under two, both the position
    and what a four-loop leaves are read from [DotsAndBoxes.w38], and removing
    the loop shifts the table by exactly the four that
    [DotsAndBoxes.w38_step] records. *)
Theorem standard_move_4loop_below :
  forall G p,
    wf G -> count3 G = 0%nat -> standard_move G = Some p ->
    fst p = Loop 4 -> snd p <> [] ->
    cval G < 2 -> cval (snd p) < 2 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hp4 Hnil HcG Hcr2.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  pose proof (selections_perm G p Hin) as Hperm.
  assert (HNil : G <> []) by (intros ->; simpl in Hin; destruct Hin).
  assert (Hn3 : forall C, In C G -> is_3chain_b C = false)
    by (apply no_3chain_of_count0; exact H3).
  assert (HeG : existsb is_3chain_b G = false).
  { apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    rewrite (Hn3 D HD) in HDf; discriminate. }
  assert (HeR : existsb is_3chain_b (snd p) = false).
  { apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    assert (HDG : In D G)
      by (apply (Permutation_in _ Hperm); right; exact HD).
    rewrite (Hn3 D HDG) in HDf; discriminate. }
  assert (Hwr : wf (snd p))
    by (destruct (selections_wf G p Hw Hin) as [_ H]; exact H).
  (* both sides are read from the same table *)
  assert (HvG : value G = w38 (cval G) (count4 G))
    by (apply value_no3; assumption).
  assert (HvR : value (snd p) = w38 (cval (snd p)) (count4 (snd p)))
    by (apply value_no3; assumption).
  (* the bonus is unmoved and the controlled value rises by four *)
  assert (Htb : tb (fst p :: snd p) = tb (snd p)).
  { apply tb_remove_loop_no3; [rewrite Hp4; reflexivity | | exact Hnil].
    apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    assert (HDG : In D G) by (apply (Permutation_in _ Hperm); exact HD).
    rewrite (Hn3 D HDG) in HDf; discriminate. }
  assert (Hcr : cval (snd p) = cval G + 4).
  { rewrite <- (cval_perm _ _ Hperm).
    unfold cval; rewrite cbase_cons, Htb, Hp4.
    assert (Ew : weight (Loop 4) = -4) by reflexivity.
    rewrite Ew; unfold cval; lia. }
  assert (Hc4 : count4 G = S (count4 (snd p))).
  { rewrite <- (count4_perm _ _ Hperm), Hp4, count4_cons; reflexivity. }
  (* the opening is a distance from four, and the table shifts by four *)
  assert (Hval : value G = value_open p).
  { unfold value_open; rewrite Hp4 at 1; rewrite HvR, vopen_loop4, HvG.
    pose proof (w38_range (cval (snd p)) (count4 (snd p))) as Hb.
    rewrite Z.abs_neq by lia.
    rewrite Hc4, Hcr.
    pose proof (w38_step (cval G) (count4 (snd p))); lia. }
  split; [exact Hval|].
  apply (opener_optimal_iff G p HNil Hin); exact Hval.
Qed.

(** * Across the threshold: opening a four-loop *)

(** When the four-loop lifts the remainder over the threshold, the two sides
    are computed by different formulas and have to be reconciled. They agree:
    the remainder is its own controlled value, so the opening is the distance
    from that to four, which is the absolute controlled value of the position;
    and with a four-loop present [DotsAndBoxes.w38] is on its [w10] branch,
    where [DotsAndBoxes.w10_small] is exactly that absolute value. *)
Theorem standard_move_4loop_cross :
  forall G p,
    wf G -> count3 G = 0%nat -> standard_move G = Some p ->
    fst p = Loop 4 -> snd p <> [] ->
    cval G < 2 -> 2 <= cval (snd p) ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hp4 Hnil HcG Hcr2.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  pose proof (selections_perm G p Hin) as Hperm.
  assert (HNil : G <> []) by (intros ->; simpl in Hin; destruct Hin).
  assert (Hn3 : forall C, In C G -> is_3chain_b C = false)
    by (apply no_3chain_of_count0; exact H3).
  assert (HeG : existsb is_3chain_b G = false).
  { apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    rewrite (Hn3 D HD) in HDf; discriminate. }
  assert (Hwr : wf (snd p))
    by (destruct (selections_wf G p Hw Hin) as [_ H]; exact H).
  assert (HvG : value G = w38 (cval G) (count4 G))
    by (apply value_no3; assumption).
  assert (HvR : value (snd p) = cval (snd p))
    by (apply value_cval_ge2; assumption).
  assert (Htb : tb (fst p :: snd p) = tb (snd p)).
  { apply tb_remove_loop_no3; [rewrite Hp4; reflexivity | | exact Hnil].
    apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    assert (HDG : In D G) by (apply (Permutation_in _ Hperm); exact HD).
    rewrite (Hn3 D HDG) in HDf; discriminate. }
  assert (Hcr : cval (snd p) = cval G + 4).
  { rewrite <- (cval_perm _ _ Hperm).
    unfold cval; rewrite cbase_cons, Htb, Hp4.
    assert (Ew : weight (Loop 4) = -4) by reflexivity.
    rewrite Ew; unfold cval; lia. }
  assert (Hc4 : count4 G = S (count4 (snd p))).
  { rewrite <- (count4_perm _ _ Hperm), Hp4, count4_cons; reflexivity. }
  (* the four-loop puts the table on its small branch *)
  assert (Hbr : (2 <=? cval G + 4 * Z.of_nat (count4 G)) = true)
    by (apply Z.leb_le; rewrite Hc4; lia).
  assert (Hw10 : w38 (cval G) (count4 G) = Z.abs (cval G)).
  { unfold w38; rewrite Hbr; apply w10_small; lia. }
  assert (Hval : value G = value_open p).
  { unfold value_open; rewrite Hp4 at 1; rewrite HvR, vopen_loop4, HvG, Hw10.
    rewrite Hcr; f_equal; lia. }
  split; [exact Hval|].
  apply (opener_optimal_iff G p HNil Hin); exact Hval.
Qed.

(** * Opening a six-loop *)

Lemma vopen_loop6 : forall w, w <= 4 -> vopen (Loop 6) w = 6 - w.
Proof.
  intros w H; rewrite vopen_max; cbn [csize hand].
  rewrite Z.max_l by lia; lia.
Qed.

(** With neither a three-chain nor a four-loop the value is read from the
    board's size alone, and [DotsAndBoxes.w4z_step6] is exactly what removing
    six boxes does to that reading. *)
Theorem standard_move_6loop :
  forall G p,
    wf G -> count3 G = 0%nat -> count4 G = 0%nat ->
    standard_move G = Some p ->
    is_loop_b (fst p) = true -> csize (fst p) = 6%nat -> snd p <> [] ->
    cval G < 2 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 H4 Hm Hloop Hsz Hnil HcG.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  pose proof (selections_perm G p Hin) as Hperm.
  assert (HNil : G <> []) by (intros ->; simpl in Hin; destruct Hin).
  assert (Hn3 : forall C, In C G -> is_3chain_b C = false)
    by (apply no_3chain_of_count0; exact H3).
  assert (Hn4 : forall C, In C G -> is_4loop_b C = false)
    by (apply (no_member_of_count0 is_4loop_b G); exact H4).
  assert (Hmem : forall (f : comp -> bool),
            (forall C, In C G -> f C = false) -> existsb f (snd p) = false).
  { intros f Hf; apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    assert (HDG : In D G)
      by (apply (Permutation_in _ Hperm); right; exact HD).
    rewrite (Hf D HDG) in HDf; discriminate. }
  assert (HmemG : forall (f : comp -> bool),
            (forall C, In C G -> f C = false) -> existsb f G = false).
  { intros f Hf; apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    rewrite (Hf D HD) in HDf; discriminate. }
  assert (Hwr : wf (snd p))
    by (destruct (selections_wf G p Hw Hin) as [_ H]; exact H).
  (* the opened component is a six-loop *)
  assert (Hp6 : fst p = Loop 6).
  { destruct (fst p) as [n | n]; [discriminate Hloop|].
    cbn [csize] in Hsz; rewrite Hsz; reflexivity. }
  (* the bonus is unmoved, so the controlled value rises by two *)
  assert (Htb : tb (fst p :: snd p) = tb (snd p)).
  { apply tb_remove_loop_no3; [exact Hloop | | exact Hnil].
    apply not_true_is_false; intros Hc.
    apply existsb_exists in Hc; destruct Hc as [D [HD HDf]].
    assert (HDG : In D G) by (apply (Permutation_in _ Hperm); exact HD).
    rewrite (Hn3 D HDG) in HDf; discriminate. }
  assert (Hcr : cval (snd p) = cval G + 2).
  { rewrite <- (cval_perm _ _ Hperm).
    unfold cval; rewrite cbase_cons, Htb, Hp6.
    assert (Ew : weight (Loop 6) = -2) by reflexivity.
    rewrite Ew; unfold cval; lia. }
  (* both sides are read from the board's size *)
  assert (HvG : value G = w4z (Z.of_nat (size G)))
    by (apply value_no34; try assumption;
        [apply HmemG; exact Hn3 | apply HmemG; exact Hn4 | lia]).
  assert (HvR : value (snd p) = w4z (Z.of_nat (size (snd p))))
    by (apply value_no34; try assumption;
        [apply Hmem; exact Hn3 | apply Hmem; exact Hn4 | lia]).
  assert (Hszr : (6 + size (snd p))%nat = size G).
  { rewrite <- Hsz; exact (selections_size G p Hin). }
  assert (Hval : value G = value_open p).
  { unfold value_open; rewrite Hp6 at 1; rewrite HvR.
    pose proof (w4z_range (Z.of_nat (size (snd p)))) as Hr.
    rewrite vopen_loop6 by lia.
    rewrite HvG.
    pose proof (w4z_step6 (Z.of_nat (size G))) as Hs.
    assert (E : Z.of_nat (size G) - 6 = Z.of_nat (size (snd p))) by lia.
    rewrite E in Hs.
    rewrite Z.abs_neq in Hs by lia; lia. }
  split; [exact Hval|].
  apply (opener_optimal_iff G p HNil Hin); exact Hval.
Qed.

(** * A single component *)

(** With one component there is nothing to choose: the opener takes it whole
    and the position is worth its own size. *)
Lemma vopen_zero : forall C, vopen C 0 = Z.of_nat (csize C).
Proof.
  intros C; rewrite vopen_max.
  pose proof (Nat2Z.is_nonneg (hand C)); rewrite Z.max_l by lia; lia.
Qed.

Theorem standard_move_singleton :
  forall G p,
    standard_move G = Some p -> snd p = [] ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hm Hnil.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  pose proof (selections_perm G p Hin) as Hperm.
  rewrite Hnil in Hperm.
  apply Permutation_length_1_inv in Hperm.
  assert (Hval : value G = value_open p).
  { rewrite Hperm, value_single.
    unfold value_open; rewrite Hnil.
    assert (Hz : value (@nil comp) = 0) by reflexivity.
    rewrite Hz, vopen_zero; reflexivity. }
  split; [exact Hval|].
  assert (HNil : G <> []) by (rewrite Hperm; discriminate).
  apply (opener_optimal_iff G p HNil Hin); exact Hval.
Qed.

(** * The three-chain block, reduced to the closed form *)

(** Opening a three-chain costs one plus the distance from two, so with
    [DotsAndBoxes.value_complete] on both sides the whole block reduces to an
    identity between the closed form at the position and at what is left. That
    turns the remaining work from a statement about play into arithmetic. *)
Theorem standard_move_3chain_reduces :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    v41 G = 1 + Z.abs (v41 (snd p) - 2) ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil Hid.
  assert (Hp3 : fst p = Chain 3)
    by (apply (standard_move_three G p H3); exact Hm).
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  assert (HNil : G <> []) by (intros ->; simpl in Hin; destruct Hin).
  assert (Hwr : wf (snd p))
    by (destruct (selections_wf G p Hw Hin) as [_ H]; exact H).
  assert (Hval : value G = value_open p).
  { unfold value_open; rewrite Hp3 at 1; rewrite vopen_chain3.
    rewrite (value_complete G Hw HNil).
    rewrite (value_complete (snd p) Hwr Hnil); exact Hid. }
  split; [exact Hval|].
  apply (opener_optimal_iff G p HNil Hin); exact Hval.
Qed.

(** The same for the whole standard move, whatever it opens: the block reduces
    to comparing the closed form against the opening of the closed form. *)
Theorem standard_move_reduces :
  forall G p,
    wf G -> standard_move G = Some p -> snd p <> [] ->
    v41 G = vopen (fst p) (v41 (snd p)) ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hm Hnil Hid.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  assert (HNil : G <> []) by (intros ->; simpl in Hin; destruct Hin).
  assert (Hwr : wf (snd p))
    by (destruct (selections_wf G p Hw Hin) as [_ H]; exact H).
  assert (Hval : value G = value_open p).
  { unfold value_open.
    rewrite (value_complete G Hw HNil).
    rewrite (value_complete (snd p) Hwr Hnil); exact Hid. }
  split; [exact Hval|].
  apply (opener_optimal_iff G p HNil Hin); exact Hval.
Qed.

(** * The closed form on its last branch *)

(** Where none of the earlier branches applies, the classifier is read from the
    board's parity alone. *)
Lemma v41_branch5 :
  forall G,
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    (1 <= count3 G)%nat ->
    ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool = false ->
    v41 G = if Z.even (Z.of_nat (size G)) then 2 else 1.
Proof.
  intros G Hc H2 H3 H4; unfold v41.
  rewrite (proj2 (Z.leb_gt 2 (cval G))) by lia.
  rewrite H2.
  rewrite (proj2 (Nat.eqb_neq (count3 G) 0)) by lia.
  rewrite H4; reflexivity.
Qed.

(** Opening a three-chain takes three boxes, so the parity flips and the
    classifier alternates between two and one. That is exactly the cost of the
    opening, so the identity holds outright. *)
Theorem standard_move_3chain_parity :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool = false ->
    (1 <= count3 (snd p))%nat ->
    cval (snd p) < 2 ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = false ->
    ((count3 (snd p) =? 1)%nat
     && (Z.of_nat (size (snd p)) mod 4 =? 3))%bool = false ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G H4G H3r HcR H2R H4R.
  assert (Hp3 : fst p = Chain 3)
    by (apply (standard_move_three G p H3); exact Hm).
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  assert (Hsz : (3 + size (snd p))%nat = size G).
  { pose proof (selections_size G p Hin) as H; rewrite Hp3 in H; exact H. }
  apply (standard_move_3chain_reduces G p Hw H3 Hm Hnil).
  rewrite (v41_branch5 G HcG H2G H3 H4G).
  rewrite (v41_branch5 (snd p) HcR H2R H3r H4R).
  assert (Hpar : Z.even (Z.of_nat (size G))
                 = negb (Z.even (Z.of_nat (size (snd p))))).
  { assert (E : Z.of_nat (size G) = Z.of_nat (size (snd p)) + 3) by lia.
    rewrite E, Z.even_add; cbn [Z.even].
    destruct (Z.even (Z.of_nat (size (snd p)))); reflexivity. }
  rewrite Hpar.
  destruct (Z.even (Z.of_nat (size (snd p)))); reflexivity.
Qed.

(** * The closed form on its four-loop branch *)

Lemma v41_branch2 :
  forall G,
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = true ->
    v41 G = Z.abs (cval G).
Proof.
  intros G Hc H; unfold v41.
  rewrite (proj2 (Z.leb_gt 2 (cval G))) by lia.
  rewrite H; reflexivity.
Qed.

(** With the position and its remainder both on that branch, the controlled
    value is pinned: the case's own exclusions leave only minus two, where the
    opening's cost matches exactly. *)
Theorem standard_move_3chain_both_4loop :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G = -2 -> cval (snd p) = -1 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = true ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = true ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG HcR H2G H2R.
  apply (standard_move_3chain_reduces G p Hw H3 Hm Hnil).
  rewrite (v41_branch2 G ltac:(lia) H2G).
  rewrite (v41_branch2 (snd p) ltac:(lia) H2R).
  rewrite HcG, HcR; reflexivity.
Qed.

(** And where the position is on the parity branch while the remainder is on
    the four-loop branch at minus two, the remainder is worth two and the
    opening costs nothing beyond its own one. *)
Theorem standard_move_3chain_parity_over_4loop :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool = false ->
    Z.even (Z.of_nat (size G)) = false ->
    cval (snd p) = -2 ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = true ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G H4G Hodd HcR H2R.
  apply (standard_move_3chain_reduces G p Hw H3 Hm Hnil).
  rewrite (v41_branch5 G HcG H2G H3 H4G), Hodd.
  rewrite (v41_branch2 (snd p) ltac:(lia) H2R), HcR; reflexivity.
Qed.

(** * The closed form on its remaining branches *)

Lemma v41_branch1 : forall G, 2 <= cval G -> v41 G = cval G.
Proof.
  intros G H; unfold v41; rewrite (proj2 (Z.leb_le 2 (cval G))) by lia.
  reflexivity.
Qed.

Lemma v41_branch4 :
  forall G,
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    count3 G = 1%nat -> Z.of_nat (size G) mod 4 = 3 ->
    v41 G = w310 (cval G) (count4 G).
Proof.
  intros G Hc H2 H3 Hmod; unfold v41.
  rewrite (proj2 (Z.leb_gt 2 (cval G))) by lia.
  rewrite H2.
  rewrite (proj2 (Nat.eqb_neq (count3 G) 0)) by lia.
  rewrite (proj2 (Nat.eqb_eq (count3 G) 1)) by exact H3.
  rewrite (proj2 (Z.eqb_eq (Z.of_nat (size G) mod 4) 3)) by exact Hmod.
  reflexivity.
Qed.

(** * The last three branch pairs *)

(** Each is settled by reading both sides and comparing: opening a three-chain
    costs one plus the distance from two, and in every pair the two readings
    differ by exactly that. *)
Theorem standard_move_3chain_w310_over_value :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    count3 G = 1%nat -> Z.of_nat (size G) mod 4 = 3 ->
    w310 (cval G) (count4 G) = 3 ->
    cval (snd p) = 4 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G Hc1 Hmod Hw310 HcR.
  apply (standard_move_3chain_reduces G p Hw H3 Hm Hnil).
  rewrite (v41_branch4 G HcG H2G Hc1 Hmod), Hw310.
  rewrite (v41_branch1 (snd p) ltac:(lia)), HcR; reflexivity.
Qed.

Theorem standard_move_3chain_parity_over_w310 :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool = false ->
    Z.even (Z.of_nat (size G)) = true ->
    cval (snd p) < 2 ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = false ->
    count3 (snd p) = 1%nat -> Z.of_nat (size (snd p)) mod 4 = 3 ->
    w310 (cval (snd p)) (count4 (snd p)) = 3 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G H4G Hev HcR H2R Hc1R HmodR Hw310.
  apply (standard_move_3chain_reduces G p Hw H3 Hm Hnil).
  rewrite (v41_branch5 G HcG H2G H3 H4G), Hev.
  rewrite (v41_branch4 (snd p) HcR H2R Hc1R HmodR), Hw310; reflexivity.
Qed.

Theorem standard_move_3chain_parity_over_value :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool = false ->
    Z.even (Z.of_nat (size G)) = false ->
    cval (snd p) = 2 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G H4G Hodd HcR.
  apply (standard_move_3chain_reduces G p Hw H3 Hm Hnil).
  rewrite (v41_branch5 G HcG H2G H3 H4G), Hodd.
  rewrite (v41_branch1 (snd p) ltac:(lia)), HcR; reflexivity.
Qed.

(** * The closed form when the last three-chain has gone *)

Lemma v41_branch3 :
  forall G,
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    count3 G = 0%nat ->
    v41 G = w38 (cval G) (count4 G).
Proof.
  intros G Hc H2 H3; unfold v41.
  rewrite (proj2 (Z.leb_gt 2 (cval G))) by lia.
  rewrite H2.
  rewrite (proj2 (Nat.eqb_eq (count3 G) 0)) by exact H3.
  reflexivity.
Qed.

(** Opening the only three-chain moves the remainder onto the three-chain-free
    branch, and the two readings differ by the cost of the opening. *)
Theorem standard_move_3chain_w310_over_w38 :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    count3 G = 1%nat -> Z.of_nat (size G) mod 4 = 3 ->
    w310 (cval G) (count4 G) = 3 ->
    cval (snd p) < 2 ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = false ->
    count3 (snd p) = 0%nat ->
    w38 (cval (snd p)) (count4 (snd p)) = 4 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G Hc1 Hmod Hw310 HcR H2R Hc0R Hw38.
  apply (standard_move_3chain_reduces G p Hw H3 Hm Hnil).
  rewrite (v41_branch4 G HcG H2G Hc1 Hmod), Hw310.
  rewrite (v41_branch3 (snd p) HcR H2R Hc0R), Hw38; reflexivity.
Qed.

Theorem standard_move_3chain_parity_over_w38 :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool = false ->
    Z.even (Z.of_nat (size G)) = true ->
    cval (snd p) < 2 ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = false ->
    count3 (snd p) = 0%nat ->
    w38 (cval (snd p)) (count4 (snd p)) = 3 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G H4G Hev HcR H2R Hc0R Hw38.
  apply (standard_move_3chain_reduces G p Hw H3 Hm Hnil).
  rewrite (v41_branch5 G HcG H2G H3 H4G), Hev.
  rewrite (v41_branch3 (snd p) HcR H2R Hc0R), Hw38; reflexivity.
Qed.

(** * Discharging the table value from the position *)

(** With no four-loop the three-chain table is read at zero, where it is three
    whatever the controlled value, so the numeric hypothesis is not needed. *)
Lemma w310_no4loop : forall c, c < 2 -> w310 c 0 = 3.
Proof.
  intros c H; unfold w310.
  replace (c + 4 * Z.of_nat 0) with c by (cbn [Z.of_nat]; lia).
  rewrite (proj2 (Z.leb_gt 2 c)) by lia; reflexivity.
Qed.

Corollary standard_move_3chain_w310_over_value' :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    count3 G = 1%nat -> Z.of_nat (size G) mod 4 = 3 ->
    count4 G = 0%nat ->
    cval (snd p) = 4 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G Hc1 Hmod H4 HcR.
  apply (standard_move_3chain_w310_over_value G p Hw H3 Hm Hnil HcG H2G
           Hc1 Hmod); [rewrite H4; apply w310_no4loop; exact HcG | exact HcR].
Qed.

Corollary standard_move_3chain_w310_over_w38' :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    count3 G = 1%nat -> Z.of_nat (size G) mod 4 = 3 ->
    count4 G = 0%nat ->
    cval (snd p) < 2 ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = false ->
    count3 (snd p) = 0%nat ->
    w38 (cval (snd p)) (count4 (snd p)) = 4 ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G Hc1 Hmod H4 HcR H2R Hc0R Hw38.
  apply (standard_move_3chain_w310_over_w38 G p Hw H3 Hm Hnil HcG H2G
           Hc1 Hmod);
    [rewrite H4; apply w310_no4loop; exact HcG
     | exact HcR | exact H2R | exact Hc0R | exact Hw38].
Qed.

(** * The three-chain-free table at the values that arise *)

(** On the remainders that arise here the table is read at a fixed point, so
    the numeric hypothesis is a computation rather than an assumption. Which
    branch of [DotsAndBoxes.w38] does the reading differs between them: the
    first two fall to [w11], the third to [w10]. *)
Lemma w38_at_0_0 : w38 0 0 = 4.
Proof. reflexivity. Qed.

Lemma w38_at_1_0 : w38 1 0 = 3.
Proof. reflexivity. Qed.

Lemma w38_at_m3_2 : w38 (-3) 2 = 3.
Proof. reflexivity. Qed.

Corollary standard_move_3chain_w310_over_w38_at0 :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    count3 G = 1%nat -> Z.of_nat (size G) mod 4 = 3 -> count4 G = 0%nat ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = false ->
    count3 (snd p) = 0%nat ->
    cval (snd p) = 0 -> count4 (snd p) = 0%nat ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G Hc1 Hmod H4 H2R Hc0R HcR H4R.
  apply (standard_move_3chain_w310_over_w38' G p Hw H3 Hm Hnil HcG H2G
           Hc1 Hmod H4); [lia | exact H2R | exact Hc0R |].
  rewrite HcR, H4R; exact w38_at_0_0.
Qed.

Corollary standard_move_3chain_parity_over_w38_at1 :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool = false ->
    Z.even (Z.of_nat (size G)) = true ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = false ->
    count3 (snd p) = 0%nat ->
    cval (snd p) = 1 -> count4 (snd p) = 0%nat ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G H4G Hev H2R Hc0R HcR H4R.
  apply (standard_move_3chain_parity_over_w38 G p Hw H3 Hm Hnil HcG H2G
           H4G Hev); [lia | exact H2R | exact Hc0R |].
  rewrite HcR, H4R; exact w38_at_1_0.
Qed.

Corollary standard_move_3chain_parity_over_w38_atm3 :
  forall G p,
    wf G -> (1 <= count3 G)%nat -> standard_move G = Some p -> snd p <> [] ->
    cval G < 2 ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = false ->
    ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool = false ->
    Z.even (Z.of_nat (size G)) = true ->
    (existsb is_4loop_b (snd p) && negb (only34 (snd p))
     && (-2 <=? cval (snd p)))%bool = false ->
    count3 (snd p) = 0%nat ->
    cval (snd p) = -3 -> count4 (snd p) = 2%nat ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hnil HcG H2G H4G Hev H2R Hc0R HcR H4R.
  apply (standard_move_3chain_parity_over_w38 G p Hw H3 Hm Hnil HcG H2G
           H4G Hev); [lia | exact H2R | exact Hc0R |].
  rewrite HcR, H4R; exact w38_at_m3_2.
Qed.

(** * Why the priority ordering is needed *)

(** Opening a shortest component is not optimal in general. On a six-loop
    beside a four-chain the chain is the shorter component, but opening it
    hands over six where opening the loop hands over two. So the strategy's
    ordering of three-chain before loop before chain is doing real work, and
    the case analysis above cannot be replaced by a rule that simply takes the
    shortest component available. *)
Example shortest_is_not_optimal :
  value [Loop 6; Chain 4] = 2
  /\ value_open (Chain 4, [Loop 6]) = 6
  /\ value_open (Loop 6, [Chain 4]) = 2.
Proof. repeat split; reflexivity. Qed.

(** The standard move takes the loop there, since no three-chain is present. *)
Example standard_move_takes_the_loop :
  standard_move [Loop 6; Chain 4] = Some (Loop 6, [Chain 4]).
Proof. reflexivity. Qed.

(** * The loop block is covered outright *)

Lemma standard_move_is_shortest_loop :
  forall G p,
    count3 G = 0%nat -> standard_move G = Some p ->
    is_loop_b (fst p) = true ->
    shortest_of is_loop_b G = Some p.
Proof.
  intros G p H3 Hm Hloop.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  assert (HinC : In (fst p) G) by (apply selections_In; exact Hin).
  unfold standard_move in Hm.
  rewrite (shortest_of_none_of_no_witness is_3chain_b G
             (no_3chain_of_count0 G H3)) in Hm.
  destruct (shortest_of is_loop_b G) as [q|] eqn:EL.
  - exact Hm.
  - exfalso.
    rewrite (shortest_of_none is_loop_b G EL (fst p) HinC) in Hloop;
      discriminate.
Qed.

(** A shortest loop of eight boxes or more leaves every weight nonnegative, so
    the position's controlled value already clears the bound; a four-loop or a
    six-loop that does not clear it falls under the other two cases. The three
    together therefore leave nothing over. *)
Theorem loop_block_exhaustive :
  forall G p,
    wf G -> count3 G = 0%nat -> standard_move G = Some p ->
    is_loop_b (fst p) = true ->
    Z.of_nat (csize (fst p)) - 4 <= cval G
    \/ (is_4loop_b (fst p) = true /\ cval G < 2)
    \/ (count4 G = 0%nat /\ csize (fst p) = 6%nat /\ cval G < 2).
Proof.
  intros G p Hw H3 Hm Hloop.
  assert (Hin : In p (selections G)) by (apply standard_move_In; exact Hm).
  assert (HinC : In (fst p) G) by (apply selections_In; exact Hin).
  assert (HNil : G <> []) by (intros ->; simpl in Hin; destruct Hin).
  pose proof (standard_move_is_shortest_loop G p H3 Hm Hloop) as Hs.
  destruct (shortest_of_min is_loop_b G p Hs) as [_ Hmn].
  assert (Hmin : forall D, In D G -> is_loop_b D = true ->
            (csize (fst p) <= csize D)%nat).
  { intros D HD Hl.
    destruct (In_selections G D HD) as [rest Hsel].
    exact (Hmn (D, rest) Hsel Hl). }
  assert (Hev : (4 <= csize (fst p))%nat /\ Nat.even (csize (fst p)) = true).
  { unfold wf in Hw; rewrite Forall_forall in Hw; specialize (Hw (fst p) HinC).
    destruct (fst p) as [n | n]; [discriminate Hloop|].
    cbn [wf_comp csize] in *; tauto. }
  destruct Hev as [Hge4 Heven].
  destruct (Z.le_gt_cases (Z.of_nat (csize (fst p)) - 4) (cval G))
    as [Hok | Hbad]; [left; exact Hok|].
  assert (Hsmall : (csize (fst p) <= 7)%nat).
  { destruct (Nat.le_gt_cases (csize (fst p)) 7) as [H | H]; [exact H|].
    exfalso.
    assert (Hwt : forall D, In D G -> 0 <= weight D).
    { intros D HD.
      unfold wf in Hw; rewrite Forall_forall in Hw.
      pose proof (Hw D HD) as HwD.
      destruct D as [n | n].
      - assert (Hn3 : is_3chain_b (Chain n) = false)
          by (apply (no_3chain_of_count0 G H3); exact HD).
        cbn [wf_comp] in HwD; rewrite weight_chain; cbn [csize].
        destruct (Nat.eq_dec n 3) as [He | Hne];
          [rewrite He in Hn3; cbn in Hn3; discriminate Hn3 | lia].
      - pose proof (Hmin (Loop n) HD eq_refl) as Hm8.
        rewrite weight_loop; cbn [csize] in *; lia. }
    pose proof (cbase_ge_member G (fst p) HinC Hwt) as Hcb.
    pose proof (tb_pos G HNil) as Htb.
    assert (Hwp : weight (fst p) = Z.of_nat (csize (fst p)) - 8).
    { destruct (fst p) as [n | n]; [discriminate Hloop | apply weight_loop]. }
    unfold cval in Hbad; lia. }
  assert (Hcase : csize (fst p) = 4%nat \/ csize (fst p) = 6%nat).
  { apply Nat.even_spec in Heven; destruct Heven as [k Hk]; lia. }
  destruct Hcase as [H4 | H6].
  - right; left; split; [|lia].
    destruct (fst p) as [n | n]; [discriminate Hloop|].
    cbn [csize] in H4; rewrite H4; reflexivity.
  - right; right; split; [|split; [exact H6 | lia]].
    destruct (count4 G) as [|k] eqn:E4; [reflexivity|].
    exfalso.
    destruct (In_selections G (Loop 4) (count4_pos_In G ltac:(lia)))
      as [rest Hsel].
    pose proof (Hmin (Loop 4) (count4_pos_In G ltac:(lia)) eq_refl) as Hle.
    cbn [csize] in Hle; lia.
Qed.

(** * Positions with no three-chain, outright *)

Lemma count_loops_zero_of_none :
  forall G, shortest_of is_loop_b G = None -> count_loops G = 0%nat.
Proof.
  intros G H; unfold count_loops.
  destruct (filter is_loop_b G) as [|D l] eqn:E; [reflexivity|].
  exfalso.
  assert (Hin : In D (filter is_loop_b G)) by (rewrite E; left; reflexivity).
  apply filter_In in Hin; destruct Hin as [HinG Hf].
  rewrite (shortest_of_none is_loop_b G H D HinG) in Hf; discriminate.
Qed.

(** Every chain has at least four boxes here, so the criterion applies with
    nothing to check. *)
Theorem standard_move_chain_complete :
  forall G p,
    wf G -> count3 G = 0%nat -> count_loops G = 0%nat ->
    standard_move G = Some p ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 HL Hm.
  destruct (list_eq_dec comp_eq_dec (snd p) []) as [Hnil | Hnn].
  - apply (standard_move_singleton G p Hm Hnil).
  - apply (standard_move_chain_optimal G p Hw H3 HL Hm Hnn).
Qed.

(** And with [loop_block_exhaustive] the loop openings are covered too. *)
Theorem standard_move_loop_complete :
  forall G p,
    wf G -> count3 G = 0%nat -> standard_move G = Some p ->
    is_loop_b (fst p) = true ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm Hloop.
  destruct (list_eq_dec comp_eq_dec (snd p) []) as [Hnil | Hnn].
  - apply (standard_move_singleton G p Hm Hnil).
  - destruct (loop_block_exhaustive G p Hw H3 Hm Hloop)
      as [Hb | [[H4 Hc] | [H4 [H6 Hc]]]].
    + apply (standard_move_loop_optimal G p Hw H3 Hm Hloop Hnn Hb).
    + assert (Hp4 : fst p = Loop 4) by (apply is_4loop_b_eq; exact H4).
      destruct (Z.lt_ge_cases (cval (snd p)) 2) as [Hcr | Hcr].
      * apply (standard_move_4loop_below G p Hw H3 Hm Hp4 Hnn Hc Hcr).
      * apply (standard_move_4loop_cross G p Hw H3 Hm Hp4 Hnn Hc Hcr).
    + apply (standard_move_6loop G p Hw H3 H4 Hm Hloop H6 Hnn Hc).
Qed.

(** So the standard move is optimal on every position holding no three-chain,
    with no hypothesis beyond wellformedness. *)
Theorem standard_move_no3_complete :
  forall G p,
    wf G -> count3 G = 0%nat -> standard_move G = Some p ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw H3 Hm.
  destruct (is_loop_b (fst p)) eqn:Hl.
  - apply (standard_move_loop_complete G p Hw H3 Hm Hl).
  - assert (HL : count_loops G = 0%nat).
    { apply count_loops_zero_of_none.
      destruct (shortest_of is_loop_b G) as [q|] eqn:EL; [|reflexivity].
      exfalso.
      assert (Hpq : p = q).
      { unfold standard_move in Hm.
        rewrite (shortest_of_none_of_no_witness is_3chain_b G
                   (no_3chain_of_count0 G H3)), EL in Hm.
        injection Hm as Hm; symmetry; exact Hm. }
      destruct (shortest_of_min is_loop_b G q EL) as [Hq _].
      rewrite Hpq, Hq in Hl; discriminate. }
    apply (standard_move_chain_complete G p Hw H3 HL Hm).
Qed.

(** * Where the four-loop branch can sit *)

(** Three three-chains beside a four-loop is a position of three-chains and
    four-loops, so it can never satisfy the four-loop branch's own exclusion. *)
Lemma three_threes_is_only34 :
  forall G,
    (1 <= count4 G)%nat -> rest_is_three_threes_b G = true -> only34 G = true.
Proof.
  intros G H4 Hr; unfold rest_is_three_threes_b in Hr.
  apply andb_true_iff in Hr; destruct Hr as [Hc3 Hlen].
  apply Nat.eqb_eq in Hc3; apply Nat.eqb_eq in Hlen.
  set (H := drop_first is_4loop_b G) in *.
  assert (Hsel : In (Loop 4, H) (selections G))
    by (apply drop_first_4loop_sel; exact H4).
  pose proof (selections_perm G (Loop 4, H) Hsel) as Hp; simpl in Hp.
  assert (Hall : forallb is_3chain_b H = true)
    by (apply filter_full; unfold count3 in Hc3; rewrite Hc3, Hlen; reflexivity).
  assert (Hcons : only34 (Loop 4 :: H) = true).
  { unfold only34; rewrite forallb_forall; intros C HC.
    destruct HC as [<- | HC]; [reflexivity|].
    rewrite forallb_forall in Hall; rewrite (Hall C HC); reflexivity. }
  apply (only34_perm_inv (Loop 4 :: H) G Hp Hcons).
Qed.

(** So outside the three named cases, a position on the four-loop branch has
    controlled value exactly minus two: the values from minus one to one are
    precisely what case (ii) claims, and the one position case (ii) sets aside
    is not on this branch at all. *)
Theorem branch2_cval_m2 :
  forall G,
    case_ii G = false ->
    (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool = true ->
    cval G < 2 ->
    cval G = -2.
Proof.
  intros G Hii Hb Hlt.
  apply andb_true_iff in Hb; destruct Hb as [Hb Hge].
  apply andb_true_iff in Hb; destruct Hb as [H4 H34].
  apply Z.leb_le in Hge; apply negb_true_iff in H34.
  assert (Hc4 : (1 <= count4 G)%nat) by (apply count4_pos_iff; exact H4).
  unfold case_ii in Hii.
  apply andb_false_iff in Hii; destruct Hii as [Hii | Hnr].
  - apply andb_false_iff in Hii; destruct Hii as [Hii | Hc].
    + apply andb_false_iff in Hii; destruct Hii as [Hle | Hm1].
      * apply Z.leb_gt in Hle; lia.
      * apply Z.leb_gt in Hm1; lia.
    + apply Nat.leb_gt in Hc; lia.
  - apply negb_false_iff in Hnr.
    rewrite (three_threes_is_only34 G Hc4 Hnr) in H34; discriminate.
Qed.

(** ****************************************************************** *)
(** The strategy, assembled.

    [DotsAndBoxes.allcock_move] opens the shortest loop in three cases and
    plays the standard move otherwise. The three cases are proved here:
    whenever one of them applies, the move the strategy names attains the value
    and no opening is better.

    The original development states the strategy and checks it by computation
    through [DotsAndBoxes.allcock_okb], which compares the named move against
    the value on a position at a time. [allcock_named_cases_optimal] replaces
    that check by a proof on those cases, so no computation is needed to know
    the strategy is right when one of them fires. *)

(** * The three named cases *)

Theorem allcock_named_cases_optimal :
  forall G p,
    wf G -> (case_i G || case_ii G || case_iii G)%bool = true ->
    allcock_move G = Some p ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hd Hm.
  destruct (case_i G) eqn:E1.
  - apply (allcock_case_i_optimal G p Hw E1 Hm).
  - destruct (case_ii G) eqn:E2.
    + apply (allcock_case_ii_complete G p Hw E2 Hm).
    + destruct (case_iii G) eqn:E3.
      * apply (allcock_case_iii_optimal G p Hw E3 Hm).
      * exfalso; cbn in Hd; discriminate.
Qed.

(** So on those cases the computational check is redundant: it succeeds. *)
Corollary allcock_okb_named_cases :
  forall G,
    wf G -> (case_i G || case_ii G || case_iii G)%bool = true ->
    allcock_okb G = true.
Proof.
  intros G Hw Hd; unfold allcock_okb.
  destruct (allcock_move G) as [p|] eqn:Hm; [|reflexivity].
  destruct (allcock_named_cases_optimal G p Hw Hd Hm) as [Hval _].
  apply Z.eqb_eq; exact Hval.
Qed.

(** And the strategy opens the shortest loop there, which on a position with a
    four-loop is a four-loop. *)
Corollary allcock_named_cases_move :
  forall G,
    (case_i G || case_ii G || case_iii G)%bool = true ->
    allcock_move G = shortest_of is_loop_b G.
Proof.
  intros G Hd; unfold allcock_move; rewrite Hd; reflexivity.
Qed.

(** * Outside the three cases *)

Lemma allcock_move_standard :
  forall G,
    (case_i G || case_ii G || case_iii G)%bool = false ->
    allcock_move G = standard_move G.
Proof. intros G H; unfold allcock_move; rewrite H; reflexivity. Qed.

(** There the strategy plays the standard move, and [standard_move_reduces]
    turns its optimality into an identity between the closed form at the
    position and at what the move leaves. A position of one component needs
    nothing at all. *)
Theorem allcock_standard_optimal :
  forall G p,
    wf G -> (case_i G || case_ii G || case_iii G)%bool = false ->
    allcock_move G = Some p ->
    (snd p = [] \/ v41 G = vopen (fst p) (v41 (snd p))) ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hd Hm Hcase.
  rewrite (allcock_move_standard G Hd) in Hm.
  destruct (list_eq_dec comp_eq_dec (snd p) []) as [Hnil | Hnn].
  - apply (standard_move_singleton G p Hm Hnil).
  - destruct Hcase as [Hnil | Hid]; [contradiction|].
    apply (standard_move_reduces G p Hw Hm Hnn Hid).
Qed.

(** * The strategy, in one statement *)

(** Allcock's opener is optimal: outright on the three named cases, and
    elsewhere as soon as the closed form at the position agrees with the
    opening of the closed form at what the move leaves behind. *)
Theorem allcock_move_optimal :
  forall G p,
    wf G -> allcock_move G = Some p ->
    ((case_i G || case_ii G || case_iii G)%bool = true
     \/ snd p = []
     \/ v41 G = vopen (fst p) (v41 (snd p))) ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hm Hcase.
  destruct (case_i G || case_ii G || case_iii G)%bool eqn:Hd.
  - apply (allcock_named_cases_optimal G p Hw Hd Hm).
  - apply (allcock_standard_optimal G p Hw Hd Hm).
    destruct Hcase as [Hc | [Hnil | Hid]];
      [rewrite Hc in Hd; discriminate | left; exact Hnil | right; exact Hid].
Qed.
