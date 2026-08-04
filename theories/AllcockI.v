(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Allcock's Theorem 1.1, case (i): the arithmetic.

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

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.ShortAll.
Require Import GameTrees.Shortest.
From Stdlib Require Import Sorting.Permutation.

Import ListNotations.

Open Scope Z_scope.

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
