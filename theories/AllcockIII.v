(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Allcock's Theorem 1.1, case (iii): the arithmetic.

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

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.Shortest.
Require Import GameTrees.Only34.
Require Import GameTrees.AllcockI.
From Stdlib Require Import Sorting.Permutation.

Import ListNotations.

Open Scope Z_scope.

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
