(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** The terminal bonus for the capped recursion.

    Berlekamp's [tb] is eight on a position of loops, six when a loop sits over
    three-chains, and four otherwise. [ShortPairs.tb_does_not_transfer] shows
    that classification is wrong once chains of one or two boxes are admitted:
    it sees a chain that is not a three-chain and drops to its default, where
    the true bonus beside a loop is eight.

    The reading that does extend separates two things the 4/6/8 split conflates.
    [maxsh] is twice the largest handout the position holds, which is what the
    controller can hope to end on. [cap] is what the opener can force her down
    to by holding back a long chain: four when some chain has four boxes or
    more, six when some three-chain is there, eight otherwise. The bonus is the
    smaller, and [stb_eq_tb] proves that on every wellformed position this is
    exactly Berlekamp's [tb]. So the definition is not fitted to the short
    cases; it agrees with his everywhere his applies. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Sorting.Permutation.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.ShortControl.

Import ListNotations.

Open Scope Z_scope.

(** * The two ingredients *)

(** Twice the largest handout in the position. *)
Definition maxsh (G : position) : Z :=
  fold_right (fun C acc => Z.max (2 * Z.of_nat (shand C)) acc) 0 G.

(** A chain of four boxes or more. *)
Definition longchain_b (C : comp) : bool :=
  match C with Chain n => Nat.leb 4 n | Loop _ => false end.

(** What the opener can force the controller down to. *)
Definition cap (G : position) : Z :=
  if existsb longchain_b G then 4
  else if existsb is_3chain_b G then 6
  else 8.

Definition stb (G : position) : Z := Z.min (maxsh G) (cap G).

Definition scval2 (G : position) : Z := scbase G + stb G.

(** * Elementary facts *)

Lemma maxsh_nil : maxsh [] = 0.
Proof. reflexivity. Qed.

Lemma maxsh_cons :
  forall C G, maxsh (C :: G) = Z.max (2 * Z.of_nat (shand C)) (maxsh G).
Proof. reflexivity. Qed.

Lemma maxsh_nonneg : forall G, 0 <= maxsh G.
Proof.
  induction G as [|C G IH]; [reflexivity|].
  rewrite maxsh_cons; lia.
Qed.

Lemma maxsh_perm : forall G H, Permutation G H -> maxsh G = maxsh H.
Proof.
  intros G H HP; induction HP.
  - reflexivity.
  - rewrite !maxsh_cons, IHHP; reflexivity.
  - rewrite !maxsh_cons; lia.
  - congruence.
Qed.

Lemma cap_perm : forall G H, Permutation G H -> cap G = cap H.
Proof.
  intros G H HP; unfold cap.
  rewrite (existsb_perm longchain_b _ _ HP), (existsb_perm is_3chain_b _ _ HP).
  reflexivity.
Qed.

Lemma stb_perm : forall G H, Permutation G H -> stb G = stb H.
Proof.
  intros G H HP; unfold stb.
  rewrite (maxsh_perm _ _ HP), (cap_perm _ _ HP); reflexivity.
Qed.

Lemma scval2_perm : forall G H, Permutation G H -> scval2 G = scval2 H.
Proof.
  intros G H HP; unfold scval2.
  rewrite (scbase_perm _ _ HP), (stb_perm _ _ HP); reflexivity.
Qed.

Lemma cap_range : forall G, 4 <= cap G <= 8.
Proof.
  intros G; unfold cap.
  destruct (existsb longchain_b G); [lia|].
  destruct (existsb is_3chain_b G); lia.
Qed.

Lemma stb_le_cap : forall G, stb G <= cap G.
Proof. intros G; unfold stb; apply Z.le_min_r. Qed.

Lemma stb_le_maxsh : forall G, stb G <= maxsh G.
Proof. intros G; unfold stb; apply Z.le_min_l. Qed.

(** * On wellformed positions this is Berlekamp's bonus *)

(** A wellformed chain has handout two, a wellformed loop handout four. *)
Lemma shand_wf_chain :
  forall n, (3 <= n)%nat -> (shand (Chain n) = 2)%nat.
Proof. intros n Hn; unfold shand, hand; cbn [csize]; lia. Qed.

Lemma shand_wf_loop :
  forall n, (4 <= n)%nat -> (shand (Loop n) = 4)%nat.
Proof. intros n Hn; unfold shand, hand; cbn [csize]; lia. Qed.

(** Every wellformed handout is at most four, so twice it is at most eight. *)
Lemma maxsh_le8 : forall G, wf G -> maxsh G <= 8.
Proof.
  induction G as [|C G IH]; intros Hw; [cbn; lia|].
  assert (HwC : wf_comp C) by (apply (wf_head C G); exact Hw).
  assert (HwG : wf G) by (apply (wf_tail C G); exact Hw).
  rewrite maxsh_cons; specialize (IH HwG).
  destruct C as [k | k].
  - rewrite (shand_wf_chain k HwC); lia.
  - destruct HwC as [H4 _]; rewrite (shand_wf_loop k H4); lia.
Qed.

(** With a loop present the largest handout is four, doubled to eight. *)
Lemma maxsh_of_loop :
  forall G, wf G -> existsb is_loop_b G = true -> maxsh G = 8.
Proof.
  induction G as [|C G IH]; intros Hw He; [discriminate|].
  assert (HwC : wf_comp C) by (apply (wf_head C G); exact Hw).
  assert (HwG : wf G) by (apply (wf_tail C G); exact Hw).
  rewrite maxsh_cons.
  simpl in He; apply orb_true_iff in He; destruct He as [HC | HG].
  - destruct C as [k | k]; [discriminate|].
    destruct HwC as [H4 _]; rewrite (shand_wf_loop k H4).
    pose proof (maxsh_le8 G HwG) as Hle; lia.
  - rewrite (IH HwG HG).
    destruct C as [k | k].
    + rewrite (shand_wf_chain k HwC); lia.
    + destruct HwC as [H4 _]; rewrite (shand_wf_loop k H4); lia.
Qed.

(** With no loop the largest handout is two, doubled to four. *)
Lemma maxsh_no_loop :
  forall G, wf G -> G <> [] -> existsb is_loop_b G = false -> maxsh G = 4.
Proof.
  induction G as [|C G IH]; intros Hw HNil He; [contradiction|].
  assert (HwC : wf_comp C) by (apply (wf_head C G); exact Hw).
  assert (HwG : wf G) by (apply (wf_tail C G); exact Hw).
  simpl in He; apply orb_false_iff in He; destruct He as [HC HG].
  destruct C as [k | k]; [|discriminate].
  rewrite maxsh_cons, (shand_wf_chain k HwC).
  destruct G as [|D G'].
  - rewrite maxsh_nil; lia.
  - rewrite (IH HwG ltac:(discriminate) HG); lia.
Qed.

(** * Chains that are not loops *)

Lemma longchain_not_loop : forall C, longchain_b C = true -> is_loop_b C = false.
Proof. intros [n | n] H; [reflexivity | discriminate]. Qed.

Lemma three_not_loop : forall C, is_3chain_b C = true -> is_loop_b C = false.
Proof. intros [n | n] H; [reflexivity | discriminate]. Qed.

(** A wellformed component that is not a loop is a three-chain or a long
    chain, since its length is at least three. *)
Lemma wf_nonloop_class :
  forall C, wf_comp C -> is_loop_b C = false ->
    is_3chain_b C = true \/ longchain_b C = true.
Proof.
  intros [n | n] Hw Hl; [|discriminate].
  cbn [wf_comp] in Hw.
  destruct n as [|[|[|[|m]]]]; try lia.
  - left; reflexivity.
  - right; unfold longchain_b; apply Nat.leb_le; lia.
Qed.

Lemma forallb_false_of_witness :
  forall (f g : comp -> bool) G,
    existsb g G = true -> (forall C, g C = true -> f C = false) ->
    forallb f G = false.
Proof.
  intros f g G He Himp.
  apply existsb_exists in He; destruct He as [D [HD Hg]].
  destruct (forallb f G) eqn:E; [|reflexivity].
  exfalso; rewrite forallb_forall in E; specialize (E D HD).
  rewrite (Himp D Hg) in E; discriminate.
Qed.

Lemma forallb_false_of_existsb_false :
  forall (f : comp -> bool) C G,
    existsb f (C :: G) = false -> forallb f (C :: G) = false.
Proof.
  intros f C G H; simpl in H |- *.
  apply orb_false_iff in H; destruct H as [HC _]; rewrite HC; reflexivity.
Qed.

(** With no long chain and no three-chain a wellformed position is all
    loops. *)
Lemma no_long_no_three_all_loops :
  forall G, wf G -> existsb longchain_b G = false ->
    existsb is_3chain_b G = false -> forallb is_loop_b G = true.
Proof.
  induction G as [|C G IH]; intros Hw Hl H3; [reflexivity|].
  simpl in Hl, H3 |- *.
  apply orb_false_iff in Hl; destruct Hl as [HlC HlG].
  apply orb_false_iff in H3; destruct H3 as [H3C H3G].
  assert (HwC : wf_comp C) by (apply (wf_head C G); exact Hw).
  destruct (is_loop_b C) eqn:EL.
  - simpl; apply IH; [apply (wf_tail C G); exact Hw | exact HlG | exact H3G].
  - exfalso; destruct (wf_nonloop_class C HwC EL) as [H | H]; congruence.
Qed.

(** And with no long chain every component is a loop or a three-chain, which
    is the condition Berlekamp's six-bonus tests. *)
Lemma no_long_all_loop_or_three :
  forall G, wf G -> existsb longchain_b G = false ->
    forallb (fun C => is_loop_b C || is_3chain_b C)%bool G = true.
Proof.
  induction G as [|C G IH]; intros Hw Hl; [reflexivity|].
  simpl in Hl |- *.
  apply orb_false_iff in Hl; destruct Hl as [HlC HlG].
  assert (HwC : wf_comp C) by (apply (wf_head C G); exact Hw).
  assert (HC : (is_loop_b C || is_3chain_b C)%bool = true).
  { destruct (is_loop_b C) eqn:EL; [reflexivity|].
    destruct (wf_nonloop_class C HwC EL) as [H | H];
      [rewrite H; apply orb_true_r | congruence]. }
  rewrite HC; simpl.
  apply IH; [apply (wf_tail C G); exact Hw | exact HlG].
Qed.

(** A long chain is neither, so it breaks that condition. *)
Lemma long_not_all_loop_or_three :
  forall G, existsb longchain_b G = true ->
    forallb (fun C => is_loop_b C || is_3chain_b C)%bool G = false.
Proof.
  intros G H.
  apply (forallb_false_of_witness _ longchain_b G H).
  intros [n | n] Hg; [|discriminate].
  unfold longchain_b in Hg; apply Nat.leb_le in Hg.
  cbn [is_loop_b is_3chain_b orb].
  destruct n as [|[|[|[|m]]]]; try lia; reflexivity.
Qed.

(** * The bonus restricts to Berlekamp's *)

(** On every wellformed position the two agree, so [stb] is not a new
    convention but the same one read through the handouts. *)
Theorem stb_eq_tb :
  forall G, wf G -> G <> [] -> stb G = tb G.
Proof.
  intros G Hw HNil.
  destruct G as [|C G']; [contradiction|].
  unfold stb, cap; rewrite tb_cons_form.
  destruct (existsb is_loop_b (C :: G')) eqn:EL.
  - rewrite (maxsh_of_loop (C :: G') Hw EL).
    destruct (existsb longchain_b (C :: G')) eqn:ELC.
    + rewrite (forallb_false_of_witness is_loop_b longchain_b _ ELC
                 longchain_not_loop).
      rewrite (long_not_all_loop_or_three _ ELC), andb_false_r; reflexivity.
    + destruct (existsb is_3chain_b (C :: G')) eqn:E3.
      * rewrite (forallb_false_of_witness is_loop_b is_3chain_b _ E3
                   three_not_loop).
        rewrite (no_long_all_loop_or_three _ Hw ELC); reflexivity.
      * rewrite (no_long_no_three_all_loops _ Hw ELC E3); reflexivity.
  - rewrite (maxsh_no_loop (C :: G') Hw ltac:(discriminate) EL).
    rewrite (forallb_false_of_existsb_false is_loop_b C G' EL), andb_false_l.
    destruct (existsb longchain_b (C :: G'));
      [reflexivity
       | destruct (existsb is_3chain_b (C :: G')); reflexivity].
Qed.

(** So the capped controlled value extends Berlekamp's on his own domain. *)
Corollary scval2_eq_cval :
  forall G, wf G -> G <> [] -> scval2 G = cval G.
Proof.
  intros G Hw HNil; unfold scval2, cval.
  rewrite (stb_eq_tb G Hw HNil).
  f_equal.
  clear HNil; induction G as [|C G IH]; [reflexivity|].
  assert (HwC : wf_comp C) by (apply (wf_head C G); exact Hw).
  cbn [scbase cbase]; rewrite (IH (wf_tail C G Hw)).
  unfold sweight, weight; f_equal.
  destruct C as [k | k].
  - rewrite (shand_wf_chain k HwC); reflexivity.
  - destruct HwC as [H4 _]; rewrite (shand_wf_loop k H4); reflexivity.
Qed.
