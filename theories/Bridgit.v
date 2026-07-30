(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Bridg-it: the first player wins by claiming one bridge, then Lehman. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.

Import ListNotations.
Require Import GameTrees.Helpers.

Require Import GameTrees.Determinacy.
Require Import GameTrees.Y.
Require Import GameTrees.Reach.
Require Import GameTrees.Shannon.

(** * Boolean certificate for the single shared edge *)

Definition share_onlyb (H1 H2 : list edge) (e0 : edge) : bool :=
  forallb (fun e => negb (ememb e H2) || edge_eqb e e0) H1.

Lemma share_onlyb_sound :
  forall H1 H2 e0, share_onlyb H1 H2 e0 = true ->
  forall e, In e H1 -> In e H2 -> e = e0.
Proof.
  intros H1 H2 e0 Hb e He1 He2.
  unfold share_onlyb in Hb; rewrite forallb_forall in Hb.
  specialize (Hb e He1).
  apply orb_true_iff in Hb.
  destruct Hb as [Hb | Hb].
  - rewrite negb_true_iff in Hb.
    rewrite (proj2 (ememb_true_iff e H2) He2) in Hb; discriminate.
  - apply edge_eqb_true_iff; auto.
Qed.

(** * Reachability from a parent map *)

Lemma cell_eqb_refl : forall p, cell_eqb p p = true.
Proof. intros p; apply cell_eqb_true_iff; reflexivity. Qed.


(** A ranking with adjacent lower-rank parents gives a spanning subgraph. *)
Lemma spans_of_parent :
  forall (W : list cell) (H : list edge) (root : cell) (rk : cell -> nat),
    In root W ->
    ends_in W H ->
    (forall v, In v W -> v <> root ->
       exists u, In u W /\ rk u < rk v /\ adjE H u v) ->
    spans W H.
Proof.
  intros W H root rk Hroot Hends Hpar.
  assert (Hto : forall N v, rk v <= N -> In v W ->
                chain (fun p => In p W) (adjE H) root v).
  { induction N as [|N IH]; intros v Hrk Hv.
    - destruct (cell_eq_dec v root) as [-> | Hne].
      + apply chain_refl; auto.
      + destruct (Hpar v Hv Hne) as [u (Hu & Hlt & Hadj)]; lia.
    - destruct (cell_eq_dec v root) as [-> | Hne].
      + apply chain_refl; auto.
      + destruct (Hpar v Hv Hne) as [u (Hu & Hlt & Hadj)].
        apply (chain_snoc _ _ root u v).
        * apply IH; [lia | exact Hu].
        * exact Hadj.
        * exact Hv. }
  split; [exact Hends|].
  intros u v Hu Hv.
  apply (chain_trans _ _ u root v).
  - apply chain_sym; [intros x y Hxy; apply adjE_sym; auto |].
    apply (Hto (rk u) u); auto.
  - apply (Hto (rk v) v); auto.
Qed.

(** * The Bridg-it board of side n *)

(** Short's graph: the left and right shores, and the interior posts. *)
Definition shoreL : cell := (0, 0).
Definition shoreR (n : nat) : cell := (0, n).

Definition posts (n : nat) : list cell :=
  flat_map (fun c => map (fun r => (r, c)) (seq 0 n)) (seq 1 (n - 1)).

Definition vB (n : nat) : list cell := shoreL :: shoreR n :: posts n.

(** The four kinds of bridge: to a shore, between columns, within a column. *)
Definition eL (n : nat) : list edge := map (fun r => (shoreL, (r, 1))) (seq 0 n).

Definition eR (n : nat) : list edge :=
  map (fun r => ((r, n - 1), shoreR n)) (seq 0 n).

Definition eH (n : nat) : list edge :=
  flat_map (fun c => map (fun r => ((r, c), (r, S c))) (seq 0 n)) (seq 1 (n - 2)).

Definition eV (n : nat) : list edge :=
  flat_map (fun c => map (fun r => ((r, c), (S r, c))) (seq 0 (n - 1)))
           (seq 1 (n - 1)).

Definition aB (n : nat) : list edge := eL n ++ eH n ++ eR n ++ eV n.

Lemma in_posts :
  forall n r c, In (r, c) (posts n) <-> r < n /\ 1 <= c <= n - 1.
Proof.
  intros n r c; unfold posts; rewrite in_flat_map; split.
  - intros [x [Hx Hin]].
    apply in_seq in Hx.
    apply in_map_iff in Hin; destruct Hin as [y [Hy Hys]].
    inversion Hy; subst.
    apply in_seq in Hys.
    repeat split; lia.
  - intros [Hr [Hc1 Hc2]].
    exists c; split; [apply in_seq; lia|].
    apply in_map_iff; exists r; split; [reflexivity | apply in_seq; lia].
Qed.

Lemma in_vB_shoreL : forall n, In shoreL (vB n).
Proof. intros n; left; reflexivity. Qed.

Lemma in_vB_shoreR : forall n, In (shoreR n) (vB n).
Proof. intros n; right; left; reflexivity. Qed.

Lemma in_vB_post :
  forall n r c, r < n -> 1 <= c -> c <= n - 1 -> In (r, c) (vB n).
Proof.
  intros n r c H1 H2 H3; right; right; apply in_posts; repeat split; auto.
Qed.

Lemma NoDup_posts : forall n, NoDup (posts n).
Proof.
  intros n; unfold posts.
  assert (Haux : forall m start,
            NoDup (flat_map (fun c => map (fun r => (r, c)) (seq 0 n))
                     (seq start m))).
  { induction m as [|m IH]; intros start; simpl; [constructor|].
    apply NoDup_app_disj.
    - apply NoDup_map_inj; [intros x y E; inversion E; auto | apply seq_NoDup].
    - apply IH.
    - intros [r c] Hin1 Hin2.
      apply in_map_iff in Hin1; destruct Hin1 as [x [Hx _]].
      inversion Hx; subst.
      apply in_flat_map in Hin2; destruct Hin2 as [y [Hy Hin]].
      apply in_seq in Hy.
      apply in_map_iff in Hin; destruct Hin as [z [Hz _]].
      inversion Hz; lia. }
  apply Haux.
Qed.

Lemma NoDup_vB : forall n, 2 <= n -> NoDup (vB n).
Proof.
  intros n Hn; unfold vB; constructor.
  - intros [Heq | Hin].
    + unfold shoreL, shoreR in Heq; inversion Heq; lia.
    + unfold shoreL in Hin; apply in_posts in Hin; lia.
  - constructor.
    + unfold shoreR; intros Hin; apply in_posts in Hin; lia.
    + apply NoDup_posts.
Qed.

(** * The two spanning subgraphs *)

(** The shared opening bridge. *)
Definition eop : edge := (shoreL, (1, 1)).

(** The first subgraph: the row-0 path, the verticals below it, a staircase. *)
Definition inT1 (n : nat) (e : edge) : bool :=
  if cell_eqb (fst e) shoreL then
    (Nat.eqb (fst (snd e)) 0 || Nat.eqb (fst (snd e)) 1)%bool
  else if cell_eqb (snd e) (shoreR n) then
    Nat.eqb (fst (fst e)) 0
  else if Nat.eqb (fst (fst e)) (fst (snd e)) then
    (Nat.eqb (fst (fst e)) 0 || Nat.eqb (fst (fst e)) (S (snd (fst e))))%bool
  else negb (Nat.eqb (fst (fst e)) 0).

Definition inT2 (n : nat) (e : edge) : bool :=
  (edge_eqb e eop || negb (inT1 n e))%bool.

Definition t1 (n : nat) : list edge := filter (inT1 n) (aB n).
Definition t2 (n : nat) : list edge := filter (inT2 n) (aB n).

Lemma t1_incl : forall n, incl (t1 n) (aB n).
Proof. intros n x Hx; unfold t1 in Hx; apply filter_In in Hx; tauto. Qed.

Lemma t2_incl : forall n, incl (t2 n) (aB n).
Proof. intros n x Hx; unfold t2 in Hx; apply filter_In in Hx; tauto. Qed.

(** The two subgraphs meet only in the opening bridge. *)
Lemma t1_t2_share :
  forall n e, In e (t1 n) -> In e (t2 n) -> e = eop.
Proof.
  intros n e H1 H2.
  unfold t1 in H1; unfold t2 in H2.
  apply filter_In in H1; apply filter_In in H2.
  destruct H1 as [_ Hb1]; destruct H2 as [_ Hb2].
  unfold inT2 in Hb2; apply orb_true_iff in Hb2.
  destruct Hb2 as [Hb2 | Hb2].
  - apply edge_eqb_true_iff; auto.
  - rewrite Hb1 in Hb2; discriminate.
Qed.

(** * Membership in the board *)

Lemma in_aB_L : forall n r, r < n -> In (shoreL, (r, 1)) (aB n).
Proof.
  intros n r Hr; unfold aB; apply in_or_app; left.
  unfold eL; apply in_map_iff; exists r; split; [reflexivity | apply in_seq; lia].
Qed.

Lemma in_aB_R : forall n r, r < n -> In ((r, n - 1), shoreR n) (aB n).
Proof.
  intros n r Hr; unfold aB.
  apply in_or_app; right; apply in_or_app; right; apply in_or_app; left.
  unfold eR; apply in_map_iff; exists r; split; [reflexivity | apply in_seq; lia].
Qed.

Lemma in_aB_H :
  forall n r c, r < n -> 1 <= c -> c <= n - 2 -> In ((r, c), (r, S c)) (aB n).
Proof.
  intros n r c Hr Hc1 Hc2; unfold aB.
  apply in_or_app; right; apply in_or_app; left.
  unfold eH; apply in_flat_map; exists c; split; [apply in_seq; lia|].
  apply in_map_iff; exists r; split; [reflexivity | apply in_seq; lia].
Qed.

Lemma in_aB_V :
  forall n r c,
    r < n - 1 -> 1 <= c -> c <= n - 1 -> In ((r, c), (S r, c)) (aB n).
Proof.
  intros n r c Hr Hc1 Hc2; unfold aB.
  apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
  unfold eV; apply in_flat_map; exists c; split; [apply in_seq; lia|].
  apply in_map_iff; exists r; split; [reflexivity | apply in_seq; lia].
Qed.

Lemma in_aB_eop : forall n, 2 <= n -> In eop (aB n).
Proof. intros n Hn; unfold eop; apply in_aB_L; lia. Qed.

Lemma ends_in_aB : forall n, 2 <= n -> ends_in (vB n) (aB n).
Proof.
  intros n Hn e He; unfold aB in He.
  apply in_app_or in He; destruct He as [He | He].
  - unfold eL in He; apply in_map_iff in He; destruct He as [r [<- Hr]].
    apply in_seq in Hr; simpl; split.
    + apply in_vB_shoreL.
    + apply in_vB_post; lia.
  - apply in_app_or in He; destruct He as [He | He].
    + unfold eH in He; apply in_flat_map in He; destruct He as [c [Hc He]].
      apply in_seq in Hc.
      apply in_map_iff in He; destruct He as [r [<- Hr]].
      apply in_seq in Hr; simpl; split; apply in_vB_post; lia.
    + apply in_app_or in He; destruct He as [He | He].
      * unfold eR in He; apply in_map_iff in He; destruct He as [r [<- Hr]].
        apply in_seq in Hr; simpl; split.
        -- apply in_vB_post; lia.
        -- apply in_vB_shoreR.
      * unfold eV in He; apply in_flat_map in He; destruct He as [c [Hc He]].
        apply in_seq in Hc.
        apply in_map_iff in He; destruct He as [r [<- Hr]].
        apply in_seq in Hr; simpl; split; apply in_vB_post; lia.
Qed.

Lemma ends_in_t1 : forall n, 2 <= n -> ends_in (vB n) (t1 n).
Proof.
  intros n Hn e He; apply ends_in_aB; auto; apply t1_incl; auto.
Qed.

Lemma ends_in_t2 : forall n, 2 <= n -> ends_in (vB n) (t2 n).
Proof.
  intros n Hn e He; apply ends_in_aB; auto; apply t2_incl; auto.
Qed.

(** Every vertex of the board is a shore or an interior post. *)
Lemma vB_cases :
  forall n v,
    In v (vB n) ->
    v = shoreL \/ v = shoreR n \/
    (fst v < n /\ 1 <= snd v /\ snd v <= n - 1).
Proof.
  intros n v [Heq | [Heq | Hin]]; [left | right; left | right; right]; auto.
  destruct v as [r c]; apply in_posts in Hin; simpl; tauto.
Qed.

(** * The first subgraph spans *)

Definition rk1 (n : nat) (v : cell) : nat :=
  if Nat.eqb (fst v) 0 then snd v
  else 2 * n * snd v + ((fst v - snd v) + (snd v - fst v)).

Lemma rk1_row0 : forall n c, rk1 n (0, c) = c.
Proof. intros n c; reflexivity. Qed.

Lemma rk1_post :
  forall n r c, 1 <= r -> rk1 n (r, c) = 2 * n * c + ((r - c) + (c - r)).
Proof.
  intros n r c Hr; unfold rk1; simpl.
  destruct r as [|r']; [lia | reflexivity].
Qed.

(** The membership tests for the two subgraphs, on each kind of bridge. *)
Lemma inT1_L :
  forall n r, inT1 n (shoreL, (r, 1)) = (Nat.eqb r 0 || Nat.eqb r 1)%bool.
Proof.
  intros n r; unfold inT1.
  change (fst (shoreL, (r, 1))) with shoreL.
  rewrite cell_eqb_refl; reflexivity.
Qed.

Lemma inT1_R :
  forall n r, 1 <= n - 1 -> inT1 n ((r, n - 1), shoreR n) = Nat.eqb r 0.
Proof.
  intros n r Hn; unfold inT1; simpl.
  destruct (cell_eqb (r, n - 1) shoreL) eqn:E.
  - apply cell_eqb_true_iff in E; unfold shoreL in E; inversion E; lia.
  - rewrite cell_eqb_refl; reflexivity.
Qed.

Lemma inT1_H :
  forall n r c, 1 <= c -> S c < n ->
    inT1 n ((r, c), (r, S c)) = (Nat.eqb r 0 || Nat.eqb r (S c))%bool.
Proof.
  intros n r c Hc1 Hc2; unfold inT1; simpl.
  destruct (cell_eqb (r, c) shoreL) eqn:E1.
  - apply cell_eqb_true_iff in E1; unfold shoreL in E1; inversion E1; lia.
  - destruct (cell_eqb (r, S c) (shoreR n)) eqn:E2.
    + apply cell_eqb_true_iff in E2; unfold shoreR in E2; inversion E2; lia.
    + rewrite Nat.eqb_refl; reflexivity.
Qed.

Lemma inT1_V :
  forall n r c, 1 <= c -> inT1 n ((r, c), (S r, c)) = negb (Nat.eqb r 0).
Proof.
  intros n r c Hc; unfold inT1; simpl.
  destruct (cell_eqb (r, c) shoreL) eqn:E1.
  - apply cell_eqb_true_iff in E1; unfold shoreL in E1; inversion E1; lia.
  - destruct (cell_eqb (S r, c) (shoreR n)) eqn:E2.
    + apply cell_eqb_true_iff in E2; unfold shoreR in E2; inversion E2.
    + destruct (Nat.eqb r (S r)) eqn:E3.
      * apply Nat.eqb_eq in E3; lia.
      * reflexivity.
Qed.

Lemma in_t1 :
  forall n e, In e (aB n) -> inT1 n e = true -> In e (t1 n).
Proof. intros n e H1 H2; unfold t1; apply filter_In; auto. Qed.

Lemma in_t2 :
  forall n e, In e (aB n) -> inT1 n e = false -> In e (t2 n).
Proof.
  intros n e H1 H2; unfold t2; apply filter_In; split; auto.
  unfold inT2; rewrite H2; apply orb_true_r.
Qed.

Lemma in_t2_eop : forall n, 2 <= n -> In eop (t2 n).
Proof.
  intros n Hn; unfold t2; apply filter_In; split.
  - apply in_aB_eop; auto.
  - unfold inT2; rewrite (proj2 (edge_eqb_true_iff eop eop) eq_refl); reflexivity.
Qed.

Theorem spans_t1 : forall n, 2 <= n -> spans (vB n) (t1 n).
Proof.
  intros n Hn.
  apply (spans_of_parent (vB n) (t1 n) shoreL (rk1 n)).
  - apply in_vB_shoreL.
  - apply ends_in_t1; auto.
  - intros v Hv Hne.
    destruct (vB_cases n v Hv) as [-> | [-> | (Hr & Hc1 & Hc2)]]; [contradiction| |].
    + exists (0, n - 1); repeat split.
      * apply in_vB_post; lia.
      * unfold shoreR; rewrite !rk1_row0; lia.
      * left; apply in_t1; [apply in_aB_R; lia|].
        rewrite inT1_R by lia; reflexivity.
    + destruct v as [r c]; simpl in Hr, Hc1, Hc2.
      destruct c as [|c']; [lia|].
      destruct r as [|r'].
      * (* a post in row 0, reached along the row-0 path *)
        destruct c' as [|c''].
        -- exists shoreL; repeat split.
           ++ apply in_vB_shoreL.
           ++ unfold shoreL; rewrite !rk1_row0; lia.
           ++ left; apply in_t1; [apply in_aB_L; lia|].
              rewrite inT1_L; reflexivity.
        -- exists (0, S c''); repeat split.
           ++ apply in_vB_post; simpl; lia.
           ++ rewrite !rk1_row0; lia.
           ++ left; apply in_t1; [apply in_aB_H; lia|].
              rewrite inT1_H by lia; reflexivity.
      * (* a post below row 0 *)
        destruct c' as [|c''].
        -- (* the first column, reached from the shore then downwards *)
           destruct r' as [|r''].
           ++ exists shoreL; repeat split.
              ** apply in_vB_shoreL.
              ** unfold shoreL; rewrite rk1_row0, rk1_post by lia; lia.
              ** left; apply in_t1; [apply in_aB_L; lia|].
                 rewrite inT1_L; reflexivity.
           ++ exists (S r'', 1); repeat split.
              ** apply in_vB_post; simpl; lia.
              ** rewrite !rk1_post by lia; lia.
              ** left; apply in_t1; [apply in_aB_V; simpl; lia|].
                 rewrite inT1_V by lia; reflexivity.
        -- (* a later column: towards the diagonal, then the staircase *)
           destruct (Nat.lt_total r' (S c'')) as [Hlt | [Heq | Hgt]].
           ++ exists (S (S r'), S (S c'')); repeat split.
              ** apply in_vB_post; simpl; lia.
              ** rewrite !rk1_post by lia; lia.
              ** right; apply in_t1; [apply in_aB_V; simpl; lia|].
                 rewrite inT1_V by lia; reflexivity.
           ++ exists (S r', S c''); repeat split.
              ** apply in_vB_post; simpl; lia.
              ** rewrite !rk1_post by lia; lia.
              ** left; apply in_t1; [apply in_aB_H; lia|].
                 rewrite inT1_H by lia.
                 apply orb_true_iff; right; apply Nat.eqb_eq; lia.
           ++ exists (r', S (S c'')); repeat split.
              ** apply in_vB_post; simpl; lia.
              ** rewrite !rk1_post by lia; lia.
              ** left; apply in_t1; [apply in_aB_V; simpl; lia|].
                 rewrite inT1_V by lia.
                 apply negb_true_iff, Nat.eqb_neq; lia.
Qed.

(** * The second subgraph spans *)

(** Rank: left arcs descend to the near shore, right arcs to the far one. *)
Definition rk2 (n : nat) (v : cell) : nat :=
  if Nat.eqb (snd v) 0 then 0
  else if Nat.eqb (snd v) n then n + 1
  else if Nat.eqb (fst v) 0 then n + 2 + snd v
  else if Nat.ltb (snd v) (fst v) then snd v
  else if Nat.eqb (fst v) 1 then snd v
  else n + 2 + (n - snd v).

Lemma rk2_shoreL : forall n, rk2 n shoreL = 0.
Proof. intros n; reflexivity. Qed.

Lemma rk2_shoreR : forall n, 2 <= n -> rk2 n (shoreR n) = n + 1.
Proof.
  intros n Hn; unfold rk2, shoreR; simpl.
  replace (Nat.eqb n 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  rewrite Nat.eqb_refl; reflexivity.
Qed.

Lemma rk2_row0 :
  forall n c, 1 <= c -> c <= n - 1 -> rk2 n (0, c) = n + 2 + c.
Proof.
  intros n c H1 H2; unfold rk2; simpl.
  replace (Nat.eqb c 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb c n) with false by (symmetry; apply Nat.eqb_neq; lia).
  reflexivity.
Qed.

Lemma rk2_row1 :
  forall n c, 1 <= c -> c <= n - 1 -> rk2 n (1, c) = c.
Proof.
  intros n c H1 H2; unfold rk2; simpl.
  replace (Nat.eqb c 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb c n) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.ltb c 1) with false by (symmetry; apply Nat.ltb_ge; lia).
  reflexivity.
Qed.

Lemma rk2_left :
  forall n r c, 2 <= r -> 1 <= c -> c < r -> c <= n - 1 -> rk2 n (r, c) = c.
Proof.
  intros n r c H1 H2 H3 H4; unfold rk2; simpl.
  replace (Nat.eqb c 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb c n) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb r 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.ltb c r) with true by (symmetry; apply Nat.ltb_lt; lia).
  reflexivity.
Qed.

Lemma rk2_right :
  forall n r c, 2 <= r -> r <= c -> c <= n - 1 -> rk2 n (r, c) = n + 2 + (n - c).
Proof.
  intros n r c H1 H2 H3; unfold rk2; simpl.
  replace (Nat.eqb c 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb c n) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.eqb r 0) with false by (symmetry; apply Nat.eqb_neq; lia).
  replace (Nat.ltb c r) with false by (symmetry; apply Nat.ltb_ge; lia).
  replace (Nat.eqb r 1) with false by (symmetry; apply Nat.eqb_neq; lia).
  reflexivity.
Qed.

Theorem spans_t2 : forall n, 2 <= n -> spans (vB n) (t2 n).
Proof.
  intros n Hn.
  apply (spans_of_parent (vB n) (t2 n) shoreL (rk2 n)).
  - apply in_vB_shoreL.
  - apply ends_in_t2; auto.
  - intros v Hv Hne.
    destruct (vB_cases n v Hv) as [-> | [-> | (Hr & Hc1 & Hc2)]]; [contradiction| |].
    + (* the right shore, reached from row 1 *)
      exists (1, n - 1); repeat split.
      * apply in_vB_post; lia.
      * rewrite rk2_shoreR, rk2_row1 by lia; lia.
      * left; apply in_t2; [apply in_aB_R; lia|].
        rewrite inT1_R by lia.
        apply Nat.eqb_neq; lia.
    + destruct v as [r c]; simpl in Hr, Hc1, Hc2.
      destruct r as [|r'].
      * (* row 0, reached from row 1 by a vertical *)
        exists (1, c); repeat split.
        -- apply in_vB_post; lia.
        -- rewrite rk2_row0, rk2_row1 by lia; lia.
        -- right; apply in_t2; [apply in_aB_V; lia|].
           rewrite inT1_V by lia; reflexivity.
      * destruct r' as [|r''].
        -- (* row 1, the arc from the opening bridge to the far shore *)
           destruct c as [|c']; [lia|].
           destruct c' as [|c''].
           ++ exists shoreL; repeat split.
              ** apply in_vB_shoreL.
              ** rewrite rk2_shoreL, rk2_row1 by lia; lia.
              ** left; change (shoreL, (1, 1)) with eop.
                 apply in_t2_eop; auto.
           ++ exists (1, S c''); repeat split.
              ** apply in_vB_post; simpl; lia.
              ** rewrite !rk2_row1 by (simpl; lia); lia.
              ** left; apply in_t2; [apply in_aB_H; lia|].
                 rewrite inT1_H by lia; reflexivity.
        -- (* row two or below: the left arc, the far shore, the right arc *)
           destruct (Nat.lt_total c (S (S r''))) as [Hlt | [Heq | Hgt]].
           ++ destruct c as [|c']; [lia|].
              destruct c' as [|c''].
              ** exists shoreL; repeat split.
                 --- apply in_vB_shoreL.
                 --- rewrite rk2_shoreL, rk2_left by lia; lia.
                 --- left; apply in_t2; [apply in_aB_L; lia|].
                     rewrite inT1_L.
                     apply orb_false_iff; split; apply Nat.eqb_neq; lia.
              ** exists (S (S r''), S c''); repeat split.
                 --- apply in_vB_post; simpl; lia.
                 --- rewrite !rk2_left by (simpl; lia); lia.
                 --- left; apply in_t2; [apply in_aB_H; lia|].
                     rewrite inT1_H by lia.
                     apply orb_false_iff; split; apply Nat.eqb_neq; lia.
           ++ (* the gap in this row: reach it from the far shore or the right *)
              destruct (Nat.eq_dec c (n - 1)) as [-> | Hcn].
              ** exists (shoreR n); repeat split.
                 --- apply in_vB_shoreR.
                 --- rewrite rk2_shoreR, rk2_right by lia; lia.
                 --- right; apply in_t2; [apply in_aB_R; lia|].
                     rewrite inT1_R by lia.
                     apply Nat.eqb_neq; lia.
              ** exists (S (S r''), S c); repeat split.
                 --- apply in_vB_post; simpl; lia.
                 --- rewrite !rk2_right by (simpl; lia); lia.
                 --- right; apply in_t2; [apply in_aB_H; lia|].
                     rewrite inT1_H by lia.
                     apply orb_false_iff; split; apply Nat.eqb_neq; lia.
           ++ destruct (Nat.eq_dec c (n - 1)) as [-> | Hcn].
              ** exists (shoreR n); repeat split.
                 --- apply in_vB_shoreR.
                 --- rewrite rk2_shoreR, rk2_right by lia; lia.
                 --- right; apply in_t2; [apply in_aB_R; lia|].
                     rewrite inT1_R by lia.
                     apply Nat.eqb_neq; lia.
              ** exists (S (S r''), S c); repeat split.
                 --- apply in_vB_post; simpl; lia.
                 --- rewrite !rk2_right by (simpl; lia); lia.
                 --- right; apply in_t2; [apply in_aB_H; lia|].
                     rewrite inT1_H by lia.
                     apply orb_false_iff; split; apply Nat.eqb_neq; lia.
Qed.

(** * Bridg-it on every board *)

(** The first player wins Bridg-it on the board of every side. *)
Theorem bridgit_first_player_wins :
  forall n, 2 <= n ->
    forces sg_moves sg_play sg_amove (sg_outc (vB n) shoreL (shoreR n)) false
      (S (2 * length (remove_edge eop (aB n)))) (MkSG (aB n) [] false).
Proof.
  intros n Hn.
  apply (lehman_short_first (vB n) (NoDup_vB n Hn) shoreL (shoreR n)
           (in_vB_shoreL n) (aB n) eop (vB n) (t1 n) (t2 n)).
  - apply in_aB_eop; auto.
  - apply NoDup_vB; auto.
  - apply incl_refl.
  - apply in_vB_shoreL.
  - apply in_vB_shoreR.
  - apply t1_incl.
  - apply t2_incl.
  - apply t1_t2_share.
  - apply spans_t1; auto.
  - apply spans_t2; auto.
Qed.

(** * A checked instance *)

(** The generic certificate, confirmed by computation on small boards. *)
Example bridgit3_certificate :
  (spansb (vB 3) (t1 3) && spansb (vB 3) (t2 3)
   && share_onlyb (t1 3) (t2 3) eop)%bool = true.
Proof. vm_compute; reflexivity. Qed.

Example bridgit4_certificate :
  (spansb (vB 4) (t1 4) && spansb (vB 4) (t2 4)
   && share_onlyb (t1 4) (t2 4) eop)%bool = true.
Proof. vm_compute; reflexivity. Qed.
