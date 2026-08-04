(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Sprague-Grundy theory of finite impartial games over rose trees. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.Trees.

(** * The minimum excludant *)

Fixpoint mex_aux (fuel k : nat) (l : list nat) : nat :=
  match fuel with
  | 0 => k
  | S f => if existsb (Nat.eqb k) l then mex_aux f (S k) l else k
  end.

(** The least natural number not in [l]. *)
Definition mex (l : list nat) : nat := mex_aux (S (length l)) 0 l.

Lemma existsb_eqb_in :
  forall k l, existsb (Nat.eqb k) l = true <-> In k l.
Proof.
  intros k l; rewrite existsb_exists; split.
  - intros [x [Hx He]].
    apply Nat.eqb_eq in He; subst; auto.
  - intros Hin; exists k; split; auto.
    apply Nat.eqb_eq; auto.
Qed.

Lemma mex_aux_spec :
  forall fuel k l,
    (forall x, x < k -> In x l) ->
    length l < fuel + k ->
    ~ In (mex_aux fuel k l) l /\
    (forall x, x < mex_aux fuel k l -> In x l).
Proof.
  induction fuel as [|f IH]; intros k l Hbelow Hfuel.
  - exfalso.
    assert (Hincl : incl (seq 0 k) l).
    { intros x Hx; apply in_seq in Hx; apply Hbelow; lia. }
    pose proof (NoDup_incl_length (seq_NoDup k 0) Hincl) as Hlen.
    rewrite length_seq in Hlen; lia.
  - simpl.
    destruct (existsb (Nat.eqb k) l) eqn:E.
    + apply IH; [| lia].
      intros x Hx.
      destruct (Nat.eq_dec x k) as [-> | Hne].
      * apply (proj1 (existsb_eqb_in k l)); auto.
      * apply Hbelow; lia.
    + split.
      * intros Hin.
        rewrite (proj2 (existsb_eqb_in k l) Hin) in E; discriminate.
      * auto.
Qed.

Lemma mex_spec :
  forall l, ~ In (mex l) l /\ (forall x, x < mex l -> In x l).
Proof.
  intros l; unfold mex.
  apply mex_aux_spec; [intros x Hx; lia | lia].
Qed.

Lemma mex_not_in : forall l, ~ In (mex l) l.
Proof. intros l; apply (proj1 (mex_spec l)). Qed.

Lemma mex_lt_in : forall l x, x < mex l -> In x l.
Proof. intros l; apply (proj2 (mex_spec l)). Qed.

Lemma mex_unique :
  forall l g, ~ In g l -> (forall x, x < g -> In x l) -> mex l = g.
Proof.
  intros l g Hg Hlt.
  destruct (Nat.lt_trichotomy (mex l) g) as [H | [H | H]]; auto.
  - exfalso; apply (mex_not_in l); apply Hlt; auto.
  - exfalso; apply Hg; apply mex_lt_in; auto.
Qed.

(** * Impartial games *)

(** A game is a rose tree whose subtrees are the options. *)
Definition game : Type := tree unit.

(** The Grundy value: the minimum excludant of the options' values. *)
Definition grundy : game -> nat := fold_tree (fun _ gs => mex gs).

(** The player to move wins exactly when some option loses. *)
Definition winb : game -> bool := fold_tree (fun _ bs => existsb negb bs).

Lemma grundy_eq :
  forall (a : unit) (ts : forest unit),
    grundy (node a ts) = mex (map grundy ts).
Proof. reflexivity. Qed.

Lemma winb_eq :
  forall (a : unit) (ts : forest unit),
    winb (node a ts) = existsb negb (map winb ts).
Proof. reflexivity. Qed.

(** The player to move wins exactly when the Grundy value is nonzero. *)
Theorem winb_grundy :
  forall t : game, winb t = true <-> grundy t <> 0.
Proof.
  apply (tree_forall_ind unit (fun t => winb t = true <-> grundy t <> 0)).
  intros a f IH.
  rewrite winb_eq, grundy_eq.
  split.
  - intros Hw.
    apply existsb_exists in Hw.
    destruct Hw as [b [Hb Hneg]].
    destruct b; [discriminate|].
    apply in_map_iff in Hb.
    destruct Hb as [c [Hc Hcf]].
    assert (Hg0 : grundy c = 0).
    { pose proof (proj1 (Forall_forall _ f) IH c Hcf) as Hiff.
      cbv beta in Hiff.
      destruct (grundy c) as [|n]; auto.
      exfalso.
      assert (Hne : S n <> 0) by lia.
      pose proof (proj2 Hiff Hne) as Hw'.
      congruence. }
    intros Hm.
    apply (mex_not_in (map grundy f)).
    rewrite Hm.
    apply in_map_iff; exists c; auto.
  - intros Hne.
    destruct (in_dec Nat.eq_dec 0 (map grundy f)) as [Hin | Hnin].
    + apply in_map_iff in Hin.
      destruct Hin as [c [Hc Hcf]].
      assert (Hwc : winb c = false).
      { pose proof (proj1 (Forall_forall _ f) IH c Hcf) as Hiff.
        destruct (winb c) eqn:Ew; auto.
        exfalso.
        apply (proj1 Hiff); auto. }
      apply existsb_exists.
      exists false; split; auto.
      rewrite <- Hwc.
      apply in_map; auto.
    + exfalso; apply Hne.
      apply mex_unique; auto.
      intros x Hx; lia.
Qed.

(** * The XOR order argument *)

Lemma bit_high : forall x k, x < 2 ^ k -> Nat.testbit x k = false.
Proof.
  intros x k Hx.
  destruct x as [|x'].
  - apply Nat.bits_0.
  - apply Nat.bits_above_log2.
    apply (proj1 (Nat.log2_lt_pow2 (S x') k ltac:(lia))); auto.
Qed.

Lemma bit_le : forall x k, Nat.testbit x k = true -> 2 ^ k <= x.
Proof.
  intros x k Hb.
  destruct (Nat.lt_ge_cases x (2 ^ k)) as [H | H]; auto.
  rewrite bit_high in Hb; [discriminate | auto].
Qed.

Lemma bit_lt_pow2 :
  forall x k, x < 2 ^ S k -> Nat.testbit x k = false -> x < 2 ^ k.
Proof.
  intros x k Hx Hb.
  destruct (Nat.lt_ge_cases x (2 ^ k)) as [H | H]; auto.
  exfalso.
  assert (Hx0 : x <> 0).
  { pose proof (Nat.pow_nonzero 2 k); lia. }
  assert (Hlog : Nat.log2 x = k).
  { assert (Hle : k <= Nat.log2 x).
    { apply (proj1 (Nat.log2_le_pow2 x k ltac:(lia))); auto. }
    assert (Hlt : Nat.log2 x < S k).
    { apply (proj1 (Nat.log2_lt_pow2 x (S k) ltac:(lia))); auto. }
    lia. }
  pose proof (Nat.bit_log2 x Hx0) as Hb'.
  rewrite Hlog in Hb'; congruence.
Qed.

Lemma high_bits_div :
  forall a b k,
    (forall j, k < j -> Nat.testbit a j = Nat.testbit b j) ->
    a / 2 ^ S k = b / 2 ^ S k.
Proof.
  intros a b k H.
  apply Nat.bits_inj; intros n.
  rewrite !Nat.div_pow2_bits.
  apply H; lia.
Qed.

(** If [a] and [b] agree above bit [k] and [b] has it set, then [a < b]. *)
Lemma testbit_order :
  forall a b k,
    Nat.testbit a k = false -> Nat.testbit b k = true ->
    (forall j, k < j -> Nat.testbit a j = Nat.testbit b j) ->
    a < b.
Proof.
  intros a b k Ha Hb Hhigh.
  assert (Hq : 2 ^ S k <> 0) by (apply Nat.pow_nonzero; lia).
  pose proof (Nat.Div0.div_mod a (2 ^ S k)) as Ea.
  pose proof (Nat.Div0.div_mod b (2 ^ S k)) as Eb.
  rewrite (high_bits_div a b k Hhigh) in Ea.
  assert (Hma : a mod 2 ^ S k < 2 ^ k).
  { apply bit_lt_pow2.
    - apply Nat.mod_upper_bound; auto.
    - rewrite Nat.mod_pow2_bits_low by lia; auto. }
  assert (Hmb : 2 ^ k <= b mod 2 ^ S k).
  { apply bit_le.
    rewrite Nat.mod_pow2_bits_low by lia; auto. }
  lia.
Qed.

Lemma lxor_eq_0 : forall a b, Nat.lxor a b = 0 <-> a = b.
Proof.
  intros a b; split.
  - intros H.
    apply Nat.bits_inj; intros n.
    pose proof (Nat.lxor_spec a b n) as Hs.
    rewrite H, Nat.bits_0 in Hs.
    destruct (Nat.testbit a n); destruct (Nat.testbit b n);
      simpl in Hs; congruence.
  - intros ->; apply Nat.lxor_nilpotent.
Qed.

Lemma lxor_cancel_left : forall a b, Nat.lxor a (Nat.lxor a b) = b.
Proof.
  intros a b.
  rewrite <- Nat.lxor_assoc, Nat.lxor_nilpotent, Nat.lxor_0_l; auto.
Qed.

Lemma lxor_cancel_l :
  forall c a b, Nat.lxor c a = Nat.lxor c b -> a = b.
Proof.
  intros c a b H.
  pose proof (f_equal (Nat.lxor c) H) as H2.
  rewrite !lxor_cancel_left in H2; auto.
Qed.

Lemma lxor_cancel_r :
  forall c a b, Nat.lxor a c = Nat.lxor b c -> a = b.
Proof.
  intros c a b H.
  apply (lxor_cancel_l c).
  rewrite Nat.lxor_comm, H, Nat.lxor_comm; auto.
Qed.

(** Any value below an XOR is reached by lowering one operand. *)
Lemma lxor_lt_witness :
  forall x y v, v < Nat.lxor x y ->
  Nat.lxor y v < x \/ Nat.lxor x v < y.
Proof.
  intros x y v Hv.
  set (g := Nat.lxor x y) in *.
  set (d := Nat.lxor v g).
  assert (Hd : d <> 0).
  { unfold d; intros H0.
    apply (proj1 (lxor_eq_0 v g)) in H0.
    rewrite H0 in Hv.
    exact (Nat.lt_irrefl g Hv). }
  set (k := Nat.log2 d).
  assert (Hhigh : forall j, k < j -> Nat.testbit v j = Nat.testbit g j).
  { intros j Hj.
    pose proof (Nat.bits_above_log2 d j Hj) as Hz.
    unfold d in Hz; rewrite Nat.lxor_spec in Hz.
    destruct (Nat.testbit v j); destruct (Nat.testbit g j);
      simpl in Hz; congruence. }
  assert (Hk : Nat.testbit v k = false /\ Nat.testbit g k = true).
  { pose proof (Nat.bit_log2 d Hd) as Hbk.
    fold k in Hbk.
    unfold d in Hbk; rewrite Nat.lxor_spec in Hbk.
    destruct (Nat.testbit v k) eqn:Ev; destruct (Nat.testbit g k) eqn:Eg;
      simpl in Hbk; try congruence.
    - exfalso.
      assert (Hlt : g < v).
      { apply (testbit_order g v k).
        - exact Eg.
        - exact Ev.
        - intros j Hj; symmetry; apply Hhigh; auto. }
      lia.
    - split; auto. }
  destruct Hk as [Hvk Hgk].
  assert (Hgs : Nat.testbit g k
                = xorb (Nat.testbit x k) (Nat.testbit y k))
    by (unfold g; apply Nat.lxor_spec).
  rewrite Hgk in Hgs.
  destruct (Nat.testbit x k) eqn:Ex.
  - left.
    apply (testbit_order (Nat.lxor y v) x k).
    + rewrite Nat.lxor_spec, Hvk.
      destruct (Nat.testbit y k); simpl in Hgs; simpl; congruence.
    + exact Ex.
    + intros j Hj.
      rewrite Nat.lxor_spec.
      rewrite (Hhigh j Hj).
      unfold g; rewrite Nat.lxor_spec.
      destruct (Nat.testbit y j); destruct (Nat.testbit x j); auto.
  - right.
    apply (testbit_order (Nat.lxor x v) y k).
    + rewrite Nat.lxor_spec, Hvk, Ex; auto.
    + destruct (Nat.testbit y k); simpl in Hgs; congruence.
    + intros j Hj.
      rewrite Nat.lxor_spec.
      rewrite (Hhigh j Hj).
      unfold g; rewrite Nat.lxor_spec.
      destruct (Nat.testbit x j); destruct (Nat.testbit y j); auto.
Qed.

(** * The disjunctive sum *)

(** The disjunctive sum: a move is a move in exactly one summand. *)
Fixpoint tsum (s : game) : game -> game :=
  match s with
  | node _ ss =>
    fix tsum_r (t : game) : game :=
      match t with
      | node b ts =>
        node tt (map (fun s' => tsum s' (node b ts)) ss
                 ++ map tsum_r ts)
      end
  end.

Lemma tsum_eq :
  forall (a : unit) ss (b : unit) ts,
    tsum (node a ss) (node b ts) =
    node tt (map (fun s' => tsum s' (node b ts)) ss
             ++ map (tsum (node a ss)) ts).
Proof. reflexivity. Qed.

(** The Sprague-Grundy theorem: a sum's value is the XOR of the values. *)
Theorem grundy_tsum :
  forall s t : game,
    grundy (tsum s t) = Nat.lxor (grundy s) (grundy t).
Proof.
  apply (tree_forall_ind unit
    (fun s => forall t : game,
       grundy (tsum s t) = Nat.lxor (grundy s) (grundy t))).
  intros a ss IHs.
  apply (tree_forall_ind unit
    (fun t => grundy (tsum (node a ss) t) =
              Nat.lxor (grundy (node a ss)) (grundy t))).
  intros b ts IHt.
  rewrite tsum_eq, grundy_eq.
  rewrite map_app, !map_map.
  assert (EL : map (fun s' => grundy (tsum s' (node b ts))) ss
             = map (fun s' => Nat.lxor (grundy s') (grundy (node b ts))) ss).
  { apply map_ext_in; intros s' Hin.
    apply (proj1 (Forall_forall _ ss) IHs s' Hin). }
  assert (ER : map (fun t' => grundy (tsum (node a ss) t')) ts
             = map (fun t' => Nat.lxor (grundy (node a ss)) (grundy t')) ts).
  { apply map_ext_in; intros t' Hin.
    apply (proj1 (Forall_forall _ ts) IHt t' Hin). }
  rewrite EL, ER.
  apply mex_unique.
  - intros Hin.
    apply in_app_or in Hin.
    destruct Hin as [Hin | Hin].
    + apply in_map_iff in Hin.
      destruct Hin as [s' [Heq Hs']].
      apply lxor_cancel_r in Heq.
      rewrite (grundy_eq a ss) in Heq.
      apply (mex_not_in (map grundy ss)).
      rewrite <- Heq.
      apply in_map; auto.
    + apply in_map_iff in Hin.
      destruct Hin as [t' [Heq Ht']].
      apply lxor_cancel_l in Heq.
      rewrite (grundy_eq b ts) in Heq.
      apply (mex_not_in (map grundy ts)).
      rewrite <- Heq.
      apply in_map; auto.
  - intros v Hv.
    destruct (lxor_lt_witness (grundy (node a ss)) (grundy (node b ts)) v Hv)
      as [Hw | Hw].
    + apply in_or_app; left.
      rewrite (grundy_eq a ss) in Hw.
      pose proof (mex_lt_in (map grundy ss) _ Hw) as Hin.
      apply in_map_iff in Hin.
      destruct Hin as [s' [Heq Hs']].
      apply in_map_iff.
      exists s'; split; auto.
      rewrite Heq.
      rewrite Nat.lxor_comm.
      apply lxor_cancel_left.
    + apply in_or_app; right.
      rewrite (grundy_eq b ts) in Hw.
      pose proof (mex_lt_in (map grundy ts) _ Hw) as Hin.
      apply in_map_iff in Hin.
      destruct Hin as [t' [Heq Ht']].
      apply in_map_iff.
      exists t'; split; auto.
      rewrite Heq.
      apply lxor_cancel_left.
Qed.

(** The mover wins a sum of two games exactly when their values differ. *)
Corollary winb_tsum :
  forall s t : game,
    winb (tsum s t) = true <-> grundy s <> grundy t.
Proof.
  intros s t; split.
  - intros Hw He.
    pose proof (proj1 (winb_grundy (tsum s t)) Hw) as Hg.
    apply Hg.
    rewrite grundy_tsum, He.
    apply Nat.lxor_nilpotent.
  - intros Hne.
    apply (proj2 (winb_grundy (tsum s t))).
    rewrite grundy_tsum.
    intros H0.
    apply Hne.
    apply lxor_eq_0; auto.
Qed.

(** * Nim *)

Fixpoint nim_list (n : nat) : list game :=
  match n with
  | 0 => []
  | S k => nim_list k ++ [node tt (nim_list k)]
  end.

(** The Nim pile of [n] stones, with every smaller pile as an option. *)
Definition nim (n : nat) : game := node tt (nim_list n).

Lemma mex_seq : forall n, mex (seq 0 n) = n.
Proof.
  intros n; apply mex_unique.
  - intros Hin; apply in_seq in Hin; lia.
  - intros x Hx; apply in_seq; lia.
Qed.

Lemma nim_grundy_aux :
  forall n, map grundy (nim_list n) = seq 0 n /\ grundy (nim n) = n.
Proof.
  induction n as [|k [IH1 IH2]].
  - split; reflexivity.
  - assert (E : map grundy (nim_list (S k)) = seq 0 (S k)).
    { simpl nim_list.
      rewrite map_app, IH1.
      simpl map.
      unfold nim in IH2.
      rewrite IH2.
      rewrite seq_S.
      auto. }
    split; auto.
    unfold nim.
    rewrite grundy_eq, E, mex_seq; auto.
Qed.

Lemma grundy_nim : forall n, grundy (nim n) = n.
Proof. intros n; apply (proj2 (nim_grundy_aux n)). Qed.

Definition nim_sum (piles : list nat) : game :=
  fold_right (fun p acc => tsum (nim p) acc) (nim 0) piles.

Lemma grundy_nim_sum :
  forall piles, grundy (nim_sum piles) = fold_right Nat.lxor 0 piles.
Proof.
  induction piles as [|p piles IH].
  - exact (grundy_nim 0).
  - change (grundy (tsum (nim p) (nim_sum piles))
            = Nat.lxor p (fold_right Nat.lxor 0 piles)).
    rewrite grundy_tsum, grundy_nim, IH; auto.
Qed.

(** Bouton's theorem. *)
Theorem bouton :
  forall piles,
    winb (nim_sum piles) = true <-> fold_right Nat.lxor 0 piles <> 0.
Proof.
  intros piles; split.
  - intros Hw.
    rewrite <- grundy_nim_sum.
    apply (proj1 (winb_grundy (nim_sum piles))); auto.
  - intros Hne.
    apply (proj2 (winb_grundy (nim_sum piles))).
    rewrite grundy_nim_sum; auto.
Qed.

(** The options of a Nim pile are the smaller piles. *)
Lemma nim_list_shape : forall n, nim_list n = map nim (seq 0 n).
Proof.
  induction n as [|k IH]; auto.
  change (nim_list (S k)) with (nim_list k ++ [node tt (nim_list k)]).
  rewrite seq_S, map_app.
  replace (0 + k) with k by lia.
  change (map nim [k]) with [nim k].
  change (nim k) with (node tt (nim_list k)).
  rewrite IH; reflexivity.
Qed.

(** * Misere play *)

(** Under misere play the player left without a move wins. *)
Fixpoint mwinb (t : game) : bool :=
  match t with
  | node _ f =>
    match f with
    | [] => true
    | _ => existsb (fun s => negb (mwinb s)) f
    end
  end.

Lemma mwinb_nil : forall a, mwinb (node a []) = true.
Proof. intros a; reflexivity. Qed.

Lemma mwinb_cons :
  forall a x l,
    mwinb (node a (x :: l)) = existsb (fun s => negb (mwinb s)) (x :: l).
Proof. intros a x l; reflexivity. Qed.

(** A single misere Nim pile is lost by the mover exactly on one stone. *)
Theorem mwinb_nim : forall k, mwinb (nim k) = negb (Nat.eqb k 1).
Proof.
  assert (Haux : forall N k, k <= N -> mwinb (nim k) = negb (Nat.eqb k 1)).
  { induction N as [|N IH]; intros k Hk.
    - assert (k = 0) by lia; subst; reflexivity.
    - destruct k as [|j]; [reflexivity|].
      destruct j as [|i].
      + (* one stone: the only move is to the empty pile, which the
           opponent then wins *)
        change (nim 1) with (node tt [node tt (@nil game)]).
        rewrite mwinb_cons.
        change (existsb (fun s => negb (mwinb s)) [node tt (@nil game)])
          with (negb (mwinb (node tt (@nil game))) || false)%bool.
        rewrite mwinb_nil; reflexivity.
      + (* two or more: move to the single stone and leave it *)
        assert (Hin : In (nim 1) (nim_list (S (S i)))).
        { rewrite nim_list_shape; apply in_map_iff.
          exists 1; split; [reflexivity | apply in_seq; lia]. }
        destruct (nim_list (S (S i))) as [|x l] eqn:El; [destruct Hin|].
        change (nim (S (S i))) with (node tt (nim_list (S (S i)))).
        rewrite El, mwinb_cons.
        apply existsb_exists.
        exists (nim 1); split; [exact Hin|].
        rewrite (IH 1) by lia; reflexivity. }
  intros k; apply (Haux k); lia.
Qed.

(** * Solved positions *)

Example nim_123_second_player_wins : winb (nim_sum [1; 2; 3]) = false.
Proof. vm_compute; reflexivity. Qed.

Example nim_25_first_player_wins : winb (nim_sum [2; 5]) = true.
Proof. vm_compute; reflexivity. Qed.

Example grundy_nim_12 : grundy (nim_sum [1; 2]) = 3.
Proof. vm_compute; reflexivity. Qed.

(** Two single stones: a normal-play loss for the mover but a misere win. *)
Example misere_differs :
  (mwinb (nim_sum [1; 1]), winb (nim_sum [1; 1])) = (true, false).
Proof. vm_compute; reflexivity. Qed.

Example misere_ones_odd : mwinb (nim_sum [1; 1; 1]) = false.
Proof. vm_compute; reflexivity. Qed.

(** With a pile of two or more the two conventions agree here. *)
Example misere_agrees :
  (mwinb (nim_sum [1; 2]), winb (nim_sum [1; 2])) = (true, true).
Proof. vm_compute; reflexivity. Qed.

(** * Misere Nim for sums *)

(** ** Pile lists as positions *)

(** A move lowers exactly one pile. *)
Fixpoint succs (l : list nat) : list (list nat) :=
  match l with
  | [] => []
  | p :: rest =>
    map (fun q => q :: rest) (seq 0 p) ++ map (fun r => p :: r) (succs rest)
  end.

Definition xo (l : list nat) : nat := fold_right Nat.lxor 0 l.
Definition ones (l : list nat) : nat := length (filter (fun p => p =? 1) l).
Definition bigs (l : list nat) : nat := length (filter (fun p => 2 <=? p) l).
Definition total (l : list nat) : nat := fold_right Nat.add 0 l.

(** Every pile is at most one stone. *)
Definition small (l : list nat) : Prop := forall p, In p l -> p <= 1.

Lemma succs_head :
  forall p rest q, q < p -> In (q :: rest) (succs (p :: rest)).
Proof.
  intros p rest q Hq; simpl; apply in_or_app; left.
  apply in_map_iff; exists q; split; [reflexivity | apply in_seq; lia].
Qed.

Lemma succs_tail :
  forall p rest r, In r (succs rest) -> In (p :: r) (succs (p :: rest)).
Proof.
  intros p rest r Hr; simpl; apply in_or_app; right.
  apply in_map_iff; exists r; split; [reflexivity | exact Hr].
Qed.

Lemma succs_inv :
  forall p rest l',
    In l' (succs (p :: rest)) ->
    (exists q, q < p /\ l' = q :: rest) \/
    (exists r, In r (succs rest) /\ l' = p :: r).
Proof.
  intros p rest l' Hin; simpl in Hin.
  apply in_app_or in Hin; destruct Hin as [Hin | Hin];
    apply in_map_iff in Hin; destruct Hin as [z [Hz Hin]].
  - left; exists z; split; [apply in_seq in Hin; lia | auto].
  - right; exists z; split; [exact Hin | auto].
Qed.

(** The game of a pile list unfolds into the games of its successors. *)
Lemma tsum_nim_unfold :
  forall p t,
    tsum (nim p) t =
    node tt (map (fun s' => tsum s' t) (nim_list p) ++
             map (tsum (nim p)) (children t)).
Proof. intros p [b ts]; apply tsum_eq. Qed.

Lemma nim_sum_unfold :
  forall l, nim_sum l = node tt (map nim_sum (succs l)).
Proof.
  induction l as [|p rest IH]; [reflexivity|].
  assert (Hch : children (nim_sum rest) = map nim_sum (succs rest))
    by (rewrite IH; reflexivity).
  change (nim_sum (p :: rest)) with (tsum (nim p) (nim_sum rest)).
  rewrite tsum_nim_unfold, Hch.
  simpl succs; rewrite map_app.
  f_equal; f_equal.
  - rewrite nim_list_shape, map_map, map_map; reflexivity.
  - rewrite map_map, map_map; reflexivity.
Qed.

Lemma mwinb_nonnil :
  forall a l, l <> [] -> mwinb (node a l) = existsb (fun s => negb (mwinb s)) l.
Proof. intros a [|x xs] Hne; [contradiction | apply mwinb_cons]. Qed.

Lemma mwinb_nim_sum_eq :
  forall l,
    mwinb (nim_sum l) =
    match succs l with
    | [] => true
    | _ => existsb (fun m => negb (mwinb (nim_sum m))) (succs l)
    end.
Proof.
  intros l; rewrite nim_sum_unfold.
  destruct (succs l) as [|m ms] eqn:E; [reflexivity|].
  rewrite mwinb_nonnil by (simpl; discriminate).
  rewrite existsb_map; reflexivity.
Qed.

Lemma winb_nim_sum_eq :
  forall l,
    winb (nim_sum l) = existsb (fun m => negb (winb (nim_sum m))) (succs l).
Proof.
  intros l; rewrite nim_sum_unfold, winb_eq, map_map.
  apply existsb_map.
Qed.

(** ** Arithmetic of the pile statistics *)

Lemma succs_nil_iff : forall l, succs l = [] <-> total l = 0.
Proof.
  induction l as [|p rest IH]; simpl; [split; auto|].
  split.
  - intros H; apply app_eq_nil in H; destruct H as [H1 H2].
    assert (Hp : p = 0).
    { destruct p as [|k]; auto; simpl in H1; discriminate. }
    assert (Hr : succs rest = []).
    { destruct (succs rest) as [|a ?]; auto; simpl in H2; discriminate. }
    rewrite Hp; simpl; apply IH; exact Hr.
  - intros H.
    assert (Hp : p = 0) by lia.
    assert (Hr : total rest = 0) by lia.
    rewrite Hp; simpl.
    rewrite (proj2 IH Hr); reflexivity.
Qed.

Lemma in_succs_total : forall l l', In l' (succs l) -> total l' < total l.
Proof.
  induction l as [|p rest IH]; intros l' Hin; [destruct Hin|].
  apply succs_inv in Hin; destruct Hin as [[q [Hq ->]] | [r [Hr ->]]];
    simpl; [lia|].
  specialize (IH r Hr); lia.
Qed.

Lemma in_succs_xor : forall l l', In l' (succs l) -> xo l' <> xo l.
Proof.
  induction l as [|p rest IH]; intros l' Hin; [destruct Hin|].
  apply succs_inv in Hin; destruct Hin as [[q [Hq ->]] | [r [Hr ->]]];
    unfold xo; simpl; intros Heq.
  - apply lxor_cancel_r in Heq; lia.
  - apply lxor_cancel_l in Heq.
    exact (IH r Hr Heq).
Qed.

Lemma small_cons_inv :
  forall p rest, small (p :: rest) -> p <= 1 /\ small rest.
Proof.
  intros p rest H; split.
  - apply H; left; reflexivity.
  - intros q Hq; apply H; right; exact Hq.
Qed.

Lemma xo_small :
  forall l, small l -> xo l = if Nat.even (ones l) then 0 else 1.
Proof.
  induction l as [|p rest IH]; [reflexivity|].
  intros Hs; apply small_cons_inv in Hs; destruct Hs as [Hp Hrest].
  specialize (IH Hrest).
  assert (Hp01 : p = 0 \/ p = 1) by lia.
  destruct Hp01 as [-> | ->].
  - assert (Ho : ones (0 :: rest) = ones rest) by reflexivity.
    assert (Hx : xo (0 :: rest) = xo rest)
      by (unfold xo; simpl; apply Nat.lxor_0_l).
    rewrite Ho, Hx; exact IH.
  - assert (Ho : ones (1 :: rest) = S (ones rest)) by reflexivity.
    assert (Hx : xo (1 :: rest) = Nat.lxor 1 (xo rest)) by reflexivity.
    rewrite Ho, Hx, IH, Nat.even_succ, <- Nat.negb_even.
    destruct (Nat.even (ones rest)); simpl negb.
    + rewrite Nat.lxor_0_r; reflexivity.
    + rewrite Nat.lxor_nilpotent; reflexivity.
Qed.

Lemma bigs_cons :
  forall p l, bigs (p :: l) = if 2 <=? p then S (bigs l) else bigs l.
Proof.
  intros p l; unfold bigs.
  change (filter (fun q => 2 <=? q) (p :: l))
    with (if 2 <=? p then p :: filter (fun q => 2 <=? q) l
          else filter (fun q => 2 <=? q) l).
  destruct (2 <=? p); reflexivity.
Qed.

Lemma ones_cons :
  forall p l, ones (p :: l) = if p =? 1 then S (ones l) else ones l.
Proof.
  intros p l; unfold ones.
  change (filter (fun q => q =? 1) (p :: l))
    with (if p =? 1 then p :: filter (fun q => q =? 1) l
          else filter (fun q => q =? 1) l).
  destruct (p =? 1); reflexivity.
Qed.

Lemma ones_cons_zero : forall l, ones (0 :: l) = ones l.
Proof. intros l; rewrite ones_cons; reflexivity. Qed.

Lemma ones_cons_one : forall l, ones (1 :: l) = S (ones l).
Proof. intros l; rewrite ones_cons; reflexivity. Qed.

Lemma small_bigs : forall l, small l <-> bigs l = 0.
Proof.
  induction l as [|p rest IH];
    [simpl; split; [reflexivity | intros _ q []] |].
  rewrite bigs_cons; split.
  - intros Hs; apply small_cons_inv in Hs; destruct Hs as [Hp Hrest].
    destruct (2 <=? p) eqn:E; [apply Nat.leb_le in E; lia|].
    apply (proj1 IH Hrest).
  - intros H q Hq.
    destruct (2 <=? p) eqn:E; [discriminate|].
    apply Nat.leb_gt in E.
    destruct Hq as [-> | Hq]; [lia|].
    apply (proj2 IH H q Hq).
Qed.

Lemma succ_small :
  forall l l',
    small l -> In l' (succs l) -> small l' /\ S (ones l') = ones l.
Proof.
  induction l as [|p rest IH]; intros l' Hs Hin; [destruct Hin|].
  apply small_cons_inv in Hs; destruct Hs as [Hp Hrest].
  apply succs_inv in Hin; destruct Hin as [[q [Hq ->]] | [r [Hr ->]]].
  - assert (Hp1 : p = 1) by lia.
    assert (Hq0 : q = 0) by lia.
    subst; split.
    + intros z [-> | Hz]; [lia | apply Hrest; exact Hz].
    + unfold ones; simpl; reflexivity.
  - destruct (IH r Hrest Hr) as [Hsm Hon].
    split.
    + intros z [-> | Hz]; [lia | apply Hsm; exact Hz].
    + unfold ones in *; simpl.
      destruct (p =? 1); simpl; lia.
Qed.

Lemma total_zero_small : forall l, total l = 0 -> small l.
Proof.
  induction l as [|p rest IH]; intros H q Hq; [destruct Hq|].
  unfold total in H; simpl in H.
  destruct Hq as [-> | Hq]; [lia|].
  apply IH; [unfold total; lia | exact Hq].
Qed.

Lemma total_zero_ones : forall l, total l = 0 -> ones l = 0.
Proof.
  induction l as [|p rest IH]; [reflexivity|].
  simpl; intros H.
  assert (Hp : p = 0) by lia.
  unfold ones; simpl; rewrite Hp; simpl.
  apply IH; lia.
Qed.

(** With exactly one big pile the XOR is a big pile against a small remainder,
   so it cannot vanish. *)
Lemma bigs_one_xor_shape :
  forall l,
    bigs l = 1 -> exists a b, 2 <= a /\ b <= 1 /\ xo l = Nat.lxor a b.
Proof.
  induction l as [|p rest IH]; intros H;
    [unfold bigs in H; simpl in H; discriminate|].
  rewrite bigs_cons in H.
  destruct (2 <=? p) eqn:E.
  - apply Nat.leb_le in E.
    injection H as H.
    assert (Hs : small rest) by (apply small_bigs; exact H).
    exists p, (xo rest); repeat split.
    + exact E.
    + rewrite (xo_small rest Hs); destruct (Nat.even (ones rest)); lia.
  - apply Nat.leb_gt in E.
    destruct (IH H) as [a [b (Ha & Hb & Hxo)]].
    exists a, (Nat.lxor p b); repeat split.
    + exact Ha.
    + assert (Hp01 : p = 0 \/ p = 1) by lia.
      assert (Hb01 : b = 0 \/ b = 1) by lia.
      destruct Hp01 as [-> | ->]; destruct Hb01 as [-> | ->];
        vm_compute; lia.
    + unfold xo; simpl; fold (xo rest); rewrite Hxo.
      rewrite <- Nat.lxor_assoc, (Nat.lxor_comm p a), Nat.lxor_assoc.
      reflexivity.
Qed.

Lemma bigs_one_xor_nonzero : forall l, bigs l = 1 -> xo l <> 0.
Proof.
  intros l H Hx.
  destruct (bigs_one_xor_shape l H) as [a [b (Ha & Hb & Hxo)]].
  rewrite Hxo in Hx.
  apply (proj1 (lxor_eq_0 a b)) in Hx.
  subst b; lia.
Qed.

Lemma xor_zero_bigs_two :
  forall l, xo l = 0 -> 1 <= bigs l -> 2 <= bigs l.
Proof.
  intros l Hx Hb.
  destruct (bigs l) as [|[|k]] eqn:E; [lia | | lia].
  exfalso; exact (bigs_one_xor_nonzero l E Hx).
Qed.

Lemma succ_keeps_big :
  forall l l', 2 <= bigs l -> In l' (succs l) -> 1 <= bigs l'.
Proof.
  induction l as [|p rest IH]; intros l' Hb Hin; [destruct Hin|].
  rewrite bigs_cons in Hb.
  destruct (2 <=? p) eqn:Ep; simpl in Hb;
    apply succs_inv in Hin; destruct Hin as [[q [Hq ->]] | [r [Hr ->]]];
    rewrite bigs_cons.
  - destruct (2 <=? q); lia.
  - rewrite Ep; simpl; lia.
  - destruct (2 <=? q); lia.
  - rewrite Ep; simpl; apply IH; [lia | exact Hr].
Qed.

(** With one big pile the mover can hand over any parity of single stones. *)
Lemma one_big_move_par :
  forall l b,
    bigs l = 1 ->
    exists l', In l' (succs l) /\ small l' /\ Nat.even (ones l') = b.
Proof.
  induction l as [|p rest IH]; intros b H;
    [unfold bigs in H; simpl in H; discriminate|].
  rewrite bigs_cons in H.
  destruct (2 <=? p) eqn:E.
  - apply Nat.leb_le in E.
    injection H as H.
    assert (Hs : small rest) by (apply small_bigs; exact H).
    destruct (Bool.bool_dec (Nat.even (ones rest)) b) as [Heq | Hne].
    + exists (0 :: rest); repeat split.
      * apply succs_head; lia.
      * intros z [-> | Hz]; [lia | apply Hs; exact Hz].
      * rewrite ones_cons_zero; exact Heq.
    + exists (1 :: rest); repeat split.
      * apply succs_head; lia.
      * intros z [-> | Hz]; [lia | apply Hs; exact Hz].
      * rewrite ones_cons_one, Nat.even_succ, <- Nat.negb_even.
        destruct (Nat.even (ones rest)); destruct b; simpl in *; congruence.
  - apply Nat.leb_gt in E.
    assert (Hb : bigs rest = 1) by lia.
    destruct (p =? 1) eqn:Ep.
    + destruct (IH (negb b) Hb) as [r (Hr & Hsm & Hon)].
      exists (p :: r); repeat split.
      * apply succs_tail; exact Hr.
      * intros z [-> | Hz]; [lia | apply Hsm; exact Hz].
      * assert (Ho : ones (p :: r) = S (ones r))
          by (rewrite ones_cons, Ep; reflexivity).
        rewrite Ho, Nat.even_succ, <- Nat.negb_even, Hon, negb_involutive.
        reflexivity.
    + destruct (IH b Hb) as [r (Hr & Hsm & Hon)].
      exists (p :: r); repeat split.
      * apply succs_tail; exact Hr.
      * intros z [-> | Hz]; [lia | apply Hsm; exact Hz].
      * assert (Ho : ones (p :: r) = ones r)
          by (rewrite ones_cons, Ep; reflexivity).
        rewrite Ho; exact Hon.
Qed.

(** ** The theorem *)

(** Under misere play the mover wins a Nim sum exactly when either some pile
   holds two or more stones and the XOR of the piles is nonzero, or every pile
   holds at most one stone and their number is even. *)
Theorem mwinb_nim_sum :
  forall l,
    mwinb (nim_sum l) =
    if 1 <=? bigs l then negb (Nat.eqb (xo l) 0) else Nat.even (ones l).
Proof.
  assert (Haux : forall N l, total l <= N ->
    mwinb (nim_sum l) =
    if 1 <=? bigs l then negb (Nat.eqb (xo l) 0) else Nat.even (ones l)).
  { induction N as [|N IH]; intros l HN.
    - assert (Ht : total l = 0) by lia.
      assert (Hs : small l) by (apply total_zero_small; exact Ht).
      rewrite mwinb_nim_sum_eq, (proj2 (succs_nil_iff l) Ht).
      rewrite (proj1 (small_bigs l) Hs); simpl.
      rewrite (total_zero_ones l Ht); reflexivity.
    - destruct (1 <=? bigs l) eqn:Eb.
      + (* some pile holds two or more stones *)
        apply Nat.leb_le in Eb.
        assert (Hne : succs l <> []).
        { intros Hnil.
          assert (Ht : total l = 0) by (apply succs_nil_iff; exact Hnil).
          assert (Hs : small l) by (apply total_zero_small; exact Ht).
          apply (proj1 (small_bigs l)) in Hs; lia. }
        destruct (Nat.eqb (xo l) 0) eqn:Ex; simpl.
        * (* vanishing XOR: every move hands the opponent a winning position *)
          apply Nat.eqb_eq in Ex.
          assert (Hb2 : 2 <= bigs l) by (apply xor_zero_bigs_two; auto).
          rewrite mwinb_nim_sum_eq.
          destruct (succs l) as [|m ms] eqn:Es; [contradiction|].
          rewrite <- Es.
          assert (Hall : forall m', In m' (succs l) ->
                    negb (mwinb (nim_sum m')) = false).
          { intros m' Hm'.
            assert (Hb' : 1 <= bigs m') by (apply (succ_keeps_big l); auto).
            assert (Hx' : xo m' <> 0)
              by (rewrite <- Ex; apply in_succs_xor; exact Hm').
            rewrite (IH m').
            - apply Nat.leb_le in Hb'; rewrite Hb'.
              destruct (Nat.eqb (xo m') 0) eqn:E'; simpl; auto.
              apply Nat.eqb_eq in E'; contradiction.
            - pose proof (in_succs_total l m' Hm'); lia. }
          rewrite (existsb_ext_in _ (fun _ => false) (succs l) Hall).
          apply existsb_const; rewrite Es; discriminate.
        * (* nonvanishing XOR: the mover has a winning reply *)
          assert (Hx : xo l <> 0)
            by (intros H0; rewrite H0 in Ex; simpl in Ex; discriminate).
          rewrite mwinb_nim_sum_eq.
          destruct (succs l) as [|m ms] eqn:Es; [contradiction|].
          rewrite <- Es.
          apply existsb_exists.
          destruct (Nat.eq_dec (bigs l) 1) as [Hb1 | Hbne].
          -- (* exactly one big pile: leave an odd number of single stones *)
             destruct (one_big_move_par l false Hb1) as [l' (Hl' & Hsm & Hon)].
             exists l'; split; [exact Hl'|].
             rewrite (IH l').
             ++ rewrite (proj1 (small_bigs l') Hsm); simpl; rewrite Hon; auto.
             ++ pose proof (in_succs_total l l' Hl'); lia.
          -- (* two or more big piles: the normal-play move keeps one *)
             assert (Hb2 : 2 <= bigs l) by lia.
             assert (Hw : winb (nim_sum l) = true)
               by (apply bouton; exact Hx).
             rewrite winb_nim_sum_eq in Hw.
             apply existsb_exists in Hw.
             destruct Hw as [l' [Hl' Hwl']].
             apply negb_true_iff in Hwl'.
             exists l'; split; [exact Hl'|].
             assert (Hx' : xo l' = 0).
             { destruct (Nat.eq_dec (xo l') 0) as [H0 | Hn0]; auto.
               exfalso.
               assert (Hbad : winb (nim_sum l') = true)
                 by (apply bouton; exact Hn0).
               congruence. }
             assert (Hb' : 1 <= bigs l') by (apply (succ_keeps_big l); auto).
             rewrite (IH l').
             ++ apply Nat.leb_le in Hb'; rewrite Hb', Hx'; reflexivity.
             ++ pose proof (in_succs_total l l' Hl'); lia.
      + (* every pile holds at most one stone *)
        assert (Hs : small l).
        { apply small_bigs.
          apply Nat.leb_gt in Eb; lia. }
        rewrite mwinb_nim_sum_eq.
        destruct (succs l) as [|m ms] eqn:Es.
        * assert (Ht : total l = 0) by (apply succs_nil_iff; exact Es).
          rewrite (total_zero_ones l Ht); reflexivity.
        * rewrite <- Es.
          assert (Hne : succs l <> []) by (rewrite Es; discriminate).
          destruct (ones l) as [|k] eqn:Eo.
          -- (* no single stones left, yet a move exists: impossible *)
             exfalso.
             destruct (succs l) as [|m' ms'] eqn:Es'; [discriminate|].
             assert (Hin : In m' (succs l)) by (rewrite Es'; left; auto).
             destruct (succ_small l m' Hs Hin) as [_ Hon]; lia.
          -- assert (Hall : forall m', In m' (succs l) ->
                       negb (mwinb (nim_sum m')) = negb (Nat.even k)).
             { intros m' Hm'.
               destruct (succ_small l m' Hs Hm') as [Hsm Hon].
               rewrite (IH m').
               - rewrite (proj1 (small_bigs m') Hsm); simpl.
                 rewrite Eo in Hon; injection Hon as Hon.
                 rewrite Hon; reflexivity.
               - pose proof (in_succs_total l m' Hm'); lia. }
             rewrite (existsb_ext_in _ (fun _ => negb (Nat.even k))
                        (succs l) Hall).
             rewrite (existsb_const (negb (Nat.even k)) (succs l) Hne).
             rewrite Nat.even_succ, <- Nat.negb_even; reflexivity. }
  intros l; apply (Haux (total l)); lia.
Qed.

(** The mover loses exactly when every pile is at most one and their number is
   odd, or some pile is at least two and the XOR vanishes. *)
Corollary mwinb_nim_sum_false_iff :
  forall l,
    mwinb (nim_sum l) = false <->
    (small l /\ Nat.odd (ones l) = true) \/
    ((exists p, In p l /\ 2 <= p) /\ xo l = 0).
Proof.
  intros l; rewrite mwinb_nim_sum.
  assert (Hbig : 1 <= bigs l <-> exists p, In p l /\ 2 <= p).
  { unfold bigs; split.
    - intros H.
      destruct (filter (fun p => 2 <=? p) l) as [|a rest] eqn:E;
        [simpl in H; lia|].
      assert (Hin : In a (filter (fun p => 2 <=? p) l))
        by (rewrite E; left; auto).
      apply filter_In in Hin; destruct Hin as [Hin Hle].
      exists a; split; [exact Hin | apply Nat.leb_le; exact Hle].
    - intros [p [Hp Hle]].
      assert (Hin : In p (filter (fun q => 2 <=? q) l))
        by (apply filter_In; split; [exact Hp | apply Nat.leb_le; exact Hle]).
      destruct (filter (fun q => 2 <=? q) l); [destruct Hin | simpl; lia]. }
  destruct (1 <=? bigs l) eqn:Eb.
  - apply Nat.leb_le in Eb.
    split.
    + intros H; right; split; [apply Hbig; exact Eb|].
      apply negb_false_iff, Nat.eqb_eq in H; exact H.
    + intros [[Hs _] | [_ Hx]].
      * exfalso; apply (proj1 (small_bigs l)) in Hs; lia.
      * rewrite Hx; reflexivity.
  - apply Nat.leb_gt in Eb.
    assert (Hs : small l) by (apply small_bigs; lia).
    split.
    + intros H; left; split; [exact Hs|].
      rewrite <- Nat.negb_even, H; reflexivity.
    + intros [[_ Ho] | [Hex _]].
      * rewrite <- Nat.negb_even in Ho.
        apply negb_true_iff in Ho; exact Ho.
      * exfalso; apply Hbig in Hex; lia.
Qed.

(** Three single stones lose under misere play and win under normal play: the
    two criteria disagree exactly on the all-small positions. *)
Example misere_ones_three : mwinb (nim_sum [1; 1; 1]) = false.
Proof. rewrite mwinb_nim_sum; reflexivity. Qed.

Example normal_ones_three : winb (nim_sum [1; 1; 1]) = true.
Proof. apply bouton; vm_compute; discriminate. Qed.

(** With a big pile present the misere criterion is the normal-play one. *)
Example misere_123 : mwinb (nim_sum [1; 2; 3]) = false.
Proof. rewrite mwinb_nim_sum; reflexivity. Qed.

Example misere_25 : mwinb (nim_sum [2; 5]) = true.
Proof. rewrite mwinb_nim_sum; reflexivity. Qed.
