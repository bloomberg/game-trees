(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Blue-Red Hackenbush on strings: Left deletes blue edges, Right red ones. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.Conway.

(** * Strict order and option collapse *)




(** * List and negation helpers *)




(** * Stalks *)

Inductive colour : Type := Blue | Red.

(** The colours of a stalk's edges, ground edge first. *)
Definition stalk : Type := list colour.

Definition is_blue (s : stalk) (i : nat) : bool :=
  match nth_error s i with Some Blue => true | _ => false end.

Definition is_red (s : stalk) (i : nat) : bool :=
  match nth_error s i with Some Red => true | _ => false end.

(** Deleting the edge at index [i] leaves the edges below it. *)
Definition lcuts (s : stalk) : list stalk :=
  map (fun i => firstn i s) (filter (is_blue s) (seq 0 (length s))).

Definition rcuts (s : stalk) : list stalk :=
  map (fun i => firstn i s) (filter (is_red s) (seq 0 (length s))).

Lemma in_lcuts :
  forall s s',
    In s' (lcuts s) <->
    exists i, i < length s /\ is_blue s i = true /\ s' = firstn i s.
Proof.
  intros s s'; unfold lcuts; rewrite in_map_iff; split.
  - intros [i [<- Hi]].
    apply filter_In in Hi; destruct Hi as [Hi Hb].
    apply in_seq in Hi.
    exists i; repeat split; auto; lia.
  - intros [i [Hi [Hb ->]]].
    exists i; split; auto.
    apply filter_In; split; auto.
    apply in_seq; lia.
Qed.

Lemma in_rcuts :
  forall s s',
    In s' (rcuts s) <->
    exists i, i < length s /\ is_red s i = true /\ s' = firstn i s.
Proof.
  intros s s'; unfold rcuts; rewrite in_map_iff; split.
  - intros [i [<- Hi]].
    apply filter_In in Hi; destruct Hi as [Hi Hb].
    apply in_seq in Hi.
    exists i; repeat split; auto; lia.
  - intros [i [Hi [Hb ->]]].
    exists i; split; auto.
    apply filter_In; split; auto.
    apply in_seq; lia.
Qed.

Lemma lcuts_shorter :
  forall s s', In s' (lcuts s) -> length s' < length s.
Proof.
  intros s s' Hs; apply in_lcuts in Hs.
  destruct Hs as [i [Hi [_ ->]]].
  rewrite length_firstn; lia.
Qed.

Lemma rcuts_shorter :
  forall s s', In s' (rcuts s) -> length s' < length s.
Proof.
  intros s s' Hs; apply in_rcuts in Hs.
  destruct Hs as [i [Hi [_ ->]]].
  rewrite length_firstn; lia.
Qed.

(** * The game of a stalk *)

Fixpoint hb (fuel : nat) (s : stalk) : pgame :=
  match fuel with
  | 0 => PG [] []
  | S f => PG (map (hb f) (lcuts s)) (map (hb f) (rcuts s))
  end.

Lemma hb_stable :
  forall N s f1 f2,
    length s <= N -> length s <= f1 -> length s <= f2 ->
    hb f1 s = hb f2 s.
Proof.
  induction N as [|N IH]; intros s f1 f2 HN Hf1 Hf2.
  - assert (Hs : s = []) by (apply length_zero_iff_nil; lia).
    subst s; destruct f1; destruct f2; reflexivity.
  - destruct f1 as [|f1].
    + assert (Hs : s = []) by (apply length_zero_iff_nil; lia).
      subst s; destruct f2; reflexivity.
    + destruct f2 as [|f2].
      * assert (Hs : s = []) by (apply length_zero_iff_nil; lia).
        subst s; reflexivity.
      * simpl; f_equal; apply map_ext_in; intros m Hm.
        -- pose proof (lcuts_shorter s m Hm); apply (IH m); lia.
        -- pose proof (rcuts_shorter s m Hm); apply (IH m); lia.
Qed.

Definition Hb (s : stalk) : pgame := hb (length s) s.

Lemma hb_Hb : forall f s, length s <= f -> hb f s = Hb s.
Proof.
  intros f s Hf; unfold Hb; apply (hb_stable (length s)); lia.
Qed.

Lemma Hb_eq :
  forall s, Hb s = PG (map Hb (lcuts s)) (map Hb (rcuts s)).
Proof.
  intros s; unfold Hb at 1.
  destruct (length s) as [|f] eqn:Es.
  - assert (Hs : s = []) by (apply length_zero_iff_nil; auto).
    subst s; reflexivity.
  - simpl; f_equal; apply map_ext_in; intros m Hm.
    + pose proof (lcuts_shorter s m Hm); apply hb_Hb; lia.
    + pose proof (rcuts_shorter s m Hm); apply hb_Hb; lia.
Qed.

Lemma lopts_Hb : forall s, lopts (Hb s) = map Hb (lcuts s).
Proof. intros s; rewrite Hb_eq; reflexivity. Qed.

Lemma ropts_Hb : forall s, ropts (Hb s) = map Hb (rcuts s).
Proof. intros s; rewrite Hb_eq; reflexivity. Qed.

Lemma Hb_nil : Hb [] = zero.
Proof. reflexivity. Qed.

(** * Colour symmetry *)

Definition swapc (c : colour) : colour :=
  match c with Blue => Red | Red => Blue end.

Definition swaps (s : stalk) : stalk := map swapc s.

Lemma swapc_swapc : forall c, swapc (swapc c) = c.
Proof. intros []; reflexivity. Qed.

Lemma swaps_swaps : forall s, swaps (swaps s) = s.
Proof.
  intros s; unfold swaps; rewrite map_map.
  rewrite (map_ext_in _ (fun c => c) s), map_id; auto.
  intros a _; apply swapc_swapc.
Qed.

Lemma is_blue_swaps : forall s i, is_blue (swaps s) i = is_red s i.
Proof.
  intros s i; unfold is_blue, is_red, swaps.
  rewrite nth_error_map.
  destruct (nth_error s i) as [[|]|]; reflexivity.
Qed.

Lemma is_red_swaps : forall s i, is_red (swaps s) i = is_blue s i.
Proof.
  intros s i; unfold is_blue, is_red, swaps.
  rewrite nth_error_map.
  destruct (nth_error s i) as [[|]|]; reflexivity.
Qed.

Lemma length_swaps : forall s, length (swaps s) = length s.
Proof. intros s; unfold swaps; apply length_map. Qed.

Lemma lcuts_swaps : forall s, lcuts (swaps s) = map swaps (rcuts s).
Proof.
  intros s; unfold lcuts, rcuts.
  rewrite length_swaps, map_map.
  rewrite (filter_ext (is_blue (swaps s)) (is_red s))
    by (intros i; apply is_blue_swaps).
  apply map_ext_in; intros i _.
  unfold swaps; rewrite firstn_map; reflexivity.
Qed.

Lemma rcuts_swaps : forall s, rcuts (swaps s) = map swaps (lcuts s).
Proof.
  intros s; unfold lcuts, rcuts.
  rewrite length_swaps, map_map.
  rewrite (filter_ext (is_red (swaps s)) (is_blue s))
    by (intros i; apply is_red_swaps).
  apply map_ext_in; intros i _.
  unfold swaps; rewrite firstn_map; reflexivity.
Qed.

(** Exchanging the colours exchanges the players. *)
Theorem Hb_swap : forall s, Hb (swaps s) = pneg (Hb s).
Proof.
  assert (Haux : forall N s, length s <= N -> Hb (swaps s) = pneg (Hb s)).
  { induction N as [|N IH]; intros s HN.
    - assert (Hs : s = []) by (apply length_zero_iff_nil; lia).
      subst s; reflexivity.
    - rewrite Hb_eq, (Hb_eq s).
      rewrite lcuts_swaps, rcuts_swaps.
      change (pneg (PG (map Hb (lcuts s)) (map Hb (rcuts s))))
        with (PG (map pneg (map Hb (rcuts s))) (map pneg (map Hb (lcuts s)))).
      rewrite !map_map.
      f_equal; apply map_ext_in; intros m Hm.
      + apply IH; pose proof (rcuts_shorter s m Hm); lia.
      + apply IH; pose proof (lcuts_shorter s m Hm); lia. }
  intros s; apply (Haux (length s)); lia.
Qed.

(** * The sign theorem *)

Lemma firstn_cons_pos :
  forall (A : Type) (a : A) (l : list A) i,
    0 < i -> firstn i (a :: l) = a :: firstn (i - 1) l.
Proof.
  intros A a l i Hi; destruct i as [|j]; [lia|].
  simpl; f_equal; f_equal; lia.
Qed.

(** A cut above the ground edge leaves the ground edge in place. *)
Lemma rcuts_blue_head :
  forall t s', In s' (rcuts (Blue :: t)) -> exists t', s' = Blue :: t'.
Proof.
  intros t s' Hs; apply in_rcuts in Hs.
  destruct Hs as [i [Hi [Hr ->]]].
  destruct i as [|j].
  - unfold is_red in Hr; simpl in Hr; discriminate.
  - exists (firstn j t); reflexivity.
Qed.

Lemma lcuts_red_head :
  forall t s', In s' (lcuts (Red :: t)) -> exists t', s' = Red :: t'.
Proof.
  intros t s' Hs; apply in_lcuts in Hs.
  destruct Hs as [i [Hi [Hb ->]]].
  destruct i as [|j].
  - unfold is_blue in Hb; simpl in Hb; discriminate.
  - exists (firstn j t); reflexivity.
Qed.

Lemma nil_in_lcuts_blue : forall t, In [] (lcuts (Blue :: t)).
Proof.
  intros t; apply in_lcuts.
  exists 0; repeat split; simpl; auto; lia.
Qed.

(** A stalk with a blue ground edge is positive. *)
Theorem hb_ground_blue : forall t, glt zero (Hb (Blue :: t)).
Proof.
  assert (Haux : forall N t, length t <= N -> glt zero (Hb (Blue :: t))).
  { induction N as [|N IH]; intros t HN.
    - assert (Ht : t = []) by (apply length_zero_iff_nil; lia).
      subst t; split; reflexivity.
    - split.
      + apply gle_true_iff; split.
        * intros r Hr.
          rewrite ropts_Hb in Hr.
          apply in_map_iff in Hr; destruct Hr as [s' [<- Hs']].
          destruct (rcuts_blue_head t s' Hs') as [t' ->].
          assert (Hlen : length t' < length t).
          { pose proof (rcuts_shorter (Blue :: t) (Blue :: t') Hs') as Hl.
            simpl in Hl; lia. }
          assert (HN' : length t' <= N) by lia.
          destruct (IH t' HN') as [_ Hne]; exact Hne.
        * intros g Hg; destruct Hg.
      + apply gle_lopt.
        rewrite lopts_Hb.
        change zero with (Hb []).
        apply in_map_iff; eexists; split;
          [reflexivity | apply nil_in_lcuts_blue]. }
  intros t; apply (Haux (length t)); lia.
Qed.

Theorem hb_ground_red : forall t, glt (Hb (Red :: t)) zero.
Proof.
  intros t.
  assert (Hs : Hb (Red :: t) = pneg (Hb (Blue :: swaps t))).
  { rewrite <- Hb_swap.
    f_equal.
    change (swaps (Blue :: swaps t)) with (Red :: swaps (swaps t)).
    rewrite swaps_swaps; reflexivity. }
  destruct (hb_ground_blue (swaps t)) as [H1 H2].
  rewrite Hs; split.
  - change (gle (pneg (Hb (Blue :: swaps t))) (pneg zero) = true).
    rewrite gle_pneg; exact H1.
  - change (gle (pneg zero) (pneg (Hb (Blue :: swaps t))) = false).
    rewrite gle_pneg; exact H2.
Qed.

(** * Integers *)

Definition blues (n : nat) : stalk := repeat Blue n.

Lemma is_blue_blues : forall n i, i < n -> is_blue (blues n) i = true.
Proof.
  intros n i Hi; unfold is_blue, blues.
  rewrite nth_error_repeat by auto; reflexivity.
Qed.

Lemma is_red_blues : forall n i, is_red (blues n) i = false.
Proof.
  intros n i; unfold is_red, blues.
  destruct (nth_error (repeat Blue n) i) as [c|] eqn:E; auto.
  apply nth_error_In in E.
  apply repeat_spec in E; subst; reflexivity.
Qed.

Lemma firstn_blues : forall n i, i <= n -> firstn i (blues n) = blues i.
Proof. intros n i Hi; unfold blues; apply firstn_repeat_le; auto. Qed.

Lemma lcuts_blues : forall n, lcuts (blues n) = map blues (seq 0 n).
Proof.
  intros n; unfold lcuts.
  replace (length (blues n)) with n by (unfold blues; rewrite repeat_length; auto).
  rewrite (filter_all (is_blue (blues n)) (seq 0 n)).
  - apply map_ext_in; intros i Hi.
    apply in_seq in Hi; apply firstn_blues; lia.
  - intros i Hi; apply in_seq in Hi; apply is_blue_blues; lia.
Qed.

Lemma rcuts_blues : forall n, rcuts (blues n) = [].
Proof.
  intros n; unfold rcuts.
  rewrite (filter_none (is_red (blues n)) (seq 0 (length (blues n)))).
  - reflexivity.
  - intros i _; apply is_red_blues.
Qed.

Lemma num_order :
  forall N i j,
    i + j <= N ->
    (i <= j -> gle (num i) (num j) = true) /\
    (i < j -> gle (num j) (num i) = false).
Proof.
  induction N as [|N IH]; intros i j HN; split.
  - intros Hle; assert (i = 0) by lia; assert (j = 0) by lia; subst.
    apply gle_refl.
  - intros Hlt; lia.
  - intros Hle.
    apply gle_true_iff; split.
    + intros r Hr.
      destruct j as [|k]; [destruct Hr|].
      change (ropts (num (S k))) with (@nil pgame) in Hr; destruct Hr.
    + intros l Hl.
      destruct i as [|k]; [destruct Hl|].
      change (lopts (num (S k))) with [num k] in Hl.
      destruct Hl as [<- | []].
      apply (IH k j); lia.
  - intros Hlt.
    apply gle_false_iff; right.
    destruct j as [|k]; [lia|].
    exists (num k); split.
    + change (lopts (num (S k))) with [num k]; left; auto.
    + apply (IH i k); lia.
Qed.

Lemma num_le : forall i j, i <= j -> gle (num i) (num j) = true.
Proof. intros i j H; apply (num_order (i + j) i j); lia. Qed.

Lemma num_lt : forall i j, i < j -> gle (num j) (num i) = false.
Proof. intros i j H; apply (num_order (i + j) i j); lia. Qed.

(** An all-blue stalk of [n] edges is the integer [n]. *)
Theorem hb_blues : forall n, gequiv (Hb (blues n)) (num n) = true.
Proof.
  assert (Haux : forall N n, n <= N -> gequiv (Hb (blues n)) (num n) = true).
  { induction N as [|N IH]; intros n HN.
    - assert (n = 0) by lia; subst; apply gequiv_refl.
    - destruct n as [|k]; [apply gequiv_refl|].
      assert (Hopts : lopts (Hb (blues (S k)))
                      = map (fun i => Hb (blues i)) (seq 0 (S k))).
      { rewrite lopts_Hb, lcuts_blues, map_map; reflexivity. }
      assert (Hr : ropts (Hb (blues (S k))) = []).
      { rewrite ropts_Hb, rcuts_blues; reflexivity. }
      assert (Hmax : In (Hb (blues k)) (lopts (Hb (blues (S k))))).
      { rewrite Hopts; apply in_map_iff; exists k; split; auto.
        apply in_seq; lia. }
      assert (Hdom : forall x, In x (lopts (Hb (blues (S k)))) ->
                     gle x (Hb (blues k)) = true).
      { intros x Hx; rewrite Hopts in Hx.
        apply in_map_iff in Hx; destruct Hx as [i [<- Hi]].
        apply in_seq in Hi.
        apply (gle_gequiv_l (num i)); [apply gequiv_sym, IH; lia|].
        apply (gle_gequiv_r _ (num k)); [apply gequiv_sym, IH; lia|].
        apply num_le; lia. }
      apply (gequiv_trans _ (PG [Hb (blues k)] (ropts (Hb (blues (S k)))))).
      + apply collapse_lopts; auto.
      + rewrite Hr.
        change (num (S k)) with (PG [num k] (@nil pgame)).
        apply gequiv_of_opts.
        * change (lopts (PG [Hb (blues k)] (@nil pgame))) with [Hb (blues k)].
          change (lopts (PG [num k] (@nil pgame))) with [num k].
          split; intros x [<- | []].
          -- exists (num k); split; [left; auto | apply IH; lia].
          -- exists (Hb (blues k)); split; [left; auto | apply IH; lia].
        * split; intros x []. }
  intros n; apply (Haux n); lia.
Qed.

(** * Halves *)






(** * A blue edge under red edges *)

Definition blue_reds (k : nat) : stalk := Blue :: repeat Red k.

Lemma is_blue_blue_reds :
  forall k i, is_blue (blue_reds k) i = true -> i = 0.
Proof.
  intros k i H; destruct i as [|j]; auto.
  exfalso; unfold is_blue, blue_reds in H; simpl in H.
  destruct (nth_error (repeat Red k) j) as [c|] eqn:E; [|discriminate].
  apply nth_error_In, repeat_spec in E; subst; discriminate.
Qed.

Lemma is_red_blue_reds :
  forall k i, i < k -> is_red (blue_reds k) (S i) = true.
Proof.
  intros k i Hi; unfold is_red, blue_reds; simpl.
  rewrite nth_error_repeat by auto; reflexivity.
Qed.

Lemma lcuts_blue_reds : forall k, lcuts (blue_reds k) = [[]].
Proof.
  intros k; unfold lcuts, blue_reds.
  replace (length (Blue :: repeat Red k)) with (1 + k)
    by (simpl; rewrite repeat_length; auto).
  rewrite seq_app, filter_app.
  change (seq 0 1) with [0].
  change (filter (is_blue (Blue :: repeat Red k)) [0]) with [0].
  rewrite (filter_none (is_blue (Blue :: repeat Red k)) (seq (0 + 1) k)).
  - reflexivity.
  - intros i Hi; apply in_seq in Hi.
    destruct (is_blue (Blue :: repeat Red k) i) eqn:E; auto.
    apply is_blue_blue_reds in E; lia.
Qed.

Lemma rcuts_blue_reds :
  forall k, rcuts (blue_reds (S k)) = map blue_reds (seq 0 (S k)).
Proof.
  intros k; unfold rcuts, blue_reds.
  replace (length (Blue :: repeat Red (S k))) with (1 + S k)
    by (simpl; rewrite repeat_length; auto).
  rewrite seq_app, filter_app.
  change (seq 0 1) with [0].
  change (filter (is_red (Blue :: repeat Red (S k))) [0]) with (@nil nat).
  rewrite app_nil_l.
  replace (0 + 1) with 1 by lia.
  rewrite (filter_all (is_red (Blue :: repeat Red (S k))) (seq 1 (S k))).
  - rewrite <- seq_shift, map_map.
    apply map_ext_in; intros i Hi.
    apply in_seq in Hi.
    change (firstn (S i) (Blue :: repeat Red (S k)))
      with (Blue :: firstn i (repeat Red (S k))).
    f_equal.
    apply firstn_repeat_le; lia.
  - intros i Hi; apply in_seq in Hi.
    destruct i as [|j]; [lia|].
    apply is_red_blue_reds; lia.
Qed.

(** A blue edge under [k] red edges is [half k]. *)
Theorem hb_blue_reds :
  forall k, gequiv (Hb (blue_reds k)) (half k) = true.
Proof.
  assert (Haux : forall N k, k <= N ->
            gequiv (Hb (blue_reds k)) (half k) = true).
  { induction N as [|N IH]; intros k HN.
    - assert (k = 0) by lia; subst.
      apply gequiv_true_iff; split; reflexivity.
    - destruct k as [|j].
      + apply gequiv_true_iff; split; reflexivity.
      + assert (Hl : lopts (Hb (blue_reds (S j))) = [zero]).
        { rewrite lopts_Hb, lcuts_blue_reds; reflexivity. }
        assert (Hr : ropts (Hb (blue_reds (S j)))
                     = map (fun i => Hb (blue_reds i)) (seq 0 (S j))).
        { rewrite ropts_Hb, rcuts_blue_reds, map_map; reflexivity. }
        assert (Hmin : In (Hb (blue_reds j)) (ropts (Hb (blue_reds (S j))))).
        { rewrite Hr; apply in_map_iff; exists j; split; auto.
          apply in_seq; lia. }
        assert (Hdom : forall y, In y (ropts (Hb (blue_reds (S j)))) ->
                       gle (Hb (blue_reds j)) y = true).
        { intros y Hy; rewrite Hr in Hy.
          apply in_map_iff in Hy; destruct Hy as [i [<- Hi]].
          apply in_seq in Hi.
          apply (gle_gequiv_l (half j)); [apply gequiv_sym, IH; lia|].
          apply (gle_gequiv_r _ (half i)); [apply gequiv_sym, IH; lia|].
          apply half_le; lia. }
        apply (gequiv_trans _ (PG (lopts (Hb (blue_reds (S j))))
                                  [Hb (blue_reds j)])).
        * apply collapse_ropts; auto.
        * rewrite Hl.
          change (half (S j)) with (PG [zero] [half j]).
          apply gequiv_of_opts.
          -- change (lopts (PG [zero] [Hb (blue_reds j)])) with [zero].
             change (lopts (PG [zero] [half j])) with [zero].
             split; intros x [<- | []]; exists zero;
               (split; [left; auto | apply gequiv_refl]).
          -- change (ropts (PG [zero] [Hb (blue_reds j)]))
               with [Hb (blue_reds j)].
             change (ropts (PG [zero] [half j])) with [half j].
             split; intros x [<- | []].
             ++ exists (half j); split; [left; auto | apply IH; lia].
             ++ exists (Hb (blue_reds j)); split; [left; auto | apply IH; lia]. }
  intros k; apply (Haux k); lia.
Qed.

(** * The outcome of every stalk *)

(** The ground edge decides the outcome of the whole stalk. *)
Theorem hb_outcome :
  forall s,
    outc (Hb s) =
    match s with
    | [] => Secondwins
    | Blue :: _ => Lwins
    | Red :: _ => Rwins
    end.
Proof.
  intros [|c t].
  - apply (proj2 (proj1 (outc_spec (Hb [])))).
    rewrite Hb_nil; apply gequiv_refl.
  - destruct c.
    + apply (proj2 (proj1 (proj2 (proj2 (outc_spec (Hb (Blue :: t))))))).
      exact (hb_ground_blue t).
    + apply (proj2 (proj2 (proj2 (proj2 (outc_spec (Hb (Red :: t))))))).
      exact (hb_ground_red t).
Qed.

(** Blue-Red Hackenbush has no fuzzy stalk: the mover never gains by moving. *)
Corollary hb_never_first : forall s, outc (Hb s) <> Firstwins.
Proof.
  intros s; rewrite hb_outcome.
  destruct s as [|[|] t]; discriminate.
Qed.

(** An all-red stalk is the negative integer. *)
Definition reds (n : nat) : stalk := repeat Red n.

Lemma swaps_blues : forall n, swaps (blues n) = reds n.
Proof.
  intros n; unfold swaps, blues, reds.
  induction n as [|n IH]; [reflexivity|].
  change (map swapc (Blue :: repeat Blue n) = Red :: repeat Red n).
  change (map swapc (Blue :: repeat Blue n))
    with (Red :: map swapc (repeat Blue n)).
  rewrite IH; reflexivity.
Qed.

Theorem hb_reds : forall n, gequiv (Hb (reds n)) (pneg (num n)) = true.
Proof.
  intros n.
  rewrite <- swaps_blues, Hb_swap.
  apply gequiv_pneg, hb_blues.
Qed.

(** * Positions of several stalks *)

Definition position : Type := list stalk.

Fixpoint pcuts (f : stalk -> list stalk) (p : position) : list position :=
  match p with
  | [] => []
  | s :: rest =>
    map (fun s' => s' :: rest) (f s) ++ map (fun r => s :: r) (pcuts f rest)
  end.

Fixpoint psize (p : position) : nat :=
  match p with [] => 0 | s :: rest => length s + psize rest end.

Fixpoint hbp (fuel : nat) (p : position) : pgame :=
  match fuel with
  | 0 => PG [] []
  | S f => PG (map (hbp f) (pcuts lcuts p)) (map (hbp f) (pcuts rcuts p))
  end.

Lemma pcuts_smaller :
  forall f p q,
    (forall s s', In s' (f s) -> length s' < length s) ->
    In q (pcuts f p) -> psize q < psize p.
Proof.
  intros f p; induction p as [|s rest IH]; intros q Hf Hq.
  - destruct Hq.
  - change (pcuts f (s :: rest))
      with (map (fun s' => s' :: rest) (f s)
            ++ map (fun r => s :: r) (pcuts f rest)) in Hq.
    apply in_app_or in Hq; destruct Hq as [Hq | Hq];
      apply in_map_iff in Hq; destruct Hq as [a [<- Ha]].
    + change (psize (a :: rest)) with (length a + psize rest).
      change (psize (s :: rest)) with (length s + psize rest).
      pose proof (Hf s a Ha); lia.
    + change (psize (s :: a)) with (length s + psize a).
      change (psize (s :: rest)) with (length s + psize rest).
      specialize (IH a Hf Ha); lia.
Qed.

Lemma pcuts_nil_of_zero :
  forall f p,
    (forall s s', In s' (f s) -> length s' < length s) ->
    psize p = 0 -> pcuts f p = [].
Proof.
  intros f p Hf Hz.
  destruct (pcuts f p) as [|x l] eqn:E; auto.
  exfalso.
  pose proof (pcuts_smaller f p x Hf) as Hlt.
  rewrite E in Hlt; specialize (Hlt (or_introl eq_refl)); lia.
Qed.

Lemma hbp_stable :
  forall N p f1 f2,
    psize p <= N -> psize p <= f1 -> psize p <= f2 ->
    hbp f1 p = hbp f2 p.
Proof.
  induction N as [|N IH]; intros p f1 f2 HN Hf1 Hf2.
  - assert (Hz : psize p = 0) by lia.
    pose proof (pcuts_nil_of_zero lcuts p lcuts_shorter Hz) as E1.
    pose proof (pcuts_nil_of_zero rcuts p rcuts_shorter Hz) as E2.
    destruct f1; destruct f2; simpl; rewrite ?E1, ?E2; reflexivity.
  - destruct f1 as [|f1]; destruct f2 as [|f2].
    + reflexivity.
    + assert (Hz : psize p = 0) by lia.
      pose proof (pcuts_nil_of_zero lcuts p lcuts_shorter Hz) as E1.
      pose proof (pcuts_nil_of_zero rcuts p rcuts_shorter Hz) as E2.
      simpl; rewrite E1, E2; reflexivity.
    + assert (Hz : psize p = 0) by lia.
      pose proof (pcuts_nil_of_zero lcuts p lcuts_shorter Hz) as E1.
      pose proof (pcuts_nil_of_zero rcuts p rcuts_shorter Hz) as E2.
      simpl; rewrite E1, E2; reflexivity.
    + simpl; f_equal; apply map_ext_in; intros q Hq.
      * pose proof (pcuts_smaller lcuts p q lcuts_shorter Hq).
        apply (IH q); lia.
      * pose proof (pcuts_smaller rcuts p q rcuts_shorter Hq).
        apply (IH q); lia.
Qed.

Definition HbP (p : position) : pgame := hbp (psize p) p.

Lemma hbp_HbP : forall f p, psize p <= f -> hbp f p = HbP p.
Proof.
  intros f p Hf; unfold HbP; apply (hbp_stable (psize p)); lia.
Qed.

Lemma HbP_eq :
  forall p, HbP p = PG (map HbP (pcuts lcuts p)) (map HbP (pcuts rcuts p)).
Proof.
  intros p; unfold HbP at 1.
  destruct (psize p) as [|f] eqn:Ep.
  - pose proof (pcuts_nil_of_zero lcuts p lcuts_shorter Ep) as E1.
    pose proof (pcuts_nil_of_zero rcuts p rcuts_shorter Ep) as E2.
    rewrite E1, E2; reflexivity.
  - simpl; f_equal; apply map_ext_in; intros q Hq.
    + pose proof (pcuts_smaller lcuts p q lcuts_shorter Hq).
      apply hbp_HbP; lia.
    + pose proof (pcuts_smaller rcuts p q rcuts_shorter Hq).
      apply hbp_HbP; lia.
Qed.

Lemma lopts_HbP : forall p, lopts (HbP p) = map HbP (pcuts lcuts p).
Proof. intros p; rewrite HbP_eq; reflexivity. Qed.

Lemma ropts_HbP : forall p, ropts (HbP p) = map HbP (pcuts rcuts p).
Proof. intros p; rewrite HbP_eq; reflexivity. Qed.

Lemma HbP_nil : HbP [] = zero.
Proof. reflexivity. Qed.

(** A position is the sum of its stalks. *)
Lemma HbP_cons :
  forall s rest, gequiv (HbP (s :: rest)) (padd (Hb s) (HbP rest)) = true.
Proof.
  assert (Haux : forall N s rest,
            length s + psize rest <= N ->
            gequiv (HbP (s :: rest)) (padd (Hb s) (HbP rest)) = true).
  { induction N as [|N IH]; intros s rest HN.
    - assert (Hs : s = []) by (apply length_zero_iff_nil; lia).
      assert (Hp : psize rest = 0) by lia.
      subst s.
      assert (Hz : psize ([] :: rest) = 0)
        by (change (psize ([] :: rest)) with (0 + psize rest); lia).
      pose proof (pcuts_nil_of_zero lcuts _ lcuts_shorter Hz) as E1.
      pose proof (pcuts_nil_of_zero rcuts _ rcuts_shorter Hz) as E2.
      pose proof (pcuts_nil_of_zero lcuts rest lcuts_shorter Hp) as E3.
      pose proof (pcuts_nil_of_zero rcuts rest rcuts_shorter Hp) as E4.
      rewrite Hb_nil, padd_zero_l.
      rewrite (HbP_eq ([] :: rest)), (HbP_eq rest), E1, E2, E3, E4.
      apply gequiv_refl.
    - apply gequiv_of_opts.
      + rewrite lopts_HbP, lopts_padd, lopts_Hb, lopts_HbP.
        change (pcuts lcuts (s :: rest))
          with (map (fun s' => s' :: rest) (lcuts s)
                ++ map (fun r => s :: r) (pcuts lcuts rest)).
        rewrite map_app, !map_map.
        cbv beta.
        apply opts_equiv_app_map; intros x Hx.
        * apply IH; pose proof (lcuts_shorter s x Hx); lia.
        * apply IH.
          pose proof (pcuts_smaller lcuts rest x lcuts_shorter Hx); lia.
      + rewrite ropts_HbP, ropts_padd, ropts_Hb, ropts_HbP.
        change (pcuts rcuts (s :: rest))
          with (map (fun s' => s' :: rest) (rcuts s)
                ++ map (fun r => s :: r) (pcuts rcuts rest)).
        rewrite map_app, !map_map.
        cbv beta.
        apply opts_equiv_app_map; intros x Hx.
        * apply IH; pose proof (rcuts_shorter s x Hx); lia.
        * apply IH.
          pose proof (pcuts_smaller rcuts rest x rcuts_shorter Hx); lia. }
  intros s rest; apply (Haux (length s + psize rest)); lia.
Qed.

Definition Hsum (p : position) : pgame :=
  fold_right (fun s acc => padd (Hb s) acc) zero p.

Theorem HbP_sum : forall p, gequiv (HbP p) (Hsum p) = true.
Proof.
  induction p as [|s rest IH].
  - apply gequiv_refl.
  - apply (gequiv_trans _ (padd (Hb s) (HbP rest))).
    + apply HbP_cons.
    + change (Hsum (s :: rest)) with (padd (Hb s) (Hsum rest)).
      apply gequiv_padd_l; auto.
Qed.

(** * Solved positions *)

Example hb_empty : Hb [] = zero.
Proof. reflexivity. Qed.

Example hb_one_blue : gequiv (Hb [Blue]) one = true.
Proof. vm_compute; reflexivity. Qed.

Example hb_one_red : gequiv (Hb [Red]) minus_one = true.
Proof. vm_compute; reflexivity. Qed.

Example hb_three_blue : gequiv (Hb (blues 3)) (num 3) = true.
Proof. vm_compute; reflexivity. Qed.

Example hb_half : gequiv (Hb [Blue; Red]) (half 1) = true.
Proof. vm_compute; reflexivity. Qed.

Example hb_quarter : gequiv (Hb [Blue; Red; Red]) (half 2) = true.
Proof. vm_compute; reflexivity. Qed.

(** Two halves make a whole. *)
Example hb_half_twice :
  gequiv (HbP [[Blue; Red]; [Blue; Red]]) one = true.
Proof. vm_compute; reflexivity. Qed.

(** A half against a whole red edge leaves Right ahead. *)
Example hb_half_minus_one :
  outc (HbP [[Blue; Red]; [Red]]) = Rwins.
Proof. vm_compute; reflexivity. Qed.
