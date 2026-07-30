(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Hackenbush on strings. Green edges move for either player; the green-free
    stalks are Blue-Red Hackenbush, whose values are the dyadic halves. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.Conway.

(** * Stalks *)

Inductive colour : Type := Blue | Red | Green.

(** The colours of a stalk's edges, ground edge first. *)
Definition stalk : Type := list colour.

(** Left deletes blue and green edges, Right red and green ones. *)
Definition is_lmove (s : stalk) (i : nat) : bool :=
  match nth_error s i with
  | Some Blue => true
  | Some Green => true
  | _ => false
  end.

Definition is_rmove (s : stalk) (i : nat) : bool :=
  match nth_error s i with
  | Some Red => true
  | Some Green => true
  | _ => false
  end.

(** * The stalk game over abstract move tests *)

(** The cut machinery does not depend on what an edge is or on which edges a
    player may take: it needs only the two move tests. Parameterising over them
    lets the same development serve the three-colour rules and the Blue-Red
    ones. *)

Section StalkGame.
  Context {E : Type}.
  Variable lmove rmove : list E -> nat -> bool.

  (** Cutting at a playable edge leaves the part below it. *)
  Definition cuts (test : list E -> nat -> bool) (s : list E) : list (list E) :=
    map (fun i => firstn i s) (filter (test s) (seq 0 (length s))).

  Lemma in_cuts :
    forall test s s',
      In s' (cuts test s) <->
      exists i, i < length s /\ test s i = true /\ s' = firstn i s.
  Proof.
    intros test s s'; unfold cuts; rewrite in_map_iff; split.
    - intros [i [<- Hi]].
      apply filter_In in Hi; destruct Hi as [Hi Hb].
      apply in_seq in Hi.
      exists i; repeat split; auto; lia.
    - intros [i [Hi [Hb ->]]].
      exists i; split; auto.
      apply filter_In; split; auto.
      apply in_seq; lia.
  Qed.

  Lemma cuts_shorter :
    forall test s s', In s' (cuts test s) -> length s' < length s.
  Proof.
    intros test s s' Hs; apply in_cuts in Hs.
    destruct Hs as [i [Hi [_ ->]]].
    rewrite length_firstn; lia.
  Qed.

  Fixpoint hbg (fuel : nat) (s : list E) : pgame :=
    match fuel with
    | 0 => PG [] []
    | S f => PG (map (hbg f) (cuts lmove s)) (map (hbg f) (cuts rmove s))
    end.

  Lemma hbg_stable :
    forall N s f1 f2,
      length s <= N -> length s <= f1 -> length s <= f2 ->
      hbg f1 s = hbg f2 s.
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
          -- pose proof (cuts_shorter lmove s m Hm); apply (IH m); lia.
          -- pose proof (cuts_shorter rmove s m Hm); apply (IH m); lia.
  Qed.

  Definition HbG (s : list E) : pgame := hbg (length s) s.

  Lemma hbg_HbG : forall f s, length s <= f -> hbg f s = HbG s.
  Proof.
    intros f s Hf; unfold HbG; apply (hbg_stable (length s)); lia.
  Qed.

  Lemma HbG_eq :
    forall s, HbG s = PG (map HbG (cuts lmove s)) (map HbG (cuts rmove s)).
  Proof.
    intros s; unfold HbG at 1.
    destruct (length s) as [|f] eqn:Es.
    - assert (Hs : s = []) by (apply length_zero_iff_nil; auto).
      subst s; reflexivity.
    - simpl; f_equal; apply map_ext_in; intros m Hm.
      + pose proof (cuts_shorter lmove s m Hm); apply hbg_HbG; lia.
      + pose proof (cuts_shorter rmove s m Hm); apply hbg_HbG; lia.
  Qed.

  Lemma HbG_nil : HbG [] = zero.
  Proof. reflexivity. Qed.
End StalkGame.

(** * The three-colour rules *)

Definition lcuts (s : stalk) : list stalk := cuts is_lmove s.

Definition rcuts (s : stalk) : list stalk := cuts is_rmove s.

Lemma in_lcuts :
  forall s s',
    In s' (lcuts s) <->
    exists i, i < length s /\ is_lmove s i = true /\ s' = firstn i s.
Proof.
  intros s s'; apply in_cuts.
Qed.

Lemma in_rcuts :
  forall s s',
    In s' (rcuts s) <->
    exists i, i < length s /\ is_rmove s i = true /\ s' = firstn i s.
Proof.
  intros s s'; apply in_cuts.
Qed.

Lemma lcuts_shorter :
  forall s s', In s' (lcuts s) -> length s' < length s.
Proof.
  intros s s'; apply (cuts_shorter is_lmove).
Qed.

Lemma rcuts_shorter :
  forall s s', In s' (rcuts s) -> length s' < length s.
Proof.
  intros s s'; apply (cuts_shorter is_rmove).
Qed.

(** * The game of a stalk *)

Definition hb : nat -> stalk -> pgame := hbg is_lmove is_rmove.

Lemma hb_stable :
  forall N s f1 f2,
    length s <= N -> length s <= f1 -> length s <= f2 ->
    hb f1 s = hb f2 s.
Proof. intros N s f1 f2; apply (hbg_stable is_lmove is_rmove N). Qed.

Definition Hb : stalk -> pgame := HbG is_lmove is_rmove.

Lemma hb_Hb : forall f s, length s <= f -> hb f s = Hb s.
Proof. intros f s; apply (hbg_HbG is_lmove is_rmove). Qed.

Lemma Hb_eq :
  forall s, Hb s = PG (map Hb (lcuts s)) (map Hb (rcuts s)).
Proof. intros s; apply (HbG_eq is_lmove is_rmove). Qed.

Lemma lopts_Hb : forall s, lopts (Hb s) = map Hb (lcuts s).
Proof. intros s; rewrite Hb_eq; reflexivity. Qed.

Lemma ropts_Hb : forall s, ropts (Hb s) = map Hb (rcuts s).
Proof. intros s; rewrite Hb_eq; reflexivity. Qed.

Lemma Hb_nil : Hb [] = zero.
Proof. reflexivity. Qed.

(** * Colour symmetry *)

(** Exchanging the players exchanges blue with red and fixes green. *)
Definition swapc (c : colour) : colour :=
  match c with Blue => Red | Red => Blue | Green => Green end.

Definition swaps (s : stalk) : stalk := map swapc s.

Lemma swapc_swapc : forall c, swapc (swapc c) = c.
Proof. intros []; reflexivity. Qed.

Lemma swaps_swaps : forall s, swaps (swaps s) = s.
Proof.
  intros s; unfold swaps; rewrite map_map.
  rewrite (map_ext_in _ (fun c => c) s), map_id; auto.
  intros a _; apply swapc_swapc.
Qed.

Lemma is_lmove_swaps : forall s i, is_lmove (swaps s) i = is_rmove s i.
Proof.
  intros s i; unfold is_lmove, is_rmove, swaps.
  rewrite nth_error_map.
  destruct (nth_error s i) as [[| |]|]; reflexivity.
Qed.

Lemma is_rmove_swaps : forall s i, is_rmove (swaps s) i = is_lmove s i.
Proof.
  intros s i; unfold is_lmove, is_rmove, swaps.
  rewrite nth_error_map.
  destruct (nth_error s i) as [[| |]|]; reflexivity.
Qed.

Lemma length_swaps : forall s, length (swaps s) = length s.
Proof. intros s; unfold swaps; apply length_map. Qed.

Lemma lcuts_swaps : forall s, lcuts (swaps s) = map swaps (rcuts s).
Proof.
  intros s; unfold lcuts, rcuts, cuts.
  rewrite length_swaps, map_map.
  rewrite (filter_ext (is_lmove (swaps s)) (is_rmove s))
    by (intros i; apply is_lmove_swaps).
  apply map_ext_in; intros i _.
  unfold swaps; rewrite firstn_map; reflexivity.
Qed.

Lemma rcuts_swaps : forall s, rcuts (swaps s) = map swaps (lcuts s).
Proof.
  intros s; unfold lcuts, rcuts, cuts.
  rewrite length_swaps, map_map.
  rewrite (filter_ext (is_rmove (swaps s)) (is_lmove s))
    by (intros i; apply is_rmove_swaps).
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

Lemma nil_in_lcuts_head :
  forall c t, is_lmove (c :: t) 0 = true -> In [] (lcuts (c :: t)).
Proof.
  intros c t Hc; apply in_lcuts.
  exists 0; repeat split; auto.
  simpl; lia.
Qed.

Lemma nil_in_rcuts_head :
  forall c t, is_rmove (c :: t) 0 = true -> In [] (rcuts (c :: t)).
Proof.
  intros c t Hc; apply in_rcuts.
  exists 0; repeat split; auto.
  simpl; lia.
Qed.

(** Every cut above the ground edge leaves the ground edge in place. *)
Lemma rcuts_blue_head :
  forall t s', In s' (rcuts (Blue :: t)) -> exists t', s' = Blue :: t'.
Proof.
  intros t s' Hs; apply in_rcuts in Hs.
  destruct Hs as [i [Hi [Hr ->]]].
  destruct i as [|j].
  - unfold is_rmove in Hr; simpl in Hr; discriminate.
  - exists (firstn j t); reflexivity.
Qed.

(** A blue ground edge makes the stalk positive. *)
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
          [reflexivity | apply nil_in_lcuts_head; reflexivity]. }
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

(** A green ground edge makes the stalk a first-player win. *)
Theorem hb_ground_green : forall t, gfuzzy (Hb (Green :: t)) zero = true.
Proof.
  intros t; unfold gfuzzy.
  apply andb_true_iff; split; apply negb_true_iff.
  - apply gle_lopt.
    rewrite lopts_Hb.
    change zero with (Hb []).
    apply in_map_iff; eexists; split;
      [reflexivity | apply nil_in_lcuts_head; reflexivity].
  - apply gle_ropt.
    rewrite ropts_Hb.
    change zero with (Hb []).
    apply in_map_iff; eexists; split;
      [reflexivity | apply nil_in_rcuts_head; reflexivity].
Qed.

(** The trichotomy: the ground edge decides the sign. *)
Theorem hb_ground :
  forall c t,
    match c with
    | Blue => glt zero (Hb (c :: t))
    | Red => glt (Hb (c :: t)) zero
    | Green => gfuzzy (Hb (c :: t)) zero = true
    end.
Proof.
  intros [| |] t.
  - apply hb_ground_blue.
  - apply hb_ground_red.
  - apply hb_ground_green.
Qed.

(** * Integers *)

Definition blues (n : nat) : stalk := repeat Blue n.

Lemma is_lmove_blues : forall n i, i < n -> is_lmove (blues n) i = true.
Proof.
  intros n i Hi; unfold is_lmove, blues.
  rewrite nth_error_repeat by auto; reflexivity.
Qed.

Lemma is_rmove_blues : forall n i, is_rmove (blues n) i = false.
Proof.
  intros n i; unfold is_rmove, blues.
  destruct (nth_error (repeat Blue n) i) as [c|] eqn:E; auto.
  apply nth_error_In in E.
  apply repeat_spec in E; subst; reflexivity.
Qed.

Lemma firstn_blues : forall n i, i <= n -> firstn i (blues n) = blues i.
Proof. intros n i Hi; unfold blues; apply firstn_repeat_le; auto. Qed.

Lemma lcuts_blues : forall n, lcuts (blues n) = map blues (seq 0 n).
Proof.
  intros n; unfold lcuts, cuts.
  replace (length (blues n)) with n by (unfold blues; rewrite repeat_length; auto).
  rewrite (filter_all (is_lmove (blues n)) (seq 0 n)).
  - apply map_ext_in; intros i Hi.
    apply in_seq in Hi; apply firstn_blues; lia.
  - intros i Hi; apply in_seq in Hi; apply is_lmove_blues; lia.
Qed.

Lemma rcuts_blues : forall n, rcuts (blues n) = [].
Proof.
  intros n; unfold rcuts, cuts.
  rewrite (filter_none (is_rmove (blues n)) (seq 0 (length (blues n)))).
  - reflexivity.
  - intros i _; apply is_rmove_blues.
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

(** * Nimbers *)

Definition greens (n : nat) : stalk := repeat Green n.

Lemma is_lmove_greens : forall n i, i < n -> is_lmove (greens n) i = true.
Proof.
  intros n i Hi; unfold is_lmove, greens.
  rewrite nth_error_repeat by auto; reflexivity.
Qed.

Lemma is_rmove_greens : forall n i, i < n -> is_rmove (greens n) i = true.
Proof.
  intros n i Hi; unfold is_rmove, greens.
  rewrite nth_error_repeat by auto; reflexivity.
Qed.

Lemma firstn_greens : forall n i, i <= n -> firstn i (greens n) = greens i.
Proof. intros n i Hi; unfold greens; apply firstn_repeat_le; auto. Qed.

Lemma lcuts_greens : forall n, lcuts (greens n) = map greens (seq 0 n).
Proof.
  intros n; unfold lcuts, cuts.
  replace (length (greens n)) with n
    by (unfold greens; rewrite repeat_length; auto).
  rewrite (filter_all (is_lmove (greens n)) (seq 0 n)).
  - apply map_ext_in; intros i Hi.
    apply in_seq in Hi; apply firstn_greens; lia.
  - intros i Hi; apply in_seq in Hi; apply is_lmove_greens; lia.
Qed.

Lemma rcuts_greens : forall n, rcuts (greens n) = map greens (seq 0 n).
Proof.
  intros n; unfold rcuts, cuts.
  replace (length (greens n)) with n
    by (unfold greens; rewrite repeat_length; auto).
  rewrite (filter_all (is_rmove (greens n)) (seq 0 n)).
  - apply map_ext_in; intros i Hi.
    apply in_seq in Hi; apply firstn_greens; lia.
  - intros i Hi; apply in_seq in Hi; apply is_rmove_greens; lia.
Qed.

Lemma nimber_list_map : forall n, nimber_list n = map nimber (seq 0 n).
Proof.
  induction n as [|k IH]; auto.
  change (nimber_list (S k))
    with (nimber_list k ++ [PG (nimber_list k) (nimber_list k)]).
  rewrite seq_S, map_app.
  replace (0 + k) with k by lia.
  change (map nimber [k]) with [nimber k].
  change (nimber k) with (PG (nimber_list k) (nimber_list k)).
  rewrite IH; reflexivity.
Qed.

(** An all-green stalk of [n] edges is the nimber [n]. *)
Theorem hb_greens : forall n, gequiv (Hb (greens n)) (nimber n) = true.
Proof.
  assert (Haux : forall N n, n <= N ->
            gequiv (Hb (greens n)) (nimber n) = true).
  { induction N as [|N IH]; intros n HN.
    - assert (n = 0) by lia; subst; apply gequiv_refl.
    - assert (Hl : lopts (Hb (greens n))
                   = map (fun i => Hb (greens i)) (seq 0 n)).
      { rewrite lopts_Hb, lcuts_greens, map_map; reflexivity. }
      assert (Hrr : ropts (Hb (greens n))
                    = map (fun i => Hb (greens i)) (seq 0 n)).
      { rewrite ropts_Hb, rcuts_greens, map_map; reflexivity. }
      assert (Hln : lopts (nimber n) = map nimber (seq 0 n)).
      { change (lopts (nimber n)) with (nimber_list n).
        apply nimber_list_map. }
      assert (Hrn : ropts (nimber n) = map nimber (seq 0 n)).
      { change (ropts (nimber n)) with (nimber_list n).
        apply nimber_list_map. }
      apply gequiv_of_opts.
      + rewrite Hl, Hln.
        apply opts_equiv_map; intros i Hi.
        apply in_seq in Hi; apply IH; lia.
      + rewrite Hrr, Hrn.
        apply opts_equiv_map; intros i Hi.
        apply in_seq in Hi; apply IH; lia. }
  intros n; apply (Haux n); lia.
Qed.

Lemma swaps_greens : forall n, swaps (greens n) = greens n.
Proof.
  intros n; unfold swaps, greens.
  induction n as [|k IH]; auto.
  simpl repeat; simpl map; f_equal; exact IH.
Qed.

(** A green stalk is impartial, so it is its own negative. *)
Theorem hb_greens_self_neg :
  forall n, Hb (greens n) = pneg (Hb (greens n)).
Proof.
  intros n.
  pose proof (Hb_swap (greens n)) as H.
  rewrite swaps_greens in H.
  exact H.
Qed.

Corollary hb_greens_double :
  forall n, gequiv (padd (Hb (greens n)) (Hb (greens n))) zero = true.
Proof.
  intros n.
  pose proof (padd_inv (Hb (greens n))) as H.
  rewrite <- (hb_greens_self_neg n) in H.
  exact H.
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
    | Green :: _ => Firstwins
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
    + apply (proj2 (proj1 (proj2 (outc_spec (Hb (Green :: t)))))).
      exact (hb_ground_green t).
Qed.

(** A stalk is fuzzy exactly when its ground edge is green. *)
Corollary hb_fuzzy_iff_green :
  forall s, outc (Hb s) = Firstwins <-> exists t, s = Green :: t.
Proof.
  intros s; rewrite hb_outcome; split.
  - destruct s as [|[| |] t]; try discriminate.
    intros _; exists t; reflexivity.
  - intros [t ->]; reflexivity.
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

(** A single green edge is star. *)
Example hb_one_green : gequiv (Hb [Green]) star = true.
Proof. vm_compute; reflexivity. Qed.

Example hb_two_green : gequiv (Hb (greens 2)) (nimber 2) = true.
Proof. vm_compute; reflexivity. Qed.

(** Two green edges standing apart cancel, as two equal Nim heaps do. *)
Example hb_green_pair : gequiv (HbP [[Green]; [Green]]) zero = true.
Proof. vm_compute; reflexivity. Qed.

Example hb_three_blue : gequiv (Hb (blues 3)) (num 3) = true.
Proof. vm_compute; reflexivity. Qed.

(** A green ground edge decides the outcome whatever stands above it. *)
Example hb_green_under_blue : outc (Hb [Green; Blue]) = Firstwins.
Proof. vm_compute; reflexivity. Qed.

Example hb_blue_under_green : outc (Hb [Blue; Green]) = Lwins.
Proof. vm_compute; reflexivity. Qed.

(** A blue edge carrying a green one is a whole move plus a star. *)
Example hb_blue_green_value :
  gequiv (Hb [Blue; Green]) (padd one star) = true.
Proof. vm_compute; reflexivity. Qed.

(** * Blue-Red Hackenbush *)

(** A stalk with no green edge is a Blue-Red Hackenbush position. On those the
    game is a number: Left and Right never share a move, so no green-free
    stalk is a first-player win, and a blue edge under [k] red ones is the
    dyadic [half k]. *)

Definition green_free (s : stalk) : Prop := ~ In Green s.

(** ** The Blue-Red rule set as a second instance *)

(** Under the Blue-Red rules each player takes only their own colour, so a
    green edge is playable by neither. *)
Definition is_lmove_br (s : stalk) (i : nat) : bool :=
  match nth_error s i with Some Blue => true | _ => false end.

Definition is_rmove_br (s : stalk) (i : nat) : bool :=
  match nth_error s i with Some Red => true | _ => false end.

Definition lcuts_br (s : stalk) : list stalk := cuts is_lmove_br s.
Definition rcuts_br (s : stalk) : list stalk := cuts is_rmove_br s.
Definition HbBR : stalk -> pgame := HbG is_lmove_br is_rmove_br.

Lemma HbBR_eq :
  forall s, HbBR s = PG (map HbBR (lcuts_br s)) (map HbBR (rcuts_br s)).
Proof. intros s; apply (HbG_eq is_lmove_br is_rmove_br). Qed.

Lemma green_free_firstn :
  forall s i, green_free s -> green_free (firstn i s).
Proof.
  intros s i Hs Hin; apply Hs.
  rewrite <- (firstn_skipn i s); apply in_or_app; left; exact Hin.
Qed.

(** On a green-free stalk the two rule sets agree edge by edge. *)
Lemma is_lmove_br_green_free :
  forall s i, green_free s -> is_lmove_br s i = is_lmove s i.
Proof.
  intros s i Hs; unfold is_lmove_br, is_lmove.
  destruct (nth_error s i) as [c|] eqn:E; auto.
  destruct c; auto.
  exfalso; apply Hs, (nth_error_In s i); exact E.
Qed.

Lemma is_rmove_br_green_free :
  forall s i, green_free s -> is_rmove_br s i = is_rmove s i.
Proof.
  intros s i Hs; unfold is_rmove_br, is_rmove.
  destruct (nth_error s i) as [c|] eqn:E; auto.
  destruct c; auto.
  exfalso; apply Hs, (nth_error_In s i); exact E.
Qed.

Lemma lcuts_br_green_free :
  forall s, green_free s -> lcuts_br s = lcuts s.
Proof.
  intros s Hs; unfold lcuts_br, lcuts, cuts.
  f_equal; apply filter_ext_in; intros i _.
  apply is_lmove_br_green_free; exact Hs.
Qed.

Lemma rcuts_br_green_free :
  forall s, green_free s -> rcuts_br s = rcuts s.
Proof.
  intros s Hs; unfold rcuts_br, rcuts, cuts.
  f_equal; apply filter_ext_in; intros i _.
  apply is_rmove_br_green_free; exact Hs.
Qed.

(** The Blue-Red game and the three-colour game are the same game on a stalk
    with no green edge: the two instances of the parameterised development
    agree wherever their rules do. *)
Theorem HbBR_green_free : forall s, green_free s -> HbBR s = Hb s.
Proof.
  assert (Haux : forall N s, length s <= N -> green_free s -> HbBR s = Hb s).
  { induction N as [|N IH]; intros s HN Hs.
    - assert (Hnil : s = []) by (apply length_zero_iff_nil; lia).
      subst s; reflexivity.
    - rewrite HbBR_eq, Hb_eq.
      rewrite (lcuts_br_green_free s Hs), (rcuts_br_green_free s Hs).
      f_equal; apply map_ext_in; intros m Hm.
      + apply IH.
        * pose proof (lcuts_shorter s m Hm); lia.
        * apply in_lcuts in Hm; destruct Hm as [i [_ [_ ->]]].
          apply green_free_firstn; exact Hs.
      + apply IH.
        * pose proof (rcuts_shorter s m Hm); lia.
        * apply in_rcuts in Hm; destruct Hm as [i [_ [_ ->]]].
          apply green_free_firstn; exact Hs. }
  intros s; apply (Haux (length s)); lia.
Qed.

(** Blue-Red Hackenbush has no fuzzy stalk. *)
Theorem hb_never_first :
  forall s, green_free s -> outc (Hb s) <> Firstwins.
Proof.
  intros s Hgf Hfz.
  apply hb_fuzzy_iff_green in Hfz.
  destruct Hfz as [t ->].
  apply Hgf; left; reflexivity.
Qed.

(** A blue ground edge under [k] red edges. *)
Definition blue_reds (k : nat) : stalk := Blue :: repeat Red k.

Lemma green_free_blue_reds : forall k, green_free (blue_reds k).
Proof.
  intros k Hin; unfold blue_reds in Hin.
  destruct Hin as [Hbad | Hin]; [discriminate|].
  apply repeat_spec in Hin; discriminate.
Qed.

Lemma is_lmove_blue_reds :
  forall k i, is_lmove (blue_reds k) i = true -> i = 0.
Proof.
  intros k i H; destruct i as [|j]; auto.
  exfalso; unfold is_lmove, blue_reds in H; simpl in H.
  destruct (nth_error (repeat Red k) j) as [c|] eqn:E; [|discriminate].
  apply nth_error_In, repeat_spec in E; subst; discriminate.
Qed.

Lemma is_rmove_blue_reds :
  forall k i, i < k -> is_rmove (blue_reds k) (S i) = true.
Proof.
  intros k i Hi; unfold is_rmove, blue_reds; simpl.
  rewrite nth_error_repeat by exact Hi; reflexivity.
Qed.

Lemma lcuts_blue_reds : forall k, lcuts (blue_reds k) = [[]].
Proof.
  intros k; unfold lcuts, cuts, blue_reds.
  replace (length (Blue :: repeat Red k)) with (1 + k)
    by (simpl; rewrite repeat_length; reflexivity).
  rewrite seq_app, filter_app.
  change (seq 0 1) with [0].
  change (filter (is_lmove (Blue :: repeat Red k)) [0]) with [0].
  rewrite (filter_none (is_lmove (Blue :: repeat Red k)) (seq (0 + 1) k)).
  - reflexivity.
  - intros i Hi; apply in_seq in Hi.
    destruct (is_lmove (Blue :: repeat Red k) i) eqn:E; auto.
    apply is_lmove_blue_reds in E; lia.
Qed.

Lemma rcuts_blue_reds :
  forall k, rcuts (blue_reds (S k)) = map blue_reds (seq 0 (S k)).
Proof.
  intros k; unfold rcuts, cuts, blue_reds.
  replace (length (Blue :: repeat Red (S k))) with (1 + S k)
    by (simpl; rewrite repeat_length; reflexivity).
  rewrite seq_app, filter_app.
  change (seq 0 1) with [0].
  change (filter (is_rmove (Blue :: repeat Red (S k))) [0]) with (@nil nat).
  rewrite app_nil_l.
  replace (0 + 1) with 1 by reflexivity.
  rewrite (filter_all (is_rmove (Blue :: repeat Red (S k))) (seq 1 (S k))).
  - rewrite <- seq_shift, map_map.
    apply map_ext_in; intros i Hi.
    apply in_seq in Hi.
    change (firstn (S i) (Blue :: repeat Red (S k)))
      with (Blue :: firstn i (repeat Red (S k))).
    f_equal.
    apply firstn_repeat_le; lia.
  - intros i Hi; apply in_seq in Hi.
    destruct i as [|j]; [lia|].
    apply is_rmove_blue_reds; lia.
Qed.

(** A blue edge under [k] red edges is the dyadic [half k]. *)
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
          apply in_seq in Hi; destruct Hi as [_ Hi].
          apply (gle_gequiv_l (half j)); [apply gequiv_sym, IH; lia|].
          apply (gle_gequiv_r _ (half i)).
          - apply gequiv_sym, IH; lia.
          - apply half_le; lia. }
        apply (gequiv_trans _ (PG (lopts (Hb (blue_reds (S j))))
                                  [Hb (blue_reds j)])).
        * apply collapse_ropts; auto.
        * rewrite Hl.
          change (half (S j)) with (PG [zero] [half j]).
          apply gequiv_of_opts.
          -- change (lopts (PG [zero] [Hb (blue_reds j)])) with [zero].
             change (lopts (PG [zero] [half j])) with [zero].
             split; intros x [<- | []]; exists zero;
               (split; [left; reflexivity | apply gequiv_refl]).
          -- change (ropts (PG [zero] [Hb (blue_reds j)]))
               with [Hb (blue_reds j)].
             change (ropts (PG [zero] [half j])) with [half j].
             split; intros x [<- | []].
             ++ exists (half j); split; [left; reflexivity | apply IH; lia].
             ++ exists (Hb (blue_reds j)); split;
                  [left; reflexivity | apply IH; lia]. } 
  intros k; apply (Haux k); lia.
Qed.

(** The blue-red stalks realise every dyadic half. *)
Example hb_half : gequiv (Hb [Blue; Red]) (half 1) = true.
Proof. vm_compute; reflexivity. Qed.

Example hb_quarter : gequiv (Hb [Blue; Red; Red]) (half 2) = true.
Proof. vm_compute; reflexivity. Qed.

(** Two quarters make a half. *)
Example hb_half_twice :
  gequiv (padd (Hb [Blue; Red; Red]) (Hb [Blue; Red; Red])) (half 1) = true.
Proof. vm_compute; reflexivity. Qed.
