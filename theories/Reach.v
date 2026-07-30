(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Board cells, guarded chains, and the saturation procedure that decides
    chain reachability. Shared by every board game in the library. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.

Import ListNotations.

Require Import GameTrees.Helpers.

(** * Cells *)

(** Board positions for both the Hex board and the triangular Y board. *)
Definition cell : Type := (nat * nat)%type.

Definition cell_eq_dec : forall p q : cell, {p = q} + {p <> q}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition cell_eqb (p q : cell) : bool :=
  if cell_eq_dec p q then true else false.

Lemma cell_eqb_true_iff : forall p q, cell_eqb p q = true <-> p = q.
Proof.
  intros p q; unfold cell_eqb; destruct (cell_eq_dec p q); split; congruence.
Qed.

(** * Guarded chains *)

Section Chain.
  Context (G : cell -> Prop) (A : cell -> cell -> Prop).

  (** Reflexive-transitive [A]-chains whose cells all satisfy the guard [G]. *)
  Inductive chain : cell -> cell -> Prop :=
  | chain_refl : forall p, G p -> chain p p
  | chain_step : forall p q r, G p -> A p q -> chain q r -> chain p r.

  Lemma chain_good_l : forall p q, chain p q -> G p.
  Proof. intros p q ch; destruct ch; auto. Qed.

  Lemma chain_good_r : forall p q, chain p q -> G q.
  Proof. intros p q ch; induction ch; auto. Qed.

  Lemma chain_trans : forall p q r, chain p q -> chain q r -> chain p r.
  Proof. intros p q r ch1 ch2; induction ch1; eauto using chain_step. Qed.

  Lemma chain_snoc : forall p q r, chain p q -> A q r -> G r -> chain p r.
  Proof.
    intros p q r ch HA HG; induction ch.
    - eapply chain_step; eauto using chain_refl.
    - eauto using chain_step.
  Qed.
End Chain.

Lemma chain_impl :
  forall (G G' : cell -> Prop) (A A' : cell -> cell -> Prop) p q,
    (forall x, G x -> G' x) ->
    (forall x y, A x y -> A' x y) ->
    chain G A p q -> chain G' A' p q.
Proof.
  intros G G' A A' p q HG HA ch; induction ch;
    eauto using chain_refl, chain_step.
Qed.

Lemma chain_map :
  forall (G G' : cell -> Prop) (A A' : cell -> cell -> Prop)
         (f : cell -> cell) p q,
    (forall x, G x -> G' (f x)) ->
    (forall x y, A x y -> A' (f x) (f y)) ->
    chain G A p q -> chain G' A' (f p) (f q).
Proof.
  intros G G' A A' f p q HG HA ch; induction ch;
    eauto using chain_refl, chain_step.
Qed.

Lemma chain_cases :
  forall (G : cell -> Prop) (A : cell -> cell -> Prop) p q,
    chain G A p q ->
    (p = q /\ G p) \/ (exists r, G p /\ A p r /\ chain G A r q).
Proof.
  intros G A p q ch; destruct ch as [p HG | p q0 r HG HA ch'];
    [left; auto | right; exists q0; auto].
Qed.

(** A chain moving [f] by at most one per step hits every intermediate value. *)
Lemma chain_proj_intermediate :
  forall (f : cell -> nat) (G : cell -> Prop) (A : cell -> cell -> Prop),
    (forall x y, A x y -> f y <= S (f x) /\ f x <= S (f y)) ->
    forall p q k,
      chain G A p q ->
      (f p <= k <= f q) \/ (f q <= k <= f p) ->
      exists x, f x = k /\ chain G A p x.
Proof.
  intros f G A Hstep p q k ch.
  induction ch as [p HG | p r q HG HA ch IH]; intros Hk.
  - exists p; split; [lia | apply chain_refl; auto].
  - destruct (Nat.eq_dec (f p) k) as [Heq | Hne].
    + exists p; split; [exact Heq | apply chain_refl; auto].
    + destruct (Hstep p r HA) as [H1 H2].
      destruct IH as [x [Hx Hch]]; [lia|].
      exists x; split; auto.
      eapply chain_step; eauto.
Qed.

(** A chain whose endpoints disagree on a Boolean test has a crossing pair. *)
Lemma chain_crossing_bool :
  forall (G : cell -> Prop) (A : cell -> cell -> Prop) (Pb : cell -> bool)
         p q,
    chain G A p q -> Pb p = true -> Pb q = false ->
    exists u v,
      A u v /\ chain G A p u /\ chain G A v q /\
      Pb u = true /\ Pb v = false.
Proof.
  intros G A Pb p q ch; induction ch as [p HG | p r q HG HA ch IH];
    intros Hp Hq.
  - congruence.
  - destruct (Pb r) eqn:Er.
    + destruct (IH eq_refl Hq) as [u [v (HAuv & Hpu & Hvq & Hu & Hv)]].
      exists u, v; repeat split; auto.
      eapply chain_step; eauto.
    + exists p, r; repeat split; auto.
      apply chain_refl; auto.
Qed.

(** * Saturation-based reachability decision procedure *)

Definition memb (p : cell) (s : list cell) : bool := existsb (cell_eqb p) s.

Lemma memb_true_iff : forall p s, memb p s = true <-> In p s.
Proof.
  intros p s; unfold memb; rewrite existsb_exists; split.
  - intros [x [Hin Hx]]; apply cell_eqb_true_iff in Hx; subst; auto.
  - intros Hin; exists p; split; auto; apply cell_eqb_true_iff; auto.
Qed.

Lemma memb_false_iff : forall p s, memb p s = false <-> ~ In p s.
Proof.
  intros p s; split.
  - intros Hm Hin; apply memb_true_iff in Hin; congruence.
  - intros Hn; destruct (memb p s) eqn:E; auto.
    apply memb_true_iff in E; contradiction.
Qed.

Section Saturation.
  Context (U : list cell) (goodb : cell -> bool) (adjb : cell -> cell -> bool).

  Definition Gb (p : cell) : Prop := goodb p = true.
  Definition Ab (p q : cell) : Prop := adjb p q = true.

    (** Add every good, absent cell adjacent to [s]. *)
  Definition expand (s : list cell) : list cell :=
    s ++ filter
           (fun p => goodb p && negb (memb p s) && existsb (fun q => adjb q p) s)
           U.

  Fixpoint iterate (fuel : nat) (s : list cell) : list cell :=
    match fuel with O => s | S f => iterate f (expand s) end.

  (** All cells chain-reachable from [seeds]; [length U] rounds saturate. *)
  Definition reach_from (seeds : list cell) : list cell :=
    iterate (length U) seeds.

  Lemma expand_incl : forall s, incl s (expand s).
  Proof. intros s p Hp; apply in_or_app; auto. Qed.

  Lemma expand_incl_U : forall s, incl s U -> incl (expand s) U.
  Proof.
    intros s Hs p Hp; apply in_app_or in Hp; destruct Hp as [Hp | Hp]; auto.
    apply filter_In in Hp; tauto.
  Qed.

  Lemma expand_nodup : forall s, NoDup U -> NoDup s -> NoDup (expand s).
  Proof.
    intros s HU Hs; apply NoDup_app_disj; auto.
    - apply NoDup_filter; auto.
    - intros x Hx Hf; apply filter_In in Hf; destruct Hf as [_ Hf].
      apply andb_true_iff in Hf; destruct Hf as [Hf _].
      apply andb_true_iff in Hf; destruct Hf as [_ Hf].
      apply negb_true_iff in Hf; apply memb_false_iff in Hf; auto.
  Qed.

  Lemma expand_of_length_eq :
    forall s, length (expand s) = length s -> expand s = s.
  Proof.
    intros s Hl; unfold expand in *.
    rewrite length_app in Hl.
    assert (Hz : length (filter
      (fun p => goodb p && negb (memb p s) && existsb (fun q => adjb q p) s)
      U) = 0) by lia.
    apply length_zero_iff_nil in Hz; rewrite Hz; apply app_nil_r.
  Qed.

  Lemma iterate_fixed :
    forall fuel s, expand s = s -> iterate fuel s = s.
  Proof.
    induction fuel as [|f IH]; intros s Hfix; simpl; auto.
    rewrite Hfix; auto.
  Qed.

  Lemma iterate_incl : forall fuel s, incl s (iterate fuel s).
  Proof.
    induction fuel as [|f IH]; intros s; simpl.
    - apply incl_refl.
    - eapply incl_tran; [apply expand_incl | apply IH].
  Qed.

  Lemma iterate_incl_U :
    forall fuel s, incl s U -> incl (iterate fuel s) U.
  Proof.
    induction fuel as [|f IH]; intros s Hs; simpl; auto.
    apply IH, expand_incl_U; auto.
  Qed.

  Lemma fix_reached :
    forall fuel s,
      NoDup U -> NoDup s -> incl s U ->
      length U <= length s + fuel ->
      expand (iterate fuel s) = iterate fuel s.
  Proof.
    induction fuel as [|f IH]; intros s HU Hs HsU Hlen; simpl.
    - assert (HUs : incl U s).
      { apply NoDup_length_incl; auto; lia. }
      unfold expand.
      rewrite (filter_none _ U); [apply app_nil_r|].
      intros x Hx.
      assert (Hxs : In x s) by (apply HUs; auto).
      apply memb_true_iff in Hxs.
      rewrite Hxs; simpl.
      rewrite andb_false_r; auto.
    - destruct (list_eq_dec cell_eq_dec (expand s) s) as [Heq | Hne].
      + rewrite Heq, (iterate_fixed f s Heq); auto.
      + assert (Hgrow : S (length s) <= length (expand s)).
        { unfold expand in *; rewrite length_app.
          destruct (filter _ U) eqn:Ef.
          - exfalso; apply Hne; rewrite app_nil_r; auto.
          - simpl; lia. }
        apply IH.
        * auto.
        * apply expand_nodup; auto.
        * apply expand_incl_U; auto.
        * lia.
  Qed.

  Lemma reach_from_fixed :
    forall seeds,
      NoDup U -> NoDup seeds -> incl seeds U ->
      expand (reach_from seeds) = reach_from seeds.
  Proof.
    intros seeds HU Hs HsU; unfold reach_from.
    apply fix_reached; auto; lia.
  Qed.

  Lemma expand_sound :
    forall seeds s,
      (forall p, In p s -> exists a, In a seeds /\ chain Gb Ab a p) ->
      forall p, In p (expand s) -> exists a, In a seeds /\ chain Gb Ab a p.
  Proof.
    intros seeds s Hs p Hp; apply in_app_or in Hp; destruct Hp as [Hp | Hp]; auto.
    apply filter_In in Hp; destruct Hp as [_ Hp].
    apply andb_true_iff in Hp; destruct Hp as [Hp Hex].
    apply andb_true_iff in Hp; destruct Hp as [Hgood _].
    apply existsb_exists in Hex; destruct Hex as [q [Hq Hadj]].
    destruct (Hs q Hq) as [a [Ha Hch]].
    exists a; split; auto.
    eapply chain_snoc; eauto.
  Qed.

  Lemma iterate_sound :
    forall seeds fuel s,
      (forall p, In p s -> exists a, In a seeds /\ chain Gb Ab a p) ->
      forall p, In p (iterate fuel s) ->
      exists a, In a seeds /\ chain Gb Ab a p.
  Proof.
    intros seeds; induction fuel as [|f IH]; intros s Hs p Hp; simpl in Hp; auto.
    eapply IH; [|exact Hp].
    apply expand_sound; auto.
  Qed.

  Lemma reach_from_sound :
    forall seeds,
      (forall a, In a seeds -> Gb a) ->
      forall p, In p (reach_from seeds) ->
      exists a, In a seeds /\ chain Gb Ab a p.
  Proof.
    intros seeds Hg p Hp; eapply iterate_sound; [|exact Hp].
    intros q Hq; exists q; split; auto.
    apply chain_refl; auto.
  Qed.

  Lemma reach_closed_complete :
    forall R,
      (forall x, goodb x = true -> In x U) ->
      expand R = R ->
      forall a p, In a R -> chain Gb Ab a p -> In p R.
  Proof.
    intros R HgU Hfix a p HaR ch.
    induction ch as [p HG | p q r HG HA ch IH]; auto.
    apply IH; clear IH.
    assert (HGq : Gb q) by (eapply chain_good_l; eauto).
    destruct (memb q R) eqn:Em.
    - apply memb_true_iff; auto.
    - rewrite <- Hfix; unfold expand.
      apply in_or_app; right.
      apply filter_In; split.
      + apply HgU; auto.
      + rewrite HGq, Em; simpl.
        apply existsb_exists; exists p; auto.
  Qed.

  Lemma reach_from_complete :
    forall seeds,
      NoDup U -> NoDup seeds -> incl seeds U ->
      (forall x, goodb x = true -> In x U) ->
      forall a p, In a seeds -> chain Gb Ab a p -> In p (reach_from seeds).
  Proof.
    intros seeds HU Hs HsU HgU a p Ha ch.
    eapply reach_closed_complete; eauto.
    - apply reach_from_fixed; auto.
    - apply iterate_incl; auto.
  Qed.
End Saturation.
