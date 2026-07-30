(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** The game of Y and Schensted's majority reduction: exactly one winner. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Export GameTrees.Reach.


(** * Players *)

Inductive player : Type := red | blue.

Definition other (X : player) : player :=
  match X with red => blue | blue => red end.

Lemma other_involutive : forall X, other (other X) = X.
Proof. destruct X; auto. Qed.

Lemma dec_eq_player : forall X Y : player, {X = Y} + {X <> Y}.
Proof. decide equality. Defined.

Definition player_eqb (X Y : player) : bool :=
  match X, Y with
  | red, red | blue, blue => true
  | _, _ => false
  end.

Lemma player_eqb_true_iff : forall X Y, player_eqb X Y = true <-> X = Y.
Proof. intros [] []; simpl; split; congruence. Qed.

(** * The game of Y *)

(** The triangular board of order [m]: cells [(i, j)] with [j <= i < m]. *)

Definition inY (m : nat) (p : cell) : Prop :=
  snd p <= fst p /\ fst p < m.

(** Triangular-lattice adjacency. *)
Definition adjY (p q : cell) : Prop :=
     (fst q = fst p /\ (snd q = S (snd p) \/ snd p = S (snd q)))
  \/ (fst q = S (fst p) /\ (snd q = snd p \/ snd q = S (snd p)))
  \/ (fst p = S (fst q) /\ (snd q = snd p \/ snd p = S (snd q))).

Lemma adjY_sym : forall p q, adjY p q -> adjY q p.
Proof. unfold adjY; intros p q H; lia. Qed.

Definition goodY (m : nat) (c : cell -> player) (X : player) (p : cell) : Prop :=
  inY m p /\ c p = X.

(** [Y_wins m c X]: an [X]-colored connected set touching all three sides. *)
Definition Y_wins (m : nat) (c : cell -> player) (X : player) : Prop :=
  exists a b d,
    snd a = 0 /\ snd b = fst b /\ S (fst d) = m /\
    chain (goodY m c X) adjY a b /\
    chain (goodY m c X) adjY a d.

(** ** Schensted's majority reduction *)

(** The triangle of order-[S m] cells lying under the order-[m] cell [u]. *)
Definition tSW (u : cell) : cell := (S (fst u), snd u).
Definition tSE (u : cell) : cell := (S (fst u), S (snd u)).

Definition inT (u p : cell) : Prop := p = u \/ p = tSW u \/ p = tSE u.

Definition maj (x y z : player) : player :=
  if player_eqb x y then x else z.

(** The reduced coloring: each cell takes its triangle's majority color. *)
Definition reduced (c : cell -> player) : cell -> player :=
  fun u => maj (c u) (c (tSW u)) (c (tSE u)).

Lemma maj_two :
  forall x y z X,
    maj x y z = X ->
    (x = X /\ y = X) \/ (x = X /\ z = X) \/ (y = X /\ z = X).
Proof.
  intros x y z X; destruct x, y, z, X; simpl; intros H; try discriminate;
    try (left; split; reflexivity);
    try (right; left; split; reflexivity);
    right; right; split; reflexivity.
Qed.

Lemma inT_inY :
  forall m u p, inY m u -> inT u p -> inY (S m) p.
Proof.
  intros m [i j] p [H1 H2] Hp; simpl in *.
  destruct Hp as [-> | [-> | ->]]; unfold tSW, tSE, inY; simpl; lia.
Qed.

Lemma tri_pair_adj :
  forall u p q, inT u p -> inT u q -> p <> q -> adjY p q.
Proof.
  intros [i j] p q Hp Hq Hne.
  destruct Hp as [-> | [-> | ->]]; destruct Hq as [-> | [-> | ->]];
    try congruence; unfold tSW, tSE, adjY; simpl; lia.
Qed.

Lemma chain_in_triangle :
  forall (G : cell -> Prop) u p q,
    inT u p -> inT u q -> G p -> G q -> chain G adjY p q.
Proof.
  intros G u p q Hp Hq Gp Gq.
  destruct (cell_eq_dec p q) as [-> | Hne].
  - apply chain_refl; auto.
  - eapply chain_step; eauto.
    + eapply tri_pair_adj; eauto.
    + apply chain_refl; auto.
Qed.

(** ** The bridge lemma *)

(** Adjacent reduced cells of one color have adjacent witness stones. *)

Lemma bridge_row :
  forall (c : cell -> player) X i j,
    reduced c (i, j) = X -> reduced c (i, S j) = X ->
    exists p q,
      inT (i, j) p /\ inT (i, S j) q /\ c p = X /\ c q = X /\
      (p = q \/ adjY p q).
Proof.
  intros c X i j Hu Hv.
  unfold reduced, tSW, tSE in *; simpl in *.
  destruct (dec_eq_player (c (S i, S j)) X) as [Hs | Hs].
  - exists (S i, S j), (S i, S j); unfold inT, tSW, tSE; simpl; auto 7.
  - apply maj_two in Hu; apply maj_two in Hv.
    assert (Hu' : c (i, j) = X /\ c (S i, j) = X) by tauto.
    assert (Hv' : c (i, S j) = X /\ c (S i, S (S j)) = X) by tauto.
    exists (i, j), (i, S j); unfold inT, tSW, tSE; simpl.
    repeat split; try tauto.
    right; unfold adjY; simpl; lia.
Qed.

Lemma bridge_sw :
  forall (c : cell -> player) X i j,
    reduced c (i, j) = X -> reduced c (S i, j) = X ->
    exists p q,
      inT (i, j) p /\ inT (S i, j) q /\ c p = X /\ c q = X /\
      (p = q \/ adjY p q).
Proof.
  intros c X i j Hu Hv.
  unfold reduced, tSW, tSE in *; simpl in *.
  destruct (dec_eq_player (c (S i, j)) X) as [Hs | Hs].
  - exists (S i, j), (S i, j); unfold inT, tSW, tSE; simpl; auto 7.
  - apply maj_two in Hu; apply maj_two in Hv.
    assert (Hu' : c (i, j) = X /\ c (S i, S j) = X) by tauto.
    assert (Hv' : c (S (S i), j) = X /\ c (S (S i), S j) = X) by tauto.
    exists (S i, S j), (S (S i), S j); unfold inT, tSW, tSE; simpl.
    repeat split; try tauto.
    right; unfold adjY; simpl; lia.
Qed.

Lemma bridge_se :
  forall (c : cell -> player) X i j,
    reduced c (i, j) = X -> reduced c (S i, S j) = X ->
    exists p q,
      inT (i, j) p /\ inT (S i, S j) q /\ c p = X /\ c q = X /\
      (p = q \/ adjY p q).
Proof.
  intros c X i j Hu Hv.
  unfold reduced, tSW, tSE in *; simpl in *.
  destruct (dec_eq_player (c (S i, S j)) X) as [Hs | Hs].
  - exists (S i, S j), (S i, S j); unfold inT, tSW, tSE; simpl; auto 7.
  - apply maj_two in Hu; apply maj_two in Hv.
    assert (Hu' : c (i, j) = X /\ c (S i, j) = X) by tauto.
    assert (Hv' : c (S (S i), S j) = X /\ c (S (S i), S (S j)) = X) by tauto.
    exists (S i, j), (S (S i), S j); unfold inT, tSW, tSE; simpl.
    repeat split; try tauto.
    right; unfold adjY; simpl; lia.
Qed.

Lemma bridge :
  forall (c : cell -> player) X u v,
    adjY u v ->
    reduced c u = X -> reduced c v = X ->
    exists p q,
      inT u p /\ inT v q /\ c p = X /\ c q = X /\ (p = q \/ adjY p q).
Proof.
  intros c X [i j] [i' j'] Hadj Hu Hv.
  unfold adjY in Hadj; simpl in Hadj.
  destruct Hadj as [[H1 H2] | [[H1 H2] | [H1 H2]]].
  - destruct H2 as [H2 | H2].
    + (* v = (i, S j) *)
      subst i'; subst j'.
      apply (bridge_row c X i j); auto.
    + (* u = (i', S j') *)
      subst i'; subst j.
      destruct (bridge_row c X i j') as [p [q Hpq]]; auto.
      exists q, p.
      destruct Hpq as (HpT & HqT & Hpc & Hqc & Hor).
      repeat split; auto.
      destruct Hor as [-> | Hor]; auto using adjY_sym.
  - destruct H2 as [H2 | H2].
    + (* v = (S i, j) *)
      subst i'; subst j'.
      apply (bridge_sw c X i j); auto.
    + (* v = (S i, S j) *)
      subst i'; subst j'.
      apply (bridge_se c X i j); auto.
  - destruct H2 as [H2 | H2].
    + (* u = (S i', j) with j = j' *)
      subst i; subst j'.
      destruct (bridge_sw c X i' j) as [p [q Hpq]]; auto.
      exists q, p.
      destruct Hpq as (HpT & HqT & Hpc & Hqc & Hor).
      repeat split; auto.
      destruct Hor as [-> | Hor]; auto using adjY_sym.
    + (* u = (S i', S j') *)
      subst i; subst j.
      destruct (bridge_se c X i' j') as [p [q Hpq]]; auto.
      exists q, p.
      destruct Hpq as (HpT & HqT & Hpc & Hqc & Hor).
      repeat split; auto.
      destruct Hor as [-> | Hor]; auto using adjY_sym.
Qed.

(** ** Lifting chains through the reduction *)

Lemma lift_chain :
  forall m c X u v,
    chain (goodY m (reduced c) X) adjY u v ->
    forall p q,
      inT u p -> c p = X -> inT v q -> c q = X ->
      chain (goodY (S m) c X) adjY p q.
Proof.
  intros m c X u v ch.
  induction ch as [u HG | u w v HG HA ch IH]; intros p q HpT Hpc HqT Hqc.
  - destruct HG as [HuY Huc].
    apply chain_in_triangle with (u := u); auto.
    + split; [apply (inT_inY m u); auto | auto].
    + split; [apply (inT_inY m u); auto | auto].
  - destruct HG as [HuY Huc].
    assert (HwG : goodY m (reduced c) X w) by (eapply chain_good_l; eauto).
    destruct HwG as [HwY Hwc].
    destruct (bridge c X u w HA Huc Hwc) as
      [p' [q' (Hp'T & Hq'T & Hp'c & Hq'c & Hor)]].
    apply chain_trans with (q := p').
    + apply chain_in_triangle with (u := u); auto.
      * split; [apply (inT_inY m u); auto | auto].
      * split; [apply (inT_inY m u); auto | auto].
    + assert (Hq'q : chain (goodY (S m) c X) adjY q' q) by (apply IH; auto).
      destruct Hor as [-> | Hor]; auto.
      eapply chain_step; eauto.
      split; [apply (inT_inY m u); auto | auto].
Qed.

(** ** Lifting the three side-touching conditions *)

Lemma left_lift :
  forall c X i j,
    reduced c (i, j) = X -> j = 0 ->
    exists p, inT (i, j) p /\ c p = X /\ snd p = 0.
Proof.
  intros c X i j H ->.
  apply maj_two in H; unfold tSW, tSE in *; simpl in *.
  destruct H as [[H1 H2] | [[H1 H2] | [H1 H2]]].
  - exists (i, 0); unfold inT; simpl; auto.
  - exists (i, 0); unfold inT; simpl; auto.
  - exists (S i, 0); unfold inT, tSW; simpl; auto.
Qed.

Lemma right_lift :
  forall c X i j,
    reduced c (i, j) = X -> j = i ->
    exists p, inT (i, j) p /\ c p = X /\ snd p = fst p.
Proof.
  intros c X i j H ->.
  apply maj_two in H; unfold tSW, tSE in *; simpl in *.
  destruct H as [[H1 H2] | [[H1 H2] | [H1 H2]]].
  - exists (i, i); unfold inT; simpl; auto.
  - exists (i, i); unfold inT; simpl; auto.
  - exists (S i, S i); unfold inT, tSE; simpl; auto 6.
Qed.

Lemma bottom_lift :
  forall c X i j,
    reduced c (i, j) = X ->
    exists p, inT (i, j) p /\ c p = X /\ fst p = S i.
Proof.
  intros c X i j H.
  apply maj_two in H; unfold tSW, tSE in *; simpl in *.
  destruct H as [[H1 H2] | [[H1 H2] | [H1 H2]]].
  - exists (S i, j); unfold inT, tSW; simpl; auto.
  - exists (S i, S j); unfold inT, tSE; simpl; auto 6.
  - exists (S i, j); unfold inT, tSW; simpl; auto.
Qed.

(** ** The Y theorem *)

Lemma y_theorem_aux :
  forall m c, Y_wins (S m) c red \/ Y_wins (S m) c blue.
Proof.
  induction m as [|m IH]; intros c.
  - (* order 1: the single cell decides *)
    destruct (c (0, 0)) eqn:E; [left | right];
      exists (0, 0), (0, 0), (0, 0); simpl;
      repeat split; auto;
      apply chain_refl; split; auto; unfold inY; simpl; lia.
  - destruct (IH (reduced c)) as [Hw | Hw]; [left | right];
      destruct Hw as (a & b & d & Ha & Hb & Hd & Hab & Had).
    + assert (HaG : goodY (S m) (reduced c) red a)
        by (eapply chain_good_l; eauto).
      assert (HbG : goodY (S m) (reduced c) red b)
        by (eapply chain_good_r; eauto).
      assert (HdG : goodY (S m) (reduced c) red d)
        by (eapply chain_good_r; eauto).
      destruct a as [ia ja]; destruct b as [ib jb]; destruct d as [id jd];
        simpl in *.
      destruct (left_lift c red ia ja) as [pa (HpaT & Hpac & Hpa0)];
        [apply HaG | auto |].
      destruct (right_lift c red ib jb) as [pb (HpbT & Hpbc & Hpbd)];
        [apply HbG | auto |].
      destruct (bottom_lift c red id jd) as [pd (HpdT & Hpdc & Hpdr)];
        [apply HdG |].
      exists pa, pb, pd.
      repeat split; try lia.
      * eapply (lift_chain (S m) c _ (ia, ja) (ib, jb)); eauto.
      * eapply (lift_chain (S m) c _ (ia, ja) (id, jd)); eauto.
    + assert (HaG : goodY (S m) (reduced c) blue a)
        by (eapply chain_good_l; eauto).
      assert (HbG : goodY (S m) (reduced c) blue b)
        by (eapply chain_good_r; eauto).
      assert (HdG : goodY (S m) (reduced c) blue d)
        by (eapply chain_good_r; eauto).
      destruct a as [ia ja]; destruct b as [ib jb]; destruct d as [id jd];
        simpl in *.
      destruct (left_lift c blue ia ja) as [pa (HpaT & Hpac & Hpa0)];
        [apply HaG | auto |].
      destruct (right_lift c blue ib jb) as [pb (HpbT & Hpbc & Hpbd)];
        [apply HbG | auto |].
      destruct (bottom_lift c blue id jd) as [pd (HpdT & Hpdc & Hpdr)];
        [apply HdG |].
      exists pa, pb, pd.
      repeat split; try lia.
      * eapply (lift_chain (S m) c _ (ia, ja) (ib, jb)); eauto.
      * eapply (lift_chain (S m) c _ (ia, ja) (id, jd)); eauto.
Qed.

Theorem y_theorem :
  forall m c, 1 <= m -> Y_wins m c red \/ Y_wins m c blue.
Proof.
  intros m c Hm; destruct m as [|m]; [lia | apply y_theorem_aux].
Qed.

(** ** Projection: winners descend through the reduction *)

(** A winning chain at order [S m] projects to one at order [m]. *)

Lemma adjY_irrefl : forall p, ~ adjY p p.
Proof. intros [i j]; unfold adjY; simpl; lia. Qed.

Lemma maj_of_two :
  forall x y z X,
    (x = X /\ y = X) \/ (x = X /\ z = X) \/ (y = X /\ z = X) ->
    maj x y z = X.
Proof.
  intros x y z X H; destruct x, y, z, X; simpl in *; intuition congruence.
Qed.

(** Two [X]-colored cells of a common triangle force its majority to [X]. *)
Lemma reduced_of_pair :
  forall (c : cell -> player) X u p q,
    inT u p -> inT u q -> p <> q -> c p = X -> c q = X ->
    reduced c u = X.
Proof.
  intros c X u p q Hp Hq Hne Hcp Hcq.
  unfold reduced.
  apply maj_of_two.
  destruct Hp as [-> | [-> | ->]]; destruct Hq as [-> | [-> | ->]];
    try congruence; tauto.
Qed.

(** Two adjacent big-board cells share a triangle of the small board. *)
Lemma pair_parent :
  forall m p q,
    inY (S m) p -> inY (S m) q -> adjY p q ->
    exists u, inY m u /\ inT u p /\ inT u q.
Proof.
  intros m [i j] [i' j'] [HYp1 HYp2] [HYq1 HYq2] HA; simpl in *.
  unfold adjY in HA; simpl in HA.
  destruct HA as [[H1 H2] | [[H1 H2] | [H1 H2]]].
  - subst i'.
    destruct H2 as [H2 | H2].
    + subst j'.
      destruct i as [|i0]; [lia|].
      exists (i0, j); unfold inY, inT, tSW, tSE; simpl.
      repeat split; try lia.
      * right; left; reflexivity.
      * right; right; reflexivity.
    + subst j.
      destruct i as [|i0]; [lia|].
      exists (i0, j'); unfold inY, inT, tSW, tSE; simpl.
      repeat split; try lia.
      * right; right; reflexivity.
      * right; left; reflexivity.
  - subst i'.
    destruct H2 as [H2 | H2]; subst j'.
    + exists (i, j); unfold inY, inT, tSW, tSE; simpl.
      repeat split; try lia.
      * left; reflexivity.
      * right; left; reflexivity.
    + exists (i, j); unfold inY, inT, tSW, tSE; simpl.
      repeat split; try lia.
      * left; reflexivity.
      * right; right; reflexivity.
  - subst i.
    destruct H2 as [H2 | H2].
    + subst j'.
      exists (i', j); unfold inY, inT, tSW, tSE; simpl.
      repeat split; try lia.
      * right; left; reflexivity.
      * left; reflexivity.
    + subst j.
      exists (i', j'); unfold inY, inT, tSW, tSE; simpl.
      repeat split; try lia.
      * right; right; reflexivity.
      * left; reflexivity.
Qed.

(** Two small cells whose triangles share a big cell are equal or adjacent. *)
Lemma shared_cell_parents :
  forall u v q, inT u q -> inT v q -> u = v \/ adjY u v.
Proof.
  intros [i j] [i' j'] q Hu Hv.
  destruct Hu as [-> | [-> | ->]]; destruct Hv as [Hv | [Hv | Hv]];
    unfold tSW, tSE in *; injection Hv as H1 H2;
    first [ left; f_equal; lia | right; unfold adjY; simpl; lia ].
Qed.

Lemma inT_left : forall u p, inT u p -> snd p = 0 -> snd u = 0.
Proof.
  intros [i j] p Hp H0; destruct Hp as [-> | [-> | ->]];
    unfold tSW, tSE in *; simpl in *; lia.
Qed.

Lemma inT_right :
  forall m u p, inY m u -> inT u p -> snd p = fst p -> snd u = fst u.
Proof.
  intros m [i j] p [H1 H2] Hp He; destruct Hp as [-> | [-> | ->]];
    unfold tSW, tSE in *; simpl in *; lia.
Qed.

Lemma inT_bottom :
  forall m u p, inY m u -> inT u p -> S (fst p) = S m -> S (fst u) = m.
Proof.
  intros m [i j] p [H1 H2] Hp Hb; destruct Hp as [-> | [-> | ->]];
    unfold tSW, tSE in *; simpl in *; lia.
Qed.

(** Project a nonempty big-board chain to one between triangle parents. *)
Lemma project_chain :
  forall m c X p p1 q,
    inY (S m) p -> c p = X -> adjY p p1 ->
    chain (goodY (S m) c X) adjY p1 q ->
    exists u v,
      inY m u /\ inT u p /\ inT u p1 /\ inT v q /\
      chain (goodY m (reduced c) X) adjY u v.
Proof.
  intros m c X p p1 q HYp Hcp HA ch; revert p HYp Hcp HA.
  induction ch as [p1 HG | p1 p2 q HG HA2 ch IH]; intros p HYp Hcp HA.
  - destruct HG as [HYp1 Hcp1].
    destruct (pair_parent m p p1 HYp HYp1 HA) as [u (HuY & HuP & HuP1)].
    assert (Hgu : goodY m (reduced c) X u).
    { split; auto.
      apply (reduced_of_pair c X u p p1); auto.
      intros ->; exact (adjY_irrefl p1 HA). }
    exists u, u.
    split; [exact HuY|].
    split; [exact HuP|].
    split; [exact HuP1|].
    split; [exact HuP1|].
    apply chain_refl; exact Hgu.
  - destruct HG as [HYp1 Hcp1].
    destruct (IH p1 HYp1 Hcp1 HA2)
      as [u' [v (Hu'Y & Hu'P1 & Hu'P2 & HvQ & ch')]].
    destruct (pair_parent m p p1 HYp HYp1 HA) as [u (HuY & HuP & HuP1)].
    assert (Hgu : goodY m (reduced c) X u).
    { split; auto.
      apply (reduced_of_pair c X u p p1); auto.
      intros ->; exact (adjY_irrefl p1 HA). }
    exists u, v.
    split; [exact HuY|].
    split; [exact HuP|].
    split; [exact HuP1|].
    split; [exact HvQ|].
    destruct (shared_cell_parents u u' p1 HuP1 Hu'P1) as [Heq | Hadj].
    + rewrite Heq; exact ch'.
    + eapply chain_step; eauto.
Qed.

Lemma project_win :
  forall m c X, 1 <= m -> Y_wins (S m) c X -> Y_wins m (reduced c) X.
Proof.
  intros m c X Hm (a & b & d & Ha & Hb & Hd & Hab & Had).
  destruct (chain_cases _ _ _ _ Hab) as [[Eb HGa] | [a1 (HGa & HAa & tailb)]].
  - (* a = b: the hub is on both the left and right edges, so a = (0, 0) *)
    subst b.
    destruct a as [ia ja]; simpl in Ha, Hb, Hd; subst ja.
    assert (ia = 0) by lia; subst ia.
    destruct (chain_cases _ _ _ _ Had)
      as [[Ed HGd] | [a1 (HGa' & HAa & tail)]].
    + (* a = d as well: only possible on the order-1 board *)
      rewrite <- Ed in Hd; simpl in Hd; lia.
    + destruct HGa' as [HYa Hca].
      destruct (project_chain m c X (0, 0) a1 d HYa Hca HAa tail)
        as [u [v (HuY & HuA & HuA1 & HvD & ch')]].
      assert (Hu0 : u = (0, 0)).
      { destruct u as [ui uj].
        destruct HuA as [HuA | [HuA | HuA]];
          unfold tSW, tSE in HuA; [congruence | discriminate | discriminate]. }
      subst u.
      assert (HvY : inY m v)
        by (destruct (chain_good_r _ _ _ _ ch'); auto).
      exists (0, 0), (0, 0), v.
      repeat split; simpl; auto.
      * exact (inT_bottom m v d HvY HvD Hd).
      * apply chain_refl.
        eapply chain_good_l; eauto.
  - destruct HGa as [HYa Hca].
    destruct (chain_cases _ _ _ _ Had)
      as [[Ed HGd] | [a1' (HGa' & HAa' & tail)]].
    + (* a = d: the hub is on both the left edge and the bottom row *)
      rewrite <- Ed in Hd.
      destruct (project_chain m c X a a1 b HYa Hca HAa tailb)
        as [u [v (HuY & HuA & HuA1 & HvB & ch')]].
      assert (HvY : inY m v)
        by (destruct (chain_good_r _ _ _ _ ch'); auto).
      exists u, v, u.
      repeat split.
      * exact (inT_left u a HuA Ha).
      * exact (inT_right m v b HvY HvB Hb).
      * exact (inT_bottom m u a HuY HuA Hd).
      * exact ch'.
      * apply chain_refl.
        eapply chain_good_l; eauto.
    + destruct (project_chain m c X a a1 b HYa Hca HAa tailb)
        as [u1 [v1 (Hu1Y & Hu1A & Hu1A1 & Hv1B & ch1)]].
      destruct (project_chain m c X a a1' d HYa Hca HAa' tail)
        as [u2 [v2 (Hu2Y & Hu2A & Hu2A1 & Hv2D & ch2)]].
      assert (Hv1Y : inY m v1)
        by (destruct (chain_good_r _ _ _ _ ch1); auto).
      assert (Hv2Y : inY m v2)
        by (destruct (chain_good_r _ _ _ _ ch2); auto).
      exists u1, v1, v2.
      repeat split.
      * exact (inT_left u1 a Hu1A Ha).
      * exact (inT_right m v1 b Hv1Y Hv1B Hb).
      * exact (inT_bottom m v2 d Hv2Y Hv2D Hd).
      * exact ch1.
      * destruct (shared_cell_parents u1 u2 a Hu1A Hu2A)
          as [Heq | Hadj].
        -- rewrite Heq; exact ch2.
        -- eapply chain_step; eauto.
           eapply chain_good_l; eauto.
Qed.

Lemma y_at_most_one_aux :
  forall m c, Y_wins (S m) c red -> Y_wins (S m) c blue -> False.
Proof.
  induction m as [|m IH]; intros c Hr Hb.
  - destruct Hr as (a & br & dr & _ & _ & _ & Hab & _).
    destruct Hb as (a' & bb & db & _ & _ & _ & Hab' & _).
    apply chain_good_l in Hab; apply chain_good_l in Hab'.
    destruct Hab as [[HY1 HY2] Hc]; destruct Hab' as [[HY1' HY2'] Hc'].
    destruct a as [i j]; destruct a' as [i' j']; simpl in *.
    assert (i = 0) by lia; assert (j = 0) by lia;
      assert (i' = 0) by lia; assert (j' = 0) by lia; subst.
    congruence.
  - exact (IH (reduced c)
             (project_win (S m) c red ltac:(lia) Hr)
             (project_win (S m) c blue ltac:(lia) Hb)).
Qed.

(** At most one color wins the game of Y at every order. *)
Theorem y_at_most_one :
  forall m c, Y_wins m c red -> Y_wins m c blue -> False.
Proof.
  intros [|m] c Hr Hb.
  - destruct Hr as (a & br & dr & _ & _ & _ & Hab & _).
    apply chain_good_l in Hab.
    destruct Hab as [[_ HY] _]; destruct a; simpl in *; lia.
  - exact (y_at_most_one_aux m c Hr Hb).
Qed.
