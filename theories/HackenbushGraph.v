(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Green Hackenbush on finite multigraphs: a player deletes any edge, and
    every edge that loses its connection to the ground goes with it. All edges
    move for either player, so the game is impartial and its value is the
    Grundy value of [GameTrees.Grundy]. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.Trees.
Require Import GameTrees.Grundy.

(** * Graphs *)

(** Vertices are numbers and the ground is vertex [0]. *)
Definition vertex : Type := nat.

Definition ground : vertex := 0.

(** An edge is an unordered pair of endpoints; a loop has both equal. *)
Definition edge : Type := (vertex * vertex)%type.

(** A graph is a list of edges, so parallel edges and loops are allowed and a
    move names an edge by its position. *)
Definition graph : Type := list edge.

Definition ends (e : edge) : vertex * vertex := e.

Definition incident (v : vertex) (e : edge) : bool :=
  (Nat.eqb v (fst e) || Nat.eqb v (snd e))%bool.

Lemma incident_true_iff :
  forall v e, incident v e = true <-> v = fst e \/ v = snd e.
Proof.
  intros v e; unfold incident; rewrite orb_true_iff, !Nat.eqb_eq; reflexivity.
Qed.

(** The endpoint of [e] opposite [v], and [v] itself on a loop. *)
Definition across (v : vertex) (e : edge) : vertex :=
  if Nat.eqb v (fst e) then snd e else fst e.

(** * Reachability from the ground *)

(** One edge joins its endpoints, in either direction. *)
Definition joins (e : edge) (v w : vertex) : Prop :=
  (v = fst e /\ w = snd e) \/ (v = snd e /\ w = fst e).

Lemma joins_across :
  forall e v, incident v e = true -> joins e v (across v e).
Proof.
  intros e v H; apply incident_true_iff in H; unfold joins, across.
  destruct (Nat.eqb v (fst e)) eqn:E.
  - apply Nat.eqb_eq in E; auto.
  - apply Nat.eqb_neq in E; destruct H; [contradiction | auto].
Qed.

(** Walks along the edges of [g]. *)
Inductive walk (g : graph) : vertex -> vertex -> Prop :=
| walk_refl : forall v, walk g v v
| walk_step : forall v w u e,
    In e g -> joins e v w -> walk g w u -> walk g v u.

Lemma walk_trans :
  forall g u v w, walk g u v -> walk g v w -> walk g u w.
Proof.
  intros g u v w H1; revert w; induction H1 as [|a b c e He Hj Hw IH]; auto.
  intros w H2; apply (walk_step g a b w e); auto.
Qed.

Lemma joins_sym : forall e v w, joins e v w -> joins e w v.
Proof. intros e v w H; unfold joins in *; tauto. Qed.

Lemma walk_sym : forall g v w, walk g v w -> walk g w v.
Proof.
  intros g v w H; induction H as [|a b c e He Hj Hw IH]; [constructor|].
  apply (walk_trans g c b a); [exact IH|].
  apply (walk_step g b a a e); [exact He | apply joins_sym; exact Hj | constructor].
Qed.

(** A set that contains the ground and is closed under the edges of [g] holds
    every vertex joined to the ground; this is how a position is shown to be
    cut off. *)
Lemma walk_closed :
  forall (g : graph) (C : vertex -> Prop),
    (forall e v w, In e g -> joins e v w -> C v -> C w) ->
    forall v w, walk g v w -> C v -> C w.
Proof.
  intros g C Hcl v w Hw; induction Hw as [|a b c e He Hj Hwk IH]; auto.
  intros Ha; apply IH; apply (Hcl e a b); auto.
Qed.

(** Membership of a vertex list. *)
Definition memb (v : vertex) (l : list vertex) : bool := existsb (Nat.eqb v) l.

Lemma memb_true_iff : forall v l, memb v l = true <-> In v l.
Proof.
  intros v l; unfold memb; rewrite existsb_exists; split.
  - intros [x [Hx Heq]]; apply Nat.eqb_eq in Heq; subst; exact Hx.
  - intros H; exists v; split; [exact H | apply Nat.eqb_refl].
Qed.

Lemma memb_false_iff : forall v l, memb v l = false <-> ~ In v l.
Proof.
  intros v l; split.
  - intros H Hin; rewrite <- memb_true_iff in Hin; congruence.
  - intros H; destruct (memb v l) eqn:E; auto.
    rewrite memb_true_iff in E; contradiction.
Qed.

(** The vertices one edge away from a set. *)
Definition nbrs (g : graph) (Q : list vertex) : list vertex :=
  flat_map (fun e => (if memb (fst e) Q then [snd e] else []) ++
                     (if memb (snd e) Q then [fst e] else [])) g.

Lemma in_nbrs :
  forall g Q w,
    In w (nbrs g Q) <-> exists e v, In e g /\ In v Q /\ joins e v w.
Proof.
  intros g Q w; unfold nbrs; rewrite in_flat_map; split.
  - intros [e [He Hin]]; apply in_app_or in Hin.
    destruct Hin as [Hin | Hin]; destruct (memb _ Q) eqn:Em;
      simpl in Hin; try contradiction.
    + destruct Hin as [<- | []]; exists e, (fst e).
      rewrite memb_true_iff in Em; unfold joins; tauto.
    + destruct Hin as [<- | []]; exists e, (snd e).
      rewrite memb_true_iff in Em; unfold joins; tauto.
  - intros [e [v [He [Hv Hj]]]]; exists e; split; [exact He|].
    destruct Hj as [[-> ->] | [-> ->]].
    + rewrite (proj2 (memb_true_iff (fst e) Q) Hv); simpl; auto.
    + rewrite (proj2 (memb_true_iff (snd e) Q) Hv).
      apply in_or_app; right; simpl; auto.
Qed.

(** One round of saturation. *)
Definition step (g : graph) (Q : list vertex) : list vertex :=
  Q ++ filter (fun w => negb (memb w Q)) (nbrs g Q).

Lemma in_step :
  forall g Q w, In w (step g Q) <-> In w Q \/ In w (nbrs g Q).
Proof.
  intros g Q w; unfold step; rewrite in_app_iff; split.
  - intros [H | H]; [left; exact H|]; apply filter_In in H; tauto.
  - intros [H | H]; [left; exact H|].
    destruct (memb w Q) eqn:Em.
    + left; apply memb_true_iff; exact Em.
    + right; apply filter_In; split; [exact H | rewrite Em; reflexivity].
Qed.

Lemma step_incl : forall g Q, incl Q (step g Q).
Proof. intros g Q v Hv; apply in_step; left; exact Hv. Qed.

Lemma step_mono :
  forall g S1 S2, incl S1 S2 -> incl (step g S1) (step g S2).
Proof.
  intros g S1 S2 H w Hw; apply in_step in Hw; apply in_step.
  destruct Hw as [Hw | Hw]; [left; apply H; exact Hw|].
  right; apply in_nbrs in Hw; destruct Hw as [e [v [He [Hv Hj]]]].
  apply in_nbrs; exists e, v; repeat split; auto.
Qed.

Fixpoint sat (n : nat) (g : graph) (Q : list vertex) : list vertex :=
  match n with
  | O => Q
  | S n' => sat n' g (step g Q)
  end.

Lemma sat_mono :
  forall n g S1 S2, incl S1 S2 -> incl (sat n g S1) (sat n g S2).
Proof.
  induction n as [|n IH]; intros g S1 S2 H; [exact H|].
  simpl; apply IH; apply step_mono; exact H.
Qed.

Lemma sat_incl : forall n g Q, incl Q (sat n g Q).
Proof.
  induction n as [|n IH]; intros g Q; [apply incl_refl|].
  simpl; apply (incl_tran (step_incl g Q)); apply IH.
Qed.

(** A closed set stays put. *)
Lemma sat_of_closed :
  forall n g Q, incl (step g Q) Q -> incl (sat n g Q) Q.
Proof.
  induction n as [|n IH]; intros g Q H; [apply incl_refl|].
  simpl; apply (incl_tran (sat_mono n g (step g Q) Q H)); apply IH; exact H.
Qed.

(** Everything reached is an endpoint of an edge, or a seed. *)
Definition usets (g : graph) : list vertex :=
  ground :: flat_map (fun e => [fst e; snd e]) g.

Lemma nbrs_usets : forall g Q, incl (nbrs g Q) (usets g).
Proof.
  intros g Q w Hw; apply in_nbrs in Hw.
  destruct Hw as [e [v [He [_ Hj]]]].
  unfold usets; right; apply in_flat_map; exists e; split; [exact He|].
  destruct Hj as [[-> ->] | [-> ->]]; simpl; auto.
Qed.

Lemma sat_usets :
  forall n g Q, incl Q (usets g) -> incl (sat n g Q) (usets g).
Proof.
  induction n as [|n IH]; intros g Q H; [exact H|].
  simpl; apply IH; intros w Hw; apply in_step in Hw.
  destruct Hw as [Hw | Hw]; [apply H; exact Hw | apply nbrs_usets with (Q := Q); exact Hw].
Qed.

(** A closure test, so a round can be examined. *)
Definition closedb (g : graph) (Q : list vertex) : bool :=
  forallb (fun w => memb w Q) (step g Q).

Lemma closedb_incl :
  forall g Q, closedb g Q = true -> incl (step g Q) Q.
Proof.
  intros g Q H w Hw; apply memb_true_iff.
  apply (proj1 (forallb_forall _ _) H w Hw).
Qed.

Lemma forallb_false_witness :
  forall {A : Type} (f : A -> bool) l,
    forallb f l = false -> exists x, In x l /\ f x = false.
Proof.
  intros A f l; induction l as [|a l IH]; simpl; [discriminate|].
  destruct (f a) eqn:Ea; simpl; intros H.
  - destruct (IH H) as [x [Hx Hf]]; exists x; auto.
  - exists a; auto.
Qed.

(** Each round either closes or adds a vertex not seen before. *)
Lemma sat_closed_or_grow :
  forall n g Q,
    incl (step g (sat n g Q)) (sat n g Q) \/
    length (nodup Nat.eq_dec Q) + n <= length (nodup Nat.eq_dec (sat n g Q)).
Proof.
  induction n as [|n IH]; intros g Q.
  - right; simpl; lia.
  - destruct (closedb g Q) eqn:Hc.
    + left.
      apply closedb_incl in Hc.
      assert (Hs : incl (sat (S n) g Q) Q) by (apply sat_of_closed; exact Hc).
      apply (incl_tran (step_mono g (sat (S n) g Q) Q Hs)).
      apply (incl_tran Hc); apply sat_incl.
    + destruct (IH g (step g Q)) as [Hcl | Hgr]; [left; exact Hcl|].
      right; simpl.
      destruct (forallb_false_witness _ _ Hc) as [w [Hw Hnm]].
      apply memb_false_iff in Hnm.
      assert (Hlt : S (length (nodup Nat.eq_dec Q))
                    <= length (nodup Nat.eq_dec (step g Q))).
      { change (length (w :: nodup Nat.eq_dec Q)
                <= length (nodup Nat.eq_dec (step g Q))).
        apply NoDup_incl_length.
        - constructor; [rewrite nodup_In; exact Hnm | apply NoDup_nodup].
        - intros x [<- | Hx]; apply nodup_In.
          + exact Hw.
          + apply nodup_In in Hx; apply step_incl; exact Hx. }
      lia.
Qed.

(** [reach g] is the set of vertices joined to the ground. *)
Definition reach (g : graph) : list vertex :=
  sat (S (S (2 * length g))) g [ground].

Definition connected (g : graph) (v : vertex) : bool := memb v (reach g).

Lemma reach_ground : forall g, In ground (reach g).
Proof. intros g; apply sat_incl; simpl; auto. Qed.

Lemma connected_ground : forall g, connected g ground = true.
Proof. intros g; apply memb_true_iff, reach_ground. Qed.

Lemma usets_length : forall g, length (usets g) = S (2 * length g).
Proof.
  intros g; unfold usets; cbn [length]; f_equal.
  induction g as [|e g IH]; cbn [flat_map length]; auto.
  rewrite length_app; cbn [length]; lia.
Qed.

(** Enough rounds have run that no edge leads out of [reach g]. *)
Lemma reach_closed : forall g, incl (step g (reach g)) (reach g).
Proof.
  intros g; unfold reach.
  destruct (sat_closed_or_grow (S (S (2 * length g))) g [ground]) as [H | H];
    [exact H|].
  exfalso.
  assert (Hsub : incl (sat (S (S (2 * length g))) g [ground]) (usets g)).
  { apply sat_usets; intros v [<- | []]; unfold usets; left; reflexivity. }
  assert (Hlen : length (nodup Nat.eq_dec (sat (S (S (2 * length g))) g [ground]))
                 <= length (usets g)).
  { apply NoDup_incl_length; [apply NoDup_nodup|].
    intros v Hv; apply nodup_In in Hv; apply Hsub; exact Hv. }
  pose proof (usets_length g) as Hu.
  assert (Hn1 : length (nodup Nat.eq_dec [ground]) = 1) by reflexivity.
  lia.
Qed.

(** Every walk from the ground lands in [reach g]. *)
Lemma connected_complete :
  forall g v, walk g ground v -> connected g v = true.
Proof.
  intros g v Hw; apply memb_true_iff.
  assert (Hcl : forall e a b,
             In e g -> joins e a b -> In a (reach g) -> In b (reach g)).
  { intros e a b He Hj Ha.
    apply (reach_closed g); apply in_step; right.
    apply in_nbrs; exists e, a; auto. }
  apply (walk_closed g (fun x => In x (reach g)) Hcl ground v Hw).
  apply reach_ground.
Qed.

(** And everything in [reach g] is joined to the ground by a walk. *)
Lemma sat_sound :
  forall n g Q w,
    In w (sat n g Q) -> exists v, In v Q /\ walk g v w.
Proof.
  induction n as [|n IH]; intros g Q w H.
  - exists w; split; [exact H | constructor].
  - simpl in H; destruct (IH g (step g Q) w H) as [u [Hu Hw]].
    apply in_step in Hu; destruct Hu as [Hu | Hu].
    + exists u; split; auto.
    + apply in_nbrs in Hu; destruct Hu as [e [v [He [Hv Hj]]]].
      exists v; split; [exact Hv|].
      apply (walk_trans g v u w); [|exact Hw].
      apply (walk_step g v u u e); [exact He | exact Hj | constructor].
Qed.

Lemma connected_walk : forall g v, connected g v = true -> walk g v ground.
Proof.
  intros g v H; apply memb_true_iff in H.
  destruct (sat_sound _ g _ v H) as [u [Hu Hw]].
  destruct Hu as [<- | []]; apply walk_sym; exact Hw.
Qed.

Theorem connected_iff :
  forall g v, connected g v = true <-> walk g v ground.
Proof.
  intros g v; split; [apply connected_walk|].
  intros H; apply connected_complete, walk_sym; exact H.
Qed.

(** An edge survives while one of its endpoints is joined to the ground. *)
Definition live (g : graph) (e : edge) : bool :=
  (connected g (fst e) || connected g (snd e))%bool.

(** * Positions and moves *)

(** Deleting an edge can strand others: what remains is what is still joined
    to the ground. *)
Definition prune (g : graph) : graph := filter (live g) g.

Lemma prune_incl : forall g e, In e (prune g) -> In e g.
Proof.
  intros g e H; unfold prune in H; apply filter_In in H; tauto.
Qed.

Lemma prune_length_le : forall g, length (prune g) <= length g.
Proof. intros g; unfold prune; apply filter_length_le. Qed.

(** Delete the edge at position [i]. *)
Definition drop_at (i : nat) (g : graph) : graph :=
  firstn i g ++ skipn (S i) g.

Lemma drop_at_length :
  forall i g, i < length g -> length (drop_at i g) = length g - 1.
Proof.
  intros i g Hi; unfold drop_at.
  rewrite length_app, length_firstn, length_skipn.
  rewrite Nat.min_l by lia; lia.
Qed.

(** The positions reachable in one move: delete a live edge, then prune. *)
Definition moves (g : graph) : list graph :=
  map (fun i => prune (drop_at i g))
      (filter (fun i => live g (nth i g (0, 0))) (seq 0 (length g))).

Lemma in_moves :
  forall g g',
    In g' (moves g) <->
    exists i, i < length g /\ live g (nth i g (0, 0)) = true /\
              g' = prune (drop_at i g).
Proof.
  intros g g'; unfold moves; rewrite in_map_iff; split.
  - intros [i [<- Hi]].
    apply filter_In in Hi; destruct Hi as [Hi Hl].
    apply in_seq in Hi; exists i; repeat split; auto; lia.
  - intros [i [Hi [Hl ->]]].
    exists i; split; auto.
    apply filter_In; split; auto; apply in_seq; lia.
Qed.

(** Every move shortens the edge list, which is what makes the game finite. *)
Lemma moves_shorter :
  forall g g', In g' (moves g) -> length g' < length g.
Proof.
  intros g g' H; apply in_moves in H.
  destruct H as [i [Hi [_ ->]]].
  pose proof (prune_length_le (drop_at i g)) as Hp.
  rewrite (drop_at_length i g Hi) in Hp; lia.
Qed.

(** * The game *)

(** The game tree of a position, cut off after [fuel] moves. *)
Fixpoint hbg (fuel : nat) (g : graph) : game :=
  match fuel with
  | O => node tt []
  | S f => node tt (map (hbg f) (moves g))
  end.

Lemma hbg_stable :
  forall N g f1 f2,
    length g <= N -> length g <= f1 -> length g <= f2 ->
    hbg f1 g = hbg f2 g.
Proof.
  induction N as [|N IH]; intros g f1 f2 HN Hf1 Hf2.
  - assert (Hg : g = []) by (apply length_zero_iff_nil; lia).
    subst g; destruct f1; destruct f2; reflexivity.
  - destruct f1 as [|f1].
    + assert (Hg : g = []) by (apply length_zero_iff_nil; lia).
      subst g; destruct f2; reflexivity.
    + destruct f2 as [|f2].
      * assert (Hg : g = []) by (apply length_zero_iff_nil; lia).
        subst g; reflexivity.
      * simpl; f_equal; apply map_ext_in; intros m Hm.
        pose proof (moves_shorter g m Hm); apply (IH m); lia.
Qed.

(** The game of a position, with just enough fuel. *)
Definition Hb (g : graph) : game := hbg (length g) g.

Lemma hbg_Hb : forall f g, length g <= f -> hbg f g = Hb g.
Proof.
  intros f g Hf; unfold Hb; apply (hbg_stable (length g)); lia.
Qed.

Lemma Hb_eq : forall g, Hb g = node tt (map Hb (moves g)).
Proof.
  intros g; unfold Hb at 1.
  destruct (length g) as [|f] eqn:Eg.
  - assert (Hg : g = []) by (apply length_zero_iff_nil; auto).
    subst g; reflexivity.
  - simpl; f_equal; apply map_ext_in; intros m Hm.
    pose proof (moves_shorter g m Hm); apply hbg_Hb; lia.
Qed.

(** The Grundy value of a position. *)
Definition gval (g : graph) : nat := grundy (Hb g).

Lemma gval_eq : forall g, gval g = mex (map gval (moves g)).
Proof.
  intros g; unfold gval; rewrite Hb_eq, grundy_eq, map_map; reflexivity.
Qed.

(** The empty position is a loss for the mover. *)
Lemma moves_nil : moves [] = [].
Proof. reflexivity. Qed.

Lemma gval_nil : gval [] = 0.
Proof. rewrite gval_eq, moves_nil; reflexivity. Qed.

(** The mover wins exactly when the value is nonzero. *)
Theorem winb_gval :
  forall g, winb (Hb g) = true <-> gval g <> 0.
Proof. intros g; apply winb_grundy. Qed.

(** * Loops at the ground *)

(** [skipn] of a constant list. *)
Lemma skipn_repeat :
  forall {A : Type} (x : A) n i, skipn i (repeat x n) = repeat x (n - i).
Proof.
  intros A x n; induction n as [|k IH]; intros i.
  - rewrite skipn_nil; reflexivity.
  - destruct i as [|i]; [reflexivity|]; simpl; apply IH.
Qed.

(** [mex] of a nonempty list with a single value: the value blocks itself and
    nothing else. *)
Lemma mex_all_eq :
  forall l v,
    l <> [] -> (forall x, In x l -> x = v) ->
    mex l = if Nat.eqb v 0 then 1 else 0.
Proof.
  intros l v Hne Hall.
  assert (Hv : In v l)
    by (destruct l as [|a l]; [contradiction | rewrite <- (Hall a); simpl; auto]).
  destruct (Nat.eqb v 0) eqn:Ev.
  - apply Nat.eqb_eq in Ev; subst v.
    apply mex_unique; [intros H; discriminate (Hall 1 H) | intros x Hx].
    assert (x = 0) as -> by lia; exact Hv.
  - apply Nat.eqb_neq in Ev.
    apply mex_unique; [intros H; apply Ev; symmetry; apply (Hall 0 H) | intros x Hx; lia].
Qed.

(** A bouquet of [k] loops at the ground. *)
Definition loops (k : nat) : graph := repeat (ground, ground) k.

Lemma loops_length : forall k, length (loops k) = k.
Proof. intros k; apply repeat_length. Qed.

Lemma in_loops : forall k e, In e (loops k) -> e = (ground, ground).
Proof. intros k e H; apply repeat_spec in H; exact H. Qed.

Lemma live_loops : forall k e, In e (loops k) -> live (loops k) e = true.
Proof.
  intros k e He; rewrite (in_loops k e He); unfold live; simpl.
  rewrite connected_ground; reflexivity.
Qed.

Lemma prune_loops : forall k, prune (loops k) = loops k.
Proof.
  intros k; unfold prune; apply filter_all; intros e He.
  apply live_loops; exact He.
Qed.

Lemma drop_at_loops :
  forall i k, i < k -> drop_at i (loops k) = loops (k - 1).
Proof.
  intros i k Hi; unfold drop_at, loops.
  rewrite firstn_repeat_le by lia.
  rewrite skipn_repeat, <- repeat_app.
  f_equal; lia.
Qed.

(** Every move on a bouquet removes one loop and leaves the rest. *)
Lemma moves_loops_nonnil : forall k, moves (loops (S k)) <> [].
Proof.
  intros k H.
  assert (Hin : In (prune (drop_at 0 (loops (S k)))) (moves (loops (S k)))).
  { apply in_moves; exists 0; repeat split;
      try (pose proof (loops_length (S k)); lia);
      try (apply live_loops, nth_In; pose proof (loops_length (S k)); lia). }
  rewrite H in Hin; destruct Hin.
Qed.

Lemma in_moves_loops :
  forall k g', In g' (moves (loops (S k))) -> g' = loops k.
Proof.
  intros k g' H; apply in_moves in H.
  destruct H as [i [Hi [_ ->]]].
  pose proof (loops_length (S k)) as Hl; rewrite Hl in Hi.
  rewrite drop_at_loops by lia.
  rewrite prune_loops; f_equal; lia.
Qed.

(** Loops at the ground cancel in pairs: this is the arithmetic that the
    fusion of a cycle leaves behind. *)
Theorem gval_loops : forall k, gval (loops k) = if Nat.even k then 0 else 1.
Proof.
  induction k as [|k IH].
  - apply gval_nil.
  - rewrite gval_eq.
    rewrite (mex_all_eq (map gval (moves (loops (S k)))) (if Nat.even k then 0 else 1)).
    + rewrite Nat.even_succ, <- Nat.negb_even.
      destruct (Nat.even k); reflexivity.
    + intros H; apply (moves_loops_nonnil k); apply map_eq_nil in H; exact H.
    + intros x Hx; apply in_map_iff in Hx.
      destruct Hx as [g' [<- Hg']].
      rewrite (in_moves_loops k g' Hg'); exact IH.
Qed.

(** * Paths from the ground *)

(** The path [0 - 1 - ... - n], with [n] edges. *)
Definition path (n : nat) : graph := map (fun i => (i, S i)) (seq 0 n).

Lemma path_length : forall n, length (path n) = n.
Proof. intros n; unfold path; rewrite length_map, length_seq; reflexivity. Qed.

Lemma in_path :
  forall n e, In e (path n) <-> exists i, i < n /\ e = (i, S i).
Proof.
  intros n e; unfold path; rewrite in_map_iff; split.
  - intros [i [<- Hi]]; apply in_seq in Hi; exists i; split; auto; lia.
  - intros [i [Hi ->]]; exists i; split; auto; apply in_seq; lia.
Qed.

Lemma path_edge_in : forall n i, i < n -> In (i, S i) (path n).
Proof. intros n i Hi; apply in_path; exists i; auto. Qed.

(** Every vertex of a path is joined to the ground. *)
Lemma walk_path : forall n j, j <= n -> walk (path n) ground j.
Proof.
  intros n j; induction j as [|j IH]; intros Hj; [constructor|].
  apply (walk_trans (path n) ground j (S j)); [apply IH; lia|].
  apply (walk_step (path n) j (S j) (S j) (j, S j)).
  - apply path_edge_in; lia.
  - unfold joins; cbn [fst snd]; left; auto.
  - constructor.
Qed.

Lemma connected_path : forall n j, j <= n -> connected (path n) j = true.
Proof. intros n j Hj; apply connected_complete, walk_path; lia. Qed.

Lemma live_path : forall n e, In e (path n) -> live (path n) e = true.
Proof.
  intros n e He; apply in_path in He; destruct He as [i [Hi ->]].
  unfold live; simpl; rewrite (connected_path n i) by lia; reflexivity.
Qed.

Lemma prune_path : forall n, prune (path n) = path n.
Proof.
  intros n; unfold prune; apply filter_all; intros e He; apply live_path; auto.
Qed.

(** Cutting a path at edge [i] strands everything above it. *)
Lemma path_split :
  forall n i, i < n ->
    path n = path i ++ (i, S i) :: map (fun j => (j, S j)) (seq (S i) (n - S i)).
Proof.
  intros n i Hi; unfold path.
  replace n with (i + (n - i)) at 1 by lia.
  rewrite seq_app, map_app; f_equal.
  replace (n - i) with (S (n - S i)) by lia.
  rewrite Nat.add_0_l; reflexivity.
Qed.

Lemma drop_at_path :
  forall n i, i < n ->
    drop_at i (path n) = path i ++ map (fun j => (j, S j)) (seq (S i) (n - S i)).
Proof.
  intros n i Hi; unfold drop_at.
  rewrite (path_split n i Hi) at 1 2.
  rewrite firstn_app, skipn_app, path_length.
  rewrite firstn_all2 by (rewrite path_length; lia).
  rewrite skipn_all2 by (rewrite path_length; lia).
  rewrite Nat.sub_diag.
  replace (S i - i) with 1 by lia.
  cbn [firstn skipn app].
  rewrite app_nil_r; reflexivity.
Qed.

(** Above the cut nothing is joined to the ground. *)
Lemma drop_at_path_edges :
  forall n i e, i < n -> In e (drop_at i (path n)) ->
    exists j, e = (j, S j) /\ (j < i \/ i < j).
Proof.
  intros n i e Hi He; rewrite (drop_at_path n i Hi) in He.
  apply in_app_or in He; destruct He as [He | He].
  - apply in_path in He; destruct He as [j [Hj ->]]; exists j; auto.
  - apply in_map_iff in He; destruct He as [j [<- Hj]].
    apply in_seq in Hj; exists j; split; auto; lia.
Qed.

Lemma drop_at_path_cut :
  forall n i v, i < n -> walk (drop_at i (path n)) ground v -> v <= i.
Proof.
  intros n i v Hi Hw.
  assert (Hcl : forall e a b,
             In e (drop_at i (path n)) -> joins e a b -> a <= i -> b <= i).
  { intros e a b He Hj Ha.
    destruct (drop_at_path_edges n i e Hi He) as [j [-> Hj']].
    unfold joins in Hj; cbn [fst snd] in Hj.
    destruct Hj as [[-> ->] | [-> ->]]; lia. }
  apply (walk_closed (drop_at i (path n)) (fun x => x <= i) Hcl ground v Hw).
  unfold ground; lia.
Qed.

Lemma not_connected_above :
  forall n i v, i < n -> i < v -> connected (drop_at i (path n)) v = false.
Proof.
  intros n i v Hi Hv.
  destruct (connected (drop_at i (path n)) v) eqn:E; auto.
  exfalso; apply connected_walk, walk_sym in E.
  pose proof (drop_at_path_cut n i v Hi E); lia.
Qed.

Lemma walk_drop_at_path :
  forall n i j, i < n -> j <= i -> walk (drop_at i (path n)) ground j.
Proof.
  intros n i j Hi; induction j as [|j IH]; intros Hj; [constructor|].
  apply (walk_trans (drop_at i (path n)) ground j (S j)); [apply IH; lia|].
  apply (walk_step (drop_at i (path n)) j (S j) (S j) (j, S j)).
  - rewrite (drop_at_path n i Hi); apply in_or_app; left.
    apply path_edge_in; lia.
  - unfold joins; cbn [fst snd]; left; auto.
  - constructor.
Qed.

Lemma connected_drop_at_path :
  forall n i j, i < n -> j <= i -> connected (drop_at i (path n)) j = true.
Proof.
  intros n i j Hi Hj; apply connected_complete, walk_drop_at_path; lia.
Qed.

(** What survives the cut is the path below it. *)
Lemma prune_drop_at_path :
  forall n i, i < n -> prune (drop_at i (path n)) = path i.
Proof.
  intros n i Hi; unfold prune.
  rewrite (drop_at_path n i Hi) at 1 2.
  rewrite filter_app.
  rewrite filter_all with (l := path i).
  - rewrite filter_none with (l := map (fun j => (j, S j)) (seq (S i) (n - S i))).
    + apply app_nil_r.
    + intros e He; apply in_map_iff in He; destruct He as [j [<- Hj]].
      apply in_seq in Hj.
      unfold live; cbn [fst snd].
      rewrite <- (drop_at_path n i Hi).
      rewrite (not_connected_above n i j Hi) by lia.
      rewrite (not_connected_above n i (S j) Hi) by lia.
      reflexivity.
  - intros e He; apply in_path in He; destruct He as [j [Hj ->]].
    unfold live; cbn [fst snd].
    rewrite <- (drop_at_path n i Hi).
    rewrite (connected_drop_at_path n i j Hi) by lia; reflexivity.
Qed.

(** Every move on a path shortens it, and every shorter path is a move. *)
Lemma moves_path : forall n, moves (path n) = map path (seq 0 n).
Proof.
  intros n; unfold moves; rewrite path_length.
  rewrite filter_all by
    (intros i Hi; apply in_seq in Hi; apply live_path, nth_In;
     rewrite path_length; lia).
  apply map_ext_in; intros i Hi; apply in_seq in Hi.
  apply prune_drop_at_path; lia.
Qed.

Lemma mex_seq : forall n, mex (seq 0 n) = n.
Proof.
  intros n; apply mex_unique.
  - intros H; apply in_seq in H; lia.
  - intros x Hx; apply in_seq; lia.
Qed.

(** A green path from the ground is a Nim heap of its length. *)
Theorem gval_path : forall n, gval (path n) = n.
Proof.
  assert (Haux : forall N n, n <= N -> gval (path n) = n).
  { induction N as [|N IH]; intros n Hn.
    - assert (n = 0) as -> by lia; apply gval_nil.
    - rewrite gval_eq, moves_path, map_map.
      rewrite map_ext_in with (g := fun i => i).
      + rewrite map_id; apply mex_seq.
      + intros i Hi; apply in_seq in Hi; apply IH; lia. }
  intros n; apply (Haux n); lia.
Qed.

(** * Positions meeting only at the ground *)

Definition occurs (v : vertex) (g : graph) : Prop :=
  exists e, In e g /\ incident v e = true.

(** Two positions are separate when they share no vertex but the ground. *)
Definition sep (g1 g2 : graph) : Prop :=
  forall v, occurs v g1 -> occurs v g2 -> v = ground.

Lemma sep_sym : forall g1 g2, sep g1 g2 -> sep g2 g1.
Proof. intros g1 g2 H v H1 H2; apply H; auto. Qed.

Lemma occurs_incl :
  forall v g g', incl g g' -> occurs v g -> occurs v g'.
Proof.
  intros v g g' Hi [e [He Hin]]; exists e; split; auto.
Qed.

Lemma sep_incl_l :
  forall g1 g1' g2, incl g1' g1 -> sep g1 g2 -> sep g1' g2.
Proof.
  intros g1 g1' g2 Hi H v H1 H2; apply H; auto.
  apply (occurs_incl v g1' g1); auto.
Qed.

Lemma joins_occurs :
  forall e a b g, In e g -> joins e a b -> occurs a g /\ occurs b g.
Proof.
  intros e a b g He Hj; split; exists e; split; auto;
    apply incident_true_iff; unfold joins in Hj; tauto.
Qed.

(** A walk that starts on one side of a separation stays there until it
    reaches the ground. *)
Lemma walk_app_left :
  forall g1 g2 v,
    sep g1 g2 -> (v = ground \/ occurs v g1) ->
    walk (g1 ++ g2) v ground -> walk g1 v ground.
Proof.
  intros g1 g2 v Hs Hv Hw.
  remember (g1 ++ g2) as g eqn:Eg; remember ground as z eqn:Ez.
  revert Hv Eg Ez; induction Hw as [|a b c e He Hj Hwk IH];
    intros Hv Eg Ez.
  - subst; constructor.
  - subst c; subst g.
    apply in_app_or in He; destruct He as [He | He].
    + apply (walk_step g1 a b ground e); auto.
      apply IH; auto.
      right; apply (proj2 (joins_occurs e a b g1 He Hj)).
    + assert (Ha : a = ground).
      { destruct Hv as [-> | Ho]; auto.
        apply Hs; auto.
        apply (proj1 (joins_occurs e a b g2 He Hj)). }
      subst a; constructor.
Qed.

Lemma walk_app_mono :
  forall g1 g2 v w, walk g1 v w -> walk (g1 ++ g2) v w.
Proof.
  intros g1 g2 v w H; induction H as [|a b c e He Hj Hw IH]; [constructor|].
  apply (walk_step (g1 ++ g2) a b c e); auto; apply in_or_app; left; exact He.
Qed.

Lemma walk_app_comm :
  forall g1 g2 v w, walk (g1 ++ g2) v w -> walk (g2 ++ g1) v w.
Proof.
  intros g1 g2 v w H; induction H as [|a b c e He Hj Hw IH]; [constructor|].
  apply (walk_step (g2 ++ g1) a b c e); auto.
  apply in_app_or in He; apply in_or_app; tauto.
Qed.

Lemma connected_app_left :
  forall g1 g2 v,
    sep g1 g2 -> (v = ground \/ occurs v g1) ->
    connected (g1 ++ g2) v = connected g1 v.
Proof.
  intros g1 g2 v Hs Hv.
  destruct (connected g1 v) eqn:E1.
  - apply connected_iff in E1; apply connected_iff, walk_app_mono; exact E1.
  - destruct (connected (g1 ++ g2) v) eqn:E2; auto.
    apply connected_iff in E2.
    pose proof (walk_app_left g1 g2 v Hs Hv E2) as Hw.
    apply connected_iff in Hw; congruence.
Qed.

Lemma connected_app_comm :
  forall g1 g2 v, connected (g1 ++ g2) v = connected (g2 ++ g1) v.
Proof.
  intros g1 g2 v.
  destruct (connected (g1 ++ g2) v) eqn:E1; destruct (connected (g2 ++ g1) v) eqn:E2;
    auto.
  - apply connected_iff in E1; apply walk_app_comm in E1.
    apply connected_iff in E1; congruence.
  - apply connected_iff in E2; apply walk_app_comm in E2.
    apply connected_iff in E2; congruence.
Qed.

Lemma live_app_left :
  forall g1 g2 e,
    sep g1 g2 -> In e g1 -> live (g1 ++ g2) e = live g1 e.
Proof.
  intros g1 g2 e Hs He; unfold live.
  rewrite (connected_app_left g1 g2 (fst e) Hs),
          (connected_app_left g1 g2 (snd e) Hs); auto;
    right; exists e; split; auto; apply incident_true_iff; auto.
Qed.

Lemma live_app_right :
  forall g1 g2 e,
    sep g1 g2 -> In e g2 -> live (g1 ++ g2) e = live g2 e.
Proof.
  intros g1 g2 e Hs He; unfold live.
  rewrite (connected_app_comm g1 g2 (fst e)), (connected_app_comm g1 g2 (snd e)).
  rewrite (connected_app_left g2 g1 (fst e) (sep_sym g1 g2 Hs)),
          (connected_app_left g2 g1 (snd e) (sep_sym g1 g2 Hs)); auto;
    right; exists e; split; auto; apply incident_true_iff; auto.
Qed.

Lemma prune_app :
  forall g1 g2, sep g1 g2 -> prune (g1 ++ g2) = prune g1 ++ prune g2.
Proof.
  intros g1 g2 Hs; unfold prune; rewrite filter_app; f_equal.
  - apply filter_ext_in; intros e He; apply live_app_left; auto.
  - apply filter_ext_in; intros e He; apply live_app_right; auto.
Qed.

(** * Independent positions add *)

Lemma drop_at_app_left :
  forall i g1 g2, i < length g1 -> drop_at i (g1 ++ g2) = drop_at i g1 ++ g2.
Proof.
  intros i g1 g2 Hi; unfold drop_at.
  rewrite firstn_app, skipn_app.
  replace (i - length g1) with 0 by lia.
  replace (S i - length g1) with 0 by lia.
  rewrite firstn_O, skipn_O.
  rewrite app_assoc, app_nil_r; reflexivity.
Qed.

Lemma drop_at_app_right :
  forall j g1 g2, drop_at (length g1 + j) (g1 ++ g2) = g1 ++ drop_at j g2.
Proof.
  intros j g1 g2; unfold drop_at.
  rewrite firstn_app, skipn_app.
  replace (length g1 + j - length g1) with j by lia.
  replace (firstn (length g1 + j) g1) with g1
    by (symmetry; apply firstn_all2; lia).
  replace (S (length g1 + j)) with (length g1 + S j) by lia.
  replace (skipn (length g1 + S j) g1) with (@nil edge)
    by (symmetry; apply skipn_all2; lia).
  replace (length g1 + S j - length g1) with (S j) by lia.
  rewrite app_nil_l, app_assoc; reflexivity.
Qed.

Lemma nth_app_left :
  forall i (g1 g2 : graph) (d : edge),
    i < length g1 -> nth i (g1 ++ g2) d = nth i g1 d.
Proof. intros i g1 g2 d Hi; apply app_nth1; exact Hi. Qed.

Lemma nth_app_right :
  forall j (g1 g2 : graph) (d : edge),
    nth (length g1 + j) (g1 ++ g2) d = nth j g2 d.
Proof. intros j g1 g2 d; apply app_nth2_plus. Qed.

Lemma in_firstn : forall {A : Type} n (l : list A) x, In x (firstn n l) -> In x l.
Proof.
  intros A n l x H; rewrite <- (firstn_skipn n l); apply in_or_app; left; exact H.
Qed.

Lemma in_skipn : forall {A : Type} n (l : list A) x, In x (skipn n l) -> In x l.
Proof.
  intros A n l x H; rewrite <- (firstn_skipn n l); apply in_or_app; right; exact H.
Qed.

Lemma drop_at_incl : forall i g, incl (drop_at i g) g.
Proof.
  intros i g e He; unfold drop_at in He; apply in_app_or in He.
  destruct He as [He | He];
    [apply (in_firstn i); exact He | apply (in_skipn (S i)); exact He].
Qed.

Lemma seq_offset : forall a n, seq a n = map (fun j => a + j) (seq 0 n).
Proof.
  intros a n; revert a; induction n as [|n IH]; intros a; simpl; auto.
  rewrite Nat.add_0_r; f_equal.
  rewrite (IH (S a)), <- seq_shift, map_map.
  apply map_ext; intros j; lia.
Qed.

Lemma filter_map_comm :
  forall {A B : Type} (f : B -> bool) (h : A -> B) (l : list A),
    filter f (map h l) = map h (filter (fun x => f (h x)) l).
Proof.
  intros A B f h l; induction l as [|a l IH]; simpl; auto.
  destruct (f (h a)); simpl; [f_equal|]; exact IH.
Qed.

(** The moves of two separate positions are the moves of each, with the other
    left alone. *)
Lemma moves_app :
  forall g1 g2,
    sep g1 g2 -> prune g1 = g1 -> prune g2 = g2 ->
    moves (g1 ++ g2) =
    map (fun g1' => g1' ++ g2) (moves g1) ++
    map (fun g2' => g1 ++ g2') (moves g2).
Proof.
  intros g1 g2 Hs Hp1 Hp2; unfold moves.
  rewrite length_app, seq_app, filter_app, map_app.
  f_equal.
  - rewrite (filter_ext_in _ (fun i => live g1 (nth i g1 (0, 0)))).
    + rewrite !map_map; apply map_ext_in; intros i Hi.
      apply filter_In in Hi; destruct Hi as [Hi _]; apply in_seq in Hi.
      rewrite drop_at_app_left by lia.
      rewrite (prune_app (drop_at i g1) g2); [f_equal; exact Hp2|].
      apply (sep_incl_l g1); auto; apply drop_at_incl.
    + intros i Hi; apply in_seq in Hi.
      rewrite nth_app_left by lia.
      apply live_app_left; auto; apply nth_In; lia.
  - rewrite Nat.add_0_l.
    rewrite (seq_offset (length g1) (length g2)).
    rewrite filter_map_comm, map_map, !map_map.
    rewrite (filter_ext_in
               (fun x => live (g1 ++ g2) (nth (length g1 + x) (g1 ++ g2) (0, 0)))
               (fun j => live g2 (nth j g2 (0, 0)))).
    + apply map_ext_in; intros j Hj.
      apply filter_In in Hj; destruct Hj as [Hj _]; apply in_seq in Hj.
      rewrite drop_at_app_right.
      rewrite (prune_app g1 (drop_at j g2)); [f_equal; exact Hp1|].
      apply sep_sym; apply (sep_incl_l g2);
        [apply drop_at_incl | apply sep_sym; exact Hs].
    + intros j Hj; apply in_seq in Hj.
      rewrite nth_app_right.
      apply live_app_right; auto; apply nth_In; lia.
Qed.

(** Pruning keeps a position pruned: an edge that reaches the ground does so
    along edges that reach the ground. *)
Lemma walk_prune :
  forall g v, walk g v ground -> walk (prune g) v ground.
Proof.
  intros g v Hw.
  remember ground as z eqn:Ez.
  induction Hw as [|a b c e He Hj Hwk IH]; [subst; constructor|].
  subst c; specialize (IH eq_refl).
  apply (walk_step (prune g) a b ground e); auto.
  unfold prune; apply filter_In; split; [exact He|].
  unfold live.
  assert (Hb : connected g b = true)
    by (apply connected_iff; exact Hwk).
  destruct Hj as [[-> ->] | [-> ->]]; cbn [fst snd].
  - rewrite Hb, orb_true_r; reflexivity.
  - rewrite Hb; reflexivity.
Qed.

Lemma prune_idem : forall g, prune (prune g) = prune g.
Proof.
  intros g; unfold prune at 1; apply filter_all; intros e He.
  pose proof He as He'; unfold prune in He'; apply filter_In in He'.
  destruct He' as [Heg Hlive]; unfold live in Hlive |- *.
  apply orb_true_iff in Hlive; destruct Hlive as [Hc | Hc];
    apply connected_iff, walk_prune, connected_iff in Hc;
    rewrite Hc; [reflexivity | apply orb_true_r].
Qed.

Lemma moves_pruned :
  forall g g', In g' (moves g) -> prune g' = g'.
Proof.
  intros g g' H; apply in_moves in H.
  destruct H as [i [_ [_ ->]]]; apply prune_idem.
Qed.

Lemma sep_moves_l :
  forall g1 g2 g1', sep g1 g2 -> In g1' (moves g1) -> sep g1' g2.
Proof.
  intros g1 g2 g1' Hs H; apply in_moves in H.
  destruct H as [i [_ [_ ->]]].
  apply (sep_incl_l g1); auto.
  intros e He; apply prune_incl in He; apply drop_at_incl in He; exact He.
Qed.

(** The game of two separate positions is the disjunctive sum of their games. *)
Theorem Hb_app :
  forall g1 g2,
    sep g1 g2 -> prune g1 = g1 -> prune g2 = g2 ->
    Hb (g1 ++ g2) = tsum (Hb g1) (Hb g2).
Proof.
  assert (Haux : forall N g1 g2,
             length g1 + length g2 <= N ->
             sep g1 g2 -> prune g1 = g1 -> prune g2 = g2 ->
             Hb (g1 ++ g2) = tsum (Hb g1) (Hb g2)).
  { induction N as [|N IH]; intros g1 g2 HN Hs Hp1 Hp2.
    - assert (Hg1 : g1 = []) by (apply length_zero_iff_nil; lia).
      assert (Hg2 : g2 = []) by (apply length_zero_iff_nil; lia).
      subst; reflexivity.
    - rewrite (Hb_eq (g1 ++ g2)).
      rewrite (moves_app g1 g2 Hs Hp1 Hp2), map_app, !map_map.
      transitivity (tsum (node tt (map Hb (moves g1))) (node tt (map Hb (moves g2)))).
      2: { rewrite <- (Hb_eq g1), <- (Hb_eq g2); reflexivity. }
      rewrite tsum_eq, !map_map.
      f_equal; f_equal.
      + apply map_ext_in; intros g1' Hg1'.
        rewrite <- (Hb_eq g2).
        apply IH.
        * pose proof (moves_shorter g1 g1' Hg1'); lia.
        * apply (sep_moves_l g1 g2); auto.
        * apply (moves_pruned g1); exact Hg1'.
        * exact Hp2.
      + apply map_ext_in; intros g2' Hg2'.
        rewrite <- (Hb_eq g1).
        apply IH.
        * pose proof (moves_shorter g2 g2' Hg2'); lia.
        * apply sep_sym; apply (sep_moves_l g2 g1); auto; apply sep_sym; auto.
        * exact Hp1.
        * apply (moves_pruned g2); exact Hg2'. }
  intros g1 g2; apply (Haux (length g1 + length g2)); lia.
Qed.

(** Separate positions add by exclusive or, as disjunctive sums do. *)
Theorem gval_app :
  forall g1 g2,
    sep g1 g2 -> prune g1 = g1 -> prune g2 = g2 ->
    gval (g1 ++ g2) = Nat.lxor (gval g1) (gval g2).
Proof.
  intros g1 g2 Hs Hp1 Hp2; unfold gval.
  rewrite (Hb_app g1 g2 Hs Hp1 Hp2); apply grundy_tsum.
Qed.

(** * The arc left above a cut *)

(** The edges above [i] on a cycle of [m] path edges, together with the edge
    that closes the cycle at the ground. *)
Definition arc (i m : nat) : graph :=
  map (fun j => (j, S j)) (seq (S i) (m - S i)) ++ [(m, ground)].

Lemma arc_length : forall i m, i < m -> length (arc i m) = m - i.
Proof.
  intros i m Hi; unfold arc.
  rewrite length_app, length_map, length_seq; cbn [length]; lia.
Qed.

Lemma in_arc :
  forall i m e,
    In e (arc i m) <->
    e = (m, ground) \/ exists j, S i <= j < m /\ e = (j, S j).
Proof.
  intros i m e; unfold arc; rewrite in_app_iff; split.
  - intros [He | He].
    + right; apply in_map_iff in He; destruct He as [j [<- Hj]].
      apply in_seq in Hj; exists j; split; auto; lia.
    + left; destruct He as [<- | []]; reflexivity.
  - intros [-> | [j [Hj ->]]].
    + right; simpl; auto.
    + left; apply in_map_iff; exists j; split; auto; apply in_seq; lia.
Qed.

Lemma arc_edge_in :
  forall i m j, S i <= j < m -> In (j, S j) (arc i m).
Proof. intros i m j Hj; apply in_arc; right; exists j; auto. Qed.

Lemma arc_close_in : forall i m, In (m, ground) (arc i m).
Proof. intros i m; apply in_arc; left; reflexivity. Qed.

(** Walking up the arc from the ground. *)
Lemma walk_arc :
  forall i m k, i < m -> i < k <= m -> walk (arc i m) ground k.
Proof.
  intros i m k Hi Hk.
  assert (Haux : forall d, d <= m - k -> walk (arc i m) ground (k + d) ->
                   walk (arc i m) ground k).
  { intros d; induction d as [|d IH]; intros Hd Hw.
    - rewrite Nat.add_0_r in Hw; exact Hw.
    - apply IH; [lia|].
      apply (walk_trans (arc i m) ground (k + S d) (k + d)); [exact Hw|].
      apply (walk_step (arc i m) (k + S d) (k + d) (k + d) (k + d, S (k + d))).
      + apply arc_edge_in; lia.
      + unfold joins; cbn [fst snd]; right; split; auto; lia.
      + constructor. }
  apply (Haux (m - k)); [lia|].
  replace (k + (m - k)) with m by lia.
  apply (walk_step (arc i m) ground m m (m, ground)).
  - apply arc_close_in.
  - unfold joins; cbn [fst snd]; right; auto.
  - constructor.
Qed.

Lemma connected_arc :
  forall i m k, i < m -> i < k <= m -> connected (arc i m) k = true.
Proof. intros i m k Hi Hk; apply connected_complete, walk_arc; auto. Qed.

Lemma live_arc : forall i m e, i < m -> In e (arc i m) -> live (arc i m) e = true.
Proof.
  intros i m e Hi He; unfold live.
  apply in_arc in He; destruct He as [-> | [j [Hj ->]]]; cbn [fst snd].
  - rewrite (connected_arc i m m Hi) by lia; reflexivity.
  - rewrite (connected_arc i m j Hi) by lia; reflexivity.
Qed.

Lemma prune_arc : forall i m, i < m -> prune (arc i m) = arc i m.
Proof.
  intros i m Hi; unfold prune; apply filter_all; intros e He.
  apply live_arc; auto.
Qed.

(** Cutting the arc at one of its path edges strands everything below. *)
Lemma arc_split :
  forall i m j,
    S i <= j < m ->
    arc i m =
    map (fun k => (k, S k)) (seq (S i) (j - S i)) ++ (j, S j) :: arc j m.
Proof.
  intros i m j Hj; unfold arc.
  replace (m - S i) with ((j - S i) + (m - j)) by lia.
  rewrite seq_app, map_app, <- app_assoc; f_equal.
  replace (S i + (j - S i)) with j by lia.
  replace (m - j) with (S (m - S j)) by lia.
  cbn [seq map]; reflexivity.
Qed.

Lemma arc_drop_at :
  forall i m j,
    S i <= j < m ->
    drop_at (j - S i) (arc i m) =
    map (fun k => (k, S k)) (seq (S i) (j - S i)) ++ arc j m.
Proof.
  intros i m j Hj.
  rewrite (arc_split i m j Hj) at 1.
  unfold drop_at.
  rewrite firstn_app, skipn_app, length_map, length_seq.
  rewrite firstn_all2 by (rewrite length_map, length_seq; lia).
  rewrite skipn_all2 by (rewrite length_map, length_seq; lia).
  rewrite Nat.sub_diag.
  replace (S (j - S i) - (j - S i)) with 1 by lia.
  cbn [firstn skipn].
  rewrite app_nil_r; reflexivity.
Qed.

Lemma arc_drop_close :
  forall i m,
    i < m ->
    drop_at (m - S i) (arc i m) = map (fun k => (k, S k)) (seq (S i) (m - S i)).
Proof.
  intros i m Hi; unfold arc, drop_at.
  rewrite firstn_app, skipn_app, length_map, length_seq.
  rewrite firstn_all2 by (rewrite length_map, length_seq; lia).
  rewrite skipn_all2 by (rewrite length_map, length_seq; lia).
  rewrite Nat.sub_diag.
  replace (S (m - S i) - (m - S i)) with 1 by lia.
  cbn [firstn skipn].
  rewrite !app_nil_r; reflexivity.
Qed.

(** Nothing above the cut keeps its hold on the ground. *)
Lemma stranded_cut :
  forall a n v,
    walk (map (fun k => (k, S k)) (seq (S a) n)) ground v -> v = ground.
Proof.
  intros a n v Hw.
  destruct (Nat.eq_dec v ground) as [-> | Hne]; [reflexivity|].
  exfalso.
  assert (Hno : forall e b c,
             In e (map (fun k => (k, S k)) (seq (S a) n)) ->
             joins e b c -> b = ground -> False).
  { intros e b c He Hj Hb.
    apply in_map_iff in He; destruct He as [k [<- Hk]].
    apply in_seq in Hk.
    unfold joins, ground in Hj, Hb; cbn [fst snd] in Hj.
    destruct Hj as [[Hb' ->] | [Hb' ->]]; lia. }
  inversion Hw as [|b c d e He Hj Hwk]; subst; [contradiction|].
  apply (Hno e ground c He Hj); reflexivity.
Qed.

Lemma prune_stranded_seg :
  forall a n, prune (map (fun k => (k, S k)) (seq (S a) n)) = [].
Proof.
  intros a n; unfold prune.
  apply filter_none; intros e He.
  pose proof He as He'.
  apply in_map_iff in He'; destruct He' as [k [<- Hk]].
  apply in_seq in Hk.
  unfold live; cbn [fst snd].
  destruct (connected (map (fun k0 => (k0, S k0)) (seq (S a) n)) k) eqn:E1.
  - apply connected_iff, walk_sym in E1.
    apply (stranded_cut a n) in E1; unfold ground in E1; lia.
  - destruct (connected (map (fun k0 => (k0, S k0)) (seq (S a) n)) (S k)) eqn:E2;
      [|reflexivity].
    apply connected_iff, walk_sym in E2.
    apply (stranded_cut a n) in E2; unfold ground in E2; lia.
Qed.

(** The moves on an arc: cut a path edge and lose everything below it, or cut
    the closing edge and lose the lot. *)
Lemma moves_arc :
  forall i m,
    i < m ->
    moves (arc i m) = map (fun j => arc j m) (seq (S i) (m - S i)) ++ [[]].
Proof.
  intros i m Hi; unfold moves.
  rewrite (arc_length i m Hi).
  rewrite filter_all by
    (intros k Hk; apply in_seq in Hk; apply live_arc; auto;
     apply nth_In; rewrite arc_length by lia; lia).
  replace (m - i) with (S (m - S i)) by lia.
  rewrite seq_S, map_app; f_equal.
  - rewrite (seq_offset (S i) (m - S i)), map_map.
    apply map_ext_in; intros k Hk; apply in_seq in Hk.
    pose proof (arc_drop_at i m (S i + k)) as Hd.
    replace (S i + k - S i) with k in Hd by lia.
    rewrite Hd by lia.
    rewrite prune_app.
    + rewrite prune_stranded_seg, (prune_arc (S i + k) m) by lia; reflexivity.
    + intros v Hv1 Hv2.
      destruct Hv1 as [e1 [He1 Hi1]]; destruct Hv2 as [e2 [He2 Hi2]].
      apply in_map_iff in He1; destruct He1 as [a [<- Ha]]; apply in_seq in Ha.
      apply incident_true_iff in Hi1; cbn [fst snd] in Hi1.
      apply in_arc in He2; apply incident_true_iff in Hi2.
      destruct He2 as [-> | [b [Hb ->]]]; cbn [fst snd] in Hi2;
        unfold ground in *; lia.
  - cbn [map seq app].
    rewrite Nat.add_0_l, (arc_drop_close i m Hi).
    rewrite prune_stranded_seg; reflexivity.
Qed.

(** An arc is the Nim heap of its length. *)
Theorem gval_arc : forall i m, i < m -> gval (arc i m) = m - i.
Proof.
  assert (Haux : forall N i m, m - i <= N -> i < m -> gval (arc i m) = m - i).
  { induction N as [|N IH]; intros i m HN Hi; [lia|].
    rewrite gval_eq, (moves_arc i m Hi), map_app, map_map.
    apply mex_unique.
    - intros H; apply in_app_iff in H; destruct H as [H | H].
      + apply in_map_iff in H; destruct H as [j [Hv Hj]]; apply in_seq in Hj.
        rewrite (IH j m) in Hv by lia; lia.
      + destruct H as [H | []]; rewrite gval_nil in H; lia.
    - intros x Hx; apply in_app_iff.
      destruct (Nat.eq_dec x 0) as [-> | Hx0].
      + right; left; symmetry; apply gval_nil.
      + left; apply in_map_iff; exists (m - x); split.
        * rewrite (IH (m - x) m) by lia; lia.
        * apply in_seq; lia. }
  intros i m Hi; apply (Haux (m - i)); lia.
Qed.

(** * Cycles through the ground *)

(** The cycle [0 - 1 - ... - m - 0], with [S m] edges. *)
Definition cyc (m : nat) : graph := path m ++ [(m, ground)].

Lemma cyc_length : forall m, length (cyc m) = S m.
Proof.
  intros m; unfold cyc; rewrite length_app, path_length; cbn [length]; lia.
Qed.

(** Cutting a cycle anywhere leaves two arms meeting at the ground. *)
Lemma cyc_drop_path :
  forall m i, i < m -> drop_at i (cyc m) = path i ++ arc i m.
Proof.
  intros m i Hi; unfold cyc.
  rewrite drop_at_app_left by (rewrite path_length; lia).
  rewrite (drop_at_path m i Hi), <- app_assoc; reflexivity.
Qed.

Lemma cyc_drop_close :
  forall m, drop_at m (cyc m) = path m.
Proof.
  intros m; unfold cyc.
  replace m with (length (path m) + 0) at 1 by (rewrite path_length; lia).
  rewrite drop_at_app_right; cbn [drop_at firstn skipn app].
  rewrite app_nil_r; reflexivity.
Qed.

Lemma sep_path_arc : forall i m, i < m -> sep (path i) (arc i m).
Proof.
  intros i m Hi v Hv1 Hv2.
  destruct Hv1 as [e1 [He1 Hin1]]; destruct Hv2 as [e2 [He2 Hin2]].
  apply in_path in He1; destruct He1 as [a [Ha ->]].
  apply incident_true_iff in Hin1; cbn [fst snd] in Hin1.
  apply in_arc in He2; apply incident_true_iff in Hin2.
  destruct He2 as [-> | [b [Hb ->]]]; cbn [fst snd] in Hin2;
    unfold ground in *; lia.
Qed.

(** So a cut cycle is worth the exclusive or of the two arms. *)
Lemma gval_cyc_cut :
  forall m i, i < m -> gval (prune (drop_at i (cyc m))) = Nat.lxor i (m - i).
Proof.
  intros m i Hi.
  rewrite (cyc_drop_path m i Hi).
  rewrite (prune_app (path i) (arc i m) (sep_path_arc i m Hi)).
  rewrite (prune_path i), (prune_arc i m Hi).
  rewrite (gval_app (path i) (arc i m) (sep_path_arc i m Hi)
             (prune_path i) (prune_arc i m Hi)).
  rewrite gval_path, (gval_arc i m Hi); reflexivity.
Qed.

Lemma live_cyc : forall m e, In e (cyc m) -> live (cyc m) e = true.
Proof.
  intros m e He; unfold cyc in He; apply in_app_iff in He.
  assert (Hw : forall k, k <= m -> connected (cyc m) k = true).
  { intros k Hk; apply connected_complete.
    unfold cyc; apply walk_app_mono; apply walk_path; lia. }
  destruct He as [He | He].
  - apply in_path in He; destruct He as [j [Hj ->]].
    unfold live; cbn [fst snd]; rewrite (Hw j) by lia; reflexivity.
  - destruct He as [<- | []].
    unfold live; cbn [fst snd]; rewrite (Hw m) by lia; reflexivity.
Qed.

Lemma moves_cyc :
  forall m,
    0 < m ->
    moves (cyc m) = map (fun i => prune (drop_at i (cyc m))) (seq 0 (S m)).
Proof.
  intros m Hm; unfold moves; rewrite cyc_length.
  rewrite filter_all by
    (intros i Hi; apply in_seq in Hi; apply live_cyc, nth_In;
     rewrite cyc_length; lia).
  reflexivity.
Qed.

(** The option values of a cycle: the two arms, exclusive-ored. *)
Lemma gval_cyc_options :
  forall m,
    0 < m ->
    map gval (moves (cyc m)) = map (fun i => Nat.lxor i (m - i)) (seq 0 (S m)).
Proof.
  intros m Hm; rewrite (moves_cyc m Hm), map_map.
  apply map_ext_in; intros i Hi; apply in_seq in Hi.
  destruct (Nat.eq_dec i m) as [-> | Hne].
  - rewrite cyc_drop_close, prune_path, gval_path.
    rewrite Nat.sub_diag, Nat.lxor_0_r; reflexivity.
  - apply gval_cyc_cut; lia.
Qed.

(** The arithmetic behind the fusion of a cycle: the values [i xor (m - i)]
    miss zero exactly when [m] is odd, and never hit one when [m] is even,
    since [i] and [m - i] then share a parity. *)
Lemma lxor_parity :
  forall i m, i <= m -> Nat.odd (Nat.lxor i (m - i)) = Nat.odd m.
Proof.
  intros i m Hi.
  assert (Hm : Nat.odd m = xorb (Nat.odd i) (Nat.odd (m - i))).
  { replace m with (i + (m - i)) at 1 by lia; apply Nat.odd_add. }
  rewrite Hm, <- (Nat.bit0_odd (Nat.lxor i (m - i))), Nat.lxor_spec.
  rewrite !Nat.bit0_odd; reflexivity.
Qed.

Lemma mex_cycle_values :
  forall m,
    0 < m ->
    mex (map (fun i => Nat.lxor i (m - i)) (seq 0 (S m))) =
    if Nat.even m then 1 else 0.
Proof.
  intros m Hm.
  destruct (Nat.even m) eqn:Em.
  - apply mex_unique.
    + intros H; apply in_map_iff in H.
      destruct H as [i [Hv Hi]]; apply in_seq in Hi.
      pose proof (lxor_parity i m) as Hp.
      rewrite Hv in Hp.
      rewrite <- (Nat.negb_even m), Em in Hp; cbn in Hp.
      discriminate (Hp ltac:(lia)).
    + intros x Hx; assert (x = 0) as -> by lia.
      apply in_map_iff; exists (Nat.div2 m); split.
      * assert (Hd : m = 2 * Nat.div2 m).
        { pose proof (Nat.div2_odd m) as Hdo.
          rewrite <- (Nat.negb_even m), Em in Hdo; cbn [negb Nat.b2n] in Hdo.
          lia. }
        replace (m - Nat.div2 m) with (Nat.div2 m) by lia.
        apply Nat.lxor_nilpotent.
      * assert (Hd : m = 2 * Nat.div2 m).
        { pose proof (Nat.div2_odd m) as Hdo.
          rewrite <- (Nat.negb_even m), Em in Hdo; cbn [negb Nat.b2n] in Hdo.
          lia. }
        apply in_seq; lia.
  - apply mex_unique.
    + intros H; apply in_map_iff in H.
      destruct H as [i [Hv Hi]]; apply in_seq in Hi.
      pose proof (lxor_parity i m ltac:(lia)) as Hp.
      rewrite Hv in Hp; cbn in Hp.
      rewrite <- (Nat.negb_even m), Em in Hp; cbn in Hp; discriminate.
    + intros x Hx; lia.
Qed.

(** * Fusion *)

(** Fusing the vertices of a cycle through the ground turns each of its edges
    into a loop there, and the value does not notice. *)
Theorem gval_cyc :
  forall m, 0 < m -> gval (cyc m) = if Nat.even m then 1 else 0.
Proof.
  intros m Hm.
  rewrite gval_eq, (gval_cyc_options m Hm).
  apply mex_cycle_values; exact Hm.
Qed.

Theorem fusion_cycle :
  forall m, 0 < m -> gval (cyc m) = gval (loops (S m)).
Proof.
  intros m Hm; rewrite (gval_cyc m Hm), gval_loops.
  rewrite Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even m); reflexivity.
Qed.

(** * Fusion *)

(** [k] edges joining the ground to a single vertex. Any two of them close a
    cycle through both endpoints, so the fusion principle says this position
    should be worth the same as [k] loops at the ground. *)
Definition par (k : nat) : graph := repeat (ground, 1) k.

Lemma par_length : forall k, length (par k) = k.
Proof. intros k; apply repeat_length. Qed.

Lemma in_par : forall k e, In e (par k) -> e = (ground, 1).
Proof. intros k e H; apply repeat_spec in H; exact H. Qed.

Lemma live_par : forall k e, In e (par k) -> live (par k) e = true.
Proof.
  intros k e He; rewrite (in_par k e He); unfold live; cbn [fst snd].
  rewrite connected_ground; reflexivity.
Qed.

Lemma prune_par : forall k, prune (par k) = par k.
Proof.
  intros k; unfold prune; apply filter_all; intros e He; apply live_par; auto.
Qed.

Lemma drop_at_par :
  forall i k, i < k -> drop_at i (par k) = par (k - 1).
Proof.
  intros i k Hi; unfold drop_at, par.
  rewrite firstn_repeat_le by lia.
  rewrite skipn_repeat, <- repeat_app.
  f_equal; lia.
Qed.

Lemma moves_par_nonnil : forall k, moves (par (S k)) <> [].
Proof.
  intros k H.
  assert (Hin : In (prune (drop_at 0 (par (S k)))) (moves (par (S k)))).
  { apply in_moves; exists 0; repeat split;
      try (pose proof (par_length (S k)); lia);
      try (apply live_par, nth_In; pose proof (par_length (S k)); lia). }
  rewrite H in Hin; destruct Hin.
Qed.

Lemma in_moves_par :
  forall k g', In g' (moves (par (S k))) -> g' = par k.
Proof.
  intros k g' H; apply in_moves in H.
  destruct H as [i [Hi [_ ->]]].
  pose proof (par_length (S k)) as Hl; rewrite Hl in Hi.
  rewrite drop_at_par by lia.
  rewrite prune_par; f_equal; lia.
Qed.

Theorem gval_par : forall k, gval (par k) = if Nat.even k then 0 else 1.
Proof.
  induction k as [|k IH].
  - apply gval_nil.
  - rewrite gval_eq.
    rewrite (mex_all_eq (map gval (moves (par (S k))))
               (if Nat.even k then 0 else 1)).
    + rewrite Nat.even_succ, <- Nat.negb_even.
      destruct (Nat.even k); reflexivity.
    + intros H; apply (moves_par_nonnil k); apply map_eq_nil in H; exact H.
    + intros x Hx; apply in_map_iff in Hx.
      destruct Hx as [g' [<- Hg']].
      rewrite (in_moves_par k g' Hg'); exact IH.
Qed.

(** The fusion principle for the endpoints of a cycle of parallel edges:
    identifying the two vertices, which turns every edge into a loop at the
    ground, leaves the value alone. *)
Theorem fusion_parallel : forall k, gval (par k) = gval (loops k).
Proof. intros k; rewrite gval_par, gval_loops; reflexivity. Qed.

(** Both are the Nim heap the fused position names: one edge, or none. *)
Corollary fusion_parallel_value :
  forall k, gval (par k) = if Nat.even k then 0 else 1.
Proof. exact gval_par. Qed.
