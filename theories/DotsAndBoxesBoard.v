(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** The Dots and Boxes board.

    Boxes are indexed [(r, c)] with [r < m] and [c < n]. A horizontal edge
    [EH r c] joins the dots [(r, c)] and [(r, c + 1)]; a vertical edge [EV r c]
    joins [(r, c)] and [(r + 1, c)]. The box [(r, c)] is bounded by [EH r c],
    [EH (S r) c], [EV r c] and [EV r (S c)].

    A move draws an undrawn edge. Completing boxes scores them and grants
    another move, so the player to move is read off the state rather than
    alternating. Play ends when every edge is drawn.

    The counting fact behind the long chain rule is [long_chain_identity]:
    over a completed game the number of turns exceeds the number of dots by
    exactly the number of extra boxes taken by moves that completed two at
    once, that is, by the doublecrosses. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.Determinacy.

(** * Edges *)

Inductive edge : Type :=
| EH : nat -> nat -> edge
| EV : nat -> nat -> edge.

Definition edge_eq_dec : forall e1 e2 : edge, {e1 = e2} + {e1 <> e2}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Definition edge_eqb (e1 e2 : edge) : bool :=
  if edge_eq_dec e1 e2 then true else false.

Lemma edge_eqb_true_iff : forall e1 e2, edge_eqb e1 e2 = true <-> e1 = e2.
Proof.
  intros e1 e2; unfold edge_eqb; destruct (edge_eq_dec e1 e2); split; congruence.
Qed.

Lemma edge_eqb_refl : forall e, edge_eqb e e = true.
Proof. intros e; apply edge_eqb_true_iff; reflexivity. Qed.

Definition emem (e : edge) (l : list edge) : bool := existsb (edge_eqb e) l.

Lemma emem_true_iff : forall e l, emem e l = true <-> In e l.
Proof.
  intros e l; unfold emem; rewrite existsb_exists; split.
  - intros [x [Hx He]]; apply edge_eqb_true_iff in He; subst; auto.
  - intros H; exists e; split; [exact H | apply edge_eqb_refl].
Qed.

Lemma emem_false_iff : forall e l, emem e l = false <-> ~ In e l.
Proof.
  intros e l; split.
  - intros H Hin; apply emem_true_iff in Hin; congruence.
  - intros H; destruct (emem e l) eqn:E; [apply emem_true_iff in E; contradiction
                                         | reflexivity].
Qed.

Lemma emem_cons : forall e f l, emem e (f :: l) = (edge_eqb e f || emem e l)%bool.
Proof. reflexivity. Qed.

Lemma emem_cons_mono :
  forall e f l, emem e l = true -> emem e (f :: l) = true.
Proof.
  intros e f l H; apply emem_true_iff; right; apply emem_true_iff; exact H.
Qed.

(** * Counting helpers *)

(** Splitting a filter along a weaker predicate. *)
Lemma filter_length_mono :
  forall {A : Type} (p q : A -> bool) (l : list A),
    (forall x, In x l -> p x = true -> q x = true) ->
    length (filter q l) =
    (length (filter p l) + length (filter (fun x => q x && negb (p x)) l))%nat.
Proof.
  intros A p q l; induction l as [|a l IH]; intros Hmono; [reflexivity|].
  assert (Hl : forall x, In x l -> p x = true -> q x = true)
    by (intros x Hx; apply Hmono; right; exact Hx).
  specialize (IH Hl); simpl.
  destruct (p a) eqn:Ep.
  - rewrite (Hmono a (or_introl eq_refl) Ep); simpl; lia.
  - destruct (q a); simpl; lia.
Qed.

Lemma length_concat_map_const :
  forall {A B : Type} (f : A -> list B) (l : list A) (k : nat),
    (forall x, In x l -> length (f x) = k) ->
    length (concat (map f l)) = (length l * k)%nat.
Proof.
  intros A B f l k; induction l as [|a l IH]; intros H; [reflexivity|].
  assert (Hl : forall x, In x l -> length (f x) = k)
    by (intros x Hx; apply H; right; exact Hx).
  simpl; rewrite length_app, (H a (or_introl eq_refl)), (IH Hl); lia.
Qed.

Lemma filter_length_lt :
  forall {A : Type} (p q : A -> bool) (l : list A) (x : A),
    (forall y, In y l -> p y = true -> q y = true) ->
    In x l -> q x = true -> p x = false ->
    (length (filter p l) < length (filter q l))%nat.
Proof.
  intros A p q l x Hmono Hx Hq Hp.
  induction l as [|a l IH]; [destruct Hx|].
  assert (Hl : forall y, In y l -> p y = true -> q y = true)
    by (intros y Hy; apply Hmono; right; exact Hy).
  destruct Hx as [<- | Hx].
  - simpl; rewrite Hp, Hq; simpl.
    pose proof (filter_impl_length_le p q l Hl); lia.
  - specialize (IH Hl Hx); simpl.
    destruct (p a) eqn:Ep.
    + rewrite (Hmono a (or_introl eq_refl) Ep); simpl; lia.
    + destruct (q a); simpl; lia.
Qed.

Lemma length_filter_le :
  forall {A : Type} (f : A -> bool) (l : list A),
    (length (filter f l) <= length l)%nat.
Proof.
  intros A f l; induction l as [|a l IH]; simpl; [lia|].
  destruct (f a); simpl; lia.
Qed.

Lemma NoDup_concat_map :
  forall {A B : Type} (f : A -> list B) (l : list A),
    NoDup l ->
    (forall x, In x l -> NoDup (f x)) ->
    (forall x y, In x l -> In y l -> x <> y ->
       forall b, In b (f x) -> ~ In b (f y)) ->
    NoDup (concat (map f l)).
Proof.
  intros A B f l; induction l as [|a l IH]; intros Hnd Hin Hdisj; [constructor|].
  inversion Hnd as [|? ? Hna Hndl]; subst.
  simpl; apply NoDup_app_disj.
  - apply Hin; left; reflexivity.
  - apply IH; auto.
    + intros x Hx; apply Hin; right; exact Hx.
    + intros x y Hx Hy Hne b Hb; apply (Hdisj x y); auto; right; auto.
  - intros b Hb Hc.
    apply in_concat in Hc; destruct Hc as [ys [Hys Hb2]].
    apply in_map_iff in Hys; destruct Hys as [y [<- Hy]].
    apply (Hdisj a y (or_introl eq_refl) (or_intror Hy)) with (b := b); auto.
    intros <-; contradiction.
Qed.

(** * The board *)

Section Board.

Variables m n : nat.

Definition hrow (r : nat) : list edge := map (fun c => EH r c) (seq 0 n).
Definition vrow (r : nat) : list edge := map (fun c => EV r c) (seq 0 (S n)).
Definition brow (r : nat) : list (nat * nat) := map (fun c => (r, c)) (seq 0 n).

Definition hedges : list edge := concat (map hrow (seq 0 (S m))).
Definition vedges : list edge := concat (map vrow (seq 0 m)).

Definition all_edges : list edge := hedges ++ vedges.
Definition boxes : list (nat * nat) := concat (map brow (seq 0 m)).

Definition box_edges (b : nat * nat) : list edge :=
  [EH (fst b) (snd b); EH (S (fst b)) (snd b);
   EV (fst b) (snd b); EV (fst b) (S (snd b))].

Definition dots : nat := (S m * S n)%nat.

(** ** Membership *)

Lemma In_hrow : forall r e, In e (hrow r) <-> exists c, (c < n)%nat /\ e = EH r c.
Proof.
  intros r e; unfold hrow; rewrite in_map_iff; split.
  - intros [c [<- Hc]]; apply in_seq in Hc; exists c; split; [lia | reflexivity].
  - intros [c [Hc ->]]; exists c; split; [reflexivity | apply in_seq; lia].
Qed.

Lemma In_vrow : forall r e, In e (vrow r) <-> exists c, (c <= n)%nat /\ e = EV r c.
Proof.
  intros r e; unfold vrow; rewrite in_map_iff; split.
  - intros [c [<- Hc]]; apply in_seq in Hc; exists c; split; [lia | reflexivity].
  - intros [c [Hc ->]]; exists c; split; [reflexivity | apply in_seq; lia].
Qed.

Lemma In_EH_all : forall r c, (r <= m)%nat -> (c < n)%nat -> In (EH r c) all_edges.
Proof.
  intros r c Hr Hc; unfold all_edges; apply in_or_app; left.
  unfold hedges; apply in_concat; exists (hrow r); split.
  - apply in_map_iff; exists r; split; [reflexivity | apply in_seq; lia].
  - apply In_hrow; exists c; split; [lia | reflexivity].
Qed.

Lemma In_EV_all : forall r c, (r < m)%nat -> (c <= n)%nat -> In (EV r c) all_edges.
Proof.
  intros r c Hr Hc; unfold all_edges; apply in_or_app; right.
  unfold vedges; apply in_concat; exists (vrow r); split.
  - apply in_map_iff; exists r; split; [reflexivity | apply in_seq; lia].
  - apply In_vrow; exists c; split; [lia | reflexivity].
Qed.

Lemma In_boxes : forall r c, In (r, c) boxes <-> ((r < m)%nat /\ (c < n)%nat).
Proof.
  intros r c; unfold boxes; split.
  - intros H; apply in_concat in H; destruct H as [l [Hl Hb]].
    apply in_map_iff in Hl; destruct Hl as [r' [<- Hr']].
    apply in_seq in Hr'; unfold brow in Hb; apply in_map_iff in Hb.
    destruct Hb as [c' [Heq Hc']]; apply in_seq in Hc'.
    injection Heq as -> ->; lia.
  - intros [Hr Hc]; apply in_concat; exists (brow r); split.
    + apply in_map_iff; exists r; split; [reflexivity | apply in_seq; lia].
    + unfold brow; apply in_map_iff; exists c; split;
        [reflexivity | apply in_seq; lia].
Qed.

Lemma box_edges_in_all :
  forall b, In b boxes -> forall e, In e (box_edges b) -> In e all_edges.
Proof.
  intros [r c] Hb e He; apply In_boxes in Hb; destruct Hb as [Hr Hc].
  simpl in He; destruct He as [<- | [<- | [<- | [<- | []]]]].
  - apply In_EH_all; lia.
  - apply In_EH_all; lia.
  - apply In_EV_all; lia.
  - apply In_EV_all; lia.
Qed.

(** ** Counts *)

Lemma length_hrow : forall r, length (hrow r) = n.
Proof. intros r; unfold hrow; rewrite length_map, length_seq; reflexivity. Qed.

Lemma length_vrow : forall r, length (vrow r) = S n.
Proof. intros r; unfold vrow; rewrite length_map, length_seq; reflexivity. Qed.

Lemma length_brow : forall r, length (brow r) = n.
Proof. intros r; unfold brow; rewrite length_map, length_seq; reflexivity. Qed.

Lemma length_boxes : length boxes = (m * n)%nat.
Proof.
  unfold boxes.
  rewrite (length_concat_map_const brow (seq 0 m) n)
    by (intros x _; apply length_brow).
  rewrite length_seq; reflexivity.
Qed.

Lemma length_all_edges : length all_edges = (S m * n + m * S n)%nat.
Proof.
  unfold all_edges, hedges, vedges; rewrite length_app.
  rewrite (length_concat_map_const hrow (seq 0 (S m)) n)
    by (intros x _; apply length_hrow).
  rewrite (length_concat_map_const vrow (seq 0 m) (S n))
    by (intros x _; apply length_vrow).
  rewrite !length_seq; reflexivity.
Qed.

(** One more edge than boxes and dots together: the identity the long chain
    rule rests on. *)
Lemma edges_boxes_dots :
  (S (length all_edges) = length boxes + dots)%nat.
Proof.
  unfold dots; rewrite length_all_edges, length_boxes.
  rewrite !Nat.mul_succ_l, !Nat.mul_succ_r; lia.
Qed.

(** ** The edge list has no repeats *)

Lemma NoDup_hrow : forall r, NoDup (hrow r).
Proof.
  intros r; unfold hrow; apply NoDup_map_inj; [| apply seq_NoDup].
  intros x y H; injection H as H; exact H.
Qed.

Lemma NoDup_vrow : forall r, NoDup (vrow r).
Proof.
  intros r; unfold vrow; apply NoDup_map_inj; [| apply seq_NoDup].
  intros x y H; injection H as H; exact H.
Qed.

Lemma NoDup_hedges : NoDup hedges.
Proof.
  unfold hedges; apply NoDup_concat_map.
  - apply seq_NoDup.
  - intros x _; apply NoDup_hrow.
  - intros x y _ _ Hne b Hbx Hby.
    apply In_hrow in Hbx; destruct Hbx as [c [_ ->]].
    apply In_hrow in Hby; destruct Hby as [c' [_ Heq]].
    injection Heq as Heq _; contradiction.
Qed.

Lemma NoDup_vedges : NoDup vedges.
Proof.
  unfold vedges; apply NoDup_concat_map.
  - apply seq_NoDup.
  - intros x _; apply NoDup_vrow.
  - intros x y _ _ Hne b Hbx Hby.
    apply In_vrow in Hbx; destruct Hbx as [c [_ ->]].
    apply In_vrow in Hby; destruct Hby as [c' [_ Heq]].
    injection Heq as Heq _; contradiction.
Qed.

Lemma NoDup_all_edges : NoDup all_edges.
Proof.
  unfold all_edges; apply NoDup_app_disj;
    [apply NoDup_hedges | apply NoDup_vedges |].
  intros x Hx Hv.
  unfold hedges in Hx; apply in_concat in Hx; destruct Hx as [l [Hl Hx]].
  apply in_map_iff in Hl; destruct Hl as [r [<- _]].
  apply In_hrow in Hx; destruct Hx as [c [_ ->]].
  unfold vedges in Hv; apply in_concat in Hv; destruct Hv as [l [Hl Hv]].
  apply in_map_iff in Hl; destruct Hl as [r' [<- _]].
  apply In_vrow in Hv; destruct Hv as [c' [_ Heq]]; discriminate.
Qed.

(** * States and moves *)

Record st : Type :=
  MkSt { laid : list edge ; s1 : nat ; s2 : nat ; p1 : bool }.

Definition init : st := MkSt [] 0 0 true.

Definition undrawn (s : st) : list edge :=
  filter (fun e => negb (emem e (laid s))) all_edges.

Definition db_moves (s : st) : list edge := undrawn s.

Lemma In_db_moves :
  forall s e, In e (db_moves s) <-> (In e all_edges /\ ~ In e (laid s)).
Proof.
  intros s e; unfold db_moves, undrawn; rewrite filter_In, negb_true_iff.
  rewrite emem_false_iff; reflexivity.
Qed.

Definition box_done (d : list edge) (b : nat * nat) : bool :=
  forallb (fun e => emem e d) (box_edges b).

Definition ndone (d : list edge) : nat := length (filter (box_done d) boxes).

Definition claimed (d : list edge) (e : edge) : list (nat * nat) :=
  filter (fun b => box_done (e :: d) b && negb (box_done d b)) boxes.

Definition ngain (d : list edge) (e : edge) : nat := length (claimed d e).

(** Drawing an edge; the mover keeps the move exactly when a box falls. *)
Definition db_play (s : st) (e : edge) : st :=
  let d := e :: laid s in
  match ngain (laid s) e with
  | O => MkSt d (s1 s) (s2 s) (negb (p1 s))
  | S k =>
      if p1 s
      then MkSt d (s1 s + S k) (s2 s) true
      else MkSt d (s1 s) (s2 s + S k) false
  end.

Lemma laid_play : forall s e, laid (db_play s e) = e :: laid s.
Proof.
  intros s e; unfold db_play.
  destruct (ngain (laid s) e); [reflexivity | destruct (p1 s); reflexivity].
Qed.

Definition scored (s : st) : nat := (s1 s + s2 s)%nat.

Lemma scored_play :
  forall s e, scored (db_play s e) = (scored s + ngain (laid s) e)%nat.
Proof.
  intros s e; unfold db_play, scored.
  destruct (ngain (laid s) e) eqn:Eg; simpl; [lia|].
  destruct (p1 s); simpl; lia.
Qed.

(** ** Boxes fall exactly as they are scored *)

Lemma box_done_mono :
  forall d e b, box_done d b = true -> box_done (e :: d) b = true.
Proof.
  intros d e b H; unfold box_done in *; rewrite forallb_forall in *.
  intros x Hx; apply emem_cons_mono, H, Hx.
Qed.

Lemma ndone_step :
  forall d e, ndone (e :: d) = (ndone d + ngain d e)%nat.
Proof.
  intros d e; unfold ndone, ngain, claimed.
  apply (filter_length_mono (box_done d) (box_done (e :: d)) boxes).
  intros b _ H; apply box_done_mono; exact H.
Qed.

Lemma box_done_nil : forall b, box_done [] b = false.
Proof. intros b; reflexivity. Qed.

Lemma ndone_nil : ndone [] = 0%nat.
Proof.
  unfold ndone; rewrite (filter_none (box_done []) boxes);
    [reflexivity | intros b _; apply box_done_nil].
Qed.

(** * Wellformed states *)

Definition wf_st (s : st) : Prop :=
  incl (laid s) all_edges /\ NoDup (laid s) /\ scored s = ndone (laid s).

Lemma wf_init : wf_st init.
Proof.
  unfold wf_st, init; simpl; repeat split.
  - intros x []; auto.
  - constructor.
  - rewrite ndone_nil; reflexivity.
Qed.

Lemma wf_play :
  forall s e, wf_st s -> In e (db_moves s) -> wf_st (db_play s e).
Proof.
  intros s e [Hincl [Hnd Hsc]] He.
  apply In_db_moves in He; destruct He as [Hall Hnin].
  unfold wf_st; rewrite laid_play, scored_play, ndone_step, Hsc.
  repeat split.
  - intros x [<- | Hx]; [exact Hall | apply Hincl; exact Hx].
  - constructor; assumption.
Qed.

(** * Turn counting *)

Fixpoint run (s : st) (ms : list edge) : st :=
  match ms with [] => s | e :: r => run (db_play s e) r end.

Fixpoint turns (s : st) (ms : list edge) : nat :=
  match ms with
  | [] => O
  | e :: r =>
      ((match ngain (laid s) e with O => 1 | S _ => 0 end)
       + turns (db_play s e) r)%nat
  end.

(** The boxes taken beyond the first by a single move: the doublecrosses. *)
Fixpoint extra (s : st) (ms : list edge) : nat :=
  match ms with
  | [] => O
  | e :: r =>
      ((match ngain (laid s) e with O => 0 | S k => k end)
       + extra (db_play s e) r)%nat
  end.

(** Every move ends a turn or takes a box, and takes one box beyond the
    first exactly when it doublecrosses. *)
Theorem turn_identity :
  forall ms s,
    (length (laid (run s ms)) + extra s ms + scored s
     = turns s ms + scored (run s ms) + length (laid s))%nat.
Proof.
  induction ms as [|e ms IH]; intros s; simpl; [lia|].
  pose proof (IH (db_play s e)) as H.
  rewrite laid_play, scored_play in H; simpl length in H.
  destruct (ngain (laid s) e); lia.
Qed.

Lemma length_laid_run :
  forall ms s, length (laid (run s ms)) = (length (laid s) + length ms)%nat.
Proof.
  induction ms as [|e ms IH]; intros s; simpl; [lia|].
  rewrite IH, laid_play; simpl; lia.
Qed.

(** * Legal play *)

Fixpoint legal (s : st) (ms : list edge) : Prop :=
  match ms with
  | [] => True
  | e :: r => In e (db_moves s) /\ legal (db_play s e) r
  end.

Lemma wf_run : forall ms s, wf_st s -> legal s ms -> wf_st (run s ms).
Proof.
  induction ms as [|e ms IH]; intros s Hw Hl; simpl; [exact Hw|].
  destruct Hl as [He Hl]; apply IH; [apply wf_play | ]; assumption.
Qed.

Definition complete (s : st) : Prop := db_moves s = [].

Lemma complete_all_in :
  forall s, complete s -> forall e, In e all_edges -> In e (laid s).
Proof.
  intros s H e He.
  destruct (in_dec edge_eq_dec e (laid s)) as [Hin | Hnin]; [exact Hin|].
  exfalso.
  assert (Hm : In e (db_moves s)) by (apply In_db_moves; split; assumption).
  rewrite H in Hm; destruct Hm.
Qed.

Lemma complete_ndone :
  forall s, complete s -> ndone (laid s) = length boxes.
Proof.
  intros s H; unfold ndone.
  rewrite (filter_all (box_done (laid s)) boxes); [reflexivity|].
  intros b Hb; unfold box_done; rewrite forallb_forall; intros e He.
  apply emem_true_iff, (complete_all_in s H), (box_edges_in_all b Hb e He).
Qed.

Lemma complete_length_laid :
  forall s, wf_st s -> complete s -> length (laid s) = length all_edges.
Proof.
  intros s [Hincl [Hnd _]] Hc; apply Nat.le_antisymm.
  - apply NoDup_incl_length; assumption.
  - apply NoDup_incl_length; [apply NoDup_all_edges|].
    intros x Hx; exact (complete_all_in s Hc x Hx).
Qed.

(** * The long chain rule *)

(** Over a completed game the turns taken exceed the dots by exactly the
    doublecrosses. This is the counting behind the long chain rule: the parity
    of the number of turns, and so of who is left to open the last chain, is
    fixed by the parity of the dots together with that of the doublecrosses. *)
Theorem long_chain_identity :
  forall ms,
    legal init ms ->
    complete (run init ms) ->
    (S (turns init ms) = dots + extra init ms)%nat.
Proof.
  intros ms Hl Hc.
  pose proof (turn_identity ms init) as Hid.
  assert (Hw : wf_st (run init ms)) by (apply wf_run; [apply wf_init | exact Hl]).
  pose proof (complete_length_laid (run init ms) Hw Hc) as Hlen.
  destruct Hw as [_ [_ Hsc]].
  rewrite (complete_ndone (run init ms) Hc) in Hsc.
  rewrite Hlen, Hsc in Hid.
  replace (scored init) with 0%nat in Hid by reflexivity.
  replace (length (laid init)) with 0%nat in Hid by reflexivity.
  pose proof edges_boxes_dots as Hd.
  lia.
Qed.

(** With no doublecrosses the number of turns is one less than the dots. *)
Corollary turns_of_no_doublecross :
  forall ms,
    legal init ms -> complete (run init ms) -> extra init ms = 0%nat ->
    (S (turns init ms) = dots)%nat.
Proof.
  intros ms Hl Hc H0.
  rewrite (long_chain_identity ms Hl Hc), H0; lia.
Qed.

(** The parity of the turn count is that of the dots and the doublecrosses
    together, which is the form the rule is usually quoted in. *)
Corollary long_chain_parity :
  forall ms,
    legal init ms -> complete (run init ms) ->
    Nat.odd (S (turns init ms)) = Nat.odd (dots + extra init ms).
Proof.
  intros ms Hl Hc; rewrite (long_chain_identity ms Hl Hc); reflexivity.
Qed.

(** * Determinacy *)

Definition db_amove (s : st) : bool := p1 s.

Definition db_outc (s : st) : option outcome :=
  match db_moves s with
  | [] =>
      Some (if Nat.ltb (s2 s) (s1 s) then win true
            else if Nat.ltb (s1 s) (s2 s) then win false
            else drawn)
  | _ :: _ => None
  end.

Lemma db_outc_none_iff : forall s, db_outc s = None <-> db_moves s <> [].
Proof.
  intros s; unfold db_outc; destruct (db_moves s); split;
    try discriminate; try reflexivity.
  intros H; contradiction.
Qed.

Definition db_measure (s : st) : nat := length (undrawn s).

Lemma db_measure_play :
  forall s e, In e (db_moves s) -> (db_measure (db_play s e) < db_measure s)%nat.
Proof.
  intros s e He; unfold db_measure, undrawn.
  rewrite laid_play.
  apply (filter_length_lt
           (fun x => negb (emem x (e :: laid s)))
           (fun x => negb (emem x (laid s))) all_edges e).
  - intros y _ Hy; rewrite negb_true_iff, emem_false_iff in Hy.
    rewrite negb_true_iff, emem_false_iff; intros Hc; apply Hy; right; exact Hc.
  - apply In_db_moves in He; tauto.
  - apply In_db_moves in He; destruct He as [_ Hn].
    rewrite negb_true_iff, emem_false_iff; exact Hn.
  - rewrite negb_false_iff; apply emem_true_iff; left; reflexivity.
Qed.

Lemma db_no_stall :
  forall s, db_outc s = None -> exists e, In e (db_moves s).
Proof.
  intros s H; apply db_outc_none_iff in H.
  destruct (db_moves s) as [|e r] eqn:E; [exact (match H eq_refl with end)|].
  exists e; left; reflexivity.
Qed.

(** Dots and Boxes is determined: from any wellformed position one player
    forces a win or both hold a draw. Scoring games draw, so this is the
    three-way form. *)
Theorem db_determined :
  forall fuel s,
    wf_st s -> (db_measure s <= fuel)%nat ->
    forces db_moves db_play db_amove db_outc true fuel s \/
    forces db_moves db_play db_amove db_outc false fuel s \/
    (nonloss db_moves db_play db_amove db_outc true fuel s /\
     nonloss db_moves db_play db_amove db_outc false fuel s).
Proof.
  intros fuel s Hw Hf.
  apply (zermelo_three_way db_moves db_play db_amove db_outc wf_st db_measure).
  - intros t e Hi _ He; apply wf_play; assumption.
  - intros t e _ _ He; apply db_measure_play; exact He.
  - intros t _ Ho; apply db_no_stall; exact Ho.
  - exact Hw.
  - exact Hf.
Qed.

Corollary db_determined_init :
  forces db_moves db_play db_amove db_outc true (length all_edges) init \/
  forces db_moves db_play db_amove db_outc false (length all_edges) init \/
  (nonloss db_moves db_play db_amove db_outc true (length all_edges) init /\
   nonloss db_moves db_play db_amove db_outc false (length all_edges) init).
Proof.
  apply db_determined; [apply wf_init|].
  unfold db_measure, undrawn; apply length_filter_le.
Qed.

End Board.
