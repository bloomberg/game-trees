(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Strings and Coins, and its duality with the Dots and Boxes board.

    A coin is a number, with [ground] reserved for the outside of the board. A
    string joins two coins, and a graph is a list of strings, so parallel
    strings and strings from a coin to itself are both allowed. Cutting a
    string removes it; a coin with no string left is free and is collected.

    The board of [DotsAndBoxesBoard] embeds here: each box is a coin, each
    edge is the string joining the boxes it separates, and an edge on the
    border of the board is a string to the ground. [box_done_iff_free] is the
    duality: a box is complete exactly when its coin has been cut loose, so
    the two games are the same game. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxesBoard.

(** * Coins, strings, graphs *)

Definition coin : Type := nat.
Definition ground : coin := 0.

Definition strng : Type := (coin * coin)%type.
Definition sgraph : Type := list strng.

Definition touches (x : coin) (s : strng) : bool :=
  (Nat.eqb (fst s) x || Nat.eqb (snd s) x)%bool.

(** The strings still tied to a coin. *)
Definition incident (g : sgraph) (x : coin) : sgraph := filter (touches x) g.

Definition deg (g : sgraph) (x : coin) : nat := length (incident g x).

(** A coin is free when nothing holds it. *)
Definition freeb (g : sgraph) (x : coin) : bool := Nat.eqb (deg g x) 0.

Lemma freeb_true_iff :
  forall g x, freeb g x = true <-> (forall s, In s g -> touches x s = false).
Proof.
  intros g x; unfold freeb, deg, incident; split.
  - intros H s Hs; apply Nat.eqb_eq, length_zero_iff_nil in H.
    destruct (touches x s) eqn:E; [|reflexivity].
    exfalso.
    assert (Hin : In s (filter (touches x) g))
      by (apply filter_In; split; assumption).
    rewrite H in Hin; destruct Hin.
  - intros H; apply Nat.eqb_eq, length_zero_iff_nil.
    apply filter_none; intros s Hs; apply H; exact Hs.
Qed.

(** Cutting a string. *)
Fixpoint remove_one (s : strng) (g : sgraph) {struct g} : sgraph :=
  match g with
  | [] => []
  | t :: r =>
      if (Nat.eqb (fst t) (fst s) && Nat.eqb (snd t) (snd s))%bool
      then r else t :: remove_one s r
  end.

Definition cut (s : strng) (g : sgraph) : sgraph := remove_one s g.

Lemma cut_length_le : forall s g, (length (cut s g) <= length g)%nat.
Proof.
  intros s g; unfold cut; induction g as [|t r IH]; simpl; [lia|].
  destruct (Nat.eqb (fst t) (fst s) && Nat.eqb (snd t) (snd s))%bool;
    simpl; lia.
Qed.

(** * The board as a graph of strings and coins *)

Section Dual.

Variables m n : nat.

(** Box [(r, c)] is the coin [S (r * n + c)]; anything off the board is the
    ground. *)
Definition cell_coin (r c : nat) : coin :=
  if (Nat.ltb r m && Nat.ltb c n)%bool then S (r * n + c) else ground.

Lemma cell_coin_in :
  forall r c, (r < m)%nat -> (c < n)%nat -> cell_coin r c = S (r * n + c).
Proof.
  intros r c Hr Hc; unfold cell_coin.
  rewrite (proj2 (Nat.ltb_lt r m) Hr), (proj2 (Nat.ltb_lt c n) Hc); reflexivity.
Qed.

Lemma cell_coin_nonground :
  forall r c, (r < m)%nat -> (c < n)%nat -> cell_coin r c <> ground.
Proof.
  intros r c Hr Hc; rewrite cell_coin_in by assumption; discriminate.
Qed.

Lemma cell_coin_inj :
  forall r c r' c',
    (r < m)%nat -> (c < n)%nat -> (r' < m)%nat -> (c' < n)%nat ->
    cell_coin r c = cell_coin r' c' -> r = r' /\ c = c'.
Proof.
  intros r c r' c' Hr Hc Hr' Hc' H.
  rewrite cell_coin_in in H by assumption.
  rewrite cell_coin_in in H by assumption.
  injection H as H.
  assert (Hrr : r = r').
  { destruct (Nat.lt_trichotomy r r') as [Hlt | [Heq | Hgt]]; [| exact Heq |];
      exfalso; nia. }
  split; [exact Hrr | nia].
Qed.

(** The two coins an edge separates. A missing neighbour is the ground. *)
Definition above (r c : nat) : coin :=
  match r with O => ground | S r' => cell_coin r' c end.
Definition below (r c : nat) : coin := cell_coin r c.
Definition leftof (r c : nat) : coin :=
  match c with O => ground | S c' => cell_coin r c' end.
Definition rightof (r c : nat) : coin := cell_coin r c.

Definition string_of (e : edge) : strng :=
  match e with
  | EH r c => (above r c, below r c)
  | EV r c => (leftof r c, rightof r c)
  end.

Definition dual (l : list edge) : sgraph := map string_of l.

(** ** Which edges hold a given coin *)

(** An edge is tied to the coin of box [(r, c)] exactly when it is one of the
    four edges of that box. *)
Lemma touches_cell_iff :
  forall r c e,
    (r < m)%nat -> (c < n)%nat ->
    touches (cell_coin r c) (string_of e) = true <-> In e (box_edges (r, c)).
Proof.
  intros r c e Hr Hc; split.
  - intros H; unfold touches in H.
    apply orb_true_iff in H; destruct H as [H | H]; apply Nat.eqb_eq in H;
      destruct e as [r' c' | r' c']; simpl in H.
    + (* above r' c' = cell_coin r c *)
      destruct r' as [|r'']; [exfalso; symmetry in H;
        exact (cell_coin_nonground r c Hr Hc H)|].
      unfold above in H.
      destruct (Nat.ltb r'' m) eqn:Er, (Nat.ltb c' n) eqn:Ec.
      * apply Nat.ltb_lt in Er; apply Nat.ltb_lt in Ec.
        destruct (cell_coin_inj r'' c' r c Er Ec Hr Hc H) as [<- <-].
        simpl; right; left; reflexivity.
      * exfalso; unfold cell_coin in H; rewrite Er, Ec in H; simpl in H;
          symmetry in H; exact (cell_coin_nonground r c Hr Hc H).
      * exfalso; unfold cell_coin in H; rewrite Er, Ec in H; simpl in H;
          symmetry in H; exact (cell_coin_nonground r c Hr Hc H).
      * exfalso; unfold cell_coin in H; rewrite Er, Ec in H; simpl in H;
          symmetry in H; exact (cell_coin_nonground r c Hr Hc H).
    + (* leftof r' c' = cell_coin r c *)
      destruct c' as [|c'']; [exfalso; symmetry in H;
        exact (cell_coin_nonground r c Hr Hc H)|].
      unfold leftof in H.
      destruct (Nat.ltb r' m) eqn:Er, (Nat.ltb c'' n) eqn:Ec.
      * apply Nat.ltb_lt in Er; apply Nat.ltb_lt in Ec.
        destruct (cell_coin_inj r' c'' r c Er Ec Hr Hc H) as [<- <-].
        simpl; right; right; right; left; reflexivity.
      * exfalso; unfold cell_coin in H; rewrite Er, Ec in H; simpl in H;
          symmetry in H; exact (cell_coin_nonground r c Hr Hc H).
      * exfalso; unfold cell_coin in H; rewrite Er, Ec in H; simpl in H;
          symmetry in H; exact (cell_coin_nonground r c Hr Hc H).
      * exfalso; unfold cell_coin in H; rewrite Er, Ec in H; simpl in H;
          symmetry in H; exact (cell_coin_nonground r c Hr Hc H).
    + (* below r' c' = cell_coin r c *)
      unfold below in H.
      destruct (Nat.ltb r' m) eqn:Er, (Nat.ltb c' n) eqn:Ec.
      * apply Nat.ltb_lt in Er; apply Nat.ltb_lt in Ec.
        destruct (cell_coin_inj r' c' r c Er Ec Hr Hc H) as [<- <-].
        simpl; left; reflexivity.
      * exfalso; unfold cell_coin in H; rewrite Er, Ec in H; simpl in H;
          symmetry in H; exact (cell_coin_nonground r c Hr Hc H).
      * exfalso; unfold cell_coin in H; rewrite Er, Ec in H; simpl in H;
          symmetry in H; exact (cell_coin_nonground r c Hr Hc H).
      * exfalso; unfold cell_coin in H; rewrite Er, Ec in H; simpl in H;
          symmetry in H; exact (cell_coin_nonground r c Hr Hc H).
    + (* rightof r' c' = cell_coin r c *)
      unfold rightof in H.
      destruct (Nat.ltb r' m) eqn:Er, (Nat.ltb c' n) eqn:Ec.
      * apply Nat.ltb_lt in Er; apply Nat.ltb_lt in Ec.
        destruct (cell_coin_inj r' c' r c Er Ec Hr Hc H) as [<- <-].
        simpl; right; right; left; reflexivity.
      * exfalso; unfold cell_coin in H; rewrite Er, Ec in H; simpl in H;
          symmetry in H; exact (cell_coin_nonground r c Hr Hc H).
      * exfalso; unfold cell_coin in H; rewrite Er, Ec in H; simpl in H;
          symmetry in H; exact (cell_coin_nonground r c Hr Hc H).
      * exfalso; unfold cell_coin in H; rewrite Er, Ec in H; simpl in H;
          symmetry in H; exact (cell_coin_nonground r c Hr Hc H).
  - intros H; simpl in H.
    destruct H as [<- | [<- | [<- | [<- | []]]]]; unfold touches; simpl;
      apply orb_true_iff.
    + right; unfold below; apply Nat.eqb_eq; reflexivity.
    + left; unfold above; apply Nat.eqb_eq; reflexivity.
    + right; unfold rightof; apply Nat.eqb_eq; reflexivity.
    + left; unfold leftof; apply Nat.eqb_eq; reflexivity.
Qed.

(** ** Duality *)

(** The strings left uncut are the duals of the edges not yet drawn. *)
Definition remaining (d : list edge) : list edge :=
  filter (fun e => negb (emem e d)) (all_edges m n).

Lemma In_remaining :
  forall d e, In e (remaining d) <-> (In e (all_edges m n) /\ ~ In e d).
Proof.
  intros d e; unfold remaining; rewrite filter_In, negb_true_iff,
    emem_false_iff; reflexivity.
Qed.

(** A box is complete exactly when its coin is free of uncut strings: the two
    games are one game. *)
Theorem box_done_iff_free :
  forall d r c,
    (r < m)%nat -> (c < n)%nat ->
    box_done d (r, c) = freeb (dual (remaining d)) (cell_coin r c).
Proof.
  intros d r c Hr Hc.
  apply eq_true_iff_eq; split.
  - intros H; rewrite freeb_true_iff; intros s Hs.
    unfold dual in Hs; apply in_map_iff in Hs; destruct Hs as [e [<- He]].
    destruct (touches (cell_coin r c) (string_of e)) eqn:Et; [|reflexivity].
    exfalso.
    apply (touches_cell_iff r c e Hr Hc) in Et.
    apply In_remaining in He; destruct He as [_ Hnd]; apply Hnd.
    unfold box_done in H; rewrite forallb_forall in H.
    apply emem_true_iff, (H e Et).
  - intros H; rewrite freeb_true_iff in H.
    unfold box_done; rewrite forallb_forall; intros e He.
    apply emem_true_iff.
    destruct (in_dec edge_eq_dec e d) as [Hin | Hnin]; [exact Hin|].
    exfalso.
    assert (Hrem : In e (remaining d)).
    { apply In_remaining; split; [| exact Hnin].
      apply (box_edges_in_all m n (r, c)); [apply In_boxes; split; assumption
                                           | exact He]. }
    assert (Hs : In (string_of e) (dual (remaining d)))
      by (unfold dual; apply in_map_iff; exists e; split; [reflexivity | exact Hrem]).
    pose proof (H (string_of e) Hs) as Hf.
    rewrite (proj2 (touches_cell_iff r c e Hr Hc) He) in Hf; discriminate.
Qed.

(** Every box of the board has a coin, and distinct boxes have distinct
    coins, so the correspondence is a bijection onto the non-ground coins. *)
Corollary coins_distinct :
  forall r c r' c',
    In (r, c) (boxes m n) -> In (r', c') (boxes m n) ->
    cell_coin r c = cell_coin r' c' -> (r, c) = (r', c').
Proof.
  intros r c r' c' H1 H2 He.
  apply In_boxes in H1; apply In_boxes in H2.
  destruct H1 as [Hr Hc]; destruct H2 as [Hr' Hc'].
  destruct (cell_coin_inj r c r' c' Hr Hc Hr' Hc' He) as [<- <-]; reflexivity.
Qed.

(** A drawn board cuts every string, so every coin is free. *)
Corollary all_free_of_complete :
  forall s,
    complete m n s ->
    forall r c, (r < m)%nat -> (c < n)%nat ->
    freeb (dual (remaining (laid s))) (cell_coin r c) = true.
Proof.
  intros s Hc r c Hr Hcc.
  rewrite <- (box_done_iff_free (laid s) r c Hr Hcc).
  unfold box_done; rewrite forallb_forall; intros e He.
  apply emem_true_iff, (complete_all_in m n s Hc).
  apply (box_edges_in_all m n (r, c)); [apply In_boxes; split; assumption | exact He].
Qed.

(** * Degrees *)

Lemma filter_map_comm :
  forall {A B : Type} (p : B -> bool) (f : A -> B) (l : list A),
    filter p (map f l) = map f (filter (fun x => p (f x)) l).
Proof.
  intros A B p f l; induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (p (f a)); simpl; [f_equal|]; exact IH.
Qed.

Lemma filter_eq_sub_length :
  forall {A : Type} (eqd : forall x y : A, {x = y} + {x <> y})
         (p : A -> bool) (l sub : list A),
    NoDup l -> NoDup sub -> incl sub l ->
    (forall x, In x l -> (p x = true <-> In x sub)) ->
    length (filter p l) = length sub.
Proof.
  intros A eqd p l sub Hl Hs Hincl Hiff; apply Nat.le_antisymm.
  - apply NoDup_incl_length; [apply NoDup_filter; exact Hl|].
    intros x Hx; apply filter_In in Hx; destruct Hx as [Hxl Hxp].
    apply (Hiff x Hxl); exact Hxp.
  - apply NoDup_incl_length; [exact Hs|].
    intros x Hx; apply filter_In; split; [apply Hincl; exact Hx|].
    apply (Hiff x (Hincl x Hx)); exact Hx.
Qed.

Lemma NoDup_box_edges :
  forall r c, NoDup (box_edges (r, c)).
Proof.
  intros r c; simpl.
  constructor; [simpl; intros H; destruct H as [H|[H|[H|[]]]];
                solve [discriminate | injection H; intros; lia] |].
  constructor; [simpl; intros H; destruct H as [H|[H|[]]]; discriminate |].
  constructor; [simpl; intros H; destruct H as [H|[]];
                injection H; intros; lia |].
  constructor; [simpl; intros H; destruct H | constructor].
Qed.

(** Every box is bounded by exactly four edges, so its coin starts with
    degree four. *)
Theorem deg_initial :
  forall r c,
    (r < m)%nat -> (c < n)%nat ->
    deg (dual (all_edges m n)) (cell_coin r c) = 4%nat.
Proof.
  intros r c Hr Hc; unfold deg, incident, dual.
  rewrite filter_map_comm, length_map.
  rewrite (filter_eq_sub_length edge_eq_dec _ (all_edges m n)
             (box_edges (r, c))).
  - reflexivity.
  - apply NoDup_all_edges.
  - apply NoDup_box_edges.
  - intros e He; apply (box_edges_in_all m n (r, c));
      [apply In_boxes; split; assumption | exact He].
  - intros e _; apply touches_cell_iff; assumption.
Qed.

(** A coin's degree during play is the number of its box's edges still
    undrawn, so degrees fall from four to zero as the box is closed in. *)
Theorem deg_remaining :
  forall d r c,
    (r < m)%nat -> (c < n)%nat ->
    deg (dual (remaining d)) (cell_coin r c)
    = length (filter (fun e => negb (emem e d)) (box_edges (r, c))).
Proof.
  intros d r c Hr Hc; unfold deg, incident, dual.
  rewrite filter_map_comm, length_map.
  apply (filter_eq_sub_length edge_eq_dec).
  - apply NoDup_filter, NoDup_all_edges.
  - apply NoDup_filter, NoDup_box_edges.
  - intros e He; apply filter_In in He; destruct He as [Heb Hed].
    apply In_remaining; split.
    + apply (box_edges_in_all m n (r, c));
        [apply In_boxes; split; assumption | exact Heb].
    + apply negb_true_iff, emem_false_iff in Hed; exact Hed.
  - intros e He; apply In_remaining in He; destruct He as [_ Hnd].
    rewrite touches_cell_iff by assumption.
    rewrite filter_In, negb_true_iff, emem_false_iff.
    split; [intros H; split; assumption | intros [H _]; exact H].
Qed.

(** A box is closed exactly when its coin has run out of strings. *)
Corollary deg_zero_iff_done :
  forall d r c,
    (r < m)%nat -> (c < n)%nat ->
    (deg (dual (remaining d)) (cell_coin r c) = 0%nat <-> box_done d (r, c) = true).
Proof.
  intros d r c Hr Hc.
  rewrite (box_done_iff_free d r c Hr Hc); unfold freeb.
  split; [intros H; rewrite H; reflexivity | apply Nat.eqb_eq].
Qed.

(** * Loops are even *)

(** Two boxes are neighbours when they share an edge. *)
Definition cadj (b1 b2 : nat * nat) : Prop :=
  (fst b1 = fst b2 /\ (snd b1 = S (snd b2) \/ snd b2 = S (snd b1))) \/
  (snd b1 = snd b2 /\ (fst b1 = S (fst b2) \/ fst b2 = S (fst b1))).

(** Neighbouring boxes carry a shared string: [cadj] is exactly the adjacency
    the dual graph gives, so a cycle of boxes is a cycle of strings. *)
Lemma cadj_string :
  forall r1 c1 r2 c2,
    cadj (r1, c1) (r2, c2) ->
    (r1 < m)%nat -> (c1 < n)%nat -> (r2 < m)%nat -> (c2 < n)%nat ->
    exists e, In e (all_edges m n) /\
      In e (box_edges (r1, c1)) /\ In e (box_edges (r2, c2)).
Proof.
  intros r1 c1 r2 c2 H H1 H2 H3 H4; unfold cadj in H; simpl in H.
  destruct H as [[Hr [Hc | Hc]] | [Hc [Hr | Hr]]].
  - exists (EV r1 c1); repeat split.
    + apply In_EV_all; lia.
    + simpl; right; right; left; reflexivity.
    + simpl; right; right; right; left; f_equal; lia.
  - exists (EV r1 c2); repeat split.
    + apply In_EV_all; lia.
    + simpl; right; right; right; left; f_equal; lia.
    + simpl; right; right; left; f_equal; lia.
  - exists (EH r1 c1); repeat split.
    + apply In_EH_all; lia.
    + simpl; left; reflexivity.
    + simpl; right; left; f_equal; lia.
  - exists (EH r2 c2); repeat split.
    + apply In_EH_all; lia.
    + simpl; right; left; f_equal; lia.
    + simpl; left; reflexivity.
Qed.

(** The grid dual is bipartite: neighbouring boxes take opposite colours. *)
Definition colour (b : nat * nat) : bool := Nat.even (fst b + snd b).

Lemma cadj_colour :
  forall b1 b2, cadj b1 b2 -> colour b1 = negb (colour b2).
Proof.
  intros [r1 c1] [r2 c2] H; unfold colour, cadj in *; simpl in *.
  assert (Hstep : r1 + c1 = S (r2 + c2) \/ r2 + c2 = S (r1 + c1))
    by (destruct H as [[Hr [Hc | Hc]] | [Hc [Hr | Hr]]]; lia).
  destruct Hstep as [E | E]; rewrite E, Nat.even_succ, <- Nat.negb_even;
    [reflexivity|].
  destruct (Nat.even (r1 + c1)); reflexivity.
Qed.

(** A walk through neighbouring boxes. *)
Inductive walk : nat * nat -> nat * nat -> nat -> Prop :=
| walk_nil : forall b, walk b b 0
| walk_step : forall b1 b2 b3 k,
    cadj b1 b2 -> walk b2 b3 k -> walk b1 b3 (S k).

(** Colour flips with every step, so it is determined by the parity of the
    length. *)
Lemma walk_colour :
  forall b1 b2 k,
    walk b1 b2 k ->
    colour b1 = (if Nat.even k then colour b2 else negb (colour b2)).
Proof.
  intros b1 b2 k H; induction H as [b | b1 b2 b3 k Hadj Hw IH].
  - reflexivity.
  - rewrite (cadj_colour b1 b2 Hadj), IH, Nat.even_succ, <- Nat.negb_even.
    destruct (Nat.even k); simpl; [reflexivity|].
    destruct (colour b3); reflexivity.
Qed.

(** Every closed walk of the grid dual has even length. A loop is a closed
    walk, so a loop of the board is even, which is the hypothesis
    [DotsAndBoxes.wf_comp] places on [Loop] and the reason a loop that is not
    large has length four or six. *)
Theorem closed_walk_even :
  forall b k, walk b b k -> Nat.even k = true.
Proof.
  intros b k H.
  pose proof (walk_colour b b k H) as Hc.
  destruct (Nat.even k) eqn:Ek; [reflexivity|].
  exfalso; rewrite Hc in Hc.
  destruct (colour b); discriminate.
Qed.

(** * Cycles of boxes *)

Lemma walk_snoc :
  forall b1 b2 k, walk b1 b2 k -> forall b3, cadj b2 b3 -> walk b1 b3 (S k).
Proof.
  intros b1 b2 k H; induction H as [b | x y z k Hadj Hw IH]; intros b3 Hc.
  - eapply walk_step; [exact Hc | apply walk_nil].
  - eapply walk_step; [exact Hadj | apply IH; exact Hc].
Qed.

(** A run of boxes, each next to the one before. *)
Fixpoint chain_walk (b : nat * nat) (bs : list (nat * nat)) : Prop :=
  match bs with
  | [] => True
  | c :: r => cadj b c /\ chain_walk c r
  end.

Lemma last_nonnil_irrel :
  forall (l : list (nat * nat)) (a d1 d2 : nat * nat),
    last (a :: l) d1 = last (a :: l) d2.
Proof.
  induction l as [|x l IH]; intros a d1 d2; [reflexivity|].
  exact (IH x d1 d2).
Qed.

Lemma last_cons_irrel :
  forall (r : list (nat * nat)) (c b : nat * nat), last (c :: r) b = last r c.
Proof.
  intros [|x r] c b; [reflexivity|].
  exact (last_nonnil_irrel r x b c).
Qed.

Lemma chain_walk_walk :
  forall bs b, chain_walk b bs -> walk b (last bs b) (length bs).
Proof.
  induction bs as [|c r IH]; intros b H.
  - apply walk_nil.
  - destruct H as [Hadj Hrest].
    rewrite last_cons_irrel.
    change (length (c :: r)) with (S (length r)).
    eapply walk_step; [exact Hadj | apply IH; exact Hrest].
Qed.

(** A cycle: a run that closes back on where it started. *)
Definition cyclic (bs : list (nat * nat)) : Prop :=
  match bs with
  | [] => False
  | b :: r => chain_walk b r /\ cadj (last r b) b
  end.

(** Every cycle of boxes has even length. A loop of the board is such a
    cycle, so a loop is even: the hypothesis [DotsAndBoxes.wf_comp] puts on
    [Loop] is a consequence of the grid, not an assumption about it. *)
Theorem cyclic_even :
  forall bs, cyclic bs -> Nat.even (length bs) = true.
Proof.
  intros [|b r] H; [destruct H|].
  destruct H as [Hw Hclose].
  simpl length.
  apply (closed_walk_even b (S (length r))).
  exact (walk_snoc b (last r b) (length r) (chain_walk_walk r b Hw) b Hclose).
Qed.

End Dual.
