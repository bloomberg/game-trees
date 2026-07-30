(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Chomp: the first player wins every rectangle of at least two squares. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.

Import ListNotations.
Require Import GameTrees.Helpers.

(** * List helpers *)

Lemma nth_repeat_lt :
  forall (x : nat) m i, i < m -> nth i (repeat x m) 0 = x.
Proof.
  intros x m; induction m as [|m IH]; intros i Hi; [lia|].
  destruct i; simpl; auto.
  apply IH; lia.
Qed.

Lemma skipn_repeat_le :
  forall (x : nat) m i, i <= m -> skipn i (repeat x m) = repeat x (m - i).
Proof.
  intros x m; induction m as [|m IH]; intros i Hi.
  - assert (i = 0) by lia; subst; auto.
  - destruct i; simpl; auto.
    apply IH; lia.
Qed.

Lemma map_repeat_eq :
  forall (f : nat -> nat) x m, map f (repeat x m) = repeat (f x) m.
Proof.
  intros f x m; induction m; simpl; congruence.
Qed.

Lemma repeat_S_app :
  forall (x : nat) m, repeat x (S m) = repeat x m ++ [x].
Proof.
  intros x m; induction m as [|m IH]; simpl; [auto|].
  f_equal; exact IH.
Qed.

(** * Positions *)

(** The row widths of the remaining Young diagram, poisoned row first. *)
Definition pos : Type := list nat.

Definition cells (p : pos) : nat := fold_right Nat.add 0 p.

Lemma cells_app : forall a b, cells (a ++ b) = cells a + cells b.
Proof.
  intros a b; induction a; simpl; lia.
Qed.

Lemma cells_repeat : forall x m, cells (repeat x m) = m * x.
Proof.
  intros x m; induction m; simpl; lia.
Qed.

Lemma nth_le_cells :
  forall p i, i < length p -> nth i p 0 <= cells p.
Proof.
  induction p as [|w p IH]; intros i Hi; simpl in *; [lia|].
  destruct i; [lia|].
  specialize (IH i); lia.
Qed.

Lemma skipn_cons_nth :
  forall (p : pos) i, i < length p ->
  skipn i p = nth i p 0 :: skipn (S i) p.
Proof.
  induction p as [|w p IH]; intros i Hi; simpl in *; [lia|].
  destruct i; simpl; auto.
  apply IH; lia.
Qed.

(** A bite at [(i, j)] removes every square weakly below and right of it. *)
Definition bite (p : pos) (c : nat * nat) : pos :=
  let (i, j) := c in
  match j with
  | 0 => firstn i p
  | S _ => firstn i p ++ map (Nat.min j) (skipn i p)
  end.

(** Every remaining square except the poisoned one. *)
Definition moves (p : pos) : list (nat * nat) :=
  filter (fun c => negb ((fst c =? 0) && (snd c =? 0)))
    (concat (map (fun i => map (fun j => (i, j)) (seq 0 (nth i p 0)))
               (seq 0 (length p)))).

Lemma in_moves_iff :
  forall p i j,
    In (i, j) (moves p) <->
    i < length p /\ j < nth i p 0 /\ (i, j) <> (0, 0).
Proof.
  intros p i j; unfold moves.
  rewrite filter_In, in_concat.
  split.
  - intros [[l [Hl Hin]] Hne].
    apply in_map_iff in Hl; destruct Hl as [i' [<- Hi']].
    apply in_seq in Hi'.
    apply in_map_iff in Hin; destruct Hin as [j' [Hpair Hj']].
    inversion Hpair; subst i' j'.
    apply in_seq in Hj'.
    simpl in Hne; rewrite negb_true_iff, andb_false_iff in Hne.
    repeat split; try lia.
    intros He; inversion He; subst.
    destruct Hne as [Hne | Hne]; rewrite Nat.eqb_neq in Hne; lia.
  - intros [Hi [Hj Hne]]; split.
    + exists (map (fun j0 => (i, j0)) (seq 0 (nth i p 0))); split.
      * apply in_map_iff; exists i; split; auto.
        apply in_seq; lia.
      * apply in_map_iff; exists j; split; auto.
        apply in_seq; lia.
    + simpl; rewrite negb_true_iff, andb_false_iff.
      destruct i.
      * right; apply Nat.eqb_neq.
        intros ->; apply Hne; auto.
      * left; apply Nat.eqb_neq; lia.
Qed.

Lemma move_cells_pos :
  forall p c, In c (moves p) -> 1 <= cells p.
Proof.
  intros p [i j] Hc; apply in_moves_iff in Hc.
  destruct Hc as [Hi [Hj _]].
  pose proof (nth_le_cells p i Hi); lia.
Qed.

Lemma cells_zero_no_moves :
  forall p, cells p = 0 -> moves p = [].
Proof.
  intros p Hc.
  destruct (moves p) as [|c l] eqn:Em; auto.
  exfalso.
  assert (Hin : In c (moves p)) by (rewrite Em; left; auto).
  pose proof (move_cells_pos p c Hin); lia.
Qed.

Lemma cells_cons : forall x l, cells (x :: l) = x + cells l.
Proof. reflexivity. Qed.

Lemma cells_map_min_le :
  forall j l, cells (map (Nat.min j) l) <= cells l.
Proof.
  intros j l; induction l as [|a l IH]; simpl; [lia|].
  pose proof (Nat.le_min_r j a); lia.
Qed.

Lemma bite_cells_lt :
  forall p i j, i < length p -> j < nth i p 0 ->
  cells (bite p (i, j)) < cells p.
Proof.
  intros p i j Hi Hj.
  assert (Hsplit : cells p = cells (firstn i p) + cells (skipn i p)).
  { rewrite <- cells_app, firstn_skipn; auto. }
  rewrite (skipn_cons_nth p i Hi) in Hsplit.
  rewrite cells_cons in Hsplit.
  destruct j as [|j].
  - change (cells (firstn i p) < cells p).
    lia.
  - change (cells (firstn i p ++ map (Nat.min (S j)) (skipn i p)) < cells p).
    rewrite cells_app.
    rewrite (skipn_cons_nth p i Hi).
    rewrite map_cons.
    rewrite cells_cons.
    rewrite (Nat.min_l (S j) (nth i p 0)) by lia.
    pose proof (cells_map_min_le (S j) (skipn (S i) p)).
    lia.
Qed.

Lemma bite_cells_lt_moves :
  forall p c, In c (moves p) -> cells (bite p c) < cells p.
Proof.
  intros p [i j] Hc; apply in_moves_iff in Hc.
  apply bite_cells_lt; tauto.
Qed.

(** * The fueled winning predicate *)

(** [winsb fuel p]: the player to move wins within [fuel] plies. *)
Fixpoint winsb (fuel : nat) (p : pos) : bool :=
  match fuel with
  | 0 => false
  | S f => existsb (fun c => negb (winsb f (bite p c))) (moves p)
  end.

(** The value is fuel-independent once the fuel covers the square count. *)
Lemma winsb_stable :
  forall N p f1 f2,
    cells p <= N -> cells p <= f1 -> cells p <= f2 ->
    winsb f1 p = winsb f2 p.
Proof.
  induction N as [|N IH]; intros p f1 f2 HN H1 H2.
  - assert (Hm : moves p = []) by (apply cells_zero_no_moves; lia).
    destruct f1; destruct f2; simpl; rewrite ?Hm; auto.
  - destruct (moves p) as [|c0 l0] eqn:Em.
    + destruct f1; destruct f2; simpl; rewrite ?Em; auto.
    + assert (Hpos : 1 <= cells p).
      { apply (move_cells_pos p c0); rewrite Em; left; auto. }
      destruct f1 as [|f1]; [lia|].
      destruct f2 as [|f2]; [lia|].
      simpl.
      apply existsb_ext_in.
      intros x Hx.
      f_equal.
      pose proof (bite_cells_lt_moves p x Hx) as Hlt.
      apply (IH (bite p x)); lia.
Qed.

(** The stable value. *)
Definition win (p : pos) : bool := winsb (cells p) p.

Lemma winsb_win :
  forall p f, cells p <= f -> winsb f p = win p.
Proof.
  intros p f Hf; unfold win.
  apply (winsb_stable (cells p)); lia.
Qed.

Lemma win_no_moves :
  forall p, moves p = [] -> win p = false.
Proof.
  intros p Hm; unfold win.
  destruct (cells p); simpl; [auto|].
  rewrite Hm; auto.
Qed.

Lemma win_true_iff :
  forall p,
    win p = true <->
    exists c, In c (moves p) /\ win (bite p c) = false.
Proof.
  intros p; split.
  - intros Hw.
    unfold win in Hw.
    destruct (cells p) as [|k] eqn:Ec; [simpl in Hw; discriminate|].
    simpl in Hw.
    apply existsb_exists in Hw.
    destruct Hw as [c [Hcm Hneg]].
    apply negb_true_iff in Hneg.
    exists c; split; auto.
    rewrite <- (winsb_win (bite p c) k); auto.
    pose proof (bite_cells_lt_moves p c Hcm); lia.
  - intros [c [Hcm Hlose]].
    assert (Hpos : 1 <= cells p) by (apply (move_cells_pos p c); auto).
    unfold win.
    destruct (cells p) as [|k] eqn:Ec; [lia|].
    simpl.
    apply existsb_exists.
    exists c; split; auto.
    apply negb_true_iff.
    rewrite (winsb_win (bite p c) k); auto.
    pose proof (bite_cells_lt_moves p c Hcm); lia.
Qed.

Lemma win_false_iff :
  forall p,
    win p = false <->
    forall c, In c (moves p) -> win (bite p c) = true.
Proof.
  intros p; split.
  - intros Hw c Hcm.
    destruct (win (bite p c)) eqn:Eb; auto.
    exfalso.
    assert (Hg : win p = true); [| congruence].
    apply win_true_iff; exists c; auto.
  - intros H.
    destruct (win p) eqn:Ew; auto.
    apply (proj1 (win_true_iff p)) in Ew.
    destruct Ew as [c [Hcm Hlose]].
    rewrite (H c Hcm) in Hlose; discriminate.
Qed.

(** * Rectangles and strategy stealing *)

Definition rect (m n : nat) : pos := repeat n m.

Lemma cells_rect : forall m n, cells (rect m n) = m * n.
Proof. intros; apply cells_repeat. Qed.

Lemma in_moves_rect :
  forall m n i j,
    In (i, j) (moves (rect m n)) <->
    i < m /\ j < n /\ (i, j) <> (0, 0).
Proof.
  intros m n i j; rewrite in_moves_iff; unfold rect.
  rewrite repeat_length.
  split.
  - intros [Hi [Hj Hne]].
    rewrite (nth_repeat_lt n m i Hi) in Hj.
    repeat split; auto.
  - intros [Hi [Hj Hne]].
    repeat split; auto.
    rewrite (nth_repeat_lt n m i Hi); auto.
Qed.

(** The far corner: the unique square whose bite removes only it. *)
Definition far_corner (m n : nat) : nat * nat := (m - 1, n - 1).

Lemma far_corner_move :
  forall m n, 1 <= m -> 1 <= n -> 2 <= m * n ->
  In (far_corner m n) (moves (rect m n)).
Proof.
  intros m n Hm Hn Hmn; apply in_moves_rect.
  repeat split; try lia.
  intros He; inversion He.
  assert (m = 1) by lia.
  assert (n = 1) by lia.
  subst; simpl in Hmn; lia.
Qed.

(** A bite in the corner-less rectangle removes the far corner as well. *)
Lemma bite_after_corner :
  forall m n i j,
    1 <= m -> 1 <= n ->
    In (i, j) (moves (bite (rect m n) (far_corner m n))) ->
    In (i, j) (moves (rect m n)) /\
    bite (bite (rect m n) (far_corner m n)) (i, j) =
    bite (rect m n) (i, j).
Proof.
  intros m n i j Hm Hn Hin.
  destruct n as [|n']; [lia|].
  destruct n' as [|n'].
  - (* single-column board: the corner bite removes the last row *)
    assert (EC : bite (rect m 1) (far_corner m 1) = rect (m - 1) 1).
    { unfold far_corner, rect, bite; simpl.
      apply firstn_repeat_le; lia. }
    rewrite EC in Hin.
    apply in_moves_rect in Hin.
    destruct Hin as [Hi [Hj Hne]].
    assert (Hj0 : j = 0) by lia; subst j.
    split.
    + apply in_moves_rect; repeat split; auto; lia.
    + rewrite EC; unfold rect, bite; simpl.
      rewrite firstn_repeat_le by lia.
      rewrite firstn_repeat_le by lia.
      auto.
  - (* at least two columns: the corner bite clips the last row *)
    set (n := S (S n')) in *.
    assert (EC : bite (rect m n) (far_corner m n) =
                 repeat n (m - 1) ++ [n - 1]).
    { unfold far_corner, rect, bite.
      assert (En : n - 1 = S n') by (unfold n; lia).
      rewrite En.
      rewrite firstn_repeat_le by lia.
      rewrite skipn_repeat_le by lia.
      replace (m - (m - 1)) with 1 by lia.
      simpl.
      f_equal.
      f_equal.
      f_equal.
      unfold n; lia.
    }
    rewrite EC in Hin.
    apply in_moves_iff in Hin.
    destruct Hin as [Hi [Hj Hne]].
    rewrite length_app, repeat_length in Hi; simpl in Hi.
    assert (Him : i < m) by lia.
    assert (Hnth : nth i (repeat n (m - 1) ++ [n - 1]) 0 <= n).
    { destruct (Nat.lt_ge_cases i (m - 1)) as [Hlt | Hge].
      - rewrite app_nth1 by (rewrite repeat_length; auto).
        rewrite nth_repeat_lt by auto; lia.
      - rewrite app_nth2 by (rewrite repeat_length; auto).
        rewrite repeat_length.
        assert (i - (m - 1) = 0) by lia.
        rewrite H; simpl; lia. }
    assert (HinR : In (i, j) (moves (rect m n))).
    { apply in_moves_rect; repeat split; auto; lia. }
    split; auto.
    rewrite EC.
    assert (Hfirst : firstn i (repeat n (m - 1) ++ [n - 1]) =
                     firstn i (rect m n)).
    { rewrite firstn_app.
      rewrite repeat_length.
      replace (i - (m - 1)) with 0 by lia.
      simpl.
      rewrite app_nil_r.
      unfold rect.
      rewrite firstn_repeat_le by lia.
      rewrite firstn_repeat_le by lia.
      auto. }
    destruct j as [|j'].
    + change (firstn i (repeat n (m - 1) ++ [n - 1]) = firstn i (rect m n)).
      exact Hfirst.
    + assert (Hjn : S j' <= n - 1).
      { destruct (Nat.lt_ge_cases i (m - 1)) as [Hlt | Hge].
        - rewrite app_nth1 in Hj by (rewrite repeat_length; auto).
          rewrite nth_repeat_lt in Hj by auto.
          lia.
        - rewrite app_nth2 in Hj by (rewrite repeat_length; auto).
          rewrite repeat_length in Hj.
          assert (i - (m - 1) = 0) by lia.
          rewrite H in Hj; simpl in Hj; lia. }
      change (firstn i (repeat n (m - 1) ++ [n - 1]) ++
              map (Nat.min (S j')) (skipn i (repeat n (m - 1) ++ [n - 1])) =
              firstn i (rect m n) ++
              map (Nat.min (S j')) (skipn i (rect m n))).
      rewrite Hfirst.
      f_equal.
      rewrite skipn_app.
      rewrite skipn_repeat_le by lia.
      rewrite repeat_length.
      replace (i - (m - 1)) with 0 by lia.
      rewrite skipn_O.
      unfold rect.
      rewrite skipn_repeat_le by lia.
      rewrite map_app.
      rewrite !map_repeat_eq.
      change (map (Nat.min (S j')) [n - 1]) with [Nat.min (S j') (n - 1)].
      rewrite (Nat.min_l (S j') n) by lia.
      rewrite (Nat.min_l (S j') (n - 1)) by lia.
      replace (m - i) with (S (m - 1 - i)) by lia.
      rewrite repeat_S_app.
      auto.
Qed.

(** The strategy steal: the reply to the corner bite is itself a first move. *)
Theorem chomp_first_player_wins :
  forall m n, 1 <= m -> 1 <= n -> 2 <= m * n ->
  win (rect m n) = true.
Proof.
  intros m n Hm Hn Hmn.
  destruct (win (rect m n)) eqn:Ew; auto.
  exfalso.
  assert (Hall : forall c, In c (moves (rect m n)) ->
                 win (bite (rect m n) c) = true).
  { apply (proj1 (win_false_iff (rect m n))); auto. }
  assert (HC : win (bite (rect m n) (far_corner m n)) = true).
  { apply Hall, far_corner_move; auto. }
  apply (proj1 (win_true_iff _)) in HC.
  destruct HC as [[i j] [Hin Hlose]].
  destruct (bite_after_corner m n i j Hm Hn Hin) as [HinR Heq].
  rewrite Heq in Hlose.
  rewrite (Hall _ HinR) in Hlose; discriminate.
Qed.

(** * The explicit strategy on squares *)

(** [ell a b]: poisoned row of width [S b] over [a] rows of width one. *)
Definition ell (a b : nat) : pos := S b :: repeat 1 a.

Lemma in_moves_ell :
  forall a b i j,
    In (i, j) (moves (ell a b)) <->
    (i = 0 /\ 1 <= j <= b) \/ (1 <= i <= a /\ j = 0).
Proof.
  intros a b i j; rewrite in_moves_iff; unfold ell; simpl.
  rewrite repeat_length.
  split.
  - intros [Hi [Hj Hne]].
    destruct i as [|i].
    + left; split; auto.
      split; [|lia].
      destruct j; [exfalso; apply Hne; auto | lia].
    + right.
      rewrite nth_repeat_lt in Hj by lia.
      split; lia.
  - intros [[-> [Hj1 Hj2]] | [[Hi1 Hi2] ->]].
    + repeat split; try lia.
      intros He; inversion He; lia.
    + repeat split.
      * lia.
      * destruct i; [lia|].
        rewrite nth_repeat_lt by lia; lia.
      * intros He; inversion He; lia.
Qed.

Lemma bite_ell_row :
  forall a b j, j <= b -> bite (ell a b) (0, S j) = ell a j.
Proof.
  intros a b j Hj; unfold ell.
  change (Nat.min (S j) (S b) :: map (Nat.min (S j)) (repeat 1 a) =
          S j :: repeat 1 a).
  rewrite map_repeat_eq.
  rewrite (Nat.min_l (S j) (S b)) by lia.
  rewrite (Nat.min_r (S j) 1) by lia.
  auto.
Qed.

Lemma bite_ell_col :
  forall a b i, i <= a -> bite (ell a b) (S i, 0) = ell i b.
Proof.
  intros a b i Hi; unfold ell.
  change (S b :: firstn i (repeat 1 a) = S b :: repeat 1 i).
  rewrite firstn_repeat_le by lia.
  auto.
Qed.

(** A symmetric L loses; an asymmetric L wins by restoring the symmetry. *)
Lemma ell_win_iff :
  forall s a b, a + b <= s -> (win (ell a b) = true <-> a <> b).
Proof.
  induction s as [|s IH]; intros a b Hs.
  - assert (Ha : a = 0) by lia.
    assert (Hb : b = 0) by lia.
    subst.
    assert (E : win (ell 0 0) = false) by reflexivity.
    split.
    + intros Hw; congruence.
    + intros Hne; exfalso; apply Hne; auto.
  - destruct (Nat.lt_trichotomy a b) as [Hab | [Hab | Hab]].
    + (* a < b: bite the poisoned row down to symmetric width *)
      split; [intros _; lia|].
      intros _.
      apply (proj2 (win_true_iff (ell a b))).
      exists (0, S a); split.
      * apply in_moves_ell; left; repeat split; lia.
      * rewrite bite_ell_row by lia.
        assert (Hbnd : a + a <= s) by lia.
        destruct (win (ell a a)) eqn:Ew; auto.
        pose proof (proj1 (IH a a Hbnd) Ew); lia.
    + (* a = b: every move breaks the symmetry into a winning L *)
      subst b.
      assert (Hfalse : win (ell a a) = false).
      { apply (proj2 (win_false_iff (ell a a))).
        intros [i j] Hm.
        apply in_moves_ell in Hm.
        destruct Hm as [[-> [Hj1 Hj2]] | [[Hi1 Hi2] ->]].
        - destruct j as [|j']; [lia|].
          rewrite bite_ell_row by lia.
          assert (Hbnd : a + j' <= s) by lia.
          apply (proj2 (IH a j' Hbnd)); lia.
        - destruct i as [|i']; [lia|].
          rewrite bite_ell_col by lia.
          assert (Hbnd : i' + a <= s) by lia.
          apply (proj2 (IH i' a Hbnd)); lia. }
      split.
      * intros Hw; congruence.
      * intros Hne; exfalso; apply Hne; auto.
    + (* b < a: bite the column down to symmetric height *)
      split; [intros _; lia|].
      intros _.
      apply (proj2 (win_true_iff (ell a b))).
      exists (S b, 0); split.
      * apply in_moves_ell; right; repeat split; lia.
      * rewrite bite_ell_col by lia.
        assert (Hbnd : b + b <= s) by lia.
        destruct (win (ell b b)) eqn:Ew; auto.
        pose proof (proj1 (IH b b Hbnd) Ew); lia.
Qed.

(** The closed form for every L, with no fuel bound to discharge. *)
Theorem chomp_ell : forall a b, win (ell a b) = negb (a =? b).
Proof.
  intros a b.
  destruct (Nat.eq_dec a b) as [-> | Hne].
  - rewrite Nat.eqb_refl.
    destruct (win (ell b b)) eqn:Ew; auto.
    exfalso.
    pose proof (proj1 (ell_win_iff (b + b) b b ltac:(lia)) Ew); lia.
  - rewrite <- Nat.eqb_neq in Hne; rewrite Hne.
    apply (proj2 (ell_win_iff (a + b) a b ltac:(lia))).
    apply Nat.eqb_neq; exact Hne.
Qed.

(** The move restoring the symmetry of an asymmetric L. *)
Definition ell_move (a b : nat) : nat * nat :=
  if a <? b then (0, S a) else (S b, 0).

(** On an asymmetric L that move is winning, and it is the strategy. *)
Theorem chomp_ell_move :
  forall a b,
    a <> b ->
    In (ell_move a b) (moves (ell a b)) /\
    win (bite (ell a b) (ell_move a b)) = false.
Proof.
  intros a b Hne; unfold ell_move.
  destruct (a <? b) eqn:Eab.
  - apply Nat.ltb_lt in Eab; split.
    + apply in_moves_ell; left; split; [reflexivity | lia].
    + rewrite bite_ell_row by lia.
      rewrite chomp_ell, Nat.eqb_refl; reflexivity.
  - apply Nat.ltb_ge in Eab; split.
    + apply in_moves_ell; right; split; [lia | reflexivity].
    + rewrite bite_ell_col by lia.
      rewrite chomp_ell, Nat.eqb_refl; reflexivity.
Qed.

(** A single column: the mover loses only on the bare poisoned square. *)
Theorem chomp_column :
  forall a, win (repeat 1 (S a)) = negb (a =? 0).
Proof.
  intros a.
  change (repeat 1 (S a)) with (ell a 0).
  rewrite chomp_ell; reflexivity.
Qed.

Lemma bite_square_center :
  forall n, 1 <= n ->
  bite (rect n n) (1, 1) = ell (n - 1) (n - 1).
Proof.
  intros n Hn; destruct n as [|n']; [lia|].
  unfold rect, ell.
  change (S n' :: map (Nat.min 1) (repeat (S n') n') =
          S (S n' - 1) :: repeat 1 (S n' - 1)).
  rewrite map_repeat_eq.
  replace (S n' - 1) with n' by lia.
  auto.
Qed.

(** On a square the bite at [(1, 1)] leaves the symmetric L. *)
Theorem chomp_square_opening :
  forall n, 2 <= n ->
  In (1, 1) (moves (rect n n)) /\
  win (bite (rect n n) (1, 1)) = false.
Proof.
  intros n Hn; split.
  - apply in_moves_rect; repeat split; try lia.
    discriminate.
  - rewrite bite_square_center by lia.
    destruct (win (ell (n - 1) (n - 1))) eqn:Ew; auto.
    assert (Hs : (n - 1) + (n - 1) <= (n - 1) + (n - 1)) by lia.
    pose proof (proj1 (ell_win_iff ((n - 1) + (n - 1)) (n - 1) (n - 1) Hs) Ew).
    lia.
Qed.

Corollary chomp_square_wins :
  forall n, 2 <= n -> win (rect n n) = true.
Proof.
  intros n Hn.
  apply (proj2 (win_true_iff (rect n n))).
  destruct (chomp_square_opening n Hn) as [Hin Hlose].
  exists (1, 1); auto.
Qed.

(** * One and two rows *)

Lemma bite_one_row :
  forall a j, bite [a] (0, S j) = [Nat.min (S j) a].
Proof. intros a j; reflexivity. Qed.

Lemma bite_row0 :
  forall a b j, bite [a; b] (0, S j) = [Nat.min (S j) a; Nat.min (S j) b].
Proof. intros a b j; reflexivity. Qed.

Lemma bite_row1_zero : forall a b, bite [a; b] (1, 0) = [a].
Proof. intros a b; reflexivity. Qed.

Lemma bite_row1 :
  forall a b j, bite [a; b] (1, S j) = [a; Nat.min (S j) b].
Proof. intros a b j; reflexivity. Qed.

Lemma win_one_row : forall a, win [a] = (2 <=? a).
Proof.
  intros a.
  assert (H1 : win [1] = false).
  { apply win_false_iff; intros [i j] Hc.
    apply in_moves_iff in Hc; destruct Hc as [Hi [Hj Hne]].
    simpl in Hi, Hj.
    destruct i as [|i']; [|lia].
    destruct j as [|j']; [exfalso; apply Hne; reflexivity | simpl in Hj; lia]. }
  destruct a as [|a'].
  - apply win_false_iff; intros [i j] Hc.
    apply in_moves_iff in Hc; destruct Hc as [Hi [Hj Hne]].
    simpl in Hi, Hj.
    destruct i as [|i']; simpl in Hj; lia.
  - destruct a' as [|a''].
    + exact H1.
    + apply win_true_iff.
      exists (0, 1); split.
      * apply in_moves_iff; repeat split; simpl; try lia.
        intros He; inversion He; lia.
      * rewrite bite_one_row.
        change (Nat.min 1 (S (S a''))) with 1.
        exact H1.
Qed.

(** On two rows the mover loses exactly when the poisoned row is one longer. *)
Theorem chomp_two_rows :
  forall a b, 1 <= a -> b <= a -> win [a; b] = negb (Nat.eqb a (S b)).
Proof.
  assert (Haux : forall N a b,
            a + b <= N -> 1 <= a -> b <= a ->
            win [a; b] = negb (Nat.eqb a (S b))).
  { induction N as [|N IH]; intros a b HN Ha Hb; [lia|].
    destruct (Nat.eq_dec a (S b)) as [-> | Hne].
    - (* the losing shape: every bite leaves a winning position *)
      replace (Nat.eqb (S b) (S b)) with true
        by (symmetry; apply Nat.eqb_eq; reflexivity).
      apply win_false_iff; intros [i j] Hc.
      apply in_moves_iff in Hc; destruct Hc as [Hi [Hj Hnz]].
      simpl in Hi.
      destruct i as [|i'].
      + change (nth 0 [S b; b] 0) with (S b) in Hj.
        destruct j as [|j']; [exfalso; apply Hnz; reflexivity|].
        rewrite bite_row0.
        replace (Nat.min (S j') (S b)) with (S j') by lia.
        replace (Nat.min (S j') b) with (S j') by lia.
        rewrite (IH (S j') (S j')) by lia.
        replace (Nat.eqb (S j') (S (S j'))) with false
          by (symmetry; apply Nat.eqb_neq; lia).
        reflexivity.
      + destruct i' as [|i'']; [|simpl in Hi; lia].
        change (nth 1 [S b; b] 0) with b in Hj.
        destruct j as [|j'].
        * rewrite bite_row1_zero, win_one_row.
          replace (2 <=? S b) with true by (symmetry; apply Nat.leb_le; lia).
          reflexivity.
        * rewrite bite_row1.
          replace (Nat.min (S j') b) with (S j') by lia.
          rewrite (IH (S b) (S j')) by lia.
          replace (Nat.eqb (S b) (S (S j'))) with false
            by (symmetry; apply Nat.eqb_neq; lia).
          reflexivity.
    - (* any other shape: bite down to the losing shape *)
      replace (Nat.eqb a (S b)) with false
        by (symmetry; apply Nat.eqb_neq; lia).
      apply win_true_iff.
      destruct (Nat.eq_dec a b) as [-> | Hab].
      + (* a square: shorten the lower row by one *)
        destruct b as [|b']; [lia|].
        destruct b' as [|b''].
        * exists (1, 0); split.
          -- apply in_moves_iff; repeat split; simpl; try lia.
             intros He; inversion He; lia.
          -- rewrite bite_row1_zero, win_one_row; reflexivity.
        * exists (1, S b''); split.
          -- apply in_moves_iff; repeat split; simpl; try lia.
             intros He; inversion He; lia.
          -- rewrite bite_row1.
             replace (Nat.min (S b'') (S (S b''))) with (S b'') by lia.
             rewrite (IH (S (S b'')) (S b'')) by lia.
             replace (Nat.eqb (S (S b'')) (S (S b''))) with true
               by (symmetry; apply Nat.eqb_eq; reflexivity).
             reflexivity.
      + (* a longer poisoned row: cut it to one more than the lower row *)
        exists (0, S b); split.
        * apply in_moves_iff; repeat split; simpl; try lia.
          intros He; inversion He; lia.
        * rewrite bite_row0.
          replace (Nat.min (S b) a) with (S b) by lia.
          replace (Nat.min (S b) b) with b by lia.
          rewrite (IH (S b) b) by lia.
          replace (Nat.eqb (S b) (S b)) with true
            by (symmetry; apply Nat.eqb_eq; reflexivity).
          reflexivity. }
  intros a b Ha Hb; apply (Haux (a + b)); lia.
Qed.

Corollary chomp_two_rows_lost :
  forall a b, 1 <= a -> b <= a -> (win [a; b] = false <-> a = S b).
Proof.
  intros a b Ha Hb; rewrite chomp_two_rows by auto.
  rewrite negb_false_iff, Nat.eqb_eq; apply iff_refl.
Qed.

(** The winning move on a two-row rectangle: shorten the lower row by one. *)
Corollary chomp_two_row_opening :
  forall n, 2 <= n -> win (bite [n; n] (1, n - 1)) = false.
Proof.
  intros n Hn.
  replace (n - 1) with (S (n - 2)) by lia.
  rewrite bite_row1.
  replace (Nat.min (S (n - 2)) n) with (n - 1) by lia.
  rewrite chomp_two_rows by lia.
  replace (Nat.eqb n (S (n - 1))) with true
    by (symmetry; apply Nat.eqb_eq; lia).
  reflexivity.
Qed.

(** * Three rows *)

(** Losing three-row positions, found by computation. *)
Example chomp_three_221 : win [2; 2; 1] = false.
Proof. vm_compute; reflexivity. Qed.

Example chomp_three_311 : win [3; 1; 1] = false.
Proof. vm_compute; reflexivity. Qed.

Example chomp_three_320 : win [3; 2; 0] = false.
Proof. vm_compute; reflexivity. Qed.

Example chomp_three_422 : win [4; 2; 2] = false.
Proof. vm_compute; reflexivity. Qed.

Example chomp_three_430 : win [4; 3; 0] = false.
Proof. vm_compute; reflexivity. Qed.

Example chomp_three_211 : win [2; 1; 1] = true.
Proof. vm_compute; reflexivity. Qed.

Example chomp_three_333 : win [3; 3; 3] = true.
Proof. vm_compute; reflexivity. Qed.

(** * Solved boards *)

Example chomp_2x2 : win (rect 2 2) = true.
Proof. vm_compute; reflexivity. Qed.

Example chomp_2x3_opening : win (bite (rect 2 3) (1, 2)) = false.
Proof. vm_compute; reflexivity. Qed.

Example chomp_3x3_opening : win (bite (rect 3 3) (1, 1)) = false.
Proof. vm_compute; reflexivity. Qed.
