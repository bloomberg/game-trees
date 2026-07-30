(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Domineering: Left places vertical dominoes and Right horizontal ones. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.
From Stdlib Require Import Permutation.

Import ListNotations.
Require Import GameTrees.Helpers.

Require Import GameTrees.Conway.

(** * Cells and boards *)

Definition cell : Type := (nat * nat)%type.

Definition cell_eqb (c d : cell) : bool :=
  (Nat.eqb (fst c) (fst d) && Nat.eqb (snd c) (snd d))%bool.

Lemma cell_eqb_true_iff : forall c d, cell_eqb c d = true <-> c = d.
Proof.
  intros [a b] [x y]; unfold cell_eqb; simpl.
  rewrite andb_true_iff, !Nat.eqb_eq.
  split.
  - intros [-> ->]; auto.
  - intros E; inversion E; auto.
Qed.

Lemma cell_eqb_refl : forall c, cell_eqb c c = true.
Proof. intros c; apply cell_eqb_true_iff; auto. Qed.

Definition memb (c : cell) (b : list cell) : bool := existsb (cell_eqb c) b.

Lemma memb_true_iff : forall c b, memb c b = true <-> In c b.
Proof.
  intros c b; unfold memb; rewrite existsb_exists; split.
  - intros [x [Hx He]]; apply cell_eqb_true_iff in He; subst; auto.
  - intros Hin; exists c; split; auto; apply cell_eqb_refl.
Qed.

Lemma memb_false_iff : forall c b, memb c b = false <-> ~ In c b.
Proof.
  intros c b; split.
  - intros Hm Hin; apply memb_true_iff in Hin; congruence.
  - intros Hn; destruct (memb c b) eqn:E; auto.
    apply memb_true_iff in E; contradiction.
Qed.

(** The cell below and the cell to the right: the second cell of a domino. *)
Definition below (c : cell) : cell := (S (fst c), snd c).
Definition rightof (c : cell) : cell := (fst c, S (snd c)).

Definition remove2 (c d : cell) (b : list cell) : list cell :=
  filter (fun x => (negb (cell_eqb x c) && negb (cell_eqb x d))%bool) b.

Lemma remove2_incl : forall c d b, incl (remove2 c d b) b.
Proof.
  intros c d b x Hx; unfold remove2 in Hx.
  apply filter_In in Hx; tauto.
Qed.

Lemma remove2_id :
  forall c d b, ~ In c b -> ~ In d b -> remove2 c d b = b.
Proof.
  intros c d b Hc Hd; unfold remove2.
  induction b as [|x b IH]; auto.
  simpl.
  assert (Hx : (negb (cell_eqb x c) && negb (cell_eqb x d))%bool = true).
  { apply andb_true_iff; split; apply negb_true_iff;
      apply not_true_is_false; intros He;
      apply cell_eqb_true_iff in He; subst; auto with datatypes. }
  rewrite Hx, IH; auto with datatypes.
Qed.

Lemma filter_length_lt :
  forall (f : cell -> bool) b x,
    In x b -> f x = false -> length (filter f b) < length b.
Proof.
  intros f b x Hin Hf; induction b as [|a b IH]; [destruct Hin|].
  simpl; destruct Hin as [-> | Hin].
  - rewrite Hf.
    pose proof (filter_length_le f b); lia.
  - specialize (IH Hin).
    destruct (f a); simpl; lia.
Qed.

Lemma remove2_length_lt :
  forall c d b, In c b -> length (remove2 c d b) < length b.
Proof.
  intros c d b Hin; unfold remove2.
  apply (filter_length_lt _ _ c); auto.
  apply andb_false_iff; left; apply negb_false_iff, cell_eqb_refl.
Qed.

(** * Moves *)

Definition vfits (b : list cell) (c : cell) : bool :=
  (memb c b && memb (below c) b)%bool.

Definition hfits (b : list cell) (c : cell) : bool :=
  (memb c b && memb (rightof c) b)%bool.

Definition lmoves (b : list cell) : list (list cell) :=
  map (fun c => remove2 c (below c) b) (filter (vfits b) b).

Definition rmoves (b : list cell) : list (list cell) :=
  map (fun c => remove2 c (rightof c) b) (filter (hfits b) b).

Lemma lmoves_shorter :
  forall b m, In m (lmoves b) -> length m < length b.
Proof.
  intros b m Hm; unfold lmoves in Hm.
  apply in_map_iff in Hm; destruct Hm as [c [<- Hc]].
  apply filter_In in Hc; destruct Hc as [Hin _].
  apply (filter_length_lt _ _ c); auto.
  apply andb_false_iff; left; apply negb_false_iff, cell_eqb_refl.
Qed.

Lemma rmoves_shorter :
  forall b m, In m (rmoves b) -> length m < length b.
Proof.
  intros b m Hm; unfold rmoves in Hm.
  apply in_map_iff in Hm; destruct Hm as [c [<- Hc]].
  apply filter_In in Hc; destruct Hc as [Hin _].
  apply (filter_length_lt _ _ c); auto.
  apply andb_false_iff; left; apply negb_false_iff, cell_eqb_refl.
Qed.

Lemma lmoves_incl :
  forall b m, In m (lmoves b) -> incl m b.
Proof.
  intros b m Hm; unfold lmoves in Hm.
  apply in_map_iff in Hm; destruct Hm as [c [<- _]].
  apply remove2_incl.
Qed.

Lemma rmoves_incl :
  forall b m, In m (rmoves b) -> incl m b.
Proof.
  intros b m Hm; unfold rmoves in Hm.
  apply in_map_iff in Hm; destruct Hm as [c [<- _]].
  apply remove2_incl.
Qed.

(** * The game of a board *)

(** The game of a board under a fuel bound. *)
Fixpoint dom (fuel : nat) (b : list cell) : pgame :=
  match fuel with
  | 0 => PG [] []
  | S f => PG (map (dom f) (lmoves b)) (map (dom f) (rmoves b))
  end.

Lemma dom_stable :
  forall N b f1 f2,
    length b <= N -> length b <= f1 -> length b <= f2 ->
    dom f1 b = dom f2 b.
Proof.
  induction N as [|N IH]; intros b f1 f2 HN Hf1 Hf2.
  - assert (Hb : b = []) by (apply length_zero_iff_nil; lia).
    subst b.
    destruct f1; destruct f2; reflexivity.
  - destruct f1 as [|f1].
    + assert (Hb : b = []) by (apply length_zero_iff_nil; lia).
      subst b; destruct f2; reflexivity.
    + destruct f2 as [|f2].
      * assert (Hb : b = []) by (apply length_zero_iff_nil; lia).
        subst b; reflexivity.
      * simpl; f_equal; apply map_ext_in; intros m Hm.
        -- pose proof (lmoves_shorter b m Hm).
           apply (IH m); lia.
        -- pose proof (rmoves_shorter b m Hm).
           apply (IH m); lia.
Qed.

(** The value of a board. *)
Definition Dom (b : list cell) : pgame := dom (length b) b.

Lemma dom_Dom :
  forall f b, length b <= f -> dom f b = Dom b.
Proof.
  intros f b Hf; unfold Dom; apply (dom_stable (length b)); lia.
Qed.

Lemma Dom_eq :
  forall b, Dom b = PG (map Dom (lmoves b)) (map Dom (rmoves b)).
Proof.
  intros b; unfold Dom at 1.
  destruct (length b) as [|f] eqn:Eb.
  - assert (Hb : b = []) by (apply length_zero_iff_nil; auto).
    subst b; reflexivity.
  - simpl; f_equal; apply map_ext_in; intros m Hm.
    + pose proof (lmoves_shorter b m Hm).
      apply dom_Dom; lia.
    + pose proof (rmoves_shorter b m Hm).
      apply dom_Dom; lia.
Qed.

Lemma lopts_Dom : forall b, lopts (Dom b) = map Dom (lmoves b).
Proof. intros b; rewrite Dom_eq; reflexivity. Qed.

Lemma ropts_Dom : forall b, ropts (Dom b) = map Dom (rmoves b).
Proof. intros b; rewrite Dom_eq; reflexivity. Qed.

(** * Decomposition *)

(** Two cells touch when one domino could cover both, or they coincide. *)
Definition touching (c d : cell) : Prop :=
  c = d \/ d = below c \/ d = rightof c \/ c = below d \/ c = rightof d.

(** Regions no domino can straddle. *)
Definition sep (b1 b2 : list cell) : Prop :=
  forall c d, In c b1 -> In d b2 -> ~ touching c d.

Lemma sep_incl_l :
  forall b1 b1' b2, incl b1' b1 -> sep b1 b2 -> sep b1' b2.
Proof. intros b1 b1' b2 Hincl Hs c d Hc Hd; apply Hs; auto. Qed.

Lemma sep_incl_r :
  forall b1 b2 b2', incl b2' b2 -> sep b1 b2 -> sep b1 b2'.
Proof. intros b1 b2 b2' Hincl Hs c d Hc Hd; apply Hs; auto. Qed.

Lemma sep_notin :
  forall b1 b2 c, sep b1 b2 -> In c b1 -> ~ In c b2.
Proof.
  intros b1 b2 c Hs Hc Hin.
  apply (Hs c c Hc Hin); left; auto.
Qed.

Lemma sep_below_r :
  forall b1 b2 c, sep b1 b2 -> In c b1 -> ~ In (below c) b2.
Proof.
  intros b1 b2 c Hs Hc Hin.
  apply (Hs c (below c) Hc Hin); right; left; auto.
Qed.

Lemma sep_rightof_r :
  forall b1 b2 c, sep b1 b2 -> In c b1 -> ~ In (rightof c) b2.
Proof.
  intros b1 b2 c Hs Hc Hin.
  apply (Hs c (rightof c) Hc Hin); right; right; left; auto.
Qed.

Lemma sep_below_l :
  forall b1 b2 c, sep b1 b2 -> In c b2 -> ~ In (below c) b1.
Proof.
  intros b1 b2 c Hs Hc Hin.
  apply (Hs (below c) c Hin Hc); right; right; right; left; auto.
Qed.

Lemma sep_rightof_l :
  forall b1 b2 c, sep b1 b2 -> In c b2 -> ~ In (rightof c) b1.
Proof.
  intros b1 b2 c Hs Hc Hin.
  apply (Hs (rightof c) c Hin Hc); right; right; right; right; auto.
Qed.

Lemma memb_app :
  forall c b1 b2, memb c (b1 ++ b2) = (memb c b1 || memb c b2)%bool.
Proof. intros c b1 b2; apply existsb_app. Qed.

(** On a separated board every placement lies within one region. *)
Lemma lmoves_app :
  forall b1 b2,
    sep b1 b2 ->
    lmoves (b1 ++ b2) =
    map (fun m => m ++ b2) (lmoves b1) ++ map (fun m => b1 ++ m) (lmoves b2).
Proof.
  intros b1 b2 Hs; unfold lmoves.
  rewrite filter_app.
  assert (E1 : filter (vfits (b1 ++ b2)) b1 = filter (vfits b1) b1).
  { apply filter_ext_in; intros c Hc; unfold vfits.
    rewrite !memb_app.
    rewrite (proj2 (memb_false_iff c b2) (sep_notin b1 b2 c Hs Hc)).
    rewrite (proj2 (memb_false_iff (below c) b2)
               (sep_below_r b1 b2 c Hs Hc)).
    rewrite !orb_false_r; reflexivity. }
  assert (E2 : filter (vfits (b1 ++ b2)) b2 = filter (vfits b2) b2).
  { apply filter_ext_in; intros c Hc; unfold vfits.
    rewrite !memb_app.
    rewrite (proj2 (memb_false_iff c b1)
               (fun H => sep_notin b1 b2 c Hs H Hc)).
    rewrite (proj2 (memb_false_iff (below c) b1)
               (sep_below_l b1 b2 c Hs Hc)).
    reflexivity. }
  rewrite E1, E2, map_app.
  f_equal.
  - rewrite map_map; apply map_ext_in; intros c Hc.
    apply filter_In in Hc; destruct Hc as [Hc _].
    unfold remove2; rewrite filter_app.
    f_equal.
    apply remove2_id.
    + exact (sep_notin b1 b2 c Hs Hc).
    + exact (sep_below_r b1 b2 c Hs Hc).
  - rewrite map_map; apply map_ext_in; intros c Hc.
    apply filter_In in Hc; destruct Hc as [Hc _].
    unfold remove2; rewrite filter_app.
    f_equal.
    apply remove2_id.
    + intros Hin; exact (sep_notin b1 b2 c Hs Hin Hc).
    + exact (sep_below_l b1 b2 c Hs Hc).
Qed.

Lemma rmoves_app :
  forall b1 b2,
    sep b1 b2 ->
    rmoves (b1 ++ b2) =
    map (fun m => m ++ b2) (rmoves b1) ++ map (fun m => b1 ++ m) (rmoves b2).
Proof.
  intros b1 b2 Hs; unfold rmoves.
  rewrite filter_app.
  assert (E1 : filter (hfits (b1 ++ b2)) b1 = filter (hfits b1) b1).
  { apply filter_ext_in; intros c Hc; unfold hfits.
    rewrite !memb_app.
    rewrite (proj2 (memb_false_iff c b2) (sep_notin b1 b2 c Hs Hc)).
    rewrite (proj2 (memb_false_iff (rightof c) b2)
               (sep_rightof_r b1 b2 c Hs Hc)).
    rewrite !orb_false_r; reflexivity. }
  assert (E2 : filter (hfits (b1 ++ b2)) b2 = filter (hfits b2) b2).
  { apply filter_ext_in; intros c Hc; unfold hfits.
    rewrite !memb_app.
    rewrite (proj2 (memb_false_iff c b1)
               (fun H => sep_notin b1 b2 c Hs H Hc)).
    rewrite (proj2 (memb_false_iff (rightof c) b1)
               (sep_rightof_l b1 b2 c Hs Hc)).
    reflexivity. }
  rewrite E1, E2, map_app.
  f_equal.
  - rewrite map_map; apply map_ext_in; intros c Hc.
    apply filter_In in Hc; destruct Hc as [Hc _].
    unfold remove2; rewrite filter_app.
    f_equal.
    apply remove2_id.
    + exact (sep_notin b1 b2 c Hs Hc).
    + exact (sep_rightof_r b1 b2 c Hs Hc).
  - rewrite map_map; apply map_ext_in; intros c Hc.
    apply filter_In in Hc; destruct Hc as [Hc _].
    unfold remove2; rewrite filter_app.
    f_equal.
    apply remove2_id.
    + intros Hin; exact (sep_notin b1 b2 c Hs Hin Hc).
    + exact (sep_rightof_l b1 b2 c Hs Hc).
Qed.

(** A board split into unstraddleable regions is the sum of the regions. *)
Theorem Dom_app :
  forall b1 b2, sep b1 b2 ->
  gequiv (Dom (b1 ++ b2)) (padd (Dom b1) (Dom b2)) = true.
Proof.
  assert (Haux : forall N b1 b2,
            length b1 + length b2 <= N -> sep b1 b2 ->
            gequiv (Dom (b1 ++ b2)) (padd (Dom b1) (Dom b2)) = true).
  { induction N as [|N IH]; intros b1 b2 HN Hs.
    - assert (Hb1 : b1 = []) by (apply length_zero_iff_nil; lia).
      assert (Hb2 : b2 = []) by (apply length_zero_iff_nil; lia).
      subst; rewrite padd_zero_r; apply gequiv_refl.
    - apply gequiv_of_opts.
      + rewrite lopts_Dom, lopts_padd, !lopts_Dom.
        rewrite (lmoves_app b1 b2 Hs), map_app, !map_map.
        cbv beta.
        apply opts_equiv_app_map; intros m Hm.
        * apply IH.
          -- pose proof (lmoves_shorter b1 m Hm); lia.
          -- apply (sep_incl_l b1); auto; apply lmoves_incl; auto.
        * apply IH.
          -- pose proof (lmoves_shorter b2 m Hm); lia.
          -- apply (sep_incl_r _ b2); auto; apply lmoves_incl; auto.
      + rewrite ropts_Dom, ropts_padd, !ropts_Dom.
        rewrite (rmoves_app b1 b2 Hs), map_app, !map_map.
        cbv beta.
        apply opts_equiv_app_map; intros m Hm.
        * apply IH.
          -- pose proof (rmoves_shorter b1 m Hm); lia.
          -- apply (sep_incl_l b1); auto; apply rmoves_incl; auto.
        * apply IH.
          -- pose proof (rmoves_shorter b2 m Hm); lia.
          -- apply (sep_incl_r _ b2); auto; apply rmoves_incl; auto. }
  intros b1 b2 Hs; apply (Haux (length b1 + length b2)); auto.
Qed.

(** * Decomposition into any number of regions *)

Fixpoint sepall (bs : list (list cell)) : Prop :=
  match bs with
  | [] => True
  | b :: rest => (forall b', In b' rest -> sep b b') /\ sepall rest
  end.

Lemma sep_concat :
  forall b rest, (forall b', In b' rest -> sep b b') -> sep b (concat rest).
Proof.
  intros b rest H c d Hc Hd.
  apply in_concat in Hd; destruct Hd as [b' [Hb' Hd]].
  apply (H b' Hb' c d); auto.
Qed.

(** A board split into any number of unstraddleable regions is their sum. *)
Theorem Dom_concat :
  forall bs,
    sepall bs ->
    gequiv (Dom (concat bs))
           (fold_right (fun b acc => padd (Dom b) acc) zero bs) = true.
Proof.
  induction bs as [|b rest IH]; intros Hs.
  - apply gequiv_refl.
  - destruct Hs as [Hpair Hrest].
    change (concat (b :: rest)) with (b ++ concat rest).
    apply (gequiv_trans _ (padd (Dom b) (Dom (concat rest)))).
    + apply Dom_app, sep_concat; auto.
    + change (fold_right (fun x acc => padd (Dom x) acc) zero (b :: rest))
        with (padd (Dom b) (fold_right (fun x acc => padd (Dom x) acc) zero rest)).
      apply gequiv_padd_l, IH; auto.
Qed.

(** * Reflection in the diagonal *)

Definition swapc (c : cell) : cell := (snd c, fst c).

Definition transpose (b : list cell) : list cell := map swapc b.

Lemma swapc_swapc : forall c, swapc (swapc c) = c.
Proof. intros [a b]; reflexivity. Qed.

Lemma swapc_below : forall c, swapc (below c) = rightof (swapc c).
Proof. intros [a b]; reflexivity. Qed.

Lemma swapc_rightof : forall c, swapc (rightof c) = below (swapc c).
Proof. intros [a b]; reflexivity. Qed.

Lemma cell_eqb_swapc :
  forall c d, cell_eqb (swapc c) (swapc d) = cell_eqb c d.
Proof.
  intros [a b] [x y]; unfold cell_eqb, swapc; simpl.
  apply andb_comm.
Qed.

Lemma filter_map_swapc :
  forall p b,
    filter p (map swapc b) = map swapc (filter (fun x => p (swapc x)) b).
Proof.
  intros p b; induction b as [|x b IH]; simpl; auto.
  destruct (p (swapc x)); simpl; congruence.
Qed.

Lemma memb_transpose :
  forall c b, memb (swapc c) (transpose b) = memb c b.
Proof.
  intros c b; unfold transpose, memb.
  rewrite existsb_map.
  apply existsb_ext_in; intros x _; apply cell_eqb_swapc.
Qed.

Lemma remove2_transpose :
  forall c d b,
    remove2 (swapc c) (swapc d) (transpose b) = transpose (remove2 c d b).
Proof.
  intros c d b; unfold remove2, transpose.
  rewrite filter_map_swapc.
  f_equal; apply filter_ext; intros x.
  rewrite !cell_eqb_swapc; reflexivity.
Qed.

Lemma lmoves_transpose :
  forall b, lmoves (transpose b) = map transpose (rmoves b).
Proof.
  intros b; unfold lmoves, rmoves.
  unfold transpose at 2.
  rewrite filter_map_swapc, map_map.
  assert (Efit : forall x, vfits (transpose b) (swapc x) = hfits b x).
  { intros x; unfold vfits, hfits.
    replace (below (swapc x)) with (swapc (rightof x))
      by (rewrite swapc_rightof; reflexivity).
    rewrite !memb_transpose; reflexivity. }
  rewrite (filter_ext _ (hfits b)) by exact Efit.
  rewrite map_map.
  apply map_ext_in; intros x _.
  replace (below (swapc x)) with (swapc (rightof x))
    by (rewrite swapc_rightof; reflexivity).
  apply remove2_transpose.
Qed.

Lemma rmoves_transpose :
  forall b, rmoves (transpose b) = map transpose (lmoves b).
Proof.
  intros b; unfold lmoves, rmoves.
  unfold transpose at 2.
  rewrite filter_map_swapc, map_map.
  assert (Efit : forall x, hfits (transpose b) (swapc x) = vfits b x).
  { intros x; unfold vfits, hfits.
    replace (rightof (swapc x)) with (swapc (below x))
      by (rewrite swapc_below; reflexivity).
    rewrite !memb_transpose; reflexivity. }
  rewrite (filter_ext _ (vfits b)) by exact Efit.
  rewrite map_map.
  apply map_ext_in; intros x _.
  replace (rightof (swapc x)) with (swapc (below x))
    by (rewrite swapc_below; reflexivity).
  apply remove2_transpose.
Qed.

(** Reflection in the main diagonal negates the value. *)
Theorem Dom_transpose :
  forall b, Dom (transpose b) = pneg (Dom b).
Proof.
  assert (Haux : forall N b, length b <= N -> Dom (transpose b) = pneg (Dom b)).
  { induction N as [|N IH]; intros b HN.
    - assert (Hb : b = []) by (apply length_zero_iff_nil; lia).
      subst b; reflexivity.
    - rewrite Dom_eq, (Dom_eq b).
      rewrite lmoves_transpose, rmoves_transpose.
      change (pneg (PG (map Dom (lmoves b)) (map Dom (rmoves b))))
        with (PG (map pneg (map Dom (rmoves b))) (map pneg (map Dom (lmoves b)))).
      rewrite !map_map.
      f_equal; apply map_ext_in; intros m Hm.
      + apply IH; pose proof (rmoves_shorter b m Hm); lia.
      + apply IH; pose proof (lmoves_shorter b m Hm); lia. }
  intros b; apply (Haux (length b)); lia.
Qed.

(** * The board is a set *)

Lemma perm_filter :
  forall (f : cell -> bool) l1 l2,
    Permutation l1 l2 -> Permutation (filter f l1) (filter f l2).
Proof.
  intros f l1 l2 H; induction H; simpl.
  - apply perm_nil.
  - destruct (f x); auto.
  - destruct (f x); destruct (f y); auto.
    apply perm_swap.
  - eapply perm_trans; eauto.
Qed.

Lemma remove2_perm :
  forall c d b1 b2,
    Permutation b1 b2 -> Permutation (remove2 c d b1) (remove2 c d b2).
Proof. intros c d b1 b2 H; unfold remove2; apply perm_filter; auto. Qed.

Lemma memb_perm :
  forall c l1 l2, Permutation l1 l2 -> memb c l1 = memb c l2.
Proof.
  intros c l1 l2 Hp.
  destruct (memb c l1) eqn:E1; destruct (memb c l2) eqn:E2; auto.
  - apply memb_true_iff in E1; apply memb_false_iff in E2.
    exfalso; apply E2; apply (Permutation_in _ Hp); auto.
  - apply memb_true_iff in E2; apply memb_false_iff in E1.
    exfalso; apply E1.
    apply (Permutation_in _ (Permutation_sym Hp)); auto.
Qed.

(** The value is invariant under reordering the cells. *)
Theorem Dom_perm :
  forall b1 b2, Permutation b1 b2 -> gequiv (Dom b1) (Dom b2) = true.
Proof.
  assert (Hone : forall N b1 b2,
            length b1 <= N -> Permutation b1 b2 ->
            gle (Dom b1) (Dom b2) = true).
  { induction N as [|N IH]; intros b1 b2 HN Hp.
    - assert (Hb1 : b1 = []) by (apply length_zero_iff_nil; lia).
      subst b1; apply Permutation_nil in Hp; subst b2; apply gle_refl.
    - pose proof (Permutation_length Hp) as Hlen.
      apply gle_of_opts.
      + intros y Hy.
        rewrite ropts_Dom in Hy.
        apply in_map_iff in Hy; destruct Hy as [m [<- Hm]].
        unfold rmoves in Hm; apply in_map_iff in Hm.
        destruct Hm as [c [<- Hc]].
        apply filter_In in Hc; destruct Hc as [Hc Hfit].
        assert (Hc1 : In c b1)
          by (apply (Permutation_in _ (Permutation_sym Hp)); auto).
        exists (Dom (remove2 c (rightof c) b1)); split.
        * rewrite ropts_Dom; apply in_map_iff.
          exists (remove2 c (rightof c) b1); split; auto.
          unfold rmoves; apply in_map_iff.
          exists c; split; auto.
          apply filter_In; split; auto.
          unfold hfits in *.
          rewrite (memb_perm c b1 b2 Hp),
                  (memb_perm (rightof c) b1 b2 Hp); auto.
        * pose proof (remove2_length_lt c (rightof c) b1 Hc1).
          pose proof (remove2_length_lt c (rightof c) b2 Hc).
          apply gequiv_true_iff; split; apply IH; try lia.
          -- apply remove2_perm; auto.
          -- apply remove2_perm, Permutation_sym; auto.
      + intros x Hx.
        rewrite lopts_Dom in Hx.
        apply in_map_iff in Hx; destruct Hx as [m [<- Hm]].
        unfold lmoves in Hm; apply in_map_iff in Hm.
        destruct Hm as [c [<- Hc]].
        apply filter_In in Hc; destruct Hc as [Hc Hfit].
        assert (Hc2 : In c b2) by (apply (Permutation_in _ Hp); auto).
        exists (Dom (remove2 c (below c) b2)); split.
        * rewrite lopts_Dom; apply in_map_iff.
          exists (remove2 c (below c) b2); split; auto.
          unfold lmoves; apply in_map_iff.
          exists c; split; auto.
          apply filter_In; split; auto.
          unfold vfits in *.
          rewrite <- (memb_perm c b1 b2 Hp),
                  <- (memb_perm (below c) b1 b2 Hp); auto.
        * pose proof (remove2_length_lt c (below c) b1 Hc).
          pose proof (remove2_length_lt c (below c) b2 Hc2).
          apply gequiv_true_iff; split; apply IH; try lia.
          -- apply remove2_perm; auto.
          -- apply remove2_perm, Permutation_sym; auto. }
  intros b1 b2 Hp; apply gequiv_true_iff; split.
  - apply (Hone (length b1)); auto.
  - apply (Hone (length b2)); auto.
    apply Permutation_sym; auto.
Qed.

(** * Rectangles *)


Fixpoint rect (m n : nat) : list cell :=
  match m with
  | 0 => []
  | S k => rect k n ++ map (fun c => (k, c)) (seq 0 n)
  end.

Lemma in_rect :
  forall m n r c, In (r, c) (rect m n) <-> r < m /\ c < n.
Proof.
  induction m as [|k IH]; intros n r c; simpl.
  - split; [intros [] | intros [H _]; lia].
  - rewrite in_app_iff, IH, in_map_iff.
    split.
    + intros [[H1 H2] | [x [Hx Hs]]].
      * split; auto; lia.
      * inversion Hx; subst.
        apply in_seq in Hs; split; lia.
    + intros [H1 H2].
      destruct (Nat.eq_dec r k) as [-> | Hne].
      * right; exists c; split; auto.
        apply in_seq; lia.
      * left; split; auto; lia.
Qed.

Lemma NoDup_rect : forall m n, NoDup (rect m n).
Proof.
  induction m as [|k IH]; intros n; simpl; [constructor|].
  apply NoDup_app_disj.
  - apply IH.
  - apply NoDup_map_inj.
    + intros x y E; inversion E; auto.
    + apply seq_NoDup.
  - intros [r c] Hin1 Hin2.
    apply in_rect in Hin1.
    apply in_map_iff in Hin2; destruct Hin2 as [x [Hx _]].
    inversion Hx; subst; lia.
Qed.

Lemma transpose_rect_perm :
  forall m n, Permutation (transpose (rect m n)) (rect n m).
Proof.
  intros m n; apply NoDup_Permutation.
  - unfold transpose; apply NoDup_map_inj.
    + intros x y E.
      apply (f_equal swapc) in E; rewrite !swapc_swapc in E; auto.
    + apply NoDup_rect.
  - apply NoDup_rect.
  - intros [r c]; unfold transpose; rewrite in_map_iff, in_rect.
    split.
    + intros [[a b] [Hx Hin]].
      unfold swapc in Hx; simpl in Hx; inversion Hx; subst.
      apply in_rect in Hin; tauto.
    + intros [H1 H2].
      exists (c, r); split; [reflexivity|].
      apply in_rect; auto.
Qed.

(** A rectangle and its reflection have opposite values. *)
Theorem Dom_rect_transpose :
  forall m n, gequiv (Dom (rect m n)) (pneg (Dom (rect n m))) = true.
Proof.
  intros m n.
  apply gequiv_sym.
  rewrite <- (Dom_transpose (rect n m)).
  apply Dom_perm, transpose_rect_perm.
Qed.

(** * Columns and rows *)

Lemma filter_nil_of_false :
  forall (f : cell -> bool) (l : list cell),
    (forall x, In x l -> f x = false) -> filter f l = [].
Proof.
  intros f l H; induction l as [|a l IH]; [reflexivity|].
  simpl; rewrite (H a (or_introl eq_refl)).
  apply IH; intros x Hx; apply H; right; exact Hx.
Qed.

(** A board confined to one column offers Right nothing. *)
Lemma rmoves_nil_of_col :
  forall b, (forall c, In c b -> snd c = 0) -> rmoves b = [].
Proof.
  intros b Hc; unfold rmoves.
  rewrite (filter_nil_of_false (hfits b) b); [reflexivity|].
  intros x Hx.
  unfold hfits; apply andb_false_iff; right.
  apply memb_false_iff; intros Hin.
  pose proof (Hc x Hx) as Hx0.
  pose proof (Hc (rightof x) Hin) as Hr0.
  unfold rightof in Hr0; simpl in Hr0; congruence.
Qed.

Lemma col_rect : forall k c, In c (rect k 1) -> snd c = 0.
Proof.
  intros k [r j] H; apply in_rect in H; simpl; lia.
Qed.

(** Every sub-board reached by a left move stays in the column. *)
Lemma col_lmoves :
  forall b m,
    (forall c, In c b -> snd c = 0) -> In m (lmoves b) ->
    forall c, In c m -> snd c = 0.
Proof.
  intros b m Hb Hm c Hc.
  apply Hb, (lmoves_incl b m Hm); exact Hc.
Qed.

(** With Right immobile, Left wins a column of two or more outright. *)
Theorem Dom_col_Lwins :
  forall k, 2 <= k -> outc (Dom (rect k 1)) = Lwins.
Proof.
  intros k Hk.
  apply (proj2 (proj1 (proj2 (proj2 (outc_spec (Dom (rect k 1))))))).
  assert (Hr : rmoves (rect k 1) = [])
    by (apply rmoves_nil_of_col, col_rect).
  assert (Hin0 : In (0, 0) (rect k 1)) by (apply in_rect; simpl; lia).
  assert (Hin1 : In (1, 0) (rect k 1)) by (apply in_rect; simpl; lia).
  assert (Hm : In (remove2 (0, 0) (below (0, 0)) (rect k 1))
                 (lmoves (rect k 1))).
  { unfold lmoves; apply in_map_iff.
    exists (0, 0); split; [reflexivity|].
    apply filter_In; split; [exact Hin0|].
    unfold vfits; apply andb_true_iff; split; apply memb_true_iff; auto. }
  split.
  - apply gle_zero_l.
    rewrite lwin_false, ropts_Dom, Hr; reflexivity.
  - destruct (gle (Dom (rect k 1)) zero) eqn:E; auto.
    exfalso.
    apply gle_zero_r in E.
    rewrite lwin_true, lopts_Dom in E.
    assert (Hex : existsb (fun g => lwin g false) (map Dom (lmoves (rect k 1)))
                  = true).
    { apply existsb_exists.
      exists (Dom (remove2 (0, 0) (below (0, 0)) (rect k 1))); split.
      - apply in_map; exact Hm.
      - rewrite lwin_false, ropts_Dom.
        rewrite (rmoves_nil_of_col _ (col_lmoves (rect k 1) _ (col_rect k) Hm));
          reflexivity. }
    congruence.
Qed.

(** A board confined to one row offers Left nothing. *)
Lemma lmoves_nil_of_row :
  forall b, (forall c, In c b -> fst c = 0) -> lmoves b = [].
Proof.
  intros b Hc; unfold lmoves.
  rewrite (filter_nil_of_false (vfits b) b); [reflexivity|].
  intros x Hx.
  unfold vfits; apply andb_false_iff; right.
  apply memb_false_iff; intros Hin.
  pose proof (Hc x Hx) as Hx0.
  pose proof (Hc (below x) Hin) as Hb0.
  unfold below in Hb0; simpl in Hb0; congruence.
Qed.

Lemma row_rect : forall n c, In c (rect 1 n) -> fst c = 0.
Proof.
  intros n [r j] H; apply in_rect in H; simpl; lia.
Qed.

Lemma row_rmoves :
  forall b m,
    (forall c, In c b -> fst c = 0) -> In m (rmoves b) ->
    forall c, In c m -> fst c = 0.
Proof.
  intros b m Hb Hm c Hc.
  apply Hb, (rmoves_incl b m Hm); exact Hc.
Qed.

(** With Left immobile, Right wins a row of two or more outright. *)
Theorem Dom_row_Rwins :
  forall n, 2 <= n -> outc (Dom (rect 1 n)) = Rwins.
Proof.
  intros n Hn.
  apply (proj2 (proj2 (proj2 (proj2 (outc_spec (Dom (rect 1 n))))))).
  assert (Hl : lmoves (rect 1 n) = [])
    by (apply lmoves_nil_of_row, row_rect).
  assert (Hin0 : In (0, 0) (rect 1 n)) by (apply in_rect; simpl; lia).
  assert (Hin1 : In (0, 1) (rect 1 n)) by (apply in_rect; simpl; lia).
  assert (Hm : In (remove2 (0, 0) (rightof (0, 0)) (rect 1 n))
                 (rmoves (rect 1 n))).
  { unfold rmoves; apply in_map_iff.
    exists (0, 0); split; [reflexivity|].
    apply filter_In; split; [exact Hin0|].
    unfold hfits; apply andb_true_iff; split; apply memb_true_iff; auto. }
  split.
  - apply gle_zero_r.
    rewrite lwin_true, lopts_Dom, Hl; reflexivity.
  - destruct (gle zero (Dom (rect 1 n))) eqn:E; auto.
    exfalso.
    apply gle_zero_l in E.
    rewrite lwin_false, ropts_Dom in E.
    rewrite forallb_forall in E.
    assert (Hfalse : lwin (Dom (remove2 (0, 0) (rightof (0, 0)) (rect 1 n)))
                       true = false).
    { rewrite lwin_true, lopts_Dom.
      rewrite (lmoves_nil_of_row _ (row_rmoves (rect 1 n) _ (row_rect n) Hm));
        reflexivity. }
    pose proof (E (Dom (remove2 (0, 0) (rightof (0, 0)) (rect 1 n)))
                  (in_map Dom _ _ Hm)) as Htrue.
    congruence.
Qed.

(** * Squares *)

Lemma gle_zero_pneg : forall G, gle zero (pneg G) = gle G zero.
Proof.
  intros G; apply bool_iff_eq.
  rewrite gle_zero_l, gle_zero_r, lwin_pneg.
  change (negb false) with true.
  apply negb_true_iff.
Qed.

(** A square board is its own negative, so neither player wins it outright. *)
Theorem square_not_one_sided :
  forall n,
    outc (Dom (rect n n)) = Firstwins \/ outc (Dom (rect n n)) = Secondwins.
Proof.
  intros n.
  set (G := Dom (rect n n)) in *.
  pose proof (Dom_rect_transpose n n) as Heq.
  fold G in Heq.
  destruct (outc_spec G) as (_ & _ & Hlw & Hrw).
  case_eq (outc G); intros Eo; auto.
  - exfalso.
    destruct (proj1 Hlw Eo) as [Hz Hz'].
    assert (Hn : gle zero (pneg G) = true).
    { apply (gle_gequiv_r zero G); auto. }
    rewrite gle_zero_pneg in Hn; congruence.
  - exfalso.
    destruct (proj1 Hrw Eo) as [Hz Hz'].
    assert (Hn : gle (pneg G) zero = true).
    { apply (gle_gequiv_l G); auto. }
    assert (Hn' : gle zero (pneg (pneg G)) = true)
      by (rewrite gle_zero_pneg; exact Hn).
    rewrite pneg_pneg in Hn'; congruence.
Qed.

(** * Solved boards *)

Example dom_empty : Dom [] = zero.
Proof. reflexivity. Qed.

(** A single column is a free move for Left, a single row for Right. *)
Example dom_2x1 : gequiv (Dom (rect 2 1)) one = true.
Proof. vm_compute; reflexivity. Qed.

Example dom_1x2 : gequiv (Dom (rect 1 2)) minus_one = true.
Proof. vm_compute; reflexivity. Qed.

(** A column of three is worth one move, a column of four two. *)
Example dom_3x1 : gequiv (Dom (rect 3 1)) one = true.
Proof. vm_compute; reflexivity. Qed.

Example dom_4x1 : gequiv (Dom (rect 4 1)) (num 2) = true.
Proof. vm_compute; reflexivity. Qed.

(** The square of side two is exactly the switch between one move each way. *)
Example dom_2x2_value : gequiv (Dom (rect 2 2)) (PG [one] [minus_one]) = true.
Proof. vm_compute; reflexivity. Qed.

Example dom_2x2_fuzzy : gfuzzy (Dom (rect 2 2)) zero = true.
Proof. vm_compute; reflexivity. Qed.

Example dom_2x3 : outc (Dom (rect 2 3)) = Firstwins.
Proof. vm_compute; reflexivity. Qed.

Example dom_3x3 : outc (Dom (rect 3 3)) = Firstwins.
Proof. vm_compute; reflexivity. Qed.

(** Two columns far enough apart are worth two free moves for Left. *)
Example dom_two_columns :
  gequiv (Dom [(0, 0); (1, 0); (0, 5); (1, 5)]) (num 2) = true.
Proof. vm_compute; reflexivity. Qed.
