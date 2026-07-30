(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Nim multiplication on the nimbers. Addition is the exclusive or that
    [GameTrees.Grundy] gives disjunctive sums; multiplication is the mex of the
    products a move leaves behind, and the two make the nimbers a field. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.
From Stdlib Require Import Btauto.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.Trees.
Require Import GameTrees.Grundy.

(** * Nim addition *)

(** The exclusive or, written as the sum it is. *)
Definition nadd (a b : nat) : nat := Nat.lxor a b.

(** Any identity of exclusive ors is a boolean tautology bit by bit. *)
Ltac xor_eq :=
  apply Nat.bits_inj; intros ?n; unfold nadd; rewrite !Nat.lxor_spec; btauto.

Lemma nadd_comm : forall a b, nadd a b = nadd b a.
Proof. intros a b; apply Nat.lxor_comm. Qed.

Lemma nadd_assoc : forall a b c, nadd (nadd a b) c = nadd a (nadd b c).
Proof. intros a b c; apply Nat.lxor_assoc. Qed.

Lemma nadd_0_l : forall a, nadd 0 a = a.
Proof. intros a; apply Nat.lxor_0_l. Qed.

Lemma nadd_0_r : forall a, nadd a 0 = a.
Proof. intros a; apply Nat.lxor_0_r. Qed.

Lemma nadd_self : forall a, nadd a a = 0.
Proof. intros a; apply Nat.lxor_nilpotent. Qed.

Lemma nadd_cancel_l : forall a b c, nadd a b = nadd a c -> b = c.
Proof.
  intros a b c H.
  rewrite <- (nadd_0_l b), <- (nadd_self a), nadd_assoc, H.
  rewrite <- nadd_assoc, nadd_self, nadd_0_l; reflexivity.
Qed.

Lemma nadd_eq_0 : forall a b, nadd a b = 0 <-> a = b.
Proof.
  intros a b; unfold nadd; apply lxor_eq_0.
Qed.

(** * Nim multiplication *)

(** The options of a product: each pair of earlier factors contributes the
    value that keeps the product from being reached. *)
Definition prodopt (f : nat -> nat -> nat) (a b : nat) (p : nat * nat) : nat :=
  nadd (nadd (f (fst p) b) (f a (snd p))) (f (fst p) (snd p)).

Definition pairs (a b : nat) : list (nat * nat) :=
  list_prod (seq 0 a) (seq 0 b).

Lemma in_pairs :
  forall a b p, In p (pairs a b) <-> fst p < a /\ snd p < b.
Proof.
  intros a b [x y]; unfold pairs; rewrite in_prod_iff, !in_seq; cbn [fst snd].
  split; intros [H1 H2]; split; lia.
Qed.

Fixpoint nmulf (fuel a b : nat) : nat :=
  match fuel with
  | O => 0
  | S f => mex (map (prodopt (nmulf f) a b) (pairs a b))
  end.

Lemma nmulf_stable :
  forall N a b f1 f2,
    a + b <= N -> a + b <= f1 -> a + b <= f2 ->
    nmulf f1 a b = nmulf f2 a b.
Proof.
  induction N as [|N IH]; intros a b f1 f2 HN Hf1 Hf2.
  - assert (Ha : a = 0) by lia; assert (Hb : b = 0) by lia; subst.
    destruct f1; destruct f2; reflexivity.
  - destruct f1 as [|f1].
    + assert (Ha : a = 0) by lia; assert (Hb : b = 0) by lia; subst.
      destruct f2; reflexivity.
    + destruct f2 as [|f2].
      * assert (Ha : a = 0) by lia; assert (Hb : b = 0) by lia; subst; reflexivity.
      * cbn [nmulf]; f_equal; apply map_ext_in; intros p Hp.
        apply in_pairs in Hp; destruct Hp as [H1 H2].
        unfold prodopt; f_equal; [f_equal|].
        -- apply (IH (fst p) b); lia.
        -- apply (IH a (snd p)); lia.
        -- apply (IH (fst p) (snd p)); lia.
Qed.

(** The product, with just enough fuel. *)
Definition nmul (a b : nat) : nat := nmulf (a + b) a b.

Lemma nmulf_nmul : forall f a b, a + b <= f -> nmulf f a b = nmul a b.
Proof.
  intros f a b Hf; unfold nmul; apply (nmulf_stable (a + b)); lia.
Qed.

(** The defining equation: a product is the mex of what the moves leave. *)
Lemma nmul_eq :
  forall a b, nmul a b = mex (map (prodopt nmul a b) (pairs a b)).
Proof.
  intros a b; unfold nmul at 1.
  destruct (a + b) as [|f] eqn:Es.
  - assert (Ha : a = 0) by lia; subst a; cbn [nmulf pairs].
    unfold pairs; cbn [seq list_prod map]; reflexivity.
  - cbn [nmulf]; f_equal; apply map_ext_in; intros p Hp.
    apply in_pairs in Hp; destruct Hp as [H1 H2].
    unfold prodopt; f_equal; [f_equal|].
    + apply nmulf_nmul; lia.
    + apply nmulf_nmul; lia.
    + apply nmulf_nmul; lia.
Qed.

(** The two halves of the mex: a product avoids every option, and everything
    below it is an option. *)
Lemma nmul_not_option :
  forall a b a' b',
    a' < a -> b' < b ->
    nadd (nadd (nmul a' b) (nmul a b')) (nmul a' b') <> nmul a b.
Proof.
  intros a b a' b' Ha Hb H.
  apply (mex_not_in (map (prodopt nmul a b) (pairs a b))).
  rewrite <- nmul_eq, <- H.
  apply in_map_iff; exists (a', b'); split; [reflexivity|].
  apply in_pairs; cbn [fst snd]; auto.
Qed.

Lemma nmul_below_option :
  forall a b x,
    x < nmul a b ->
    exists a' b', a' < a /\ b' < b /\
                  nadd (nadd (nmul a' b) (nmul a b')) (nmul a' b') = x.
Proof.
  intros a b x Hx.
  assert (Hin : In x (map (prodopt nmul a b) (pairs a b))).
  { apply mex_lt_in; rewrite <- nmul_eq; exact Hx. }
  apply in_map_iff in Hin; destruct Hin as [p [Hp Hpin]].
  apply in_pairs in Hpin; destruct Hpin as [H1 H2].
  exists (fst p), (snd p); repeat split; auto.
Qed.

Lemma mex_ext :
  forall l l', (forall x, In x l <-> In x l') -> mex l = mex l'.
Proof.
  intros l l' H; apply mex_unique.
  - intros Hin; apply (mex_not_in l'); apply H in Hin; exact Hin.
  - intros x Hx; apply H; apply mex_lt_in; exact Hx.
Qed.

(** * The ring laws *)

Lemma nmul_0_l : forall b, nmul 0 b = 0.
Proof.
  intros b; rewrite nmul_eq; unfold pairs; cbn [seq list_prod map]; reflexivity.
Qed.

Lemma pairs_0_r : forall a, pairs a 0 = [].
Proof.
  intros a; unfold pairs; cbn [seq].
  induction (seq 0 a) as [|x l IH]; cbn [list_prod map app]; auto.
Qed.

Lemma nmul_0_r : forall a, nmul a 0 = 0.
Proof.
  intros a; rewrite nmul_eq, pairs_0_r; reflexivity.
Qed.

(** Products are read the same way round. *)
Theorem nmul_comm : forall a b, nmul a b = nmul b a.
Proof.
  assert (Haux : forall N a b, a + b <= N -> nmul a b = nmul b a).
  { induction N as [|N IH]; intros a b HN.
    - assert (a = 0) as -> by lia; assert (b = 0) as -> by lia; reflexivity.
    - rewrite (nmul_eq a b), (nmul_eq b a).
      apply mex_ext; intros x; split.
      + intros Hx; apply in_map_iff in Hx.
        destruct Hx as [p [<- Hp]]; apply in_pairs in Hp; destruct Hp as [H1 H2].
        apply in_map_iff; exists (snd p, fst p); split.
        * unfold prodopt; cbn [fst snd].
          rewrite (IH (fst p) b), (IH a (snd p)), (IH (fst p) (snd p)) by lia.
          f_equal; apply nadd_comm.
        * apply in_pairs; cbn [fst snd]; auto.
      + intros Hx; apply in_map_iff in Hx.
        destruct Hx as [p [<- Hp]]; apply in_pairs in Hp; destruct Hp as [H1 H2].
        apply in_map_iff; exists (snd p, fst p); split.
        * unfold prodopt; cbn [fst snd].
          rewrite (IH (fst p) a), (IH b (snd p)), (IH (fst p) (snd p)) by lia.
          f_equal; apply nadd_comm.
        * apply in_pairs; cbn [fst snd]; auto. }
  intros a b; apply (Haux (a + b)); lia.
Qed.

(** One is the unit. *)
Theorem nmul_1_l : forall b, nmul 1 b = b.
Proof.
  assert (Haux : forall N b, b <= N -> nmul 1 b = b).
  { induction N as [|N IH]; intros b HN.
    - assert (b = 0) as -> by lia; apply nmul_0_r.
    - rewrite nmul_eq.
      apply mex_unique.
      + intros H; apply in_map_iff in H.
        destruct H as [p [Hv Hp]]; apply in_pairs in Hp; destruct Hp as [H1 H2].
        assert (Hfst : fst p = 0) by lia.
        unfold prodopt in Hv; rewrite Hfst, nmul_0_l, nmul_0_l, nadd_0_l in Hv.
        rewrite (IH (snd p)) in Hv by lia.
        rewrite nadd_0_r in Hv; lia.
      + intros x Hx; apply in_map_iff; exists (0, x); split.
        * unfold prodopt; cbn [fst snd].
          rewrite !nmul_0_l, nadd_0_l, nadd_0_r.
          apply IH; lia.
        * apply in_pairs; cbn [fst snd]; lia. }
  intros b; apply (Haux b); lia.
Qed.

Theorem nmul_1_r : forall a, nmul a 1 = a.
Proof. intros a; rewrite nmul_comm; apply nmul_1_l. Qed.

(** A product of nonzero nimbers is nonzero: the zero option is always
    available, so the mex steps over it. *)
Theorem nmul_neq_0 :
  forall a b, a <> 0 -> b <> 0 -> nmul a b <> 0.
Proof.
  intros a b Ha Hb H.
  assert (Hin : In 0 (map (prodopt nmul a b) (pairs a b))).
  { apply in_map_iff; exists (0, 0); split.
    - unfold prodopt; cbn [fst snd].
      rewrite !nmul_0_l, !nmul_0_r, !nadd_0_l; reflexivity.
    - apply in_pairs; cbn [fst snd]; lia. }
  apply (mex_not_in (map (prodopt nmul a b) (pairs a b))).
  rewrite <- (nmul_eq a b), H; exact Hin.
Qed.

(** * The four-element nimber field *)

(** The nimbers below four, with the exclusive or and the nim product, are the
    field of four elements: the smallest of Conway's Fermat fields. *)

Example nmul_2_2 : nmul 2 2 = 3.
Proof. vm_compute; reflexivity. Qed.

Example nmul_2_3 : nmul 2 3 = 1.
Proof. vm_compute; reflexivity. Qed.

Example nmul_3_3 : nmul 3 3 = 2.
Proof. vm_compute; reflexivity. Qed.

Definition below (n : nat) (f : nat -> bool) : bool := forallb f (seq 0 n).

Lemma below_spec :
  forall n f, below n f = true <-> forall x, x < n -> f x = true.
Proof.
  intros n f; unfold below; rewrite forallb_forall; split.
  - intros H x Hx; apply H, in_seq; lia.
  - intros H x Hx; apply in_seq in Hx; apply H; lia.
Qed.

(** Closure: a product of nimbers below four stays below four. *)
Theorem nmul_closed_4 :
  forall a b, a < 4 -> b < 4 -> nmul a b < 4.
Proof.
  assert (H : below 4 (fun a => below 4 (fun b => Nat.ltb (nmul a b) 4)) = true)
    by (vm_compute; reflexivity).
  intros a b Ha Hb.
  apply below_spec with (x := a) in H; auto.
  apply below_spec with (x := b) in H; auto.
  apply Nat.ltb_lt; exact H.
Qed.

(** Multiplication distributes over addition there. *)
Theorem nmul_distr_4 :
  forall a b c, a < 4 -> b < 4 -> c < 4 ->
    nmul a (nadd b c) = nadd (nmul a b) (nmul a c).
Proof.
  assert (H : below 4 (fun a => below 4 (fun b => below 4 (fun c =>
                Nat.eqb (nmul a (nadd b c)) (nadd (nmul a b) (nmul a c))))) = true)
    by (vm_compute; reflexivity).
  intros a b c Ha Hb Hc.
  apply below_spec with (x := a) in H; auto.
  apply below_spec with (x := b) in H; auto.
  apply below_spec with (x := c) in H; auto.
  apply Nat.eqb_eq; exact H.
Qed.

(** And it is associative there. *)
Theorem nmul_assoc_4 :
  forall a b c, a < 4 -> b < 4 -> c < 4 ->
    nmul (nmul a b) c = nmul a (nmul b c).
Proof.
  assert (H : below 4 (fun a => below 4 (fun b => below 4 (fun c =>
                Nat.eqb (nmul (nmul a b) c) (nmul a (nmul b c)))))= true)
    by (vm_compute; reflexivity).
  intros a b c Ha Hb Hc.
  apply below_spec with (x := a) in H; auto.
  apply below_spec with (x := b) in H; auto.
  apply below_spec with (x := c) in H; auto.
  apply Nat.eqb_eq; exact H.
Qed.

(** Every nonzero nimber below four has an inverse below four. *)
Theorem nmul_inverse_4 :
  forall a, 0 < a < 4 -> exists b, b < 4 /\ nmul a b = 1.
Proof.
  intros a Ha.
  destruct a as [|[|[|[|a]]]]; try lia.
  - exists 1; split; [lia | apply nmul_1_r].
  - exists 3; split; [lia | apply nmul_2_3].
  - exists 2; split; [lia|].
    rewrite nmul_comm; apply nmul_2_3.
Qed.

(** * The multiplication table *)

(** The recursion recomputes its subproducts, so products past the smallest
    ones are read off a table built once, row by row. *)

Definition tg (rows : list (list nat)) (a b : nat) : nat :=
  nth b (nth a rows []) 0.

(** Row [a] of the table, as far as column [k], from the completed rows. *)
Fixpoint mrow (prev : list (list nat)) (a k : nat) : list nat :=
  match k with
  | O => []
  | S k' =>
      let r := mrow prev a k' in
      r ++ [mex (map (fun p => nadd (nadd (tg prev (fst p) k') (nth (snd p) r 0))
                                    (tg prev (fst p) (snd p)))
                     (pairs a k'))]
  end.

Fixpoint mtab (n a : nat) : list (list nat) :=
  match a with
  | O => []
  | S a' => let prev := mtab n a' in prev ++ [mrow prev a' n]
  end.

Definition ntimes (n a b : nat) : nat := tg (mtab n n) a b.

Lemma mrow_length : forall prev a k, length (mrow prev a k) = k.
Proof.
  intros prev a k; induction k as [|k IH]; cbn [mrow]; auto.
  rewrite length_app, IH; cbn [length]; lia.
Qed.

Lemma mtab_length : forall n a, length (mtab n a) = a.
Proof.
  intros n a; induction a as [|a IH]; cbn [mtab]; auto.
  rewrite length_app, IH; cbn [length]; lia.
Qed.

Lemma mtab_nth :
  forall n a a', a' < a -> nth a' (mtab n a) [] = mrow (mtab n a') a' n.
Proof.
  intros n a; induction a as [|a IH]; intros a' Ha; [lia|].
  cbn [mtab].
  destruct (Nat.eq_dec a' a) as [-> | Hne].
  - rewrite app_nth2; rewrite mtab_length; [|lia].
    rewrite Nat.sub_diag; reflexivity.
  - rewrite app_nth1 by (rewrite mtab_length; lia).
    apply IH; lia.
Qed.

Lemma mrow_nth :
  forall prev a k b,
    b < k ->
    nth b (mrow prev a k) 0 =
    mex (map (fun p => nadd (nadd (tg prev (fst p) b)
                                  (nth (snd p) (mrow prev a b) 0))
                            (tg prev (fst p) (snd p)))
             (pairs a b)).
Proof.
  intros prev a k; induction k as [|k IH]; intros b Hb; [lia|].
  cbn [mrow].
  destruct (Nat.eq_dec b k) as [-> | Hne].
  - rewrite app_nth2; rewrite mrow_length; [|lia].
    rewrite Nat.sub_diag; reflexivity.
  - rewrite app_nth1 by (rewrite mrow_length; lia).
    apply IH; lia.
Qed.

(** Reading an entry does not depend on how far the table has been built. *)
Lemma mtab_prefix :
  forall n a a' b, a' < a -> a <= n -> tg (mtab n a) a' b = tg (mtab n n) a' b.
Proof.
  intros n a a' b Ha Han; unfold tg.
  rewrite (mtab_nth n a a') by lia.
  rewrite (mtab_nth n n a') by lia; reflexivity.
Qed.

Lemma mrow_prefix :
  forall prev a k k' b,
    b < k' -> k' <= k ->
    nth b (mrow prev a k') 0 = nth b (mrow prev a k) 0.
Proof.
  intros prev a k k' b Hb Hk.
  rewrite (mrow_nth prev a k' b) by lia.
  rewrite (mrow_nth prev a k b) by lia; reflexivity.
Qed.

(** The table holds the products. *)
Theorem ntimes_nmul :
  forall n a b, a < n -> b < n -> ntimes n a b = nmul a b.
Proof.
  assert (Haux : forall N n a b,
             a + b <= N -> a < n -> b < n -> tg (mtab n n) a b = nmul a b).
  { induction N as [|N IH]; intros n a b HN Ha Hb.
    - assert (Ha0 : a = 0) by lia; assert (Hb0 : b = 0) by lia; subst.
      unfold tg; rewrite (mtab_nth n n 0) by lia.
      rewrite nmul_0_l.
      rewrite (mrow_nth (mtab n 0) 0 n 0) by lia.
      unfold pairs; cbn [seq list_prod map]; reflexivity.
    - unfold tg; rewrite (mtab_nth n n a) by lia.
      rewrite (mrow_nth (mtab n a) a n b) by lia.
      rewrite nmul_eq.
      f_equal; apply map_ext_in; intros p Hp.
      apply in_pairs in Hp; destruct Hp as [H1 H2].
      unfold prodopt; f_equal; [f_equal|].
      + rewrite (mtab_prefix n a (fst p) b) by lia.
        apply IH; lia.
      + rewrite (mrow_prefix (mtab n a) a n b (snd p)) by lia.
        rewrite <- (mtab_nth n n a) by lia.
        change (nth (snd p) (nth a (mtab n n) []) 0) with (tg (mtab n n) a (snd p)).
        apply IH; lia.
      + rewrite (mtab_prefix n a (fst p) (snd p)) by lia.
        apply IH; lia. }
  intros n a b Ha Hb; unfold ntimes; apply (Haux (a + b) n); lia.
Qed.

(** * The sixteen-element nimber field *)

Lemma log2_lt_pow2_0 : forall n, 0 < n -> Nat.log2 0 < n.
Proof. intros n Hn; cbn; lia. Qed.

Lemma nadd_lt_pow2 :
  forall n a b, a < 2 ^ n -> b < 2 ^ n -> nadd a b < 2 ^ n.
Proof.
  intros n a b Ha Hb; unfold nadd.
  assert (Hn : 0 < n \/ n = 0) by lia.
  destruct Hn as [Hn | ->].
  2: { cbn in *; assert (a = 0) as -> by lia; assert (b = 0) as -> by lia; cbn; lia. }
  destruct (Nat.eq_dec (Nat.lxor a b) 0) as [-> | Hne].
  - apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia.
  - apply Nat.log2_lt_pow2; [lia|].
    apply Nat.le_lt_trans with (m := Nat.max (Nat.log2 a) (Nat.log2 b)).
    + apply Nat.log2_lxor.
    + apply Nat.max_lub_lt.
      * destruct (Nat.eq_dec a 0) as [-> | Ha0];
          [apply log2_lt_pow2_0; lia | apply Nat.log2_lt_pow2; lia].
      * destruct (Nat.eq_dec b 0) as [-> | Hb0];
          [apply log2_lt_pow2_0; lia | apply Nat.log2_lt_pow2; lia].
Qed.

Lemma nadd_lt_16 : forall a b, a < 16 -> b < 16 -> nadd a b < 16.
Proof.
  intros a b Ha Hb.
  change 16 with (2 ^ 4) in *; apply nadd_lt_pow2; assumption.
Qed.

(** Products of nimbers below sixteen stay below sixteen. *)
Theorem nmul_closed_16 :
  forall a b, a < 16 -> b < 16 -> nmul a b < 16.
Proof.
  assert (H : (let t := mtab 16 16 in
               below 16 (fun a => below 16 (fun b => Nat.ltb (tg t a b) 16)))
              = true) by (vm_compute; reflexivity).
  cbv zeta in H.
  intros a b Ha Hb.
  apply below_spec with (x := a) in H; auto.
  apply below_spec with (x := b) in H; auto.
  apply Nat.ltb_lt in H.
  rewrite <- (ntimes_nmul 16 a b Ha Hb); unfold ntimes; exact H.
Qed.

(** Multiplication distributes over addition there. *)
Theorem nmul_distr_16 :
  forall a b c, a < 16 -> b < 16 -> c < 16 ->
    nmul a (nadd b c) = nadd (nmul a b) (nmul a c).
Proof.
  assert (H : (let t := mtab 16 16 in
               below 16 (fun a => below 16 (fun b => below 16 (fun c =>
                 Nat.eqb (tg t a (nadd b c)) (nadd (tg t a b) (tg t a c))))))
              = true) by (vm_compute; reflexivity).
  cbv zeta in H.
  intros a b c Ha Hb Hc.
  apply below_spec with (x := a) in H; auto.
  apply below_spec with (x := b) in H; auto.
  apply below_spec with (x := c) in H; auto.
  apply Nat.eqb_eq in H.
  rewrite <- (ntimes_nmul 16 a (nadd b c) Ha (nadd_lt_16 b c Hb Hc)).
  rewrite <- (ntimes_nmul 16 a b Ha Hb), <- (ntimes_nmul 16 a c Ha Hc).
  unfold ntimes; exact H.
Qed.

(** And it is associative there. *)
Theorem nmul_assoc_16 :
  forall a b c, a < 16 -> b < 16 -> c < 16 ->
    nmul (nmul a b) c = nmul a (nmul b c).
Proof.
  assert (H : (let t := mtab 16 16 in
               below 16 (fun a => below 16 (fun b => below 16 (fun c =>
                 Nat.eqb (tg t (tg t a b) c) (tg t a (tg t b c))))))
              = true) by (vm_compute; reflexivity).
  cbv zeta in H.
  intros a b c Ha Hb Hc.
  apply below_spec with (x := a) in H; auto.
  apply below_spec with (x := b) in H; auto.
  apply below_spec with (x := c) in H; auto.
  apply Nat.eqb_eq in H.
  rewrite <- (ntimes_nmul 16 (nmul a b) c (nmul_closed_16 a b Ha Hb) Hc).
  rewrite <- (ntimes_nmul 16 a (nmul b c) Ha (nmul_closed_16 b c Hb Hc)).
  rewrite <- (ntimes_nmul 16 a b Ha Hb), <- (ntimes_nmul 16 b c Hb Hc).
  unfold ntimes; exact H.
Qed.

(** Every nonzero nimber below sixteen has an inverse below sixteen. *)
Theorem nmul_inverse_16 :
  forall a, 0 < a < 16 -> exists b, b < 16 /\ nmul a b = 1.
Proof.
  assert (H : (let t := mtab 16 16 in
               below 16 (fun a => orb (Nat.eqb a 0)
                 (existsb (fun b => Nat.eqb (tg t a b) 1) (seq 0 16))))
              = true) by (vm_compute; reflexivity).
  cbv zeta in H.
  intros a Ha.
  apply below_spec with (x := a) in H; [|lia].
  apply orb_true_iff in H; destruct H as [H | H].
  - apply Nat.eqb_eq in H; lia.
  - apply existsb_exists in H; destruct H as [b [Hb Hv]].
    apply in_seq in Hb; apply Nat.eqb_eq in Hv.
    exists b; split; [lia|].
    rewrite <- (ntimes_nmul 16 a b ltac:(lia) ltac:(lia)); unfold ntimes; exact Hv.
Qed.

(** * Distributivity *)

Lemma mex_incl :
  forall l l', (forall x, In x l -> In x l') -> mex l <= mex l'.
Proof.
  intros l l' H.
  destruct (Nat.le_gt_cases (mex l) (mex l')) as [Hle | Hgt]; [exact Hle|].
  exfalso; apply (mex_not_in l').
  apply H, mex_lt_in; exact Hgt.
Qed.

(** The options of a sum: move in one side and leave the other. *)
Definition sumopts (P Q : list nat) (p q : nat) : list nat :=
  map (fun o => nadd o q) P ++ map (fun o => nadd p o) Q.

(** Their mex is the exclusive or, which is Bouton's theorem read on option
    lists rather than on heaps. *)
Lemma mex_sumopts :
  forall P Q p q,
    mex P = p -> mex Q = q -> mex (sumopts P Q p q) = nadd p q.
Proof.
  intros P Q p q Hp Hq; apply mex_unique.
  - intros H; unfold sumopts in H; apply in_app_iff in H.
    destruct H as [H | H]; apply in_map_iff in H; destruct H as [o [Ho Hin]].
    + apply (mex_not_in P); rewrite Hp.
      replace p with o; [exact Hin|].
      apply (lxor_cancel_r q); exact Ho.
    + apply (mex_not_in Q); rewrite Hq.
      replace q with o; [exact Hin|].
      apply (lxor_cancel_l p); exact Ho.
  - intros w Hw; unfold sumopts; apply in_app_iff.
    destruct (lxor_lt_witness p q w Hw) as [H | H].
    + left; apply in_map_iff; exists (Nat.lxor q w); split.
      * unfold nadd; rewrite Nat.lxor_comm, lxor_cancel_left; reflexivity.
      * rewrite <- Hp in H; apply mex_lt_in; exact H.
    + right; apply in_map_iff; exists (Nat.lxor p w); split.
      * unfold nadd; rewrite lxor_cancel_left; reflexivity.
      * rewrite <- Hq in H; apply mex_lt_in; exact H.
Qed.

(** The measure that carries the induction: it does not notice which two of
    [b], [c] and [b + c] are named, so the three inequalities the triangle
    argument needs all sit at the same level. *)
Definition dmeasure (a b c : nat) : nat := a + b + c + nadd b c.

Lemma dmeasure_rot1 : forall a b c, dmeasure a (nadd b c) c = dmeasure a b c.
Proof.
  intros a b c; unfold dmeasure.
  replace (nadd (nadd b c) c) with b by xor_eq; lia.
Qed.

Lemma dmeasure_rot2 : forall a b c, dmeasure a b (nadd b c) = dmeasure a b c.
Proof.
  intros a b c; unfold dmeasure.
  replace (nadd b (nadd b c)) with c by xor_eq; lia.
Qed.

(** One inequality, from every option of the product on the left being an
    option of the sum of products on the right. *)
Lemma distr_le_step :
  forall m a b c,
    (forall a1 b1 c1,
        dmeasure a1 b1 c1 < m ->
        nmul a1 (nadd b1 c1) = nadd (nmul a1 b1) (nmul a1 c1)) ->
    dmeasure a b c <= m ->
    nmul a (nadd b c) <= nadd (nmul a b) (nmul a c).
Proof.
  intros m a b c IH Hm.
  rewrite (nmul_eq a (nadd b c)).
  rewrite <- (mex_sumopts (map (prodopt nmul a b) (pairs a b))
                          (map (prodopt nmul a c) (pairs a c))
                          (nmul a b) (nmul a c))
    by (symmetry; apply nmul_eq).
  apply mex_incl.
  intros x Hx; apply in_map_iff in Hx.
  destruct Hx as [p [<- Hp]]; apply in_pairs in Hp; destruct Hp as [H1 H2].
  unfold sumopts; apply in_app_iff.
  destruct (lxor_lt_witness b c (snd p) H2) as [Hw | Hw].
  - left; apply in_map_iff.
    remember (Nat.lxor c (snd p)) as b' eqn:Eb'.
    assert (Hd : nadd b' c = snd p) by (rewrite Eb'; xor_eq).
    exists (prodopt nmul a b (fst p, b')); split.
    + unfold prodopt; cbn [fst snd].
      rewrite <- Hd.
      rewrite (IH (fst p) b c) by (unfold dmeasure in *; lia).
      rewrite (IH a b' c) by (unfold dmeasure in *; rewrite Hd; lia).
      rewrite (IH (fst p) b' c) by (unfold dmeasure in *; rewrite Hd; lia).
      xor_eq.
    + apply in_map_iff; exists (fst p, b'); split; [reflexivity|].
      apply (proj2 (in_pairs a b (fst p, b'))); cbn [fst snd].
      split; [exact H1 | exact Hw].
  - right; apply in_map_iff.
    remember (Nat.lxor b (snd p)) as c' eqn:Ec'.
    assert (Hd : nadd b c' = snd p) by (rewrite Ec'; xor_eq).
    exists (prodopt nmul a c (fst p, c')); split.
    + unfold prodopt; cbn [fst snd].
      rewrite <- Hd.
      rewrite (IH (fst p) b c) by (unfold dmeasure in *; lia).
      rewrite (IH a b c') by (unfold dmeasure in *; rewrite Hd; lia).
      rewrite (IH (fst p) b c') by (unfold dmeasure in *; rewrite Hd; lia).
      xor_eq.
    + apply in_map_iff; exists (fst p, c'); split; [reflexivity|].
      apply (proj2 (in_pairs a c (fst p, c'))); cbn [fst snd].
      split; [exact H1 | exact Hw].
Qed.

(** Three exclusive-or inequalities leave no room: if each of the three values
    is at most the sum of the other two, they sum to zero. *)
Lemma xor_triangle :
  forall u p q,
    u <= nadd p q -> p <= nadd u q -> q <= nadd u p -> u = nadd p q.
Proof.
  intros u p q H1 H2 H3.
  set (w := nadd u (nadd p q)).
  destruct (Nat.eq_dec w 0) as [Hw0 | Hw].
  - unfold w in Hw0; apply (proj1 (nadd_eq_0 u (nadd p q))); exact Hw0.
  - exfalso.
    set (k := Nat.log2 w).
    assert (Hbits : forall x y, nadd x y = w ->
               (forall j, k < j -> Nat.testbit x j = Nat.testbit y j)).
    { intros x y Hxy j Hj.
      assert (Hz : Nat.testbit w j = false)
        by (apply Nat.bits_above_log2; exact Hj).
      rewrite <- Hxy in Hz; unfold nadd in Hz; rewrite Nat.lxor_spec in Hz.
      destruct (Nat.testbit x j); destruct (Nat.testbit y j);
        simpl in Hz; congruence. }
    assert (Hk : Nat.testbit w k = true) by (apply Nat.bit_log2; exact Hw).
    assert (Hsum : xorb (Nat.testbit u k)
                     (xorb (Nat.testbit p k) (Nat.testbit q k)) = true).
    { unfold w in Hk; unfold nadd in Hk; rewrite !Nat.lxor_spec in Hk; exact Hk. }
    assert (Hupq : nadd u (nadd p q) = w) by reflexivity.
    assert (Hpuq : nadd p (nadd u q) = w) by (unfold w; xor_eq).
    assert (Hqup : nadd q (nadd u p) = w) by (unfold w; xor_eq).
    destruct (Nat.testbit u k) eqn:Eu; simpl in Hsum.
    + assert (Hpq : xorb (Nat.testbit p k) (Nat.testbit q k) = false)
        by (destruct (Nat.testbit p k); destruct (Nat.testbit q k);
            simpl in Hsum |- *; congruence).
      assert (Hlt : nadd p q < u).
      { apply (testbit_order (nadd p q) u k).
        - unfold nadd; rewrite Nat.lxor_spec; exact Hpq.
        - exact Eu.
        - intros j Hj; symmetry; apply (Hbits u (nadd p q) Hupq j Hj). }
      lia.
    + destruct (Nat.testbit p k) eqn:Ep; simpl in Hsum.
      * assert (Hq : Nat.testbit q k = false)
          by (destruct (Nat.testbit q k); simpl in Hsum; congruence).
        assert (Hlt : nadd u q < p).
        { apply (testbit_order (nadd u q) p k).
          - unfold nadd; rewrite Nat.lxor_spec, Eu, Hq; reflexivity.
          - exact Ep.
          - intros j Hj; symmetry; apply (Hbits p (nadd u q) Hpuq j Hj). }
        lia.
      * assert (Hq : Nat.testbit q k = true)
          by (destruct (Nat.testbit q k); simpl in Hsum; congruence).
        assert (Hlt : nadd u p < q).
        { apply (testbit_order (nadd u p) q k).
          - unfold nadd; rewrite Nat.lxor_spec, Eu, Ep; reflexivity.
          - exact Hq.
          - intros j Hj; symmetry; apply (Hbits q (nadd u p) Hqup j Hj). }
        lia.
Qed.

(** Nim multiplication distributes over nim addition. *)
Theorem nmul_distr :
  forall a b c, nmul a (nadd b c) = nadd (nmul a b) (nmul a c).
Proof.
  assert (Haux : forall m a b c,
             dmeasure a b c <= m ->
             nmul a (nadd b c) = nadd (nmul a b) (nmul a c)).
  { induction m as [|m IH]; intros a b c Hm.
    { assert (Ha : a = 0) by (unfold dmeasure in Hm; lia).
      assert (Hb : b = 0) by (unfold dmeasure in Hm; lia).
      assert (Hc : c = 0) by (unfold dmeasure in Hm; lia).
      subst; rewrite !nmul_0_l; reflexivity. }
    assert (IH' : forall a1 b1 c1,
               dmeasure a1 b1 c1 < S m ->
               nmul a1 (nadd b1 c1) = nadd (nmul a1 b1) (nmul a1 c1)).
    { intros a1 b1 c1 H1; apply IH; lia. }
    apply xor_triangle.
    - apply (distr_le_step (S m) a b c IH' Hm).
    - pose proof (distr_le_step (S m) a (nadd b c) c IH'
                    ltac:(rewrite dmeasure_rot1; exact Hm)) as Hle.
      replace (nadd (nadd b c) c) with b in Hle by xor_eq; exact Hle.
    - pose proof (distr_le_step (S m) a b (nadd b c) IH'
                    ltac:(rewrite dmeasure_rot2; exact Hm)) as Hle.
      replace (nadd b (nadd b c)) with c in Hle by xor_eq.
      rewrite nadd_comm; exact Hle. }
  intros a b c; apply (Haux (dmeasure a b c)); lia.
Qed.

Theorem nmul_distr_r :
  forall a b c, nmul (nadd a b) c = nadd (nmul a c) (nmul b c).
Proof.
  intros a b c; rewrite nmul_comm, nmul_distr, (nmul_comm c a), (nmul_comm c b).
  reflexivity.
Qed.

(** * Cancellation *)

(** With distributivity in hand the product map is injective away from zero,
    which is the cancellation the mex arguments below need. *)
Theorem nmul_cancel :
  forall a b c, a <> 0 -> nmul a b = nmul a c -> b = c.
Proof.
  intros a b c Ha H.
  destruct (Nat.eq_dec b c) as [Hbc | Hbc]; [exact Hbc|].
  exfalso.
  assert (Hd : nadd b c <> 0)
    by (intros H0; apply Hbc; apply (proj1 (nadd_eq_0 b c)); exact H0).
  apply (nmul_neq_0 a (nadd b c) Ha Hd).
  rewrite nmul_distr, H; apply nadd_self.
Qed.

(** The option of a product, in the form distributivity gives it. *)
Lemma prodopt_diff :
  forall a b a' b',
    nadd (nadd (nadd (nmul a' b) (nmul a b')) (nmul a' b')) (nmul a b) =
    nmul (nadd a a') (nadd b b').
Proof.
  intros a b a' b'.
  rewrite nmul_distr_r, !nmul_distr.
  xor_eq.
Qed.

(** A product is not an option of itself, read as the statement that the
    difference of two factors multiplies to something nonzero. *)
Lemma nmul_option_ne :
  forall a b a' b',
    a' <> a -> b' <> b ->
    nadd (nadd (nmul a' b) (nmul a b')) (nmul a' b') <> nmul a b.
Proof.
  intros a b a' b' Ha Hb H.
  apply (nmul_neq_0 (nadd a a') (nadd b b')).
  - intros H0; apply Ha; symmetry; apply (proj1 (nadd_eq_0 a a')); exact H0.
  - intros H0; apply Hb; symmetry; apply (proj1 (nadd_eq_0 b b')); exact H0.
  - rewrite <- prodopt_diff, H; apply nadd_self.
Qed.

(** * The mex may be taken over any covering sets *)

(** If [A] and [B] have mexes [a] and [b], the same construction over [A] and
    [B] still names the product: the extra options miss it because a
    difference of factors has a nonzero product. *)
Theorem nmul_mex_rep :
  forall a b A B,
    mex A = a -> mex B = b ->
    nmul a b =
    mex (map (fun p => nadd (nadd (nmul (fst p) b) (nmul a (snd p)))
                            (nmul (fst p) (snd p)))
             (list_prod A B)).
Proof.
  intros a b A B Ha Hb; symmetry; apply mex_unique.
  - intros H; apply in_map_iff in H.
    destruct H as [p [Hv Hp]]; destruct p as [x y].
    apply in_prod_iff in Hp; destruct Hp as [HA HB]; cbn [fst snd] in *.
    apply (nmul_option_ne a b x y).
    + intros ->; apply (mex_not_in A); rewrite Ha; exact HA.
    + intros ->; apply (mex_not_in B); rewrite Hb; exact HB.
    + exact Hv.
  - intros x Hx.
    destruct (nmul_below_option a b x Hx) as [a' [b' [Ha' [Hb' Hv]]]].
    apply in_map_iff; exists (a', b'); split; [exact Hv|].
    apply in_prod_iff; split.
    + rewrite <- Ha in Ha'; apply mex_lt_in; exact Ha'.
    + rewrite <- Hb in Hb'; apply mex_lt_in; exact Hb'.
Qed.

(** * Associativity *)

Lemma mex_seq : forall n, mex (seq 0 n) = n.
Proof.
  intros n; apply mex_unique.
  - intros H; apply in_seq in H; lia.
  - intros x Hx; apply in_seq; lia.
Qed.

(** Both sides of associativity have the same options, indexed by the same
    triples: this is that computation, done once. *)
Lemma assoc_option_eq :
  forall N a b c a' b' c',
    a + b + c <= S N ->
    (forall x y z, x + y + z <= N -> nmul (nmul x y) z = nmul x (nmul y z)) ->
    a' < a -> b' < b -> c' < c ->
    nadd (nadd (nmul (prodopt nmul a b (a', b')) c) (nmul (nmul a b) c'))
         (nmul (prodopt nmul a b (a', b')) c')
    =
    nadd (nadd (nmul a' (nmul b c)) (nmul a (prodopt nmul b c (b', c'))))
         (nmul a' (prodopt nmul b c (b', c'))).
Proof.
  intros N a b c a' b' c' HN IH Ha Hb Hc.
  unfold prodopt; cbn [fst snd].
  rewrite !nmul_distr_r, !nmul_distr.
  rewrite (IH a' b c) by lia.
  rewrite (IH a b' c) by lia.
  rewrite (IH a' b' c) by lia.
  rewrite (IH a b c') by lia.
  rewrite (IH a' b c') by lia.
  rewrite (IH a b' c') by lia.
  rewrite (IH a' b' c') by lia.
  xor_eq.
Qed.

(** Nim multiplication is associative. *)
Theorem nmul_assoc :
  forall a b c, nmul (nmul a b) c = nmul a (nmul b c).
Proof.
  assert (Haux : forall N a b c,
             a + b + c <= N -> nmul (nmul a b) c = nmul a (nmul b c)).
  { induction N as [|N IH]; intros a b c HN.
    - assert (a = 0) as -> by lia; assert (b = 0) as -> by lia.
      assert (c = 0) as -> by lia.
      rewrite !nmul_0_l; reflexivity.
    - rewrite (nmul_mex_rep (nmul a b) c
                 (map (prodopt nmul a b) (pairs a b)) (seq 0 c))
        by (try (symmetry; apply nmul_eq); apply mex_seq).
      rewrite (nmul_mex_rep a (nmul b c)
                 (seq 0 a) (map (prodopt nmul b c) (pairs b c)))
        by (try apply mex_seq; symmetry; apply nmul_eq).
      apply mex_ext; intros v; split; intros Hv; apply in_map_iff in Hv;
        destruct Hv as [p [Hp Hin]]; destruct p as [x y]; cbn [fst snd] in *.
      + apply in_prod_iff in Hin; destruct Hin as [Hx Hy].
        apply in_map_iff in Hx; destruct Hx as [q [<- Hq]].
        apply in_pairs in Hq; destruct Hq as [Hq1 Hq2].
        apply in_seq in Hy.
        apply in_map_iff.
        exists (fst q, prodopt nmul b c (snd q, y)); split.
        * cbn [fst snd]; rewrite <- Hp; symmetry.
          apply (assoc_option_eq N a b c (fst q) (snd q) y);
            [lia | intros x1 y1 z1 H1; apply IH; lia | lia | lia | lia].
        * apply in_prod_iff; split; [apply in_seq; lia|].
          apply in_map_iff; exists (snd q, y); split; [reflexivity|].
          apply (proj2 (in_pairs b c (snd q, y))); cbn [fst snd]; lia.
      + apply in_prod_iff in Hin; destruct Hin as [Hx Hy].
        apply in_seq in Hx.
        apply in_map_iff in Hy; destruct Hy as [q [<- Hq]].
        apply in_pairs in Hq; destruct Hq as [Hq1 Hq2].
        apply in_map_iff.
        exists (prodopt nmul a b (x, fst q), snd q); split.
        * cbn [fst snd]; rewrite <- Hp.
          apply (assoc_option_eq N a b c x (fst q) (snd q));
            [lia | intros x1 y1 z1 H1; apply IH; lia | lia | lia | lia].
        * apply in_prod_iff; split; [|apply in_seq; lia].
          apply in_map_iff; exists (x, fst q); split; [reflexivity|].
          apply (proj2 (in_pairs a b (x, fst q))); cbn [fst snd]; lia. }
  intros a b c; apply (Haux (a + b + c)); lia.
Qed.

(** * A bound on products *)

Lemma mex_le_length : forall l, mex l <= length l.
Proof.
  intros l.
  apply (Nat.le_trans _ (length (seq 0 (mex l)))).
  - rewrite length_seq; lia.
  - apply NoDup_incl_length; [apply seq_NoDup|].
    intros x Hx; apply in_seq in Hx; apply mex_lt_in; lia.
Qed.

(** A product is at most the ordinary product, since that counts its options. *)
Theorem nmul_le_mul : forall a b, nmul a b <= a * b.
Proof.
  intros a b; rewrite nmul_eq.
  apply (Nat.le_trans _ (length (map (prodopt nmul a b) (pairs a b)))).
  - apply mex_le_length.
  - rewrite length_map; unfold pairs.
    rewrite length_prod, !length_seq; lia.
Qed.

(** So a product of nimbers below a power of two lies below its square. *)
Corollary nmul_lt_pow2_square :
  forall k a b, a < 2 ^ k -> b < 2 ^ k -> nmul a b < 2 ^ (k + k).
Proof.
  intros k a b Ha Hb.
  apply (Nat.le_lt_trans _ (a * b)); [apply nmul_le_mul|].
  rewrite Nat.pow_add_r.
  apply Nat.mul_lt_mono_nonneg; lia.
Qed.

(** * The Fermat levels *)

(** Closure holds exactly at the Fermat powers, and it is what inverses need. *)
Definition fermat (n : nat) : nat := 2 ^ (2 ^ n).

Lemma fermat_pos : forall n, 0 < fermat n.
Proof. intros n; unfold fermat; apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia. Qed.

Lemma fermat_ge_2 : forall n, 2 <= fermat n.
Proof.
  intros n; unfold fermat.
  apply (Nat.le_trans _ (2 ^ 1)); [cbn; lia|].
  apply Nat.pow_le_mono_r; [lia|].
  apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia.
Qed.

Lemma fermat_succ : forall n, fermat (S n) = fermat n * fermat n.
Proof.
  intros n; unfold fermat.
  rewrite <- Nat.pow_add_r; f_equal; cbn [Nat.pow]; lia.
Qed.

Definition closed_below (F : nat) : Prop :=
  forall a b, a < F -> b < F -> nmul a b < F.

Lemma closed_fermat_0 : closed_below (fermat 0).
Proof.
  unfold closed_below, fermat; cbn [Nat.pow].
  intros a b Ha Hb.
  destruct a as [|[|a]]; destruct b as [|[|b]]; try lia;
    rewrite ?nmul_0_l, ?nmul_0_r, ?nmul_1_l; lia.
Qed.

(** Inside a closed range, multiplying by a nonzero nimber permutes it. *)
Lemma nmul_surj_below :
  forall F u y,
    closed_below F -> u < F -> u <> 0 -> y < F ->
    exists x, x < F /\ nmul u x = y.
Proof.
  intros F u y Hcl Hu Hu0 Hy.
  assert (Hnd : NoDup (map (nmul u) (seq 0 F))).
  { apply NoDup_map_inj; [|apply seq_NoDup].
    intros x1 x2 He; apply (nmul_cancel u); assumption. }
  assert (Hincl : incl (map (nmul u) (seq 0 F)) (seq 0 F)).
  { intros v Hv; apply in_map_iff in Hv; destruct Hv as [x [<- Hx]].
    apply in_seq in Hx; apply in_seq; split; [lia|].
    cbn [Nat.add]; apply Hcl; lia. }
  assert (Hlen : length (seq 0 F) <= length (map (nmul u) (seq 0 F)))
    by (rewrite length_map; lia).
  pose proof (NoDup_length_incl Hnd Hlen Hincl) as Hback.
  assert (Hin : In y (map (nmul u) (seq 0 F)))
    by (apply Hback, in_seq; lia).
  apply in_map_iff in Hin; destruct Hin as [x [Hx Hxin]].
  apply in_seq in Hxin.
  exists x; split; [lia | exact Hx].
Qed.

(** A multiple of a power of two and a remainder below it do not interact. *)
Lemma nadd_mul_pow2 :
  forall k q r, r < 2 ^ k -> nadd (2 ^ k * q) r = 2 ^ k * q + r.
Proof.
  intros k q r Hr; unfold nadd.
  rewrite Nat.add_comm, Nat.lxor_comm.
  symmetry; apply Nat.add_nocarry_lxor.
  apply Nat.bits_inj; intros j.
  rewrite Nat.land_spec, Nat.bits_0.
  destruct (Nat.lt_ge_cases j k) as [Hj | Hj].
  - rewrite Nat.mul_comm, (Nat.mul_pow2_bits_low q k j Hj), andb_false_r.
    reflexivity.
  - rewrite (bit_high r j); [apply andb_false_l|].
    apply (Nat.lt_le_trans _ (2 ^ k)); [lia | apply Nat.pow_le_mono_r; lia].
Qed.

(** Below a closed power of two, multiplying by that power is the ordinary
    product: the options of [F * x] are exactly the numbers under it. *)
Theorem nmul_fermat_low :
  forall F x,
    closed_below F -> (exists k, F = 2 ^ k) -> x < F -> nmul F x = F * x.
Proof.
  intros F x Hcl Hpow; destruct Hpow as [k ->].
  assert (Haux : forall N x, x <= N -> x < (2 ^ k) -> nmul (2 ^ k) x = (2 ^ k) * x).
  { induction N as [|N IH]; intros y Hy Hlt.
    - assert (y = 0) as -> by lia; rewrite nmul_0_r; lia.
    - rewrite nmul_eq; apply mex_unique.
      + intros H; apply in_map_iff in H.
        destruct H as [p [Hv Hp]]; apply in_pairs in Hp; destruct Hp as [H1 H2].
        unfold prodopt in Hv.
        rewrite (IH (snd p)) in Hv by lia.
        assert (Hlow : nadd (nmul (fst p) y) (nmul (fst p) (snd p))
                       = nmul (fst p) (nadd y (snd p)))
          by (rewrite nmul_distr; reflexivity).
        assert (Hb : nmul (fst p) (nadd y (snd p)) < (2 ^ k)).
        { apply Hcl; [lia|].
          apply nadd_lt_pow2; lia. }
        assert (Hval : nadd (nadd (nmul (fst p) y) ((2 ^ k) * snd p))
                            (nmul (fst p) (snd p))
                       = nadd ((2 ^ k) * snd p) (nmul (fst p) (nadd y (snd p))))
          by (rewrite <- Hlow; xor_eq).
        rewrite Hval in Hv.
        assert (Hsum : nadd ((2 ^ k) * snd p) (nmul (fst p) (nadd y (snd p)))
                       = (2 ^ k) * snd p + nmul (fst p) (nadd y (snd p))).
        { apply nadd_mul_pow2; exact Hb. }
        rewrite Hsum in Hv.
        assert (Hlt2 : (2 ^ k) * snd p + nmul (fst p) (nadd y (snd p)) < (2 ^ k) * y).
        { assert (Hle : (2 ^ k) * (snd p + 1) <= (2 ^ k) * y)
            by (apply Nat.mul_le_mono_l; lia).
          rewrite Nat.mul_add_distr_l, Nat.mul_1_r in Hle; lia. }
        lia.
      + intros v Hv.
        apply in_map_iff.
        set (x' := v / (2 ^ k)).
        set (r := v mod (2 ^ k)).
        assert (HF : 0 < (2 ^ k)) by lia.
        assert (Hx' : x' < y).
        { unfold x'; apply Nat.div_lt_upper_bound; [lia|]; rewrite Nat.mul_comm; lia. }
        assert (Hr : r < (2 ^ k)) by (unfold r; apply Nat.mod_upper_bound; lia).
        assert (Hne : nadd y x' <> 0).
        { intros H0; apply (proj1 (nadd_eq_0 y x')) in H0; lia. }
        assert (Hlt3 : nadd y x' < (2 ^ k))
          by (apply nadd_lt_pow2; lia).
        destruct (nmul_surj_below (2 ^ k) (nadd y x') r Hcl Hlt3 Hne Hr)
          as [f' [Hf' Hfv]].
        exists (f', x'); split.
        * unfold prodopt; cbn [fst snd].
          rewrite (IH x') by lia.
          assert (Hlow : nadd (nmul f' y) (nmul f' x') = nmul f' (nadd y x'))
            by (rewrite nmul_distr; reflexivity).
          assert (Hval : nadd (nadd (nmul f' y) ((2 ^ k) * x')) (nmul f' x')
                         = nadd ((2 ^ k) * x') (nmul f' (nadd y x')))
            by (rewrite <- Hlow; xor_eq).
          rewrite Hval, (nmul_comm f' (nadd y x')), Hfv.
          assert (Hsum : nadd ((2 ^ k) * x') r = (2 ^ k) * x' + r).
          { apply nadd_mul_pow2; exact Hr. }
          rewrite Hsum.
          unfold x', r.
          pose proof (Nat.Div0.div_mod v (2 ^ k)) as Hdm.
          lia.
        * apply (proj2 (in_pairs (2 ^ k) y (f', x'))); cbn [fst snd]; auto. }
  intros Hx; apply (Haux x); lia.
Qed.

(** Splitting a nimber below [F * F] into its quotient and remainder. *)
Lemma split_below_square :
  forall k x,
    x < 2 ^ k * 2 ^ k ->
    exists q r, q < 2 ^ k /\ r < 2 ^ k /\ x = nadd (2 ^ k * q) r.
Proof.
  intros k x Hx.
  assert (Hp : 0 < 2 ^ k) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  exists (x / 2 ^ k), (x mod 2 ^ k); repeat split.
  - apply Nat.Div0.div_lt_upper_bound; lia.
  - apply Nat.mod_upper_bound; lia.
  - rewrite nadd_mul_pow2 by (apply Nat.mod_upper_bound; lia).
    pose proof (Nat.Div0.div_mod x (2 ^ k)); lia.
Qed.

(** * Squaring *)

(** In characteristic two squaring is additive, so it is injective. *)
Lemma nsq_add : forall x y, nmul (nadd x y) (nadd x y) = nadd (nmul x x) (nmul y y).
Proof.
  intros x y; rewrite nmul_distr_r, !nmul_distr.
  rewrite (nmul_comm y x); xor_eq.
Qed.

Lemma nsq_inj : forall x y, nmul x x = nmul y y -> x = y.
Proof.
  intros x y H.
  destruct (Nat.eq_dec x y) as [Hxy | Hxy]; [exact Hxy|].
  exfalso.
  assert (Hd : nadd x y <> 0)
    by (intros H0; apply Hxy, (proj1 (nadd_eq_0 x y)); exact H0).
  apply (nmul_neq_0 (nadd x y) (nadd x y) Hd Hd).
  rewrite nsq_add, H; apply nadd_self.
Qed.

(** So on a closed range every nimber is a square, which is the Frobenius map
    being a permutation there. *)
Theorem nsq_surj_below :
  forall F y, closed_below F -> y < F -> exists x, x < F /\ nmul x x = y.
Proof.
  intros F y Hcl Hy.
  assert (Hnd : NoDup (map (fun x => nmul x x) (seq 0 F))).
  { apply NoDup_map_inj; [|apply seq_NoDup].
    intros x1 x2 He; apply nsq_inj; exact He. }
  assert (Hincl : incl (map (fun x => nmul x x) (seq 0 F)) (seq 0 F)).
  { intros v Hv; apply in_map_iff in Hv; destruct Hv as [x [<- Hx]].
    apply in_seq in Hx; apply in_seq; split; [lia|].
    cbn [Nat.add]; apply Hcl; lia. }
  assert (Hlen : length (seq 0 F) <= length (map (fun x => nmul x x) (seq 0 F)))
    by (rewrite length_map; lia).
  pose proof (NoDup_length_incl Hnd Hlen Hincl) as Hback.
  assert (Hin : In y (map (fun x => nmul x x) (seq 0 F)))
    by (apply Hback, in_seq; lia).
  apply in_map_iff in Hin; destruct Hin as [x [Hx Hxin]].
  apply in_seq in Hxin.
  exists x; split; [lia | exact Hx].
Qed.

(** The values the trace argument runs over. *)
Definition trace_val (x : nat) : nat := nadd (nmul x x) x.

Lemma trace_val_pair : forall x, trace_val (nadd x 1) = trace_val x.
Proof.
  intros x; unfold trace_val.
  rewrite nsq_add, nmul_1_l; xor_eq.
Qed.

Lemma trace_val_eq_inv :
  forall x y, trace_val x = trace_val y -> y = x \/ y = nadd x 1.
Proof.
  intros x y H; unfold trace_val in H.
  destruct (Nat.eq_dec x y) as [-> | Hne]; [left; reflexivity | right].
  assert (Hd : nadd x y <> 0)
    by (intros H0; apply Hne, (proj1 (nadd_eq_0 x y)); exact H0).
  assert (Hsq : nmul (nadd x y) (nadd x y) = nadd x y).
  { rewrite nsq_add.
    assert (Hxy : nadd (nmul x x) x = nadd (nmul y y) y) by exact H.
    apply (nadd_cancel_l (nadd (nmul y y) y)).
    rewrite <- Hxy at 1.
    replace (nadd (nadd (nmul x x) x) (nadd (nmul x x) (nmul y y)))
      with (nadd x (nmul y y)) by xor_eq.
    replace (nadd (nadd (nmul y y) y) (nadd x y)) with (nadd (nmul y y) x)
      by xor_eq.
    apply nadd_comm. }
  assert (H1 : nmul (nadd x y) (nadd x y) = nmul (nadd x y) 1)
    by (rewrite nmul_1_r; exact Hsq).
  apply nmul_cancel in H1; [|exact Hd].
  apply (nadd_cancel_l x); rewrite <- H1; xor_eq.
Qed.

(** The trace values are closed under the level, since a sum of nimbers below
    a power of two stays below it. *)
Lemma trace_val_below :
  forall k x, closed_below (2 ^ k) -> x < 2 ^ k -> trace_val x < 2 ^ k.
Proof.
  intros k x Hcl Hx; unfold trace_val.
  apply nadd_lt_pow2; [apply Hcl; assumption | assumption].
Qed.

(** Each trace value is taken exactly twice, by [x] and by [x + 1]. *)
Theorem trace_val_fibre :
  forall x y, trace_val x = trace_val y <-> (y = x \/ y = nadd x 1).
Proof.
  intros x y; split; [apply trace_val_eq_inv|].
  intros [-> | ->]; [reflexivity | symmetry; apply trace_val_pair].
Qed.

Lemma nadd_1_ne : forall x, nadd x 1 <> x.
Proof.
  intros x H.
  assert (H0 : nadd x x = nadd (nadd x 1) x) by (rewrite H at 1; reflexivity).
  rewrite nadd_self in H0.
  replace (nadd (nadd x 1) x) with 1 in H0 by xor_eq.
  discriminate.
Qed.

(** * Counting fibres *)

Lemma filter_filter :
  forall {A : Type} (g h : A -> bool) l,
    filter g (filter h l) = filter (fun x => andb (h x) (g x)) l.
Proof.
  intros A g h l; induction l as [|a l IH]; [reflexivity|]; simpl.
  destruct (h a) eqn:Eh; simpl.
  - destruct (g a) eqn:Eg; simpl; rewrite IH; reflexivity.
  - exact IH.
Qed.

Lemma filter_filter_ne :
  forall (f : nat -> nat) v w l,
    w <> v ->
    filter (fun x => Nat.eqb (f x) w) (filter (fun x => negb (Nat.eqb (f x) v)) l)
    = filter (fun x => Nat.eqb (f x) w) l.
Proof.
  intros f v w l Hne; rewrite filter_filter.
  apply filter_ext; intros x.
  destruct (Nat.eqb (f x) w) eqn:Ew; destruct (Nat.eqb (f x) v) eqn:Ev;
    cbn [negb andb]; try reflexivity.
  exfalso; apply Hne.
  apply Nat.eqb_eq in Ev; apply Nat.eqb_eq in Ew; rewrite <- Ev, <- Ew; reflexivity.
Qed.

Lemma length_filter_split :
  forall (f : nat -> nat) v l,
    length l = length (filter (fun x => Nat.eqb (f x) v) l)
             + length (filter (fun x => negb (Nat.eqb (f x) v)) l).
Proof.
  intros f v l; induction l as [|a l IH]; [reflexivity|]; simpl.
  destruct (Nat.eqb (f a) v); simpl; lia.
Qed.

Lemma count_fibres :
  forall (f : nat -> nat) (img l : list nat),
    NoDup img ->
    (forall x, In x l -> In (f x) img) ->
    length l =
    list_sum (map (fun v => length (filter (fun x => Nat.eqb (f x) v) l)) img).
Proof.
  intros f img; induction img as [|v img IH]; intros l Hnd Hcov.
  - destruct l as [|a l]; [reflexivity|].
    exfalso; apply (Hcov a); cbn; auto.
  - assert (Hcons : forall (a : nat) r, list_sum (a :: r) = a + list_sum r)
      by reflexivity.
    cbn [map]; rewrite Hcons.
    inversion Hnd as [|v' img' Hv Hnd']; subst.
    assert (Hcov' : forall x, In x (filter (fun x => negb (Nat.eqb (f x) v)) l) ->
                    In (f x) img).
    { intros x Hx; apply filter_In in Hx; destruct Hx as [Hx Hne].
      destruct (Hcov x Hx) as [Heq | Hin]; [|exact Hin].
      rewrite <- Heq, Nat.eqb_refl in Hne; discriminate. }
    pose proof (IH (filter (fun x => negb (Nat.eqb (f x) v)) l) Hnd' Hcov') as Hl'.
    assert (Hmap : map (fun w => length (filter (fun x => Nat.eqb (f x) w) l)) img
                 = map (fun w => length (filter (fun x => Nat.eqb (f x) w)
                          (filter (fun x => negb (Nat.eqb (f x) v)) l))) img).
    { apply map_ext_in; intros w Hw; f_equal.
      symmetry; apply filter_filter_ne; intros ->; contradiction. }
    rewrite Hmap, <- Hl'.
    apply length_filter_split.
Qed.

(** Each trace value is taken by exactly two nimbers of the level, so the
    values number half of it. *)
Theorem trace_image_half :
  forall k,
    closed_below (2 ^ k) -> 0 < k ->
    2 * length (nodup Nat.eq_dec (map trace_val (seq 0 (2 ^ k)))) = 2 ^ k.
Proof.
  intros k Hcl Hk.
  set (F := 2 ^ k).
  set (img := nodup Nat.eq_dec (map trace_val (seq 0 F))).
  assert (HF2 : 2 <= F).
  { unfold F; apply (Nat.le_trans _ (2 ^ 1)); [cbn; lia|].
    apply Nat.pow_le_mono_r; lia. }
  assert (Hpair : forall x, x < F -> nadd x 1 < F)
    by (intros x Hx; unfold F; apply nadd_lt_pow2; [exact Hx | lia]).
  assert (Hcov : forall x, In x (seq 0 F) -> In (trace_val x) img).
  { intros x Hx; apply nodup_In, in_map_iff; exists x; auto. }
  pose proof (count_fibres trace_val img (seq 0 F) (NoDup_nodup _ _) Hcov) as Hsum.
  rewrite length_seq in Hsum.
  assert (Hfib : forall v, In v img ->
             length (filter (fun x => Nat.eqb (trace_val x) v) (seq 0 F)) = 2).
  { intros v Hv.
    apply nodup_In, in_map_iff in Hv; destruct Hv as [x [<- Hx]].
    apply in_seq in Hx.
    assert (Hmem : forall y,
               In y (filter (fun y => Nat.eqb (trace_val y) (trace_val x)) (seq 0 F))
               <-> In y [x; nadd x 1]).
    { intros y; rewrite filter_In, in_seq; cbn [In]; split.
      - intros [Hy Hev]; apply Nat.eqb_eq in Hev.
        destruct (trace_val_eq_inv x y ltac:(symmetry; exact Hev)) as [-> | ->];
          auto.
      - intros [<- | [<- | []]].
        + split; [split; [lia | cbn [Nat.add]; lia]|].
          apply Nat.eqb_eq; reflexivity.
        + split; [split; [lia | cbn [Nat.add]; apply Hpair; lia]|].
          apply Nat.eqb_eq; apply trace_val_pair. }
    assert (Hnd1 : NoDup (filter (fun y => Nat.eqb (trace_val y) (trace_val x))
                             (seq 0 F)))
      by (apply NoDup_filter, seq_NoDup).
    assert (Hnd2 : NoDup [x; nadd x 1]).
    { constructor; [|constructor; [intros [] | constructor]].
      intros [H | []]; apply (nadd_1_ne x); exact H. }
    assert (Hle1 : length (filter (fun y => Nat.eqb (trace_val y) (trace_val x))
                              (seq 0 F)) <= length [x; nadd x 1])
      by (apply NoDup_incl_length; [exact Hnd1 | intros y Hy; apply Hmem; auto]).
    assert (Hle2 : length [x; nadd x 1]
                   <= length (filter (fun y => Nat.eqb (trace_val y) (trace_val x))
                                (seq 0 F)))
      by (apply NoDup_incl_length; [exact Hnd2 | intros y Hy; apply Hmem; auto]).
    cbn [length] in Hle1, Hle2; lia. }
  rewrite (map_ext_in _ (fun _ => 2)) in Hsum by (intros v Hv; apply Hfib; exact Hv).
  assert (Hconst : forall l : list nat,
             list_sum (map (fun _ : nat => 2) l) = 2 * length l).
  { induction l as [|a l IHl]; simpl; lia. }
  rewrite (Hconst img) in Hsum.
  unfold img, F in *; lia.
Qed.

(** * Options of a square level *)

(** Shifting by a power of two commutes with the exclusive or. *)
Lemma mul_pow2_lxor :
  forall k a b, 2 ^ k * Nat.lxor a b = Nat.lxor (2 ^ k * a) (2 ^ k * b).
Proof.
  intros k a b.
  apply Nat.bits_inj; intros n.
  rewrite Nat.lxor_spec.
  destruct (Nat.lt_ge_cases n k) as [Hn | Hn].
  - rewrite !Nat.mul_comm with (n := 2 ^ k).
    rewrite !Nat.mul_pow2_bits_low by exact Hn; reflexivity.
  - rewrite !Nat.mul_comm with (n := 2 ^ k).
    rewrite !Nat.mul_pow2_bits_high by exact Hn.
    rewrite Nat.lxor_spec; reflexivity.
Qed.

(** The options of [F * F] are the sums of a multiple of [F] and a product of
    two smaller nimbers, and every such value with a nonzero multiplier lies
    above the level. *)
Lemma fermat_square_option :
  forall k F' F'',
    closed_below (2 ^ k) -> F' < 2 ^ k -> F'' < 2 ^ k ->
    nadd (nadd (nmul F' (2 ^ k)) (nmul (2 ^ k) F'')) (nmul F' F'')
    = nadd (2 ^ k * nadd F' F'') (nmul F' F'').
Proof.
  intros k F' F'' Hcl H1 H2.
  rewrite (nmul_comm F' (2 ^ k)).
  rewrite !nmul_fermat_low by (auto; try (exists k; reflexivity)).
  f_equal.
  unfold nadd; rewrite <- mul_pow2_lxor; reflexivity.
Qed.

(** Every value below the level is a square of something below it, so with
    equal factors the options already cover the level. *)
Lemma fermat_square_options_low :
  forall k v,
    closed_below (2 ^ k) -> v < 2 ^ k ->
    exists F' F'', F' < 2 ^ k /\ F'' < 2 ^ k /\
      nadd (nadd (nmul F' (2 ^ k)) (nmul (2 ^ k) F'')) (nmul F' F'') = v.
Proof.
  intros k v Hcl Hv.
  destruct (nsq_surj_below (2 ^ k) v Hcl Hv) as [x [Hx Hsq]].
  exists x, x; repeat split; auto.
  rewrite (fermat_square_option k x x Hcl Hx Hx).
  rewrite nadd_self, Nat.mul_0_r; cbn [nadd].
  rewrite nadd_0_l; exact Hsq.
Qed.

(** With unequal factors the option lies at least a level up, and its offset
    above [F] runs over the trace values. *)
Lemma fermat_square_options_high :
  forall k F' F'',
    closed_below (2 ^ k) -> F' < 2 ^ k -> F'' < 2 ^ k -> nadd F' F'' = 1 ->
    nadd (nadd (nmul F' (2 ^ k)) (nmul (2 ^ k) F'')) (nmul F' F'')
    = 2 ^ k + trace_val F'.
Proof.
  intros k F' F'' Hcl H1 H2 Hd.
  rewrite (fermat_square_option k F' F'' Hcl H1 H2), Hd, Nat.mul_1_r.
  assert (Hf'' : F'' = nadd F' 1).
  { apply (nadd_cancel_l F'); rewrite Hd; xor_eq. }
  rewrite Hf''.
  assert (Htr : nmul F' (nadd F' 1) = trace_val F').
  { unfold trace_val; rewrite nmul_distr, nmul_1_r; reflexivity. }
  rewrite Htr.
  pose proof (nadd_mul_pow2 k 1 (trace_val F')) as Hnc.
  rewrite Nat.mul_1_r in Hnc.
  apply Hnc.
  unfold trace_val; apply nadd_lt_pow2; [apply Hcl; assumption | assumption].
Qed.

(** The trace values are exactly the lower half of the level. *)
Definition trace_image (k : nat) : list nat :=
  nodup Nat.eq_dec (map trace_val (seq 0 (2 ^ k))).

Lemma trace_image_incl :
  forall k, closed_below (2 ^ k) -> incl (trace_image k) (seq 0 (2 ^ k)).
Proof.
  intros k Hcl v Hv; unfold trace_image in Hv.
  apply nodup_In, in_map_iff in Hv; destruct Hv as [x [<- Hx]].
  apply in_seq in Hx; apply in_seq; split; [lia|].
  cbn [Nat.add]; unfold trace_val.
  apply nadd_lt_pow2; [apply Hcl; lia | lia].
Qed.

Lemma trace_image_nodup : forall k, NoDup (trace_image k).
Proof. intros k; apply NoDup_nodup. Qed.

(** A nimber is a trace value exactly when it is in that image. *)
Lemma in_trace_image :
  forall k v,
    In v (trace_image k) <-> exists x, x < 2 ^ k /\ trace_val x = v.
Proof.
  intros k v; unfold trace_image; rewrite nodup_In, in_map_iff; split.
  - intros [x [Hx Hin]]; apply in_seq in Hin; exists x; split; [lia | exact Hx].
  - intros [x [Hx <-]]; exists x; split; [reflexivity | apply in_seq; lia].
Qed.

(** The mex of the trace image is where the options of the level square stop
    covering, one level up. *)
Lemma trace_mex_lt :
  forall k, closed_below (2 ^ k) -> 0 < k -> mex (trace_image k) < 2 ^ k.
Proof.
  intros k Hcl Hk.
  pose proof (trace_image_half k Hcl Hk) as Hhalf.
  fold (trace_image k) in Hhalf.
  assert (Hle : mex (trace_image k) <= length (trace_image k))
    by apply mex_le_length.
  assert (H2 : 2 <= 2 ^ k).
  { apply (Nat.le_trans _ (2 ^ 1)); [cbn; lia | apply Nat.pow_le_mono_r; lia]. }
  lia.
Qed.

(** Half the level is the number of trace values, so the level is twice it. *)
Lemma trace_image_length :
  forall k,
    closed_below (2 ^ k) -> 0 < k ->
    2 * length (trace_image k) = 2 ^ k.
Proof.
  intros k Hcl Hk; unfold trace_image; apply trace_image_half; assumption.
Qed.

(** * The square of a level *)

(** The options of [F * F], listed by their two shapes. *)
Lemma nmul_fermat_square_options :
  forall k v,
    closed_below (2 ^ k) -> 0 < k ->
    In v (map (prodopt nmul (2 ^ k) (2 ^ k)) (pairs (2 ^ k) (2 ^ k))) <->
    exists F' F'', F' < 2 ^ k /\ F'' < 2 ^ k /\
      v = nadd (2 ^ k * nadd F' F'') (nmul F' F'').
Proof.
  intros k v Hcl Hk; split.
  - intros H; apply in_map_iff in H.
    destruct H as [p [<- Hp]]; apply in_pairs in Hp; destruct Hp as [H1 H2].
    exists (fst p), (snd p); repeat split; auto.
    unfold prodopt.
    apply (fermat_square_option k (fst p) (snd p) Hcl H1 H2).
  - intros [F' [F'' [H1 [H2 ->]]]].
    apply in_map_iff; exists (F', F''); split.
    + unfold prodopt; cbn [fst snd].
      apply (fermat_square_option k F' F'' Hcl H1 H2).
    + apply (proj2 (in_pairs (2 ^ k) (2 ^ k) (F', F''))); cbn [fst snd]; auto.
Qed.

(** Everything below the level is an option, so the value of the square is at
    least the level. *)
Lemma nmul_fermat_square_ge :
  forall k,
    closed_below (2 ^ k) -> 0 < k -> 2 ^ k <= nmul (2 ^ k) (2 ^ k).
Proof.
  intros k Hcl Hk.
  rewrite nmul_eq.
  destruct (Nat.le_gt_cases (2 ^ k) (mex (map (prodopt nmul (2 ^ k) (2 ^ k))
                                          (pairs (2 ^ k) (2 ^ k))))) as [H | H];
    [exact H|].
  exfalso.
  destruct (fermat_square_options_low k (mex (map (prodopt nmul (2 ^ k) (2 ^ k))
                                              (pairs (2 ^ k) (2 ^ k)))) Hcl H)
    as [F' [F'' [H1 [H2 Hv]]]].
  apply (mex_not_in (map (prodopt nmul (2 ^ k) (2 ^ k)) (pairs (2 ^ k) (2 ^ k)))).
  apply in_map_iff; exists (F', F''); split.
  + unfold prodopt; cbn [fst snd]; exact Hv.
  + apply (proj2 (in_pairs (2 ^ k) (2 ^ k) (F', F''))); cbn [fst snd]; auto.
Qed.

(** Above the level, the options are the level plus a trace value, so the
    square of the level is the level plus the mex of the trace values. *)
Lemma nmul_fermat_square_high :
  forall k v,
    closed_below (2 ^ k) -> 0 < k -> v < 2 ^ k ->
    In (2 ^ k + v) (map (prodopt nmul (2 ^ k) (2 ^ k)) (pairs (2 ^ k) (2 ^ k)))
    <-> In v (trace_image k).
Proof.
  intros k v Hcl Hk Hv0.
  assert (H2 : 2 <= 2 ^ k)
    by (apply (Nat.le_trans _ (2 ^ 1)); [cbn; lia | apply Nat.pow_le_mono_r; lia]).
  rewrite (nmul_fermat_square_options k (2 ^ k + v) Hcl Hk); split.
  - intros [F' [F'' [H1 [H2' Hv]]]].
    assert (Hd : nadd F' F'' = 1).
    { destruct (Nat.eq_dec (nadd F' F'') 0) as [H0 | Hne].
      - exfalso; rewrite H0, Nat.mul_0_r, nadd_0_l in Hv.
        assert (Hlow : nmul F' F'' < 2 ^ k) by (apply Hcl; assumption).
        lia.
      - destruct (Nat.eq_dec (nadd F' F'') 1) as [H1' | Hne1]; [exact H1'|].
        exfalso.
        assert (Hge : 2 <= nadd F' F'') by lia.
        assert (Hlow : nmul F' F'' < 2 ^ k) by (apply Hcl; assumption).
        assert (Hbig : 2 ^ k * 2 <= 2 ^ k * nadd F' F'')
          by (apply Nat.mul_le_mono_l; lia).
        assert (Hsum : nadd (2 ^ k * nadd F' F'') (nmul F' F'')
                       = 2 ^ k * nadd F' F'' + nmul F' F'')
          by (apply nadd_mul_pow2; exact Hlow).
        lia. }
    apply in_trace_image; exists F'; split; [exact H1|].
    pose proof (fermat_square_options_high k F' F'' Hcl H1 H2' Hd) as Hhigh.
    rewrite (fermat_square_option k F' F'' Hcl H1 H2') in Hhigh.
    rewrite Hhigh in Hv; lia.
  - intros Hv; apply in_trace_image in Hv; destruct Hv as [x [Hx <-]].
    exists x, (nadd x 1); repeat split.
    + exact Hx.
    + apply nadd_lt_pow2; lia.
    + rewrite <- (fermat_square_option k x (nadd x 1) Hcl Hx
                    ltac:(apply nadd_lt_pow2; lia)).
      rewrite (fermat_square_options_high k x (nadd x 1) Hcl Hx
                 ltac:(apply nadd_lt_pow2; lia)); [reflexivity|].
      xor_eq.
Qed.

(** So the square of a level is the level plus the first nimber that is not a
    trace value. *)
Theorem nmul_fermat_square :
  forall k,
    closed_below (2 ^ k) -> 0 < k ->
    nmul (2 ^ k) (2 ^ k) = 2 ^ k + mex (trace_image k).
Proof.
  intros k Hcl Hk.
  pose proof (trace_mex_lt k Hcl Hk) as Hmex.
  rewrite nmul_eq; apply mex_unique.
  - intros H.
    rewrite (nmul_fermat_square_high k (mex (trace_image k)) Hcl Hk Hmex) in H.
    apply (mex_not_in (trace_image k)); exact H.
  - intros x Hx.
    destruct (Nat.lt_ge_cases x (2 ^ k)) as [Hlow | Hhigh].
    + destruct (fermat_square_options_low k x Hcl Hlow) as [F' [F'' [H1 [H2 Hv]]]].
      apply in_map_iff; exists (F', F''); split.
      * unfold prodopt; cbn [fst snd]; exact Hv.
      * apply (proj2 (in_pairs (2 ^ k) (2 ^ k) (F', F''))); cbn [fst snd]; auto.
    + assert (Hx' : x - 2 ^ k < mex (trace_image k)) by lia.
      assert (Hlt : x - 2 ^ k < 2 ^ k) by lia.
      replace x with (2 ^ k + (x - 2 ^ k)) by lia.
      apply (nmul_fermat_square_high k (x - 2 ^ k) Hcl Hk Hlt).
      apply mex_lt_in; exact Hx'.
Qed.

(** At the first levels the first non-trace value is half the level, which is
    Conway's rule that a level squared is three halves of it. *)
Example trace_mex_1 : mex (trace_image 1) = 1.
Proof. vm_compute; reflexivity. Qed.

Example trace_mex_2 : mex (trace_image 2) = 2.
Proof. vm_compute; reflexivity. Qed.

Example nmul_4_4 : nmul 4 4 = 6.
Proof. vm_compute; reflexivity. Qed.

(** * The lower half *)

(** The trace values of a level are closed downward, so being half of the
    level in number they are exactly its lower half. *)
Lemma trace_image_mex_le :
  forall k, closed_below (2 ^ k) -> 0 < k ->
    mex (trace_image k) <= 2 ^ k / 2.
Proof.
  intros k Hcl Hk.
  pose proof (trace_image_length k Hcl Hk) as Hlen.
  pose proof (mex_le_length (trace_image k)) as Hle.
  assert (H2 : 2 ^ k / 2 = length (trace_image k)).
  { rewrite <- Hlen, Nat.mul_comm, Nat.div_mul; lia. }
  lia.
Qed.

(** With the mex at half the level, the square rule takes Conway's form. *)
Theorem nmul_fermat_square_half :
  forall k,
    closed_below (2 ^ k) -> 0 < k ->
    mex (trace_image k) = 2 ^ k / 2 ->
    nmul (2 ^ k) (2 ^ k) = 2 ^ k + 2 ^ k / 2.
Proof.
  intros k Hcl Hk Hmex.
  rewrite (nmul_fermat_square k Hcl Hk), Hmex; reflexivity.
Qed.

(** And then a product of two nimbers below the square of a level stays there:
    the four pieces of the expansion are each in range. *)
Theorem closed_below_square :
  forall k,
    closed_below (2 ^ k) -> 0 < k ->
    mex (trace_image k) = 2 ^ k / 2 ->
    closed_below (2 ^ k * 2 ^ k).
Proof.
  intros k Hcl Hk Hmex a b Ha Hb.
  assert (Hp : 0 < 2 ^ k) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  assert (Hhalf : 2 ^ k / 2 < 2 ^ k)
    by (apply Nat.div_lt; lia).
  assert (Hlow : forall x, x < 2 ^ k -> nmul (2 ^ k) x = 2 ^ k * x)
    by (intros x Hx; apply nmul_fermat_low; auto; exists k; reflexivity).
  destruct (split_below_square k a Ha) as [q [r [Hq [Hr ->]]]].
  destruct (split_below_square k b Hb) as [q' [r' [Hq' [Hr' ->]]]].
  rewrite !nmul_distr, !nmul_distr_r.
  (* the piece with both quotients, using the square rule *)
  assert (HPP : nmul (2 ^ k * q) (2 ^ k * q')
                = nadd (2 ^ k * nmul q q') (nmul (nmul q q') (2 ^ k / 2))).
  { rewrite <- !Hlow by assumption.
    rewrite <- nmul_assoc, (nmul_comm (nmul (2 ^ k) q) (2 ^ k)).
    rewrite <- nmul_assoc, nmul_assoc.
    rewrite (nmul_fermat_square_half k Hcl Hk Hmex).
    assert (Hsplit : 2 ^ k + 2 ^ k / 2 = nadd (2 ^ k) (2 ^ k / 2)).
    { pose proof (nadd_mul_pow2 k 1 (2 ^ k / 2) Hhalf) as Hnc.
      rewrite Nat.mul_1_r in Hnc; lia. }
    rewrite Hsplit, nmul_comm, nmul_distr.
    rewrite (nmul_comm (nmul q q') (2 ^ k)), Hlow by (apply Hcl; assumption).
    reflexivity. }
  rewrite HPP.
  assert (HQ : nmul (2 ^ k * q) r' = 2 ^ k * nmul q r').
  { rewrite <- (Hlow q Hq).
    rewrite nmul_assoc, (Hlow (nmul q r')) by (apply Hcl; assumption).
    reflexivity. }
  assert (HR : nmul r (2 ^ k * q') = 2 ^ k * nmul r q').
  { rewrite <- (Hlow q' Hq').
    rewrite (nmul_comm r (nmul (2 ^ k) q')), nmul_assoc.
    rewrite (nmul_comm q' r), (Hlow (nmul r q')) by (apply Hcl; assumption).
    reflexivity. }
  rewrite HQ, HR.
  (* every piece is a multiple of the level plus something below it *)
  set (hi := nadd (nadd (nmul q q') (nmul q r')) (nmul r q')).
  set (lo := nadd (nmul (nmul q q') (2 ^ k / 2)) (nmul r r')).
  assert (Hcollect : nadd (nadd (nadd (2 ^ k * nmul q q')
                                  (nmul (nmul q q') (2 ^ k / 2)))
                            (2 ^ k * nmul r q'))
                       (nadd (2 ^ k * nmul q r') (nmul r r'))
                     = nadd (2 ^ k * hi) lo).
  { unfold hi, lo, nadd; rewrite !mul_pow2_lxor; xor_eq. }
  rewrite Hcollect.
  assert (Hhi : hi < 2 ^ k)
    by (unfold hi; repeat (apply nadd_lt_pow2); apply Hcl; assumption).
  assert (Hlo : lo < 2 ^ k).
  { unfold lo; apply nadd_lt_pow2; apply Hcl; try assumption.
    apply Hcl; assumption. }
  rewrite (nadd_mul_pow2 k hi lo Hlo).
  assert (Hbound : 2 ^ k * hi + lo < 2 ^ k * 2 ^ k).
  { assert (2 ^ k * hi + 2 ^ k <= 2 ^ k * 2 ^ k).
    { replace (2 ^ k * hi + 2 ^ k) with (2 ^ k * (hi + 1)) by lia.
      apply Nat.mul_le_mono_l; lia. }
    lia. }
  exact Hbound.
Qed.

(** * Inverses *)

(** In a closed range every nonzero nimber has an inverse there, since
    multiplying by it permutes the range. *)
Theorem nmul_inverse_below :
  forall F a,
    closed_below F -> 1 < F -> a < F -> a <> 0 ->
    exists b, b < F /\ nmul a b = 1.
Proof.
  intros F a Hcl HF Ha Ha0.
  destruct (nmul_surj_below F a 1 Hcl Ha Ha0 ltac:(lia)) as [b [Hb Hv]].
  exists b; split; assumption.
Qed.

(** The levels chain: closure and the square rule at one level give closure at
    the next, so a level that is closed with the rule holding all the way up
    stays closed. *)
Definition level_ok (k : nat) : Prop :=
  closed_below (2 ^ k) /\ (0 < k -> mex (trace_image k) = 2 ^ k / 2).

Lemma level_ok_0 : closed_below (2 ^ 0).
Proof.
  cbn [Nat.pow]; intros a b Ha Hb.
  assert (a = 0) as -> by lia; rewrite nmul_0_l; lia.
Qed.

Lemma level_ok_1 : closed_below (2 ^ 1).
Proof.
  cbn [Nat.pow]; intros a b Ha Hb.
  destruct a as [|[|a]]; destruct b as [|[|b]]; try lia;
    rewrite ?nmul_0_l, ?nmul_0_r, ?nmul_1_l; lia.
Qed.

Lemma closed_step :
  forall k,
    closed_below (2 ^ k) -> 0 < k ->
    mex (trace_image k) = 2 ^ k / 2 ->
    closed_below (2 ^ (k + k)).
Proof.
  intros k Hcl Hk Hmex.
  rewrite Nat.pow_add_r.
  apply closed_below_square; assumption.
Qed.

(** So the first two Fermat levels are closed outright. *)
Theorem closed_fermat_1 : closed_below (fermat 1).
Proof.
  assert (H : fermat 1 = 2 ^ 2) by (unfold fermat; f_equal; cbn; lia).
  rewrite H.
  replace (2 ^ 2) with (2 ^ (1 + 1)) by (f_equal; lia).
  apply closed_step; [apply level_ok_1 | lia |].
  apply trace_mex_1.
Qed.

Theorem closed_fermat_2 : closed_below (fermat 2).
Proof.
  assert (H4 : fermat 2 = 2 ^ (2 + 2)) by (unfold fermat; f_equal; cbn; lia).
  rewrite H4.
  apply closed_step; [| lia |].
  - replace (2 ^ 2) with 4 by (cbn; lia).
    replace 4 with (2 ^ 2) by (cbn; lia).
    apply (closed_step 1); [apply level_ok_1 | lia |].
    cbn [Nat.pow]; apply trace_mex_1.
  - replace (2 ^ 2) with 4 by (cbn; lia); apply trace_mex_2.
Qed.

(** Every nonzero nimber below a settled level has an inverse there. *)
Theorem nmul_inverse_fermat_2 :
  forall a, a < fermat 2 -> a <> 0 -> exists b, b < fermat 2 /\ nmul a b = 1.
Proof.
  intros a Ha Ha0.
  apply (nmul_inverse_below (fermat 2)); auto.
  - apply closed_fermat_2.
  - assert (H : fermat 2 = 16) by (unfold fermat; cbn; lia); lia.
Qed.

(** * The trace image is the lower half *)

(** What remains for every level is that the first non-trace value is half the
    level. Below the level, the trace values are closed under the pairing, and
    the count already forces the mex no higher than half. *)
Lemma trace_val_lt :
  forall k x, closed_below (2 ^ k) -> x < 2 ^ k -> trace_val x < 2 ^ k.
Proof.
  intros k x Hcl Hx; unfold trace_val.
  apply nadd_lt_pow2; [apply Hcl; assumption | assumption].
Qed.

(** A value below the level is a trace value exactly when the equation
    [y * y + y = v] has a solution there. *)
Lemma trace_image_spec :
  forall k v,
    In v (trace_image k) <-> exists y, y < 2 ^ k /\ nadd (nmul y y) y = v.
Proof.
  intros k v; rewrite in_trace_image; unfold trace_val; reflexivity.
Qed.

(** How a trace value splits along a level. *)
Lemma trace_val_split :
  forall k q r,
    closed_below (2 ^ k) -> 0 < k ->
    mex (trace_image k) = 2 ^ k / 2 ->
    q < 2 ^ k -> r < 2 ^ k ->
    trace_val (nadd (2 ^ k * q) r)
    = nadd (2 ^ k * trace_val q)
           (nadd (nmul (2 ^ k / 2) (nmul q q)) (trace_val r)).
Proof.
  intros k q r Hcl Hk Hmex Hq Hr.
  assert (Hhalf : 2 ^ k / 2 < 2 ^ k)
    by (apply Nat.div_lt; [apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia | lia]).
  assert (Hlow : forall x, x < 2 ^ k -> nmul (2 ^ k) x = 2 ^ k * x)
    by (intros x Hx; apply nmul_fermat_low; auto; exists k; reflexivity).
  assert (Hqq : nmul q q < 2 ^ k) by (apply Hcl; assumption).
  unfold trace_val.
  rewrite nsq_add.
  assert (Hsq : nmul (2 ^ k * q) (2 ^ k * q)
                = nadd (2 ^ k * nmul q q) (nmul (2 ^ k / 2) (nmul q q))).
  { rewrite <- (Hlow q Hq).
    rewrite <- nmul_assoc, (nmul_comm (nmul (2 ^ k) q) (2 ^ k)).
    rewrite <- nmul_assoc, nmul_assoc.
    rewrite (nmul_fermat_square_half k Hcl Hk Hmex).
    assert (Hsplit : 2 ^ k + 2 ^ k / 2 = nadd (2 ^ k) (2 ^ k / 2)).
    { pose proof (nadd_mul_pow2 k 1 (2 ^ k / 2) Hhalf) as Hnc.
      rewrite Nat.mul_1_r in Hnc; lia. }
    rewrite Hsplit, nmul_comm, nmul_distr.
    rewrite (nmul_comm (nmul q q) (2 ^ k)), (Hlow (nmul q q) Hqq).
    rewrite (nmul_comm (nmul q q) (2 ^ k / 2)); reflexivity. }
  rewrite Hsq.
  assert (Hshift : nadd (2 ^ k * nmul q q) (2 ^ k * q)
                   = 2 ^ k * nadd (nmul q q) q)
    by (unfold nadd; rewrite mul_pow2_lxor; reflexivity).
  rewrite <- Hshift.
  xor_eq.
Qed.

(** So being in the lower half propagates to the next level. *)
Lemma half_trace_step :
  forall k,
    closed_below (2 ^ k) -> 0 < k ->
    mex (trace_image k) = 2 ^ k / 2 ->
    (forall x, x < 2 ^ k -> trace_val x < 2 ^ k / 2) ->
    forall x, x < 2 ^ (k + k) -> trace_val x < 2 ^ (k + k) / 2.
Proof.
  intros k Hcl Hk Hmex Hhalf x Hx.
  assert (Hpos : 0 < 2 ^ k) by (apply Nat.neq_0_lt_0, Nat.pow_nonzero; lia).
  assert (Heven : 2 ^ k = 2 * (2 ^ k / 2)).
  { assert (Hk1 : 2 ^ k = 2 * 2 ^ (k - 1)).
    { replace k with (S (k - 1)) at 1 by lia.
      rewrite Nat.pow_succ_r by lia; reflexivity. }
    rewrite Hk1, Nat.mul_comm, Nat.div_mul by lia; lia. }
  assert (Hhalfpos : 0 < 2 ^ k / 2) by lia.
  rewrite Nat.pow_add_r in Hx |- *.
  destruct (split_below_square k x Hx) as [q [r [Hq [Hr ->]]]].
  rewrite (trace_val_split k q r Hcl Hk Hmex Hq Hr).
  assert (Hqq : nmul q q < 2 ^ k) by (apply Hcl; assumption).
  assert (Hw : nadd (nmul (2 ^ k / 2) (nmul q q)) (trace_val r) < 2 ^ k).
  { apply nadd_lt_pow2.
    - apply Hcl; [lia | exact Hqq].
    - unfold trace_val; apply nadd_lt_pow2; [apply Hcl; assumption | assumption]. }
  rewrite (nadd_mul_pow2 k (trace_val q) _ Hw).
  assert (Htq : trace_val q < 2 ^ k / 2) by (apply Hhalf; exact Hq).
  assert (Hhalfsq : 2 ^ k * 2 ^ k / 2 = 2 ^ k * (2 ^ k / 2)).
  { set (h := 2 ^ k / 2).
    replace (2 ^ k * 2 ^ k) with ((2 ^ k * h) * 2) by lia.
    rewrite Nat.div_mul by lia; reflexivity. }
  rewrite Hhalfsq.
  assert (Hstep : 2 ^ k * trace_val q + 2 ^ k <= 2 ^ k * (2 ^ k / 2)).
  { replace (2 ^ k * trace_val q + 2 ^ k) with (2 ^ k * (trace_val q + 1)) by lia.
    apply Nat.mul_le_mono_l; lia. }
  lia.
Qed.

(** Half the level's worth of values, all in its lower half, is the lower half:
    so the first non-trace value is exactly half the level. *)
Lemma mex_trace_of_half :
  forall k,
    closed_below (2 ^ k) -> 0 < k ->
    (forall x, x < 2 ^ k -> trace_val x < 2 ^ k / 2) ->
    mex (trace_image k) = 2 ^ k / 2.
Proof.
  intros k Hcl Hk Hhalf.
  assert (Hlen : 2 * length (trace_image k) = 2 ^ k)
    by (apply trace_image_length; assumption).
  assert (Hincl : incl (trace_image k) (seq 0 (2 ^ k / 2))).
  { intros v Hv; apply in_trace_image in Hv; destruct Hv as [x [Hx <-]].
    apply in_seq; split; [lia | cbn [Nat.add]; apply Hhalf; exact Hx]. }
  assert (Hhalfval : 2 ^ k / 2 = length (trace_image k)).
  { assert (H2 : 2 ^ k = 2 * length (trace_image k)) by lia.
    rewrite H2, Nat.mul_comm, Nat.div_mul; lia. }
  assert (Hback : incl (seq 0 (2 ^ k / 2)) (trace_image k)).
  { apply NoDup_length_incl; [apply trace_image_nodup| |exact Hincl].
    rewrite length_seq; lia. }
  apply mex_unique.
  - intros H; apply Hincl, in_seq in H; lia.
  - intros y Hy; apply Hback, in_seq; lia.
Qed.

(** The chain of levels, each the square of the last. *)
Fixpoint chain (n : nat) : nat :=
  match n with
  | O => 1
  | S m => chain m + chain m
  end.

Lemma chain_pos : forall n, 0 < chain n.
Proof. induction n as [|n IH]; cbn [chain]; lia. Qed.

Lemma chain_fermat : forall n, 2 ^ chain n = fermat n.
Proof.
  intros n; unfold fermat; f_equal.
  induction n as [|n IH]; cbn [chain Nat.pow]; lia.
Qed.

(** Every level in the chain is closed and has its trace values in the lower
    half. *)
Theorem chain_closed_half :
  forall n,
    closed_below (2 ^ chain n) /\
    (forall x, x < 2 ^ chain n -> trace_val x < 2 ^ chain n / 2).
Proof.
  induction n as [|n IH].
  - cbn [chain]; split; [apply level_ok_1|].
    intros x Hx; cbn [Nat.pow] in Hx |- *.
    destruct x as [|[|x]]; try lia; unfold trace_val.
    + rewrite nmul_0_l, nadd_0_l; cbn; lia.
    + rewrite nmul_1_l, nadd_self; cbn; lia.
  - destruct IH as [Hcl Hhalf]; cbn [chain].
    pose proof (chain_pos n) as Hpos.
    assert (Hmex : mex (trace_image (chain n)) = 2 ^ chain n / 2)
      by (apply mex_trace_of_half; assumption).
    split.
    + apply closed_step; assumption.
    + apply half_trace_step; assumption.
Qed.

(** So every Fermat level is closed. *)
Theorem closed_fermat : forall n, closed_below (fermat n).
Proof.
  intros n; rewrite <- chain_fermat; apply (chain_closed_half n).
Qed.

(** * The field *)

(** Every nimber lies below some Fermat level. *)
Lemma below_some_fermat : forall a, exists n, a < fermat n.
Proof.
  intros a; exists a.
  unfold fermat.
  assert (Hlin : forall m, m < 2 ^ m).
  { induction m as [|m IH]; [cbn; lia|].
    rewrite Nat.pow_succ_r by lia; lia. }
  apply (Nat.lt_le_trans _ (2 ^ a)); [apply Hlin|].
  apply Nat.pow_le_mono_r; [lia | apply Nat.lt_le_incl, Hlin].
Qed.

(** So every nonzero nimber has a multiplicative inverse. *)
Theorem nmul_inverse :
  forall a, a <> 0 -> exists b, nmul a b = 1.
Proof.
  intros a Ha.
  destruct (below_some_fermat a) as [n Hn].
  destruct (nmul_inverse_below (fermat n) a (closed_fermat n)
              ltac:(pose proof (fermat_ge_2 n); lia) Hn Ha) as [b [_ Hb]].
  exists b; exact Hb.
Qed.

(** Nim multiplication is closed on every Fermat level, so the nimbers below
    one form a field: the ring laws hold everywhere, and inverses are found in
    the level itself. *)
Theorem fermat_field :
  forall n,
    (forall a b, a < fermat n -> b < fermat n -> nmul a b < fermat n) /\
    (forall a, a < fermat n -> a <> 0 ->
       exists b, b < fermat n /\ nmul a b = 1).
Proof.
  intros n; split.
  - apply closed_fermat.
  - intros a Ha Ha0.
    apply (nmul_inverse_below (fermat n)); auto.
    + apply closed_fermat.
    + pose proof (fermat_ge_2 n); lia.
Qed.
