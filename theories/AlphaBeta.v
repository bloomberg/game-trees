(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(* Verified shallow alpha-beta pruning for generalized multi-player game trees.
   Only shallow pruning (one level: parent -> child) is valid for >2 players;
   deep pruning provably fails (Korf 1991). *)

Require Import Corelib.Classes.RelationClasses.
Require Import Corelib.Relations.Relation_Definitions.
From Stdlib Require Import Streams.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import PeanoNat.

Require Import ExtLib.Core.RelDec.

Require Import GameTrees.Helpers.
Require Import GameTrees.Trees.
Require Import GameTrees.Eval.

Import ListNotations.
Import SigTNotations.

(* ---------- max2 algebra ---------- *)

Lemma max2_below :
  forall {A : Type} (R : relation A)
         (D : RelDec R) (DC : @RelDec_Correct A R D)
         (Rf : Reflexive R) (Tr : Transitive R)
         (SC : StronglyConnected R) (AS : Antisymmetric A eq R)
         (a b : A),
    R b a -> max2 R a b = a.
Proof.
  intros. unfold max2.
  destruct (a ?[ R ] b) eqn:E.
  - apply rel_dec_correct in E. apply AS; auto.
  - auto.
Qed.

Lemma max2_R_l :
  forall {A : Type} (R : relation A)
         (D : RelDec R) (DC : @RelDec_Correct A R D)
         (Rf : Reflexive R) (SC : StronglyConnected R)
         (a b : A),
    R a (max2 R a b).
Proof.
  intros. unfold max2.
  destruct (a ?[ R ] b) eqn:E.
  - apply rel_dec_correct in E. exact E.
  - apply Rf.
Qed.

(* ---------- Reference minimax ---------- *)

(* Computes the minimax score, matching eval_tree semantics. *)
Fixpoint eval_val
         {G S : Type}
         (ps : players S)
         (score : G -> S)
         (t : tree G) : S :=
  match ps with
  | Cons (R; D) ps' =>
    match t with
    | node g f =>
      match map (eval_val ps' score) f with
      | [] => score g
      | v :: vs => fold_left (fun acc y => max2 R acc y) vs v
      end
    end
  end.

(* ---------- fold_left / map bridge ---------- *)

Lemma fold_left_map :
  forall {A B C : Type} (f : A -> C -> A) (g : B -> C) (l : list B) (a : A),
    fold_left f (map g l) a = fold_left (fun acc x => f acc (g x)) l a.
Proof.
  intros A B C f g l. induction l as [|x xs IH]; simpl; intros; auto.
Qed.

Lemma eval_val_node_cons :
  forall {G S : Type}
         (R : relation S) (D : RelDec R)
         (ps' : players S) (score : G -> S)
         (g : G) (c : tree G) (cs : list (tree G)),
  eval_val (Cons (R; D) ps') score (node g (c :: cs))
  = fold_left (fun acc c' => max2 R acc (eval_val ps' score c'))
              cs (eval_val ps' score c).
Proof.
  intros. simpl.
  rewrite fold_left_map. auto.
Qed.

(* ---------- Pruned evaluation ---------- *)

Fixpoint eval_ab
         {G S : Type}
         (ps : players S)
         (score : G -> S)
         (cutoff : S -> bool)
         (t : tree G) : S :=
  match ps with
  | Cons (R; D) ps' =>
    match t with
    | node g f =>
      match f with
      | [] => score g
      | c :: cs =>
        (fix go (best : S) (remaining : list (tree G)) : S :=
           match remaining with
           | [] => best
           | c' :: remaining' =>
             if cutoff best then best
             else
               let v := eval_ab ps' score
                          (fun s => @rel_dec _ _ D s best) c' in
               go (max2 R best v) remaining'
           end) (eval_ab ps' score (fun _ => false) c) cs
      end
    end
  end.

(* ---------- Strong player operations ---------- *)

Definition player_ops_strong {S : Type} (ps : players S) :=
  Each (fun '(R; D) =>
    @RelDec_Correct S R D /\
    Reflexive R /\ Transitive R /\
    StronglyConnected R /\ Antisymmetric S eq R) ps.

(* ---------- Adversarial condition ---------- *)

CoInductive adversarial_players {S : Type} : players S -> Prop :=
| adversarial_cons :
    forall (p : {R : relation S & RelDec R}) (ps : players S),
      (forall x y, (Streams.hd ps).1 x y -> p.1 y x) ->
      adversarial_players ps ->
      adversarial_players (Cons p ps).

(* ---------- Coinductive projections ---------- *)

Definition Each_hd {A : Type} {P : A -> Prop} {a : A} {s : Stream A}
  (H : Each P (Cons a s)) : P a :=
  match H with EachCons _ _ _ pa _ => pa end.

Definition Each_tl {A : Type} {P : A -> Prop} {a : A} {s : Stream A}
  (H : Each P (Cons a s)) : Each P s :=
  match H with EachCons _ _ _ _ rest => rest end.

Definition adversarial_hd {S : Type} {p : {R : relation S & RelDec R}} {ps : players S}
  (H : adversarial_players (Cons p ps)) : forall x y, (Streams.hd ps).1 x y -> p.1 y x :=
  match H with adversarial_cons _ _ pf _ => pf end.

Definition adversarial_tl {S : Type} {p : {R : relation S & RelDec R}} {ps : players S}
  (H : adversarial_players (Cons p ps)) : adversarial_players ps :=
  match H with adversarial_cons _ _ _ rest => rest end.

(* ---------- Fishburn property ---------- *)

Definition fishburn {S : Type} (cut : S -> bool) (v v' : S) : Prop :=
  (cut v = false -> v' = v) /\
  (cut v = true -> cut v' = true).

Lemma fishburn_refl :
  forall {S : Type} (cut : S -> bool) (v : S),
    fishburn cut v v.
Proof. unfold fishburn; auto. Qed.

Lemma fishburn_false :
  forall {S : Type} (v v' : S),
    fishburn (fun _ => false) v v' -> v' = v.
Proof.
  intros S v v' [H _]. apply H. auto.
Qed.

(* A cutoff is R-monotone: if R x y and cut x = true, then cut y = true. *)
Definition cutoff_monotone {S : Type} (R : relation S) (cut : S -> bool) : Prop :=
  forall x y, R x y -> cut x = true -> cut y = true.

Definition player_rel {S : Type} (ps : players S) : relation S :=
  (Streams.hd ps).1.

(* ---------- fold_left monotonicity ---------- *)

Lemma fold_left_max2_R :
  forall {A : Type} (R : relation A)
         (D : RelDec R) (DC : @RelDec_Correct A R D)
         (Rf : Reflexive R) (Tr : Transitive R)
         (SC : StronglyConnected R)
         (init : A) (l : list A),
    R init (fold_left (fun acc y => max2 R acc y) l init).
Proof.
  intros A R D DC Rf Tr SC init l.
  revert init.
  induction l as [|x xs IH]; simpl; intros; auto.
  eapply Tr.
  apply (max2_R_l R D DC Rf SC init x).
  apply IH.
Qed.

Lemma fold_left_max2_children_R :
  forall {G S : Type} (R : relation S)
         (D : RelDec R) (DC : @RelDec_Correct S R D)
         (Rf : Reflexive R) (Tr : Transitive R)
         (SC : StronglyConnected R)
         (ps' : players S) (score : G -> S)
         (init : S) (cs : list (tree G)),
    R init (fold_left (fun acc c' => max2 R acc (eval_val ps' score c')) cs init).
Proof.
  intros. revert init.
  induction cs as [|c cs' IH]; simpl; intros; auto.
  eapply Tr.
  apply (max2_R_l R D DC Rf SC init (eval_val ps' score c)).
  apply IH.
Qed.

(* ---------- Main theorem ---------- *)

Theorem eval_ab_fishburn :
  forall {G S : Type}
         (score : G -> S)
         (t : tree G)
         (ps : players S)
         (cutoff : S -> bool),
    player_ops_strong ps ->
    adversarial_players ps ->
    cutoff_monotone (player_rel ps) cutoff ->
    fishburn cutoff (eval_val ps score t) (eval_ab ps score cutoff t).
Proof.
  intros G S score t.
  refine (tree_forall_ind G
    (fun t => forall (ps : players S) (cutoff : S -> bool),
      player_ops_strong ps ->
      adversarial_players ps ->
      cutoff_monotone (player_rel ps) cutoff ->
      fishburn cutoff (eval_val ps score t) (eval_ab ps score cutoff t))
    _ t).
  intros g f IH ps cutoff Hps Hadv Hmon.
  destruct ps as [[R D] [[R2 D2] ps'']].
  unfold player_rel in Hmon. simpl in Hmon.
  set (ps' := Cons (R2; D2) ps'') in *.
  pose proof (Each_hd Hps) as Hcur.
  pose proof (Each_tl Hps) as Hps'.
  simpl in Hcur.
  destruct Hcur as [DC [Rf [Tr [SC AS]]]].
  pose proof (adversarial_hd Hadv) as Hadv_rel.
  pose proof (adversarial_tl Hadv) as Hadv_rest.
  simpl in Hadv_rel.
  destruct f as [|c cs].
  - (* Leaf *)
    simpl. apply fishburn_refl.
  - (* Internal node *)
    rewrite (eval_val_node_cons R D ps' score g c cs).
    simpl.
    (* First child is evaluated exactly *)
    inv IH.
    assert (Hfirst : eval_ab ps' score (fun _ => false) c = eval_val ps' score c).
    { apply fishburn_false.
      apply H1.
      - exact Hps'.
      - exact Hadv_rest.
      - unfold cutoff_monotone. intros. discriminate. }
    rewrite Hfirst.
    (* Inner loop by list induction on cs *)
    clear Hfirst g.
    rename H2 into IHcs_all. clear H1.
    generalize (eval_val ps' score c) as init.
    induction cs as [|c' cs' IHlist]; simpl; intros.
    + apply fishburn_refl.
    + destruct (cutoff init) eqn:Ecut.
      * (* Cutoff fires *)
        split; intros.
        -- (* fold_left increases init, monotonicity gives contradiction *)
           assert (Hge : R init (fold_left (fun acc c0 => max2 R acc (eval_val ps' score c0))
                    (c' :: cs') init)).
           { apply (fold_left_max2_children_R R D DC Rf Tr SC ps' score init (c' :: cs')). }
           pose proof (Hmon _ _ Hge Ecut) as Hcut'.
           simpl in Hcut'. rewrite H in Hcut'. discriminate.
        -- exact Ecut.
      * (* Cutoff doesn't fire *)
        inv IHcs_all.
        (* Child's fishburn *)
        assert (Hchild : fishburn (fun s => @rel_dec _ _ D s init)
                  (eval_val ps' score c')
                  (eval_ab ps' score (fun s => @rel_dec _ _ D s init) c')).
        { apply H1.
          - exact Hps'.
          - exact Hadv_rest.
          - subst ps'.
            unfold cutoff_monotone, player_rel. simpl.
            intros x y HR2 Hcut.
            apply rel_dec_correct in Hcut.
            apply rel_dec_correct.
            eapply Tr; [ apply Hadv_rel; exact HR2 | exact Hcut ]. }
        destruct Hchild as [Hexact Hpruned].
        cbv beta in Hexact, Hpruned.
        destruct ((eval_val ps' score c') ?[ R ] init) eqn:Echild;
          [ (* Child value R-below init: max2 gives init *)
            apply rel_dec_correct in Echild;
            specialize (Hpruned eq_refl); simpl in Hpruned;
            apply rel_dec_correct in Hpruned;
            rewrite (max2_below R D DC Rf Tr SC AS init
              (eval_ab ps' score (fun s => s ?[ R ] init) c')); auto;
            rewrite (max2_below R D DC Rf Tr SC AS init
              (eval_val ps' score c')); auto
          | (* Child value not R-below init: child is exact *)
            specialize (Hexact eq_refl);
            rewrite Hexact ];
          apply IHlist; auto.
Qed.

Theorem eval_ab_correct :
  forall {G S : Type} (score : G -> S)
         (t : tree G) (ps : players S),
    player_ops_strong ps ->
    adversarial_players ps ->
    eval_ab ps score (fun _ => false) t = eval_val ps score t.
Proof.
  intros G S score t ps Hps Hadv.
  apply fishburn_false.
  apply eval_ab_fishburn; auto.
  unfold cutoff_monotone. intros. discriminate.
Qed.

(* ---------- Nat instances ---------- *)

#[export] Instance RelDec_nat_le : @RelDec nat Nat.le.
Proof. constructor. exact Nat.leb. Defined.

#[export] Instance RelDec_Correct_nat_le : @RelDec_Correct nat Nat.le RelDec_nat_le.
Proof.
  constructor. intros x y. simpl. split; apply Nat.leb_le.
Qed.

#[export] Instance RelDec_nat_ge : @RelDec nat (fun x y => Nat.le y x).
Proof. constructor. intros a b. exact (Nat.leb b a). Defined.

#[export] Instance RelDec_Correct_nat_ge :
  @RelDec_Correct nat (fun x y => Nat.le y x) RelDec_nat_ge.
Proof.
  constructor. intros x y. simpl. split; apply Nat.leb_le.
Qed.

Definition players_le_ge : players nat :=
  two_players Nat.le (fun x y => Nat.le y x).

Lemma players_le_ge_strong : player_ops_strong players_le_ge.
Proof.
  cofix H.
  unfold player_ops_strong, players_le_ge.
  rewrite (Streams.unfold_Stream (two_players Nat.le (fun x y => Nat.le y x))).
  constructor.
  - split; [ exact RelDec_Correct_nat_le |].
    split; [ intro x; apply Nat.le_refl |].
    split; [ intros x y z; apply Nat.le_trans |].
    split.
    + intros a b. destruct (Nat.le_gt_cases a b).
      * left; auto.
      * right. apply Nat.lt_le_incl. auto.
    + intros x y. apply Nat.le_antisymm.
  - constructor.
    + split; [ exact RelDec_Correct_nat_ge |].
      split; [ intro x; apply Nat.le_refl |].
      split; [ intros x y z Hyx Hzy; eapply Nat.le_trans; eauto |].
      split.
      * intros a b. destruct (Nat.le_gt_cases b a).
        -- left; auto.
        -- right. apply Nat.lt_le_incl. auto.
      * intros x y H1 H2. apply Nat.le_antisymm; auto.
    + exact H.
Qed.

Lemma players_le_ge_adversarial : adversarial_players players_le_ge.
Proof.
  cofix H.
  unfold players_le_ge.
  rewrite (Streams.unfold_Stream (two_players Nat.le (fun x y => Nat.le y x))).
  constructor.
  - simpl. intros x y. auto.
  - constructor.
    + simpl. intros x y. auto.
    + exact H.
Qed.

Definition eval_val_2p (sc : nat -> nat) (t : tree nat) : nat :=
  eval_val players_le_ge sc t.

Definition eval_ab_2p (sc : nat -> nat) (t : tree nat) : nat :=
  eval_ab players_le_ge sc (fun _ => false) t.

(* Smoke test *)
Definition example_tree : tree nat :=
  node 0 [node 0 [node 3 []; node 5 []];
          node 0 [node 6 []; node 9 []; node 2 []];
          node 0 [node 1 []]].

(* MAX picks max of children evaluated by MIN.
   MIN subtree 1: min(3,5) = 3
   MIN subtree 2: min(6,9,2) = 2
   MIN subtree 3: min(1) = 1
   MAX picks max(3,2,1) = 3 *)
Eval compute in eval_val_2p id example_tree.
Eval compute in eval_ab_2p id example_tree.
