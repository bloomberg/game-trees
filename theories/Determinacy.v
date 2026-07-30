(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Zermelo determinacy for finite two-player games over an abstract state.
    A finished game is won by one of the two players or drawn, so forcing is
    stated against a set of acceptable outcomes: forcing a win and forcing a
    non-loss are the two instances that matter, and the three-way split
    between them is determinacy in the presence of draws. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.

Import ListNotations.

Require Import GameTrees.Helpers.

(** * Outcomes *)

(** A finished game is won by the player named by the flag, or drawn. *)
Inductive outcome : Type :=
| win : bool -> outcome
| drawn : outcome.

(** The outcomes [who] calls a win. *)
Definition goal_win (who : bool) (o : outcome) : bool :=
  match o with win w => Bool.eqb w who | drawn => false end.

(** The outcomes [who] calls a non-loss: a win or a draw. *)
Definition goal_nonloss (who : bool) (o : outcome) : bool :=
  match o with win w => Bool.eqb w who | drawn => true end.

(** Not losing is exactly failing to let the opponent win. *)
Lemma goal_nonloss_negb :
  forall who o, goal_nonloss who o = negb (goal_win (negb who) o).
Proof. intros [] [[]|]; reflexivity. Qed.

Lemma goal_win_nonloss :
  forall who o, goal_win who o = true -> goal_nonloss who o = true.
Proof. intros who [w|]; simpl; auto. Qed.

Lemma goal_win_disj :
  forall o, goal_win true o = true -> goal_win false o = false.
Proof. intros [[]|]; simpl; auto. Qed.

Lemma goal_win_nonloss_disj :
  forall who o, goal_win (negb who) o = true -> goal_nonloss who o = false.
Proof. intros [] [[]|]; simpl; auto. Qed.

Section Zermelo.
  Context {St M : Type}.
  Variable moves : St -> list M.
  Variable play : St -> M -> St.
  Variable amove : St -> bool.
  Variable outc : St -> option outcome.

  (** * Forcing an outcome into a set *)

  (** [forces_in goal who fuel s]: within [fuel] plies, and against any play by
     the opponent, [who] can drive the finished outcome into [goal]. *)
  Fixpoint forces_in (goal : outcome -> bool) (who : bool) (fuel : nat)
      (s : St) : Prop :=
    match fuel with
    | O => match outc s with Some o => goal o = true | None => False end
    | S f =>
      match outc s with
      | Some o => goal o = true
      | None =>
        if Bool.eqb (amove s) who
        then exists m, In m (moves s) /\ forces_in goal who f (play s m)
        else forall m, In m (moves s) -> forces_in goal who f (play s m)
      end
    end.

  Lemma forces_in_S_iff :
    forall goal who f s,
      forces_in goal who (S f) s <->
      match outc s with
      | Some o => goal o = true
      | None =>
        if Bool.eqb (amove s) who
        then exists m, In m (moves s) /\ forces_in goal who f (play s m)
        else forall m, In m (moves s) -> forces_in goal who f (play s m)
      end.
  Proof. intros; apply iff_refl. Qed.

  Lemma forces_in_0_iff :
    forall goal who s,
      forces_in goal who 0 s <->
      match outc s with Some o => goal o = true | None => False end.
  Proof. intros; apply iff_refl. Qed.

  Lemma forces_in_S :
    forall goal who fuel s,
      forces_in goal who fuel s -> forces_in goal who (S fuel) s.
  Proof.
    induction fuel as [|f IH]; intros s H.
    - apply (proj1 (forces_in_0_iff goal who s)) in H.
      apply (proj2 (forces_in_S_iff goal who 0 s)).
      destruct (outc s) as [o|]; [exact H | destruct H].
    - apply (proj1 (forces_in_S_iff goal who f s)) in H.
      apply (proj2 (forces_in_S_iff goal who (S f) s)).
      destruct (outc s) as [o|]; auto.
      destruct (Bool.eqb (amove s) who).
      + destruct H as [m [Hm Hwin]]; exists m; split; auto.
      + intros m Hm; auto.
  Qed.

  Lemma forces_in_le :
    forall goal who f f' s,
      f <= f' -> forces_in goal who f s -> forces_in goal who f' s.
  Proof.
    intros goal who f f' s Hle H.
    induction Hle; auto using forces_in_S.
  Qed.

  (** A wider goal is easier to force. *)
  Lemma forces_in_impl :
    forall g1 g2 who fuel s,
      (forall o, g1 o = true -> g2 o = true) ->
      forces_in g1 who fuel s -> forces_in g2 who fuel s.
  Proof.
    intros g1 g2 who fuel; induction fuel as [|f IH]; intros s Himpl H.
    - apply (proj1 (forces_in_0_iff g1 who s)) in H.
      apply (proj2 (forces_in_0_iff g2 who s)).
      destruct (outc s) as [o|]; auto.
    - apply (proj1 (forces_in_S_iff g1 who f s)) in H.
      apply (proj2 (forces_in_S_iff g2 who f s)).
      destruct (outc s) as [o|]; auto.
      destruct (Bool.eqb (amove s) who).
      + destruct H as [m [Hm Hw]]; exists m; split; auto.
      + intros m Hm; apply IH; auto.
  Qed.

  (** Goals that agree on the outcomes the game can actually reach are
     interchangeable. *)
  Lemma forces_in_ext :
    forall g1 g2 who fuel s,
      (forall t o, outc t = Some o -> g1 o = g2 o) ->
      forces_in g1 who fuel s -> forces_in g2 who fuel s.
  Proof.
    intros g1 g2 who fuel; induction fuel as [|f IH]; intros s Hag H.
    - apply (proj1 (forces_in_0_iff g1 who s)) in H.
      apply (proj2 (forces_in_0_iff g2 who s)).
      destruct (outc s) as [o|] eqn:E; auto.
      rewrite <- (Hag s o E); exact H.
    - apply (proj1 (forces_in_S_iff g1 who f s)) in H.
      apply (proj2 (forces_in_S_iff g2 who f s)).
      destruct (outc s) as [o|] eqn:E.
      + rewrite <- (Hag s o E); exact H.
      + destruct (Bool.eqb (amove s) who).
        * destruct H as [m [Hm Hw]]; exists m; split; auto.
        * intros m Hm; apply IH; auto.
  Qed.

  Lemma eqb_amove_negb :
    forall s who, Bool.eqb (amove s) (negb who) = negb (Bool.eqb (amove s) who).
  Proof. intros s who; destruct (amove s); destruct who; reflexivity. Qed.

  (** Opposing players cannot both force disjoint goals. *)
  Lemma forces_in_not_both :
    forall g1 g2 who fuel s,
      (forall o, g1 o = true -> g2 o = false) ->
      forces_in g1 who fuel s -> forces_in g2 (negb who) fuel s -> False.
  Proof.
    intros g1 g2 who fuel; induction fuel as [|f IH]; intros s Hdisj H1 H2.
    - apply (proj1 (forces_in_0_iff g1 who s)) in H1.
      apply (proj1 (forces_in_0_iff g2 (negb who) s)) in H2.
      destruct (outc s) as [o|]; [|destruct H1].
      rewrite (Hdisj o H1) in H2; discriminate.
    - apply (proj1 (forces_in_S_iff g1 who f s)) in H1.
      apply (proj1 (forces_in_S_iff g2 (negb who) f s)) in H2.
      destruct (outc s) as [o|].
      + rewrite (Hdisj o H1) in H2; discriminate.
      + rewrite eqb_amove_negb in H2.
        destruct (Bool.eqb (amove s) who); simpl in H1, H2.
        * destruct H1 as [m [Hm Hw]]; exact (IH _ Hdisj Hw (H2 m Hm)).
        * destruct H2 as [m [Hm Hw]]; exact (IH _ Hdisj (H1 m Hm) Hw).
  Qed.

  (** * Winning and not losing *)

  (** [forces who fuel s]: [who] wins within [fuel] plies against any play. *)
  Definition forces (who : bool) (fuel : nat) (s : St) : Prop :=
    forces_in (goal_win who) who fuel s.

  (** [nonloss who fuel s]: [who] avoids losing within [fuel] plies. *)
  Definition nonloss (who : bool) (fuel : nat) (s : St) : Prop :=
    forces_in (goal_nonloss who) who fuel s.

  Lemma forces_S_iff :
    forall who f s,
      forces who (S f) s <->
      match outc s with
      | Some o => goal_win who o = true
      | None =>
        if Bool.eqb (amove s) who
        then exists m, In m (moves s) /\ forces who f (play s m)
        else forall m, In m (moves s) -> forces who f (play s m)
      end.
  Proof. intros; apply forces_in_S_iff. Qed.

  Lemma forces_0_iff :
    forall who s,
      forces who 0 s <->
      match outc s with Some o => goal_win who o = true | None => False end.
  Proof. intros; apply forces_in_0_iff. Qed.

  Lemma forces_S : forall who fuel s, forces who fuel s -> forces who (S fuel) s.
  Proof. intros; apply forces_in_S; auto. Qed.

  Lemma forces_le :
    forall who f f' s, f <= f' -> forces who f s -> forces who f' s.
  Proof. intros who f f' s; apply forces_in_le. Qed.

  Lemma nonloss_S_iff :
    forall who f s,
      nonloss who (S f) s <->
      match outc s with
      | Some o => goal_nonloss who o = true
      | None =>
        if Bool.eqb (amove s) who
        then exists m, In m (moves s) /\ nonloss who f (play s m)
        else forall m, In m (moves s) -> nonloss who f (play s m)
      end.
  Proof. intros; apply forces_in_S_iff. Qed.

  Lemma nonloss_0_iff :
    forall who s,
      nonloss who 0 s <->
      match outc s with Some o => goal_nonloss who o = true | None => False end.
  Proof. intros; apply forces_in_0_iff. Qed.

  Lemma nonloss_S :
    forall who fuel s, nonloss who fuel s -> nonloss who (S fuel) s.
  Proof. intros; apply forces_in_S; auto. Qed.

  (** Winning is one way of not losing. *)
  Lemma forces_nonloss :
    forall who fuel s, forces who fuel s -> nonloss who fuel s.
  Proof.
    intros who fuel s; apply forces_in_impl; apply goal_win_nonloss.
  Qed.

  (** Both players winning is impossible. *)
  Lemma forces_not_both :
    forall fuel s, forces true fuel s -> forces false fuel s -> False.
  Proof.
    intros fuel s H1 H2.
    exact (forces_in_not_both _ _ true fuel s goal_win_disj H1 H2).
  Qed.

  (** One player winning and the other not losing is impossible. *)
  Lemma forces_not_nonloss :
    forall who fuel s,
      forces (negb who) fuel s -> nonloss who fuel s -> False.
  Proof.
    intros who fuel s H1 H2.
    apply (forces_in_not_both (goal_win (negb who)) (goal_nonloss who)
             (negb who) fuel s).
    - apply goal_win_nonloss_disj.
    - exact H1.
    - rewrite negb_involutive; exact H2.
  Qed.

  (** * Boolean decision procedures *)

  (** Short-circuiting Boolean move quantifiers. *)
  Fixpoint any_move (test : M -> bool) (l : list M) : bool :=
    match l with
    | [] => false
    | m :: rest => if test m then true else any_move test rest
    end.

  Fixpoint all_move (test : M -> bool) (l : list M) : bool :=
    match l with
    | [] => true
    | m :: rest => if test m then all_move test rest else false
    end.

  Lemma any_move_true_iff :
    forall test l,
      any_move test l = true <-> exists m, In m l /\ test m = true.
  Proof.
    intros test l; induction l as [|a l IH]; simpl.
    - split; [discriminate | intros [m [[] _]]].
    - destruct (test a) eqn:Ea.
      + split; [intros _; exists a; auto | auto].
      + rewrite IH; split.
        * intros [m [Hm Ht]]; exists m; auto.
        * intros [m [[-> | Hm] Ht]]; [congruence | exists m; auto].
  Qed.

  Lemma all_move_true_iff :
    forall test l,
      all_move test l = true <-> forall m, In m l -> test m = true.
  Proof.
    intros test l; induction l as [|a l IH]; simpl.
    - split; [intros _ m [] | auto].
    - destruct (test a) eqn:Ea.
      + rewrite IH; split.
        * intros H m [-> | Hm]; auto.
        * intros H m Hm; apply H; auto.
      + split; [discriminate |].
        intros H; rewrite (H a) in Ea; [discriminate | auto].
  Qed.

  (** Boolean decision procedure for the fueled forcing predicate. *)
  Fixpoint forces_in_b (goal : outcome -> bool) (who : bool) (fuel : nat)
      (s : St) : bool :=
    match fuel with
    | O => match outc s with Some o => goal o | None => false end
    | S f =>
      match outc s with
      | Some o => goal o
      | None =>
        if Bool.eqb (amove s) who
        then any_move (fun m => forces_in_b goal who f (play s m)) (moves s)
        else all_move (fun m => forces_in_b goal who f (play s m)) (moves s)
      end
    end.

  Lemma forces_in_b_correct :
    forall goal who fuel s,
      forces_in_b goal who fuel s = true <-> forces_in goal who fuel s.
  Proof.
    intros goal who; induction fuel as [|f IH]; intros s; simpl.
    - destruct (outc s) as [o|]; [apply iff_refl | split; [discriminate | intros []]].
    - destruct (outc s) as [o|]; [apply iff_refl|].
      destruct (Bool.eqb (amove s) who).
      + rewrite any_move_true_iff; split.
        * intros [m [Hm Ht]]; exists m; split; auto; apply IH; auto.
        * intros [m [Hm Hf]]; exists m; split; auto; apply IH; auto.
      + rewrite all_move_true_iff; split.
        * intros H m Hm; apply IH; auto.
        * intros H m Hm; apply IH; auto.
  Qed.

  Definition forces_b (who : bool) (fuel : nat) (s : St) : bool :=
    forces_in_b (goal_win who) who fuel s.

  Definition nonloss_b (who : bool) (fuel : nat) (s : St) : bool :=
    forces_in_b (goal_nonloss who) who fuel s.

  Lemma forces_b_correct :
    forall who fuel s, forces_b who fuel s = true <-> forces who fuel s.
  Proof. intros; apply forces_in_b_correct. Qed.

  Lemma nonloss_b_correct :
    forall who fuel s, nonloss_b who fuel s = true <-> nonloss who fuel s.
  Proof. intros; apply forces_in_b_correct. Qed.

  (** * Determinacy *)

  (** Hypotheses: invariant, decreasing measure, non-stalling. *)
  Variable inv : St -> Prop.
  Variable measure : St -> nat.

  Hypothesis inv_play :
    forall s m, inv s -> outc s = None -> In m (moves s) -> inv (play s m).
  Hypothesis measure_play :
    forall s m, inv s -> outc s = None -> In m (moves s) ->
    measure (play s m) < measure s.
  Hypothesis no_stall :
    forall s, inv s -> outc s = None -> exists m, In m (moves s).

  (** The general form: against any goal, either the player forces it or the
     opponent forces its complement. Everything else is an instance. *)
  Theorem zermelo_goal :
    forall goal who fuel s,
      inv s -> measure s <= fuel ->
      forces_in goal who fuel s \/
      forces_in (fun o => negb (goal o)) (negb who) fuel s.
  Proof.
    intros goal who fuel; induction fuel as [|f IH]; intros s Hinv Hfuel.
    - destruct (outc s) as [o|] eqn:E.
      + destruct (goal o) eqn:Eo.
        * left; apply (proj2 (forces_in_0_iff goal who s)); rewrite E; auto.
        * right; apply (proj2 (forces_in_0_iff _ (negb who) s)).
          rewrite E, Eo; reflexivity.
      + exfalso.
        destruct (no_stall s Hinv E) as [m Hm].
        pose proof (measure_play s m Hinv E Hm); lia.
    - destruct (outc s) as [o|] eqn:E.
      + destruct (goal o) eqn:Eo.
        * left; apply (proj2 (forces_in_S_iff goal who f s)); rewrite E; auto.
        * right; apply (proj2 (forces_in_S_iff _ (negb who) f s)).
          rewrite E, Eo; reflexivity.
      + assert (Hstep : forall m, In m (moves s) ->
          forces_in goal who f (play s m) \/
          forces_in (fun o => negb (goal o)) (negb who) f (play s m)).
        { intros m Hm.
          apply IH.
          - apply (inv_play s m); auto.
          - pose proof (measure_play s m Hinv E Hm); lia. }
        destruct (Bool.eqb (amove s) who) eqn:Ea.
        * destruct (split_exists_or_forall
                      (fun m => forces_in goal who f (play s m))
                      (fun m => forces_in (fun o => negb (goal o)) (negb who) f
                                  (play s m))
                      (moves s) Hstep) as [Hex | Hall].
          -- left; apply (proj2 (forces_in_S_iff goal who f s)).
             rewrite E, Ea; exact Hex.
          -- right; apply (proj2 (forces_in_S_iff _ (negb who) f s)).
             rewrite E, eqb_amove_negb, Ea; simpl; exact Hall.
        * destruct (split_exists_or_forall
                      (fun m => forces_in (fun o => negb (goal o)) (negb who) f
                                  (play s m))
                      (fun m => forces_in goal who f (play s m))
                      (moves s)) as [Hex | Hall].
          -- intros m Hm; destruct (Hstep m Hm); auto.
          -- right; apply (proj2 (forces_in_S_iff _ (negb who) f s)).
             rewrite E, eqb_amove_negb, Ea; simpl; exact Hex.
          -- left; apply (proj2 (forces_in_S_iff goal who f s)).
             rewrite E, Ea; exact Hall.
  Qed.

  (** The three-way split: one side wins, or both sides hold a draw. *)
  Theorem zermelo_three_way :
    forall fuel s,
      inv s -> measure s <= fuel ->
      forces true fuel s \/ forces false fuel s \/
      (nonloss true fuel s /\ nonloss false fuel s).
  Proof.
    intros fuel s Hinv Hfuel.
    destruct (zermelo_goal (goal_win true) true fuel s Hinv Hfuel)
      as [Ht | Hnf]; [left; exact Ht|].
    destruct (zermelo_goal (goal_win false) false fuel s Hinv Hfuel)
      as [Hf | Hnt]; [right; left; exact Hf|].
    right; right; split.
    - unfold nonloss.
      apply (forces_in_ext (fun o => negb (goal_win false o))
               (goal_nonloss true) true fuel s).
      + intros t o _; rewrite (goal_nonloss_negb true o); reflexivity.
      + exact Hnt.
    - unfold nonloss.
      apply (forces_in_ext (fun o => negb (goal_win true o))
               (goal_nonloss false) false fuel s).
      + intros t o _; rewrite (goal_nonloss_negb false o); reflexivity.
      + exact Hnf.
  Qed.

  (** Draw-free games are decided outright: this is the classical statement. *)
  Theorem zermelo :
    forall fuel s,
      (forall t, outc t <> Some drawn) ->
      inv s -> measure s <= fuel ->
      forces true fuel s \/ forces false fuel s.
  Proof.
    intros fuel s Hnd Hinv Hfuel.
    destruct (zermelo_goal (goal_win true) true fuel s Hinv Hfuel)
      as [Ht | Hnf]; [left; exact Ht|].
    right.
    apply (forces_in_ext (fun o => negb (goal_win true o))
             (goal_win false) false fuel s).
    - intros t o Ho.
      destruct o as [w|]; [destruct w; reflexivity|].
      exfalso; exact (Hnd t Ho).
    - exact Hnf.
  Qed.
End Zermelo.
