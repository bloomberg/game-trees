(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** An optimality criterion for openings.

    [GameTrees.OpenerStrategy] names Allcock's strategy and checks it position
    by position, but proves nothing about when an opening is optimal. The
    engine of Allcock's Theorem 1.1 is the observation that an opening which
    leaves the terminal bonus alone, and leaves behind at least the handout it
    gives away, realises the controlled value and is therefore optimal.

    [open_optimal_of_step] is that criterion, and [open_loop_optimal_ge4] and
    [open_chain_optimal_ge2] are the two instances the case analysis of
    Theorem 1.1 rests on. The theorem itself is still not proved: its three
    named cases turn on comparing the shortest loop against the standard move
    when the criterion does not apply, and that comparison is not made here. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Lia.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.

Open Scope Z_scope.

(** * The criterion *)

(** An opening that leaves the bonus alone and leaves at least its own
    handout behind is worth the controlled value, and so no opening is
    better. *)
Theorem open_optimal_of_step :
  forall G p,
    wf G -> In p (selections G) ->
    tb (fst p :: snd p) = tb (snd p) ->
    Z.of_nat (hand (fst p)) <= cval (snd p) ->
    value (snd p) = cval (snd p) ->
    value_open p = cval G /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hp Htb Hh Hrec.
  assert (HNil : G <> []) by (intros ->; simpl in Hp; destruct Hp).
  assert (HG : value G = cval G)
    by (apply (value_step_eq G p); assumption).
  assert (Hop : value_open p = cval G).
  { unfold value_open; rewrite Hrec.
    rewrite (controller_keeps (fst p) (cval (snd p)) Hh).
    unfold keep_control.
    pose proof (selections_cval G p Hp) as Hcv.
    rewrite Htb in Hcv.
    unfold cval, weight in *; lia. }
  split; [exact Hop|].
  pose proof (proj1 (opener_optimal_iff G p HNil Hp)) as Hmin.
  intros q Hq; apply Hmin; [lia | exact Hq].
Qed.

(** The same criterion with the recursive value supplied by Berlekamp and
    Scott, so only the controlled value of the remainder has to be checked. *)
Corollary open_optimal_of_cval :
  forall G p,
    wf G -> In p (selections G) ->
    tb (fst p :: snd p) = tb (snd p) ->
    Z.of_nat (hand (fst p)) <= cval (snd p) ->
    2 <= cval (snd p) ->
    value_open p = cval G /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw Hp Htb Hh Hc2.
  apply (open_optimal_of_step G p Hw Hp Htb Hh).
  apply value_cval_ge2; [exact (proj2 (selections_wf G p Hw Hp)) | exact Hc2].
Qed.

(** * Opening a loop *)

(** A loop hands over four boxes, so the criterion asks the remainder to be
    worth four. This is the shape every loop-opening case of Theorem 1.1
    reduces to. *)
Theorem open_loop_optimal_ge4 :
  forall G l rest,
    wf G -> In (Loop l, rest) (selections G) ->
    tb (Loop l :: rest) = tb rest ->
    4 <= cval rest ->
    value_open (Loop l, rest) = cval G /\
    (forall q, In q (selections G) ->
       value_open (Loop l, rest) <= value_open q).
Proof.
  intros G l rest Hw Hp Htb Hc.
  apply (open_optimal_of_cval G (Loop l, rest) Hw Hp);
    cbn [fst snd hand]; [exact Htb | lia | lia].
Qed.

(** * Opening a chain *)

(** A chain hands over two, so a remainder worth two is enough. *)
Theorem open_chain_optimal_ge2 :
  forall G k rest,
    wf G -> In (Chain k, rest) (selections G) ->
    tb (Chain k :: rest) = tb rest ->
    2 <= cval rest ->
    value_open (Chain k, rest) = cval G /\
    (forall q, In q (selections G) ->
       value_open (Chain k, rest) <= value_open q).
Proof.
  intros G k rest Hw Hp Htb Hc.
  apply (open_optimal_of_cval G (Chain k, rest) Hw Hp);
    cbn [fst snd hand]; [exact Htb | lia | lia].
Qed.

(** * Where the criterion applies *)

(** With no three-chains anywhere, removing a loop never moves the bonus, so
    the criterion applies to every loop of such a position. *)
Theorem open_loop_optimal_no3 :
  forall G l rest,
    wf G -> In (Loop l, rest) (selections G) ->
    existsb is_3chain_b G = false ->
    rest <> [] ->
    4 <= cval rest ->
    value_open (Loop l, rest) = cval G /\
    (forall q, In q (selections G) ->
       value_open (Loop l, rest) <= value_open q).
Proof.
  intros G l rest Hw Hp H3 HrNil Hc.
  apply (open_loop_optimal_ge4 G l rest Hw Hp); [|exact Hc].
  apply tb_remove_loop_no3; [reflexivity | | exact HrNil].
  pose proof (selections_perm G (Loop l, rest) Hp) as Hperm;
    cbn [fst snd] in Hperm.
  rewrite (existsb_perm is_3chain_b _ _ Hperm); exact H3.
Qed.

(** * A case of Theorem 1.1 *)

(** A position of loops and three-chains keeps its terminal bonus when a
    four-loop is removed: it is eight if nothing but loops remain and six as
    soon as a three-chain is there, on both sides of the removal. *)
Lemma tb_remove_4loop_only34 :
  forall rest,
    existsb is_loop_b rest = true ->
    forallb (fun C => is_loop_b C || is_3chain_b C)%bool rest = true ->
    tb (Loop 4 :: rest) = tb rest.
Proof.
  intros rest HL Hall.
  assert (HrNil : rest <> [])
    by (destruct rest; [simpl in HL; discriminate | discriminate]).
  destruct (existsb is_3chain_b rest) eqn:E3.
  - rewrite (tb_six rest HL E3 Hall).
    apply tb_six.
    + simpl; reflexivity.
    + simpl; exact E3.
    + simpl; exact Hall.
  - assert (HallL : forallb is_loop_b rest = true).
    { rewrite forallb_forall; intros x Hx.
      rewrite forallb_forall in Hall; specialize (Hall x Hx).
      apply orb_true_iff in Hall; destruct Hall as [H | H]; [exact H|].
      exfalso.
      assert (Hbad : existsb is_3chain_b rest = true)
        by (apply existsb_exists; exists x; split; assumption).
      congruence. }
    rewrite (tb_all_loops rest HrNil HallL).
    apply tb_all_loops; [discriminate | simpl; exact HallL].
Qed.

(** Case (i) of Allcock's Theorem 1.1 when a four-loop is present: with a
    controlled value of two or more, opening the four-loop attains the value,
    so it is an optimal opening. *)
Theorem case_i_four_loop :
  forall rest,
    wf (Loop 4 :: rest) ->
    existsb is_loop_b rest = true ->
    forallb (fun C => is_loop_b C || is_3chain_b C)%bool rest = true ->
    2 <= cval (Loop 4 :: rest) ->
    value_open (Loop 4, rest) = cval (Loop 4 :: rest) /\
    (forall q, In q (selections (Loop 4 :: rest)) ->
       value_open (Loop 4, rest) <= value_open q).
Proof.
  intros rest Hw HL Hall Hc.
  assert (Hp : In (Loop 4, rest) (selections (Loop 4 :: rest)))
    by (simpl; left; reflexivity).
  assert (Htb : tb (Loop 4 :: rest) = tb rest)
    by (apply tb_remove_4loop_only34; assumption).
  apply (open_loop_optimal_ge4 (Loop 4 :: rest) 4 rest Hw Hp Htb).
  (* removing a four-loop raises the controlled value by four *)
  pose proof (selections_cval (Loop 4 :: rest) (Loop 4, rest) Hp) as Hcv;
    cbn [fst snd] in Hcv.
  rewrite Htb, weight_loop_len in Hcv.
  unfold cval in *; simpl Z.of_nat in Hcv; lia.
Qed.

(** * Case (i) in general *)

(** Loops of eight or more are large, so a heap of them weighs nothing
    against the controller. *)
Lemma allbig_loops_ge8 :
  forall L,
    forallb is_loop_b L = true ->
    (forall C, In C L -> (8 <= csize C)%nat) ->
    allbig L.
Proof.
  intros L HL Hmin; unfold allbig; rewrite Forall_forall; intros C HC.
  rewrite forallb_forall in HL; specialize (HL C HC).
  destruct C as [k | k]; [simpl in HL; discriminate|].
  unfold big; simpl hand; simpl csize.
  specialize (Hmin (Loop k) HC); simpl csize in Hmin; lia.
Qed.

(** A position of one three-chain over a nonempty heap of loops scores the
    six bonus, before and after a loop is taken out. *)
Lemma tb_three_over_loops :
  forall R,
    forallb is_loop_b R = true -> R <> [] ->
    tb (Chain 3 :: R) = 6.
Proof.
  intros R HR HNil; apply tb_six_of_loops_and_three; assumption.
Qed.

(** Case (i) of Allcock's Theorem 1.1. A three-chain over two or more loops
    with a controlled value of two or more: opening a shortest loop attains
    the value, so it is an optimal opening. *)
Theorem case_i :
  forall L l rest,
    wf (Chain 3 :: L) ->
    forallb is_loop_b L = true ->
    In (Loop l, rest) (selections L) ->
    (forall C, In C L -> (l <= csize C)%nat) ->
    (2 <= length L)%nat ->
    2 <= cval (Chain 3 :: L) ->
    value_open (Loop l, Chain 3 :: rest) = cval (Chain 3 :: L) /\
    (forall q, In q (selections (Chain 3 :: L)) ->
       value_open (Loop l, Chain 3 :: rest) <= value_open q).
Proof.
  intros L l rest Hw HL Hsel Hmin Hlen Hc.
  (* the opening is a selection of the whole position *)
  assert (Hp : In (Loop l, Chain 3 :: rest) (selections (Chain 3 :: L))).
  { simpl selections; right.
    apply (in_map (fun p => (fst p, Chain 3 :: snd p)) (selections L)
                  (Loop l, rest)); exact Hsel. }
  (* what is left of the loops *)
  pose proof (selections_perm L (Loop l, rest) Hsel) as Hperm;
    cbn [fst snd] in Hperm.
  assert (HLr : forallb is_loop_b rest = true).
  { rewrite forallb_forall in HL |- *; intros C HC; apply HL.
    eapply Permutation_in; [exact Hperm | right; exact HC]. }
  assert (Hlr : length rest = pred (length L)).
  { pose proof (selections_length L (Loop l, rest) Hsel) as H;
      cbn [snd] in H; lia. }
  assert (HrNil : rest <> [])
    by (destruct rest; simpl in Hlr; [lia | discriminate]).
  assert (Hminr : forall C, In C rest -> (l <= csize C)%nat).
  { intros C HC; apply Hmin.
    eapply Permutation_in; [exact Hperm | right; exact HC]. }
  (* the bonus is six on both sides of the opening *)
  assert (Htb1 : tb (Chain 3 :: rest) = 6)
    by (apply tb_three_over_loops; assumption).
  assert (Htb2 : tb (Loop l :: Chain 3 :: rest) = 6).
  { rewrite <- (tb_perm (Chain 3 :: Loop l :: rest)) by apply perm_swap.
    apply tb_six.
    - apply (proj2 (existsb_exists is_loop_b _)).
      exists (Loop l); split; [right; left; reflexivity | reflexivity].
    - apply (proj2 (existsb_exists is_3chain_b _)).
      exists (Chain 3); split; [left; reflexivity | reflexivity].
    - rewrite forallb_forall; intros x Hx.
      destruct Hx as [<- | [<- | Hx]]; [reflexivity | reflexivity |].
      rewrite forallb_forall in HLr; rewrite (HLr x Hx); reflexivity. }
  (* the controlled value of the remainder *)
  assert (Hcb : cbase L = (Z.of_nat l - 8) + cbase rest).
  { rewrite (selections_cbase L (Loop l, rest) Hsel); cbn [fst snd].
    rewrite weight_loop_len; reflexivity. }
  assert (HcG : cval (Chain 3 :: L) = 5 + cbase L).
  { unfold cval; rewrite cbase_cons, weight_chain; simpl csize.
    rewrite (tb_three_over_loops L HL);
      [lia | intros HH; rewrite HH in Hlen; simpl in Hlen; lia]. }
  assert (Hcr : cval (Chain 3 :: rest) = 5 + cbase rest).
  { unfold cval; rewrite cbase_cons, weight_chain, Htb1; simpl csize; lia. }
  assert (Hge4 : 4 <= cval (Chain 3 :: rest)).
  { destruct (Nat.le_gt_cases 8 l) as [Hbig | Hsmall].
    - (* every remaining loop is large, so the base weight is nonnegative *)
      assert (Hall8 : forall C, In C rest -> (8 <= csize C)%nat)
        by (intros C HC; pose proof (Hminr C HC); lia).
      pose proof (allbig_cbase rest (allbig_loops_ge8 rest HLr Hall8)); lia.
    - (* a short loop, which by evenness is a four-loop or a six-loop, and
         there the hypothesis on the whole position bites *)
      assert (HinL : In (Loop l) L).
      { pose proof (selections_In L (Loop l, rest) Hsel) as H;
          cbn [fst] in H; exact H. }
      assert (HwfL : wf_comp (Loop l)).
      { pose proof (wf_tail (Chain 3) L Hw) as HwL.
        unfold wf in HwL; rewrite Forall_forall in HwL; apply HwL; exact HinL. }
      destruct HwfL as [H4 Hev].
      apply Nat.even_spec in Hev; destruct Hev as [k Hk].
      assert (Hzl : Z.of_nat l <= 6) by lia.
      lia. }
  (* now the criterion applies *)
  apply (open_loop_optimal_ge4 (Chain 3 :: L) l (Chain 3 :: rest) Hw Hp);
    [| exact Hge4].
  rewrite Htb2, Htb1; reflexivity.
Qed.

(** * Optimality as a comparison of closed forms *)

(** What an opening is worth, read off the closed form of the remainder
    rather than off the recursion. *)
Theorem value_open_closed :
  forall G p,
    wf G -> In p (selections G) -> snd p <> [] ->
    value_open p = vopen (fst p) (v41 (snd p)).
Proof.
  intros G p Hw Hp HrNil; unfold value_open.
  rewrite (value_complete (snd p)); [reflexivity | | exact HrNil].
  exact (proj2 (selections_wf G p Hw Hp)).
Qed.

(** So an opening is optimal exactly when the two closed forms agree, and
    every case of Theorem 1.1 is an arithmetic comparison between [vopen] of
    one [v41] and another. *)
Theorem opening_optimal_closed_form :
  forall G p,
    wf G -> G <> [] -> In p (selections G) -> snd p <> [] ->
    (vopen (fst p) (v41 (snd p)) = v41 G <->
     forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hw HNil Hp HrNil.
  rewrite <- (value_open_closed G p Hw Hp HrNil).
  rewrite <- (value_complete G Hw HNil).
  split.
  - intros H; apply (proj1 (opener_optimal_iff G p HNil Hp)); symmetry; exact H.
  - intros H; symmetry.
    apply (proj2 (opener_optimal_iff G p HNil Hp)); exact H.
Qed.

(** The comparison as a decision procedure on a named opening. *)
Definition opening_optimal_b (G : position) (p : comp * position) : bool :=
  Z.eqb (vopen (fst p) (v41 (snd p))) (v41 G).

Theorem opening_optimal_b_sound :
  forall G p,
    wf G -> G <> [] -> In p (selections G) -> snd p <> [] ->
    opening_optimal_b G p = true ->
    forall q, In q (selections G) -> value_open p <= value_open q.
Proof.
  intros G p Hw HNil Hp HrNil Hb.
  apply (proj1 (opening_optimal_closed_form G p Hw HNil Hp HrNil)).
  apply Z.eqb_eq; exact Hb.
Qed.

(** And it is complete: an optimal opening passes the test. *)
Theorem opening_optimal_b_complete :
  forall G p,
    wf G -> G <> [] -> In p (selections G) -> snd p <> [] ->
    (forall q, In q (selections G) -> value_open p <= value_open q) ->
    opening_optimal_b G p = true.
Proof.
  intros G p Hw HNil Hp HrNil Hmin.
  apply Z.eqb_eq.
  apply (proj2 (opening_optimal_closed_form G p Hw HNil Hp HrNil)); exact Hmin.
Qed.

(** * The criterion is not vacuous *)

(** Two eight-loops: opening either is optimal and the position is worth its
    controlled value. *)
Example open_loop_two_eights :
  value_open (Loop 8, [Loop 8]) = cval [Loop 8; Loop 8].
Proof. vm_compute; reflexivity. Qed.

(** And the value agrees, so the opening really does attain it. *)
Example value_two_eights : value [Loop 8; Loop 8] = cval [Loop 8; Loop 8].
Proof. vm_compute; reflexivity. Qed.
