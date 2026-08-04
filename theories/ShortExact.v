(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Where the capped control bound is exact.

    [ShortStrong.scval2_le_svalue] bounds the capped value below by the capped
    controlled value. Berlekamp and Scott prove the two agree once the
    controlled value reaches two, and [DotsAndBoxes.value_cval_ge2] is that
    theorem for wellformed positions.

    [svalue_step_eq] is the step the agreement rests on: an opening that leaves
    the terminal bonus alone, and leaves behind at least the handout it gives
    away, realises the controlled value exactly. [svalue_cval_ge2_wf] transfers
    Berlekamp and Scott through [ShortBonus.scval2_eq_cval], so only positions
    holding a chain of one or two boxes remain. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Sorting.Permutation.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.ShortControl.
Require Import GameTrees.ShortPairs.
Require Import GameTrees.ShortBonus.
Require Import GameTrees.ShortSmall.
Require Import GameTrees.ShortStrong.

Import ListNotations.

Open Scope Z_scope.

(** * Declining is the controller's choice once the rest is worth the handout *)

Lemma svopen_decline :
  forall C w, Z.of_nat (shand C) <= w -> svopen C w = sweight C + w.
Proof.
  intros C w H; unfold svopen, sweight.
  rewrite Z.max_r by lia; lia.
Qed.

Lemma svopen_take :
  forall C w, w <= Z.of_nat (shand C) -> svopen C w = Z.of_nat (csize C) - w.
Proof.
  intros C w H; unfold svopen.
  rewrite Z.max_l by lia; lia.
Qed.

(** * The step *)

(** An opening that leaves the bonus alone and leaves at least its own handout
    behind realises the capped controlled value. *)
Theorem svalue_step_eq :
  forall G p,
    swf G -> In p (selections G) ->
    stb (fst p :: snd p) = stb (snd p) ->
    Z.of_nat (shand (fst p)) <= scval2 (snd p) ->
    svalue (snd p) = scval2 (snd p) ->
    svalue G = scval2 G.
Proof.
  intros G p Hw Hp Htb Hh Hrec.
  assert (HNil : G <> []) by (intros ->; simpl in Hp; destruct Hp).
  assert (Hperm : Permutation (fst p :: snd p) G)
    by (apply selections_perm; exact Hp).
  apply Z.le_antisymm.
  - (* the named opening is no better than the controlled value *)
    eapply Z.le_trans; [apply (svalue_le_open G p Hp)|].
    unfold svalue_open; rewrite Hrec, (svopen_decline (fst p) _ Hh).
    rewrite <- (scval2_perm _ _ Hperm).
    unfold scval2; cbn [scbase]; lia.
  - apply scval2_le_svalue; [exact Hw | exact HNil].
Qed.

(** The same step with the recursive value supplied by the bound rather than
    assumed, which is how it is used once the threshold is met. *)
Corollary svalue_step_of_ge2 :
  forall G p,
    swf G -> In p (selections G) ->
    stb (fst p :: snd p) = stb (snd p) ->
    Z.of_nat (shand (fst p)) <= scval2 (snd p) ->
    2 <= scval2 (snd p) ->
    svalue (snd p) = scval2 (snd p) ->
    svalue G = scval2 G.
Proof.
  intros G p Hw Hp Htb Hh _ Hrec.
  exact (svalue_step_eq G p Hw Hp Htb Hh Hrec).
Qed.

(** * Berlekamp and Scott, transferred *)

(** On wellformed positions the capped theory is the original one, so the
    agreement above two comes across unchanged. *)
Theorem svalue_scval2_ge2_wf :
  forall G, wf G -> G <> [] -> 2 <= scval2 G -> svalue G = scval2 G.
Proof.
  intros G Hw HNil H2.
  rewrite (svalue_wf G Hw), (scval2_eq_cval G Hw HNil).
  rewrite (scval2_eq_cval G Hw HNil) in H2.
  apply value_cval_ge2; [exact Hw | exact H2].
Qed.

(** * Short chains are never large *)

(** A chain of one or two boxes never repays twice its handout, so it is never
    a large component. *)
Lemma shortb_not_big : forall C, shortb C = true -> ~ big C.
Proof.
  intros [n | n] H; [|discriminate].
  pose proof (shortb_chain n H) as Hb.
  unfold big, hand; cbn [csize]; lia.
Qed.

(** A short chain leaves the cap alone, being neither a long chain nor a
    three-chain. *)
Lemma cap_cons_short :
  forall C G, shortb C = true -> cap (C :: G) = cap G.
Proof.
  intros C G H; unfold cap; simpl.
  assert (Hl : longchain_b C = false).
  { destruct C as [n | n]; [|reflexivity].
    pose proof (shortb_chain n H) as Hb.
    unfold longchain_b; apply Nat.leb_gt; lia. }
  assert (H3 : is_3chain_b C = false).
  { destruct C as [n | n]; [|reflexivity].
    pose proof (shortb_chain n H) as Hb.
    destruct n as [|[|[|n]]]; cbn; try reflexivity; lia. }
  rewrite Hl, H3; simpl; reflexivity.
Qed.

(** And its handout is at most four, so it can only raise the largest handout
    from that of a one-box heap. *)
Lemma shand_short_le2 : forall C, shortb C = true -> (shand C <= 2)%nat.
Proof.
  intros [n | n] H; [|discriminate].
  pose proof (shortb_chain n H) as Hb.
  unfold shand, hand; cbn [csize]; lia.
Qed.

(** So opening a short chain leaves the bonus alone whenever what remains
    already holds a handout as large. *)
Theorem stb_cons_short :
  forall C rest,
    shortb C = true ->
    2 * Z.of_nat (shand C) <= maxsh rest ->
    stb (C :: rest) = stb rest.
Proof.
  intros C rest Hs Hm.
  unfold stb; rewrite maxsh_cons, (cap_cons_short C rest Hs).
  rewrite Z.max_r by exact Hm; reflexivity.
Qed.

(** * Every position is wellformed or holds a short chain *)

(** Wellformedness and its relaxation differ only on chains, so a position the
    relaxation admits and [shortb] misses is wellformed outright. *)
Lemma swf_no_short_wf :
  forall G, swf G -> existsb shortb G = false -> wf G.
Proof.
  induction G as [|C G IH]; intros Hw Hs; [constructor|].
  simpl in Hs; apply orb_false_iff in Hs; destruct Hs as [HC HG].
  inversion Hw as [|D E HwC HwG Heq]; subst.
  constructor; [| apply IH; assumption].
  destruct C as [k | k]; [| exact HwC].
  cbn [swf_comp] in HwC; cbn [wf_comp].
  unfold shortb in HC; apply andb_false_iff in HC.
  destruct HC as [H | H]; apply Nat.leb_gt in H; lia.
Qed.

(** * Handouts, and where the largest of them sits *)

Lemma maxsh_ge_of_In :
  forall C G, In C G -> 2 * Z.of_nat (shand C) <= maxsh G.
Proof.
  intros C G; induction G as [|D G IH]; intros HC; [destruct HC|].
  rewrite maxsh_cons; destruct HC as [<- | HC].
  - apply Z.le_max_l.
  - eapply Z.le_trans; [apply IH; exact HC | apply Z.le_max_r].
Qed.

Lemma shand_swf_ge1 : forall C, swf_comp C -> (1 <= shand C)%nat.
Proof.
  intros [n | n] H; cbn [swf_comp] in H.
  - unfold shand, hand; cbn [csize]; lia.
  - destruct H as [H4 _]; unfold shand, hand; cbn [csize]; lia.
Qed.

Lemma selection_rest_In :
  forall G C rest D, In (C, rest) (selections G) -> In D rest -> In D G.
Proof.
  intros G C rest D Hsel HD.
  pose proof (selections_perm G (C, rest) Hsel) as Hp; simpl in Hp.
  apply (Permutation_in _ Hp); simpl; right; exact HD.
Qed.

Lemma swf_of_selection :
  forall G C rest, swf G -> In (C, rest) (selections G) -> swf (C :: rest).
Proof.
  intros G C rest Hw Hsel.
  pose proof (selections_perm G (C, rest) Hsel) as Hp; simpl in Hp.
  unfold swf in Hw |- *; rewrite Forall_forall; intros D HD.
  rewrite Forall_forall in Hw; apply Hw; apply (Permutation_in _ Hp HD).
Qed.

(** * A single component is always exact *)

(** Twice a component's handout never exceeds the cap it sets on its own: a
    chain's is at most four, which is the floor of the cap, and a loop's is
    eight, which is the cap a lone loop leaves. *)
Lemma shand2_le_cap_single :
  forall C, swf_comp C -> 2 * Z.of_nat (shand C) <= cap [C].
Proof.
  intros [n | n] H.
  - pose proof (cap_range [Chain n]) as Hr.
    unfold shand, hand; cbn [csize]; lia.
  - cbn [swf_comp] in H; destruct H as [H4 _].
    assert (Hc : cap [Loop n] = 8) by reflexivity.
    rewrite Hc; unfold shand, hand; cbn [csize]; lia.
Qed.

Lemma stb_single :
  forall C, swf_comp C -> stb [C] = 2 * Z.of_nat (shand C).
Proof.
  intros C H; unfold stb; rewrite maxsh_cons, maxsh_nil.
  rewrite Z.max_l by lia.
  apply Z.min_l, shand2_le_cap_single; exact H.
Qed.

Lemma svalue_single_scval2 :
  forall C, swf_comp C -> svalue [C] = scval2 [C].
Proof.
  intros C H; rewrite svalue_single_c; unfold scval2; cbn [scbase].
  rewrite (stb_single C H); unfold sweight; lia.
Qed.

(** * Choosing which short chain to open *)

Definition chain1b (C : comp) : bool :=
  match C with Chain 1 => true | _ => false end.

Lemma chain1b_shortb : forall C, chain1b C = true -> shortb C = true.
Proof. intros [[|[|n]] | n] H; try discriminate; reflexivity. Qed.

Lemma shand_chain1b : forall C, chain1b C = true -> shand C = 1%nat.
Proof. intros [[|[|n]] | n] H; try discriminate; reflexivity. Qed.

Lemma shand_ge2_of_not_chain1 :
  forall C, swf_comp C -> chain1b C = false -> (2 <= shand C)%nat.
Proof.
  intros [n | n] Hw Hc; cbn [swf_comp] in Hw.
  - destruct n as [|[|n]]; [lia | discriminate |].
    unfold shand, hand; cbn [csize]; lia.
  - destruct Hw as [H4 _]; unfold shand, hand; cbn [csize]; lia.
Qed.

Lemma shand_short_not1 :
  forall C, shortb C = true -> chain1b C = false -> shand C = 2%nat.
Proof.
  intros [n | n] Hs Hc; [|discriminate].
  pose proof (shortb_chain n Hs) as Hb.
  destruct n as [|[|n]]; [lia | discriminate |].
  unfold shand, hand; cbn [csize]; lia.
Qed.

(** Open a one-box chain if there is one, and a two-box chain otherwise. Either
    way what is left holds a handout at least as large as the one given away,
    so the terminal bonus does not move. *)
Lemma short_selection :
  forall G, swf G -> existsb shortb G = true ->
    exists C rest,
      In (C, rest) (selections G) /\ shortb C = true /\
      (rest = [] \/ 2 * Z.of_nat (shand C) <= maxsh rest).
Proof.
  intros G Hw Hs; unfold swf in Hw.
  destruct (existsb chain1b G) eqn:E1.
  - apply existsb_exists in E1; destruct E1 as [C [HinC HC]].
    destruct (In_selections G C HinC) as [rest Hrest].
    exists C, rest; split; [exact Hrest|].
    split; [apply chain1b_shortb; exact HC|].
    destruct rest as [|D rest']; [left; reflexivity | right].
    assert (HinD : In D G)
      by (eapply selection_rest_In; [exact Hrest | left; reflexivity]).
    rewrite Forall_forall in Hw; pose proof (shand_swf_ge1 D (Hw D HinD)) as Hd.
    pose proof (maxsh_ge_of_In D (D :: rest') (or_introl eq_refl)) as Hm.
    rewrite (shand_chain1b C HC); lia.
  - apply existsb_exists in Hs; destruct Hs as [C [HinC HC]].
    assert (H1 : chain1b C = false).
    { destruct (chain1b C) eqn:E; [|reflexivity].
      exfalso; assert (existsb chain1b G = true)
        by (apply existsb_exists; exists C; split; assumption).
      congruence. }
    destruct (In_selections G C HinC) as [rest Hrest].
    exists C, rest; split; [exact Hrest | split; [exact HC|]].
    destruct rest as [|D rest']; [left; reflexivity | right].
    assert (HinD : In D G)
      by (eapply selection_rest_In; [exact Hrest | left; reflexivity]).
    assert (HD1 : chain1b D = false).
    { destruct (chain1b D) eqn:E; [|reflexivity].
      exfalso; assert (existsb chain1b G = true)
        by (apply existsb_exists; exists D; split; assumption).
      congruence. }
    rewrite Forall_forall in Hw.
    pose proof (shand_ge2_of_not_chain1 D (Hw D HinD) HD1) as Hd.
    pose proof (maxsh_ge_of_In D (D :: rest') (or_introl eq_refl)) as Hm.
    rewrite (shand_short_not1 C HC H1); lia.
Qed.

(** * The capped control bound is exact above two *)

(** Berlekamp and Scott's threshold theorem, on every position the board can
    present: chains of one and two boxes included. *)
Theorem svalue_scval2_ge2 :
  forall G, swf G -> G <> [] -> 2 <= scval2 G -> svalue G = scval2 G.
Proof.
  assert (Haux : forall n G, (length G <= n)%nat -> swf G -> G <> [] ->
                   2 <= scval2 G -> svalue G = scval2 G).
  { induction n as [|n IH]; intros G Hlen Hw HNil H2.
    - destruct G as [|C G']; [contradiction | simpl in Hlen; lia].
    - destruct (existsb shortb G) eqn:Es.
      + destruct (short_selection G Hw Es) as [C [rest [Hsel [Hshort Hcase]]]].
        pose proof (selections_perm G (C, rest) Hsel) as Hperm; simpl in Hperm.
        pose proof (swf_of_selection G C rest Hw Hsel) as Hwcr.
        inversion Hwcr as [|D E HwC HwR Heq]; subst.
        destruct Hcase as [Hnil | Hmax].
        * subst rest; apply Permutation_length_1_inv in Hperm; subst G.
          apply svalue_single_scval2; exact HwC.
        * assert (Hnil2 : rest <> []).
          { intros ->; rewrite maxsh_nil in Hmax.
            pose proof (shand_swf_ge1 C HwC); lia. }
          assert (Htb : stb (C :: rest) = stb rest)
            by (apply stb_cons_short; assumption).
          (* the controlled value only rises when the short chain is removed *)
          assert (Hsw : sweight C <= -1)
            by (rewrite (sweight_short C Hshort);
                pose proof (shand_swf_ge1 C HwC);
                pose proof (shand_le_csize C); lia).
          assert (Hsplit : scval2 G = sweight C + scval2 rest).
          { rewrite <- (scval2_perm _ _ Hperm).
            unfold scval2; cbn [scbase]; rewrite Htb; lia. }
          assert (H2r : 2 <= scval2 rest) by lia.
          assert (Hh : Z.of_nat (shand C) <= scval2 rest)
            by (pose proof (shand_short_le2 C Hshort); lia).
          assert (Hlr : (length rest <= n)%nat).
          { apply Permutation_length in Hperm; simpl in Hperm; lia. }
          assert (Hrec : svalue rest = scval2 rest)
            by (apply IH; assumption).
          exact (svalue_step_eq G (C, rest) Hw Hsel Htb Hh Hrec).
      + apply svalue_scval2_ge2_wf;
          [apply (swf_no_short_wf G Hw Es) | exact HNil | exact H2]. }
  intros G Hw HNil H2; exact (Haux (length G) G (Nat.le_refl _) Hw HNil H2).
Qed.
