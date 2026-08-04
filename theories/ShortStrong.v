(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Berlekamp's control bound for the capped recursion, with the true bonus.

    [ShortControl.scval_le_svalue] proves the bound with the weakest terminal
    bonus that survives an induction: the smallest handout the position holds.
    [ShortBonus.stb] is the true one, and [ShortBonus.stb_eq_tb] shows it is
    Berlekamp's on every wellformed position. This file proves the bound for
    it.

    The induction splits on whether removing the opened component can raise
    the bonus. It usually cannot, and then the controller declines and the
    bound follows from the remainder. When it can, the remainder is forced to
    be chains of at most three boxes, and there the controller takes the
    component whole instead; [ShortSmall] supplies the two bounds that case
    needs. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Sorting.Permutation.
Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.ShortControl.
Require Import GameTrees.ShortBonus.
Require Import GameTrees.ShortSmall.

Import ListNotations.

Open Scope Z_scope.

(** * Handouts take three values *)

Lemma shand_values :
  forall C, swf_comp C -> (shand C = 1 \/ shand C = 2 \/ shand C = 4)%nat.
Proof.
  intros [n | n] Hw; cbn [swf_comp] in Hw; unfold shand, hand; cbn [csize].
  - destruct (Nat.eq_dec n 1) as [-> | Hne]; [left; reflexivity|].
    right; left; lia.
  - destruct Hw as [H4 _]; right; right; lia.
Qed.

Lemma maxsh_values :
  forall G, swf G -> G <> [] -> maxsh G = 2 \/ maxsh G = 4 \/ maxsh G = 8.
Proof.
  induction G as [|C G IH]; intros Hw HNil; [contradiction|].
  assert (HsC : swf_comp C)
    by (unfold swf in Hw; rewrite Forall_forall in Hw; apply Hw; left; auto).
  assert (HsG : swf G)
    by (unfold swf in Hw |- *; rewrite Forall_forall in Hw |- *;
        intros x Hx; apply Hw; right; exact Hx).
  rewrite maxsh_cons.
  destruct (shand_values C HsC) as [H1 | [H2 | H4]]; rewrite ?H1, ?H2, ?H4.
  - destruct G as [|D G']; [rewrite maxsh_nil; left; reflexivity|].
    destruct (IH HsG ltac:(discriminate)) as [E | [E | E]]; rewrite E; auto.
  - destruct G as [|D G']; [rewrite maxsh_nil; right; left; reflexivity|].
    destruct (IH HsG ltac:(discriminate)) as [E | [E | E]]; rewrite E; auto.
  - destruct G as [|D G']; [rewrite maxsh_nil; right; right; reflexivity|].
    destruct (IH HsG ltac:(discriminate)) as [E | [E | E]]; rewrite E; auto.
Qed.

(** * Small handouts force short components *)

Lemma maxsh_in :
  forall G C, In C G -> 2 * Z.of_nat (shand C) <= maxsh G.
Proof.
  induction G as [|D G IH]; intros C HC; [destruct HC|].
  rewrite maxsh_cons; destruct HC as [<- | HC]; [lia|].
  pose proof (IH C HC); lia.
Qed.

Lemma shortb_of_shand1 :
  forall C, swf_comp C -> (shand C <= 1)%nat -> shortb C = true.
Proof.
  intros [n | n] Hw Hs; cbn [swf_comp] in Hw;
    unfold shand, hand in Hs; cbn [csize] in Hs.
  - assert (Hn : n = 1%nat) by lia.
    subst n; reflexivity.
  - destruct Hw as [H4 _]; lia.
Qed.

Lemma smallb_of_shand2 :
  forall C, swf_comp C -> (shand C <= 2)%nat -> longchain_b C = false ->
    smallb C = true.
Proof.
  intros [n | n] Hw Hs Hl; cbn [swf_comp] in Hw;
    unfold shand, hand in Hs; cbn [csize] in Hs.
  - unfold longchain_b in Hl; apply Nat.leb_gt in Hl.
    unfold smallb; apply andb_true_iff; split; apply Nat.leb_le; lia.
  - destruct Hw as [H4 _]; lia.
Qed.

Lemma maxsh_le2_short :
  forall G, swf G -> maxsh G <= 2 -> forallb shortb G = true.
Proof.
  intros G Hw Hm; rewrite forallb_forall; intros C HC.
  assert (HsC : swf_comp C)
    by (unfold swf in Hw; rewrite Forall_forall in Hw; apply Hw; exact HC).
  pose proof (maxsh_in G C HC) as Hin.
  apply shortb_of_shand1; [exact HsC | lia].
Qed.

Lemma maxsh_le4_small :
  forall G, swf G -> maxsh G <= 4 -> existsb longchain_b G = false ->
    forallb smallb G = true.
Proof.
  intros G Hw Hm Hl; rewrite forallb_forall; intros C HC.
  assert (HsC : swf_comp C)
    by (unfold swf in Hw; rewrite Forall_forall in Hw; apply Hw; exact HC).
  pose proof (maxsh_in G C HC) as Hin.
  assert (HlC : longchain_b C = false).
  { destruct (longchain_b C) eqn:E; [|reflexivity].
    exfalso; assert (Hbad : existsb longchain_b G = true)
      by (apply existsb_exists; exists C; split; assumption).
    congruence. }
  apply smallb_of_shand2; [exact HsC | lia | exact HlC].
Qed.

Lemma smallb_no3_short :
  forall G, forallb smallb G = true -> existsb is_3chain_b G = false ->
    forallb shortb G = true.
Proof.
  induction G as [|C G IH]; intros Hs H3; [reflexivity|].
  simpl in Hs, H3 |- *.
  apply andb_true_iff in Hs; destruct Hs as [HsC HsG].
  apply orb_false_iff in H3; destruct H3 as [H3C H3G].
  assert (HC : shortb C = true).
  { destruct C as [n | n]; [|discriminate].
    pose proof (smallb_chain n HsC) as Hb.
    assert (Hn3 : n <> 3%nat)
      by (intros ->; cbn in H3C; discriminate).
    unfold shortb; apply andb_true_iff; split; apply Nat.leb_le; lia. }
  rewrite HC; simpl; apply IH; assumption.
Qed.

(** * The cap cannot rise when a component is added *)

Lemma cap_cons_le : forall C G, cap (C :: G) <= cap G.
Proof.
  intros C G; unfold cap; simpl.
  destruct (longchain_b C); simpl.
  - destruct (existsb longchain_b G); [lia|].
    destruct (existsb is_3chain_b G); lia.
  - destruct (existsb longchain_b G); [lia|].
    destruct (is_3chain_b C); simpl;
      destruct (existsb is_3chain_b G); lia.
Qed.

Lemma cap_long : forall G, existsb longchain_b G = true -> cap G = 4.
Proof. intros G H; unfold cap; rewrite H; reflexivity. Qed.

Lemma cap_six :
  forall G, existsb longchain_b G = false -> existsb is_3chain_b G = true ->
    cap G = 6.
Proof. intros G H1 H2; unfold cap; rewrite H1, H2; reflexivity. Qed.

(** * When the bonus rises *)

(** A rise forces the opened component to hold a strictly larger handout than
    anything left, and the cap to stay above it. *)
Lemma stb_rise_gaps :
  forall C rest,
    stb rest < stb (C :: rest) ->
    maxsh rest < 2 * Z.of_nat (shand C) /\ maxsh rest < cap (C :: rest).
Proof.
  intros C rest Hlt.
  pose proof (cap_cons_le C rest) as Hcap.
  unfold stb in *; rewrite maxsh_cons in Hlt.
  split.
  - destruct (Z.le_gt_cases (2 * Z.of_nat (shand C)) (maxsh rest)) as [Hle | Hgt];
      [|lia].
    rewrite Z.max_r in Hlt by lia; lia.
  - destruct (Z.le_gt_cases (cap (C :: rest)) (maxsh rest)) as [Hle | Hgt];
      [|lia].
    lia.
Qed.

(** The bound the rise case needs: the controller takes the component whole,
    and what she gives up is covered by the handout she gains. *)
Lemma rise_bound :
  forall C rest,
    swf (C :: rest) -> rest <> [] ->
    stb rest < stb (C :: rest) ->
    svalue rest + scbase rest + stb (C :: rest) <= 2 * Z.of_nat (shand C).
Proof.
  intros C rest Hw HNil Hlt.
  destruct (stb_rise_gaps C rest Hlt) as [Hg1 Hg2].
  assert (HsR : swf rest)
    by (unfold swf in Hw |- *; rewrite Forall_forall in Hw |- *;
        intros x Hx; apply Hw; right; exact Hx).
  assert (Hstb : stb (C :: rest) <= 2 * Z.of_nat (shand C)).
  { unfold stb; rewrite maxsh_cons; lia. }
  destruct (Z.le_gt_cases (maxsh rest) 2) as [Hm2 | Hm2].
  - (* everything left is a one-box chain *)
    pose proof (svalue_scbase_short rest (maxsh_le2_short rest HsR Hm2)); lia.
  - (* the cap is above four, so no long chain is left *)
    assert (Hm4 : maxsh rest <= 4).
    { destruct (maxsh_values rest HsR HNil) as [E | [E | E]]; try lia.
      pose proof (cap_range (C :: rest)); lia. }
    assert (Hmeq : maxsh rest = 4).
    { destruct (maxsh_values rest HsR HNil) as [E | [E | E]]; lia. }
    assert (Hnl : existsb longchain_b (C :: rest) = false).
    { destruct (existsb longchain_b (C :: rest)) eqn:E; [|reflexivity].
      exfalso; rewrite (cap_long _ E) in Hg2; lia. }
    assert (HnlR : existsb longchain_b rest = false)
      by (simpl in Hnl; apply orb_false_iff in Hnl; tauto).
    pose proof (maxsh_le4_small rest HsR Hm4 HnlR) as Hsm.
    destruct (existsb is_3chain_b rest) eqn:E3.
    + (* a three-chain is left, so the cap is six *)
      assert (Hcap6 : cap (C :: rest) = 6).
      { apply cap_six; [exact Hnl|].
        simpl; rewrite E3; apply orb_true_r. }
      assert (HsC : swf_comp C)
        by (unfold swf in Hw; rewrite Forall_forall in Hw; apply Hw;
            left; reflexivity).
      assert (HhC : 2 * Z.of_nat (shand C) = 8).
      { destruct (shand_values C HsC) as [E | [E | E]];
          rewrite E in Hg1 |- *; lia. }
      pose proof (svalue_scbase_small rest Hsm).
      unfold stb; rewrite maxsh_cons; lia.
    + (* none is, so the sharper bound applies *)
      pose proof (svalue_scbase_short rest (smallb_no3_short rest Hsm E3)); lia.
Qed.

(** * The bound *)

Theorem scval2_le_svalue :
  forall G, swf G -> G <> [] -> scval2 G <= svalue G.
Proof.
  assert (Haux : forall n G, (length G <= n)%nat -> swf G -> G <> [] ->
                   scval2 G <= svalue G).
  { induction n as [|n IH]; intros G Hn Hw HNil.
    - exfalso; apply HNil; destruct G; [reflexivity | simpl in Hn; lia].
    - apply svalue_lower_bound; [exact HNil|].
      intros q Hq.
      pose proof (selections_length G q Hq) as Hlen.
      pose proof (selections_perm G q Hq) as Hperm.
      destruct (selections_swf G q Hw Hq) as [HwC Hwr].
      assert (Hsc : scval2 G = scval2 (fst q :: snd q))
        by (rewrite (scval2_perm _ _ Hperm); reflexivity).
      assert (Hsw : swf (fst q :: snd q))
        by (unfold swf; constructor; assumption).
      assert (Hsle : Z.of_nat (shand (fst q)) <= Z.of_nat (csize (fst q)))
        by (pose proof (shand_le_csize (fst q)); lia).
      rewrite Hsc; unfold scval2; cbn [scbase].
      destruct (list_eq_dec comp_eq_dec (snd q) []) as [Hnil | Hrne].
      + (* the last component, taken whole *)
        unfold svalue_open, svopen; rewrite Hnil.
        assert (Hb : stb (fst q :: @nil comp) <= 2 * Z.of_nat (shand (fst q))).
        { unfold stb; rewrite maxsh_cons, maxsh_nil.
          rewrite Z.max_l by lia; apply Z.le_min_l. }
        assert (Hs0 : svalue (@nil comp) = 0) by reflexivity.
        rewrite Hs0.
        eapply Z.le_trans; [| apply Z.le_max_l].
        cbn [scbase]; unfold sweight; lia.
      + assert (Hrec : scval2 (snd q) <= svalue (snd q))
          by (apply IH; [lia | exact Hwr | exact Hrne]).
        destruct (Z.le_gt_cases (stb (fst q :: snd q)) (stb (snd q)))
          as [Hle | Hgt].
        * (* the bonus does not rise: decline and appeal to the rest *)
          unfold svalue_open, svopen.
          eapply Z.le_trans; [| apply Z.le_max_r].
          unfold scval2 in Hrec; unfold sweight; lia.
        * (* the bonus rises: take the component whole *)
          pose proof (rise_bound (fst q) (snd q) Hsw Hrne Hgt)
            as Hrb.
          unfold svalue_open, svopen.
          eapply Z.le_trans; [| apply Z.le_max_l].
          unfold sweight; lia. }
  intros G Hw HNil; apply (Haux (length G)); [lia | exact Hw | exact HNil].
Qed.

(** So on wellformed positions this is exactly Berlekamp's control bound,
    recovered through the handouts rather than the component names. *)
Corollary scval2_le_svalue_wf :
  forall G, wf G -> G <> [] -> cval G <= value G.
Proof.
  intros G Hw HNil.
  rewrite <- (scval2_eq_cval G Hw HNil), <- (svalue_wf G Hw).
  apply scval2_le_svalue; [apply wf_swf; exact Hw | exact HNil].
Qed.
