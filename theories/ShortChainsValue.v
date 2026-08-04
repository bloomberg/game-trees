(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Values of positions holding short chains.

    [GameTrees.ShortChains] caps the handout at the component and proves the
    capped recursion conservative, but proves nothing about the positions the
    cap was introduced for. The recursion [svf] had no unfolding lemmas at
    all, so nothing could be said about [svalue] beyond its agreement with
    [value] on wellformed positions.

    This file supplies that machinery, mirroring the development of
    [GameTrees.DotsAndBoxes] for the capped recursion, and settles what it
    reaches: [svalue_parity], the upper bound [svalue_le_size], and closed
    forms for the uniform families of one- and two-box chains, which the
    earlier theory could not state.

    The full analogue of [DotsAndBoxes.value_complete] is not proved. The
    closed form there is a case analysis on the terminal bonus and the counts
    of three-chains and four-loops, and admitting short chains changes every
    one of those cases, since a chain of one or two has no handout to leave
    and so cannot keep control. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.ShortChains.

Open Scope Z_scope.

(** * Unfolding the capped recursion *)

Lemma svf_cons :
  forall f C G,
    svf (S f) (C :: G) =
    minl (svopen C (svf f G))
         (map (fun q => svopen (fst q) (svf f (snd q)))
              (map (fun p => (fst p, C :: snd p)) (selections G))).
Proof. reflexivity. Qed.

Lemma svf_stable :
  forall k G f1 f2,
    (length G <= k)%nat -> (length G <= f1)%nat -> (length G <= f2)%nat ->
    svf f1 G = svf f2 G.
Proof.
  induction k as [|k IH]; intros G f1 f2 Hk H1 H2.
  - assert (HG : G = []) by (destruct G; simpl in Hk; [reflexivity | lia]).
    subst G; destruct f1, f2; reflexivity.
  - destruct G as [|C G]; [destruct f1, f2; reflexivity|].
    destruct f1 as [|f1]; [simpl in H1; lia|].
    destruct f2 as [|f2]; [simpl in H2; lia|].
    simpl length in Hk, H1, H2.
    rewrite !svf_cons, (IH G f1 f2) by lia.
    f_equal.
    apply map_ext_in; intros q Hq.
    apply in_map_iff in Hq; destruct Hq as [[Cp restp] [Heq Hp]].
    simpl in Heq; subst q; simpl.
    pose proof (selections_length G (Cp, restp) Hp) as Hl; simpl in Hl.
    f_equal; apply (IH (C :: restp)); simpl length; lia.
Qed.

Lemma svf_svalue :
  forall f G, (length G <= f)%nat -> svf f G = svalue G.
Proof.
  intros f G Hf; unfold svalue; apply (svf_stable (length G)); lia.
Qed.

Lemma svalue_nil : svalue [] = 0.
Proof. reflexivity. Qed.

(** The worth of a position once a component has been opened. *)
Definition svalue_open (p : comp * position) : Z :=
  svopen (fst p) (svalue (snd p)).

Lemma svalue_cons :
  forall C G,
    svalue (C :: G) =
    minl (svalue_open (C, G))
         (map svalue_open (map (fun p => (fst p, C :: snd p)) (selections G))).
Proof.
  intros C G.
  unfold svalue at 1; simpl length; rewrite svf_cons.
  unfold svalue_open; simpl fst; simpl snd.
  rewrite (svf_svalue (length G) G) by lia.
  f_equal.
  apply map_ext_in; intros q Hq.
  apply in_map_iff in Hq; destruct Hq as [[Cp restp] [Heq Hp]].
  simpl in Heq; subst q; simpl.
  pose proof (selections_length G (Cp, restp) Hp) as Hl; simpl in Hl.
  f_equal; apply svf_svalue; simpl length; lia.
Qed.

(** The fixpoint equation: the opener minimises over components. *)
Lemma svalue_unfold :
  forall G,
    svalue G =
    match selections G with
    | [] => 0
    | p :: more => minl (svalue_open p) (map svalue_open more)
    end.
Proof.
  intros [|C G]; [reflexivity | apply svalue_cons].
Qed.

Lemma svalue_le_open :
  forall G p, In p (selections G) -> svalue G <= svalue_open p.
Proof.
  intros G p Hp; rewrite svalue_unfold.
  destruct (selections G) as [|q more]; [destruct Hp|].
  destruct Hp as [<- | Hp]; [apply minl_le|].
  apply minl_le_in, in_map_iff; exists p; split; [reflexivity | exact Hp].
Qed.

Lemma svalue_attained :
  forall G, G <> [] -> exists p, In p (selections G) /\ svalue G = svalue_open p.
Proof.
  intros G HG.
  assert (Hval := svalue_unfold G).
  destruct (selections G) as [|q more] eqn:Esel.
  - exfalso; apply HG, selections_nil_iff; exact Esel.
  - destruct (minl_attained (map svalue_open more) (svalue_open q))
      as [H | [y [Hy Hy2]]].
    + exists q; split; [left; reflexivity | rewrite Hval, H; reflexivity].
    + apply in_map_iff in Hy; destruct Hy as [r [<- Hr]].
      exists r; split; [right; exact Hr | rewrite Hval, Hy2; reflexivity].
Qed.

Lemma svalue_const_options :
  forall G z,
    G <> [] ->
    (forall p, In p (selections G) -> svalue_open p = z) ->
    svalue G = z.
Proof.
  intros G z HG H.
  destruct (svalue_attained G HG) as [p [Hp Hval]].
  rewrite Hval; apply H; exact Hp.
Qed.

Lemma svalue_repeat_S :
  forall C k, svalue (repeat C (S k)) = svopen C (svalue (repeat C k)).
Proof.
  intros C k.
  apply svalue_const_options; [simpl; discriminate|].
  intros p Hp; rewrite (selections_repeat k C p Hp); reflexivity.
Qed.

(** * Parity *)

(** The capped recursion keeps the parity of the box count, exactly as the
    uncapped one does. *)
Theorem svalue_parity :
  forall G, Z.even (svalue G) = Z.even (Z.of_nat (size G)).
Proof.
  assert (Haux : forall k G, (length G <= k)%nat ->
            Z.even (svalue G) = Z.even (Z.of_nat (size G))).
  { induction k as [|k IH]; intros G Hk.
    - assert (HG : G = []) by (destruct G; simpl in Hk; [reflexivity | lia]).
      subst G; reflexivity.
    - destruct (list_eq_dec comp_eq_dec G []) as [-> | HNil]; [reflexivity|].
      destruct (svalue_attained G HNil) as [p [Hp Hval]].
      rewrite Hval; unfold svalue_open; rewrite svopen_parity.
      pose proof (selections_size G p Hp) as Hsz.
      pose proof (selections_length G p Hp) as Hlen.
      rewrite Z.even_add, (IH (snd p)) by lia.
      rewrite <- Z.even_add, <- Nat2Z.inj_add, Hsz; reflexivity. }
  intros G; apply (Haux (length G)); lia.
Qed.

(** * An upper bound *)

(** Under [swf] every component has a handout of at least one, so opening it
    never pays more than the whole board. *)
Lemma shand_pos : forall C, swf_comp C -> (1 <= shand C)%nat.
Proof.
  intros [j | j] H; unfold shand; apply Nat.min_glb; simpl in H |- *; lia.
Qed.

Lemma swf_tail : forall C G, swf (C :: G) -> swf G.
Proof. intros C G H; inversion H; assumption. Qed.

Lemma selections_swf :
  forall G p, swf G -> In p (selections G) -> swf_comp (fst p) /\ swf (snd p).
Proof.
  induction G as [|C G IH]; intros p HG Hp; simpl in Hp; [destruct Hp|].
  inversion HG as [|? ? HC HGs]; subst.
  destruct Hp as [<- | Hp]; simpl; [split; assumption|].
  apply in_map_iff in Hp; destruct Hp as [[Cq restq] [Heq Hq]].
  simpl in Heq; subst p; simpl.
  destruct (IH (Cq, restq) HGs Hq) as [H1 H2]; simpl in H1, H2.
  split; [exact H1 | constructor; assumption].
Qed.

Theorem svalue_le_size :
  forall G, swf G -> svalue G <= Z.of_nat (size G).
Proof.
  assert (Haux : forall k G, (length G <= k)%nat -> swf G ->
            svalue G <= Z.of_nat (size G)).
  { induction k as [|k IH]; intros G Hk HG.
    - assert (HGnil : G = []) by (destruct G; simpl in Hk; [reflexivity | lia]).
      subst G; rewrite svalue_nil; simpl; lia.
    - destruct (list_eq_dec comp_eq_dec G []) as [-> | HNil];
        [rewrite svalue_nil; simpl; lia|].
      destruct (svalue_attained G HNil) as [p [Hp Hval]].
      pose proof (selections_size G p Hp) as Hsz.
      pose proof (selections_length G p Hp) as Hlen.
      destruct (selections_swf G p HG Hp) as [HwC Hwrest].
      pose proof (svalue_nonneg (snd p)) as Hpos.
      assert (Hrec : svalue (snd p) <= Z.of_nat (size (snd p)))
        by (apply IH; [lia | exact Hwrest]).
      pose proof (shand_pos (fst p) HwC) as Hh.
      assert (Hhz : 1 <= Z.of_nat (shand (fst p))) by lia.
      rewrite Hval; unfold svalue_open, svopen.
      apply Z.max_lub; rewrite <- Hsz, Nat2Z.inj_add; lia. }
  intros G HG; apply (Haux (length G)); [lia | exact HG].
Qed.

(** * The uniform short families *)

(** A one-box chain is taken whole or declined whole, so a heap of them is
    worth the parity of its size. *)
Theorem svalue_chain1_heap :
  forall k, svalue (repeat (Chain 1) k) = if Nat.even k then 0 else 1.
Proof.
  induction k as [|k IH]; [reflexivity|].
  rewrite svalue_repeat_S, IH, svopen_chain1.
  rewrite Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even k); reflexivity.
Qed.

(** A two-box chain has its whole self as handout, so declining takes
    nothing and the heap alternates by two. *)
Theorem svalue_chain2_heap :
  forall k, svalue (repeat (Chain 2) k) = if Nat.even k then 0 else 2.
Proof.
  induction k as [|k IH]; [reflexivity|].
  rewrite svalue_repeat_S, IH, svopen_chain2.
  rewrite Nat.even_succ, <- Nat.negb_even.
  destruct (Nat.even k); reflexivity.
Qed.

(** Both families are bounded by the smallest component, which is what makes
    short chains worth so little: the controller cannot bank anything. *)
Corollary svalue_chain1_le1 : forall k, svalue (repeat (Chain 1) k) <= 1.
Proof.
  intros k; rewrite svalue_chain1_heap; destruct (Nat.even k); lia.
Qed.

Corollary svalue_chain2_le2 : forall k, svalue (repeat (Chain 2) k) <= 2.
Proof.
  intros k; rewrite svalue_chain2_heap; destruct (Nat.even k); lia.
Qed.

(** * Mixed short chains *)

(** If every option is worth one of two amounts, and both occur, the opener
    takes the smaller. *)
Lemma svalue_two_options :
  forall G a b,
    G <> [] ->
    (forall p, In p (selections G) -> svalue_open p = a \/ svalue_open p = b) ->
    (exists p, In p (selections G) /\ svalue_open p = a) ->
    (exists p, In p (selections G) /\ svalue_open p = b) ->
    svalue G = Z.min a b.
Proof.
  intros G a b HNil Hall [pa [Hpa Ha]] [pb [Hpb Hb]].
  destruct (svalue_attained G HNil) as [p [Hp Hval]].
  pose proof (svalue_le_open G pa Hpa) as La; rewrite Ha in La.
  pose proof (svalue_le_open G pb Hpb) as Lb; rewrite Hb in Lb.
  destruct (Hall p Hp) as [E | E]; rewrite Hval, E; lia.
Qed.

Definition smix (a b : nat) : position :=
  repeat (Chain 1) a ++ repeat (Chain 2) b.

Lemma smix_0 : forall b, smix 0 b = repeat (Chain 2) b.
Proof. reflexivity. Qed.

Lemma smix_S : forall a b, smix (S a) b = Chain 1 :: smix a b.
Proof. reflexivity. Qed.

Lemma smix_b0 : forall a, smix a 0 = repeat (Chain 1) a.
Proof. intros a; unfold smix; simpl repeat; apply app_nil_r. Qed.

Lemma smix_nonnil : forall a b, (0 < a + b)%nat -> smix a b <> [].
Proof.
  intros [|a] [|b] H; unfold smix; simpl; try lia; discriminate.
Qed.

(** Removing a component of a mixed short position leaves a mixed short
    position, with the order of the list preserved. *)
Lemma selections_smix :
  forall a b p,
    In p (selections (smix a b)) ->
    (fst p = Chain 1 /\ exists a', a = S a' /\ snd p = smix a' b) \/
    (fst p = Chain 2 /\ exists b', b = S b' /\ snd p = smix a b').
Proof.
  induction a as [|a IH]; intros b p Hp.
  - rewrite smix_0 in Hp.
    destruct b as [|b']; [simpl in Hp; destruct Hp|].
    rewrite (selections_repeat b' (Chain 2) p Hp).
    right; split; [reflexivity|]; exists b'; split; reflexivity.
  - rewrite smix_S in Hp; simpl in Hp.
    destruct Hp as [<- | Hp].
    + left; split; [reflexivity|]; exists a; split; reflexivity.
    + apply in_map_iff in Hp; destruct Hp as [[qc qr] [Heq Hq]].
      cbn [fst snd] in Heq; subst p.
      destruct (IH b (qc, qr) Hq) as [[Hc [a' [Ha Hs]]] | [Hc [b' [Hb Hs]]]];
        cbn [fst snd] in Hc, Hs.
      * left; cbn [fst snd]; split; [exact Hc|].
        exists a; split; [reflexivity|].
        rewrite Hs, Ha; reflexivity.
      * right; cbn [fst snd]; split; [exact Hc|].
        exists b'; split; [exact Hb|].
        rewrite Hs; reflexivity.
Qed.

(** The closed form. A single one-box chain already pins the value to the
    parity of the one-box chains, whatever the two-box chains do; with none
    of them present the two-box chains alternate by two instead. *)
Definition sm (a b : nat) : Z :=
  match a with
  | O => if Nat.even b then 0 else 2
  | S _ => if Nat.even a then 0 else 1
  end.

Theorem svalue_smix : forall a b, svalue (smix a b) = sm a b.
Proof.
  assert (Haux : forall k a b, (a + b <= k)%nat -> svalue (smix a b) = sm a b).
  { induction k as [|k IH]; intros a b Hk.
    - assert (Ha : a = 0%nat) by lia; assert (Hb : b = 0%nat) by lia.
      subst; reflexivity.
    - destruct a as [|a'].
      + rewrite smix_0, svalue_chain2_heap; reflexivity.
      + destruct b as [|b'].
        * rewrite smix_b0, svalue_chain1_heap; reflexivity.
        * assert (Hne : smix (S a') (S b') <> []) by (apply smix_nonnil; lia).
          assert (H1 : In (Chain 1, smix a' (S b'))
                          (selections (smix (S a') (S b')))).
          { rewrite smix_S; simpl; left; reflexivity. }
          assert (HinC2 : In (Chain 2) (smix (S a') (S b'))).
          { unfold smix; apply in_or_app; right; simpl; left; reflexivity. }
          destruct (In_selections _ (Chain 2) HinC2) as [rest Hrest].
          assert (Hr : rest = smix (S a') b').
          { destruct (selections_smix (S a') (S b') (Chain 2, rest) Hrest)
              as [[Hc _] | [_ [b'' [Hb Hs]]]]; [cbn in Hc; discriminate|].
            cbn in Hs; injection Hb as Hb; subst b''; exact Hs. }
          rewrite (svalue_two_options (smix (S a') (S b'))
                     (svopen (Chain 1) (svalue (smix a' (S b'))))
                     (svopen (Chain 2) (svalue (smix (S a') b'))) Hne).
          -- rewrite (IH a' (S b')) by lia.
             rewrite (IH (S a') b') by lia.
             rewrite svopen_chain1, svopen_chain2.
             destruct a' as [|a''].
             ++ cbn [sm]; destruct (Nat.even (S b')); cbn; lia.
             ++ cbn [sm].
                rewrite (Nat.even_succ (S a'')), <- Nat.negb_even.
                destruct (Nat.even (S a'')); cbn; lia.
          -- intros p Hp.
             destruct (selections_smix (S a') (S b') p Hp)
               as [[Hc [a2 [Ha Hs]]] | [Hc [b2 [Hb Hs]]]].
             ++ left; unfold svalue_open; rewrite Hc, Hs.
                injection Ha as Ha; subst a2; reflexivity.
             ++ right; unfold svalue_open; rewrite Hc, Hs.
                injection Hb as Hb; subst b2; reflexivity.
          -- exists (Chain 1, smix a' (S b')); split;
               [exact H1 | reflexivity].
          -- exists (Chain 2, rest); split; [exact Hrest|].
             unfold svalue_open; cbn [fst snd]; rewrite Hr; reflexivity. }
  intros a b; apply (Haux (a + b)%nat); lia.
Qed.

(** * The closed form where the chains are long *)

(** Wherever the uncapped theory applies, the capped value is the full closed
    form of [DotsAndBoxes.value_complete]. *)
Theorem svalue_complete_wf :
  forall G, wf G -> G <> [] -> svalue G = v41 G.
Proof.
  intros G Hw Hn; rewrite (svalue_wf G Hw); apply value_complete; assumption.
Qed.

(** * Where the capped and uncapped theories part *)

(** With a one-box chain beside a three-chain the two recursions part: the
    uncapped one credits the single box with a two-box handout it does not
    have and reports zero, where the capped one reports two. *)
Example short_chain_differs :
  value [Chain 1; Chain 3] = 0 /\ svalue [Chain 1; Chain 3] = 2.
Proof. split; reflexivity. Qed.

(** On a heap of one-box chains alone the two happen to agree, so the gap is
    not visible until a long component is present. *)
Example short_chain_agrees_alone :
  value [Chain 1; Chain 1] = 0 /\ svalue [Chain 1; Chain 1] = 0.
Proof. split; reflexivity. Qed.

(** The two agree again as soon as every chain is long. *)
Example svalue_agrees_long :
  svalue [Chain 3; Chain 3] = value [Chain 3; Chain 3].
Proof. apply svalue_wf; repeat constructor. Qed.
