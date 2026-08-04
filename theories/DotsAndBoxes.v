(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Dots and Boxes endgames consisting of loops and long chains.

    A position is a multiset of components, each a chain of length at least
    three or a loop of even length at least four. Whoever must open a
    component is the opener; the other player is the controller. Having been
    handed an open component, the controller either takes all of it, giving up
    control and becoming the opener, or leaves the hard-hearted handout of two
    boxes from a chain or four from a loop, keeping control.

    The value of a position is the margin by which the controller beats the
    opener when both maximise their own capture count. The controlled value is
    Berlekamp's lower bound on it, computable from the component multiset
    alone. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Sorting.Permutation.
Require Import GameTrees.Helpers.
Require Import GameTrees.Relations.
Require Import GameTrees.Trees.
Require Import Corelib.Program.Basics.
From Stdlib Require Import Relations.Relation_Operators.
From Stdlib Require Import Relations.Operators_Properties.
Require Import GameTrees.DotsAndBoxesBoard.

Import ListNotations.

(** * Components and positions *)

(** A component is a long chain or a loop, tagged with its box count. *)
Inductive comp : Type :=
| Chain : nat -> comp
| Loop : nat -> comp.

Definition csize (C : comp) : nat :=
  match C with Chain n => n | Loop n => n end.

(** The hard-hearted handout: two boxes from a chain, four from a loop. *)
Definition hand (C : comp) : nat :=
  match C with Chain _ => 2 | Loop _ => 4 end.

Definition position : Type := list comp.

Definition size (G : position) : nat := list_sum (map csize G).

Definition comp_eq_dec : forall C D : comp, {C = D} + {C <> D}.
Proof. decide equality; apply Nat.eq_dec. Defined.

(** Chains are long and loops are even and at least four, by the geometry of
    the grid. Both halves are used: the length bounds carry the counting
    arguments, and the evenness pins the small loops down to four and six, so
    that a loop which is not large has demand zero or two. Without it a loop of
    seven would have demand three and [small_demand], [demand_of_no34],
    [weight_ge_of_no34] and [value_open_zero_shape] would all fail. *)
Definition wf_comp (C : comp) : Prop :=
  match C with
  | Chain n => 3 <= n
  | Loop n => 4 <= n /\ Nat.even n = true
  end.

Definition wf (G : position) : Prop := Forall wf_comp G.

Lemma wf_nil : wf [].
Proof. constructor. Qed.

Lemma wf_cons : forall C G, wf_comp C -> wf G -> wf (C :: G).
Proof. intros; constructor; auto. Qed.

Lemma wf_tail : forall C G, wf (C :: G) -> wf G.
Proof. intros C G H; inversion H; auto. Qed.

Lemma wf_head : forall C G, wf (C :: G) -> wf_comp C.
Proof. intros C G H; inversion H; auto. Qed.

(** The handout never exceeds the component. *)
Lemma hand_le_csize : forall C, wf_comp C -> hand C <= csize C.
Proof. intros [n | n] H; simpl in *; lia. Qed.

(** * Selections *)

(** Each component of a position paired with what remains after removing that
    one occurrence. This is the branching set of the opener's move. *)
Fixpoint selections (G : position) : list (comp * position) :=
  match G with
  | [] => []
  | C :: rest =>
      (C, rest) :: map (fun p => (fst p, C :: snd p)) (selections rest)
  end.

Lemma selections_nil_iff : forall G, selections G = [] <-> G = [].
Proof.
  intros [|C G]; simpl; split; intros H; auto; discriminate.
Qed.

(** Removing a component drops the component count by exactly one. *)
Lemma selections_length :
  forall G p, In p (selections G) -> S (length (snd p)) = length G.
Proof.
  induction G as [|C G IH]; intros p Hp; simpl in Hp; [destruct Hp|].
  destruct Hp as [<- | Hp]; simpl; auto.
  apply in_map_iff in Hp; destruct Hp as [[Cq restq] [Heq Hq]].
  simpl in Heq; subst p; simpl.
  specialize (IH (Cq, restq) Hq); simpl in IH; lia.
Qed.

(** Selection preserves wellformedness of the remainder and picks a
    wellformed component. *)
Lemma selections_wf :
  forall G p, wf G -> In p (selections G) -> wf_comp (fst p) /\ wf (snd p).
Proof.
  induction G as [|C G IH]; intros p HG Hp; simpl in Hp; [destruct Hp|].
  destruct Hp as [<- | Hp]; simpl.
  - split; [apply (wf_head C G) | apply (wf_tail C G)]; auto.
  - apply in_map_iff in Hp; destruct Hp as [[Cq restq] [Heq Hq]].
    simpl in Heq; subst p; simpl.
    destruct (IH (Cq, restq) (wf_tail C G HG) Hq) as [H1 H2].
    simpl in H1, H2.
    split; [exact H1 | constructor; auto].
    apply (wf_head C G); auto.
Qed.

(** Selection removes exactly the chosen component's boxes. *)
Lemma selections_size :
  forall G p, In p (selections G) -> csize (fst p) + size (snd p) = size G.
Proof.
  induction G as [|C G IH]; intros p Hp; simpl in Hp; [destruct Hp|].
  destruct Hp as [<- | Hp]; [unfold size; simpl; lia|].
  apply in_map_iff in Hp; destruct Hp as [[Cq restq] [Heq Hq]].
  simpl in Heq; subst p.
  specialize (IH (Cq, restq) Hq); unfold size in *; simpl in *; lia.
Qed.

(** Every selection is a genuine member, and every member is selectable. *)
Lemma selections_In :
  forall G p, In p (selections G) -> In (fst p) G.
Proof.
  induction G as [|C G IH]; intros p Hp; simpl in Hp; [destruct Hp|].
  destruct Hp as [<- | Hp]; simpl; [left; reflexivity|].
  apply in_map_iff in Hp; destruct Hp as [[Cq restq] [Heq Hq]].
  simpl in Heq; subst p; simpl.
  right; exact (IH (Cq, restq) Hq).
Qed.

Lemma In_selections :
  forall G C, In C G -> exists rest, In (C, rest) (selections G).
Proof.
  induction G as [|D G IH]; intros C HC; [destruct HC|].
  destruct HC as [<- | HC].
  - exists G; left; reflexivity.
  - destruct (IH C HC) as [rest Hrest].
    exists (D :: rest); simpl; right.
    apply in_map_iff; exists (C, rest); split; [reflexivity | exact Hrest].
Qed.

(** * The value recursion *)

(** Values are integers: the controlled value of a position may be negative,
    even though the value itself never is. *)
Open Scope Z_scope.

(** The margin the controller secures once component [C] has been opened and
    the remaining position is worth [w]: take all of [C] and become the
    opener, or leave the handout and stay in control, whichever is larger. *)
Definition vopen (C : comp) (w : Z) : Z :=
  (Z.of_nat (csize C) - Z.of_nat (hand C)) + Z.abs (w - Z.of_nat (hand C)).

(** The two options spelled out, as in the source recursion. *)
Lemma vopen_max :
  forall C w,
    vopen C w = Z.max (Z.of_nat (csize C) - w)
                      (Z.of_nat (csize C) - 2 * Z.of_nat (hand C) + w).
Proof.
  intros C w; unfold vopen.
  destruct (Z.le_ge_cases w (Z.of_nat (hand C))) as [H | H].
  - rewrite Z.abs_neq by lia. lia.
  - rewrite Z.abs_eq by lia. lia.
Qed.

(** Minimum over a nonempty list, given its head. *)
Definition minl (x : Z) (l : list Z) : Z := fold_left Z.min l x.

Lemma minl_le : forall l x, minl x l <= x.
Proof.
  induction l as [|y l IH]; intros x; simpl; [lia|].
  eapply Z.le_trans; [apply IH | lia].
Qed.

Lemma minl_le_in : forall l x y, In y l -> minl x l <= y.
Proof.
  induction l as [|z l IH]; intros x y Hy; [destruct Hy|].
  destruct Hy as [<- | Hy]; simpl.
  - eapply Z.le_trans; [apply minl_le | lia].
  - apply IH; exact Hy.
Qed.

(** The minimum is attained: either at the head or at a list element. *)
Lemma minl_attained :
  forall l x, minl x l = x \/ exists y, In y l /\ minl x l = y.
Proof.
  induction l as [|z l IH]; intros x; simpl; [left; reflexivity|].
  destruct (IH (Z.min x z)) as [H | [y [Hy Hval]]].
  - unfold minl in *; rewrite H.
    destruct (Z.min_spec x z) as [[_ E] | [_ E]]; rewrite E.
    + left; reflexivity.
    + right; exists z; split; [left; reflexivity | reflexivity].
  - right; exists y; split; [right; exact Hy | exact Hval].
Qed.

Lemma minl_lower_bound :
  forall l x b, b <= x -> (forall y, In y l -> b <= y) -> b <= minl x l.
Proof.
  intros l x b Hx Hl.
  destruct (minl_attained l x) as [H | [y [Hy Hval]]].
  - rewrite H; exact Hx.
  - rewrite Hval; apply Hl; exact Hy.
Qed.

(** The fuelled value. The fuel bounds the number of components, each move
    removing exactly one. *)
Fixpoint vf (fuel : nat) (G : position) : Z :=
  match fuel with
  | O => 0
  | S f =>
      match selections G with
      | [] => 0
      | p :: more =>
          minl (vopen (fst p) (vf f (snd p)))
               (map (fun q => vopen (fst q) (vf f (snd q))) more)
      end
  end.

(** One unfolding of [vf] at a nonempty position. *)
Lemma vf_cons :
  forall f C G,
    vf (S f) (C :: G) =
    minl (vopen C (vf f G))
         (map (fun q => vopen (fst q) (vf f (snd q)))
              (map (fun p => (fst p, C :: snd p)) (selections G))).
Proof. reflexivity. Qed.

(** The value is independent of the fuel once the fuel covers the position. *)
Lemma vf_stable :
  forall n G f1 f2,
    (length G <= n)%nat -> (length G <= f1)%nat -> (length G <= f2)%nat ->
    vf f1 G = vf f2 G.
Proof.
  induction n as [|n IH]; intros G f1 f2 Hn H1 H2.
  - assert (HG : G = []) by (destruct G; simpl in Hn; [reflexivity | lia]).
    subst G; destruct f1, f2; reflexivity.
  - destruct G as [|C G]; [destruct f1, f2; reflexivity|].
    destruct f1 as [|f1]; [simpl in H1; lia|].
    destruct f2 as [|f2]; [simpl in H2; lia|].
    simpl length in Hn, H1, H2.
    rewrite !vf_cons.
    rewrite (IH G f1 f2) by lia.
    f_equal.
    apply map_ext_in; intros q Hq.
    apply in_map_iff in Hq; destruct Hq as [[Cp restp] [Heq Hp]].
    simpl in Heq; subst q; simpl.
    pose proof (selections_length G (Cp, restp) Hp) as Hl; simpl in Hl.
    f_equal.
    apply (IH (C :: restp)); simpl length; lia.
Qed.

(** The value of a position. *)
Definition value (G : position) : Z := vf (length G) G.

Lemma value_nil : value [] = 0.
Proof. reflexivity. Qed.

Lemma vf_value :
  forall f G, (length G <= f)%nat -> vf f G = value G.
Proof.
  intros f G Hf; unfold value.
  apply (vf_stable (length G)); lia.
Qed.

(** The value of a position given that a particular component of it has just
    been opened. *)
Definition value_open (p : comp * position) : Z :=
  vopen (fst p) (value (snd p)).

(** One unfolding of the value at a nonempty position. *)
Lemma value_cons :
  forall C G,
    value (C :: G) =
    minl (value_open (C, G))
         (map value_open (map (fun p => (fst p, C :: snd p)) (selections G))).
Proof.
  intros C G.
  unfold value at 1; simpl length; rewrite vf_cons.
  unfold value_open; simpl fst; simpl snd.
  rewrite (vf_value (length G) G) by lia.
  f_equal.
  apply map_ext_in; intros q Hq.
  apply in_map_iff in Hq; destruct Hq as [[Cp restp] [Heq Hp]].
  simpl in Heq; subst q; simpl.
  pose proof (selections_length G (Cp, restp) Hp) as Hl; simpl in Hl.
  f_equal.
  apply vf_value; simpl length; lia.
Qed.

(** The fixpoint equation: the opener minimises over components. *)
Lemma value_unfold :
  forall G,
    value G =
    match selections G with
    | [] => 0
    | p :: more => minl (value_open p) (map value_open more)
    end.
Proof.
  intros [|C G]; [reflexivity | apply value_cons].
Qed.

(** The opener can do no better than any single choice. *)
Lemma value_le_open :
  forall G p, In p (selections G) -> value G <= value_open p.
Proof.
  intros G p Hp.
  rewrite value_unfold.
  destruct (selections G) as [|q more]; [destruct Hp|].
  destruct Hp as [<- | Hp].
  - apply minl_le.
  - apply minl_le_in.
    apply in_map_iff; exists p; split; [reflexivity | exact Hp].
Qed.

(** And the opener achieves one of them. *)
Lemma value_attained :
  forall G, G <> [] -> exists p, In p (selections G) /\ value G = value_open p.
Proof.
  intros G HG.
  assert (Hval := value_unfold G).
  destruct (selections G) as [|q more] eqn:Esel.
  - exfalso; apply HG; apply selections_nil_iff; exact Esel.
  - destruct (minl_attained (map value_open more) (value_open q))
      as [H | [y [Hy Hy2]]].
    + exists q; split; [left; reflexivity|].
      rewrite Hval, H; reflexivity.
    + apply in_map_iff in Hy; destruct Hy as [r [<- Hr]].
      exists r; split; [right; exact Hr|].
      rewrite Hval, Hy2; reflexivity.
Qed.

(** A lower bound on every option is a lower bound on the value. *)
Lemma value_lower_bound :
  forall G b,
    (forall p, In p (selections G) -> b <= value_open p) ->
    G <> [] -> b <= value G.
Proof.
  intros G b Hb HG.
  destruct (value_attained G HG) as [p [Hp Hval]].
  rewrite Hval; apply Hb; exact Hp.
Qed.

(** * Basic bounds *)

(** Each option is nonnegative, because the handout is never larger than the
    component that was opened. *)
Lemma vopen_nonneg :
  forall C w, wf_comp C -> 0 <= vopen C w.
Proof.
  intros C w HC; unfold vopen.
  pose proof (hand_le_csize C HC) as H.
  assert (0 <= Z.of_nat (csize C) - Z.of_nat (hand C)) by lia.
  pose proof (Z.abs_nonneg (w - Z.of_nat (hand C))); lia.
Qed.

(** The opener never profits: every endgame of loops and long chains is worth
    a nonnegative margin to the controller. *)
Theorem value_nonneg : forall G, wf G -> 0 <= value G.
Proof.
  intros G HG.
  destruct (list_eq_dec comp_eq_dec G []) as [-> | HNil];
    [rewrite value_nil; lia|].
  apply value_lower_bound; [|exact HNil].
  intros p Hp; unfold value_open.
  apply vopen_nonneg.
  exact (proj1 (selections_wf G p HG Hp)).
Qed.

(** A single component is taken whole. *)
Lemma value_single : forall C, value [C] = Z.of_nat (csize C).
Proof.
  intros C.
  assert (H : value [C] = vopen C (value [])) by (rewrite value_cons; reflexivity).
  rewrite H, value_nil; unfold vopen; destruct C; simpl; lia.
Qed.

(** * Parity *)

(** Values and sizes share a parity, because the value is a margin under some
    line of play that distributes every remaining box. *)
Lemma vopen_parity :
  forall C w,
    Z.even (vopen C w) = Z.even (Z.of_nat (csize C) + w).
Proof.
  intros C w; rewrite vopen_max.
  destruct (Z.le_ge_cases w (Z.of_nat (hand C))) as [H | H].
  - rewrite Z.max_l by (destruct C; simpl in *; lia).
    rewrite Z.even_sub, Z.even_add.
    destruct (Z.even (Z.of_nat (csize C))), (Z.even w); reflexivity.
  - rewrite Z.max_r by (destruct C; simpl in *; lia).
    replace (Z.of_nat (csize C) - 2 * Z.of_nat (hand C) + w)
      with ((Z.of_nat (csize C) + w) - 2 * Z.of_nat (hand C)) by lia.
    rewrite Z.even_sub.
    rewrite (Z.even_mul 2 (Z.of_nat (hand C))); simpl Z.even at 2.
    destruct (Z.even (Z.of_nat (csize C) + w)); reflexivity.
Qed.

Lemma size_cons : forall C G, (size (C :: G) = csize C + size G)%nat.
Proof. intros C G; unfold size; simpl; lia. Qed.

Theorem value_parity :
  forall G, Z.even (value G) = Z.even (Z.of_nat (size G)).
Proof.
  assert (Haux : forall n G, (length G <= n)%nat ->
            Z.even (value G) = Z.even (Z.of_nat (size G))).
  { induction n as [|n IH]; intros G Hn.
    - assert (HG : G = []) by (destruct G; simpl in Hn; [reflexivity | lia]).
      subst G; reflexivity.
    - destruct (list_eq_dec comp_eq_dec G []) as [-> | HNil]; [reflexivity|].
      destruct (value_attained G HNil) as [p [Hp Hval]].
      rewrite Hval; unfold value_open.
      rewrite vopen_parity.
      pose proof (selections_size G p Hp) as Hsz.
      pose proof (selections_length G p Hp) as Hlen.
      rewrite Z.even_add.
      rewrite (IH (snd p)) by lia.
      rewrite <- Z.even_add.
      rewrite <- Nat2Z.inj_add, Hsz; reflexivity. }
  intros G; apply (Haux (length G)); lia.
Qed.

(** * Positions built from one repeated component *)

(** Inversion for a selection from a nonempty position. *)
Lemma selections_cons_In :
  forall C G p,
    In p (selections (C :: G)) ->
    p = (C, G) \/ exists q, In q (selections G) /\ p = (fst q, C :: snd q).
Proof.
  intros C G p Hp; simpl in Hp.
  destruct Hp as [<- | Hp]; [left; reflexivity|].
  right; apply in_map_iff in Hp; destruct Hp as [q [Heq Hq]].
  exists q; split; [exact Hq | symmetry; exact Heq].
Qed.

(** Removing a component from a uniform position leaves a uniform position. *)
Lemma selections_repeat :
  forall n C p,
    In p (selections (repeat C (S n))) -> p = (C, repeat C n).
Proof.
  induction n as [|n IH]; intros C p Hp; apply selections_cons_In in Hp.
  - destruct Hp as [-> | [q [Hq _]]]; [reflexivity | destruct Hq].
  - destruct Hp as [-> | [q [Hq ->]]]; [reflexivity|].
    rewrite (IH C q Hq); reflexivity.
Qed.

(** If every option has the same worth then that is the value. *)
Lemma value_const_options :
  forall G z,
    G <> [] ->
    (forall p, In p (selections G) -> value_open p = z) ->
    value G = z.
Proof.
  intros G z HG H.
  destruct (value_attained G HG) as [p [Hp Hval]].
  rewrite Hval; apply H; exact Hp.
Qed.

Lemma value_repeat_S :
  forall C n, value (repeat C (S n)) = vopen C (value (repeat C n)).
Proof.
  intros C n.
  apply value_const_options; [simpl; discriminate|].
  intros p Hp; rewrite (selections_repeat n C p Hp).
  reflexivity.
Qed.

(** The value of a heap of three-chains, by the recursion itself. *)
Fixpoint v3 (n : nat) : Z :=
  match n with
  | O => 0
  | S k => vopen (Chain 3) (v3 k)
  end.

Lemma value_three_chains :
  forall n, value (repeat (Chain 3) n) = v3 n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite value_repeat_S, IH; reflexivity.
Qed.

Lemma even_S : forall m, Nat.even (S m) = negb (Nat.even m).
Proof. intros m; rewrite Nat.even_succ, <- Nat.negb_even; reflexivity. Qed.

(** Closed form: after the single chain, the heap alternates between two and
    one according to parity. *)
Lemma v3_closed :
  forall n, v3 (S (S n)) = if Nat.even (S (S n)) then 2 else 1.
Proof.
  induction n as [|n IH]; [reflexivity|].
  change (v3 (S (S (S n)))) with (vopen (Chain 3) (v3 (S (S n)))).
  rewrite IH, (even_S (S (S n))).
  destruct (Nat.even (S (S n))); reflexivity.
Qed.

Lemma v3_0 : v3 0 = 0.
Proof. reflexivity. Qed.

Lemma v3_1 : v3 1 = 3.
Proof. reflexivity. Qed.

Lemma v3_bounds : forall n, 0 <= v3 n <= 3.
Proof.
  intros [|[|n]].
  - rewrite v3_0; lia.
  - rewrite v3_1; lia.
  - rewrite v3_closed; destruct (Nat.even (S (S n))); lia.
Qed.

Lemma v3_pos : forall n, (1 <= n)%nat -> 1 <= v3 n.
Proof.
  intros [|[|n]] H.
  - lia.
  - rewrite v3_1; lia.
  - rewrite v3_closed; destruct (Nat.even (S (S n))); lia.
Qed.

(** * The controlled value *)

(** Each component contributes its length less twice its handout: four for a
    chain, eight for a loop. *)
Definition weight (C : comp) : Z :=
  Z.of_nat (csize C) - 2 * Z.of_nat (hand C).

Fixpoint cbase (G : position) : Z :=
  match G with
  | [] => 0
  | C :: rest => weight C + cbase rest
  end.

Definition is_loop_b (C : comp) : bool :=
  match C with Loop _ => true | Chain _ => false end.

Definition is_3chain_b (C : comp) : bool :=
  match C with Chain 3 => true | _ => false end.

(** Berlekamp's terminal bonus. *)
Definition tb (G : position) : Z :=
  match G with
  | [] => 0
  | _ :: _ =>
      if forallb is_loop_b G then 8
      else if (existsb is_loop_b G &&
               forallb (fun C => is_loop_b C || is_3chain_b C) G)%bool
           then 6
           else 4
  end.

Definition cval (G : position) : Z := cbase G + tb G.

Lemma cbase_nil : cbase [] = 0.
Proof. reflexivity. Qed.

Lemma cbase_cons : forall C G, cbase (C :: G) = weight C + cbase G.
Proof. reflexivity. Qed.

Lemma weight_chain : forall m, weight (Chain m) = Z.of_nat m - 4.
Proof. intros m; unfold weight; simpl csize; simpl hand; lia. Qed.

Lemma weight_loop_len : forall m, weight (Loop m) = Z.of_nat m - 8.
Proof. intros m; unfold weight; simpl csize; simpl hand; lia. Qed.

Lemma tb_nil : tb [] = 0.
Proof. reflexivity. Qed.

(** The terminal bonus at a nonempty position, with the outer match resolved. *)
Lemma tb_cons_form :
  forall C G,
    tb (C :: G) =
    if forallb is_loop_b (C :: G) then 8
    else if (existsb is_loop_b (C :: G) &&
             forallb (fun D => is_loop_b D || is_3chain_b D) (C :: G))%bool
         then 6
         else 4.
Proof. reflexivity. Qed.

Lemma tb_range : forall G, 0 <= tb G <= 8.
Proof.
  intros [|C G]; [rewrite tb_nil; lia|].
  rewrite tb_cons_form.
  destruct (forallb is_loop_b (C :: G)); [lia|].
  destruct (existsb is_loop_b (C :: G) &&
            forallb (fun D => is_loop_b D || is_3chain_b D) (C :: G))%bool; lia.
Qed.

Lemma tb_pos : forall G, G <> [] -> 4 <= tb G.
Proof.
  intros [|C G] H; [contradiction|].
  rewrite tb_cons_form.
  destruct (forallb is_loop_b (C :: G)); [lia|].
  destruct (existsb is_loop_b (C :: G) &&
            forallb (fun D => is_loop_b D || is_3chain_b D) (C :: G))%bool; lia.
Qed.

(** * Permutation invariance *)

Lemma forallb_perm :
  forall (f : comp -> bool) G H, Permutation G H -> forallb f G = forallb f H.
Proof.
  intros f G H HP; induction HP; simpl; try congruence.
  destruct (f x), (f y); reflexivity.
Qed.

Lemma existsb_perm :
  forall (f : comp -> bool) G H, Permutation G H -> existsb f G = existsb f H.
Proof.
  intros f G H HP; induction HP; simpl; try congruence.
  destruct (f x), (f y); reflexivity.
Qed.

Lemma negb_forallb :
  forall (f : comp -> bool) l,
    negb (forallb f l) = existsb (fun x => negb (f x)) l.
Proof.
  intros f l; induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (f a); simpl; [exact IH | reflexivity].
Qed.

Lemma tb_perm : forall G H, Permutation G H -> tb G = tb H.
Proof.
  intros G H HP.
  destruct G as [|C G]; destruct H as [|D H].
  - reflexivity.
  - apply Permutation_nil in HP; discriminate.
  - symmetry in HP; apply Permutation_nil in HP; discriminate.
  - unfold tb.
    rewrite (forallb_perm is_loop_b _ _ HP).
    rewrite (existsb_perm is_loop_b _ _ HP).
    rewrite (forallb_perm (fun E => is_loop_b E || is_3chain_b E)%bool _ _ HP).
    reflexivity.
Qed.

(** A selection is a permutation of the position it came from. *)
Lemma selections_perm :
  forall G p, In p (selections G) -> Permutation (fst p :: snd p) G.
Proof.
  induction G as [|C G IH]; intros p Hp; simpl in Hp; [destruct Hp|].
  destruct Hp as [<- | Hp]; simpl; [apply Permutation_refl|].
  apply in_map_iff in Hp; destruct Hp as [[Cq restq] [Heq Hq]].
  simpl in Heq; subst p; simpl.
  eapply Permutation_trans; [apply perm_swap|].
  apply perm_skip.
  exact (IH (Cq, restq) Hq).
Qed.

Lemma selections_cbase :
  forall G p, In p (selections G) -> cbase G = weight (fst p) + cbase (snd p).
Proof.
  induction G as [|C G IH]; intros p Hp; simpl in Hp; [destruct Hp|].
  destruct Hp as [<- | Hp]; [reflexivity|].
  apply in_map_iff in Hp; destruct Hp as [[Cq restq] [Heq Hq]].
  simpl in Heq; subst p.
  specialize (IH (Cq, restq) Hq); simpl in *; lia.
Qed.

Lemma selections_tb :
  forall G p, In p (selections G) -> tb G = tb (fst p :: snd p).
Proof.
  intros G p Hp.
  symmetry; apply tb_perm, selections_perm; exact Hp.
Qed.

Lemma selections_cval :
  forall G p,
    In p (selections G) ->
    cval G = weight (fst p) + cbase (snd p) + tb (fst p :: snd p).
Proof.
  intros G p Hp; unfold cval.
  rewrite (selections_cbase G p Hp), (selections_tb G p Hp); reflexivity.
Qed.

(** * Where the terminal bonus can rise *)

(** A position all of whose components are loops or three-chains, and which
    has no loop, consists of three-chains. *)
Lemma all_3chains_of_no_loop :
  forall l,
    forallb (fun X => is_loop_b X || is_3chain_b X)%bool l = true ->
    existsb is_loop_b l = false ->
    forallb is_3chain_b l = true.
Proof.
  induction l as [|X l IH]; intros HF HE; [reflexivity|].
  simpl in HF, HE |- *.
  apply andb_true_iff in HF; destruct HF as [HX HF].
  apply orb_false_iff in HE; destruct HE as [HXl HE].
  rewrite HXl in HX; simpl in HX.
  rewrite HX; simpl; apply IH; assumption.
Qed.

Lemma is_3chain_eq : forall X, is_3chain_b X = true -> X = Chain 3.
Proof.
  intros [[|[|[|[|n]]]] | n] H; simpl in H; try discriminate; reflexivity.
Qed.

Lemma all_3chains_repeat :
  forall l, forallb is_3chain_b l = true -> l = repeat (Chain 3) (length l).
Proof.
  induction l as [|X l IH]; intros H; [reflexivity|].
  simpl in H; apply andb_true_iff in H; destruct H as [HX Hl].
  simpl; rewrite (is_3chain_eq X HX), <- (IH Hl); reflexivity.
Qed.

(** Adding a component can only raise the terminal bonus by turning a heap of
    three-chains into a heap of three-chains with a loop. *)
Lemma tb_increase_shape :
  forall C rest,
    rest <> [] ->
    tb rest < tb (C :: rest) ->
    is_loop_b C = true /\ forallb is_3chain_b rest = true.
Proof.
  intros C rest Hne Hlt.
  destruct rest as [|D rest]; [contradiction|].
  rewrite (tb_cons_form C (D :: rest)), (tb_cons_form D rest) in Hlt.
  change (forallb is_loop_b (C :: D :: rest))
    with (is_loop_b C && forallb is_loop_b (D :: rest))%bool in Hlt.
  change (existsb is_loop_b (C :: D :: rest))
    with (is_loop_b C || existsb is_loop_b (D :: rest))%bool in Hlt.
  change (forallb (fun X => is_loop_b X || is_3chain_b X)%bool (C :: D :: rest))
    with ((is_loop_b C || is_3chain_b C) &&
          forallb (fun X => is_loop_b X || is_3chain_b X)%bool (D :: rest))%bool
    in Hlt.
  destruct (is_loop_b C) eqn:EC, (is_3chain_b C) eqn:E3,
           (forallb is_loop_b (D :: rest)) eqn:EL,
           (existsb is_loop_b (D :: rest)) eqn:EE,
           (forallb (fun X => is_loop_b X || is_3chain_b X)%bool (D :: rest))
             eqn:EF;
    simpl in Hlt; try lia;
    (split; [reflexivity | apply all_3chains_of_no_loop; assumption]).
Qed.

(** Every component of a heap of three-chains is a loop or a three-chain. *)
Lemma forallb_loop3_repeat3 :
  forall n,
    forallb (fun X => is_loop_b X || is_3chain_b X)%bool
            (repeat (Chain 3) n) = true.
Proof. induction n as [|n IH]; [reflexivity | simpl; exact IH]. Qed.

(** With a loop in front, a nonempty heap of three-chains has bonus six. *)
Lemma tb_loop_three_chains :
  forall C k,
    is_loop_b C = true ->
    tb (C :: repeat (Chain 3) (S k)) = 6.
Proof.
  intros C k HC.
  rewrite tb_cons_form.
  change (forallb is_loop_b (C :: repeat (Chain 3) (S k)))
    with (is_loop_b C && forallb is_loop_b (repeat (Chain 3) (S k)))%bool.
  change (existsb is_loop_b (C :: repeat (Chain 3) (S k)))
    with (is_loop_b C || existsb is_loop_b (repeat (Chain 3) (S k)))%bool.
  change (forallb (fun X => is_loop_b X || is_3chain_b X)%bool
                  (C :: repeat (Chain 3) (S k)))
    with ((is_loop_b C || is_3chain_b C) &&
          forallb (fun X => is_loop_b X || is_3chain_b X)%bool
                  (repeat (Chain 3) (S k)))%bool.
  rewrite HC.
  assert (Hall : forallb is_loop_b (repeat (Chain 3) (S k)) = false)
    by reflexivity.
  rewrite Hall, (forallb_loop3_repeat3 (S k)); reflexivity.
Qed.

Lemma cbase_repeat_three : forall k, cbase (repeat (Chain 3) k) = - Z.of_nat k.
Proof.
  induction k as [|k IH]; [reflexivity|].
  change (cbase (repeat (Chain 3) (S k)))
    with (weight (Chain 3) + cbase (repeat (Chain 3) k)).
  rewrite IH; unfold weight; simpl csize; simpl hand; lia.
Qed.

Lemma weight_loop : forall C, is_loop_b C = true -> weight C = Z.of_nat (csize C) - 8.
Proof.
  intros [n | n] H; simpl in H; [discriminate|].
  unfold weight; simpl; lia.
Qed.

(** * Berlekamp's control bound *)

(** The control strategy guarantees the controller the controlled value, so
    the value of a position is never below it. *)
Theorem cval_le_value : forall G, wf G -> cval G <= value G.
Proof.
  assert (Haux : forall n G, (length G <= n)%nat -> wf G -> cval G <= value G).
  { induction n as [|n IH]; intros G Hn HG.
    - assert (HGnil : G = []) by (destruct G; simpl in Hn; [reflexivity | lia]).
      subst G; unfold cval; rewrite tb_nil, value_nil; simpl cbase; lia.
    - destruct (list_eq_dec comp_eq_dec G []) as [-> | HNil].
      { unfold cval; rewrite tb_nil, value_nil; simpl cbase; lia. }
      apply value_lower_bound; [|exact HNil].
      intros p Hp.
      pose proof (selections_cval G p Hp) as Hcv.
      pose proof (selections_length G p Hp) as Hlen.
      pose proof (selections_wf G p HG Hp) as [HwC Hwrest].
      assert (Hw : weight (fst p) =
                   Z.of_nat (csize (fst p)) - 2 * Z.of_nat (hand (fst p)))
        by reflexivity.
      unfold value_open; rewrite vopen_max, Hcv.
      destruct (Z_le_gt_dec (tb (fst p :: snd p)) (tb (snd p))) as [Hle | Hgt].
      + (* the terminal bonus does not rise: keep control *)
        assert (Hrec : cval (snd p) <= value (snd p))
          by (apply IH; [lia | exact Hwrest]).
        unfold cval in Hrec.
        eapply Z.le_trans; [| apply Z.le_max_r]; lia.
      + destruct (list_eq_dec comp_eq_dec (snd p) []) as [Hnil | Hrne].
        * (* the opened component was the last one *)
          rewrite Hnil, value_nil.
          assert (Htb : tb (fst p :: []) <= 2 * Z.of_nat (hand (fst p))).
          { destruct (fst p) as [m | m]; rewrite tb_cons_form; simpl; lia. }
          change (cbase []) with 0.
          eapply Z.le_trans; [| apply Z.le_max_l]; lia.
        * (* a loop opened over a heap of three-chains *)
          destruct (tb_increase_shape (fst p) (snd p) Hrne (Z.gt_lt _ _ Hgt))
            as [HCl H3].
          pose proof (all_3chains_repeat (snd p) H3) as Hrep.
          destruct (length (snd p)) as [|k] eqn:Elen.
          { exfalso; apply Hrne.
            destruct (snd p) as [|X l]; [reflexivity | simpl in Elen; discriminate]. }
          assert (Hv : value (snd p) = v3 (S k))
            by (rewrite Hrep; apply value_three_chains).
          assert (Hcb : cbase (snd p) = - Z.of_nat (S k))
            by (rewrite Hrep; apply cbase_repeat_three).
          assert (Htb6 : tb (fst p :: snd p) = 6)
            by (rewrite Hrep; apply tb_loop_three_chains; exact HCl).
          rewrite Hv, Hcb, Htb6, (weight_loop (fst p) HCl).
          pose proof (v3_bounds (S k)) as Hb.
          assert (Hk : 1 <= Z.of_nat (S k)) by lia.
          eapply Z.le_trans; [| apply Z.le_max_l]; lia. }
  intros G HG; apply (Haux (length G)); [lia | exact HG].
Qed.

(** * The controller's decision *)

(** The controller's two replies to an opened component, named. *)
Definition give_up_control (C : comp) (w : Z) : Z :=
  Z.of_nat (csize C) - w.

Definition keep_control (C : comp) (w : Z) : Z :=
  Z.of_nat (csize C) - 2 * Z.of_nat (hand C) + w.

(** She takes whichever is larger. *)
Theorem controller_optimal :
  forall C w, vopen C w = Z.max (give_up_control C w) (keep_control C w).
Proof. intros C w; unfold give_up_control, keep_control; apply vopen_max. Qed.

(** Keeping control is right exactly when what remains is worth more to her
    than the handout she gives away: two boxes from a chain, four from a
    loop. *)
Theorem controller_keeps :
  forall C w, Z.of_nat (hand C) <= w -> vopen C w = keep_control C w.
Proof.
  intros C w H; unfold vopen, keep_control; rewrite Z.abs_eq by lia; lia.
Qed.

Theorem controller_gives_up :
  forall C w, w <= Z.of_nat (hand C) -> vopen C w = give_up_control C w.
Proof.
  intros C w H; unfold vopen, give_up_control; rewrite Z.abs_neq by lia; lia.
Qed.

(** * The all-but-two rule *)

(** Declining by leaving [k] boxes behind: the controller takes the rest, the
    opener takes those [k] and, having scored, must open again, so control
    stays where it was. *)
Definition decline (C : comp) (k : nat) (w : Z) : Z :=
  Z.of_nat (csize C) - 2 * Z.of_nat k + w.

Lemma decline_hand : forall C w, decline C (hand C) w = keep_control C w.
Proof. intros C w; unfold decline, keep_control; lia. Qed.

(** Leaving more than the handout is never better, so the smallest legal
    handout is the right one: two boxes from a chain, four from a loop. *)
Theorem all_but_two :
  forall C w k, (hand C <= k)%nat -> decline C k w <= decline C (hand C) w.
Proof.
  intros C w k H; unfold decline.
  assert (Hz : Z.of_nat (hand C) <= Z.of_nat k) by (apply Nat2Z.inj_le; exact H).
  lia.
Qed.

(** So every reply open to the controller is worth at most [vopen], and
    [vopen] is realised by one of the two named replies. *)
Theorem controller_best :
  forall C w k,
    (hand C <= k)%nat ->
    decline C k w <= vopen C w /\
    give_up_control C w <= vopen C w /\
    (vopen C w = give_up_control C w \/ vopen C w = keep_control C w).
Proof.
  intros C w k H; rewrite controller_optimal; repeat split.
  - eapply Z.le_trans; [apply all_but_two; exact H|].
    rewrite decline_hand; apply Z.le_max_r.
  - apply Z.le_max_l.
  - destruct (Z.max_spec (give_up_control C w) (keep_control C w))
      as [[_ E] | [_ E]]; rewrite E; [right | left]; reflexivity.
Qed.

(** * Single components and the smallest mixed position *)

Lemma tb_single_chain : forall m, tb [Chain m] = 4.
Proof. intros m; rewrite tb_cons_form; reflexivity. Qed.

Lemma tb_single_loop : forall m, tb [Loop m] = 8.
Proof. intros m; rewrite tb_cons_form; reflexivity. Qed.

Lemma cval_single : forall C, cval [C] = Z.of_nat (csize C).
Proof.
  intros [m | m]; unfold cval; rewrite cbase_cons, cbase_nil.
  - rewrite tb_single_chain, weight_chain; simpl csize; lia.
  - rewrite tb_single_loop, weight_loop_len; simpl csize; lia.
Qed.

(** A lone component is taken whole, and that is its controlled value. *)
Theorem value_single_cval : forall C, value [C] = cval [C].
Proof. intros C; rewrite value_single, cval_single; reflexivity. Qed.

Lemma tb_three_loop : forall l, tb [Chain 3; Loop l] = 6.
Proof. intros l; rewrite tb_cons_form; reflexivity. Qed.

Lemma cval_three_loop :
  forall l, cval [Chain 3; Loop l] = Z.of_nat l - 3.
Proof.
  intros l; unfold cval; rewrite tb_three_loop.
  rewrite !cbase_cons, cbase_nil, weight_chain, weight_loop_len; lia.
Qed.

(** The smallest position with no bonus-preserving move: a three-chain and a
    loop. Opening the loop is optimal and the value is the controlled
    value. *)
Theorem value_three_loop :
  forall l, (4 <= l)%nat -> value [Chain 3; Loop l] = cval [Chain 3; Loop l].
Proof.
  intros l Hl.
  assert (Hsel : value [Chain 3; Loop l] =
                 minl (vopen (Chain 3) (value [Loop l]))
                      [vopen (Loop l) (value [Chain 3])])
    by (rewrite value_cons; reflexivity).
  rewrite !value_single in Hsel; simpl csize in Hsel.
  assert (H1 : vopen (Chain 3) (Z.of_nat l) = Z.of_nat l - 1).
  { rewrite controller_keeps by (simpl hand; lia).
    unfold keep_control; simpl csize; simpl hand; lia. }
  assert (H2 : vopen (Loop l) (Z.of_nat 3) = Z.of_nat l - 3).
  { rewrite controller_gives_up by (simpl hand; lia).
    unfold give_up_control; simpl csize; lia. }
  rewrite H1, H2 in Hsel.
  rewrite cval_three_loop, Hsel.
  unfold minl; simpl fold_left; lia.
Qed.

(** * Sizes and controlled values modulo four *)

Lemma size_minus_cbase :
  forall G,
    Z.of_nat (size G) - cbase G = 2 * Z.of_nat (list_sum (map hand G)).
Proof.
  induction G as [|C G IH]; [reflexivity|].
  rewrite size_cons; simpl cbase; simpl map; simpl list_sum.
  unfold weight.
  rewrite !Nat2Z.inj_add; lia.
Qed.

Lemma handsum_even :
  forall G, exists m, list_sum (map hand G) = (2 * m)%nat.
Proof.
  induction G as [|C G [m Hm]]; [exists 0%nat; reflexivity|].
  simpl map; simpl list_sum; rewrite Hm.
  destruct C as [k | k]; simpl hand.
  - exists (S m); lia.
  - exists (S (S m)); lia.
Qed.

(** A position with no three-chain never scores the six-bonus. *)
Lemma tb_no_three_chain :
  forall G, existsb is_3chain_b G = false -> tb G = 0 \/ tb G = 4 \/ tb G = 8.
Proof.
  intros [|C G] H; [left; reflexivity|].
  rewrite tb_cons_form.
  destruct (forallb is_loop_b (C :: G)) eqn:EL; [right; right; reflexivity|].
  destruct (existsb is_loop_b (C :: G) &&
            forallb (fun D => is_loop_b D || is_3chain_b D) (C :: G))%bool
    eqn:E6; [|right; left; reflexivity].
  exfalso.
  apply andb_true_iff in E6; destruct E6 as [_ HF].
  assert (Hchain : existsb (fun D => negb (is_loop_b D)) (C :: G) = true).
  { rewrite <- negb_forallb, EL; reflexivity. }
  apply existsb_exists in Hchain; destruct Hchain as [D [HD HDn]].
  rewrite forallb_forall in HF; specialize (HF D HD).
  apply negb_true_iff in HDn; rewrite HDn in HF; simpl in HF.
  assert (Hex : existsb is_3chain_b (C :: G) = true)
    by (apply existsb_exists; exists D; split; assumption).
  congruence.
Qed.

(** Without three-chains the size and the controlled value agree modulo
    four. *)
Theorem size_cval_mod4 :
  forall G,
    existsb is_3chain_b G = false ->
    exists q, Z.of_nat (size G) - cval G = 4 * q.
Proof.
  intros G H.
  destruct (handsum_even G) as [m Hm].
  pose proof (size_minus_cbase G) as Hs.
  rewrite Hm in Hs.
  unfold cval.
  destruct (tb_no_three_chain G H) as [E | [E | E]]; rewrite E.
  - exists (Z.of_nat m); rewrite Nat2Z.inj_mul in Hs; lia.
  - exists (Z.of_nat m - 1); rewrite Nat2Z.inj_mul in Hs; lia.
  - exists (Z.of_nat m - 2); rewrite Nat2Z.inj_mul in Hs; lia.
Qed.

(** * Upper bound *)

(** No endgame is worth more than every box in it. *)
Theorem value_le_size : forall G, wf G -> value G <= Z.of_nat (size G).
Proof.
  assert (Haux : forall n G, (length G <= n)%nat -> wf G ->
            value G <= Z.of_nat (size G)).
  { induction n as [|n IH]; intros G Hn HG.
    - assert (HGnil : G = []) by (destruct G; simpl in Hn; [reflexivity | lia]).
      subst G; rewrite value_nil; simpl; lia.
    - destruct (list_eq_dec comp_eq_dec G []) as [-> | HNil];
        [rewrite value_nil; simpl; lia|].
      destruct (value_attained G HNil) as [p [Hp Hval]].
      pose proof (selections_size G p Hp) as Hsz.
      pose proof (selections_length G p Hp) as Hlen.
      pose proof (selections_wf G p HG Hp) as [HwC Hwrest].
      pose proof (value_nonneg (snd p) Hwrest) as Hpos.
      assert (Hrec : value (snd p) <= Z.of_nat (size (snd p)))
        by (apply IH; [lia | exact Hwrest]).
      assert (Hh : (1 <= hand (fst p))%nat) by (destruct (fst p); simpl; lia).
      rewrite Hval; unfold value_open; rewrite vopen_max.
      apply Z.max_lub; rewrite <- Hsz, Nat2Z.inj_add; lia. }
  intros G HG; apply (Haux (length G)); [lia | exact HG].
Qed.

(** So the value of an endgame lies between the controlled value and the
    number of boxes still on the board. *)
Corollary value_between :
  forall G, wf G -> cval G <= value G <= Z.of_nat (size G).
Proof.
  intros G HG; split; [apply cval_le_value | apply value_le_size]; exact HG.
Qed.

(** * The value depends only on the multiset of components *)

(** Every selection of a position transfers along a permutation. *)
Lemma selections_transfer :
  forall G H p,
    Permutation G H -> In p (selections G) ->
    exists q, In q (selections H) /\
              fst q = fst p /\ Permutation (snd q) (snd p).
Proof.
  intros G H p HP Hp.
  pose proof (selections_perm G p Hp) as Hperm.
  assert (HpH : Permutation (fst p :: snd p) H)
    by (eapply Permutation_trans; [exact Hperm | exact HP]).
  assert (HinH : In (fst p) H)
    by (eapply Permutation_in; [exact HpH | left; reflexivity]).
  destruct (In_selections H (fst p) HinH) as [rest' Hrest'].
  exists (fst p, rest'); simpl.
  split; [exact Hrest'|]; split; [reflexivity|].
  pose proof (selections_perm H (fst p, rest') Hrest') as Hperm'; simpl in Hperm'.
  apply (Permutation_cons_inv (a := fst p)).
  eapply Permutation_trans; [exact Hperm' | apply Permutation_sym; exact HpH].
Qed.

Lemma value_perm_le :
  forall n G H,
    (length G <= n)%nat -> Permutation G H -> value G <= value H.
Proof.
  induction n as [|n IH]; intros G H Hn HP.
  - assert (HG : G = []) by (destruct G; simpl in Hn; [reflexivity | lia]).
    subst G; apply Permutation_nil in HP; subst H; lia.
  - destruct (list_eq_dec comp_eq_dec H []) as [-> | HNil].
    + apply Permutation_sym, Permutation_nil in HP; subst G; lia.
    + destruct (value_attained H HNil) as [p [Hp Hval]].
      destruct (selections_transfer H G p (Permutation_sym HP) Hp)
        as [q [Hq [Hfst Hsnd]]].
      pose proof (selections_length G q Hq) as HlG.
      pose proof (selections_length H p Hp) as HlH.
      pose proof (Permutation_length HP) as Hlen.
      assert (Hqp : value (snd q) = value (snd p)).
      { apply Z.le_antisymm.
        - apply (IH (snd q)); [lia | exact Hsnd].
        - apply (IH (snd p)); [lia | apply Permutation_sym; exact Hsnd]. }
      eapply Z.le_trans; [apply (value_le_open G q Hq)|].
      unfold value_open; rewrite Hfst, Hqp, Hval; reflexivity.
Qed.

(** Reordering the components changes nothing. *)
Theorem value_perm : forall G H, Permutation G H -> value G = value H.
Proof.
  intros G H HP; apply Z.le_antisymm.
  - apply (value_perm_le (length G)); [lia | exact HP].
  - apply (value_perm_le (length H)); [lia | apply Permutation_sym; exact HP].
Qed.

Lemma cbase_perm : forall G H, Permutation G H -> cbase G = cbase H.
Proof.
  intros G H HP; induction HP; simpl; try lia; congruence.
Qed.

Theorem cval_perm : forall G H, Permutation G H -> cval G = cval H.
Proof.
  intros G H HP; unfold cval.
  rewrite (cbase_perm G H HP), (tb_perm G H HP); reflexivity.
Qed.

(** * Positions whose components are all large *)

(** A component is large when its length is at least twice its handout: a
    chain of four or more, or a loop of eight or more. Exactly the three-
    chains, four-loops and six-loops fail this. *)
Definition big (C : comp) : Prop := (2 * hand C <= csize C)%nat.

Definition allbig (G : position) : Prop := Forall big G.

Lemma big_weight : forall C, big C -> 0 <= weight C.
Proof. intros C H; unfold big, weight in *; lia. Qed.

Lemma allbig_cbase : forall G, allbig G -> 0 <= cbase G.
Proof.
  induction G as [|C G IH]; intros H; [reflexivity|].
  inversion H as [|? ? HC HG]; subst.
  rewrite cbase_cons.
  pose proof (big_weight C HC); pose proof (IH HG); lia.
Qed.

Lemma tb_all_loops :
  forall G, G <> [] -> forallb is_loop_b G = true -> tb G = 8.
Proof.
  intros [|C G] H HL; [contradiction|].
  rewrite tb_cons_form, HL; reflexivity.
Qed.

(** A chain that is not a three-chain forces the bonus down to four. *)
Lemma tb_long_chain :
  forall G D,
    In D G -> is_loop_b D = false -> is_3chain_b D = false -> tb G = 4.
Proof.
  intros [|C G] D HD HL H3; [destruct HD|].
  rewrite tb_cons_form.
  assert (HFL : forallb is_loop_b (C :: G) = false).
  { destruct (forallb is_loop_b (C :: G)) eqn:E; [|reflexivity].
    rewrite forallb_forall in E; specialize (E D HD); congruence. }
  assert (HF6 : forallb (fun X => is_loop_b X || is_3chain_b X)%bool (C :: G)
                = false).
  { destruct (forallb (fun X => is_loop_b X || is_3chain_b X)%bool (C :: G))
      eqn:E; [|reflexivity].
    rewrite forallb_forall in E; specialize (E D HD).
    rewrite HL, H3 in E; simpl in E; congruence. }
  rewrite HFL, HF6, andb_false_r; reflexivity.
Qed.

Lemma wf_perm : forall G H, Permutation G H -> wf G -> wf H.
Proof.
  intros G H HP HG; unfold wf in *; rewrite Forall_forall in *.
  intros x Hx; apply HG.
  eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hx].
Qed.

Lemma allbig_perm : forall G H, Permutation G H -> allbig G -> allbig H.
Proof.
  intros G H HP HG; unfold allbig in *; rewrite Forall_forall in *.
  intros x Hx; apply HG.
  eapply Permutation_in; [apply Permutation_sym; exact HP | exact Hx].
Qed.

(** The inductive step: if the opened component leaves the bonus alone and
    what remains is worth at least the handout, then opening it realises the
    controlled value. *)
Lemma value_step_eq :
  forall G p,
    wf G -> In p (selections G) ->
    tb (fst p :: snd p) = tb (snd p) ->
    Z.of_nat (hand (fst p)) <= cval (snd p) ->
    value (snd p) = cval (snd p) ->
    value G = cval G.
Proof.
  intros G p HG Hp Htb Hhand Hrec.
  pose proof (selections_cval G p Hp) as Hcv.
  rewrite Htb in Hcv.
  assert (HcG : cval G = weight (fst p) + cval (snd p))
    by (unfold cval in *; lia).
  apply Z.le_antisymm.
  - eapply Z.le_trans; [apply (value_le_open G p Hp)|].
    unfold value_open; rewrite Hrec, vopen_max.
    apply Z.max_lub.
    + unfold weight in HcG; lia.
    + unfold weight in HcG; lia.
  - apply cval_le_value; exact HG.
Qed.

(** For a position of large components the value is the controlled value. *)
Theorem value_allbig :
  forall G, wf G -> allbig G -> G <> [] -> value G = cval G.
Proof.
  assert (Haux : forall n G, (length G <= n)%nat ->
            wf G -> allbig G -> G <> [] -> value G = cval G).
  { induction n as [|n IH]; intros G Hn HG HB HNil.
    - exfalso; apply HNil; destruct G; [reflexivity | simpl in Hn; lia].
    - destruct G as [|A G0]; [contradiction|].
      destruct G0 as [|B G1]; [apply value_single_cval|].
      (* at least two components: choose a component to keep in front *)
      destruct (existsb (fun X => negb (is_loop_b X)) (A :: B :: G1)) eqn:Echain.
      + (* some component is a chain; it is long because the position is
           large, so it pins the bonus at four *)
        apply existsb_exists in Echain; destruct Echain as [D [HD HDn]].
        apply negb_true_iff in HDn.
        assert (HbD : big D).
        { unfold allbig in HB; rewrite Forall_forall in HB; apply HB; exact HD. }
        assert (HD3 : is_3chain_b D = false).
        { destruct D as [m | m]; [|reflexivity].
          unfold big in HbD; simpl in HbD.
          destruct m as [|[|[|[|m]]]]; simpl; try reflexivity; lia. }
        destruct (In_selections (A :: B :: G1) D HD) as [rest0 Hsel0].
        pose proof (selections_perm (A :: B :: G1) (D, rest0) Hsel0) as Hperm;
          simpl in Hperm.
        assert (Hlen0 : length rest0 = S (length G1)).
        { pose proof (selections_length (A :: B :: G1) (D, rest0) Hsel0) as HL;
            simpl in HL; lia. }
        destruct rest0 as [|E rest1]; [simpl in Hlen0; lia|].
        assert (HwfP : wf (D :: E :: rest1))
          by (apply (wf_perm (A :: B :: G1)); [apply Permutation_sym; exact Hperm
                                              | exact HG]).
        assert (HbigP : allbig (D :: E :: rest1))
          by (apply (allbig_perm (A :: B :: G1));
              [apply Permutation_sym; exact Hperm | exact HB]).
        rewrite <- (value_perm (D :: E :: rest1) (A :: B :: G1) Hperm),
                <- (cval_perm (D :: E :: rest1) (A :: B :: G1) Hperm).
        set (p := (E, D :: rest1)).
        assert (Hp : In p (selections (D :: E :: rest1))).
        { simpl; right.
          apply (in_map (fun q => (fst q, D :: snd q))
                        (selections (E :: rest1)) (E, rest1)).
          left; reflexivity. }
        apply (value_step_eq _ p HwfP Hp).
        * simpl fst; simpl snd.
          rewrite (tb_long_chain (E :: D :: rest1) D) by (auto; right; left; auto).
          rewrite (tb_long_chain (D :: rest1) D) by (auto; left; auto).
          reflexivity.
        * simpl fst; simpl snd.
          assert (Hcb : 0 <= cbase (D :: rest1)).
          { apply allbig_cbase.
            inversion HbigP as [|? ? Hb1D HbER]; subst.
            inversion HbER as [|? ? HbE Hb1]; subst.
            constructor; assumption. }
          assert (Htb4 : tb (D :: rest1) = 4)
            by (apply (tb_long_chain _ D); auto; left; auto).
          unfold cval; rewrite Htb4.
          destruct E as [m | m]; simpl hand; lia.
        * simpl snd.
          apply IH; [simpl in Hn, Hlen0 |- *; lia | | | discriminate].
          -- inversion HwfP as [|? ? HwD HwER]; subst.
             inversion HwER as [|? ? HwE Hw1]; subst.
             constructor; assumption.
          -- inversion HbigP as [|? ? Hb2D HbER]; subst.
             inversion HbER as [|? ? HbE Hb1]; subst.
             constructor; assumption.
      + (* every component is a loop *)
        assert (HL : forallb is_loop_b (A :: B :: G1) = true).
        { rewrite <- negb_false_iff, negb_forallb; exact Echain. }
        set (p := (A, B :: G1)).
        assert (Hp : In p (selections (A :: B :: G1)))
          by (simpl; left; reflexivity).
        apply (value_step_eq _ p HG Hp).
        * simpl fst; simpl snd.
          rewrite (tb_all_loops (A :: B :: G1)) by (discriminate || exact HL).
          rewrite (tb_all_loops (B :: G1)); [reflexivity | discriminate |].
          simpl in HL; apply andb_true_iff in HL; tauto.
        * simpl fst; simpl snd.
          assert (Hcb : 0 <= cbase (B :: G1))
            by (apply allbig_cbase; inversion HB; assumption).
          assert (Htb8 : tb (B :: G1) = 8).
          { apply tb_all_loops; [discriminate|].
            simpl in HL; apply andb_true_iff in HL; tauto. }
          unfold cval; rewrite Htb8.
          destruct A as [m | m]; simpl hand; lia.
        * simpl snd.
          apply IH; [simpl in Hn |- *; lia | | | discriminate].
          -- inversion HG; assumption.
          -- inversion HB; assumption. }
  intros G HG HB HNil; apply (Haux (length G)); [lia | exact HG | exact HB | exact HNil].
Qed.

(** * Opening a component whose demand the position can afford *)

(** The demand of a component is its length less its handout: one for a
    three-chain, zero for a four-loop, two for a four-chain or a six-loop. *)
Definition demand (C : comp) : Z :=
  Z.of_nat (csize C) - Z.of_nat (hand C).

Lemma value_step_demand :
  forall G p,
    wf G -> In p (selections G) ->
    tb (fst p :: snd p) = tb (snd p) ->
    demand (fst p) <= cval G ->
    value (snd p) = cval (snd p) ->
    value G = cval G.
Proof.
  intros G p HG Hp Htb Hd Hrec.
  apply (value_step_eq G p HG Hp Htb); [|exact Hrec].
  pose proof (selections_cval G p Hp) as Hcv.
  rewrite Htb in Hcv.
  unfold cval, demand, weight in *; lia.
Qed.

(** A component that is not large is a three-chain, a four-loop or a
    six-loop, and each of those has demand at most two. *)
Lemma small_demand :
  forall C, wf_comp C -> ~ big C -> demand C <= 2.
Proof.
  intros [m | m] Hwf Hb; unfold big, demand in *; simpl in *.
  - lia.
  - destruct Hwf as [Hge Hev].
    apply Nat.even_spec in Hev; destruct Hev as [k Hk].
    lia.
Qed.

Definition bigb (C : comp) : bool := Nat.leb (2 * hand C) (csize C).

Lemma bigb_spec : forall C, bigb C = true <-> big C.
Proof. intros C; unfold bigb, big; apply Nat.leb_le. Qed.

Lemma not_allbig_small :
  forall G,
    forallb bigb G = false -> exists C, In C G /\ ~ big C.
Proof.
  intros G H.
  assert (Hex : existsb (fun C => negb (bigb C)) G = true)
    by (rewrite <- negb_forallb, H; reflexivity).
  apply existsb_exists in Hex; destruct Hex as [C [HC Hn]].
  exists C; split; [exact HC|].
  intros Hb; apply negb_true_iff in Hn.
  rewrite (proj2 (bigb_spec C) Hb) in Hn; discriminate.
Qed.

Lemma allbig_of_forallb :
  forall G, forallb bigb G = true -> allbig G.
Proof.
  intros G H; unfold allbig; rewrite Forall_forall.
  rewrite forallb_forall in H.
  intros x Hx; apply bigb_spec, H, Hx.
Qed.

(** * Uniform families *)

Lemma tb_no_loops :
  forall G,
    G <> [] -> existsb is_loop_b G = false -> tb G = 4.
Proof.
  intros [|C G] H HE; [contradiction|].
  rewrite tb_cons_form.
  assert (HFL : forallb is_loop_b (C :: G) = false).
  { destruct (forallb is_loop_b (C :: G)) eqn:E; [|reflexivity].
    simpl in E, HE; apply andb_true_iff in E; destruct E as [E _].
    rewrite E in HE; discriminate. }
  rewrite HFL, HE; reflexivity.
Qed.

(** A position of chains alone is worth its controlled value once that value
    reaches two. *)
Theorem value_all_chains :
  forall G,
    wf G -> G <> [] -> existsb is_loop_b G = false ->
    2 <= cval G -> value G = cval G.
Proof.
  assert (Haux : forall n G, (length G <= n)%nat ->
            wf G -> G <> [] -> existsb is_loop_b G = false ->
            2 <= cval G -> value G = cval G).
  { induction n as [|n IH]; intros G Hn HG HNil HE Hc.
    - exfalso; apply HNil; destruct G; [reflexivity | simpl in Hn; lia].
    - destruct G as [|A G0]; [contradiction|].
      destruct G0 as [|B G1]; [apply value_single_cval|].
      destruct (forallb bigb (A :: B :: G1)) eqn:EB.
      { apply value_allbig; [exact HG | apply allbig_of_forallb; exact EB
                            | discriminate]. }
      destruct (not_allbig_small _ EB) as [S [HS Hns]].
      destruct (In_selections (A :: B :: G1) S HS) as [rest Hsel].
      pose proof (selections_perm (A :: B :: G1) (S, rest) Hsel) as Hperm;
        simpl in Hperm.
      pose proof (selections_length (A :: B :: G1) (S, rest) Hsel) as Hlen;
        simpl in Hlen.
      pose proof (selections_wf (A :: B :: G1) (S, rest) HG Hsel) as [HwS Hwr];
        simpl in HwS, Hwr.
      assert (HrNil : rest <> [])
        by (destruct rest; simpl in Hlen; [lia | discriminate]).
      assert (HEr : existsb is_loop_b rest = false).
      { destruct (existsb is_loop_b rest) eqn:E; [|reflexivity].
        exfalso; apply existsb_exists in E; destruct E as [x [Hx Hxl]].
        assert (Hin : In x (A :: B :: G1)).
        { eapply Permutation_in; [exact Hperm | right; exact Hx]. }
        assert (Hbad : existsb is_loop_b (A :: B :: G1) = true).
        { apply (proj2 (existsb_exists is_loop_b (A :: B :: G1))).
          exists x; split; [exact Hin | exact Hxl]. }
        congruence. }
      assert (HESr : existsb is_loop_b (S :: rest) = false).
      { rewrite (existsb_perm is_loop_b _ _ Hperm); exact HE. }
      apply (value_step_demand _ (S, rest) HG Hsel).
      + simpl fst; simpl snd.
        rewrite (tb_no_loops (S :: rest)) by (discriminate || exact HESr).
        rewrite (tb_no_loops rest) by (exact HrNil || exact HEr).
        reflexivity.
      + simpl fst.
        pose proof (small_demand S HwS Hns); lia.
      + simpl snd.
        apply IH; [simpl in Hn, Hlen; lia | exact Hwr | exact HrNil | exact HEr |].
        pose proof (selections_cval (A :: B :: G1) (S, rest) Hsel) as Hcv;
          cbn [fst snd] in Hcv.
        rewrite (tb_no_loops (S :: rest)) in Hcv by (discriminate || exact HESr).
        pose proof (small_demand S HwS Hns) as Hsd.
        assert (Hh : (2 <= hand S)%nat) by (destruct S; simpl; lia).
        unfold cval; rewrite (tb_no_loops rest) by (exact HrNil || exact HEr).
        unfold cval in Hcv, Hc; unfold demand, weight in *; lia. }
  intros G HG HNil HE Hc; apply (Haux (length G));
    [lia | exact HG | exact HNil | exact HE | exact Hc].
Qed.

(** And so is a position of loops alone. *)
Theorem value_all_loops :
  forall G,
    wf G -> G <> [] -> forallb is_loop_b G = true ->
    2 <= cval G -> value G = cval G.
Proof.
  assert (Haux : forall n G, (length G <= n)%nat ->
            wf G -> G <> [] -> forallb is_loop_b G = true ->
            2 <= cval G -> value G = cval G).
  { induction n as [|n IH]; intros G Hn HG HNil HL Hc.
    - exfalso; apply HNil; destruct G; [reflexivity | simpl in Hn; lia].
    - destruct G as [|A G0]; [contradiction|].
      destruct G0 as [|B G1]; [apply value_single_cval|].
      destruct (forallb bigb (A :: B :: G1)) eqn:EB.
      { apply value_allbig; [exact HG | apply allbig_of_forallb; exact EB
                            | discriminate]. }
      destruct (not_allbig_small _ EB) as [S [HS Hns]].
      destruct (In_selections (A :: B :: G1) S HS) as [rest Hsel].
      pose proof (selections_perm (A :: B :: G1) (S, rest) Hsel) as Hperm;
        simpl in Hperm.
      pose proof (selections_length (A :: B :: G1) (S, rest) Hsel) as Hlen;
        simpl in Hlen.
      pose proof (selections_wf (A :: B :: G1) (S, rest) HG Hsel) as [HwS Hwr];
        simpl in HwS, Hwr.
      assert (HrNil : rest <> [])
        by (destruct rest; simpl in Hlen; [lia | discriminate]).
      assert (HLSr : forallb is_loop_b (S :: rest) = true)
        by (rewrite (forallb_perm is_loop_b _ _ Hperm); exact HL).
      assert (HLr : forallb is_loop_b rest = true)
        by (simpl in HLSr; apply andb_true_iff in HLSr; tauto).
      apply (value_step_demand _ (S, rest) HG Hsel).
      + simpl fst; simpl snd.
        rewrite (tb_all_loops (S :: rest)) by (discriminate || exact HLSr).
        rewrite (tb_all_loops rest) by (exact HrNil || exact HLr).
        reflexivity.
      + simpl fst.
        pose proof (small_demand S HwS Hns); lia.
      + simpl snd.
        apply IH; [simpl in Hn, Hlen; lia | exact Hwr | exact HrNil | exact HLr |].
        pose proof (selections_cval (A :: B :: G1) (S, rest) Hsel) as Hcv;
          cbn [fst snd] in Hcv.
        rewrite (tb_all_loops (S :: rest)) in Hcv by (discriminate || exact HLSr).
        pose proof (small_demand S HwS Hns) as Hsd.
        assert (Hh : (2 <= hand S)%nat) by (destruct S; simpl; lia).
        unfold cval; rewrite (tb_all_loops rest) by (exact HrNil || exact HLr).
        unfold cval in Hcv, Hc; unfold demand, weight in *; lia. }
  intros G HG HNil HL Hc; apply (Haux (length G));
    [lia | exact HG | exact HNil | exact HL | exact Hc].
Qed.

(** * Machinery for the general equality *)

(** Opening the component that stands at the head. *)
Lemma value_step_head :
  forall C rest,
    wf (C :: rest) ->
    tb (C :: rest) = tb rest ->
    demand C <= cval (C :: rest) ->
    value rest = cval rest ->
    value (C :: rest) = cval (C :: rest).
Proof.
  intros C rest Hwf Htb Hd Hrec.
  apply (value_step_demand (C :: rest) (C, rest) Hwf);
    [simpl; left; reflexivity | exact Htb | exact Hd | exact Hrec].
Qed.

(** Transporting the equality along a permutation. *)
Lemma value_via_perm :
  forall G H, Permutation G H -> value H = cval H -> value G = cval G.
Proof.
  intros G H HP Heq.
  rewrite (value_perm G H HP), (cval_perm G H HP); exact Heq.
Qed.

Lemma weight_of_small : forall C, demand C <= 2 -> weight C <= 0.
Proof.
  intros C H; unfold demand, weight in *.
  assert (2 <= Z.of_nat (hand C)) by (destruct C; simpl; lia).
  lia.
Qed.

(** Removing a component whose weight is not positive leaves the controlled
    value at least two, when the bonus is unchanged. *)
Lemma cval_rest_ge2 :
  forall C rest,
    tb (C :: rest) = tb rest ->
    2 <= cval (C :: rest) ->
    weight C <= 0 ->
    2 <= cval rest.
Proof.
  intros C rest Htb Hc Hw.
  unfold cval in *; rewrite cbase_cons, Htb in Hc; lia.
Qed.

(** A position holding a loop, a three-chain, and nothing but loops and
    three-chains scores the six-bonus. *)
Lemma tb_six :
  forall G,
    existsb is_loop_b G = true ->
    existsb is_3chain_b G = true ->
    forallb (fun X => is_loop_b X || is_3chain_b X)%bool G = true ->
    tb G = 6.
Proof.
  intros [|C G] HL H3 HF; [discriminate|].
  rewrite tb_cons_form.
  assert (HFL : forallb is_loop_b (C :: G) = false).
  { destruct (forallb is_loop_b (C :: G)) eqn:E; [|reflexivity].
    exfalso.
    apply existsb_exists in H3; destruct H3 as [D [HD HD3]].
    rewrite forallb_forall in E; specialize (E D HD).
    destruct D as [m | m]; simpl in E, HD3; discriminate. }
  rewrite HFL, HL, HF; reflexivity.
Qed.

Lemma tb_eight_all_loops :
  forall G, G <> [] -> tb G = 8 -> forallb is_loop_b G = true.
Proof.
  intros [|C G] H HT; [contradiction|].
  rewrite tb_cons_form in HT.
  destruct (forallb is_loop_b (C :: G)) eqn:E; [reflexivity|].
  destruct (existsb is_loop_b (C :: G) &&
            forallb (fun D => is_loop_b D || is_3chain_b D) (C :: G))%bool;
    lia.
Qed.

(** A heap of three-chains with one loop in front, written with the loop
    anywhere. *)
Lemma tb_six_of_loops_and_three :
  forall L,
    forallb is_loop_b L = true -> L <> [] -> tb (Chain 3 :: L) = 6.
Proof.
  intros L HL HNil.
  apply tb_six.
  - destruct L as [|X L']; [contradiction|].
    simpl in HL |- *.
    apply andb_true_iff in HL; destruct HL as [HX _].
    rewrite HX; reflexivity.
  - simpl; reflexivity.
  - rewrite forallb_forall; intros x Hx.
    destruct Hx as [<- | Hx]; [reflexivity|].
    rewrite forallb_forall in HL; rewrite (HL x Hx); reflexivity.
Qed.

Lemma allbig_loops_cbase :
  forall L, forallb bigb L = true -> 0 <= cbase L.
Proof. intros L H; apply allbig_cbase, allbig_of_forallb; exact H. Qed.

Lemma value_step_head_eq :
  forall C rest,
    wf (C :: rest) ->
    tb (C :: rest) = tb rest ->
    Z.of_nat (hand C) <= cval rest ->
    value rest = cval rest ->
    value (C :: rest) = cval (C :: rest).
Proof.
  intros C rest Hwf Htb Hh Hrec.
  apply (value_step_eq (C :: rest) (C, rest) Hwf);
    [simpl; left; reflexivity | exact Htb | exact Hh | exact Hrec].
Qed.

Lemma tb_three_then_loop_threes :
  forall l k, tb (Chain 3 :: Loop l :: repeat (Chain 3) k) = 6.
Proof.
  intros l k; apply tb_six.
  - apply (proj2 (existsb_exists is_loop_b _)).
    exists (Loop l); split; [right; left; reflexivity | reflexivity].
  - apply (proj2 (existsb_exists is_3chain_b _)).
    exists (Chain 3); split; [left; reflexivity | reflexivity].
  - rewrite forallb_forall; intros x Hx.
    destruct Hx as [<- | [<- | Hx]]; [reflexivity | reflexivity |].
    apply repeat_spec in Hx; subst x; reflexivity.
Qed.

(** * One loop among three-chains *)

Lemma value_loop_plus_threes :
  forall k l,
    wf_comp (Loop l) ->
    2 <= cval (Loop l :: repeat (Chain 3) (S k)) ->
    value (Loop l :: repeat (Chain 3) (S k)) =
    cval (Loop l :: repeat (Chain 3) (S k)).
Proof.
  induction k as [|k IH]; intros l Hl Hc.
  - apply (value_via_perm _ [Chain 3; Loop l]); [apply perm_swap|].
    apply value_three_loop; destruct Hl as [H4 _]; exact H4.
  - apply (value_via_perm _ (Chain 3 :: Loop l :: repeat (Chain 3) (S k))).
    { simpl repeat; apply perm_swap. }
    assert (Htb1 : tb (Chain 3 :: Loop l :: repeat (Chain 3) (S k)) = 6)
      by apply tb_three_then_loop_threes.
    assert (Htb2 : tb (Loop l :: repeat (Chain 3) (S k)) = 6)
      by (apply tb_loop_three_chains; reflexivity).
    assert (Hwf : wf (Chain 3 :: Loop l :: repeat (Chain 3) (S k))).
    { constructor; [simpl; lia|].
      constructor; [exact Hl|].
      unfold wf; rewrite Forall_forall; intros x Hx.
      apply repeat_spec in Hx; subst x; simpl; lia. }
    assert (Hcperm : cval (Chain 3 :: Loop l :: repeat (Chain 3) (S k)) =
                     cval (Loop l :: repeat (Chain 3) (S (S k)))).
    { apply cval_perm; simpl repeat; apply perm_swap. }
    apply value_step_head; [exact Hwf | rewrite Htb1, Htb2; reflexivity | |].
    + unfold demand; simpl csize; simpl hand; lia.
    + apply IH; [exact Hl|].
      assert (Hstep : cval (Chain 3 :: Loop l :: repeat (Chain 3) (S k)) + 1 =
                      cval (Loop l :: repeat (Chain 3) (S k))).
      { unfold cval; rewrite cbase_cons, Htb1, Htb2, weight_chain; lia. }
      lia.
Qed.

(** * One three-chain among loops *)

Lemma value_three_plus_loops :
  forall n L,
    (length L <= n)%nat ->
    wf L -> forallb is_loop_b L = true -> L <> [] ->
    2 <= cval (Chain 3 :: L) ->
    value (Chain 3 :: L) = cval (Chain 3 :: L).
Proof.
  induction n as [|n IH]; intros L Hn HwL HL HNil Hc.
  - exfalso; apply HNil; destruct L; [reflexivity | simpl in Hn; lia].
  - destruct L as [|L1 L0]; [contradiction|].
    destruct L0 as [|L2 L''].
    + destruct L1 as [m | m]; [simpl in HL; discriminate|].
      apply value_three_loop.
      inversion HwL as [|? ? Hw1 _]; subst; destruct Hw1 as [H4 _]; exact H4.
    + assert (HwfC : wf (Chain 3 :: L1 :: L2 :: L''))
        by (constructor; [simpl; lia | exact HwL]).
      assert (Htb6 : tb (Chain 3 :: L1 :: L2 :: L'') = 6)
        by (apply tb_six_of_loops_and_three; [exact HL | discriminate]).
      destruct (forallb bigb (L1 :: L2 :: L'')) eqn:EB.
      * (* every loop is large: open the first one *)
        apply (value_via_perm _ (L1 :: Chain 3 :: L2 :: L'')); [apply perm_swap|].
        assert (HL2 : forallb is_loop_b (L2 :: L'') = true)
          by (simpl in HL; apply andb_true_iff in HL; tauto).
        assert (Htb6' : tb (Chain 3 :: L2 :: L'') = 6)
          by (apply tb_six_of_loops_and_three; [exact HL2 | discriminate]).
        assert (Htb6'' : tb (L1 :: Chain 3 :: L2 :: L'') = 6)
          by (rewrite <- Htb6; apply tb_perm; apply perm_swap).
        assert (Hcb : 0 <= cbase (L2 :: L'')).
        { apply allbig_loops_cbase.
          simpl in EB; apply andb_true_iff in EB; tauto. }
        apply value_step_head_eq.
        -- constructor; [inversion HwL; assumption|].
           constructor; [simpl; lia | inversion HwL; assumption].
        -- rewrite Htb6', Htb6''; reflexivity.
        -- unfold cval; rewrite Htb6', cbase_cons, weight_chain.
           destruct L1 as [m | m]; simpl hand; lia.
        -- apply IH.
           ++ simpl in Hn |- *; lia.
           ++ inversion HwL; assumption.
           ++ exact HL2.
           ++ discriminate.
           ++ unfold cval; rewrite Htb6', cbase_cons, weight_chain; lia.
      * (* some loop is small: open that one *)
        destruct (not_allbig_small _ EB) as [Sm [HS Hns]].
        destruct (In_selections (L1 :: L2 :: L'') Sm HS) as [restL HselL].
        pose proof (selections_perm (L1 :: L2 :: L'') (Sm, restL) HselL) as HpL;
          simpl in HpL.
        pose proof (selections_length (L1 :: L2 :: L'') (Sm, restL) HselL) as HlL;
          simpl in HlL.
        pose proof (selections_wf (L1 :: L2 :: L'') (Sm, restL) HwL HselL)
          as [HwS HwrL]; simpl in HwS, HwrL.
        assert (HrNil : restL <> [])
          by (destruct restL; simpl in HlL; [lia | discriminate]).
        assert (HLr : forallb is_loop_b restL = true).
        { rewrite forallb_forall in HL |- *; intros x Hx; apply HL.
          eapply Permutation_in; [exact HpL | right; exact Hx]. }
        assert (HSloop : is_loop_b Sm = true).
        { rewrite forallb_forall in HL; apply HL.
          eapply Permutation_in; [exact HpL | left; reflexivity]. }
        assert (Hperm2 : Permutation (Chain 3 :: L1 :: L2 :: L'')
                                     (Sm :: Chain 3 :: restL)).
        { eapply Permutation_trans;
            [apply perm_skip; apply Permutation_sym; exact HpL
            | apply perm_swap]. }
        apply (value_via_perm _ (Sm :: Chain 3 :: restL) Hperm2).
        assert (Htb6r : tb (Chain 3 :: restL) = 6)
          by (apply tb_six_of_loops_and_three; [exact HLr | exact HrNil]).
        assert (Htb6s : tb (Sm :: Chain 3 :: restL) = 6)
          by (rewrite <- Htb6; apply tb_perm; apply Permutation_sym; exact Hperm2).
        assert (Hd : demand Sm <= 2) by (apply small_demand; assumption).
        assert (Hw : weight Sm <= 0) by (apply weight_of_small; exact Hd).
        assert (HcS : 2 <= cval (Sm :: Chain 3 :: restL))
          by (rewrite <- (cval_perm _ _ Hperm2); exact Hc).
        apply value_step_head.
        -- constructor; [exact HwS|].
           constructor; [simpl; lia | exact HwrL].
        -- rewrite Htb6r, Htb6s; reflexivity.
        -- lia.
        -- apply IH.
           ++ simpl in Hn, HlL |- *; lia.
           ++ exact HwrL.
           ++ exact HLr.
           ++ exact HrNil.
           ++ apply (cval_rest_ge2 Sm (Chain 3 :: restL));
                [rewrite Htb6r, Htb6s; reflexivity | exact HcS | exact Hw].
Qed.

(** * Where the terminal bonus can fall *)

Lemma tb_values : forall G, G <> [] -> tb G = 4 \/ tb G = 6 \/ tb G = 8.
Proof.
  intros [|C G] H; [contradiction|].
  rewrite tb_cons_form.
  destruct (forallb is_loop_b (C :: G)); [right; right; reflexivity|].
  destruct (existsb is_loop_b (C :: G) &&
            forallb (fun D => is_loop_b D || is_3chain_b D) (C :: G))%bool;
    [right; left | left]; reflexivity.
Qed.

Lemma tb_six_inv :
  forall G,
    tb G = 6 ->
    existsb is_loop_b G = true /\
    forallb (fun X => is_loop_b X || is_3chain_b X)%bool G = true.
Proof.
  intros [|C G] H; [rewrite tb_nil in H; lia|].
  rewrite tb_cons_form in H.
  destruct (forallb is_loop_b (C :: G)); [lia|].
  destruct (existsb is_loop_b (C :: G) &&
            forallb (fun D => is_loop_b D || is_3chain_b D) (C :: G))%bool
    eqn:E; [|lia].
  apply andb_true_iff in E; exact E.
Qed.

Lemma tb_four_inv :
  forall G,
    G <> [] -> tb G = 4 ->
    (existsb is_loop_b G &&
     forallb (fun X => is_loop_b X || is_3chain_b X)%bool G)%bool = false.
Proof.
  intros [|C G] HN H; [contradiction|].
  rewrite tb_cons_form in H.
  destruct (forallb is_loop_b (C :: G)); [lia|].
  destruct (existsb is_loop_b (C :: G) &&
            forallb (fun D => is_loop_b D || is_3chain_b D) (C :: G))%bool
    eqn:E; [lia | reflexivity].
Qed.

(** Putting a component in front can only lower the bonus by placing a
    three-chain on a heap of loops. *)
Lemma tb_decrease_shape :
  forall C rest,
    rest <> [] -> wf_comp C -> ~ big C ->
    tb (C :: rest) < tb rest ->
    C = Chain 3 /\ forallb is_loop_b rest = true.
Proof.
  intros C rest HrNil HwC HnbC Hdec.
  assert (Hor : (is_loop_b C || is_3chain_b C)%bool = true).
  { destruct C as [m | m]; [|reflexivity].
    unfold big in HnbC; simpl in HnbC, HwC.
    assert (Hm3 : m = 3%nat) by lia; subst m; reflexivity. }
  assert (HLr : forallb is_loop_b rest = true).
  { destruct (forallb is_loop_b rest) eqn:E; [reflexivity|].
    exfalso.
    destruct (tb_values rest HrNil) as [H4 | [H6 | H8]].
    - pose proof (tb_pos (C :: rest) ltac:(discriminate)); lia.
    - assert (Htb4 : tb (C :: rest) = 4).
      { destruct (tb_values (C :: rest) ltac:(discriminate)) as [X|[X|X]];
          lia. }
      destruct (tb_six_inv rest H6) as [Hex Hall].
      pose proof (tb_four_inv (C :: rest) ltac:(discriminate) Htb4) as Hf.
      change (existsb is_loop_b (C :: rest))
        with (is_loop_b C || existsb is_loop_b rest)%bool in Hf.
      change (forallb (fun X => is_loop_b X || is_3chain_b X)%bool (C :: rest))
        with ((is_loop_b C || is_3chain_b C) &&
              forallb (fun X => is_loop_b X || is_3chain_b X)%bool rest)%bool
        in Hf.
      rewrite Hex, Hall, Hor, orb_true_r in Hf; simpl in Hf; discriminate.
    - pose proof (tb_eight_all_loops rest HrNil H8); congruence. }
  split; [|exact HLr].
  destruct C as [m | m].
  - unfold big in HnbC; simpl in HnbC, HwC.
    assert (Hm3 : m = 3%nat) by lia; subst m; reflexivity.
  - exfalso.
    assert (HallL : forallb is_loop_b (Loop m :: rest) = true)
      by (simpl; exact HLr).
    rewrite (tb_all_loops (Loop m :: rest) ltac:(discriminate) HallL) in Hdec.
    rewrite (tb_all_loops rest HrNil HLr) in Hdec; lia.
Qed.

(** * Berlekamp and Scott: a controlled value of two or more is exact *)

Theorem value_cval_ge2 :
  forall G, wf G -> 2 <= cval G -> value G = cval G.
Proof.
  assert (Haux : forall n G, (length G <= n)%nat -> wf G -> 2 <= cval G ->
                   value G = cval G).
  { induction n as [|n IH]; intros G Hn HG Hc.
    - exfalso.
      assert (HGnil : G = []) by (destruct G; simpl in Hn; [reflexivity | lia]).
      subst G; unfold cval in Hc; rewrite tb_nil, cbase_nil in Hc; lia.
    - destruct G as [|A G0].
      { exfalso; unfold cval in Hc; rewrite tb_nil, cbase_nil in Hc; lia. }
      destruct G0 as [|B G1]; [apply value_single_cval|].
      destruct (forallb bigb (A :: B :: G1)) eqn:EB.
      { apply value_allbig;
          [exact HG | apply allbig_of_forallb; exact EB | discriminate]. }
      destruct (not_allbig_small _ EB) as [Sm [HS Hns]].
      destruct (In_selections (A :: B :: G1) Sm HS) as [rest Hsel].
      pose proof (selections_perm (A :: B :: G1) (Sm, rest) Hsel) as Hperm;
        simpl in Hperm.
      pose proof (selections_length (A :: B :: G1) (Sm, rest) Hsel) as Hlen;
        simpl in Hlen.
      pose proof (selections_wf (A :: B :: G1) (Sm, rest) HG Hsel)
        as [HwS Hwr]; simpl in HwS, Hwr.
      apply (value_via_perm _ (Sm :: rest) (Permutation_sym Hperm)).
      assert (HwfSr : wf (Sm :: rest))
        by (apply (wf_perm (A :: B :: G1));
            [apply Permutation_sym; exact Hperm | exact HG]).
      assert (HcSr : 2 <= cval (Sm :: rest))
        by (rewrite (cval_perm (Sm :: rest) (A :: B :: G1) Hperm); exact Hc).
      assert (HrNil : rest <> [])
        by (destruct rest; simpl in Hlen; [lia | discriminate]).
      assert (Hd : demand Sm <= 2) by (apply small_demand; assumption).
      assert (Hw : weight Sm <= 0) by (apply weight_of_small; exact Hd).
      destruct (Z.lt_trichotomy (tb rest) (tb (Sm :: rest)))
        as [Hinc | [Heq | Hdec]].
      + (* the bonus rises: a loop over a heap of three-chains *)
        destruct (tb_increase_shape Sm rest HrNil Hinc) as [HSl H3].
        pose proof (all_3chains_repeat rest H3) as Hrep.
        destruct Sm as [m | m]; [discriminate|].
        destruct (length rest) as [|k] eqn:Elen.
        { exfalso; apply HrNil.
          destruct rest as [|x l]; [reflexivity | simpl in Elen; discriminate]. }
        rewrite Hrep.
        apply value_loop_plus_threes; [exact HwS|].
        rewrite <- Hrep; exact HcSr.
      + (* the bonus is unchanged: open the small component *)
        apply value_step_head;
          [exact HwfSr | symmetry; exact Heq | lia |].
        apply IH; [simpl in Hn, Hlen |- *; lia | exact Hwr |].
        apply (cval_rest_ge2 Sm rest (eq_sym Heq) HcSr Hw).
      + (* the bonus falls: a three-chain over a heap of loops *)
        destruct (tb_decrease_shape Sm rest HrNil HwS Hns Hdec) as [HSc HLr].
        subst Sm.
        apply (value_three_plus_loops (length rest) rest);
          [lia | exact Hwr | exact HLr | exact HrNil | exact HcSr]. }
  intros G HG Hc; apply (Haux (length G)); [lia | exact HG | exact Hc].
Qed.

(** * Consequences *)

(** A large controlled value is realised exactly. *)
Theorem value_gt4_of_cval_gt4 :
  forall G, wf G -> 4 < cval G -> 4 < value G.
Proof.
  intros G HG H; rewrite (value_cval_ge2 G HG) by lia; exact H.
Qed.

(** Under a controlled value of two or more, some opening realises it, and no
    opening does better. *)
Corollary opener_realises_cval :
  forall G,
    wf G -> 2 <= cval G -> G <> [] ->
    exists p, In p (selections G) /\ value_open p = cval G /\
              forall q, In q (selections G) -> cval G <= value_open q.
Proof.
  intros G HG Hc HNil.
  destruct (value_attained G HNil) as [p [Hp Hval]].
  exists p; split; [exact Hp | split].
  - rewrite <- Hval; apply value_cval_ge2; assumption.
  - intros q Hq.
    rewrite <- (value_cval_ge2 G HG Hc); apply value_le_open; exact Hq.
Qed.

(** The controlled value is exact on every position of two or more, so the
    controller's guaranteed score is the true margin there. *)
Corollary control_strategy_optimal :
  forall G, wf G -> 2 <= cval G -> cval G = value G.
Proof. intros G HG Hc; symmetry; apply value_cval_ge2; assumption. Qed.

(** * Three-chains and four-loops *)

(** The positions built from three-chains and four-loops alone. *)
Definition mix (t f : nat) : position :=
  repeat (Chain 3) t ++ repeat (Loop 4) f.

Lemma mix_chain_cons : forall t f, mix (S t) f = Chain 3 :: mix t f.
Proof. reflexivity. Qed.

Lemma mix_loop_perm :
  forall t f, Permutation (mix t (S f)) (Loop 4 :: mix t f).
Proof.
  intros t f; unfold mix; simpl repeat.
  apply Permutation_sym, Permutation_middle.
Qed.

Lemma mix_wf : forall t f, wf (mix t f).
Proof.
  intros t f; unfold wf, mix; rewrite Forall_forall; intros x Hx.
  apply in_app_or in Hx; destruct Hx as [Hx | Hx];
    apply repeat_spec in Hx; subst x; simpl; auto.
Qed.

Lemma mix_nonnil : forall t f, (0 < t + f)%nat -> mix t f <> [].
Proof.
  intros [|t] [|f] H; unfold mix; simpl; try lia; discriminate.
Qed.

Lemma In_mix : forall t f C, In C (mix t f) -> C = Chain 3 \/ C = Loop 4.
Proof.
  intros t f C H; unfold mix in H; apply in_app_or in H.
  destruct H as [H | H]; apply repeat_spec in H; auto.
Qed.

Lemma In_mix_chain : forall t f, In (Chain 3) (mix t f) -> t <> 0%nat.
Proof.
  intros [|t] f H Hc; [|discriminate].
  unfold mix in H; simpl in H.
  apply repeat_spec in H; discriminate.
Qed.

Lemma In_mix_loop : forall t f, In (Loop 4) (mix t f) -> f <> 0%nat.
Proof.
  intros t [|f] H Hc; [|discriminate].
  unfold mix in H; rewrite app_nil_r in H.
  apply repeat_spec in H; discriminate.
Qed.

(** Every option of a mixed position removes a three-chain or a four-loop. *)
Lemma selections_mix :
  forall t f p,
    In p (selections (mix t f)) ->
    (fst p = Chain 3 /\
     exists t', t = S t' /\ Permutation (snd p) (mix t' f)) \/
    (fst p = Loop 4 /\
     exists f', f = S f' /\ Permutation (snd p) (mix t f')).
Proof.
  intros t f p Hp.
  pose proof (selections_perm (mix t f) p Hp) as Hperm.
  pose proof (selections_In (mix t f) p Hp) as HIn.
  destruct (In_mix t f (fst p) HIn) as [HC | HC].
  - left; split; [exact HC|].
    rewrite HC in HIn.
    destruct t as [|t']; [exfalso; apply (In_mix_chain 0 f HIn); reflexivity|].
    exists t'; split; [reflexivity|].
    apply (Permutation_cons_inv (a := Chain 3)).
    rewrite <- mix_chain_cons.
    rewrite <- HC; exact Hperm.
  - right; split; [exact HC|].
    rewrite HC in HIn.
    destruct f as [|f']; [exfalso; apply (In_mix_loop t 0 HIn); reflexivity|].
    exists f'; split; [reflexivity|].
    apply (Permutation_cons_inv (a := Loop 4)).
    eapply Permutation_trans; [rewrite <- HC; exact Hperm |].
    apply mix_loop_perm.
Qed.

(** If every option is worth one of two amounts, and both occur, the value is
    the smaller. *)
Lemma value_two_options :
  forall G a b,
    G <> [] ->
    (forall p, In p (selections G) -> value_open p = a \/ value_open p = b) ->
    (exists p, In p (selections G) /\ value_open p = a) ->
    (exists p, In p (selections G) /\ value_open p = b) ->
    value G = Z.min a b.
Proof.
  intros G a b HNil Hall [pa [Hpa Ha]] [pb [Hpb Hb]].
  destruct (value_attained G HNil) as [p [Hp Hval]].
  pose proof (value_le_open G pa Hpa) as La; rewrite Ha in La.
  pose proof (value_le_open G pb Hpb) as Lb; rewrite Hb in Lb.
  destruct (Hall p Hp) as [E | E]; rewrite Hval, E; lia.
Qed.

(** The closed form of the table. *)
Definition v36 (t f : nat) : Z :=
  match t with
  | O => if Nat.even f then 0 else 4
  | S O => if Nat.even f then 3 else 1
  | _ => if Nat.even t then 2 else 1
  end.

Lemma value_mix_chain_option :
  forall t f p,
    fst p = Chain 3 -> Permutation (snd p) (mix t f) ->
    value_open p = vopen (Chain 3) (value (mix t f)).
Proof.
  intros t f [C rest] HC Hperm; cbn [fst snd] in HC, Hperm; subst C.
  unfold value_open; cbn [fst snd].
  rewrite (value_perm rest (mix t f) Hperm); reflexivity.
Qed.

Lemma value_mix_loop_option :
  forall t f p,
    fst p = Loop 4 -> Permutation (snd p) (mix t f) ->
    value_open p = vopen (Loop 4) (value (mix t f)).
Proof.
  intros t f [C rest] HC Hperm; cbn [fst snd] in HC, Hperm; subst C.
  unfold value_open; cbn [fst snd].
  rewrite (value_perm rest (mix t f) Hperm); reflexivity.
Qed.

Lemma vopen_chain3 : forall w, vopen (Chain 3) w = 1 + Z.abs (w - 2).
Proof. intros w; reflexivity. Qed.

Lemma vopen_loop4 : forall w, vopen (Loop 4) w = Z.abs (w - 4).
Proof. intros w; reflexivity. Qed.

(** The table of values for positions of three-chains and four-loops. *)
Lemma value_mix_aux :
  forall n t f, (t + f <= n)%nat -> value (mix t f) = v36 t f.
Proof.
  induction n as [|n IH]; intros t f Hn.
  - assert (Ht : t = 0%nat) by lia; assert (Hf : f = 0%nat) by lia.
    subst; reflexivity.
  - destruct t as [|t'].
    + destruct f as [|f']; [reflexivity|].
      assert (Hv : value (mix 0 (S f')) = vopen (Loop 4) (value (mix 0 f'))).
      { apply value_const_options; [apply mix_nonnil; simpl; lia|].
        intros p Hp.
        destruct (selections_mix 0 (S f') p Hp)
          as [[HC [t'' [Hc _]]] | [HC [f'' [Hf2 Hperm]]]]; [discriminate|].
        injection Hf2 as Hf2; subst f''.
        apply (value_mix_loop_option 0 f' (fst p, snd p) HC Hperm). }
      rewrite Hv, (IH 0%nat f') by (simpl; lia).
      rewrite vopen_loop4.
      change (v36 0 f') with (if Nat.even f' then 0 else 4).
      change (v36 0 (S f')) with (if Nat.even (S f') then 0 else 4).
      rewrite even_S; destruct (Nat.even f'); reflexivity.
    + destruct f as [|f'].
      * assert (Hv : value (mix (S t') 0) = vopen (Chain 3) (value (mix t' 0))).
        { apply value_const_options; [apply mix_nonnil; simpl; lia|].
          intros p Hp.
          destruct (selections_mix (S t') 0 p Hp)
            as [[HC [t'' [Ht2 Hperm]]] | [HC [f'' [Hf2 _]]]]; [|discriminate].
          injection Ht2 as Ht2; subst t''.
          apply (value_mix_chain_option t' 0 (fst p, snd p) HC Hperm). }
        rewrite Hv, (IH t' 0%nat) by (simpl; lia).
        rewrite vopen_chain3.
        destruct t' as [|[|t'']]; [reflexivity | reflexivity |].
        change (v36 (S (S t'')) 0)
          with (if Nat.even (S (S t'')) then 2 else 1).
        change (v36 (S (S (S t''))) 0)
          with (if Nat.even (S (S (S t''))) then 2 else 1).
        rewrite (even_S (S (S t''))).
        destruct (Nat.even (S (S t''))); reflexivity.
      * assert (HnilM : mix (S t') (S f') <> [])
          by (apply mix_nonnil; simpl; lia).
        assert (Hchain : In (Chain 3, mix t' (S f'))
                            (selections (mix (S t') (S f')))).
        { rewrite mix_chain_cons; simpl; left; reflexivity. }
        assert (HInL : In (Loop 4) (mix (S t') (S f'))).
        { unfold mix; apply in_or_app; right; simpl; left; reflexivity. }
        destruct (In_selections (mix (S t') (S f')) (Loop 4) HInL)
          as [restL HselL].
        assert (HpermL : Permutation restL (mix (S t') f')).
        { destruct (selections_mix (S t') (S f') (Loop 4, restL) HselL)
            as [[HC _] | [HC [f'' [Hf2 Hperm]]]]; [cbn in HC; discriminate|].
          cbn in Hperm; injection Hf2 as Hf2; subst f''; exact Hperm. }
        assert (Hval : value (mix (S t') (S f')) =
                       Z.min (vopen (Chain 3) (value (mix t' (S f'))))
                             (vopen (Loop 4) (value (mix (S t') f')))).
        { apply value_two_options; [exact HnilM | | |].
          - intros p Hp.
            destruct (selections_mix (S t') (S f') p Hp)
              as [[HC [t'' [Ht2 Hperm]]] | [HC [f'' [Hf2 Hperm]]]].
            + left; injection Ht2 as Ht2; subst t''.
              apply (value_mix_chain_option t' (S f') (fst p, snd p) HC Hperm).
            + right; injection Hf2 as Hf2; subst f''.
              apply (value_mix_loop_option (S t') f' (fst p, snd p) HC Hperm).
          - exists (Chain 3, mix t' (S f')); split; [exact Hchain|].
            apply (value_mix_chain_option t' (S f'));
              [reflexivity | apply Permutation_refl].
          - exists (Loop 4, restL); split; [exact HselL|].
            apply (value_mix_loop_option (S t') f');
              [reflexivity | exact HpermL]. }
        rewrite Hval.
        rewrite (IH t' (S f')) by (simpl; lia).
        rewrite (IH (S t') f') by (simpl; lia).
        rewrite vopen_chain3, vopen_loop4.
        destruct t' as [|[|t'']].
        -- change (v36 0 (S f')) with (if Nat.even (S f') then 0 else 4).
           change (v36 1 f') with (if Nat.even f' then 3 else 1).
           change (v36 1 (S f')) with (if Nat.even (S f') then 3 else 1).
           rewrite even_S; destruct (Nat.even f'); reflexivity.
        -- change (v36 1 (S f')) with (if Nat.even (S f') then 3 else 1).
           change (v36 2 f') with 2.
           change (v36 2 (S f')) with 2.
           rewrite even_S; destruct (Nat.even f'); reflexivity.
        -- change (v36 (S (S t'')) (S f'))
             with (if Nat.even (S (S t'')) then 2 else 1).
           change (v36 (S (S (S t''))) f')
             with (if Nat.even (S (S (S t''))) then 2 else 1).
           change (v36 (S (S (S t''))) (S f'))
             with (if Nat.even (S (S (S t''))) then 2 else 1).
           rewrite (even_S (S (S t''))).
           destruct (Nat.even (S (S t''))); reflexivity.
Qed.

Theorem value_mix : forall t f, value (mix t f) = v36 t f.
Proof. intros t f; apply (value_mix_aux (t + f)); lia. Qed.

(** * Comparing options *)

(** An option is worth at least the demand of the component it opens. *)
Lemma value_open_ge_demand :
  forall G p, In p (selections G) -> demand (fst p) <= value_open p.
Proof.
  intros G p Hp; unfold value_open, vopen, demand.
  pose proof (Z.abs_nonneg (value (snd p) - Z.of_nat (hand (fst p)))); lia.
Qed.

(** All options of a position share the parity of its box count. *)
Lemma value_open_parity :
  forall G p,
    In p (selections G) ->
    Z.even (value_open p) = Z.even (Z.of_nat (size G)).
Proof.
  intros G p Hp; unfold value_open.
  rewrite vopen_parity, Z.even_add, (value_parity (snd p)), <- Z.even_add.
  rewrite <- Nat2Z.inj_add, (selections_size G p Hp); reflexivity.
Qed.

(** A least option is the value. *)
Lemma value_of_min_option :
  forall G p,
    In p (selections G) ->
    (forall q, In q (selections G) -> value_open p <= value_open q) ->
    value G = value_open p.
Proof.
  intros G p Hp Hmin.
  assert (HNil : G <> []).
  { intros ->; simpl in Hp; destruct Hp. }
  destruct (value_attained G HNil) as [q [Hq Hval]].
  pose proof (value_le_open G p Hp) as H1.
  pose proof (Hmin q Hq) as H2.
  rewrite Hval in *; lia.
Qed.

(** * Small-component tests *)

Definition is_4loop_b (C : comp) : bool :=
  match C with Loop 4 => true | _ => false end.

Definition is_6loop_b (C : comp) : bool :=
  match C with Loop 6 => true | _ => false end.

Lemma is_4loop_eq : forall C, is_4loop_b C = true -> C = Loop 4.
Proof.
  intros [m | [|[|[|[|[|m]]]]]] H; simpl in H; try discriminate; reflexivity.
Qed.

Lemma is_6loop_eq : forall C, is_6loop_b C = true -> C = Loop 6.
Proof.
  intros [m | [|[|[|[|[|[|[|m]]]]]]]] H; simpl in H; try discriminate;
    reflexivity.
Qed.

(** Without three-chains and four-loops every component has weight at least
    minus two, with equality exactly at the six-loops. *)
Lemma weight_ge_of_no34 :
  forall C,
    wf_comp C -> is_3chain_b C = false -> is_4loop_b C = false ->
    -2 <= weight C.
Proof.
  intros [m | m] Hw H3 H4; unfold weight; simpl csize; simpl hand.
  - destruct m as [|[|[|[|m]]]]; try (simpl in Hw); try (simpl in H3);
      solve [ lia | discriminate ].
  - destruct Hw as [Hge Hev].
    destruct m as [|[|[|[|[|[|m]]]]]]; try (simpl in Hge); try (simpl in Hev);
      try (simpl in H4); solve [ lia | discriminate ].
Qed.

Lemma weight_6loop : weight (Loop 6) = -2.
Proof. reflexivity. Qed.

Lemma demand_of_no34 :
  forall C,
    wf_comp C -> is_3chain_b C = false -> is_4loop_b C = false ->
    2 <= demand C.
Proof.
  intros [m | m] Hw H3 H4; unfold demand; simpl csize; simpl hand.
  - destruct m as [|[|[|[|m]]]]; try (simpl in Hw); try (simpl in H3);
      solve [ lia | discriminate ].
  - destruct Hw as [Hge Hev].
    destruct m as [|[|[|[|[|[|m]]]]]]; try (simpl in Hge); try (simpl in Hev);
      try (simpl in H4); solve [ lia | discriminate ].
Qed.

(** * The value below a controlled value of two, without small components *)

Lemma filter_perm :
  forall (f : comp -> bool) G H,
    Permutation G H -> Permutation (filter f G) (filter f H).
Proof.
  intros f G H HP; induction HP; simpl.
  - apply Permutation_refl.
  - destruct (f x); [apply perm_skip; exact IHHP | exact IHHP].
  - destruct (f x), (f y); try apply perm_swap; apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

Definition count6 (G : position) : nat := length (filter is_6loop_b G).

Lemma count6_perm : forall G H, Permutation G H -> count6 G = count6 H.
Proof.
  intros G H HP; unfold count6.
  apply Permutation_length, filter_perm; exact HP.
Qed.

Lemma count6_cons :
  forall C G,
    count6 (C :: G) = (if is_6loop_b C then S (count6 G) else count6 G).
Proof. intros C G; unfold count6; simpl; destruct (is_6loop_b C); reflexivity. Qed.

Lemma count6_pos_In : forall G, (0 < count6 G)%nat -> In (Loop 6) G.
Proof.
  induction G as [|C G IH]; intros H; [unfold count6 in H; simpl in H; lia|].
  rewrite count6_cons in H.
  destruct (is_6loop_b C) eqn:E.
  - left; apply is_6loop_eq; exact E.
  - right; apply IH; lia.
Qed.

Lemma weight_nonneg_of_no346 :
  forall C,
    wf_comp C -> is_3chain_b C = false -> is_4loop_b C = false ->
    is_6loop_b C = false -> 0 <= weight C.
Proof.
  intros [m | m] Hw H3 H4 H6; unfold weight; simpl csize; simpl hand.
  - destruct m as [|[|[|[|m]]]]; try (simpl in Hw); try (simpl in H3);
      solve [ lia | discriminate ].
  - destruct Hw as [Hge Hev].
    destruct m as [|[|[|[|[|[|[|[|m]]]]]]]];
      try (simpl in Hge); try (simpl in Hev); try (simpl in H4);
      try (simpl in H6); solve [ lia | discriminate ].
Qed.

(** The six-loops are the only drag on the base weight. *)
Lemma cbase_ge_count6 :
  forall G,
    (forall C, In C G ->
       wf_comp C /\ is_3chain_b C = false /\ is_4loop_b C = false) ->
    - 2 * Z.of_nat (count6 G) <= cbase G.
Proof.
  induction G as [|C G IH]; intros Hall; [simpl; unfold count6; simpl; lia|].
  assert (HC : wf_comp C /\ is_3chain_b C = false /\ is_4loop_b C = false)
    by (apply Hall; left; reflexivity).
  destruct HC as [Hw [H3 H4]].
  assert (HG : forall D, In D G ->
            wf_comp D /\ is_3chain_b D = false /\ is_4loop_b D = false)
    by (intros D HD; apply Hall; right; exact HD).
  specialize (IH HG).
  rewrite cbase_cons, count6_cons.
  destruct (is_6loop_b C) eqn:E6.
  - rewrite (is_6loop_eq C E6), weight_6loop.
    rewrite Nat2Z.inj_succ; lia.
  - pose proof (weight_nonneg_of_no346 C Hw H3 H4 E6); lia.
Qed.

(** The value in the residue classes. *)
Definition w4z (z : Z) : Z :=
  if Z.eqb (z mod 4) 0 then 4
  else if Z.eqb (z mod 4) 1 then 3
  else if Z.eqb (z mod 4) 2 then 2
  else 3.

Lemma w4z_mod : forall a b, a mod 4 = b mod 4 -> w4z a = w4z b.
Proof. intros a b H; unfold w4z; rewrite H; reflexivity. Qed.

Lemma w4z_id_2_4 : forall c, 2 <= c <= 4 -> w4z c = c.
Proof.
  intros c H.
  assert (Hc : c = 2 \/ c = 3 \/ c = 4) by lia.
  destruct Hc as [-> | [-> | ->]]; reflexivity.
Qed.

Lemma w4z_range : forall z, 2 <= w4z z <= 4.
Proof.
  intros z; unfold w4z.
  destruct (Z.eqb (z mod 4) 0); [lia|].
  destruct (Z.eqb (z mod 4) 1); [lia|].
  destruct (Z.eqb (z mod 4) 2); lia.
Qed.

Lemma size_cval_w4z :
  forall G,
    existsb is_3chain_b G = false ->
    w4z (Z.of_nat (size G)) = w4z (cval G).
Proof.
  intros G H; destruct (size_cval_mod4 G H) as [q Hq].
  apply w4z_mod.
  replace (Z.of_nat (size G)) with (cval G + q * 4) by lia.
  apply Z_mod_plus_full.
Qed.

Lemma w4z_step6 : forall s, 2 + Z.abs (w4z (s - 6) - 4) = w4z s.
Proof.
  intros s.
  pose proof (Z.mod_pos_bound s 4 ltac:(lia)) as Hb.
  assert (Hsub : (s - 6) mod 4 = ((s mod 4) + 2) mod 4).
  { replace (s - 6) with (s + 2 + (-2) * 4) by lia.
    rewrite Z_mod_plus_full.
    rewrite Z.add_mod_idemp_l by lia; reflexivity. }
  unfold w4z; rewrite Hsub.
  assert (Hr : s mod 4 = 0 \/ s mod 4 = 1 \/ s mod 4 = 2 \/ s mod 4 = 3) by lia.
  destruct Hr as [H | [H | [H | H]]]; rewrite H; reflexivity.
Qed.

Lemma existsb_false_tail :
  forall (f : comp -> bool) C rest G,
    Permutation (C :: rest) G -> existsb f G = false -> existsb f rest = false.
Proof.
  intros f C rest G HP H.
  rewrite <- (existsb_perm f (C :: rest) G HP) in H.
  simpl in H; apply orb_false_iff in H; tauto.
Qed.

(** Removing a loop from a position with no three-chains leaves the bonus
    alone, provided something is left. *)
Lemma tb_remove_loop_no3 :
  forall C rest,
    is_loop_b C = true ->
    existsb is_3chain_b (C :: rest) = false ->
    rest <> [] ->
    tb (C :: rest) = tb rest.
Proof.
  intros C rest HC H3 HrNil.
  destruct (forallb is_loop_b rest) eqn:EL.
  - assert (HL : forallb is_loop_b (C :: rest) = true)
      by (simpl; rewrite HC; exact EL).
    rewrite (tb_all_loops (C :: rest) ltac:(discriminate) HL).
    rewrite (tb_all_loops rest HrNil EL); reflexivity.
  - assert (Hex : existsb (fun D => negb (is_loop_b D)) rest = true)
      by (rewrite <- negb_forallb, EL; reflexivity).
    apply existsb_exists in Hex; destruct Hex as [D [HD HDn]].
    apply negb_true_iff in HDn.
    assert (HD3 : is_3chain_b D = false).
    { destruct (is_3chain_b D) eqn:E3; [|reflexivity].
      exfalso.
      assert (Hbad : existsb is_3chain_b (C :: rest) = true).
      { apply (proj2 (existsb_exists is_3chain_b (C :: rest))).
        exists D; split; [right; exact HD | exact E3]. }
      congruence. }
    rewrite (tb_long_chain (C :: rest) D) by (auto; right; exact HD).
    rewrite (tb_long_chain rest D) by (auto; exact HD).
    reflexivity.
Qed.

Lemma vopen_loop6 : forall w, vopen (Loop 6) w = 2 + Z.abs (w - 4).
Proof. intros w; reflexivity. Qed.

Lemma vopen_chain4 : forall w, vopen (Chain 4) w = 2 + Z.abs (w - 2).
Proof. intros w; reflexivity. Qed.

Lemma even_eq_diff2 :
  forall a b, Z.even a = Z.even b -> a < b -> a + 2 <= b.
Proof.
  intros a b He Hlt.
  destruct (Z.even a) eqn:Ea.
  - assert (Eb : Z.even b = true) by (symmetry; exact He).
    apply Z.even_spec in Ea; destruct Ea as [k Hk].
    apply Z.even_spec in Eb; destruct Eb as [m Hm]; lia.
  - assert (Eb : Z.even b = false) by (symmetry; exact He).
    assert (Oa : Z.odd a = true) by (rewrite <- Z.negb_even, Ea; reflexivity).
    assert (Ob : Z.odd b = true) by (rewrite <- Z.negb_even, Eb; reflexivity).
    apply Z.odd_spec in Oa; destruct Oa as [k Hk].
    apply Z.odd_spec in Ob; destruct Ob as [m Hm]; lia.
Qed.

Lemma demand_eq2 :
  forall C, wf_comp C -> demand C = 2 -> C = Chain 4 \/ C = Loop 6.
Proof.
  intros [m | m] Hw Hd; unfold demand in Hd; simpl csize in Hd;
    simpl hand in Hd.
  - left; f_equal; lia.
  - right; f_equal; lia.
Qed.

Lemma count6_le_length : forall G, (count6 G <= length G)%nat.
Proof.
  induction G as [|C G IH]; [reflexivity|].
  rewrite count6_cons; simpl; destruct (is_6loop_b C); lia.
Qed.

(** With no three-chains and no four-loops, and a controlled value of at most
    four, the value depends only on the box count modulo four. *)
Lemma value_no34_aux :
  forall n G, (length G <= n)%nat ->
    wf G -> G <> [] ->
    existsb is_3chain_b G = false ->
    existsb is_4loop_b G = false ->
    cval G <= 4 ->
    value G = w4z (Z.of_nat (size G)).
Proof.
  induction n as [|n IH]; intros G Hn HG HNil H3 H4 Hc.
  - exfalso; apply HNil; destruct G; [reflexivity | simpl in Hn; lia].
  - assert (Hall : forall C, In C G ->
              wf_comp C /\ is_3chain_b C = false /\ is_4loop_b C = false).
    { intros C HC; split; [|split].
      - unfold wf in HG; rewrite Forall_forall in HG; apply HG; exact HC.
      - destruct (is_3chain_b C) eqn:E; [|reflexivity].
        exfalso; assert (Hbad : existsb is_3chain_b G = true)
          by (apply (proj2 (existsb_exists is_3chain_b G));
              exists C; split; assumption).
        congruence.
      - destruct (is_4loop_b C) eqn:E; [|reflexivity].
        exfalso; assert (Hbad : existsb is_4loop_b G = true)
          by (apply (proj2 (existsb_exists is_4loop_b G));
              exists C; split; assumption).
        congruence. }
    destruct (Z_le_gt_dec 2 (cval G)) as [Hge2 | Hlt2].
    + rewrite (value_cval_ge2 G HG Hge2), (size_cval_w4z G H3).
      symmetry; apply w4z_id_2_4; lia.
    + pose proof (cbase_ge_count6 G Hall) as Hcb.
      pose proof (tb_pos G HNil) as Htbp.
      assert (Hc6 : (2 <= count6 G)%nat) by (unfold cval in Hlt2; lia).
      assert (HlenG : (2 <= length G)%nat)
        by (pose proof (count6_le_length G); lia).
      assert (HIn6 : In (Loop 6) G) by (apply count6_pos_In; lia).
      destruct (In_selections G (Loop 6) HIn6) as [rest Hsel].
      pose proof (selections_perm G (Loop 6, rest) Hsel) as Hperm;
        cbn [fst snd] in Hperm.
      pose proof (selections_length G (Loop 6, rest) Hsel) as Hlen;
        cbn [fst snd] in Hlen.
      pose proof (selections_wf G (Loop 6, rest) HG Hsel) as [Hw6 Hwr];
        cbn [fst snd] in Hw6, Hwr.
      pose proof (selections_size G (Loop 6, rest) Hsel) as Hsz;
        cbn [fst snd] in Hsz.
      assert (HrNil : rest <> [])
        by (destruct rest; simpl in Hlen; [lia | discriminate]).
      assert (H3r : existsb is_3chain_b rest = false)
        by (apply (existsb_false_tail is_3chain_b (Loop 6) rest G Hperm H3)).
      assert (H4r : existsb is_4loop_b rest = false)
        by (apply (existsb_false_tail is_4loop_b (Loop 6) rest G Hperm H4)).
      assert (H3G2 : existsb is_3chain_b (Loop 6 :: rest) = false)
        by (rewrite (existsb_perm is_3chain_b _ _ Hperm); exact H3).
      assert (Htbeq : tb (Loop 6 :: rest) = tb rest)
        by (apply tb_remove_loop_no3;
            [reflexivity | exact H3G2 | exact HrNil]).
      assert (Hcvr : cval rest <= 4).
      { pose proof (selections_cval G (Loop 6, rest) Hsel) as Hcv;
          cbn [fst snd] in Hcv.
        rewrite Htbeq, weight_6loop in Hcv.
        unfold cval in *; lia. }
      assert (Hvr : value rest = w4z (Z.of_nat (size rest)))
        by (apply IH;
            [lia | exact Hwr | exact HrNil | exact H3r | exact H4r
             | exact Hcvr]).
      assert (Hopt6 : value_open (Loop 6, rest) = w4z (Z.of_nat (size G))).
      { unfold value_open; cbn [fst snd]; rewrite Hvr, vopen_loop6.
        replace (Z.of_nat (size rest)) with (Z.of_nat (size G) - 6)
          by (simpl csize in Hsz; lia).
        apply w4z_step6. }
      assert (Hmin : forall q, In q (selections G) ->
                value_open (Loop 6, rest) <= value_open q).
      { intros q Hq.
        destruct (Z_le_gt_dec (value_open (Loop 6, rest)) (value_open q))
          as [Hle | Hgt]; [exact Hle | exfalso].
        pose proof (value_open_parity G (Loop 6, rest) Hsel) as Hp1.
        pose proof (value_open_parity G q Hq) as Hp2.
        pose proof (value_open_ge_demand G q Hq) as Hdq.
        pose proof (selections_wf G q HG Hq) as [Hwq Hwrq].
        pose proof (selections_In G q Hq) as HInq.
        destruct (Hall (fst q) HInq) as [_ [Hq3 Hq4]].
        assert (Hdem : 2 <= demand (fst q))
          by (apply demand_of_no34; assumption).
        rewrite Hopt6 in Hp1, Hgt.
        pose proof (w4z_range (Z.of_nat (size G))) as Hrange.
        assert (Hgap : value_open q + 2 <= w4z (Z.of_nat (size G))).
        { apply even_eq_diff2; [rewrite Hp2, <- Hp1; reflexivity | lia]. }
        assert (Hq2 : value_open q = 2) by lia.
        assert (Hw4 : w4z (Z.of_nat (size G)) = 4) by lia.
        assert (Hdem2 : demand (fst q) = 2) by lia.
        destruct (demand_eq2 (fst q) Hwq Hdem2) as [HC4 | HC6].
        - pose proof (selections_size G q Hq) as Hszq.
          pose proof (selections_length G q Hq) as Hlenq.
          assert (HqNil : snd q <> [])
            by (destruct (snd q); simpl in Hlenq; [lia | discriminate]).
          assert (Hvq : value (snd q) = 2).
          { unfold value_open in Hq2; rewrite HC4, vopen_chain4 in Hq2.
            pose proof (Z.abs_nonneg (value (snd q) - 2)) as Hab.
            assert (Hz : Z.abs (value (snd q) - 2) = 0) by lia.
            apply Z.abs_0_iff in Hz; lia. }
          assert (Hw4q : w4z (Z.of_nat (size (snd q))) = 4).
          { rewrite <- Hw4; apply w4z_mod.
            replace (Z.of_nat (size G))
              with (Z.of_nat (size (snd q)) + 1 * 4)
              by (rewrite HC4 in Hszq; simpl csize in Hszq; lia).
            symmetry; apply Z_mod_plus_full. }
          assert (H3q : existsb is_3chain_b (snd q) = false)
            by (apply (existsb_false_tail is_3chain_b (fst q) (snd q) G);
                [apply selections_perm; exact Hq | exact H3]).
          assert (H4q : existsb is_4loop_b (snd q) = false)
            by (apply (existsb_false_tail is_4loop_b (fst q) (snd q) G);
                [apply selections_perm; exact Hq | exact H4]).
          destruct (Z_le_gt_dec (cval (snd q)) 4) as [Hle4 | Hgt4].
          + rewrite (IH (snd q)) in Hvq;
              [lia | lia | exact Hwrq | exact HqNil | exact H3q | exact H4q
               | exact Hle4].
          + rewrite (value_cval_ge2 (snd q) Hwrq) in Hvq; lia.
        - assert (Hpq : Permutation (snd q) rest).
          { apply (Permutation_cons_inv (a := Loop 6)).
            eapply Permutation_trans;
              [rewrite <- HC6; apply selections_perm; exact Hq
               | apply Permutation_sym; exact Hperm]. }
          unfold value_open in Hq2; rewrite HC6 in Hq2.
          rewrite (value_perm (snd q) rest Hpq) in Hq2.
          unfold value_open in Hopt6; cbn [fst snd] in Hopt6.
          lia. }
      rewrite (value_of_min_option G (Loop 6, rest) Hsel Hmin); exact Hopt6.
Qed.

Theorem value_no34 :
  forall G,
    wf G -> G <> [] ->
    existsb is_3chain_b G = false ->
    existsb is_4loop_b G = false ->
    cval G <= 4 ->
    value G = w4z (Z.of_nat (size G)).
Proof. intros G; apply (value_no34_aux (length G)); lia. Qed.

(** * Three-chains present, no four-loops *)

Lemma even_mod4 : forall s, Z.even s = Z.even (s mod 4).
Proof.
  intros s.
  rewrite (Z.div_mod s 4) at 1 by lia.
  rewrite Z.even_add, Z.even_mul.
  simpl (Z.even 4).
  destruct (Z.even (s mod 4)); reflexivity.
Qed.

Definition count3 (G : position) : nat := length (filter is_3chain_b G).

Lemma count3_perm : forall G H, Permutation G H -> count3 G = count3 H.
Proof.
  intros G H HP; unfold count3.
  apply Permutation_length, filter_perm; exact HP.
Qed.

Lemma count3_cons :
  forall C G,
    count3 (C :: G) = (if is_3chain_b C then S (count3 G) else count3 G).
Proof.
  intros C G; unfold count3; simpl; destruct (is_3chain_b C); reflexivity.
Qed.

Lemma count3_pos_iff :
  forall G, existsb is_3chain_b G = true <-> (0 < count3 G)%nat.
Proof.
  induction G as [|C G IH]; simpl; [unfold count3; simpl; split; [discriminate | lia]|].
  rewrite count3_cons.
  destruct (is_3chain_b C); simpl; split; intros H; try lia; try reflexivity.
  - apply IH in H; lia.
  - apply IH; lia.
Qed.

Lemma count3_In : forall G, (0 < count3 G)%nat -> In (Chain 3) G.
Proof.
  induction G as [|C G IH]; intros H; [unfold count3 in H; simpl in H; lia|].
  rewrite count3_cons in H.
  destruct (is_3chain_b C) eqn:E.
  - left; apply is_3chain_eq; exact E.
  - right; apply IH; lia.
Qed.

(** Deleting one three-chain from a position that keeps another leaves the
    terminal bonus alone. *)
Lemma tb_cons_3chain_with3 :
  forall rest,
    existsb is_3chain_b rest = true ->
    tb (Chain 3 :: rest) = tb rest.
Proof.
  intros rest H3.
  assert (HrNil : rest <> [])
    by (destruct rest; [simpl in H3; discriminate | discriminate]).
  destruct (existsb is_loop_b rest) eqn:EL.
  - destruct (forallb (fun X => is_loop_b X || is_3chain_b X)%bool rest)
      eqn:EF.
    + assert (E1 : existsb is_loop_b (Chain 3 :: rest) = true)
        by (simpl; rewrite EL; reflexivity).
      assert (E2 : existsb is_3chain_b (Chain 3 :: rest) = true)
        by reflexivity.
      assert (E3 : forallb (fun X => is_loop_b X || is_3chain_b X)%bool
                           (Chain 3 :: rest) = true)
        by (simpl; rewrite EF; reflexivity).
      rewrite (tb_six (Chain 3 :: rest) E1 E2 E3).
      rewrite (tb_six rest EL H3 EF); reflexivity.
    + assert (Hex : existsb
                (fun X => negb (is_loop_b X || is_3chain_b X)%bool) rest = true)
        by (rewrite <- negb_forallb, EF; reflexivity).
      apply existsb_exists in Hex; destruct Hex as [D [HD HDn]].
      apply negb_true_iff, orb_false_iff in HDn; destruct HDn as [HDl HD3].
      rewrite (tb_long_chain (Chain 3 :: rest) D); [| right; exact HD | exact HDl | exact HD3].
      rewrite (tb_long_chain rest D); [reflexivity | exact HD | exact HDl | exact HD3].
  - assert (E1 : existsb is_loop_b (Chain 3 :: rest) = false)
      by (simpl; rewrite EL; reflexivity).
    rewrite (tb_no_loops (Chain 3 :: rest)); [| discriminate | exact E1].
    rewrite (tb_no_loops rest); [reflexivity | exact HrNil | exact EL].
Qed.

(** The value once three-chains are present but four-loops are not. *)
Definition w35z (t : nat) (s : Z) : Z :=
  if Z.even s then 2
  else if ((t =? 1)%nat && (s mod 4 =? 3))%bool then 3 else 1.

Lemma w35z_range : forall t s, 1 <= w35z t s <= 3.
Proof.
  intros t s; unfold w35z.
  destruct (Z.even s); [lia|].
  destruct ((t =? 1)%nat && (s mod 4 =? 3))%bool; lia.
Qed.

Lemma even_sub3 : forall s, Z.even (s - 3) = negb (Z.even s).
Proof.
  intros s; rewrite Z.even_sub; simpl (Z.even 3).
  destruct (Z.even s); reflexivity.
Qed.

Lemma w35z_step_big :
  forall t s v,
    (2 <= t)%nat -> 1 <= v <= 3 -> Z.even v = Z.even (s - 3) ->
    1 + Z.abs (v - 2) = w35z t s.
Proof.
  intros t s v Ht Hv Hpar.
  unfold w35z.
  replace ((t =? 1)%nat) with false by (symmetry; apply Nat.eqb_neq; lia).
  rewrite andb_false_l.
  rewrite even_sub3 in Hpar.
  destruct (Z.even s) eqn:Es; simpl in Hpar.
  - assert (Hv2 : v <> 2) by (intros Hc; rewrite Hc in Hpar; discriminate).
    assert (Hcase : v = 1 \/ v = 3) by lia.
    destruct Hcase as [-> | ->]; reflexivity.
  - assert (Hv1 : v <> 1) by (intros Hc; rewrite Hc in Hpar; discriminate).
    assert (Hv3 : v <> 3) by (intros Hc; rewrite Hc in Hpar; discriminate).
    assert (Hc2 : v = 2) by lia.
    rewrite Hc2; reflexivity.
Qed.

Lemma w35z_step_one :
  forall s, 1 + Z.abs (w4z (s - 3) - 2) = w35z 1 s.
Proof.
  intros s.
  pose proof (Z.mod_pos_bound s 4 ltac:(lia)) as Hb.
  assert (Hsub : (s - 3) mod 4 = ((s mod 4) + 1) mod 4).
  { replace (s - 3) with (s + 1 + (-1) * 4) by lia.
    rewrite Z_mod_plus_full.
    rewrite Z.add_mod_idemp_l by lia; reflexivity. }
  unfold w4z, w35z; rewrite Hsub, (even_mod4 s).
  assert (Hr : s mod 4 = 0 \/ s mod 4 = 1 \/ s mod 4 = 2 \/ s mod 4 = 3) by lia.
  destruct Hr as [H | [H | [H | H]]]; rewrite H; reflexivity.
Qed.

Lemma vopen_chain3_abs : forall w, vopen (Chain 3) w = 1 + Z.abs (w - 2).
Proof. intros w; reflexivity. Qed.

(** With a three-chain present and no four-loops, opening a three-chain is
    optimal and the value is given by the parity of the board and, in the
    single three-chain case, its residue modulo four. *)
Lemma value_no4_with3_aux :
  forall n G, (length G <= n)%nat ->
    wf G ->
    existsb is_4loop_b G = false ->
    existsb is_3chain_b G = true ->
    cval G < 2 ->
    value G = w35z (count3 G) (Z.of_nat (size G)).
Proof.
  induction n as [|n IH]; intros G Hn HG H4 H3 Hc.
  - exfalso.
    assert (HGnil : G = []) by (destruct G; simpl in Hn; [reflexivity | lia]).
    subst G; simpl in H3; discriminate.
  - assert (HIn3 : In (Chain 3) G)
      by (apply count3_In; apply count3_pos_iff; exact H3).
    destruct (In_selections G (Chain 3) HIn3) as [rest Hsel].
    pose proof (selections_perm G (Chain 3, rest) Hsel) as Hperm;
      cbn [fst snd] in Hperm.
    pose proof (selections_length G (Chain 3, rest) Hsel) as Hlen;
      cbn [fst snd] in Hlen.
    pose proof (selections_wf G (Chain 3, rest) HG Hsel) as [Hw3 Hwr];
      cbn [fst snd] in Hw3, Hwr.
    pose proof (selections_size G (Chain 3, rest) Hsel) as Hsz;
      cbn [fst snd] in Hsz.
    pose proof (selections_cval G (Chain 3, rest) Hsel) as Hcv;
      cbn [fst snd] in Hcv.
    rewrite weight_chain in Hcv.
    assert (H4r : existsb is_4loop_b rest = false)
      by (apply (existsb_false_tail is_4loop_b (Chain 3) rest G Hperm H4)).
    assert (Ht3 : count3 G = S (count3 rest)).
    { rewrite <- (count3_perm (Chain 3 :: rest) G Hperm), count3_cons;
        reflexivity. }
    assert (Hszz : Z.of_nat (size rest) = Z.of_nat (size G) - 3)
      by (simpl csize in Hsz; lia).
    assert (Hopt : value_open (Chain 3, rest) =
                   w35z (count3 G) (Z.of_nat (size G))).
    { unfold value_open; cbn [fst snd]; rewrite vopen_chain3_abs.
      destruct (existsb is_3chain_b rest) eqn:E3r.
      - (* another three-chain remains *)
        assert (HrNil : rest <> [])
          by (destruct rest; [simpl in E3r; discriminate | discriminate]).
        assert (Htbeq : tb (Chain 3 :: rest) = tb rest)
          by (apply tb_cons_3chain_with3; exact E3r).
        assert (Hcr : cval rest = cval G + 1)
          by (unfold cval in *; rewrite Htbeq in Hcv; lia).
        assert (Hvr : 1 <= value rest <= 3).
        { destruct (Z_le_gt_dec 2 (cval rest)) as [Hge | Hlt].
          - rewrite (value_cval_ge2 rest Hwr Hge); lia.
          - rewrite (IH rest); [apply w35z_range | lia | exact Hwr | exact H4r
                                | exact E3r | exact (Z.gt_lt _ _ Hlt)]. }
        apply (w35z_step_big (count3 G) (Z.of_nat (size G)) (value rest)).
        + assert (H0 : (0 < count3 rest)%nat)
            by (apply count3_pos_iff; exact E3r).
          lia.
        + exact Hvr.
        + rewrite (value_parity rest), Hszz; reflexivity.
      - (* the last three-chain *)
        assert (HrNil : rest <> []).
        { intros Hnil; subst rest.
          simpl cbase in Hcv.
          rewrite tb_single_chain in Hcv; lia. }
        assert (Htb4 : tb rest = 4 \/ tb rest = 8).
        { destruct (tb_no_three_chain rest E3r) as [E | [E | E]];
            [| left; exact E | right; exact E].
          exfalso; pose proof (tb_pos rest HrNil); lia. }
        assert (Hrise : tb rest - tb (Chain 3 :: rest) <= 2).
        { destruct Htb4 as [E4 | E8].
          - pose proof (tb_pos (Chain 3 :: rest) ltac:(discriminate)); lia.
          - assert (HL : forallb is_loop_b rest = true)
              by (apply tb_eight_all_loops; assumption).
            rewrite (tb_six_of_loops_and_three rest HL HrNil); lia. }
        assert (Hcr : cval rest <= 4)
          by (unfold cval in *; lia).
        assert (Hvr : value rest = w4z (Z.of_nat (size rest)))
          by (apply value_no34; assumption).
        assert (Ht1 : count3 G = 1%nat).
        { assert (H0 : count3 rest = 0%nat).
          { destruct (count3 rest) eqn:E; [reflexivity|].
            exfalso; assert (existsb is_3chain_b rest = true)
              by (apply count3_pos_iff; lia).
            congruence. }
          lia. }
        rewrite Ht1, Hvr, Hszz; apply w35z_step_one. }
    assert (Hmin : forall q, In q (selections G) ->
              value_open (Chain 3, rest) <= value_open q).
    { intros q Hq.
      destruct (is_3chain_b (fst q)) eqn:Eq3.
      - (* another three-chain option: the same worth *)
        assert (HqC : fst q = Chain 3) by (apply is_3chain_eq; exact Eq3).
        assert (Hpq : Permutation (snd q) rest).
        { apply (Permutation_cons_inv (a := Chain 3)).
          eapply Permutation_trans;
            [rewrite <- HqC; apply selections_perm; exact Hq
             | apply Permutation_sym; exact Hperm]. }
        unfold value_open; cbn [fst snd]; rewrite HqC.
        rewrite (value_perm (snd q) rest Hpq); lia.
      - (* any other option is worth at least two *)
        destruct (Z_le_gt_dec (value_open (Chain 3, rest)) (value_open q))
          as [Hle | Hgt]; [exact Hle | exfalso].
        pose proof (value_open_ge_demand G q Hq) as Hdq.
        pose proof (selections_wf G q HG Hq) as [Hwq _].
        pose proof (selections_In G q Hq) as HInq.
        assert (Hq4 : is_4loop_b (fst q) = false).
        { destruct (is_4loop_b (fst q)) eqn:E; [|reflexivity].
          exfalso; assert (Hbad : existsb is_4loop_b G = true)
            by (apply (proj2 (existsb_exists is_4loop_b G));
                exists (fst q); split; assumption).
          congruence. }
        assert (Hdem : 2 <= demand (fst q))
          by (apply demand_of_no34; assumption).
        pose proof (value_open_parity G (Chain 3, rest) Hsel) as Hp1.
        pose proof (value_open_parity G q Hq) as Hp2.
        assert (Hgap : value_open q + 2 <= value_open (Chain 3, rest)).
        { apply even_eq_diff2; [rewrite Hp2, <- Hp1; reflexivity | lia]. }
        rewrite Hopt in Hgap.
        pose proof (w35z_range (count3 G) (Z.of_nat (size G))); lia. }
    rewrite (value_of_min_option G (Chain 3, rest) Hsel Hmin); exact Hopt.
Qed.

Theorem value_no4_with3 :
  forall G,
    wf G ->
    existsb is_4loop_b G = false ->
    existsb is_3chain_b G = true ->
    cval G < 2 ->
    value G = w35z (count3 G) (Z.of_nat (size G)).
Proof. intros G; apply (value_no4_with3_aux (length G)); lia. Qed.

(** * Four-loops *)

Definition count4 (G : position) : nat := length (filter is_4loop_b G).

Lemma count4_cons :
  forall C G,
    count4 (C :: G) = (if is_4loop_b C then S (count4 G) else count4 G).
Proof.
  intros C G; unfold count4; simpl; destruct (is_4loop_b C); reflexivity.
Qed.

Definition only34 (G : position) : bool :=
  forallb (fun C => is_3chain_b C || is_4loop_b C)%bool G.

(** A position of three-chains and four-loops is one of the [mix] family. *)
Lemma perm_mix_of_only34 :
  forall G, only34 G = true -> Permutation G (mix (count3 G) (count4 G)).
Proof.
  induction G as [|C G IH]; intros H; [apply Permutation_refl|].
  unfold only34 in H; simpl in H; apply andb_true_iff in H.
  destruct H as [HC HG].
  specialize (IH HG).
  apply orb_true_iff in HC; destruct HC as [H3 | H4].
  - assert (HCeq : C = Chain 3) by (apply is_3chain_eq; exact H3).
    subst C.
    assert (A : count3 (Chain 3 :: G) = S (count3 G)) by reflexivity.
    assert (B : count4 (Chain 3 :: G) = count4 G) by reflexivity.
    rewrite A, B, mix_chain_cons; apply perm_skip; exact IH.
  - assert (HCeq : C = Loop 4) by (apply is_4loop_eq; exact H4).
    subst C.
    assert (A : count3 (Loop 4 :: G) = count3 G) by reflexivity.
    assert (B : count4 (Loop 4 :: G) = S (count4 G)) by reflexivity.
    rewrite A, B.
    eapply Permutation_trans; [apply perm_skip; exact IH|].
    apply Permutation_sym, mix_loop_perm.
Qed.

Theorem value_only34 :
  forall G, only34 G = true -> value G = v36 (count3 G) (count4 G).
Proof.
  intros G H.
  rewrite (value_perm G (mix (count3 G) (count4 G)) (perm_mix_of_only34 G H)).
  apply value_mix.
Qed.

Lemma demand_ge1_of_not4loop :
  forall C, wf_comp C -> is_4loop_b C = false -> 1 <= demand C.
Proof.
  intros [m | m] Hw H4; unfold demand; simpl csize; simpl hand.
  - simpl in Hw; lia.
  - destruct Hw as [Hge Hev].
    destruct m as [|[|[|[|[|[|m]]]]]];
      try (simpl in Hge); try (simpl in Hev); try (simpl in H4);
      solve [ lia | discriminate ].
Qed.

(** Removing a four-loop from a position that also holds a longer component
    leaves the terminal bonus alone. *)
Lemma tb_remove_4loop :
  forall rest D,
    In D rest ->
    is_3chain_b D = false -> is_4loop_b D = false -> wf_comp D ->
    tb (Loop 4 :: rest) = tb rest.
Proof.
  intros rest D HD H3 H4 HwD.
  assert (HrNil : rest <> []) by (destruct rest; [destruct HD | discriminate]).
  destruct (is_loop_b D) eqn:EDl.
  - (* D is a loop of length at least six *)
    destruct (forallb is_loop_b rest) eqn:EL.
    + assert (HL : forallb is_loop_b (Loop 4 :: rest) = true)
        by (simpl; exact EL).
      rewrite (tb_all_loops (Loop 4 :: rest) ltac:(discriminate) HL).
      rewrite (tb_all_loops rest HrNil EL); reflexivity.
    + assert (Hex : existsb (fun X => negb (is_loop_b X)) rest = true)
        by (rewrite <- negb_forallb, EL; reflexivity).
      apply existsb_exists in Hex; destruct Hex as [E [HE HEn]].
      apply negb_true_iff in HEn.
      destruct (is_3chain_b E) eqn:E3.
      * (* a three-chain and a long loop: the bonus is six on both sides *)
        assert (A1 : existsb is_loop_b (Loop 4 :: rest) = true) by reflexivity.
        assert (A2 : existsb is_loop_b rest = true)
          by (apply (proj2 (existsb_exists is_loop_b rest));
              exists D; split; assumption).
        assert (A3 : existsb is_3chain_b (Loop 4 :: rest) = true)
          by (apply (proj2 (existsb_exists is_3chain_b (Loop 4 :: rest)));
              exists E; split; [right; exact HE | exact E3]).
        assert (A4 : existsb is_3chain_b rest = true)
          by (apply (proj2 (existsb_exists is_3chain_b rest));
              exists E; split; assumption).
        destruct (forallb (fun X => is_loop_b X || is_3chain_b X)%bool rest)
          eqn:EF.
        -- assert (A5 : forallb (fun X => is_loop_b X || is_3chain_b X)%bool
                          (Loop 4 :: rest) = true)
             by (simpl; rewrite EF; reflexivity).
           rewrite (tb_six (Loop 4 :: rest) A1 A3 A5), (tb_six rest A2 A4 EF);
             reflexivity.
        -- assert (Hex2 : existsb
                     (fun X => negb (is_loop_b X || is_3chain_b X)%bool) rest
                   = true)
             by (rewrite <- negb_forallb, EF; reflexivity).
           apply existsb_exists in Hex2; destruct Hex2 as [F [HF HFn]].
           apply negb_true_iff, orb_false_iff in HFn; destruct HFn as [Hl Hc].
           rewrite (tb_long_chain (Loop 4 :: rest) F);
             [| right; exact HF | exact Hl | exact Hc].
           rewrite (tb_long_chain rest F);
             [reflexivity | exact HF | exact Hl | exact Hc].
      * rewrite (tb_long_chain (Loop 4 :: rest) E);
          [| right; exact HE | exact HEn | exact E3].
        rewrite (tb_long_chain rest E);
          [reflexivity | exact HE | exact HEn | exact E3].
  - (* D is a chain of length at least four *)
    rewrite (tb_long_chain (Loop 4 :: rest) D);
      [| right; exact HD | exact EDl | exact H3].
    rewrite (tb_long_chain rest D);
      [reflexivity | exact HD | exact EDl | exact H3].
Qed.

(** With a four-loop present, a longer component present, and a controlled
    value of at least minus two, the value is the absolute controlled
    value. *)
Theorem value_with_4loop :
  forall G,
    wf G ->
    existsb is_4loop_b G = true ->
    only34 G = false ->
    -2 <= cval G ->
    value G = Z.abs (cval G).
Proof.
  intros G HG H4 Honly Hge.
  destruct (Z_le_gt_dec 2 (cval G)) as [Hge2 | Hlt2].
  { rewrite (value_cval_ge2 G HG Hge2); lia. }
  (* a component that is neither a three-chain nor a four-loop *)
  assert (Hex : existsb (fun C => negb (is_3chain_b C || is_4loop_b C)%bool) G
                = true)
    by (unfold only34 in Honly; rewrite <- negb_forallb, Honly; reflexivity).
  apply existsb_exists in Hex; destruct Hex as [D [HD HDn]].
  apply negb_true_iff, orb_false_iff in HDn; destruct HDn as [HD3 HD4].
  assert (HwD : wf_comp D)
    by (unfold wf in HG; rewrite Forall_forall in HG; apply HG; exact HD).
  (* pick a four-loop *)
  assert (HIn4 : In (Loop 4) G).
  { apply existsb_exists in H4; destruct H4 as [C [HC HC4]].
    rewrite <- (is_4loop_eq C HC4); exact HC. }
  destruct (In_selections G (Loop 4) HIn4) as [rest Hsel].
  pose proof (selections_perm G (Loop 4, rest) Hsel) as Hperm;
    cbn [fst snd] in Hperm.
  pose proof (selections_wf G (Loop 4, rest) HG Hsel) as [Hw4 Hwr];
    cbn [fst snd] in Hw4, Hwr.
  pose proof (selections_cval G (Loop 4, rest) Hsel) as Hcv;
    cbn [fst snd] in Hcv.
  rewrite weight_loop_len in Hcv.
  assert (HDrest : In D rest).
  { assert (HDG : In D (Loop 4 :: rest))
      by (eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact HD]).
    destruct HDG as [HDeq | HDr]; [|exact HDr].
    exfalso; rewrite <- HDeq in HD4; discriminate. }
  assert (Htbeq : tb (Loop 4 :: rest) = tb rest)
    by (apply (tb_remove_4loop rest D); assumption).
  assert (Hcr : cval rest = cval G + 4)
    by (unfold cval in *; rewrite Htbeq in Hcv; simpl Z.of_nat in Hcv; lia).
  assert (Hvr : value rest = cval G + 4).
  { rewrite (value_cval_ge2 rest Hwr); lia. }
  assert (Hopt : value_open (Loop 4, rest) = Z.abs (cval G)).
  { unfold value_open; cbn [fst snd]; rewrite Hvr.
    unfold vopen; simpl csize; simpl hand.
    replace (cval G + 4 - Z.of_nat 4) with (cval G) by (simpl; lia).
    simpl; lia. }
  assert (Hmin : forall q, In q (selections G) ->
            value_open (Loop 4, rest) <= value_open q).
  { intros q Hq.
    destruct (is_4loop_b (fst q)) eqn:Eq4.
    - assert (HqC : fst q = Loop 4) by (apply is_4loop_eq; exact Eq4).
      assert (Hpq : Permutation (snd q) rest).
      { apply (Permutation_cons_inv (a := Loop 4)).
        eapply Permutation_trans;
          [rewrite <- HqC; apply selections_perm; exact Hq
           | apply Permutation_sym; exact Hperm]. }
      unfold value_open; cbn [fst snd]; rewrite HqC.
      rewrite (value_perm (snd q) rest Hpq); lia.
    - destruct (Z_le_gt_dec (value_open (Loop 4, rest)) (value_open q))
        as [Hle | Hgt]; [exact Hle | exfalso].
      pose proof (value_open_ge_demand G q Hq) as Hdq.
      pose proof (selections_wf G q HG Hq) as [Hwq _].
      assert (Hdem : 1 <= demand (fst q))
        by (apply demand_ge1_of_not4loop; assumption).
      pose proof (value_open_parity G (Loop 4, rest) Hsel) as Hp1.
      pose proof (value_open_parity G q Hq) as Hp2.
      assert (Hgap : value_open q + 2 <= value_open (Loop 4, rest))
        by (apply even_eq_diff2; [rewrite Hp2, <- Hp1; reflexivity | lia]).
      rewrite Hopt in Hgap; lia. }
  rewrite (value_of_min_option G (Loop 4, rest) Hsel Hmin); exact Hopt.
Qed.

(** * The residue formulas below a controlled value of two *)

Definition w10 (c : Z) : Z :=
  if (c mod 8) =? 0 then 0
  else if ((c mod 8) =? 1) || ((c mod 8) =? 7) then 1
  else if ((c mod 8) =? 2) || ((c mod 8) =? 6) then 2
  else if ((c mod 8) =? 3) || ((c mod 8) =? 5) then 3
  else 4.

Definition w11 (c : Z) (f : nat) : Z :=
  if (c mod 4) =? 2 then 2
  else if Nat.odd f then (if Z.even c then 0 else 1)
  else (if Z.even c then 4 else 3).

Lemma w10_range : forall c, 0 <= w10 c <= 4.
Proof.
  intros c; unfold w10.
  destruct ((c mod 8) =? 0); [lia|].
  destruct (((c mod 8) =? 1) || ((c mod 8) =? 7))%bool; [lia|].
  destruct (((c mod 8) =? 2) || ((c mod 8) =? 6))%bool; [lia|].
  destruct (((c mod 8) =? 3) || ((c mod 8) =? 5))%bool; lia.
Qed.

Lemma w11_range : forall c f, 0 <= w11 c f <= 4.
Proof.
  intros c f; unfold w11.
  destruct ((c mod 4) =? 2); [lia|].
  destruct (Nat.odd f); destruct (Z.even c); lia.
Qed.

Lemma w10_step : forall c, 4 - w10 (c + 4) = w10 c.
Proof.
  intros c.
  pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as Hb.
  assert (H : (c + 4) mod 8 = ((c mod 8) + 4) mod 8)
    by (rewrite Z.add_mod_idemp_l by lia; reflexivity).
  unfold w10; rewrite H.
  assert (Hr : c mod 8 = 0 \/ c mod 8 = 1 \/ c mod 8 = 2 \/ c mod 8 = 3 \/
               c mod 8 = 4 \/ c mod 8 = 5 \/ c mod 8 = 6 \/ c mod 8 = 7)
    by lia.
  destruct Hr as [H0|[H0|[H0|[H0|[H0|[H0|[H0|H0]]]]]]];
    rewrite H0; reflexivity.
Qed.

Lemma even_add4 : forall c, Z.even (c + 4) = Z.even c.
Proof.
  intros c; rewrite Z.even_add; simpl (Z.even 4).
  destruct (Z.even c); reflexivity.
Qed.

Lemma mod4_add4 : forall c, (c + 4) mod 4 = c mod 4.
Proof.
  intros c; replace (c + 4) with (c + 1 * 4) by lia; apply Z_mod_plus_full.
Qed.

Lemma odd_S : forall f, Nat.odd (S f) = negb (Nat.odd f).
Proof.
  intros f; rewrite Nat.odd_succ, <- Nat.negb_odd; reflexivity.
Qed.

Lemma w11_step : forall c f, 4 - w11 (c + 4) f = w11 c (S f).
Proof.
  intros c f; unfold w11.
  rewrite mod4_add4, even_add4, odd_S.
  destruct ((c mod 4) =? 2); [lia|].
  destruct (Nat.odd f); destruct (Z.even c); simpl; lia.
Qed.

Lemma w11_f0 : forall c, w11 c 0 = w4z c.
Proof.
  intros c; unfold w11, w4z.
  pose proof (Z.mod_pos_bound c 4 ltac:(lia)) as Hb.
  rewrite (even_mod4 c).
  assert (Hr : c mod 4 = 0 \/ c mod 4 = 1 \/ c mod 4 = 2 \/ c mod 4 = 3)
    by lia.
  destruct Hr as [H|[H|[H|H]]]; rewrite H; reflexivity.
Qed.

Lemma w10_allloops :
  forall f, w10 (8 - 4 * Z.of_nat f) = (if Nat.even f then 0 else 4).
Proof.
  intros f; unfold w10.
  destruct (Nat.even f) eqn:Ef.
  - apply Nat.even_spec in Ef; destruct Ef as [k Hk]; subst f.
    assert (H : (8 - 4 * Z.of_nat (2 * k)) mod 8 = 0).
    { replace (8 - 4 * Z.of_nat (2 * k)) with (0 + (1 - Z.of_nat k) * 8)
        by lia.
      rewrite Z_mod_plus_full; reflexivity. }
    rewrite H; reflexivity.
  - assert (Ho : Nat.odd f = true)
      by (rewrite <- Nat.negb_even, Ef; reflexivity).
    apply Nat.odd_spec in Ho; destruct Ho as [k Hk]; subst f.
    assert (H : (8 - 4 * Z.of_nat (2 * k + 1)) mod 8 = 4).
    { replace (8 - 4 * Z.of_nat (2 * k + 1)) with (4 + (- Z.of_nat k) * 8)
        by lia.
      rewrite Z_mod_plus_full; reflexivity. }
    rewrite H; reflexivity.
Qed.

Definition w38 (c : Z) (f : nat) : Z :=
  if 2 <=? c + 4 * Z.of_nat f then w10 c else w11 c f.

Lemma w38_range : forall c f, 0 <= w38 c f <= 4.
Proof.
  intros c f; unfold w38.
  destruct (2 <=? c + 4 * Z.of_nat f);
    [apply w10_range | apply w11_range].
Qed.

Lemma mod4_of_mod8 : forall c, c mod 4 = (c mod 8) mod 4.
Proof.
  intros c.
  rewrite (Z.div_mod c 8) at 1 by lia.
  replace (8 * (c / 8) + c mod 8) with (c mod 8 + (2 * (c / 8)) * 4) by lia.
  rewrite Z_mod_plus_full; reflexivity.
Qed.

Lemma w10_eq2 : forall c, w10 c = 2 -> c mod 4 = 2.
Proof.
  intros c H; rewrite mod4_of_mod8.
  pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as Hb.
  unfold w10 in H.
  assert (Hr : c mod 8 = 0 \/ c mod 8 = 1 \/ c mod 8 = 2 \/ c mod 8 = 3 \/
               c mod 8 = 4 \/ c mod 8 = 5 \/ c mod 8 = 6 \/ c mod 8 = 7)
    by lia.
  destruct Hr as [H0|[H0|[H0|[H0|[H0|[H0|[H0|H0]]]]]]];
    rewrite H0 in H |- *; simpl in H; solve [discriminate | reflexivity].
Qed.

Lemma w10_eq4 : forall c, w10 c = 4 -> c mod 4 = 0.
Proof.
  intros c H; rewrite mod4_of_mod8.
  pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as Hb.
  unfold w10 in H.
  assert (Hr : c mod 8 = 0 \/ c mod 8 = 1 \/ c mod 8 = 2 \/ c mod 8 = 3 \/
               c mod 8 = 4 \/ c mod 8 = 5 \/ c mod 8 = 6 \/ c mod 8 = 7)
    by lia.
  destruct Hr as [H0|[H0|[H0|[H0|[H0|[H0|[H0|H0]]]]]]];
    rewrite H0 in H |- *; simpl in H; solve [discriminate | reflexivity].
Qed.

Lemma w11_eq2 : forall c f, w11 c f = 2 -> c mod 4 = 2.
Proof.
  intros c f H; unfold w11 in H.
  destruct ((c mod 4) =? 2) eqn:E; [apply Z.eqb_eq; exact E|].
  destruct (Nat.odd f); destruct (Z.even c); discriminate.
Qed.

Lemma w11_eq4 : forall c f, w11 c f = 4 -> c mod 4 = 0.
Proof.
  intros c f H; unfold w11 in H.
  pose proof (Z.mod_pos_bound c 4 ltac:(lia)) as Hb.
  destruct ((c mod 4) =? 2) eqn:E; [discriminate|].
  apply Z.eqb_neq in E.
  destruct (Nat.odd f).
  - destruct (Z.even c); discriminate.
  - destruct (Z.even c) eqn:Ec; [|discriminate].
    rewrite (even_mod4 c) in Ec.
    assert (Hr : c mod 4 = 0 \/ c mod 4 = 1 \/ c mod 4 = 2 \/ c mod 4 = 3)
      by lia.
    destruct Hr as [H0|[H0|[H0|H0]]]; rewrite H0 in Ec;
      solve [exact H0 | simpl in Ec; discriminate | lia].
Qed.

Lemma w38_eq2 : forall c f, w38 c f = 2 -> c mod 4 = 2.
Proof.
  intros c f H; unfold w38 in H.
  destruct (2 <=? c + 4 * Z.of_nat f);
    [apply w10_eq2 | apply (w11_eq2 c f)]; exact H.
Qed.

Lemma w38_eq4 : forall c f, w38 c f = 4 -> c mod 4 = 0.
Proof.
  intros c f H; unfold w38 in H.
  destruct (2 <=? c + 4 * Z.of_nat f);
    [apply w10_eq4 | apply (w11_eq4 c f)]; exact H.
Qed.

Lemma w38_step :
  forall c f, 4 - w38 (c + 4) f = w38 c (S f).
Proof.
  intros c f; unfold w38.
  replace (c + 4 + 4 * Z.of_nat f) with (c + 4 * Z.of_nat (S f))
    by (rewrite Nat2Z.inj_succ; lia).
  destruct (2 <=? c + 4 * Z.of_nat (S f));
    [apply w10_step | apply w11_step].
Qed.

Lemma count4_perm : forall G H, Permutation G H -> count4 G = count4 H.
Proof.
  intros G H HP; unfold count4.
  apply Permutation_length, filter_perm; exact HP.
Qed.

Lemma count4_pos_iff :
  forall G, existsb is_4loop_b G = true <-> (0 < count4 G)%nat.
Proof.
  induction G as [|C G IH]; simpl;
    [unfold count4; simpl; split; [discriminate | lia]|].
  rewrite count4_cons.
  destruct (is_4loop_b C); simpl; split; intros H; try lia; try reflexivity.
  - apply IH in H; lia.
  - apply IH; lia.
Qed.

Lemma cbase_repeat_loop4 :
  forall f, cbase (repeat (Loop 4) f) = -4 * Z.of_nat f.
Proof.
  induction f as [|f IH]; [reflexivity|].
  change (cbase (repeat (Loop 4) (S f)))
    with (weight (Loop 4) + cbase (repeat (Loop 4) f)).
  rewrite IH, weight_loop_len; lia.
Qed.

Lemma forallb_loop_repeat4 :
  forall f, forallb is_loop_b (repeat (Loop 4) f) = true.
Proof. induction f as [|f IH]; [reflexivity | simpl; exact IH]. Qed.

Lemma cval_mix0 :
  forall f, (1 <= f)%nat -> cval (mix 0 f) = 8 - 4 * Z.of_nat f.
Proof.
  intros f Hf.
  change (mix 0 f) with (repeat (Loop 4) f).
  unfold cval; rewrite cbase_repeat_loop4.
  rewrite (tb_all_loops (repeat (Loop 4) f));
    [lia | destruct f; [lia | discriminate] | apply forallb_loop_repeat4].
Qed.

Lemma w10_small : forall c, -2 <= c <= 1 -> w10 c = Z.abs c.
Proof.
  intros c H.
  assert (Hc : c = -2 \/ c = -1 \/ c = 0 \/ c = 1) by lia.
  destruct Hc as [H1 | [H1 | [H1 | H1]]]; rewrite H1; reflexivity.
Qed.

(** With no three-chains and a controlled value below two, the value is given
    by the residue formulas. *)
Lemma value_no3_aux :
  forall n G, (length G <= n)%nat ->
    wf G -> G <> [] ->
    existsb is_3chain_b G = false ->
    cval G < 2 ->
    value G = w38 (cval G) (count4 G).
Proof.
  induction n as [|n IH]; intros G Hn HG HNil H3 Hc.
  - exfalso; apply HNil; destruct G; [reflexivity | simpl in Hn; lia].
  - destruct (existsb is_4loop_b G) eqn:E4.
    + destruct (only34 G) eqn:Eo.
      * (* only four-loops remain *)
        assert (Hc3 : count3 G = 0%nat).
        { destruct (count3 G) eqn:Ecc; [reflexivity|].
          exfalso.
          assert (Hbad : existsb is_3chain_b G = true)
            by (apply count3_pos_iff; lia).
          congruence. }
        pose proof (perm_mix_of_only34 G Eo) as Hperm.
        rewrite Hc3 in Hperm.
        assert (Hf : (1 <= count4 G)%nat) by (apply count4_pos_iff; exact E4).
        rewrite (value_perm G _ Hperm), value_mix.
        rewrite (cval_perm G _ Hperm), (cval_mix0 (count4 G) Hf).
        unfold w38.
        replace (8 - 4 * Z.of_nat (count4 G) + 4 * Z.of_nat (count4 G))
          with 8 by lia.
        simpl (2 <=? 8).
        rewrite w10_allloops; reflexivity.
      * destruct (Z_le_gt_dec (-2) (cval G)) as [Hge | Hlt].
        -- (* a controlled value of at least minus two *)
           assert (Hf : (1 <= count4 G)%nat)
             by (apply count4_pos_iff; exact E4).
           rewrite (value_with_4loop G HG E4 Eo Hge).
           unfold w38.
           assert (Hb : 2 <=? cval G + 4 * Z.of_nat (count4 G) = true)
             by (apply Z.leb_le; lia).
           rewrite Hb; symmetry; apply w10_small; lia.
        -- (* the induction step: open a four-loop *)
           assert (Hex : existsb
                     (fun C => negb (is_3chain_b C || is_4loop_b C)%bool) G
                   = true)
             by (unfold only34 in Eo; rewrite <- negb_forallb, Eo; reflexivity).
           apply existsb_exists in Hex; destruct Hex as [D [HD HDn]].
           apply negb_true_iff, orb_false_iff in HDn; destruct HDn as [HD3 HD4].
           assert (HwD : wf_comp D)
             by (unfold wf in HG; rewrite Forall_forall in HG; apply HG;
                 exact HD).
           assert (HIn4 : In (Loop 4) G).
           { apply existsb_exists in E4; destruct E4 as [C [HC HC4]].
             rewrite <- (is_4loop_eq C HC4); exact HC. }
           destruct (In_selections G (Loop 4) HIn4) as [rest Hsel].
           pose proof (selections_perm G (Loop 4, rest) Hsel) as Hperm;
             cbn [fst snd] in Hperm.
           pose proof (selections_length G (Loop 4, rest) Hsel) as Hlen;
             cbn [fst snd] in Hlen.
           pose proof (selections_wf G (Loop 4, rest) HG Hsel) as [Hw4 Hwr];
             cbn [fst snd] in Hw4, Hwr.
           pose proof (selections_cval G (Loop 4, rest) Hsel) as Hcv;
             cbn [fst snd] in Hcv.
           rewrite weight_loop_len in Hcv.
           assert (HDrest : In D rest).
           { assert (HDG : In D (Loop 4 :: rest))
               by (eapply Permutation_in;
                   [apply Permutation_sym; exact Hperm | exact HD]).
             destruct HDG as [HDeq | HDr]; [|exact HDr].
             exfalso; rewrite <- HDeq in HD4; discriminate. }
           assert (HrNil : rest <> [])
             by (destruct rest; [destruct HDrest | discriminate]).
           assert (Htbeq : tb (Loop 4 :: rest) = tb rest)
             by (apply (tb_remove_4loop rest D); assumption).
           assert (Hcr : cval rest = cval G + 4)
             by (unfold cval in *; rewrite Htbeq in Hcv; simpl Z.of_nat in Hcv;
                 lia).
           assert (Hf4 : count4 G = S (count4 rest)).
           { rewrite <- (count4_perm (Loop 4 :: rest) G Hperm), count4_cons;
               reflexivity. }
           assert (H3r : existsb is_3chain_b rest = false)
             by (apply (existsb_false_tail is_3chain_b (Loop 4) rest G Hperm H3)).
           assert (Hvr : value rest = w38 (cval rest) (count4 rest))
             by (apply IH; [lia | exact Hwr | exact HrNil | exact H3r | lia]).
           assert (Hopt : value_open (Loop 4, rest) =
                          w38 (cval G) (count4 G)).
           { unfold value_open; cbn [fst snd]; rewrite Hvr, vopen_loop4.
             pose proof (w38_range (cval rest) (count4 rest)) as Hrg.
             rewrite Hcr, Hf4.
             replace (Z.abs (w38 (cval G + 4) (count4 rest) - 4))
               with (4 - w38 (cval G + 4) (count4 rest))
               by (rewrite Hcr in Hrg; lia).
             apply w38_step. }
           assert (Hmin : forall q, In q (selections G) ->
                     value_open (Loop 4, rest) <= value_open q).
           { intros q Hq.
             destruct (is_4loop_b (fst q)) eqn:Eq4.
             - assert (HqC : fst q = Loop 4) by (apply is_4loop_eq; exact Eq4).
               assert (Hpq : Permutation (snd q) rest).
               { apply (Permutation_cons_inv (a := Loop 4)).
                 eapply Permutation_trans;
                   [rewrite <- HqC; apply selections_perm; exact Hq
                    | apply Permutation_sym; exact Hperm]. }
               unfold value_open; cbn [fst snd]; rewrite HqC.
               rewrite (value_perm (snd q) rest Hpq); lia.
             - destruct (Z_le_gt_dec (value_open (Loop 4, rest)) (value_open q))
                 as [Hle | Hgt]; [exact Hle | exfalso].
               pose proof (value_open_ge_demand G q Hq) as Hdq.
               pose proof (selections_wf G q HG Hq) as [Hwq Hwrq].
               pose proof (selections_In G q Hq) as HInq.
               assert (Hq3 : is_3chain_b (fst q) = false).
               { destruct (is_3chain_b (fst q)) eqn:E; [|reflexivity].
                 exfalso.
                 assert (Hbad : existsb is_3chain_b G = true)
                   by (apply (proj2 (existsb_exists is_3chain_b G));
                       exists (fst q); split; assumption).
                 congruence. }
               assert (Hdem : 2 <= demand (fst q))
                 by (apply demand_of_no34; assumption).
               pose proof (value_open_parity G (Loop 4, rest) Hsel) as Hp1.
               pose proof (value_open_parity G q Hq) as Hp2.
               assert (Hgap : value_open q + 2 <= value_open (Loop 4, rest))
                 by (apply even_eq_diff2;
                     [rewrite Hp2, <- Hp1; reflexivity | lia]).
               rewrite Hopt in Hgap.
               pose proof (w38_range (cval G) (count4 G)) as Hrg.
               assert (Hq2 : value_open q = 2) by lia.
               assert (Hw4v : w38 (cval G) (count4 G) = 4) by lia.
               assert (Hdem2 : demand (fst q) = 2) by lia.
               pose proof (w38_eq4 _ _ Hw4v) as Hcmod.
               pose proof (selections_size G q Hq) as Hszq.
               pose proof (selections_length G q Hq) as Hlenq.
               assert (HqNil : snd q <> []).
               { intros Hnil.
                 pose proof (selections_perm G q Hq) as Hpq0.
                 rewrite Hnil in Hpq0.
                 assert (HDq : D = fst q).
                 { pose proof (Permutation_in D (Permutation_sym Hpq0) HD)
                     as HDin.
                   destruct HDin as [He | []]; symmetry; exact He. }
                 assert (H4q : Loop 4 = fst q).
                 { pose proof
                     (Permutation_in (Loop 4) (Permutation_sym Hpq0) HIn4)
                     as H4in.
                   destruct H4in as [He | []]; symmetry; exact He. }
                 rewrite HDq, <- H4q in HD4; discriminate. }
               assert (H3q : existsb is_3chain_b (snd q) = false)
                 by (apply (existsb_false_tail is_3chain_b (fst q) (snd q) G);
                     [apply selections_perm; exact Hq | exact H3]).
               assert (Hmod_q : (Z.of_nat (size (snd q))) mod 4
                                = (cval (snd q)) mod 4).
               { destruct (size_cval_mod4 (snd q) H3q) as [qq Hqq].
                 replace (Z.of_nat (size (snd q))) with (cval (snd q) + qq * 4)
                   by lia.
                 apply Z_mod_plus_full. }
               assert (Hmod_G : (Z.of_nat (size G)) mod 4 = (cval G) mod 4).
               { destruct (size_cval_mod4 G H3) as [qq Hqq].
                 replace (Z.of_nat (size G)) with (cval G + qq * 4) by lia.
                 apply Z_mod_plus_full. }
               assert (Hvq : value (snd q) = w38 (cval (snd q)) (count4 (snd q))
                             \/ value (snd q) = cval (snd q)).
               { destruct (Z_le_gt_dec 2 (cval (snd q))) as [Hge2 | Hlt2].
                 - right; apply value_cval_ge2; assumption.
                 - left; apply IH;
                     [lia | exact Hwrq | exact HqNil | exact H3q | lia]. }
               destruct (demand_eq2 (fst q) Hwq Hdem2) as [HC4 | HC6].
               + assert (Hv2 : value (snd q) = 2).
                 { unfold value_open in Hq2; rewrite HC4, vopen_chain4 in Hq2.
                   pose proof (Z.abs_nonneg (value (snd q) - 2)) as Hab.
                   assert (Hz : Z.abs (value (snd q) - 2) = 0) by lia.
                   apply Z.abs_0_iff in Hz; lia. }
                 assert (Hcq2 : cval (snd q) mod 4 = 2).
                 { destruct Hvq as [Hw | Heq].
                   - rewrite Hv2 in Hw; symmetry in Hw; apply (w38_eq2 _ _ Hw).
                   - rewrite Hv2 in Heq; rewrite <- Heq; reflexivity. }
                 assert (Hs : Z.of_nat (size G) = Z.of_nat (size (snd q)) + 4)
                   by (rewrite HC4 in Hszq; simpl csize in Hszq; lia).
                 assert (Hbad : cval G mod 4 = 2).
                 { rewrite <- Hmod_G, Hs.
                   replace (Z.of_nat (size (snd q)) + 4)
                     with (Z.of_nat (size (snd q)) + 1 * 4) by lia.
                   rewrite Z_mod_plus_full, Hmod_q; exact Hcq2. }
                 lia.
               + assert (Hv4 : value (snd q) = 4).
                 { unfold value_open in Hq2; rewrite HC6, vopen_loop6 in Hq2.
                   pose proof (Z.abs_nonneg (value (snd q) - 4)) as Hab.
                   assert (Hz : Z.abs (value (snd q) - 4) = 0) by lia.
                   apply Z.abs_0_iff in Hz; lia. }
                 assert (Hcq0 : cval (snd q) mod 4 = 0).
                 { destruct Hvq as [Hw | Heq].
                   - rewrite Hv4 in Hw; symmetry in Hw; apply (w38_eq4 _ _ Hw).
                   - rewrite Hv4 in Heq; rewrite <- Heq; reflexivity. }
                 assert (Hs : Z.of_nat (size G) = Z.of_nat (size (snd q)) + 6)
                   by (rewrite HC6 in Hszq; simpl csize in Hszq; lia).
                 assert (Hbad : cval G mod 4 = 2).
                 { rewrite <- Hmod_G, Hs.
                   replace (Z.of_nat (size (snd q)) + 6)
                     with ((Z.of_nat (size (snd q)) + 2) + 1 * 4) by lia.
                   rewrite Z_mod_plus_full.
                   rewrite <- Z.add_mod_idemp_l by lia.
                   rewrite Hmod_q, Hcq0; reflexivity. }
                 lia. }
           rewrite (value_of_min_option G (Loop 4, rest) Hsel Hmin); exact Hopt.
    + (* no four-loops at all *)
      assert (Hf0 : count4 G = 0%nat).
      { destruct (count4 G) eqn:Ef; [reflexivity|].
        exfalso.
        assert (Hbad : existsb is_4loop_b G = true)
          by (apply count4_pos_iff; lia).
        congruence. }
      rewrite (value_no34 G HG HNil H3 E4 ltac:(lia)).
      rewrite (size_cval_w4z G H3), Hf0.
      unfold w38.
      replace (cval G + 4 * Z.of_nat 0) with (cval G) by (simpl; lia).
      assert (Hb : 2 <=? cval G = false) by (apply Z.leb_gt; lia).
      rewrite Hb; symmetry; apply w11_f0.
Qed.

Theorem value_no3 :
  forall G,
    wf G -> G <> [] ->
    existsb is_3chain_b G = false ->
    cval G < 2 ->
    value G = w38 (cval G) (count4 G).
Proof. intros G; apply (value_no3_aux (length G)); lia. Qed.

(** * One three-chain on an odd board *)

Lemma tb_even : forall G, Z.even (tb G) = true.
Proof.
  intros [|C G]; [reflexivity|].
  rewrite tb_cons_form.
  destruct (forallb is_loop_b (C :: G)); [reflexivity|].
  destruct (existsb is_loop_b (C :: G) &&
            forallb (fun D => is_loop_b D || is_3chain_b D) (C :: G))%bool;
    reflexivity.
Qed.

Lemma cval_parity :
  forall G, Z.even (cval G) = Z.even (Z.of_nat (size G)).
Proof.
  intros G; unfold cval.
  destruct (handsum_even G) as [m Hm].
  pose proof (size_minus_cbase G) as Hs; rewrite Hm in Hs.
  rewrite Z.even_add, tb_even.
  assert (Hc : Z.of_nat (size G) = cbase G + 2 * Z.of_nat (2 * m))
    by lia.
  rewrite Hc, Z.even_add, Z.even_mul; simpl (Z.even 2).
  destruct (Z.even (cbase G)); reflexivity.
Qed.

Lemma mod8_of_mod4_0 :
  forall c, c mod 4 = 0 -> c mod 8 = 0 \/ c mod 8 = 4.
Proof.
  intros c H.
  pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as Hb.
  rewrite mod4_of_mod8 in H.
  assert (Hr : c mod 8 = 0 \/ c mod 8 = 1 \/ c mod 8 = 2 \/ c mod 8 = 3 \/
               c mod 8 = 4 \/ c mod 8 = 5 \/ c mod 8 = 6 \/ c mod 8 = 7)
    by lia.
  destruct Hr as [H0|[H0|[H0|[H0|[H0|[H0|[H0|H0]]]]]]];
    rewrite H0 in H; simpl in H; try discriminate; auto.
Qed.

Lemma w38_mod4_0 :
  forall c f, c mod 4 = 0 -> w38 c f = 0 \/ w38 c f = 4.
Proof.
  intros c f H; unfold w38.
  destruct (2 <=? c + 4 * Z.of_nat f).
  - unfold w10.
    destruct (mod8_of_mod4_0 c H) as [H8 | H8]; rewrite H8;
      [left | right]; reflexivity.
  - unfold w11.
    assert (E2 : (c mod 4) =? 2 = false) by (rewrite H; reflexivity).
    rewrite E2.
    assert (Hev : Z.even c = true)
      by (rewrite (even_mod4 c), H; reflexivity).
    rewrite Hev; destruct (Nat.odd f); [left | right]; reflexivity.
Qed.

Definition w13 (c : Z) : Z :=
  if ((c mod 8) =? 1) || ((c mod 8) =? 7) then 1 else 3.

Definition w14 (f : nat) : Z := if Nat.odd f then 1 else 3.

Definition w310 (c : Z) (f : nat) : Z :=
  if 2 <=? c + 4 * Z.of_nat f then w13 c else w14 f.

Lemma w13_range : forall c, w13 c = 1 \/ w13 c = 3.
Proof.
  intros c; unfold w13.
  destruct (((c mod 8) =? 1) || ((c mod 8) =? 7))%bool; [left | right];
    reflexivity.
Qed.

Lemma w14_range : forall f, w14 f = 1 \/ w14 f = 3.
Proof.
  intros f; unfold w14; destruct (Nat.odd f); [left | right]; reflexivity.
Qed.

Lemma w310_range : forall c f, w310 c f = 1 \/ w310 c f = 3.
Proof.
  intros c f; unfold w310.
  destruct (2 <=? c + 4 * Z.of_nat f); [apply w13_range | apply w14_range].
Qed.

Lemma even_mod8 : forall s, Z.even s = Z.even (s mod 8).
Proof.
  intros s.
  rewrite (Z.div_mod s 8) at 1 by lia.
  rewrite Z.even_add, Z.even_mul; simpl (Z.even 8).
  destruct (Z.even (s mod 8)); reflexivity.
Qed.

Lemma w13_step : forall c, Z.even c = false -> 4 - w13 (c + 4) = w13 c.
Proof.
  intros c Hodd.
  pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as Hb.
  assert (H : (c + 4) mod 8 = ((c mod 8) + 4) mod 8)
    by (rewrite Z.add_mod_idemp_l by lia; reflexivity).
  rewrite (even_mod8 c) in Hodd.
  unfold w13; rewrite H.
  assert (Hr : c mod 8 = 0 \/ c mod 8 = 1 \/ c mod 8 = 2 \/ c mod 8 = 3 \/
               c mod 8 = 4 \/ c mod 8 = 5 \/ c mod 8 = 6 \/ c mod 8 = 7)
    by lia.
  destruct Hr as [H0|[H0|[H0|[H0|[H0|[H0|[H0|H0]]]]]]];
    rewrite H0 in Hodd |- *; simpl in Hodd;
    solve [discriminate | reflexivity].
Qed.

Lemma w14_step : forall f, 4 - w14 f = w14 (S f).
Proof.
  intros f; unfold w14; rewrite odd_S; destruct (Nat.odd f); simpl; lia.
Qed.

Lemma w310_step :
  forall c f, Z.even c = false -> 4 - w310 (c + 4) f = w310 c (S f).
Proof.
  intros c f Hodd; unfold w310.
  replace (c + 4 + 4 * Z.of_nat f) with (c + 4 * Z.of_nat (S f))
    by (rewrite Nat2Z.inj_succ; lia).
  destruct (2 <=? c + 4 * Z.of_nat (S f));
    [apply w13_step; exact Hodd | apply w14_step].
Qed.

Lemma w13_pm1 : forall c, c = -1 \/ c = 1 -> w13 c = 1.
Proof.
  intros c [-> | ->]; reflexivity.
Qed.

Lemma w13_mix1 :
  forall f, w13 (5 - 4 * Z.of_nat f) = (if Nat.even f then 3 else 1).
Proof.
  intros f; unfold w13.
  destruct (Nat.even f) eqn:Ef.
  - apply Nat.even_spec in Ef; destruct Ef as [k Hk]; subst f.
    assert (H : (5 - 4 * Z.of_nat (2 * k)) mod 8 = 5)
      by (replace (5 - 4 * Z.of_nat (2 * k)) with (5 + (- Z.of_nat k) * 8)
            by lia;
          rewrite Z_mod_plus_full; reflexivity).
    rewrite H; reflexivity.
  - assert (Ho : Nat.odd f = true)
      by (rewrite <- Nat.negb_even, Ef; reflexivity).
    apply Nat.odd_spec in Ho; destruct Ho as [k Hk]; subst f.
    assert (H : (5 - 4 * Z.of_nat (2 * k + 1)) mod 8 = 1)
      by (replace (5 - 4 * Z.of_nat (2 * k + 1)) with (1 + (- Z.of_nat k) * 8)
            by lia;
          rewrite Z_mod_plus_full; reflexivity).
    rewrite H; reflexivity.
Qed.

Lemma tb_rise_last_3chain :
  forall rest,
    rest <> [] ->
    existsb is_3chain_b rest = false ->
    tb rest - tb (Chain 3 :: rest) <= 2.
Proof.
  intros rest HrNil H3r.
  assert (Htb4 : tb rest = 4 \/ tb rest = 8).
  { destruct (tb_no_three_chain rest H3r) as [E | [E | E]];
      [| left; exact E | right; exact E].
    exfalso; pose proof (tb_pos rest HrNil); lia. }
  destruct Htb4 as [E4 | E8].
  - pose proof (tb_pos (Chain 3 :: rest) ltac:(discriminate)); lia.
  - assert (HL : forallb is_loop_b rest = true)
      by (apply tb_eight_all_loops; assumption).
    rewrite (tb_six_of_loops_and_three rest HL HrNil); lia.
Qed.

Lemma cval_mix1 :
  forall f, (1 <= f)%nat -> cval (mix 1 f) = 5 - 4 * Z.of_nat f.
Proof.
  intros f Hf.
  change (mix 1 f) with (Chain 3 :: repeat (Loop 4) f).
  unfold cval; rewrite cbase_cons, cbase_repeat_loop4, weight_chain.
  rewrite (tb_six_of_loops_and_three (repeat (Loop 4) f));
    [lia | apply forallb_loop_repeat4 | destruct f; [lia | discriminate]].
Qed.

(** With exactly one three-chain and a board of three modulo four, the value
    alternates with the number of four-loops. *)
Lemma value_theta1_odd_aux :
  forall n G, (length G <= n)%nat ->
    wf G ->
    count3 G = 1%nat ->
    (Z.of_nat (size G)) mod 4 = 3 ->
    cval G < 2 ->
    value G = w310 (cval G) (count4 G).
Proof.
  induction n as [|n IH]; intros G Hn HG Ht1 Hmod Hc.
  - exfalso.
    assert (HGnil : G = []) by (destruct G; simpl in Hn; [reflexivity | lia]).
    subst G; unfold count3 in Ht1; simpl in Ht1; discriminate.
  - assert (H3 : existsb is_3chain_b G = true)
      by (apply count3_pos_iff; lia).
    assert (HNil : G <> []) by (intros Hz; rewrite Hz in H3; discriminate).
    assert (Hodd : Z.even (cval G) = false).
    { rewrite cval_parity, (even_mod4 (Z.of_nat (size G))), Hmod; reflexivity. }
    destruct (existsb is_4loop_b G) eqn:E4.
    + destruct (only34 G) eqn:Eo.
      * pose proof (perm_mix_of_only34 G Eo) as Hperm.
        rewrite Ht1 in Hperm.
        assert (Hf : (1 <= count4 G)%nat) by (apply count4_pos_iff; exact E4).
        rewrite (value_perm G _ Hperm), value_mix.
        rewrite (cval_perm G _ Hperm), (cval_mix1 (count4 G) Hf).
        unfold w310.
        replace (5 - 4 * Z.of_nat (count4 G) + 4 * Z.of_nat (count4 G))
          with 5 by lia.
        simpl (2 <=? 5).
        rewrite w13_mix1; reflexivity.
      * destruct (Z_le_gt_dec (-2) (cval G)) as [Hge | Hlt].
        -- rewrite (value_with_4loop G HG E4 Eo Hge).
           assert (Hf : (1 <= count4 G)%nat)
             by (apply count4_pos_iff; exact E4).
           unfold w310.
           assert (Hb : 2 <=? cval G + 4 * Z.of_nat (count4 G) = true)
             by (apply Z.leb_le; lia).
           rewrite Hb.
           assert (Hc1 : cval G = -1 \/ cval G = 1).
           { assert (Hcc : cval G = -2 \/ cval G = -1 \/ cval G = 0 \/
                           cval G = 1) by lia.
             destruct Hcc as [E|[E|[E|E]]]; rewrite E in Hodd;
               try discriminate; rewrite E; [left | right]; reflexivity. }
           rewrite (w13_pm1 (cval G) Hc1).
           destruct Hc1 as [E | E]; rewrite E; reflexivity.
        -- assert (Hex : existsb
                     (fun C => negb (is_3chain_b C || is_4loop_b C)%bool) G
                   = true)
             by (unfold only34 in Eo; rewrite <- negb_forallb, Eo; reflexivity).
           apply existsb_exists in Hex; destruct Hex as [D [HD HDn]].
           apply negb_true_iff, orb_false_iff in HDn; destruct HDn as [HD3 HD4].
           assert (HwD : wf_comp D)
             by (unfold wf in HG; rewrite Forall_forall in HG; apply HG;
                 exact HD).
           assert (HIn4 : In (Loop 4) G).
           { apply existsb_exists in E4; destruct E4 as [C [HC HC4]].
             rewrite <- (is_4loop_eq C HC4); exact HC. }
           (* the three-chain option is worth three *)
           assert (HIn3 : In (Chain 3) G)
             by (apply count3_In; lia).
           destruct (In_selections G (Chain 3) HIn3) as [rest3 Hsel3].
           pose proof (selections_perm G (Chain 3, rest3) Hsel3) as Hperm3;
             cbn [fst snd] in Hperm3.
           pose proof (selections_length G (Chain 3, rest3) Hsel3) as Hlen3;
             cbn [fst snd] in Hlen3.
           pose proof (selections_wf G (Chain 3, rest3) HG Hsel3)
             as [Hw3c Hwr3]; cbn [fst snd] in Hw3c, Hwr3.
           pose proof (selections_size G (Chain 3, rest3) Hsel3) as Hsz3;
             cbn [fst snd] in Hsz3.
           pose proof (selections_cval G (Chain 3, rest3) Hsel3) as Hcv3;
             cbn [fst snd] in Hcv3.
           rewrite weight_chain in Hcv3.
           assert (H3r3 : existsb is_3chain_b rest3 = false).
           { destruct (existsb is_3chain_b rest3) eqn:E; [|reflexivity].
             exfalso.
             assert (Hc3 : (0 < count3 rest3)%nat)
               by (apply count3_pos_iff; exact E).
             assert (Hcc : count3 G = S (count3 rest3))
               by (rewrite <- (count3_perm (Chain 3 :: rest3) G Hperm3),
                   count3_cons; reflexivity).
             lia. }
           assert (Hr3Nil : rest3 <> []).
           { intros Hz.
             assert (HDG : In D (Chain 3 :: rest3))
               by (eapply Permutation_in;
                   [apply Permutation_sym; exact Hperm3 | exact HD]).
             rewrite Hz in HDG; destruct HDG as [He | []].
             rewrite <- He in HD3; discriminate. }
           assert (Hrise3 : tb rest3 - tb (Chain 3 :: rest3) <= 2)
             by (apply tb_rise_last_3chain; assumption).
           assert (Hcr3 : cval rest3 < 2)
             by (unfold cval in *; lia).
           assert (Hm0 : (Z.of_nat (size rest3)) mod 4 = 0).
           { replace (Z.of_nat (size rest3))
               with (Z.of_nat (size G) + (-3))
               by (simpl csize in Hsz3; lia).
             rewrite <- Z.add_mod_idemp_l by lia.
             rewrite Hmod; reflexivity. }
           assert (Hcm0 : cval rest3 mod 4 = 0).
           { destruct (size_cval_mod4 rest3 H3r3) as [qq Hqq].
             rewrite <- Hm0.
             replace (Z.of_nat (size rest3)) with (cval rest3 + qq * 4) by lia.
             rewrite Z_mod_plus_full; reflexivity. }
           assert (Hv3 : value rest3 = w38 (cval rest3) (count4 rest3))
             by (apply value_no3; assumption).
           assert (Hopt3 : value_open (Chain 3, rest3) = 3).
           { unfold value_open; cbn [fst snd]; rewrite vopen_chain3_abs, Hv3.
             destruct (w38_mod4_0 (cval rest3) (count4 rest3) Hcm0) as [E | E];
               rewrite E; reflexivity. }
           (* the four-loop option *)
           destruct (In_selections G (Loop 4) HIn4) as [rest Hsel].
           pose proof (selections_perm G (Loop 4, rest) Hsel) as Hperm;
             cbn [fst snd] in Hperm.
           pose proof (selections_length G (Loop 4, rest) Hsel) as Hlen;
             cbn [fst snd] in Hlen.
           pose proof (selections_wf G (Loop 4, rest) HG Hsel) as [Hw4 Hwr];
             cbn [fst snd] in Hw4, Hwr.
           pose proof (selections_size G (Loop 4, rest) Hsel) as Hsz;
             cbn [fst snd] in Hsz.
           pose proof (selections_cval G (Loop 4, rest) Hsel) as Hcv;
             cbn [fst snd] in Hcv.
           rewrite weight_loop_len in Hcv.
           assert (HDrest : In D rest).
           { assert (HDG : In D (Loop 4 :: rest))
               by (eapply Permutation_in;
                   [apply Permutation_sym; exact Hperm | exact HD]).
             destruct HDG as [HDeq | HDr]; [|exact HDr].
             exfalso; rewrite <- HDeq in HD4; discriminate. }
           assert (HrNil : rest <> [])
             by (destruct rest; [destruct HDrest | discriminate]).
           assert (Htbeq : tb (Loop 4 :: rest) = tb rest)
             by (apply (tb_remove_4loop rest D); assumption).
           assert (Hcr : cval rest = cval G + 4)
             by (unfold cval in *; rewrite Htbeq in Hcv;
                 simpl Z.of_nat in Hcv; lia).
           assert (Hf4 : count4 G = S (count4 rest))
             by (rewrite <- (count4_perm (Loop 4 :: rest) G Hperm),
                 count4_cons; reflexivity).
           assert (Ht1r : count3 rest = 1%nat).
           { rewrite <- (count3_perm (Loop 4 :: rest) G Hperm) in Ht1.
             rewrite count3_cons in Ht1; exact Ht1. }
           assert (Hmodr : (Z.of_nat (size rest)) mod 4 = 3).
           { replace (Z.of_nat (size rest))
               with (Z.of_nat (size G) + (-1) * 4)
               by (simpl csize in Hsz; lia).
             rewrite Z_mod_plus_full; exact Hmod. }
           assert (Hvr : value rest = w310 (cval rest) (count4 rest))
             by (apply IH; [lia | exact Hwr | exact Ht1r | exact Hmodr | lia]).
           assert (Hopt : value_open (Loop 4, rest) =
                          w310 (cval G) (count4 G)).
           { unfold value_open; cbn [fst snd]; rewrite Hvr, vopen_loop4.
             pose proof (w310_range (cval rest) (count4 rest)) as Hrg.
             rewrite Hcr, Hf4.
             replace (Z.abs (w310 (cval G + 4) (count4 rest) - 4))
               with (4 - w310 (cval G + 4) (count4 rest))
               by (rewrite Hcr in Hrg; lia).
             apply w310_step; exact Hodd. }
           assert (Hmin : forall q, In q (selections G) ->
                     value_open (Loop 4, rest) <= value_open q).
           { intros q Hq.
             pose proof (w310_range (cval G) (count4 G)) as Hrg.
             destruct (is_4loop_b (fst q)) eqn:Eq4.
             - assert (HqC : fst q = Loop 4) by (apply is_4loop_eq; exact Eq4).
               assert (Hpq : Permutation (snd q) rest).
               { apply (Permutation_cons_inv (a := Loop 4)).
                 eapply Permutation_trans;
                   [rewrite <- HqC; apply selections_perm; exact Hq
                    | apply Permutation_sym; exact Hperm]. }
               unfold value_open; cbn [fst snd]; rewrite HqC.
               rewrite (value_perm (snd q) rest Hpq); lia.
             - destruct (is_3chain_b (fst q)) eqn:Eq3.
               + assert (HqC : fst q = Chain 3)
                   by (apply is_3chain_eq; exact Eq3).
                 assert (Hpq : Permutation (snd q) rest3).
                 { apply (Permutation_cons_inv (a := Chain 3)).
                   eapply Permutation_trans;
                     [rewrite <- HqC; apply selections_perm; exact Hq
                      | apply Permutation_sym; exact Hperm3]. }
                 assert (Hqv : value_open q = 3).
                 { unfold value_open in Hopt3 |- *; cbn [fst snd] in Hopt3 |- *.
                   rewrite HqC, (value_perm (snd q) rest3 Hpq); exact Hopt3. }
                 rewrite Hopt, Hqv; lia.
               + pose proof (value_open_ge_demand G q Hq) as Hdq.
                 pose proof (selections_wf G q HG Hq) as [Hwq _].
                 assert (Hdem : 2 <= demand (fst q))
                   by (apply demand_of_no34; assumption).
                 pose proof (value_open_parity G q Hq) as Hp2.
                 assert (Hsodd : Z.even (Z.of_nat (size G)) = false)
                   by (rewrite (even_mod4 (Z.of_nat (size G))), Hmod;
                       reflexivity).
                 rewrite Hsodd in Hp2.
                 assert (Hq3v : 3 <= value_open q).
                 { destruct (Z_le_gt_dec 3 (value_open q)) as [Hok | Hbad];
                     [exact Hok|].
                   exfalso.
                   assert (Hv2 : value_open q = 2) by lia.
                   rewrite Hv2 in Hp2; discriminate. }
                 rewrite Hopt; lia. }
           rewrite (value_of_min_option G (Loop 4, rest) Hsel Hmin); exact Hopt.
    + (* no four-loops *)
      assert (Hf0 : count4 G = 0%nat).
      { destruct (count4 G) eqn:Ef; [reflexivity|].
        exfalso.
        assert (Hbad : existsb is_4loop_b G = true)
          by (apply count4_pos_iff; lia).
        congruence. }
      rewrite (value_no4_with3 G HG E4 H3 Hc), Ht1.
      unfold w310, w35z; rewrite Hf0.
      replace (cval G + 4 * Z.of_nat 0) with (cval G) by (simpl; lia).
      assert (Hb : 2 <=? cval G = false) by (apply Z.leb_gt; lia).
      rewrite Hb.
      assert (Hsodd : Z.even (Z.of_nat (size G)) = false)
        by (rewrite (even_mod4 (Z.of_nat (size G))), Hmod; reflexivity).
      rewrite Hsodd.
      assert (Hb2 : (Z.of_nat (size G) mod 4 =? 3) = true)
        by (rewrite Hmod; reflexivity).
      rewrite Hb2; reflexivity.
Qed.

Theorem value_theta1_odd :
  forall G,
    wf G ->
    count3 G = 1%nat ->
    (Z.of_nat (size G)) mod 4 = 3 ->
    cval G < 2 ->
    value G = w310 (cval G) (count4 G).
Proof. intros G; apply (value_theta1_odd_aux (length G)); lia. Qed.

(** * Two or more three-chains *)

Lemma w38_mod4_ne0 :
  forall c f, c mod 4 <> 0 -> 1 <= w38 c f <= 3.
Proof.
  intros c f H.
  pose proof (Z.mod_pos_bound c 4 ltac:(lia)) as Hb4.
  unfold w38.
  destruct (2 <=? c + 4 * Z.of_nat f).
  - unfold w10.
    pose proof (Z.mod_pos_bound c 8 ltac:(lia)) as Hb8.
    rewrite mod4_of_mod8 in H.
    assert (Hr : c mod 8 = 0 \/ c mod 8 = 1 \/ c mod 8 = 2 \/ c mod 8 = 3 \/
                 c mod 8 = 4 \/ c mod 8 = 5 \/ c mod 8 = 6 \/ c mod 8 = 7)
      by lia.
    destruct Hr as [H0|[H0|[H0|[H0|[H0|[H0|[H0|H0]]]]]]];
      rewrite H0 in H |- *; simpl in H |- *; try lia;
      exfalso; apply H; reflexivity.
  - unfold w11.
    destruct ((c mod 4) =? 2) eqn:E2; [lia|].
    assert (Hodd : Z.even c = false).
    { rewrite (even_mod4 c).
      apply Z.eqb_neq in E2.
      assert (Hr : c mod 4 = 0 \/ c mod 4 = 1 \/ c mod 4 = 2 \/ c mod 4 = 3)
        by lia.
      destruct Hr as [H0|[H0|[H0|H0]]]; rewrite H0;
        solve [reflexivity | exfalso; apply H; exact H0
               | exfalso; apply E2; exact H0]. }
    rewrite Hodd; destruct (Nat.odd f); lia.
Qed.

Lemma v36_bounds : forall t f, (1 <= t)%nat -> 1 <= v36 t f <= 3.
Proof.
  intros t f H.
  destruct t as [|[|t]]; [lia | |].
  - change (v36 1 f) with (if Nat.even f then 3 else 1).
    destruct (Nat.even f); lia.
  - change (v36 (S (S t)) f) with (if Nat.even (S (S t)) then 2 else 1).
    destruct (Nat.even (S (S t))); lia.
Qed.

Lemma value_bounds_small :
  forall G,
    wf G -> (1 <= count3 G)%nat -> -2 <= cval G < 0 ->
    1 <= value G <= 3.
Proof.
  intros G HG H3 Hc.
  assert (Hex3 : existsb is_3chain_b G = true)
    by (apply count3_pos_iff; lia).
  destruct (existsb is_4loop_b G) eqn:E4.
  - destruct (only34 G) eqn:Eo.
    + rewrite (value_only34 G Eo); apply v36_bounds; exact H3.
    + rewrite (value_with_4loop G HG E4 Eo ltac:(lia)); lia.
  - rewrite (value_no4_with3 G HG E4 Hex3 ltac:(lia)).
    apply w35z_range.
Qed.

Lemma w310_bounds : forall c f, 1 <= w310 c f <= 3.
Proof.
  intros c f; unfold w310, w13, w14.
  destruct (2 <=? c + 4 * Z.of_nat f).
  - destruct ((c mod 8 =? 1) || (c mod 8 =? 7))%bool; lia.
  - destruct (Nat.odd f); lia.
Qed.

Lemma value_no3_bounds :
  forall G,
    wf G -> G <> [] ->
    existsb is_3chain_b G = false ->
    cval G < 2 -> (cval G) mod 4 <> 0 ->
    1 <= value G <= 3.
Proof.
  intros G Hw Hn H3 Hc Hm.
  rewrite (value_no3 G Hw Hn H3 Hc); apply w38_mod4_ne0; exact Hm.
Qed.

Lemma value_theta1_odd_bounds :
  forall G,
    wf G -> count3 G = 1%nat ->
    (Z.of_nat (size G)) mod 4 = 3 ->
    cval G < 2 ->
    1 <= value G <= 3.
Proof.
  intros G Hw H1 Hs Hc.
  rewrite (value_theta1_odd G Hw H1 Hs Hc); apply w310_bounds.
Qed.

(** A position holding a three-chain is nonempty. *)
Lemma count3_pos_nonnil : forall G, (1 <= count3 G)%nat -> G <> [].
Proof.
  intros [|C G] H Hc; [unfold count3 in H; simpl in H; lia | discriminate].
Qed.

Lemma count3_pos_In : forall G, (1 <= count3 G)%nat -> In (Chain 3) G.
Proof.
  induction G as [|C G IH]; intros H; [unfold count3 in H; simpl in H; lia|].
  unfold count3 in H; simpl in H.
  destruct (is_3chain_b C) eqn:E.
  - left; apply is_3chain_eq; exact E.
  - right; apply IH; unfold count3; simpl in H |- *; lia.
Qed.


(** Removing a three-chain raises the controlled value by one or by three:
    the weight of the chain, plus the two the terminal bonus can gain when the
    last three-chain leaves a heap of loops. *)
Lemma cval_remove_3chain :
  forall rest,
    cval (Chain 3 :: rest) = cval rest + weight (Chain 3)
                             + (tb (Chain 3 :: rest) - tb rest).
Proof.
  intros rest; unfold cval; rewrite cbase_cons; lia.
Qed.

Lemma tb_remove_3chain_le :
  forall rest,
    rest <> [] ->
    tb rest - tb (Chain 3 :: rest) <= 2.
Proof.
  intros rest Hn.
  pose proof (tb_values rest Hn) as Hr.
  pose proof (tb_pos (Chain 3 :: rest) ltac:(discriminate)) as Hp.
  destruct Hr as [H4 | [H6 | H8]]; [lia | lia |].
  assert (Hall : forallb is_loop_b rest = true)
    by (apply tb_eight_all_loops; assumption).
  rewrite (tb_six_of_loops_and_three rest Hall Hn); lia.
Qed.

(** So the controlled value of the remainder is bounded above by three more
    than that of the position. *)
Lemma cval_rest_le3 :
  forall rest,
    rest <> [] ->
    cval rest <= cval (Chain 3 :: rest) + 3.
Proof.
  intros rest Hn.
  pose proof (cval_remove_3chain rest) as He.
  pose proof (tb_remove_3chain_le rest Hn) as Hle.
  rewrite weight_chain in He; lia.
Qed.

Lemma cval_rest_ge1 :
  forall rest,
    tb (Chain 3 :: rest) = tb rest ->
    cval rest = cval (Chain 3 :: rest) + 1.
Proof.
  intros rest Ht.
  pose proof (cval_remove_3chain rest) as He.
  rewrite weight_chain, Ht in He; lia.
Qed.

Lemma size_perm : forall G H, Permutation G H -> size G = size H.
Proof.
  intros G H HP; induction HP; unfold size in *; simpl; lia.
Qed.

Lemma count3_zero_iff :
  forall G, count3 G = 0%nat <-> existsb is_3chain_b G = false.
Proof.
  induction G as [|C G IH]; simpl; [split; reflexivity|].
  rewrite count3_cons.
  destruct (is_3chain_b C); simpl.
  - split; [discriminate | discriminate].
  - exact IH.
Qed.

(** Move a three-chain to the front. *)
Lemma norm_3chain :
  forall G, (1 <= count3 G)%nat -> exists rest, Permutation G (Chain 3 :: rest).
Proof.
  intros G H.
  destruct (In_selections G (Chain 3) (count3_pos_In G H)) as [rest Hs].
  exists rest; apply Permutation_sym, (selections_perm G (Chain 3, rest) Hs).
Qed.

Lemma value_cons3_le :
  forall rest, value (Chain 3 :: rest) <= 1 + Z.abs (value rest - 2).
Proof.
  intros rest.
  eapply Z.le_trans;
    [apply (value_le_open (Chain 3 :: rest) (Chain 3, rest));
     simpl; left; reflexivity |].
  unfold value_open; cbn [fst snd]; rewrite vopen_chain3; lia.
Qed.

(** With a three-chain present and a controlled value below two, no endgame
    is worth more than three. *)
Lemma value_le3_with3_aux :
  forall n G,
    (length G <= n)%nat ->
    wf G -> (1 <= count3 G)%nat -> cval G < 2 -> value G <= 3.
Proof.
  induction n as [|n IH]; intros G Hn Hw H3 Hc.
  - exfalso.
    assert (HG : G = []) by (destruct G; simpl in Hn; [reflexivity | lia]).
    subst G; unfold count3 in H3; simpl in H3; lia.
  - destruct (norm_3chain G H3) as [rest Hperm].
    assert (Hlen : length G = S (length rest))
      by (rewrite (Permutation_length Hperm); reflexivity).
    assert (Hw' : wf (Chain 3 :: rest)) by (apply (wf_perm G); assumption).
    assert (Hcv : cval (Chain 3 :: rest) = cval G)
      by (symmetry; apply cval_perm; exact Hperm).
    rewrite (value_perm G (Chain 3 :: rest) Hperm).
    assert (Hwr : wf rest) by (inversion Hw'; assumption).
    assert (HrNil : rest <> []).
    { intros Hnil; rewrite Hnil in Hcv.
      rewrite cval_single in Hcv; simpl csize in Hcv; lia. }
    assert (Hvr : value rest <= 4).
    { destruct (Z_lt_le_dec (cval rest) 2) as [Hlt | Hge].
      - destruct (Nat.eq_dec (count3 rest) 0) as [H0 | Hpos].
        + rewrite (value_no3 rest Hwr HrNil (proj1 (count3_zero_iff rest) H0) Hlt).
          pose proof (w38_range (cval rest) (count4 rest)); lia.
        + assert (value rest <= 3) by (apply IH; [lia | exact Hwr | lia | exact Hlt]).
          lia.
      - rewrite (value_cval_ge2 rest Hwr Hge).
        pose proof (cval_rest_le3 rest HrNil); lia. }
    pose proof (value_nonneg rest Hwr).
    pose proof (value_cons3_le rest); lia.
Qed.

Theorem value_le3_with3 :
  forall G, wf G -> (1 <= count3 G)%nat -> cval G < 2 -> value G <= 3.
Proof. intros G; apply (value_le3_with3_aux (length G)); lia. Qed.

(** An option worth nothing can only be a four-loop leaving four behind. *)
Lemma value_open_zero_shape :
  forall C rest,
    wf_comp C -> wf rest ->
    vopen C (value rest) = 0 ->
    C = Loop 4 /\ value rest = 4.
Proof.
  intros C rest HwC Hwr H.
  pose proof (value_nonneg rest Hwr) as Hpos.
  rewrite vopen_max in H.
  assert (H1 : Z.of_nat (csize C) - value rest <= 0) by lia.
  assert (H2 : Z.of_nat (csize C) - 2 * Z.of_nat (hand C) + value rest <= 0)
    by lia.
  destruct C as [m | m]; simpl csize in *; simpl hand in *.
  - simpl in HwC; lia.
  - destruct HwC as [H4 Hev].
    assert (Hm : m = 4%nat) by lia.
    subst m; split; [reflexivity | lia].
Qed.

(** Adding a three-chain to a position that already holds one leaves the
    terminal bonus alone. *)
Lemma tb_3chain_stable :
  forall rest,
    rest <> [] -> (1 <= count3 rest)%nat ->
    tb (Chain 3 :: rest) = tb rest.
Proof.
  intros rest Hn H3.
  destruct (Z.lt_trichotomy (tb rest) (tb (Chain 3 :: rest)))
    as [Hlt | [He | Hgt]].
  - destruct (tb_increase_shape (Chain 3) rest Hn Hlt) as [Hl _]; discriminate.
  - symmetry; exact He.
  - exfalso.
    destruct (tb_decrease_shape (Chain 3) rest Hn
                ltac:(simpl; lia) ltac:(unfold big; simpl; lia) Hgt)
      as [_ Hall].
    pose proof (count3_pos_In rest H3) as Hin.
    rewrite forallb_forall in Hall; specialize (Hall (Chain 3) Hin).
    discriminate.
Qed.

(** With a three-chain present and a controlled value of minus two or less,
    the endgame is worth at least one. *)
Lemma value_pos_of_3chain :
  forall G, wf G -> (1 <= count3 G)%nat -> cval G <= -2 -> 1 <= value G.
Proof.
  intros G Hw H3 Hc.
  pose proof (value_nonneg G Hw) as Hpos.
  destruct (Z.eq_dec (value G) 0) as [H0 | Hne]; [|lia].
  exfalso.
  assert (HNil : G <> []) by (apply count3_pos_nonnil; exact H3).
  destruct (value_attained G HNil) as [p [Hp Hval]].
  rewrite H0 in Hval.
  pose proof (selections_wf G p Hw Hp) as [HwC Hwr].
  unfold value_open in Hval.
  destruct (value_open_zero_shape (fst p) (snd p) HwC Hwr (eq_sym Hval))
    as [HC Hv4].
  pose proof (selections_perm G p Hp) as Hperm.
  assert (Hc3 : count3 (snd p) = count3 G).
  { rewrite <- (count3_perm _ _ Hperm), count3_cons, HC; reflexivity. }
  assert (HrNil : snd p <> []).
  { intros Hnil; rewrite Hnil, value_nil in Hv4; lia. }
  assert (Htble : tb (snd p) <= tb (fst p :: snd p)).
  { destruct (Z.lt_trichotomy (tb (fst p :: snd p)) (tb (snd p)))
      as [Hlt | [He | Hgt]]; [|lia|lia].
    exfalso.
    destruct (tb_decrease_shape (fst p) (snd p) HrNil HwC
                ltac:(rewrite HC; unfold big; simpl; lia) Hlt) as [Hch _].
    rewrite HC in Hch; discriminate. }
  assert (Hwt : weight (fst p) = -4)
    by (rewrite HC, weight_loop_len; lia).
  pose proof (selections_cval G p Hp) as Hcv.
  assert (Hcr : cval (snd p) <= 2)
    by (unfold cval in Hcv, Hc |- *; lia).
  destruct (Z_lt_le_dec (cval (snd p)) 2) as [Hlt | Hge].
  - assert (value (snd p) <= 3)
      by (apply value_le3_with3; [exact Hwr | lia | exact Hlt]).
    lia.
  - rewrite (value_cval_ge2 (snd p) Hwr Hge) in Hv4; lia.
Qed.

Lemma mod4_three : forall m, (3 + m * 4) mod 4 = 3.
Proof. intros m; rewrite Z.mod_add by lia; reflexivity. Qed.

Lemma size_app : forall A B, size (A ++ B) = (size A + size B)%nat.
Proof.
  induction A as [|C A IH]; intros B; [reflexivity|].
  simpl app; rewrite !size_cons, IH; lia.
Qed.

Lemma size_repeat : forall C k, size (repeat C k) = (k * csize C)%nat.
Proof.
  intros C; induction k as [|k IH]; [reflexivity|].
  simpl repeat; rewrite size_cons, IH; lia.
Qed.

Lemma size_mix : forall t f, size (mix t f) = (3 * t + 4 * f)%nat.
Proof.
  intros t f; unfold mix; rewrite size_app, !size_repeat; simpl csize; lia.
Qed.

(** * Two or more three-chains, or one on an even board *)

Lemma value_theta_general_aux :
  forall n G,
    (length G <= n)%nat ->
    wf G -> cval G <= -2 ->
    ((2 <= count3 G)%nat \/
     (count3 G = 1%nat /\ (Z.of_nat (size G)) mod 4 <> 3)) ->
    1 <= value G <= 2.
Proof.
  induction n as [|n IH]; intros G Hn Hw Hc Hdisj.
  - exfalso.
    assert (HG : G = []) by (destruct G; simpl in Hn; [reflexivity | lia]).
    subst G; unfold cval in Hc; rewrite tb_nil, cbase_nil in Hc; lia.
  - assert (H3 : (1 <= count3 G)%nat) by (destruct Hdisj as [H | [H _]]; lia).
    assert (Hex3 : existsb is_3chain_b G = true).
    { destruct (existsb is_3chain_b G) eqn:E; [reflexivity|].
      apply count3_zero_iff in E; lia. }
    destruct (existsb is_4loop_b G) eqn:E4.
    + destruct (only34 G) eqn:E34.
      * rewrite (value_only34 G E34).
        assert (Ht2 : (2 <= count3 G)%nat).
        { destruct Hdisj as [H | [H1 Hs]]; [exact H|].
          exfalso; apply Hs.
          assert (Hsz : Z.of_nat (size G) = 3 + Z.of_nat (count4 G) * 4).
          { rewrite (size_perm G _ (perm_mix_of_only34 G E34)), size_mix, H1.
            rewrite Nat2Z.inj_add, !Nat2Z.inj_mul; lia. }
          rewrite Hsz; apply mod4_three. }
        unfold v36.
        destruct (count3 G) as [|[|t]]; [lia | lia |].
        destruct (Nat.even (S (S t))); lia.
      * destruct (Z.eq_dec (cval G) (-2)) as [Hm2 | Hne2].
        -- rewrite (value_with_4loop G Hw E4 E34 ltac:(lia)), Hm2; simpl; lia.
        -- destruct (norm_3chain G H3) as [rest Hperm].
           assert (Hlen : length G = S (length rest))
             by (rewrite (Permutation_length Hperm); reflexivity).
           assert (Hw' : wf (Chain 3 :: rest)) by (apply (wf_perm G); assumption).
           assert (Hwr : wf rest) by (inversion Hw'; assumption).
           assert (Hcv : cval (Chain 3 :: rest) = cval G)
             by (symmetry; apply cval_perm; exact Hperm).
           assert (Hsz : size G = size (Chain 3 :: rest))
             by (apply size_perm; exact Hperm).
           assert (Hct : count3 G = S (count3 rest))
             by (rewrite (count3_perm G _ Hperm), count3_cons; reflexivity).
           assert (HrNil : rest <> []).
           { intros Hnil; rewrite Hnil in Hcv.
             rewrite cval_single in Hcv; simpl csize in Hcv; lia. }
           assert (Hszr : Z.of_nat (size G) = 3 + Z.of_nat (size rest)).
           { rewrite Hsz, size_cons; simpl csize; lia. }
           split.
           ++ apply value_pos_of_3chain; assumption.
           ++ rewrite (value_perm G (Chain 3 :: rest) Hperm).
              assert (Hvr : 1 <= value rest <= 3).
              { destruct (Nat.eq_dec (count3 rest) 0) as [H0 | Hpos].
                - assert (Hno3 : existsb is_3chain_b rest = false)
                    by (apply count3_zero_iff; exact H0).
                  assert (Hd2 : (Z.of_nat (size G)) mod 4 <> 3)
                    by (destruct Hdisj as [H | [_ H]]; [exfalso; lia | exact H]).
                  assert (Hcr : cval rest < 2)
                    by (pose proof (cval_rest_le3 rest HrNil); lia).
                  apply (value_no3_bounds rest Hwr HrNil Hno3 Hcr).
                  destruct (size_cval_mod4 rest Hno3) as [q Hq].
                  intros Hm0.
                  assert (Hdiv : (4 | cval rest))
                    by (apply (proj1 (Z.mod_divide (cval rest) 4 ltac:(lia)));
                        exact Hm0).
                  destruct Hdiv as [k Hk].
                  apply Hd2.
                  assert (Hs : Z.of_nat (size G) = 3 + (q + k) * 4) by lia.
                  rewrite Hs; apply mod4_three.
                - assert (Htb : tb (Chain 3 :: rest) = tb rest)
                    by (apply tb_3chain_stable; [exact HrNil | lia]).
                  assert (Hcr : cval rest = cval G + 1)
                    by (pose proof (cval_rest_ge1 rest Htb); lia).
                  destruct (Nat.eq_dec (count3 rest) 1) as [H1 | Hne1].
                  + destruct (Z.eq_dec ((Z.of_nat (size rest)) mod 4) 3)
                      as [Hs3 | Hsne].
                    * apply (value_theta1_odd_bounds rest Hwr H1 Hs3); lia.
                    * assert (Hb : 1 <= value rest <= 2)
                        by (apply (IH rest);
                            [lia | exact Hwr | lia
                             | right; split; assumption]).
                      lia.
                  + assert (Hb : 1 <= value rest <= 2)
                      by (apply (IH rest);
                          [lia | exact Hwr | lia | left; lia]).
                    lia. }
              pose proof (value_cons3_le rest); lia.
    + rewrite (value_no4_with3 G Hw E4 Hex3 ltac:(lia)).
      unfold w35z.
      destruct (Z.even (Z.of_nat (size G))); [lia|].
      destruct ((count3 G =? 1)%nat &&
                (Z.of_nat (size G) mod 4 =? 3))%bool eqn:Eb; [|lia].
      exfalso.
      apply andb_true_iff in Eb; destruct Eb as [Ea Eb].
      apply Nat.eqb_eq in Ea; apply Z.eqb_eq in Eb.
      destruct Hdisj as [H | [_ Hs]]; lia.
Qed.

(** Allcock's Lemma 3.11: with two or more three-chains, or exactly one on a
    board whose size is not three modulo four, the value is one or two
    according to the parity of the board. *)
Theorem value_theta_general :
  forall G,
    wf G -> cval G <= -2 ->
    ((2 <= count3 G)%nat \/
     (count3 G = 1%nat /\ (Z.of_nat (size G)) mod 4 <> 3)) ->
    value G = (if Z.even (Z.of_nat (size G)) then 2 else 1).
Proof.
  intros G Hw Hc Hdisj.
  pose proof (value_theta_general_aux (length G) G ltac:(lia) Hw Hc Hdisj)
    as Hb.
  pose proof (value_parity G) as Hp.
  destruct (Z.even (Z.of_nat (size G))) eqn:Es.
  - destruct (Z.even (value G)) eqn:Ev; [|discriminate].
    apply Z.even_spec in Ev; destruct Ev as [k Hk]; lia.
  - destruct (Z.even (value G)) eqn:Ev; [discriminate|].
    assert (Ov : Z.odd (value G) = true)
      by (rewrite <- Z.negb_even, Ev; reflexivity).
    apply Z.odd_spec in Ov; destruct Ov as [k Hk]; lia.
Qed.

(** * The complete value *)

Lemma Zeven_of_nat : forall n, Z.even (Z.of_nat n) = Nat.even n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  rewrite Nat2Z.inj_succ, Z.even_succ, <- Z.negb_even, IH.
  rewrite Nat.even_succ, <- Nat.negb_even; reflexivity.
Qed.

Lemma even_3t4f : forall t f, Nat.even (3 * t + 4 * f) = Nat.even t.
Proof.
  intros t f; destruct (Nat.even t) eqn:Et.
  - apply Nat.even_spec in Et; destruct Et as [k Hk].
    apply Nat.even_spec; exists (3 * k + 2 * f)%nat; lia.
  - assert (Ot : Nat.odd t = true)
      by (rewrite <- Nat.negb_even, Et; reflexivity).
    apply Nat.odd_spec in Ot; destruct Ot as [k Hk].
    assert (Ho : Nat.odd (3 * t + 4 * f) = true)
      by (apply Nat.odd_spec; exists (3 * k + 1 + 2 * f)%nat; lia).
    rewrite <- Nat.negb_even in Ho.
    destruct (Nat.even (3 * t + 4 * f)); [discriminate | reflexivity].
Qed.

Lemma count3_pos_existsb :
  forall G, (1 <= count3 G)%nat -> existsb is_3chain_b G = true.
Proof.
  intros G H; destruct (existsb is_3chain_b G) eqn:E; [reflexivity|].
  apply count3_zero_iff in E; lia.
Qed.

(** The value of every endgame of loops and long chains, by the first case
    that applies: the controlled value when it reaches two; its absolute value
    at a four-loop position that is not made of three-chains and four-loops
    alone; the tables of Lemmas 3.8 and 3.10 when the three-chains are absent
    or a single one sits on an odd board; and otherwise one or two by the
    parity of the board. *)
Definition v41 (G : position) : Z :=
  if 2 <=? cval G then cval G
  else if (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool
       then Z.abs (cval G)
  else if (count3 G =? 0)%nat then w38 (cval G) (count4 G)
  else if ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool
       then w310 (cval G) (count4 G)
  else if Z.even (Z.of_nat (size G)) then 2 else 1.

Theorem value_complete :
  forall G, wf G -> G <> [] -> value G = v41 G.
Proof.
  intros G Hw HNil; unfold v41.
  destruct (2 <=? cval G) eqn:E1.
  { apply Z.leb_le in E1; apply value_cval_ge2; assumption. }
  apply Z.leb_gt in E1.
  destruct (existsb is_4loop_b G && negb (only34 G) &&
            (-2 <=? cval G))%bool eqn:E2.
  { apply andb_true_iff in E2; destruct E2 as [E2a E2c].
    apply andb_true_iff in E2a; destruct E2a as [E4 E34].
    apply negb_true_iff in E34; apply Z.leb_le in E2c.
    apply value_with_4loop; assumption. }
  destruct (count3 G =? 0)%nat eqn:E3.
  { apply Nat.eqb_eq in E3.
    apply value_no3; try assumption.
    apply count3_zero_iff; exact E3. }
  apply Nat.eqb_neq in E3.
  assert (H3 : (1 <= count3 G)%nat) by lia.
  destruct ((count3 G =? 1)%nat &&
            (Z.of_nat (size G) mod 4 =? 3))%bool eqn:E5.
  { apply andb_true_iff in E5; destruct E5 as [E5a E5b].
    apply Nat.eqb_eq in E5a; apply Z.eqb_eq in E5b.
    apply value_theta1_odd; assumption. }
  assert (Hdisj : (2 <= count3 G)%nat \/
                  (count3 G = 1%nat /\ (Z.of_nat (size G)) mod 4 <> 3)).
  { apply andb_false_iff in E5; destruct E5 as [E5 | E5].
    - apply Nat.eqb_neq in E5; left; lia.
    - apply Z.eqb_neq in E5.
      destruct (Nat.eq_dec (count3 G) 1) as [H1 | Hne];
        [right; split; assumption | left; lia]. }
  destruct (existsb is_4loop_b G) eqn:E4.
  - destruct (only34 G) eqn:E34.
    + rewrite (value_only34 G E34).
      assert (Hsize : size G = (3 * count3 G + 4 * count4 G)%nat)
        by (rewrite (size_perm G _ (perm_mix_of_only34 G E34)); apply size_mix).
      assert (Ht2 : (2 <= count3 G)%nat).
      { destruct Hdisj as [H | [H1 Hs]]; [exact H|].
        exfalso; apply Hs.
        assert (Hz : Z.of_nat (size G) = 3 + Z.of_nat (count4 G) * 4).
        { rewrite Hsize, H1, Nat2Z.inj_add, !Nat2Z.inj_mul; lia. }
        rewrite Hz; apply mod4_three. }
      rewrite Zeven_of_nat, Hsize, even_3t4f.
      unfold v36.
      destruct (count3 G) as [|[|t]]; [lia | lia | reflexivity].
    + assert (Hc2 : cval G <= -3).
      { apply andb_false_iff in E2; destruct E2 as [E2 | E2].
        - exfalso; apply andb_false_iff in E2; destruct E2 as [E2 | E2];
            first [discriminate | congruence].
        - apply Z.leb_gt in E2; lia. }
      apply value_theta_general; [assumption | lia | assumption].
  - rewrite (value_no4_with3 G Hw E4 (count3_pos_existsb G H3) E1).
    unfold w35z.
    destruct (Z.even (Z.of_nat (size G))); [reflexivity|].
    rewrite E5; reflexivity.
Qed.

Lemma v41_le4 : forall G, cval G <= 4 -> v41 G <= 4.
Proof.
  intros G Hc; unfold v41.
  destruct (2 <=? cval G) eqn:E1; [apply Z.leb_le in E1; lia|].
  apply Z.leb_gt in E1.
  destruct (existsb is_4loop_b G && negb (only34 G) &&
            (-2 <=? cval G))%bool eqn:E2.
  { apply andb_true_iff in E2; destruct E2 as [_ E2c].
    apply Z.leb_le in E2c; lia. }
  destruct (count3 G =? 0)%nat.
  { pose proof (w38_range (cval G) (count4 G)); lia. }
  destruct ((count3 G =? 1)%nat &&
            (Z.of_nat (size G) mod 4 =? 3))%bool.
  { pose proof (w310_bounds (cval G) (count4 G)); lia. }
  destruct (Z.even (Z.of_nat (size G))); lia.
Qed.

Theorem value_le4_of_cval_le4 :
  forall G, wf G -> cval G <= 4 -> value G <= 4.
Proof.
  intros G Hw Hc.
  destruct (list_eq_dec comp_eq_dec G []) as [-> | HNil];
    [rewrite value_nil; lia|].
  rewrite (value_complete G Hw HNil); apply v41_le4; exact Hc.
Qed.

(** Allcock's Theorem 1.4: an endgame is worth more than four exactly when its
    controlled value is. *)
Theorem value_gt4_iff :
  forall G, wf G -> (4 < value G <-> 4 < cval G).
Proof.
  intros G Hw; split.
  - intros H.
    destruct (Z_lt_le_dec 4 (cval G)) as [Hlt | Hge]; [exact Hlt|].
    exfalso; pose proof (value_le4_of_cval_le4 G Hw Hge); lia.
  - apply value_gt4_of_cval_gt4; exact Hw.
Qed.

(** The controller's test from Theorem 1.3, read off the controlled value for
    a loop. *)
Corollary keep_control_loop_iff :
  forall G, wf G -> (4 < value G <-> 4 < cval G).
Proof. exact value_gt4_iff. Qed.

(** * Optimal openings *)

(** A component is an optimal opening exactly when no other is worth less. *)
Theorem opener_optimal_iff :
  forall G p,
    G <> [] -> In p (selections G) ->
    (value G = value_open p <->
     forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p HNil Hp; split.
  - intros Hval q Hq.
    rewrite <- Hval; apply value_le_open; exact Hq.
  - intros Hmin.
    destruct (value_attained G HNil) as [r [Hr Hval]].
    apply Z.le_antisymm.
    + apply value_le_open; exact Hp.
    + rewrite Hval; apply Hmin; exact Hr.
Qed.

(** Every endgame has an optimal opening. *)
Corollary opener_exists :
  forall G,
    G <> [] ->
    exists p, In p (selections G) /\
              forall q, In q (selections G) -> value_open p <= value_open q.
Proof.
  intros G HNil.
  destruct (value_attained G HNil) as [p [Hp Hval]].
  exists p; split; [exact Hp|].
  apply (proj1 (opener_optimal_iff G p HNil Hp)); exact Hval.
Qed.

(** The value of an endgame is a function of its controlled value, its counts
    of three-chains and four-loops, its size, and whether it consists of those
    two kinds alone. *)
Corollary value_determined :
  forall G H,
    wf G -> wf H -> G <> [] -> H <> [] ->
    cval G = cval H ->
    count3 G = count3 H ->
    count4 G = count4 H ->
    size G = size H ->
    only34 G = only34 H ->
    existsb is_4loop_b G = existsb is_4loop_b H ->
    value G = value H.
Proof.
  intros G H HwG HwH HnG HnH Hc H3 H4 Hs H34 He.
  rewrite (value_complete G HwG HnG), (value_complete H HwH HnH).
  unfold v41; rewrite Hc, H3, H4, Hs, H34, He; reflexivity.
Qed.

(** * Recognising a value above two *)

Lemma w10_gt2 :
  forall c,
    2 < w10 c <->
    ((c mod 8 =? 3) || (c mod 8 =? 4) || (c mod 8 =? 5))%bool = true.
Proof.
  intros c.
  assert (Hb : 0 <= c mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (H8 : c mod 8 = 0 \/ c mod 8 = 1 \/ c mod 8 = 2 \/ c mod 8 = 3 \/
               c mod 8 = 4 \/ c mod 8 = 5 \/ c mod 8 = 6 \/ c mod 8 = 7)
    by lia.
  unfold w10.
  destruct H8 as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; cbn;
    split; intros; first [lia | discriminate | reflexivity].
Qed.

Lemma w11_gt2 :
  forall c f,
    2 < w11 c f <-> (negb (c mod 4 =? 2) && Nat.even f)%bool = true.
Proof.
  intros c f; unfold w11.
  destruct (c mod 4 =? 2) eqn:E4; cbn.
  - split; intros; first [lia | discriminate].
  - rewrite <- Nat.negb_odd.
    destruct (Nat.odd f); cbn; destruct (Z.even c); cbn;
      split; intros; first [lia | discriminate | reflexivity].
Qed.

Lemma w13_gt2 :
  forall c,
    2 < w13 c <-> negb ((c mod 8 =? 1) || (c mod 8 =? 7))%bool = true.
Proof.
  intros c; unfold w13.
  destruct ((c mod 8 =? 1) || (c mod 8 =? 7))%bool; cbn;
    split; intros; first [lia | discriminate | reflexivity].
Qed.

Lemma w14_gt2 : forall f, 2 < w14 f <-> Nat.even f = true.
Proof.
  intros f; unfold w14.
  rewrite <- Nat.negb_odd.
  destruct (Nat.odd f); cbn;
    split; intros; first [lia | discriminate | reflexivity].
Qed.

Definition gt2_no3 (c : Z) (f : nat) : bool :=
  if 2 <=? c + 4 * Z.of_nat f
  then ((c mod 8 =? 3) || (c mod 8 =? 4) || (c mod 8 =? 5))%bool
  else (negb (c mod 4 =? 2) && Nat.even f)%bool.

Definition gt2_theta1 (c : Z) (f : nat) : bool :=
  if 2 <=? c + 4 * Z.of_nat f
  then negb ((c mod 8 =? 1) || (c mod 8 =? 7))%bool
  else Nat.even f.

(** The closed-form test for an endgame worth more than two, which is what the
    controller consults before keeping control at a chain. *)
Definition gt2b (G : position) : bool :=
  if 2 <=? cval G then 2 <? cval G
  else if (existsb is_4loop_b G && negb (only34 G) && (-2 <=? cval G))%bool
       then false
  else if (count3 G =? 0)%nat then gt2_no3 (cval G) (count4 G)
  else if ((count3 G =? 1)%nat && (Z.of_nat (size G) mod 4 =? 3))%bool
       then gt2_theta1 (cval G) (count4 G)
  else false.

Lemma w38_gt2 :
  forall c f, 2 < w38 c f <-> gt2_no3 c f = true.
Proof.
  intros c f; unfold w38, gt2_no3.
  destruct (2 <=? c + 4 * Z.of_nat f); [apply w10_gt2 | apply w11_gt2].
Qed.

Lemma w310_gt2 :
  forall c f, 2 < w310 c f <-> gt2_theta1 c f = true.
Proof.
  intros c f; unfold w310, gt2_theta1.
  destruct (2 <=? c + 4 * Z.of_nat f); [apply w13_gt2 | apply w14_gt2].
Qed.

(** Allcock's Theorem 1.5. *)
Theorem value_gt2_iff :
  forall G, wf G -> G <> [] -> (2 < value G <-> gt2b G = true).
Proof.
  intros G Hw HNil.
  rewrite (value_complete G Hw HNil); unfold v41, gt2b.
  destruct (2 <=? cval G) eqn:E1.
  { split; [apply Z.ltb_lt | apply Z.ltb_lt]. }
  apply Z.leb_gt in E1.
  destruct (existsb is_4loop_b G && negb (only34 G) &&
            (-2 <=? cval G))%bool eqn:E2.
  { apply andb_true_iff in E2; destruct E2 as [_ E2c].
    apply Z.leb_le in E2c.
    split; intros H; [lia | discriminate]. }
  destruct (count3 G =? 0)%nat.
  { apply w38_gt2. }
  destruct ((count3 G =? 1)%nat &&
            (Z.of_nat (size G) mod 4 =? 3))%bool.
  { apply w310_gt2. }
  destruct (Z.even (Z.of_nat (size G)));
    split; intros H; first [lia | discriminate].
Qed.

(** So the controller's two tests are decided by closed formulas: she keeps
    control at a chain when the rest is worth more than two, and at a loop
    when it is worth more than four. *)
Corollary controller_tests :
  forall G,
    wf G -> G <> [] ->
    (2 < value G <-> gt2b G = true) /\
    (4 < value G <-> 4 < cval G).
Proof.
  intros G Hw HNil; split;
    [apply value_gt2_iff; assumption | apply value_gt4_iff; assumption].
Qed.

(** * A computable optimal opening *)

Fixpoint argmin_open (best : comp * position) (l : list (comp * position))
  : comp * position :=
  match l with
  | [] => best
  | q :: rest =>
      argmin_open (if value_open q <? value_open best then q else best) rest
  end.

Definition best_open (G : position) : option (comp * position) :=
  match selections G with
  | [] => None
  | p :: rest => Some (argmin_open p rest)
  end.

Lemma argmin_open_In :
  forall l b, In (argmin_open b l) (b :: l).
Proof.
  induction l as [|q l IH]; intros b; simpl; [left; reflexivity|].
  destruct (value_open q <? value_open b).
  - destruct (IH q) as [H | H]; [right; left; exact H | right; right; exact H].
  - destruct (IH b) as [H | H]; [left; exact H | right; right; exact H].
Qed.

Lemma argmin_open_le :
  forall l b q, In q (b :: l) -> value_open (argmin_open b l) <= value_open q.
Proof.
  induction l as [|r l IH]; intros b q Hq; simpl.
  - destruct Hq as [<- | []]; lia.
  - destruct (value_open r <? value_open b) eqn:E.
    + apply Z.ltb_lt in E.
      destruct Hq as [<- | [<- | Hq]].
      * eapply Z.le_trans; [apply (IH r r); left; reflexivity | lia].
      * apply (IH r); left; reflexivity.
      * apply (IH r); right; exact Hq.
    + apply Z.ltb_ge in E.
      destruct Hq as [<- | [<- | Hq]].
      * apply (IH b); left; reflexivity.
      * eapply Z.le_trans; [apply (IH b b); left; reflexivity | lia].
      * apply (IH b); right; exact Hq.
Qed.

Lemma best_open_none : forall G, best_open G = None <-> G = [].
Proof.
  intros G; unfold best_open.
  destruct (selections G) eqn:E.
  - split; [intros _; apply selections_nil_iff; exact E | reflexivity].
  - split; [discriminate|].
    intros ->; simpl in E; discriminate.
Qed.

(** The selected opening is legal, attains the value, and no opening does
    better. *)
Theorem best_open_correct :
  forall G p,
    best_open G = Some p ->
    In p (selections G) /\
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p H; unfold best_open in H.
  destruct (selections G) as [|b l] eqn:E; [discriminate|].
  injection H as <-.
  assert (HNil : G <> []).
  { intros Hg; rewrite Hg in E; simpl in E; discriminate. }
  assert (Hin : In (argmin_open b l) (selections G))
    by (rewrite E; apply argmin_open_In).
  assert (Hmin : forall q, In q (selections G) ->
                   value_open (argmin_open b l) <= value_open q).
  { intros q Hq; rewrite E in Hq; apply argmin_open_le; exact Hq. }
  destruct (value_attained G HNil) as [r [Hr Hval]].
  repeat split.
  - first [exact Hin | apply argmin_open_In].
  - apply Z.le_antisymm;
      [apply value_le_open; exact Hin | rewrite Hval; apply Hmin; exact Hr].
  - first [exact Hmin | intros q Hq; apply argmin_open_le; exact Hq].
Qed.

(** Every nonempty endgame has a computed optimal opening. *)
Corollary best_open_some :
  forall G, G <> [] -> exists p, best_open G = Some p.
Proof.
  intros G HNil; unfold best_open.
  destruct (selections G) eqn:E.
  - exfalso; apply HNil, selections_nil_iff; exact E.
  - eexists; reflexivity.
Qed.

(** ****************************************************************** *)
(** Short chains.

    [GameTrees.DotsAndBoxes] asks every chain to have at least three boxes,
    and the handout of two is then always available. A chain of one box has no
    such handout, and there [vopen] is simply wrong: with one box and a
    remainder worth three it reports zero, when the controller can only take
    the box and open, for minus two.

    [shand] caps the handout at the component itself and [svopen] is the
    recursion built on it. [svopen_wf] proves the two agree wherever the
    existing theory applies, so this is a conservative extension, and
    [svopen_chain1] and [svopen_chain2] give the short cases the earlier
    development cannot state. *)

Import ListNotations.

Open Scope Z_scope.

(** * The capped handout *)

(** The controller cannot leave more than the component holds. *)
Definition shand (C : comp) : nat := Nat.min (hand C) (csize C).

Definition svopen (C : comp) (w : Z) : Z :=
  Z.max (Z.of_nat (csize C) - w)
        (Z.of_nat (csize C) - 2 * Z.of_nat (shand C) + w).

Lemma shand_le_csize : forall C, (shand C <= csize C)%nat.
Proof. intros C; unfold shand; lia. Qed.

(** * Conservativity *)

Lemma shand_wf : forall C, wf_comp C -> shand C = hand C.
Proof.
  intros C H; unfold shand.
  pose proof (hand_le_csize C H); lia.
Qed.

(** Wherever the earlier development applies, the capped recursion is the
    same recursion. *)
Theorem svopen_wf :
  forall C w, wf_comp C -> svopen C w = vopen C w.
Proof.
  intros C w H; unfold svopen; rewrite (shand_wf C H), <- vopen_max; reflexivity.
Qed.

(** * The capped recursion is still sound *)

(** The opener never profits at a single component, however short. *)
Theorem svopen_nonneg : forall C w, 0 <= svopen C w.
Proof.
  intros C w; unfold svopen.
  pose proof (shand_le_csize C) as Hs.
  assert (Hz : (Z.of_nat (shand C) <= Z.of_nat (csize C)))
    by (apply Nat2Z.inj_le; exact Hs).
  destruct (Z.le_gt_cases w (Z.of_nat (csize C))) as [Hle | Hgt].
  - eapply Z.le_trans; [| apply Z.le_max_l]; lia.
  - eapply Z.le_trans; [| apply Z.le_max_r]; lia.
Qed.

(** The capped handout still shares the parity of the component and the
    remainder, so the counting arguments carry over. *)
Theorem svopen_parity :
  forall C w, Z.even (svopen C w) = Z.even (Z.of_nat (csize C) + w).
Proof.
  intros C w; unfold svopen.
  destruct (Z.le_gt_cases (Z.of_nat (csize C) - w)
                          (Z.of_nat (csize C) - 2 * Z.of_nat (shand C) + w))
    as [Hle | Hgt].
  - rewrite Z.max_r by lia.
    replace (Z.of_nat (csize C) - 2 * Z.of_nat (shand C) + w)
      with ((Z.of_nat (csize C) + w) - 2 * Z.of_nat (shand C)) by lia.
    rewrite Z.even_sub, (Z.even_mul 2 (Z.of_nat (shand C))); simpl Z.even at 2.
    destruct (Z.even (Z.of_nat (csize C) + w)); reflexivity.
  - rewrite Z.max_l by lia.
    rewrite Z.even_sub, Z.even_add.
    destruct (Z.even (Z.of_nat (csize C))), (Z.even w); reflexivity.
Qed.

(** * The short cases *)

(** A single box: take it and open, or leave it and keep control. *)
Theorem svopen_chain1 : forall w, svopen (Chain 1) w = Z.abs (w - 1).
Proof.
  intros w; unfold svopen, shand; simpl csize; simpl hand; simpl Nat.min.
  destruct (Z.le_gt_cases w 1) as [Hle | Hgt].
  - rewrite Z.abs_neq by lia; lia.
  - rewrite Z.abs_eq by lia; lia.
Qed.

(** Two boxes: the handout is the whole chain, so declining takes nothing. *)
Theorem svopen_chain2 : forall w, svopen (Chain 2) w = Z.abs (w - 2).
Proof.
  intros w; unfold svopen, shand; simpl csize; simpl hand; simpl Nat.min.
  destruct (Z.le_gt_cases w 2) as [Hle | Hgt].
  - rewrite Z.abs_neq by lia; lia.
  - rewrite Z.abs_eq by lia; lia.
Qed.

(** The uncapped recursion really does go wrong on a one-box chain: it
    reports zero where the controller can only lose two. *)
Example vopen_chain1_wrong : vopen (Chain 1) 3 = 0 /\ svopen (Chain 1) 3 = 2.
Proof. split; reflexivity. Qed.

(** * Positions with short chains *)

(** Chains of one or two boxes, and the loops the board can produce. *)
Definition swf_comp (C : comp) : Prop :=
  match C with
  | Chain n => (1 <= n)%nat
  | Loop n => (4 <= n)%nat /\ Nat.even n = true
  end.

Definition swf (G : position) : Prop := Forall swf_comp G.

Lemma wf_swf : forall G, wf G -> swf G.
Proof.
  intros G H; unfold swf; rewrite Forall_forall.
  unfold wf in H; rewrite Forall_forall in H.
  intros C HC; specialize (H C HC).
  destruct C as [k | k]; simpl in *; [lia | exact H].
Qed.

(** So every wellformed loony position is one the capped theory covers, and
    on those the two recursions agree component by component. *)
Theorem svopen_agrees_on_wf :
  forall G, wf G -> Forall (fun C => forall w, svopen C w = vopen C w) G.
Proof.
  intros G H; unfold wf in H; rewrite Forall_forall in H.
  rewrite Forall_forall; intros C HC w.
  apply svopen_wf, H, HC.
Qed.

(** * The value with short chains allowed *)

Fixpoint svf (fuel : nat) (G : position) : Z :=
  match fuel with
  | O => 0
  | S f =>
      match selections G with
      | [] => 0
      | p :: more =>
          minl (svopen (fst p) (svf f (snd p)))
               (map (fun q => svopen (fst q) (svf f (snd q))) more)
      end
  end.

Definition svalue (G : position) : Z := svf (length G) G.

Lemma svf_vf : forall fuel G, wf G -> svf fuel G = vf fuel G.
Proof.
  induction fuel as [|f IH]; intros G HG; [reflexivity|].
  simpl svf; simpl vf.
  destruct (selections G) as [|p more] eqn:E; [reflexivity|].
  assert (Hp : In p (selections G)) by (rewrite E; left; reflexivity).
  destruct (selections_wf G p HG Hp) as [Hcp Hrp].
  rewrite (IH (snd p) Hrp), (svopen_wf (fst p) (vf f (snd p)) Hcp).
  f_equal.
  apply map_ext_in; intros q Hq.
  assert (Hq' : In q (selections G)) by (rewrite E; right; exact Hq).
  destruct (selections_wf G q HG Hq') as [Hcq Hrq].
  rewrite (IH (snd q) Hrq), (svopen_wf (fst q) (vf f (snd q)) Hcq); reflexivity.
Qed.

(** The capped value is the value, wherever the value is defined. Every
    closed form of [GameTrees.DotsAndBoxes] therefore transfers, and what is
    new is only the positions the earlier theory had to exclude. *)
Theorem svalue_wf : forall G, wf G -> svalue G = value G.
Proof. intros G H; unfold svalue, value; apply svf_vf; exact H. Qed.

(** The opener never profits, short chains or not. *)
Theorem svalue_nonneg : forall G, 0 <= svalue G.
Proof.
  assert (Haux : forall n G, (length G <= n)%nat -> 0 <= svf n G).
  { induction n as [|n IH]; intros G Hn; [apply Z.le_refl|].
    simpl svf; destruct (selections G) as [|p more] eqn:E;
      [apply Z.le_refl|].
    apply minl_lower_bound; [apply svopen_nonneg|].
    intros y Hy; apply in_map_iff in Hy; destruct Hy as [q [<- _]].
    apply svopen_nonneg. }
  intros G; unfold svalue; apply Haux; lia.
Qed.

(** A lone short chain is taken whole. *)
Example svalue_chain1 : svalue [Chain 1] = 1.
Proof. reflexivity. Qed.

Example svalue_two_chain1 : svalue [Chain 1; Chain 1] = 0.
Proof. reflexivity. Qed.

(** ****************************************************************** *)
(** Values of positions holding short chains.

    [GameTrees.DotsAndBoxes] caps the handout at the component and proves the
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

(** ****************************************************************** *)
(** Scoring games, and the loony endgame as one of them.

    A scoring game is a rose tree carrying, at each node, the score a finished
    game pays to Left, the player whose turn it is, and that player's options.
    The mover is written into the node rather than alternating, because in a
    scoring game a player who scores keeps the move.

    [eg] builds the loony endgame of [GameTrees.DotsAndBoxes] as such a game,
    with the moves spelled out: the opener names a component, and the
    controller either takes it whole and becomes the opener, or leaves the
    handout and stays in control. Boxes are banked as they are taken, with the
    sign of the player taking them. [score_eg] proves the optimal score of
    that game is the [value] of the position, so [value] is the score of a
    game whose rules are written down rather than a recursion asserted to
    model one. *)

Import ListNotations.

Open Scope Z_scope.

(** * Scoring games *)

(** [SG s lft opts]: with [opts] empty the game is over and pays [s] to Left;
    otherwise the player named by [lft] chooses among [opts]. *)
Inductive sgame : Type :=
| SG : Z -> bool -> list sgame -> sgame.

Definition maxl (x : Z) (l : list Z) : Z := fold_left Z.max l x.

(** The optimal score to Left, Left maximising and Right minimising. *)
Fixpoint score (g : sgame) : Z :=
  match g with
  | SG s lft opts =>
      match map score opts with
      | [] => s
      | v :: vs => if lft then maxl v vs else minl v vs
      end
  end.

Lemma score_node :
  forall s lft opts,
    score (SG s lft opts) =
    match map score opts with
    | [] => s
    | v :: vs => if lft then maxl v vs else minl v vs
    end.
Proof. reflexivity. Qed.

Lemma score_two_left :
  forall s a b, score (SG s true [a; b]) = Z.max (score a) (score b).
Proof. reflexivity. Qed.

Lemma score_two_right :
  forall s a b, score (SG s false [a; b]) = Z.min (score a) (score b).
Proof. reflexivity. Qed.

(** * Banking a constant through a game *)

Lemma minl_add_shift :
  forall l a x,
    fold_left Z.min (map (Z.add a) l) (a + x) = a + fold_left Z.min l x.
Proof.
  induction l as [|y l IH]; intros a x; simpl; [reflexivity|].
  replace (Z.min (a + x) (a + y)) with (a + Z.min x y) by lia.
  apply IH.
Qed.

Lemma maxl_sub_shift :
  forall l a x,
    fold_left Z.max (map (fun z => a - z) l) (a - x) = a - fold_left Z.min l x.
Proof.
  induction l as [|y l IH]; intros a x; simpl; [reflexivity|].
  replace (Z.max (a - x) (a - y)) with (a - Z.min x y) by lia.
  apply IH.
Qed.

(** * The loony endgame as a scoring game *)

(** Boxes taken by the player who is not the opener, banked with that
    player's sign. Left is [true]. *)
Definition bank (p : bool) (acc x : Z) : Z := if p then acc - x else acc + x.

Lemma bank_true : forall acc x, bank true acc x = acc - x.
Proof. reflexivity. Qed.

Lemma bank_false : forall acc x, bank false acc x = acc + x.
Proof. reflexivity. Qed.

(** [eg fuel acc G p]: the endgame on [G], with [acc] already banked to Left
    and the opener named by [p]. *)
Fixpoint eg (fuel : nat) (acc : Z) (G : position) (p : bool) : sgame :=
  match fuel with
  | O => SG acc p []
  | S f =>
      match selections G with
      | [] => SG acc p []
      | _ :: _ =>
          SG acc p
            (map (fun pr =>
               SG acc (negb p)
                 [ eg f (bank p acc (Z.of_nat (csize (fst pr)))) (snd pr) (negb p) ;
                   eg f (bank p acc (Z.of_nat (csize (fst pr))
                                     - 2 * Z.of_nat (hand (fst pr)))) (snd pr) p ])
             (selections G))
      end
  end.

Lemma eg_cons :
  forall f acc G p,
    selections G <> [] ->
    eg (S f) acc G p =
    SG acc p
      (map (fun pr =>
         SG acc (negb p)
           [ eg f (bank p acc (Z.of_nat (csize (fst pr)))) (snd pr) (negb p) ;
             eg f (bank p acc (Z.of_nat (csize (fst pr))
                               - 2 * Z.of_nat (hand (fst pr)))) (snd pr) p ])
       (selections G)).
Proof.
  intros f acc G p H; simpl eg.
  destruct (selections G) as [|a l] eqn:E; [contradiction | reflexivity].
Qed.

(** * The endgame scores its value *)

Theorem score_eg :
  forall fuel acc G p,
    (length G <= fuel)%nat ->
    score (eg fuel acc G p) = if p then acc - value G else acc + value G.
Proof.
  induction fuel as [|f IH]; intros acc G p Hf.
  - assert (HG : G = []) by (destruct G; simpl in Hf; [reflexivity | lia]).
    subst G; rewrite value_nil; simpl score; destruct p; lia.
  - destruct (list_eq_dec comp_eq_dec G []) as [-> | HNil].
    { simpl eg; simpl score; rewrite value_nil; destruct p; lia. }
    assert (Hsel : selections G <> [])
      by (intros Hz; apply HNil, selections_nil_iff; exact Hz).
    rewrite (eg_cons f acc G p Hsel), score_node, map_map.
    (* every option is worth the handout algebra, banked *)
    assert (Hopt : forall pr, In pr (selections G) ->
      score (SG acc (negb p)
               [ eg f (bank p acc (Z.of_nat (csize (fst pr)))) (snd pr) (negb p) ;
                 eg f (bank p acc (Z.of_nat (csize (fst pr))
                                   - 2 * Z.of_nat (hand (fst pr)))) (snd pr) p ])
      = bank p acc (value_open pr)).
    { intros pr Hpr.
      assert (Hlen : (length (snd pr) <= f)%nat)
        by (pose proof (selections_length G pr Hpr); lia).
      assert (Ht : forall a, score (eg f a (snd pr) true) = a - value (snd pr))
        by (intros a; rewrite (IH a (snd pr) true) by exact Hlen; reflexivity).
      assert (Hfa : forall a, score (eg f a (snd pr) false) = a + value (snd pr))
        by (intros a; rewrite (IH a (snd pr) false) by exact Hlen; reflexivity).
      unfold value_open.
      destruct (Z.le_gt_cases (value (snd pr)) (Z.of_nat (hand (fst pr))))
        as [Hle | Hgt].
      - rewrite (controller_gives_up (fst pr) (value (snd pr)) Hle).
        unfold give_up_control.
        destruct p; cbn [negb bank].
        + rewrite score_two_right, Hfa, Ht; lia.
        + rewrite score_two_left, Ht, Hfa; lia.
      - rewrite (controller_keeps (fst pr) (value (snd pr)) ltac:(lia)).
        unfold keep_control.
        destruct p; cbn [negb bank].
        + rewrite score_two_right, Hfa, Ht; lia.
        + rewrite score_two_left, Ht, Hfa; lia. }
    rewrite (map_ext_in _ (fun pr => bank p acc (value_open pr))
               (selections G) Hopt).
    (* now read off the opener's choice *)
    pose proof (value_unfold G) as Hval.
    destruct (selections G) as [|s0 more] eqn:Esel; [contradiction|].
    simpl map.
    assert (Hshape : map (fun pr => bank p acc (value_open pr)) more =
                     map (fun z => bank p acc z) (map value_open more))
      by (rewrite map_map; reflexivity).
    rewrite Hshape.
    destruct p; unfold bank, maxl, minl in *; rewrite Hval.
    + rewrite maxl_sub_shift; reflexivity.
    + rewrite minl_add_shift; reflexivity.
Qed.

(** The endgame value, read off the game rather than the recursion: with
    Right to open, the score Left secures is exactly [value]. *)
Corollary score_eg_root :
  forall G, score (eg (length G) 0 G false) = value G.
Proof. intros G; rewrite score_eg by lia; lia. Qed.

(** And with Left to open it is its negation, since the roles are swapped. *)
Corollary score_eg_root_left :
  forall G, score (eg (length G) 0 G true) = - value G.
Proof. intros G; rewrite score_eg by lia; lia. Qed.

(** ****************************************************************** *)
(** The standard scoring game, and where the loony endgame sits relative to
    it.

    Ettinger, and Milley and Renault after him, write a scoring game with the
    two option lists separated and the turn carried by which of two mutually
    recursive values is being read: [Lsc] is the score Left secures with Left
    to move, [Rsc] with Right to move. Play alternates by construction, and a
    player with no option ends the game at its score.

    [GameTrees.DotsAndBoxes] instead writes the mover into the node. [embed] sends
    that form to this one and [score_embed] proves the two agree wherever the
    movers alternate, so the bespoke type is a conservative notation for the
    standard one on the alternating fragment.

    [eg_not_alternates] is why the bespoke type was convenient. The loony
    endgame does not alternate: a controller who takes a whole component
    scores and therefore opens the next one, moving twice in a row.

    It is still a standard scoring game. [pad] simulates the repeated move by
    giving the other player a single forced option, which leaves the value
    alone, and [score_pad] proves the two readings agree on every game with
    no alternation hypothesis. [value_is_standard_score] is the consequence:
    the Dots and Boxes endgame value is the score a game of Ettinger and
    Milley-Renault form pays Left with Right to move. *)

Open Scope Z_scope.

(** * The standard form *)

(** A score, Left's options, Right's options. *)
Inductive scgame : Type :=
| SCg : Z -> list scgame -> list scgame -> scgame.

Definition lopts (g : scgame) : list scgame := match g with SCg _ L _ => L end.
Definition ropts (g : scgame) : list scgame := match g with SCg _ _ R => R end.
Definition sc (g : scgame) : Z := match g with SCg s _ _ => s end.

(** Left maximises, Right minimises, and a player with no option ends the
    game. The two values are read off one recursion so the definition passes
    the guard checker without a mutual fixpoint. *)
Fixpoint scv (g : scgame) : Z * Z :=
  match g with
  | SCg s L R =>
      (match map (fun x => snd (scv x)) L with
       | [] => s
       | v :: vs => maxl v vs
       end,
       match map (fun x => fst (scv x)) R with
       | [] => s
       | v :: vs => minl v vs
       end)
  end.

Definition Lsc (g : scgame) : Z := fst (scv g).
Definition Rsc (g : scgame) : Z := snd (scv g).

Lemma Lsc_eq :
  forall s L R,
    Lsc (SCg s L R) =
    match map Rsc L with [] => s | v :: vs => maxl v vs end.
Proof. reflexivity. Qed.

Lemma Rsc_eq :
  forall s L R,
    Rsc (SCg s L R) =
    match map Lsc R with [] => s | v :: vs => minl v vs end.
Proof. reflexivity. Qed.

(** A game in which neither player can move is worth its score to both. *)
Lemma Lsc_leaf : forall s, Lsc (SCg s [] []) = s.
Proof. reflexivity. Qed.

Lemma Rsc_leaf : forall s, Rsc (SCg s [] []) = s.
Proof. reflexivity. Qed.

(** * The mover-tagged form *)

Definition mover (g : sgame) : bool := match g with SG _ lft _ => lft end.
Definition sopts (g : sgame) : list sgame := match g with SG _ _ o => o end.
Definition sval (g : sgame) : Z := match g with SG s _ _ => s end.

(** Induction supplying the hypothesis for every option. *)
Fixpoint sgame_forall_ind
    (P : sgame -> Prop)
    (pf : forall (s : Z) (lft : bool) (opts : list sgame),
            Forall P opts -> P (SG s lft opts))
    (g : sgame) {struct g} : P g :=
  match g with
  | SG s lft opts =>
      pf s lft opts
        (list_ind (Forall P) (Forall_nil P)
           (fun x xs IHxs => Forall_cons x (sgame_forall_ind P pf x) IHxs) opts)
  end.

(** The mover alternates down every line. *)
Inductive alternates : sgame -> Prop :=
| alternates_SG :
    forall s lft opts,
      Forall (fun x => mover x = negb lft) opts ->
      Forall alternates opts ->
      alternates (SG s lft opts).

Lemma alternates_movers :
  forall s lft opts,
    alternates (SG s lft opts) -> Forall (fun x => mover x = negb lft) opts.
Proof. intros s lft opts H; inversion H; assumption. Qed.

Lemma alternates_opts :
  forall s lft opts, alternates (SG s lft opts) -> Forall alternates opts.
Proof. intros s lft opts H; inversion H; assumption. Qed.

(** * The embedding *)

(** The player to move keeps the options; the other side has none. *)
Fixpoint embed (g : sgame) : scgame :=
  match g with
  | SG s lft opts =>
      if lft then SCg s (map embed opts) [] else SCg s [] (map embed opts)
  end.

Lemma embed_left :
  forall s opts, embed (SG s true opts) = SCg s (map embed opts) [].
Proof. reflexivity. Qed.

Lemma embed_right :
  forall s opts, embed (SG s false opts) = SCg s [] (map embed opts).
Proof. reflexivity. Qed.

(** On an alternating game the bespoke score is the standard one, read from
    the side whose turn it is. *)
Theorem score_embed :
  forall g,
    alternates g ->
    score g = if mover g then Lsc (embed g) else Rsc (embed g).
Proof.
  refine (sgame_forall_ind
            (fun g => alternates g ->
               score g = if mover g then Lsc (embed g) else Rsc (embed g)) _).
  intros s lft opts IH Halt.
  pose proof (alternates_movers s lft opts Halt) as Hmov.
  pose proof (alternates_opts s lft opts Halt) as Hsub.
  destruct lft; cbn [mover].
  - rewrite embed_left, Lsc_eq, map_map.
    rewrite score_node.
    assert (Hmap : map score opts = map (fun x => Rsc (embed x)) opts).
    { apply map_ext_in; intros x Hx.
      rewrite (proj1 (Forall_forall _ opts) IH x Hx)
        by (apply (proj1 (Forall_forall _ opts) Hsub x Hx)).
      rewrite (proj1 (Forall_forall _ opts) Hmov x Hx); reflexivity. }
    rewrite Hmap; reflexivity.
  - rewrite embed_right, Rsc_eq, map_map.
    rewrite score_node.
    assert (Hmap : map score opts = map (fun x => Lsc (embed x)) opts).
    { apply map_ext_in; intros x Hx.
      rewrite (proj1 (Forall_forall _ opts) IH x Hx)
        by (apply (proj1 (Forall_forall _ opts) Hsub x Hx)).
      rewrite (proj1 (Forall_forall _ opts) Hmov x Hx); reflexivity. }
    rewrite Hmap; reflexivity.
Qed.

(** * The loony endgame is not alternating *)

(** Every game [eg] builds names its own mover. *)
Lemma mover_eg : forall f acc G p, mover (eg f acc G p) = p.
Proof.
  intros [|f] acc G p; [reflexivity|].
  simpl eg; destruct (selections G); reflexivity.
Qed.

(** One unfolding, naming the controller's two replies. *)
Lemma sopts_eg :
  forall f acc G p,
    selections G <> [] ->
    sopts (eg (S f) acc G p) =
    map (fun pr =>
           SG acc (negb p)
             [ eg f (bank p acc (Z.of_nat (csize (fst pr)))) (snd pr) (negb p) ;
               eg f (bank p acc (Z.of_nat (csize (fst pr))
                                 - 2 * Z.of_nat (hand (fst pr)))) (snd pr) p ])
        (selections G).
Proof.
  intros f acc G p H; rewrite (eg_cons f acc G p H); reflexivity.
Qed.

(** The controller who takes a whole component scores, and so opens the next
    one: the same player moves twice, which an alternating game never does. *)
Theorem eg_not_alternates :
  forall f acc G p,
    selections G <> [] -> ~ alternates (eg (S f) acc G p).
Proof.
  intros f acc G p Hsel Halt.
  destruct (selections G) as [|pr more] eqn:Esel; [contradiction|].
  assert (Hne : selections G <> []) by (rewrite Esel; discriminate).
  set (child := SG acc (negb p)
                  [ eg f (bank p acc (Z.of_nat (csize (fst pr)))) (snd pr) (negb p) ;
                    eg f (bank p acc (Z.of_nat (csize (fst pr))
                                      - 2 * Z.of_nat (hand (fst pr)))) (snd pr) p ]).
  assert (Hin : In child (sopts (eg (S f) acc G p))).
  { rewrite (sopts_eg f acc G p Hne), Esel; left; reflexivity. }
  (* the endgame node is an [SG], so its options carry the alternation *)
  assert (Hshape : eg (S f) acc G p = SG acc p (sopts (eg (S f) acc G p))).
  { rewrite (eg_cons f acc G p Hne); reflexivity. }
  rewrite Hshape in Halt.
  pose proof (alternates_opts _ _ _ Halt) as Hsub.
  pose proof (proj1 (Forall_forall _ _) Hsub child Hin) as Hchild.
  (* inside the child, the take-it-all reply repeats the mover *)
  pose proof (alternates_movers _ _ _ Hchild) as Hmov.
  assert (Hgc : In (eg f (bank p acc (Z.of_nat (csize (fst pr)))) (snd pr) (negb p))
                   [ eg f (bank p acc (Z.of_nat (csize (fst pr)))) (snd pr) (negb p) ;
                     eg f (bank p acc (Z.of_nat (csize (fst pr))
                                       - 2 * Z.of_nat (hand (fst pr)))) (snd pr) p ])
    by (left; reflexivity).
  pose proof (proj1 (Forall_forall _ _) Hmov _ Hgc) as Hbad.
  cbv beta in Hbad.
  rewrite mover_eg in Hbad.
  destruct p; simpl in Hbad; discriminate.
Qed.

(** So the loony endgame is a scoring game that the alternating form cannot
    express, and [score_embed] does not apply to it. The extra move a scoring
    player earns is exactly the difference. *)
Corollary eg_outside_standard_form :
  forall f acc G p,
    selections G <> [] ->
    ~ (alternates (eg (S f) acc G p) /\
       score (eg (S f) acc G p)
       = if p then Lsc (embed (eg (S f) acc G p))
              else Rsc (embed (eg (S f) acc G p))).
Proof.
  intros f acc G p Hsel [Halt _].
  exact (eg_not_alternates f acc G p Hsel Halt).
Qed.

(** * A faithful embedding through forced moves *)

(** The alternating form cannot let a player move twice, but it can make the
    other player's move forced: a position where one side has exactly one
    option leaves that side no choice, so the value is unchanged. [pad]
    inserts such a move wherever the mover repeats, and so sends every
    mover-tagged game, alternating or not, into the standard form. *)
Fixpoint pad (g : sgame) : scgame :=
  match g with
  | SG s lft opts =>
      if lft
      then SCg s (map (fun o => if mover o then SCg s [] [pad o] else pad o)
                      opts) []
      else SCg s [] (map (fun o => if mover o then pad o else SCg s [pad o] [])
                         opts)
  end.

Lemma pad_left :
  forall s opts,
    pad (SG s true opts) =
    SCg s (map (fun o => if mover o then SCg s [] [pad o] else pad o) opts) [].
Proof. reflexivity. Qed.

Lemma pad_right :
  forall s opts,
    pad (SG s false opts) =
    SCg s [] (map (fun o => if mover o then pad o else SCg s [pad o] []) opts).
Proof. reflexivity. Qed.

Lemma Rsc_forced : forall s x, Rsc (SCg s [] [x]) = Lsc x.
Proof. reflexivity. Qed.

Lemma Lsc_forced : forall s x, Lsc (SCg s [x] []) = Rsc x.
Proof. reflexivity. Qed.

(** With the forced moves in place the two readings agree on every game, with
    no alternation hypothesis. *)
Theorem score_pad :
  forall g, score g = if mover g then Lsc (pad g) else Rsc (pad g).
Proof.
  refine (sgame_forall_ind
            (fun g => score g = if mover g then Lsc (pad g) else Rsc (pad g)) _).
  intros s lft opts IH; destruct lft; cbn [mover].
  - rewrite pad_left, Lsc_eq, map_map, score_node.
    assert (Hmap : map score opts
                 = map (fun o => Rsc (if mover o then SCg s [] [pad o] else pad o))
                       opts).
    { apply map_ext_in; intros o Ho.
      rewrite (proj1 (Forall_forall _ opts) IH o Ho).
      destruct (mover o); [rewrite Rsc_forced |]; reflexivity. }
    rewrite Hmap; reflexivity.
  - rewrite pad_right, Rsc_eq, map_map, score_node.
    assert (Hmap : map score opts
                 = map (fun o => Lsc (if mover o then pad o else SCg s [pad o] []))
                       opts).
    { apply map_ext_in; intros o Ho.
      rewrite (proj1 (Forall_forall _ opts) IH o Ho).
      destruct (mover o); [| rewrite Lsc_forced]; reflexivity. }
    rewrite Hmap; reflexivity.
Qed.

(** So the loony endgame is a standard scoring game after all: not an
    alternating one, but the image of one under [pad]. *)
Corollary score_eg_standard :
  forall f acc G p,
    score (eg f acc G p) =
    if p then Lsc (pad (eg f acc G p)) else Rsc (pad (eg f acc G p)).
Proof.
  intros f acc G p; rewrite (score_pad (eg f acc G p)), mover_eg; reflexivity.
Qed.

(** And the Dots and Boxes endgame value is the score a standard scoring game
    pays Left with Right to move. *)
Corollary value_is_standard_score :
  forall G, value G = Rsc (pad (eg (length G) 0 G false)).
Proof.
  intros G; rewrite <- (score_eg_root G), score_eg_standard; reflexivity.
Qed.

(** * An alternating example, for contrast *)

(** A one-move game in which Left chooses between two finished positions.
    Here the movers do alternate and the two readings agree. *)
Definition demo : sgame := SG 0 true [SG 3 false []; SG 5 false []].

Example demo_alternates : alternates demo.
Proof.
  apply alternates_SG.
  - repeat constructor.
  - repeat (constructor; [apply alternates_SG; repeat constructor |]).
    constructor.
Qed.

Example demo_score : score demo = 5.
Proof. vm_compute; reflexivity. Qed.

Example demo_std : Lsc (embed demo) = 5.
Proof. vm_compute; reflexivity. Qed.

Example demo_agree : score demo = Lsc (embed demo).
Proof. reflexivity. Qed.

(** ****************************************************************** *)
(** Allcock's opener strategy.

    The standard move opens a three-chain if one is present, otherwise a
    shortest loop if a loop is present, otherwise a shortest chain. Allcock's
    Theorem 1.1 says that opening the shortest loop is optimal in three named
    cases and that the standard move is optimal in every other, the three
    cases being

      (i)   c(G) >= 2 and G is a three-chain together with one or more loops;
      (ii)  c(G) in {0, 1, -1} and G holds a four-loop, and what is left after
            removing one four-loop is not exactly three three-chains;
      (iii) c(G) <= -2 and G holds a four-loop and a three-chain, and what is
            left after removing one of each has size divisible by four and no
            three-chains.

    [allcock_move] is that strategy. It is stated here and checked by
    computation through [allcock_okb], which compares the move it names
    against the value; the theorem itself is not proved. [example_1_2] is
    Allcock's own worked example, machine-checked. *)

Import ListNotations.

Open Scope Z_scope.

(** * Choosing a component *)

Fixpoint pick_min (best : comp * position) (l : list (comp * position))
  : comp * position :=
  match l with
  | [] => best
  | q :: r =>
      pick_min (if (csize (fst q) <? csize (fst best))%nat then q else best) r
  end.

Lemma pick_min_In :
  forall l b, In (pick_min b l) (b :: l).
Proof.
  induction l as [|q l IH]; intros b; simpl; [left; reflexivity|].
  destruct ((csize (fst q) <? csize (fst b))%nat).
  - destruct (IH q) as [H | H]; [right; left; exact H | right; right; exact H].
  - destruct (IH b) as [H | H]; [left; exact H | right; right; exact H].
Qed.

(** The shortest component passing a test, if there is one. *)
Definition shortest_of (f : comp -> bool) (G : position)
  : option (comp * position) :=
  match filter (fun p => f (fst p)) (selections G) with
  | [] => None
  | p :: r => Some (pick_min p r)
  end.

Lemma shortest_of_In :
  forall f G p, shortest_of f G = Some p -> In p (selections G).
Proof.
  intros f G p H; unfold shortest_of in H.
  destruct (filter (fun q => f (fst q)) (selections G)) as [|b l] eqn:E;
    [discriminate|].
  injection H as <-.
  assert (Hin : In (pick_min b l) (b :: l)) by apply pick_min_In.
  rewrite <- E in Hin.
  apply filter_In in Hin; tauto.
Qed.

Definition any_comp (_ : comp) : bool := true.

(** Open a three-chain if there is one, otherwise a shortest loop, otherwise
    a shortest chain. *)
Definition standard_move (G : position) : option (comp * position) :=
  match shortest_of is_3chain_b G with
  | Some p => Some p
  | None =>
      match shortest_of is_loop_b G with
      | Some p => Some p
      | None => shortest_of any_comp G
      end
  end.

Lemma standard_move_In :
  forall G p, standard_move G = Some p -> In p (selections G).
Proof.
  intros G p H; unfold standard_move in H.
  destruct (shortest_of is_3chain_b G) eqn:E3;
    [injection H as <-; apply (shortest_of_In is_3chain_b G); exact E3|].
  destruct (shortest_of is_loop_b G) eqn:EL;
    [injection H as <-; apply (shortest_of_In is_loop_b G); exact EL|].
  apply (shortest_of_In any_comp G); exact H.
Qed.

(** * The three cases *)

Definition count_loops (G : position) : nat := length (filter is_loop_b G).

Definition drop_first (f : comp -> bool) (G : position) : position :=
  match filter (fun p => f (fst p)) (selections G) with
  | [] => G
  | p :: _ => snd p
  end.

(** [G] is one three-chain together with one or more loops. *)
Definition three_plus_loops_b (G : position) : bool :=
  ((count3 G =? 1)%nat && (1 <=? count_loops G)%nat &&
   ((count_loops G + 1)%nat =? length G)%nat)%bool.

(** After removing one four-loop, exactly three three-chains remain. *)
Definition rest_is_three_threes_b (G : position) : bool :=
  let H := drop_first is_4loop_b G in
  ((count3 H =? 3)%nat && (length H =? 3)%nat)%bool.

Definition case_i (G : position) : bool :=
  ((2 <=? cval G) && three_plus_loops_b G)%bool.

Definition case_ii (G : position) : bool :=
  ((cval G <=? 1) && (-1 <=? cval G) && (1 <=? count4 G)%nat &&
   negb (rest_is_three_threes_b G))%bool.

Definition case_iii (G : position) : bool :=
  let H := drop_first is_3chain_b (drop_first is_4loop_b G) in
  ((cval G <=? -2) && (1 <=? count4 G)%nat && (1 <=? count3 G)%nat &&
   ((Z.of_nat (size H) mod 4) =? 0) && (count3 H =? 0)%nat)%bool.

(** * The strategy *)

Definition allcock_move (G : position) : option (comp * position) :=
  if (case_i G || case_ii G || case_iii G)%bool
  then shortest_of is_loop_b G
  else standard_move G.

Lemma allcock_move_In :
  forall G p, allcock_move G = Some p -> In p (selections G).
Proof.
  intros G p H; unfold allcock_move in H.
  destruct (case_i G || case_ii G || case_iii G)%bool;
    [apply (shortest_of_In is_loop_b G); exact H
     | apply standard_move_In; exact H].
Qed.

(** Whenever the strategy names a move on a nonempty position, that move is
    legal and, if it attains the value, no opening is better. *)
Theorem allcock_move_optimal_iff :
  forall G p,
    G <> [] -> allcock_move G = Some p ->
    (value G = value_open p <->
     forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p HNil H.
  apply opener_optimal_iff; [exact HNil | apply allcock_move_In; exact H].
Qed.

(** * Checking the strategy on a position *)

Definition allcock_okb (G : position) : bool :=
  match allcock_move G with
  | None => true
  | Some p => Z.eqb (value G) (value_open p)
  end.

Theorem allcock_okb_sound :
  forall G p,
    allcock_okb G = true -> allcock_move G = Some p ->
    value G = value_open p /\
    (forall q, In q (selections G) -> value_open p <= value_open q).
Proof.
  intros G p Hok Hm.
  assert (HNil : G <> []).
  { intros ->; unfold allcock_move, shortest_of, standard_move in Hm;
      simpl in Hm; discriminate. }
  unfold allcock_okb in Hok; rewrite Hm in Hok.
  apply Z.eqb_eq in Hok.
  split; [exact Hok|].
  apply (allcock_move_optimal_iff G p HNil Hm); exact Hok.
Qed.

(** * Allcock's Lemma 3.1 *)

(** A three-chain and a loop: opening the loop attains the value and opening
    the chain costs exactly two. This is the base the case analysis of
    Theorem 1.1 bottoms out on. *)
Theorem open_loop_optimal_3_loop :
  forall l, (4 <= l)%nat ->
    value_open (Loop l, [Chain 3]) = value [Chain 3; Loop l] /\
    value_open (Chain 3, [Loop l]) = value [Chain 3; Loop l] + 2.
Proof.
  intros l Hl.
  rewrite (value_three_loop l Hl), cval_three_loop.
  unfold value_open; cbn [fst snd].
  rewrite !value_single; cbn [csize].
  split.
  - rewrite controller_gives_up by (cbn [hand]; lia).
    unfold give_up_control; cbn [csize]; lia.
  - rewrite controller_keeps by (cbn [hand]; lia).
    unfold keep_control; cbn [csize hand]; lia.
Qed.

(** So on those positions the loop is strictly the better opening. *)
Corollary loop_strictly_better :
  forall l, (4 <= l)%nat ->
    value_open (Loop l, [Chain 3]) < value_open (Chain 3, [Loop l]).
Proof.
  intros l Hl; destruct (open_loop_optimal_3_loop l Hl) as [H1 H2].
  rewrite H1, H2; lia.
Qed.

(** * Allcock's Example 1.2 *)

(** Five three-chains, a four-loop and an eight-loop. The controlled value is
    [27 - 4*5 - 8*2 + 6 = -3], so case (iii) is the only candidate and it
    fails because what is left has three-chains; the standard move applies
    and opens a three-chain. *)
Definition example_G : position :=
  [Chain 3; Chain 3; Chain 3; Chain 3; Chain 3; Loop 4; Loop 8].

Example example_cval : cval example_G = -3.
Proof. vm_compute; reflexivity. Qed.

Example example_cases :
  (case_i example_G, case_ii example_G, case_iii example_G)
  = (false, false, false).
Proof. vm_compute; reflexivity. Qed.

Example example_opens_three_chain :
  match allcock_move example_G with
  | Some p => fst p = Chain 3
  | None => False
  end.
Proof. vm_compute; reflexivity. Qed.

(** The move the strategy names attains the value, so it is optimal. *)
Example example_1_2 : allcock_okb example_G = true.
Proof. vm_compute; reflexivity. Qed.

(** ****************************************************************** *)
(** An optimality criterion for openings.

    [GameTrees.DotsAndBoxes] names Allcock's strategy and checks it position
    by position, but proves nothing about when an opening is optimal. The
    engine of Allcock's Theorem 1.1 is the observation that an opening which
    leaves the terminal bonus alone, and leaves behind at least the handout it
    gives away, realises the controlled value and is therefore optimal.

    [open_optimal_of_step] is that criterion, and [open_loop_optimal_ge4] and
    [open_chain_optimal_ge2] are the two instances the case analysis of
    Theorem 1.1 rests on. The theorem itself is still not proved: its three
    named cases turn on comparing the shortest loop against the standard move
    when the criterion does not apply, and that comparison is not made here. *)

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
Theorem case_i_optimal :
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

(** ****************************************************************** *)
(** The loony endgame as a game tree of the host library.

    [dab_tree] unfolds a position with [GameTrees.Trees.unfold_tree], so its
    soundness and completeness against [reachable] come from the library
    rather than from anything special to Dots and Boxes. [value_tval] then
    proves that [value] is a [fold_tree] over that tree: the closed forms of
    [GameTrees.DotsAndBoxes] are statements about the library's own game tree,
    not a computation that avoids it. *)

Import ListNotations.

Open Scope Z_scope.

(** * Unfolding a position *)

(** A move removes one component, so the component count falls. *)
Definition shorter (H G : position) : Prop := (length H < length G)%nat.

#[export] Instance WF_shorter : WellFounded shorter.
Proof. unfold shorter; apply Relations.wf_inverse_image, Nat.lt_wf_0. Defined.

Definition dab_next (G : position)
  : {l : list position | Forall (fun H => shorter H G) l}.
Proof.
  exists (map snd (selections G)).
  apply Forall_forall; intros H HH.
  apply in_map_iff in HH; destruct HH as [p [<- Hp]].
  unfold shorter; pose proof (selections_length G p Hp); lia.
Defined.

Lemma dab_next_proj :
  forall G, (dab_next G).1 = map snd (selections G).
Proof. reflexivity. Qed.

(** The game tree of a loony endgame, built by the library's unfolder. *)
Definition dab_tree (G : position) : tree position :=
  unfold_tree shorter dab_next G.

(** Soundness and completeness are inherited. *)
Theorem dab_tree_sound :
  forall G H, In_tree H (dab_tree G) -> reachable dab_next G H.
Proof. intros G; apply unfold_tree_sound. Qed.

Theorem dab_tree_complete :
  forall G H, reachable dab_next G H -> In_tree H (dab_tree G).
Proof. intros G; apply unfold_tree_complete. Qed.

Lemma dab_tree_unwrap :
  forall G, dab_tree G = node G (map dab_tree (map snd (selections G))).
Proof.
  intros G; unfold dab_tree at 1.
  rewrite unfold_tree_unwrap, dab_next_proj; reflexivity.
Qed.

(** * The value is a fold over that tree *)

(** Pair each component with the value of what removing it leaves. *)
Fixpoint zip_vopen (sel : list (comp * position)) (vs : list Z) : list Z :=
  match sel, vs with
  | p :: sr, v :: vr => vopen (fst p) v :: zip_vopen sr vr
  | _, _ => []
  end.

Lemma zip_vopen_value :
  forall sel, zip_vopen sel (map (fun p => value (snd p)) sel)
              = map value_open sel.
Proof.
  induction sel as [|p sel IH]; simpl; [reflexivity|].
  unfold value_open at 2; rewrite IH; reflexivity.
Qed.

(** The opener minimises over the components, reading the children's values
    off the tree. *)
Definition comb (G : position) (vs : list Z) : Z :=
  match zip_vopen (selections G) vs with
  | [] => 0
  | x :: xs => minl x xs
  end.

Definition tval : tree position -> Z := fold_tree comb.

Lemma tval_node :
  forall G ts, tval (node G ts) = comb G (map tval ts).
Proof. reflexivity. Qed.

Theorem value_tval : forall G, value G = tval (dab_tree G).
Proof.
  assert (Haux : forall n G, (length G <= n)%nat -> value G = tval (dab_tree G)).
  { induction n as [|n IH]; intros G Hn.
    - assert (HG : G = []) by (destruct G; simpl in Hn; [reflexivity | lia]).
      subst G; rewrite dab_tree_unwrap; simpl.
      rewrite value_nil; reflexivity.
    - rewrite dab_tree_unwrap, tval_node, !map_map.
      assert (Hmap : map (fun x => tval (dab_tree (snd x))) (selections G)
                     = map (fun p => value (snd p)) (selections G)).
      { apply map_ext_in; intros p Hp.
        symmetry; apply IH.
        pose proof (selections_length G p Hp); lia. }
      rewrite Hmap.
      unfold comb; rewrite zip_vopen_value.
      rewrite value_unfold.
      destruct (selections G) as [|p more]; reflexivity. }
  intros G; apply (Haux (length G)); lia.
Qed.

(** So every closed form proved of [value] is a statement about this tree.
    In particular the complete value of Allcock's Theorem 4.1 evaluates it. *)
Corollary v41_tval :
  forall G, wf G -> G <> [] -> tval (dab_tree G) = v41 G.
Proof.
  intros G Hw Hn; rewrite <- value_tval; apply value_complete; assumption.
Qed.

(** And the controlled value bounds the tree's value from below. *)
Corollary cval_le_tval :
  forall G, wf G -> cval G <= tval (dab_tree G).
Proof.
  intros G Hw; rewrite <- value_tval; apply cval_le_value; exact Hw.
Qed.

(** ****************************************************************** *)
(** The board as a game tree of the host library.

    [GameTrees.DotsAndBoxes] unfolds a loony position, a multiset of
    components, and so never reaches the board itself. This file unfolds the
    board: a state, its legal edges, and the states they lead to.

    Drawing an edge shortens the undrawn list, so [flip board_step] is
    wellfounded and [GameTrees.Trees.unfold_tree] applies. Soundness and
    completeness against [reachable] come from the library. What is proved
    here beyond that is [reachable_iff_legal]: the states in the tree are
    exactly the states legal play reaches, so [run] and [legal] of
    [GameTrees.DotsAndBoxesBoard] and [reachable] of the library name the same
    set. *)

Section BoardTree.

Variables m n : nat.

(** * The step relation *)

(** One drawn edge. *)
Inductive board_step : st -> st -> Prop :=
| bstep : forall s e, In e (db_moves m n s) -> board_step s (db_play m n s e).

(** The undrawn edges are the measure. *)
Definition blater (s1 s2 : st) : Prop :=
  (db_measure m n s1 < db_measure m n s2)%nat.

Instance WF_blater : WellFounded blater.
Proof. unfold blater; apply Relations.wf_inverse_image, Nat.lt_wf_0. Defined.

Instance WF_flip_board_step : WellFounded (flip board_step).
Proof.
  eapply WF_subrelation, WF_blater.
  intros s2 s1; inversion 1; subst.
  unfold blater; apply db_measure_play; assumption.
Defined.

(** Every legal edge yields a step, so the successor list carries its own
    decrease proof. *)
Lemma board_next_intrinsic :
  forall s : st, {l : list st | Forall (board_step s) l}.
Proof.
  intros s; exists (map (db_play m n s) (db_moves m n s)).
  apply Forall_map, Forall_forall; intros e He; apply bstep; exact He.
Defined.

Lemma board_next_proj :
  forall s,
    (board_next_intrinsic s).1 = map (db_play m n s) (db_moves m n s).
Proof. intros s; reflexivity. Qed.

(** * The tree *)

(** Type-checking this is the finiteness proof. *)
Definition board_tree (s : st) : tree st :=
  unfold_tree (flip board_step) board_next_intrinsic s.

Theorem board_tree_sound :
  forall s t, In_tree t (board_tree s) -> reachable board_next_intrinsic s t.
Proof. intros s; apply unfold_tree_sound. Qed.

Theorem board_tree_complete :
  forall s t, reachable board_next_intrinsic s t -> In_tree t (board_tree s).
Proof. intros s; apply unfold_tree_complete. Qed.

(** * The library step is the board step *)

Lemma step_iff_board_step :
  forall s1 s2, step board_next_intrinsic s1 s2 <-> board_step s1 s2.
Proof.
  intros s1 s2; unfold step; rewrite board_next_proj; split.
  - intros H; apply in_map_iff in H; destruct H as [e [<- He]].
    apply bstep; exact He.
  - intros H; inversion H; subst.
    apply in_map_iff; eexists; split; [reflexivity | assumption].
Qed.

(** * Legal play and reachability agree *)

Lemma run_app :
  forall ms ms' s, run m n s (ms ++ ms') = run m n (run m n s ms) ms'.
Proof.
  induction ms as [|e ms IH]; intros ms' s; simpl; [reflexivity | apply IH].
Qed.

Lemma legal_app :
  forall ms ms' s,
    legal m n s (ms ++ ms') <->
    (legal m n s ms /\ legal m n (run m n s ms) ms').
Proof.
  induction ms as [|e ms IH]; intros ms' s; simpl.
  - split; [intros H; split; [exact I | exact H] | intros [_ H]; exact H].
  - rewrite IH; split.
    + intros [He [Hm Hm']]; repeat split; assumption.
    + intros [[He Hm] Hm']; repeat split; assumption.
Qed.

(** Any legal run lands on a reachable state. *)
Theorem reachable_of_legal :
  forall ms s, legal m n s ms -> reachable board_next_intrinsic s (run m n s ms).
Proof.
  induction ms as [|e ms IH]; intros s Hl; simpl in Hl |- *.
  - apply rt_refl.
  - destruct Hl as [He Hms].
    eapply rt_trans; [| apply IH; exact Hms].
    apply rt_step, step_iff_board_step, bstep; exact He.
Qed.

(** And every reachable state is the end of a legal run. *)
Theorem legal_of_reachable :
  forall s t,
    reachable board_next_intrinsic s t ->
    exists ms, legal m n s ms /\ run m n s ms = t.
Proof.
  intros s t H; induction H as [x y Hstep | x | x y z Hxy IHxy Hyz IHyz].
  - apply step_iff_board_step in Hstep; inversion Hstep; subst.
    exists [e]; split; [split; [assumption | exact I] | reflexivity].
  - exists []; split; [exact I | reflexivity].
  - destruct IHxy as [ms1 [Hl1 Hr1]].
    destruct IHyz as [ms2 [Hl2 Hr2]].
    exists (ms1 ++ ms2); split.
    + apply legal_app; split; [exact Hl1 | rewrite Hr1; exact Hl2].
    + rewrite run_app, Hr1; exact Hr2.
Qed.

(** So the tree holds exactly the states legal play reaches. *)
Theorem reachable_iff_legal :
  forall s t,
    reachable board_next_intrinsic s t <->
    exists ms, legal m n s ms /\ run m n s ms = t.
Proof.
  intros s t; split; [apply legal_of_reachable|].
  intros [ms [Hl Hr]]; rewrite <- Hr; apply reachable_of_legal; exact Hl.
Qed.

(** The tree of a board is the tree of its legal play. *)
Theorem board_tree_iff_legal :
  forall s t,
    In_tree t (board_tree s) <->
    exists ms, legal m n s ms /\ run m n s ms = t.
Proof.
  intros s t; split.
  - intros H; apply reachable_iff_legal, board_tree_sound; exact H.
  - intros H; apply board_tree_complete, reachable_iff_legal; exact H.
Qed.

(** * Wellformedness travels through the tree *)

(** Every state in the tree of a wellformed board is wellformed, so the
    counting theory of [GameTrees.DotsAndBoxesBoard] applies at every node. *)
Theorem board_tree_wf :
  forall s t, wf_st m n s -> In_tree t (board_tree s) -> wf_st m n t.
Proof.
  intros s t Hw Hin.
  apply board_tree_iff_legal in Hin; destruct Hin as [ms [Hl <-]].
  apply wf_run; assumption.
Qed.

(** In particular the whole tree from the empty board is wellformed. *)
Corollary board_tree_init_wf :
  forall t, In_tree t (board_tree (init)) -> wf_st m n t.
Proof. intros t; apply board_tree_wf, wf_init. Qed.

End BoardTree.
