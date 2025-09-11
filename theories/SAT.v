(* Copyright 2024 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(* A brute-force propositional SAT solver. *)
From Stdlib Require Import List PeanoNat Psatz Arith.
From Stdlib Require Import Wellfounded.Inverse_Image.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.Relations.
Require Import GameTrees.Trees.

Definition name : Type := nat.

Inductive formula : Type :=
| f_var : name -> formula
| f_bool : bool -> formula
| f_not : formula -> formula
| f_and : formula -> formula -> formula
| f_or : formula -> formula -> formula.

Definition fimplies (f1 f2 : formula) : formula :=
  f_or (f_not f1) f2.

Lemma dec_eq_name : forall (n1 n2 : name), {n1 = n2} + {n1 <> n2}.
Proof. decide equality. Defined.

Lemma dec_eq_formula : forall (f1 f2 : formula), {f1 = f2} + {f1 <> f2}.
Proof. decide equality. eapply dec_eq_name. decide equality. Defined.

Fixpoint free_vars (f : formula) : list name :=
  match f with
  | f_var n => [n]
  | f_bool _ => []
  | f_not f1 => free_vars f1
  | f_and f1 f2 => free_vars f1 ++ free_vars f2
  | f_or f1 f2 => free_vars f1 ++ free_vars f2
  end.

Fixpoint eval (f : formula) : option bool :=
  match f with
  | f_var n => None
  | f_bool b => Some b
  | f_not f1 =>
    match eval f1 with
    | Some b => Some (negb b)
    | None => None
    end
  | f_and f1 f2 =>
    match eval f1, eval f2 with
    | Some b1, Some b2 => Some (andb b1 b2)
    | _, _ => None
    end
  | f_or f1 f2 =>
    match eval f1, eval f2 with
    | Some b1, Some b2 => Some (orb b1 b2)
    | _, _ => None
    end
  end.

Fixpoint assign (f : formula) (n : name) (b : bool) : formula :=
  match f with
  | f_var n' => if dec_eq_name n n' then f_bool b else f_var n'
  | f_bool b => f_bool b
  | f_not f1 => f_not (assign f1 n b)
  | f_and f1 f2 => f_and (assign f1 n b) (assign f2 n b)
  | f_or f1 f2 => f_or (assign f1 n b) (assign f2 n b)
  end.

Lemma assigned_variable_is_not_free :
  forall (f : formula) (n : name) (b : bool),
    ~ In n (free_vars (assign f n b)).
Proof.
  intros f n b H.
  induction f; simpl in *; auto.
  * destruct (dec_eq_name n n0); simpl in *; auto.
    destruct H; auto.
  * destruct (in_app_or _ _ _ H); auto.
  * destruct (in_app_or _ _ _ H); auto.
Qed.

Lemma assign_doesnt_change_other_variables :
  forall (f : formula) (n1 n2 : name) (b : bool),
    n1 <> n2 ->
    In n1 (free_vars f) ->
    In n1 (free_vars (assign f n2 b)).
Proof.
  intros f n1 n2 b neq pf.
  induction f; simpl in *; auto.
  destruct pf; try contradiction; subst.
  destruct (dec_eq_name n2 n1); simpl in *; auto.
  destruct (in_app_or _ _ _ pf); eapply in_or_app; [left | right]; auto.
  destruct (in_app_or _ _ _ pf); eapply in_or_app; [left | right]; auto.
Qed.

Definition game : Type := list (name * bool).

Definition apply_assignments (f : formula) (g : game) : formula :=
  List.fold_left (fun f '(n, b) => assign f n b) g f.

Definition sat_next (f : formula) (g : game) : list game :=
  match free_vars (apply_assignments f g) with
  | [] => []
  | n :: _ => [ (n, true) :: g ; (n, false) :: g ]
  end.

Definition later (f : formula) (g1 g2 : game) : Prop :=
  length (free_vars (apply_assignments f g1)) < length (free_vars (apply_assignments f g2)).

Instance WF_later (f : formula) : WellFounded (later f).
Proof.
  unfold WellFounded, later.
  eapply wf_inverse_image.
  eapply Nat.lt_wf_0.
Qed.

Lemma assign_length_le :
  forall (f : formula) (n : name) (b : bool),
    length (free_vars (assign f n b)) <= length (free_vars f).
Proof.
  intros f n b.
  induction f; simpl; auto.
  destruct (dec_eq_name n n0); simpl; lia.
  rewrite !length_app; lia.
  rewrite !length_app; lia.
Qed.

Lemma assign_is_later :
  forall (f : formula) (n : name) (b : bool),
    In n (free_vars f) ->
    length (free_vars (assign f n b)) < length (free_vars f).
Proof.
  intros f n b Hin.
  induction f; simpl in *.
  * destruct Hin as [Heq | Hcontra]; [| contradiction].
    subst.
    destruct (dec_eq_name n n); [| contradiction].
    simpl; lia.
  * contradiction.
  * apply IHf, Hin.
  * rewrite length_app.
    apply in_app_or in Hin.
    destruct Hin as [Hin1 | Hin2].
    + rewrite length_app.
      specialize (IHf1 Hin1).
      specialize (assign_length_le f2 n b).
      lia.
    + rewrite length_app.
      specialize (IHf2 Hin2).
      specialize (assign_length_le f1 n b).
      lia.
  * rewrite length_app.
    apply in_app_or in Hin.
    destruct Hin as [Hin1 | Hin2].
    + rewrite length_app.
      specialize (IHf1 Hin1).
      specialize (assign_length_le f2 n b).
      lia.
    + rewrite length_app.
      specialize (IHf2 Hin2).
      specialize (assign_length_le f1 n b).
      lia.
Qed.

Lemma assign_reverse_preservation :
  forall (f : formula) (n1 n2 : name) (b : bool),
    n1 <> n2 ->
    In n1 (free_vars (assign f n2 b)) ->
    In n1 (free_vars f).
Proof.
  intros f n1 n2 b neq pf.
  induction f as [n | b' | f1 IH1 | f1 IH1 f2 IH2 | f1 IH1 f2 IH2]; simpl in *.
  * destruct (dec_eq_name n2 n) as [Heq_n2_n | Hneq_n2_n]; intuition auto.
  * contradiction.
  * auto.
  * apply in_app_or in pf.
    destruct pf as [pf1 | pf2]; apply in_or_app; [left|right]; auto.
  * apply in_app_or in pf.
    destruct pf as [pf1 | pf2]; apply in_or_app; [left|right]; auto.
Qed.

Lemma free_vars_assign_subset :
  forall (f : formula) (n : name) (b : bool),
    forall (m : name), In m (free_vars (assign f n b)) -> In m (free_vars f).
Proof.
  intros f n b m Hin.
  destruct (dec_eq_name m n) as [Heq | Hneq].
  - subst m.
    exfalso.
    apply (assigned_variable_is_not_free f n b); auto.
  - apply (assign_reverse_preservation f m n b); auto.
Qed.

Lemma free_vars_apply_assignments_subset_aux :
  forall (g : game) (f : formula),
    forall n, In n (free_vars (apply_assignments f g)) -> In n (free_vars f).
Proof.
  induction g as [| [n' b'] g' IH]; intros p n Hin; simpl in *.
  - auto.
  - apply IH in Hin.
    apply free_vars_assign_subset in Hin; auto.
Qed.


Lemma free_vars_apply_assignments_subset :
  forall (f : formula) (g : game),
    forall n, In n (free_vars (apply_assignments f g)) -> In n (free_vars f).
Proof.
  intros f g n Hin.
  apply (free_vars_apply_assignments_subset_aux g f n Hin).
Qed.

Lemma assign_commute :
  forall (f : formula) (n1 n2 : name) (b1 b2 : bool),
    n1 <> n2 ->
    assign (assign f n1 b1) n2 b2 =
    assign (assign f n2 b2) n1 b1.
Proof.
  intros f n1 n2 b1 b2 Hneq.
  induction f as [n | bb | f1 IH1 | f1 IH1 f2 IH2 | f1 IH1 f2 IH2]; simpl.
  * destruct (dec_eq_name n1 n) as [E1|E1]; destruct (dec_eq_name n2 n) as [E2|E2]; simpl.
    + subst. contradiction.
    + destruct (dec_eq_name n1 n) as [E1'|E1']; [auto | contradiction].
    + destruct (dec_eq_name n2 n) as [E2'|E2']; [auto | contradiction].
    + destruct (dec_eq_name n2 n) as [E2'|E2']; [contradiction | ].
      destruct (dec_eq_name n1 n) as [E1'|E1']; [contradiction | auto].
  * auto.
  * rewrite IH1; auto.
  * rewrite IH1, IH2; auto.
  * rewrite IH1, IH2; auto.
Qed.

Lemma apply_assignments_reduces_vars :
  forall (f : formula) (n : name) (b : bool) (g : game),
    In n (free_vars (apply_assignments f g)) ->
    length (free_vars (apply_assignments f ((n, b) :: g))) <
    length (free_vars (apply_assignments f g)).
Proof.
  intros f n b g Hin.
  revert f n b Hin.
  induction g as [| [n' b'] g' IH]; intros f n b Hin; simpl in *.
  - simpl in Hin. apply assign_is_later; auto.
  - destruct (dec_eq_name n n') as [Heq|Hneq].
    + subst n'. exfalso.
      apply (free_vars_apply_assignments_subset (assign f n b') g') in Hin.
      apply (assigned_variable_is_not_free f n b' Hin).
    + rewrite assign_commute; auto.
Qed.

Lemma apply_assignments_assign_first_reduces :
  forall (f : formula) (n : name) (b : bool) (g : game),
    In n (free_vars (apply_assignments f g)) ->
    length (free_vars (apply_assignments (assign f n b) g)) <
    length (free_vars (apply_assignments f g)).
Proof.
  intros f n b g Hin.
  revert f n b Hin.
  induction g as [| [n' b'] g' IH]; intros f n b Hin; simpl in *.
  * apply assign_is_later; auto.
  * destruct (dec_eq_name n n') as [Heq|Hneq].
    + subst n'. exfalso.
      apply (free_vars_apply_assignments_subset (assign f n b') g') in Hin.
      apply (assigned_variable_is_not_free f n b' Hin).
    + rewrite assign_commute; auto.
Qed.

Lemma sat_next_produces_later :
  forall (f : formula) (g : game),
    Forall (fun g' : game => later f g' g) (sat_next f g).
Proof.
  intros f g.
  unfold sat_next, later.
  destruct (free_vars (apply_assignments f g)) eqn:Heq.
  constructor.
  constructor.
  simpl.
  assert (H: length (free_vars (apply_assignments (assign f n true) g)) <
             length (free_vars (apply_assignments f g))).
  { apply apply_assignments_assign_first_reduces.
    rewrite Heq. left; reflexivity. }
  rewrite Heq in H.
  simpl in H.
  lia.
  constructor.
  simpl.
  assert (H: length (free_vars (apply_assignments (assign f n false) g)) <
             length (free_vars (apply_assignments f g))).
  { apply apply_assignments_assign_first_reduces.
    rewrite Heq. left; reflexivity. }
  rewrite Heq in H.
  simpl in H.
  lia.
  constructor.
Qed.

Definition sat_next_intrinsic (f : formula) (g : game) :
  {l : list game | Forall (fun g' : game => later f g' g) l}.
Proof.
  exists (sat_next f g).
  apply sat_next_produces_later.
Defined.

Fixpoint somes {A : Type} (l : list (option A)) : list A :=
  match l with
  | [] => []
  | Some x :: xs => x :: somes xs
  | None :: xs => somes xs
  end.

(* Look for a node in the game tree that evaluates to a [Some] value. *)
Definition find_sat (f : formula) : option (list (name * bool)) :=
  fold_tree
    (fun (g : game) (l : list (option (list (name * bool)))) =>
       match eval (apply_assignments f g) with
       | Some true => Some g
       | _ => List.hd_error (somes l)
       end)
    (Trees.unfold_tree (later f) (sat_next_intrinsic f) []).

From Stdlib Require Import String.
#[local] Open Scope string_scope.

Require Import SimpleIO.SimpleIO.
From Stdlib Require Import Sorting.Mergesort.
Require Import ExtLib.Core.RelDec.
Import IO.Notations.

Definition print_assignment (f : name * bool) : IO unit :=
  let '(n, b) := f in
  print_int (ExtrOcamlIntConv.int_of_nat n) ;;
  print_string " = " ;;
  print_string (if b then "true" else "false") ;;
  print_newline.

Fixpoint iter {A : Type} (f : A -> IO unit) (l : list A) : IO unit :=
  match l with
  | [] => IO.ret tt
  | x :: xs => f x ;; iter f xs
  end.

Definition print_solution (o : option (list (name * bool))) : IO unit :=
  match o with
  | None => print_string "unsat"
  | Some l =>
      print_string "sat" ;;
      print_newline ;;
      iter print_assignment l
  end.

Definition main : IO unit :=
  print_solution (find_sat (f_not (fimplies (f_var 0) (f_var 1)))).

Definition unsafe_main : io_unit :=
  IO.unsafe_run main.

From Stdlib Require Import ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlNatInt.
From Stdlib Require Import ExtrOcamlString.
Extract Inductive sigT => "( * )" [""].
Extract Inlined Constant negb => "not".
Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
Extract Inlined Constant app => "(@)".
Extract Inlined Constant concat => "List.concat".
Extract Inlined Constant map => "List.map".
Extract Inlined Constant find => "List.find_opt".
Extract Inlined Constant ltb => "(<)".
Extraction Inline zip_proofs.
Extraction Inline unfold_tree_aux.
Extraction "sat.ml" unsafe_main.
