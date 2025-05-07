(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

Require Import Corelib.Classes.RelationClasses.
Require Import Corelib.Relations.Relation_Definitions.
From Stdlib Require Import List.

Require Import ExtLib.Core.RelDec.

Import ListNotations.

Definition monotone
           {A B : Type}
           (R1 : relation A)
           (R2 : B -> B -> Prop)
           (g : A -> B) : Prop :=
  forall (x y : A), R1 x y -> R2 (g x) (g y).

Class WellFounded {A : Type} (R : relation A) : Prop :=
  wellfounded : forall (x : A), Acc R x.

Theorem WF_subrelation :
  forall
    {A : Type}
    (R1 R2 : relation A)
    (sub : subrelation R1 R2)
   `(WF : @WellFounded A R2),
  @WellFounded A R1.
Proof.
  intros A R1 R2 sub WF x.
  generalize (WF x); revert x.
  induction 1; constructor; intuition.
Defined.

Instance WF_nat_lt : WellFounded lt.
Proof.
  eapply PeanoNat.Nat.lt_wf_0.
Defined.

Definition comparing {A B : Type} (R : relation B) (f : A -> B) : relation A :=
  fun (x y : A) => R (f x) (f y).

#[export] Instance RelDec_comparing :
  forall {A B : Type} (R : relation B) `{RelDec B R} (f : A -> B), RelDec (comparing R f).
Proof.
  intros A B R DR f.
  constructor.
  intros x y.
  apply (rel_dec (f x) (f y)).
Defined.

#[export] Instance RelDec_Correct_comparing :
  forall {A B : Type} (R : relation B)
        `{D : RelDec B R} `{@RelDec_Correct B R D}
         (f : A -> B), RelDec_Correct (RelDec_comparing R f).
Proof.
  intros A B R D C f.
  constructor.
  intros x y.
  unfold comparing.
  eapply (@rel_dec_correct B R D C).
Defined.

#[export] Instance RelDec_nat_lt : @RelDec nat lt.
  constructor.
  eapply Nat.ltb.
Defined.

#[export] Instance RelDec_nat_gt : @RelDec nat gt.
  constructor.
  intros a b.
  exact (negb (Nat.leb a b)).
Defined.
