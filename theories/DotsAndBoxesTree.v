(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** The loony endgame as a game tree of the host library.

    [dab_tree] unfolds a position with [GameTrees.Trees.unfold_tree], so its
    soundness and completeness against [reachable] come from the library
    rather than from anything special to Dots and Boxes. [value_tval] then
    proves that [value] is a [fold_tree] over that tree: the closed forms of
    [GameTrees.DotsAndBoxes] are statements about the library's own game tree,
    not a computation that avoids it. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.Relations.
Require Import GameTrees.Trees.
Require Import GameTrees.DotsAndBoxes.

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
