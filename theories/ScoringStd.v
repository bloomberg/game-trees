(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** The standard scoring game, and where the loony endgame sits relative to
    it.

    Ettinger, and Milley and Renault after him, write a scoring game with the
    two option lists separated and the turn carried by which of two mutually
    recursive values is being read: [Lsc] is the score Left secures with Left
    to move, [Rsc] with Right to move. Play alternates by construction, and a
    player with no option ends the game at its score.

    [GameTrees.Scoring] instead writes the mover into the node. [embed] sends
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

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Import ListNotations.

Require Import GameTrees.Helpers.
Require Import GameTrees.DotsAndBoxes.
Require Import GameTrees.Scoring.

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
