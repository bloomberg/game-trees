(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the Apache 2.0 license. *)

(** Conway's partisan games: the order, the group structure, the outcomes. *)

From Stdlib Require Import List.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Psatz.
From Stdlib Require Import Bool.
From Stdlib Require Import Sorting.Sorted.
From Stdlib Require Import Sorting.Permutation.

Import ListNotations.
Require Import GameTrees.Helpers.

(** * Boolean list helpers *)

Lemma forallb_ext_in :
  forall {A : Type} (f g : A -> bool) (l : list A),
    (forall x, In x l -> f x = g x) -> forallb f l = forallb g l.
Proof.
  intros A f g l; induction l as [|a l IH]; intros H; simpl; auto.
  rewrite (H a (or_introl eq_refl)), IH; auto.
  intros x Hx; apply H; right; auto.
Qed.

Lemma negb_existsb :
  forall {A : Type} (f : A -> bool) (l : list A),
    negb (existsb f l) = forallb (fun x => negb (f x)) l.
Proof.
  intros A f l; induction l as [|a l IH]; simpl; auto.
  destruct (f a); simpl; auto.
Qed.

Lemma negb_forallb :
  forall {A : Type} (f : A -> bool) (l : list A),
    negb (forallb f l) = existsb (fun x => negb (f x)) l.
Proof.
  intros A f l; induction l as [|a l IH]; simpl; auto.
  destruct (f a); simpl; auto.
Qed.

Lemma in_le_list_sum : forall x l, In x l -> x <= list_sum l.
Proof.
  intros x l; induction l as [|a l IH]; intros Hin; [destruct Hin|].
  destruct Hin as [-> | Hin]; simpl; [lia | specialize (IH Hin); lia].
Qed.

Lemma orb_middle4 :
  forall a b c d : bool, ((a || b) || (c || d) = (a || c) || (b || d))%bool.
Proof. intros [] [] [] []; reflexivity. Qed.

Lemma andb_middle4 :
  forall a b c d : bool, ((a && b) && (c && d) = (a && c) && (b && d))%bool.
Proof. intros [] [] [] []; reflexivity. Qed.

(** * Games *)

(** A partisan game: the option lists of Left and of Right. *)
Inductive pgame : Type :=
| PG : list pgame -> list pgame -> pgame.

Definition lopts (G : pgame) : list pgame := match G with PG L _ => L end.
Definition ropts (G : pgame) : list pgame := match G with PG _ R => R end.

Lemma lopts_PG : forall L R, lopts (PG L R) = L.
Proof. reflexivity. Qed.

Lemma ropts_PG : forall L R, ropts (PG L R) = R.
Proof. reflexivity. Qed.

(** A game is determined by its two option lists. *)
Lemma pgame_eq :
  forall G H, lopts G = lopts H -> ropts G = ropts H -> G = H.
Proof. intros [a b] [c d]; simpl; intros -> ->; auto. Qed.

(** Induction supplying the hypothesis for every option. *)
Fixpoint pgame_forall_ind
    (P : pgame -> Prop)
    (pf : forall (L R : list pgame), Forall P L -> Forall P R -> P (PG L R))
    (G : pgame) {struct G} : P G :=
  match G with
  | PG L R =>
      pf L R
        (list_ind (Forall P) (Forall_nil P)
           (fun x xs IHxs => Forall_cons x (pgame_forall_ind P pf x) IHxs) L)
        (list_ind (Forall P) (Forall_nil P)
           (fun x xs IHxs => Forall_cons x (pgame_forall_ind P pf x) IHxs) R)
  end.

(** An upper bound on the length of play. *)
Fixpoint rank (G : pgame) : nat :=
  match G with
  | PG L R => S (list_sum (map rank L) + list_sum (map rank R))
  end.

Lemma rank_pos : forall G, 1 <= rank G.
Proof. intros [L R]; simpl; lia. Qed.

Lemma rank_lopt : forall G g, In g (lopts G) -> rank g < rank G.
Proof.
  intros [L R] g Hg; simpl in *.
  pose proof (in_le_list_sum (rank g) (map rank L) (in_map rank L g Hg)); lia.
Qed.

Lemma rank_ropt : forall G g, In g (ropts G) -> rank g < rank G.
Proof.
  intros [L R] g Hg; simpl in *.
  pose proof (in_le_list_sum (rank g) (map rank R) (in_map rank R g Hg)); lia.
Qed.

(** * Outcomes *)

(** [lwin G t] decides whether Left wins [G], with [t] marking Left to move. *)
Fixpoint lwin (G : pgame) (t : bool) : bool :=
  match G with
  | PG L R =>
    if t then existsb (fun g => lwin g false) L
         else forallb (fun g => lwin g true) R
  end.

Lemma lwin_true :
  forall G, lwin G true = existsb (fun g => lwin g false) (lopts G).
Proof. intros [L R]; reflexivity. Qed.

Lemma lwin_false :
  forall G, lwin G false = forallb (fun g => lwin g true) (ropts G).
Proof. intros [L R]; reflexivity. Qed.

(** * Negation and sum *)

(** Swapping the roles of the players. *)
Fixpoint pneg (G : pgame) : pgame :=
  match G with PG L R => PG (map pneg R) (map pneg L) end.

Lemma lopts_pneg : forall G, lopts (pneg G) = map pneg (ropts G).
Proof. intros [L R]; reflexivity. Qed.

Lemma ropts_pneg : forall G, ropts (pneg G) = map pneg (lopts G).
Proof. intros [L R]; reflexivity. Qed.

Lemma pneg_pneg : forall G, pneg (pneg G) = G.
Proof.
  refine (pgame_forall_ind (fun G => pneg (pneg G) = G) _).
  intros L R IHL IHR.
  apply pgame_eq.
  - rewrite lopts_pneg, ropts_pneg, lopts_PG, map_map.
    rewrite (map_ext_in _ id L), map_id; auto.
    intros a Ha; apply (proj1 (Forall_forall _ L) IHL a Ha).
  - rewrite ropts_pneg, lopts_pneg, ropts_PG, map_map.
    rewrite (map_ext_in _ id R), map_id; auto.
    intros a Ha; apply (proj1 (Forall_forall _ R) IHR a Ha).
Qed.

(** The disjunctive sum: a move is a move in exactly one summand. *)
Fixpoint padd (G : pgame) : pgame -> pgame :=
  match G with
  | PG GL GR =>
    fix padd_r (H : pgame) : pgame :=
      match H with
      | PG HL HR =>
        PG (map (fun g => padd g (PG HL HR)) GL ++ map padd_r HL)
           (map (fun g => padd g (PG HL HR)) GR ++ map padd_r HR)
      end
  end.

Lemma lopts_padd :
  forall G H,
    lopts (padd G H) =
    map (fun g => padd g H) (lopts G) ++ map (fun h => padd G h) (lopts H).
Proof. intros [GL GR] [HL HR]; reflexivity. Qed.

Lemma ropts_padd :
  forall G H,
    ropts (padd G H) =
    map (fun g => padd g H) (ropts G) ++ map (fun h => padd G h) (ropts H).
Proof. intros [GL GR] [HL HR]; reflexivity. Qed.

Definition zero : pgame := PG [] [].

Lemma padd_zero_r : forall G, padd G zero = G.
Proof.
  refine (pgame_forall_ind (fun G => padd G zero = G) _).
  intros L R IHL IHR.
  apply pgame_eq.
  - rewrite lopts_padd, lopts_PG.
    change (lopts zero) with (@nil pgame).
    rewrite app_nil_r.
    rewrite (map_ext_in _ id L), map_id; auto.
    intros a Ha; apply (proj1 (Forall_forall _ L) IHL a Ha).
  - rewrite ropts_padd, ropts_PG.
    change (ropts zero) with (@nil pgame).
    rewrite app_nil_r.
    rewrite (map_ext_in _ id R), map_id; auto.
    intros a Ha; apply (proj1 (Forall_forall _ R) IHR a Ha).
Qed.

Lemma padd_zero_l : forall G, padd zero G = G.
Proof.
  refine (pgame_forall_ind (fun G => padd zero G = G) _).
  intros L R IHL IHR.
  apply pgame_eq.
  - rewrite lopts_padd, lopts_PG.
    change (lopts zero) with (@nil pgame).
    simpl app.
    rewrite (map_ext_in _ id L), map_id; auto.
    intros a Ha; apply (proj1 (Forall_forall _ L) IHL a Ha).
  - rewrite ropts_padd, ropts_PG.
    change (ropts zero) with (@nil pgame).
    simpl app.
    rewrite (map_ext_in _ id R), map_id; auto.
    intros a Ha; apply (proj1 (Forall_forall _ R) IHR a Ha).
Qed.

Lemma pneg_zero : pneg zero = zero.
Proof. reflexivity. Qed.

Lemma pneg_padd_aux :
  forall N G H,
    rank G + rank H <= N -> pneg (padd G H) = padd (pneg G) (pneg H).
Proof.
  induction N as [|N IH]; intros G H HN.
  - pose proof (rank_pos G); pose proof (rank_pos H); lia.
  - apply pgame_eq.
    + rewrite lopts_pneg, ropts_padd, lopts_padd, !lopts_pneg.
      rewrite map_app, !map_map.
      f_equal; apply map_ext_in; intros a Ha.
      * apply IH; pose proof (rank_ropt G a Ha); lia.
      * apply IH; pose proof (rank_ropt H a Ha); lia.
    + rewrite ropts_pneg, lopts_padd, ropts_padd, !ropts_pneg.
      rewrite map_app, !map_map.
      f_equal; apply map_ext_in; intros a Ha.
      * apply IH; pose proof (rank_lopt G a Ha); lia.
      * apply IH; pose proof (rank_lopt H a Ha); lia.
Qed.

Lemma pneg_padd :
  forall G H, pneg (padd G H) = padd (pneg G) (pneg H).
Proof.
  intros G H; apply (pneg_padd_aux (rank G + rank H)); lia.
Qed.

(** * Outcomes of negations and sums *)

(** Negation exchanges winning with losing and moving with waiting. *)
Lemma lwin_pneg :
  forall G t, lwin (pneg G) t = negb (lwin G (negb t)).
Proof.
  refine (pgame_forall_ind
    (fun G => forall t, lwin (pneg G) t = negb (lwin G (negb t))) _).
  intros L R IHL IHR t; destruct t.
  - change (negb true) with false.
    rewrite lwin_true, lopts_pneg, ropts_PG, existsb_map.
    rewrite lwin_false, ropts_PG, negb_forallb.
    apply existsb_ext_in; intros g Hg.
    apply (proj1 (Forall_forall _ R) IHR g Hg false).
  - change (negb false) with true.
    rewrite lwin_false, ropts_pneg, lopts_PG, forallb_map.
    rewrite lwin_true, lopts_PG, negb_existsb.
    apply forallb_ext_in; intros g Hg.
    apply (proj1 (Forall_forall _ L) IHL g Hg true).
Qed.

(** The outcome of a sum is independent of the order of the summands. *)
Lemma lwin_padd_comm :
  forall N G H t,
    rank G + rank H <= N -> lwin (padd G H) t = lwin (padd H G) t.
Proof.
  induction N as [|N IH]; intros G H t HN.
  - pose proof (rank_pos G); pose proof (rank_pos H); lia.
  - destruct t.
    + rewrite !lwin_true, !lopts_padd, !existsb_app, !existsb_map.
      cbv beta.
      assert (E1 : existsb (fun g => lwin (padd g H) false) (lopts G)
                 = existsb (fun g => lwin (padd H g) false) (lopts G)).
      { apply existsb_ext_in; intros g Hg.
        apply IH; pose proof (rank_lopt G g Hg); lia. }
      assert (E2 : existsb (fun h => lwin (padd G h) false) (lopts H)
                 = existsb (fun h => lwin (padd h G) false) (lopts H)).
      { apply existsb_ext_in; intros h Hh.
        apply IH; pose proof (rank_lopt H h Hh); lia. }
      rewrite E1, E2; apply orb_comm.
    + rewrite !lwin_false, !ropts_padd, !forallb_app, !forallb_map.
      cbv beta.
      assert (E1 : forallb (fun g => lwin (padd g H) true) (ropts G)
                 = forallb (fun g => lwin (padd H g) true) (ropts G)).
      { apply forallb_ext_in; intros g Hg.
        apply IH; pose proof (rank_ropt G g Hg); lia. }
      assert (E2 : forallb (fun h => lwin (padd G h) true) (ropts H)
                 = forallb (fun h => lwin (padd h G) true) (ropts H)).
      { apply forallb_ext_in; intros h Hh.
        apply IH; pose proof (rank_ropt H h Hh); lia. }
      rewrite E1, E2; apply andb_comm.
Qed.

(** Exchanging the middle summands of a fourfold sum preserves the outcome. *)
Lemma lwin_padd4 :
  forall N G H K M t,
    rank G + rank H + rank K + rank M <= N ->
    lwin (padd (padd G H) (padd K M)) t = lwin (padd (padd G K) (padd H M)) t.
Proof.
  induction N as [|N IH]; intros G H K M t HN.
  - pose proof (rank_pos G); pose proof (rank_pos H).
    pose proof (rank_pos K); pose proof (rank_pos M); lia.
  - destruct t.
    + rewrite !lwin_true, !lopts_padd, !map_app, !map_map,
              !existsb_app, !existsb_map.
      cbv beta.
      rewrite orb_middle4.
      f_equal; f_equal; apply existsb_ext_in; intros a Ha.
      * apply IH; pose proof (rank_lopt G a Ha); lia.
      * apply IH; pose proof (rank_lopt K a Ha); lia.
      * apply IH; pose proof (rank_lopt H a Ha); lia.
      * apply IH; pose proof (rank_lopt M a Ha); lia.
    + rewrite !lwin_false, !ropts_padd, !map_app, !map_map,
              !forallb_app, !forallb_map.
      cbv beta.
      rewrite andb_middle4.
      f_equal; f_equal; apply forallb_ext_in; intros a Ha.
      * apply IH; pose proof (rank_ropt G a Ha); lia.
      * apply IH; pose proof (rank_ropt K a Ha); lia.
      * apply IH; pose proof (rank_ropt H a Ha); lia.
      * apply IH; pose proof (rank_ropt M a Ha); lia.
Qed.

(** A sum of two second-player wins for Left is a second-player win for Left. *)
Lemma lwin_padd_second :
  forall N A B,
    rank A + rank B <= N ->
    lwin A false = true -> lwin B false = true ->
    lwin (padd A B) false = true.
Proof.
  induction N as [|N IH]; intros A B HN HA HB.
  - pose proof (rank_pos A); pose proof (rank_pos B); lia.
  - rewrite lwin_false, ropts_padd, forallb_app, !forallb_map.
    cbv beta.
    apply andb_true_iff; split.
    + apply forallb_forall; intros a Ha.
      rewrite lwin_false in HA.
      pose proof (proj1 (forallb_forall _ (ropts A)) HA a Ha) as Hat.
      cbv beta in Hat.
      rewrite lwin_true in Hat.
      apply existsb_exists in Hat.
      destruct Hat as [al [Hal Halw]].
      rewrite lwin_true, lopts_padd.
      apply existsb_exists.
      exists (padd al B); split.
      * apply in_or_app; left; apply in_map_iff; eexists; split; [reflexivity | auto].
      * apply IH; auto.
        pose proof (rank_ropt A a Ha); pose proof (rank_lopt a al Hal); lia.
    + apply forallb_forall; intros b Hb.
      rewrite lwin_false in HB.
      pose proof (proj1 (forallb_forall _ (ropts B)) HB b Hb) as Hbt.
      cbv beta in Hbt.
      rewrite lwin_true in Hbt.
      apply existsb_exists in Hbt.
      destruct Hbt as [bl [Hbl Hblw]].
      rewrite lwin_true, lopts_padd.
      apply existsb_exists.
      exists (padd A bl); split.
      * apply in_or_app; right; apply in_map_iff; eexists; split; [reflexivity | auto].
      * apply IH; auto.
        pose proof (rank_ropt B b Hb); pose proof (rank_lopt b bl Hbl); lia.
Qed.

(** The second player wins a game plus its negation, by mirroring. *)
Lemma lwin_padd_pneg :
  forall N G, rank G <= N -> lwin (padd G (pneg G)) false = true.
Proof.
  induction N as [|N IH]; intros G HN.
  - pose proof (rank_pos G); lia.
  - rewrite lwin_false, ropts_padd, ropts_pneg, forallb_app, !forallb_map.
    cbv beta.
    apply andb_true_iff; split.
    + apply forallb_forall; intros g Hg.
      rewrite lwin_true, lopts_padd, lopts_pneg.
      apply existsb_exists.
      exists (padd g (pneg g)); split.
      * apply in_or_app; right.
        rewrite map_map; apply in_map_iff; eexists; split; [reflexivity | auto].
      * apply IH; pose proof (rank_ropt G g Hg); lia.
    + apply forallb_forall; intros g Hg.
      rewrite lwin_true, lopts_padd.
      apply existsb_exists.
      exists (padd g (pneg g)); split.
      * apply in_or_app; left; apply in_map_iff; eexists; split; [reflexivity | auto].
      * apply IH; pose proof (rank_lopt G g Hg); lia.
Qed.

Lemma lwin_padd_pneg_first :
  forall G, lwin (padd G (pneg G)) true = false.
Proof.
  intros G.
  assert (Heq : pneg (padd G (pneg G)) = padd (pneg G) G).
  { rewrite pneg_padd, pneg_pneg; reflexivity. }
  assert (Hs : lwin (padd (pneg G) G) false = true).
  { rewrite (lwin_padd_comm (rank (pneg G) + rank G) (pneg G) G false) by lia.
    apply (lwin_padd_pneg (rank G)); lia. }
  rewrite <- Heq in Hs.
  rewrite lwin_pneg in Hs.
  change (negb false) with true in Hs.
  apply negb_true_iff in Hs.
  exact Hs.
Qed.

(** * Conway's order *)

(** [gleb fuel G H] decides [G <= H] to comparison depth [fuel]. *)
Fixpoint gleb (fuel : nat) (G H : pgame) : bool :=
  match fuel with
  | 0 => false
  | S f =>
    (forallb (fun h => negb (gleb f h G)) (ropts H) &&
     forallb (fun g => negb (gleb f H g)) (lopts G))%bool
  end.

Lemma gleb_S :
  forall f G H,
    gleb (S f) G H =
    (forallb (fun h => negb (gleb f h G)) (ropts H) &&
     forallb (fun g => negb (gleb f H g)) (lopts G))%bool.
Proof. reflexivity. Qed.

Lemma gleb_stable :
  forall N G H f1 f2,
    rank G + rank H <= N -> rank G + rank H <= f1 -> rank G + rank H <= f2 ->
    gleb f1 G H = gleb f2 G H.
Proof.
  induction N as [|N IH]; intros G H f1 f2 HN Hf1 Hf2.
  - pose proof (rank_pos G); pose proof (rank_pos H); lia.
  - pose proof (rank_pos G) as HG; pose proof (rank_pos H) as HH.
    destruct f1 as [|f1]; [lia|].
    destruct f2 as [|f2]; [lia|].
    rewrite !gleb_S.
    f_equal.
    + apply forallb_ext_in; intros h Hh; f_equal.
      apply (IH h G); pose proof (rank_ropt H h Hh); lia.
    + apply forallb_ext_in; intros g Hg; f_equal.
      apply (IH H g); pose proof (rank_lopt G g Hg); lia.
Qed.

(** The fuel-free order. *)
Definition gle (G H : pgame) : bool := gleb (rank G + rank H) G H.

Lemma gleb_gle :
  forall f G H, rank G + rank H <= f -> gleb f G H = gle G H.
Proof.
  intros f G H Hf; unfold gle.
  apply (gleb_stable (rank G + rank H)); lia.
Qed.

(** The fixpoint equation defining the order. *)
Lemma gle_unfold :
  forall G H,
    gle G H =
    (forallb (fun h => negb (gle h G)) (ropts H) &&
     forallb (fun g => negb (gle H g)) (lopts G))%bool.
Proof.
  intros G H; unfold gle.
  pose proof (rank_pos G) as HG; pose proof (rank_pos H) as HH.
  destruct (rank G + rank H) as [|f] eqn:E; [lia|].
  rewrite gleb_S.
  f_equal.
  - apply forallb_ext_in; intros h Hh; f_equal.
    apply gleb_gle; pose proof (rank_ropt H h Hh); lia.
  - apply forallb_ext_in; intros g Hg; f_equal.
    apply gleb_gle; pose proof (rank_lopt G g Hg); lia.
Qed.

Lemma gle_true_iff :
  forall G H,
    gle G H = true <->
    (forall h, In h (ropts H) -> gle h G = false) /\
    (forall g, In g (lopts G) -> gle H g = false).
Proof.
  intros G H; rewrite gle_unfold, andb_true_iff.
  rewrite !forallb_forall.
  split; intros [H1 H2]; split.
  - intros h Hh; apply negb_true_iff; auto.
  - intros g Hg; apply negb_true_iff; auto.
  - intros h Hh; apply negb_true_iff; auto.
  - intros g Hg; apply negb_true_iff; auto.
Qed.

Lemma gle_false_iff :
  forall G H,
    gle G H = false <->
    (exists h, In h (ropts H) /\ gle h G = true) \/
    (exists g, In g (lopts G) /\ gle H g = true).
Proof.
  intros G H; split.
  - intros Hf.
    rewrite gle_unfold in Hf.
    apply andb_false_iff in Hf.
    destruct Hf as [Hf | Hf].
    + left.
      assert (Hex : existsb (fun h => negb (negb (gle h G))) (ropts H) = true).
      { rewrite <- negb_forallb, Hf; reflexivity. }
      apply existsb_exists in Hex.
      destruct Hex as [h [Hh Hhw]].
      cbv beta in Hhw; rewrite negb_involutive in Hhw.
      exists h; auto.
    + right.
      assert (Hex : existsb (fun g => negb (negb (gle H g))) (lopts G) = true).
      { rewrite <- negb_forallb, Hf; reflexivity. }
      apply existsb_exists in Hex.
      destruct Hex as [g [Hg Hgw]].
      cbv beta in Hgw; rewrite negb_involutive in Hgw.
      exists g; auto.
  - intros Hex.
    destruct (gle G H) eqn:E; auto.
    apply (proj1 (gle_true_iff G H)) in E.
    destruct E as [E1 E2].
    destruct Hex as [[h [Hh Hhw]] | [g [Hg Hgw]]].
    + rewrite (E1 h Hh) in Hhw; discriminate.
    + rewrite (E2 g Hg) in Hgw; discriminate.
Qed.

(** Reflexivity of the order. *)
Lemma gle_refl : forall G, gle G G = true.
Proof.
  assert (Haux : forall N G, rank G <= N -> gle G G = true).
  { induction N as [|N IH]; intros G HN.
    - pose proof (rank_pos G); lia.
    - apply gle_true_iff; split.
      + intros h Hh.
        apply gle_false_iff; left.
        exists h; split; auto.
        apply IH; pose proof (rank_ropt G h Hh); lia.
      + intros g Hg.
        apply gle_false_iff; right.
        exists g; split; auto.
        apply IH; pose proof (rank_lopt G g Hg); lia. }
  intros G; apply (Haux (rank G)); lia.
Qed.

Lemma gle_lopt : forall G g, In g (lopts G) -> gle G g = false.
Proof.
  intros G g Hg; apply gle_false_iff; right.
  exists g; split; auto; apply gle_refl.
Qed.

Lemma gle_ropt : forall G g, In g (ropts G) -> gle g G = false.
Proof.
  intros G g Hg; apply gle_false_iff; left.
  exists g; split; auto; apply gle_refl.
Qed.

Lemma gle_trans_aux :
  forall N G H K,
    rank G + rank H + rank K <= N ->
    gle G H = true -> gle H K = true -> gle G K = true.
Proof.
  induction N as [|N IH]; intros G H K HN Hgh Hhk.
  - pose proof (rank_pos G); pose proof (rank_pos H);
      pose proof (rank_pos K); lia.
  - apply gle_true_iff; split.
    + intros r Hr.
      destruct (gle r G) eqn:Er; auto.
      exfalso.
      assert (Hrh : gle r H = true).
      { apply (IH r G H); auto; pose proof (rank_ropt K r Hr); lia. }
      pose proof (proj1 (proj1 (gle_true_iff H K) Hhk) r Hr) as Hno.
      congruence.
    + intros l Hl.
      destruct (gle K l) eqn:El; auto.
      exfalso.
      assert (Hhl : gle H l = true).
      { apply (IH H K l); auto; pose proof (rank_lopt G l Hl); lia. }
      pose proof (proj2 (proj1 (gle_true_iff G H) Hgh) l Hl) as Hno.
      congruence.
Qed.

Theorem gle_trans :
  forall G H K, gle G H = true -> gle H K = true -> gle G K = true.
Proof.
  intros G H K; apply (gle_trans_aux (rank G + rank H + rank K)); lia.
Qed.

(** * Equivalence and confusion *)

Definition gequiv (G H : pgame) : bool := (gle G H && gle H G)%bool.

Definition gfuzzy (G H : pgame) : bool := (negb (gle G H) && negb (gle H G))%bool.

Lemma gequiv_true_iff :
  forall G H, gequiv G H = true <-> gle G H = true /\ gle H G = true.
Proof. intros G H; apply andb_true_iff. Qed.

Lemma gequiv_refl : forall G, gequiv G G = true.
Proof. intros G; apply gequiv_true_iff; split; apply gle_refl. Qed.

Lemma gequiv_sym : forall G H, gequiv G H = true -> gequiv H G = true.
Proof.
  intros G H Hgh; apply gequiv_true_iff in Hgh.
  apply gequiv_true_iff; tauto.
Qed.

Lemma gequiv_trans :
  forall G H K, gequiv G H = true -> gequiv H K = true -> gequiv G K = true.
Proof.
  intros G H K Hgh Hhk.
  apply gequiv_true_iff in Hgh; apply gequiv_true_iff in Hhk.
  apply gequiv_true_iff; split.
  - apply (gle_trans G H K); tauto.
  - apply (gle_trans K H G); tauto.
Qed.

Lemma gle_gequiv_l :
  forall G G' H, gequiv G G' = true -> gle G H = true -> gle G' H = true.
Proof.
  intros G G' H He Hgh; apply gequiv_true_iff in He.
  apply (gle_trans G' G H); tauto.
Qed.

Lemma gle_gequiv_r :
  forall G H H', gequiv H H' = true -> gle G H = true -> gle G H' = true.
Proof.
  intros G H H' He Hgh; apply gequiv_true_iff in He.
  apply (gle_trans G H H'); tauto.
Qed.

(** Games whose options agree up to equivalence are equivalent. *)
Lemma gle_of_opts :
  forall X Y,
    (forall y, In y (ropts Y) -> exists x, In x (ropts X) /\ gequiv x y = true) ->
    (forall x, In x (lopts X) -> exists y, In y (lopts Y) /\ gequiv x y = true) ->
    gle X Y = true.
Proof.
  intros X Y HR HL; apply gle_true_iff; split.
  - intros y Hy.
    destruct (gle y X) eqn:Ey; auto.
    exfalso.
    destruct (HR y Hy) as [x [Hx Hxy]].
    apply gequiv_true_iff in Hxy.
    assert (Hxx : gle x X = true) by (apply (gle_trans x y X); tauto).
    rewrite (gle_ropt X x Hx) in Hxx; discriminate.
  - intros x Hx.
    destruct (gle Y x) eqn:Ex; auto.
    exfalso.
    destruct (HL x Hx) as [y [Hy Hxy]].
    apply gequiv_true_iff in Hxy.
    assert (Hyy : gle Y y = true) by (apply (gle_trans Y x y); tauto).
    rewrite (gle_lopt Y y Hy) in Hyy; discriminate.
Qed.

(** Both option lists matched up to equivalence, in both directions. *)
Definition opts_equiv (l1 l2 : list pgame) : Prop :=
  (forall x, In x l1 -> exists y, In y l2 /\ gequiv x y = true) /\
  (forall y, In y l2 -> exists x, In x l1 /\ gequiv x y = true).

Theorem gequiv_of_opts :
  forall X Y,
    opts_equiv (lopts X) (lopts Y) ->
    opts_equiv (ropts X) (ropts Y) ->
    gequiv X Y = true.
Proof.
  intros X Y [HL1 HL2] [HR1 HR2]; apply gequiv_true_iff; split.
  - apply gle_of_opts; auto.
  - apply gle_of_opts.
    + intros x Hx; destruct (HR1 x Hx) as [y [Hy Hxy]].
      exists y; split; auto; apply gequiv_sym; auto.
    + intros y Hy; destruct (HL2 y Hy) as [x [Hx Hxy]].
      exists x; split; auto; apply gequiv_sym; auto.
Qed.

(** * The difference game *)

(** [G <= H] iff Left wins [H] plus the negation of [G] moving second. *)
Theorem gle_diff :
  forall G H, gle G H = true <-> lwin (padd H (pneg G)) false = true.
Proof.
  assert (Haux : forall N G H, rank G + rank H <= N ->
            (gle G H = true <-> lwin (padd H (pneg G)) false = true)).
  { induction N as [|N IH]; intros G H HN.
    - pose proof (rank_pos G); pose proof (rank_pos H); lia.
    - assert (Hopt : forall X Y,
        lwin (padd X (pneg Y)) true = negb (lwin (padd Y (pneg X)) false)).
      { intros X Y.
        assert (Heq : pneg (padd X (pneg Y)) = padd (pneg X) Y).
        { rewrite pneg_padd, pneg_pneg; reflexivity. }
        assert (Hl : lwin (pneg (padd X (pneg Y))) false
                   = negb (lwin (padd X (pneg Y)) true)).
        { rewrite lwin_pneg; change (negb false) with true; reflexivity. }
        rewrite Heq in Hl.
        rewrite (lwin_padd_comm (rank (pneg X) + rank Y) (pneg X) Y false)
          in Hl by lia.
        rewrite Hl, negb_involutive; reflexivity. }
      rewrite lwin_false, ropts_padd, ropts_pneg, forallb_app, !forallb_map.
      cbv beta.
      rewrite gle_true_iff.
      split.
      + intros [H1 H2].
        apply andb_true_iff; split.
        * apply forallb_forall; intros h Hh.
          rewrite Hopt.
          apply negb_true_iff.
          destruct (lwin (padd G (pneg h)) false) eqn:Eh; auto.
          exfalso.
          assert (Hle : gle h G = true).
          { apply (IH h G); auto; pose proof (rank_ropt H h Hh); lia. }
          rewrite (H1 h Hh) in Hle; discriminate.
        * apply forallb_forall; intros g Hg.
          rewrite Hopt.
          apply negb_true_iff.
          destruct (lwin (padd g (pneg H)) false) eqn:Eg; auto.
          exfalso.
          assert (Hle : gle H g = true).
          { apply (IH H g); auto; pose proof (rank_lopt G g Hg); lia. }
          rewrite (H2 g Hg) in Hle; discriminate.
      + intros Hw; apply andb_true_iff in Hw; destruct Hw as [Hw1 Hw2]; split.
        * intros h Hh.
          destruct (gle h G) eqn:Eh; auto.
          exfalso.
          assert (Hlw : lwin (padd G (pneg h)) false = true).
          { apply (IH h G); auto; pose proof (rank_ropt H h Hh); lia. }
          pose proof (proj1 (forallb_forall _ (ropts H)) Hw1 h Hh) as Hcon.
          cbv beta in Hcon.
          rewrite Hopt, Hlw in Hcon; discriminate.
        * intros g Hg.
          destruct (gle H g) eqn:Eg; auto.
          exfalso.
          assert (Hlw : lwin (padd g (pneg H)) false = true).
          { apply (IH H g); auto; pose proof (rank_lopt G g Hg); lia. }
          pose proof (proj1 (forallb_forall _ (lopts G)) Hw2 g Hg) as Hcon.
          cbv beta in Hcon.
          rewrite Hopt, Hlw in Hcon; discriminate. }
  intros G H; apply (Haux (rank G + rank H)); lia.
Qed.

(** Comparison with [zero] is exactly the outcome. *)
Theorem gle_zero_l : forall G, gle zero G = true <-> lwin G false = true.
Proof.
  intros G; rewrite gle_diff, pneg_zero, padd_zero_r; apply iff_refl.
Qed.

Theorem gle_zero_r : forall G, gle G zero = true <-> lwin G true = false.
Proof.
  intros G; rewrite gle_diff, padd_zero_l, lwin_pneg; simpl negb.
  rewrite negb_true_iff; apply iff_refl.
Qed.

(** * The group structure *)

Theorem padd_inv : forall G, gequiv (padd G (pneg G)) zero = true.
Proof.
  intros G; apply gequiv_true_iff; split.
  - apply gle_zero_r, lwin_padd_pneg_first.
  - apply gle_zero_l, (lwin_padd_pneg (rank G)); lia.
Qed.

(** Addition is monotone in the order. *)
Theorem gle_padd_r :
  forall G H K, gle G H = true -> gle (padd G K) (padd H K) = true.
Proof.
  intros G H K Hgh.
  apply gle_diff.
  rewrite pneg_padd.
  rewrite (lwin_padd4 (rank H + rank K + rank (pneg G) + rank (pneg K))
             H K (pneg G) (pneg K) false) by lia.
  apply (lwin_padd_second (rank (padd H (pneg G)) + rank (padd K (pneg K)))); auto.
  - apply gle_diff; auto.
  - apply (lwin_padd_pneg (rank K)); lia.
Qed.

Theorem gle_padd_l :
  forall G H K, gle G H = true -> gle (padd K G) (padd K H) = true.
Proof.
  intros G H K Hgh.
  apply gle_diff.
  rewrite pneg_padd.
  rewrite (lwin_padd4 (rank K + rank H + rank (pneg K) + rank (pneg G))
             K H (pneg K) (pneg G) false) by lia.
  apply (lwin_padd_second (rank (padd K (pneg K)) + rank (padd H (pneg G)))).
  - lia.
  - apply (lwin_padd_pneg (rank K)); lia.
  - apply gle_diff; auto.
Qed.

Theorem gequiv_padd_r :
  forall G H K, gequiv G H = true -> gequiv (padd G K) (padd H K) = true.
Proof.
  intros G H K He; apply gequiv_true_iff in He.
  apply gequiv_true_iff; split; apply gle_padd_r; tauto.
Qed.

Theorem gequiv_padd_l :
  forall G H K, gequiv G H = true -> gequiv (padd K G) (padd K H) = true.
Proof.
  intros G H K He; apply gequiv_true_iff in He.
  apply gequiv_true_iff; split; apply gle_padd_l; tauto.
Qed.

Theorem padd_comm : forall G H, gequiv (padd G H) (padd H G) = true.
Proof.
  assert (Haux : forall N G H,
            rank G + rank H <= N -> gequiv (padd G H) (padd H G) = true).
  { induction N as [|N IH]; intros G H HN.
    - pose proof (rank_pos G); pose proof (rank_pos H); lia.
    - apply gequiv_of_opts.
      + rewrite !lopts_padd; split.
        * intros x Hx.
          apply in_app_or in Hx; destruct Hx as [Hx | Hx];
            apply in_map_iff in Hx; destruct Hx as [a [<- Ha]].
          -- exists (padd H a); split.
             ++ apply in_or_app; right; apply in_map_iff; eexists; split; [reflexivity | auto].
             ++ apply IH; pose proof (rank_lopt G a Ha); lia.
          -- exists (padd a G); split.
             ++ apply in_or_app; left; apply in_map_iff; eexists; split; [reflexivity | auto].
             ++ apply IH; pose proof (rank_lopt H a Ha); lia.
        * intros y Hy.
          apply in_app_or in Hy; destruct Hy as [Hy | Hy];
            apply in_map_iff in Hy; destruct Hy as [a [<- Ha]].
          -- exists (padd G a); split.
             ++ apply in_or_app; right; apply in_map_iff; eexists; split; [reflexivity | auto].
             ++ apply IH; pose proof (rank_lopt H a Ha); lia.
          -- exists (padd a H); split.
             ++ apply in_or_app; left; apply in_map_iff; eexists; split; [reflexivity | auto].
             ++ apply IH; pose proof (rank_lopt G a Ha); lia.
      + rewrite !ropts_padd; split.
        * intros x Hx.
          apply in_app_or in Hx; destruct Hx as [Hx | Hx];
            apply in_map_iff in Hx; destruct Hx as [a [<- Ha]].
          -- exists (padd H a); split.
             ++ apply in_or_app; right; apply in_map_iff; eexists; split; [reflexivity | auto].
             ++ apply IH; pose proof (rank_ropt G a Ha); lia.
          -- exists (padd a G); split.
             ++ apply in_or_app; left; apply in_map_iff; eexists; split; [reflexivity | auto].
             ++ apply IH; pose proof (rank_ropt H a Ha); lia.
        * intros y Hy.
          apply in_app_or in Hy; destruct Hy as [Hy | Hy];
            apply in_map_iff in Hy; destruct Hy as [a [<- Ha]].
          -- exists (padd G a); split.
             ++ apply in_or_app; right; apply in_map_iff; eexists; split; [reflexivity | auto].
             ++ apply IH; pose proof (rank_ropt H a Ha); lia.
          -- exists (padd a H); split.
             ++ apply in_or_app; left; apply in_map_iff; eexists; split; [reflexivity | auto].
             ++ apply IH; pose proof (rank_ropt G a Ha); lia. }
  intros G H; apply (Haux (rank G + rank H)); lia.
Qed.

Theorem padd_assoc :
  forall G H K, gequiv (padd (padd G H) K) (padd G (padd H K)) = true.
Proof.
  assert (Haux : forall N G H K,
            rank G + rank H + rank K <= N ->
            gequiv (padd (padd G H) K) (padd G (padd H K)) = true).
  { induction N as [|N IH]; intros G H K HN.
    - pose proof (rank_pos G); pose proof (rank_pos H);
        pose proof (rank_pos K); lia.
    - apply gequiv_of_opts.
      + rewrite !lopts_padd, !map_app, !map_map; split.
        * intros x Hx.
          apply in_app_or in Hx; destruct Hx as [Hx | Hx].
          -- apply in_app_or in Hx; destruct Hx as [Hx | Hx];
               apply in_map_iff in Hx; destruct Hx as [a [<- Ha]].
             ++ exists (padd a (padd H K)); split.
                ** apply in_or_app; left; apply in_map_iff; eexists; split; [reflexivity | auto].
                ** apply IH; pose proof (rank_lopt G a Ha); lia.
             ++ exists (padd G (padd a K)); split.
                ** apply in_or_app; right; apply in_or_app; left;
                     apply in_map_iff; eexists; split; [reflexivity | auto].
                ** apply IH; pose proof (rank_lopt H a Ha); lia.
          -- apply in_map_iff in Hx; destruct Hx as [a [<- Ha]].
             exists (padd G (padd H a)); split.
             ++ apply in_or_app; right; apply in_or_app; right;
                  apply in_map_iff; eexists; split; [reflexivity | auto].
             ++ apply IH; pose proof (rank_lopt K a Ha); lia.
        * intros y Hy.
          apply in_app_or in Hy; destruct Hy as [Hy | Hy].
          -- apply in_map_iff in Hy; destruct Hy as [a [<- Ha]].
             exists (padd (padd a H) K); split.
             ++ apply in_or_app; left; apply in_or_app; left;
                  apply in_map_iff; eexists; split; [reflexivity | auto].
             ++ apply IH; pose proof (rank_lopt G a Ha); lia.
          -- apply in_app_or in Hy; destruct Hy as [Hy | Hy];
               apply in_map_iff in Hy; destruct Hy as [a [<- Ha]].
             ++ exists (padd (padd G a) K); split.
                ** apply in_or_app; left; apply in_or_app; right;
                     apply in_map_iff; eexists; split; [reflexivity | auto].
                ** apply IH; pose proof (rank_lopt H a Ha); lia.
             ++ exists (padd (padd G H) a); split.
                ** apply in_or_app; right; apply in_map_iff; eexists; split; [reflexivity | auto].
                ** apply IH; pose proof (rank_lopt K a Ha); lia.
      + rewrite !ropts_padd, !map_app, !map_map; split.
        * intros x Hx.
          apply in_app_or in Hx; destruct Hx as [Hx | Hx].
          -- apply in_app_or in Hx; destruct Hx as [Hx | Hx];
               apply in_map_iff in Hx; destruct Hx as [a [<- Ha]].
             ++ exists (padd a (padd H K)); split.
                ** apply in_or_app; left; apply in_map_iff; eexists; split; [reflexivity | auto].
                ** apply IH; pose proof (rank_ropt G a Ha); lia.
             ++ exists (padd G (padd a K)); split.
                ** apply in_or_app; right; apply in_or_app; left;
                     apply in_map_iff; eexists; split; [reflexivity | auto].
                ** apply IH; pose proof (rank_ropt H a Ha); lia.
          -- apply in_map_iff in Hx; destruct Hx as [a [<- Ha]].
             exists (padd G (padd H a)); split.
             ++ apply in_or_app; right; apply in_or_app; right;
                  apply in_map_iff; eexists; split; [reflexivity | auto].
             ++ apply IH; pose proof (rank_ropt K a Ha); lia.
        * intros y Hy.
          apply in_app_or in Hy; destruct Hy as [Hy | Hy].
          -- apply in_map_iff in Hy; destruct Hy as [a [<- Ha]].
             exists (padd (padd a H) K); split.
             ++ apply in_or_app; left; apply in_or_app; left;
                  apply in_map_iff; eexists; split; [reflexivity | auto].
             ++ apply IH; pose proof (rank_ropt G a Ha); lia.
          -- apply in_app_or in Hy; destruct Hy as [Hy | Hy];
               apply in_map_iff in Hy; destruct Hy as [a [<- Ha]].
             ++ exists (padd (padd G a) K); split.
                ** apply in_or_app; left; apply in_or_app; right;
                     apply in_map_iff; eexists; split; [reflexivity | auto].
                ** apply IH; pose proof (rank_ropt H a Ha); lia.
             ++ exists (padd (padd G H) a); split.
                ** apply in_or_app; right; apply in_map_iff; eexists; split; [reflexivity | auto].
                ** apply IH; pose proof (rank_ropt K a Ha); lia. }
  intros G H K; apply (Haux (rank G + rank H + rank K)); lia.
Qed.

(** Adding a game and then its negation returns to where one started. *)
Lemma padd_pneg_cancel :
  forall G K, gequiv (padd (padd G K) (pneg K)) G = true.
Proof.
  intros G K.
  apply (gequiv_trans _ (padd G (padd K (pneg K)))).
  - apply padd_assoc.
  - rewrite <- (padd_zero_r G) at 2.
    apply gequiv_padd_l, padd_inv.
Qed.

Theorem gle_padd_cancel :
  forall G H K, gle (padd G K) (padd H K) = true -> gle G H = true.
Proof.
  intros G H K Hle.
  assert (Hstep : gle (padd (padd G K) (pneg K)) (padd (padd H K) (pneg K)) = true)
    by (apply gle_padd_r; auto).
  apply (gle_gequiv_l (padd (padd G K) (pneg K))); [apply padd_pneg_cancel|].
  apply (gle_gequiv_r _ (padd (padd H K) (pneg K))); [apply padd_pneg_cancel|].
  exact Hstep.
Qed.

Theorem gequiv_padd_cancel :
  forall G H K, gequiv (padd G K) (padd H K) = true -> gequiv G H = true.
Proof.
  intros G H K He; apply gequiv_true_iff in He.
  apply gequiv_true_iff; split; apply (gle_padd_cancel _ _ K); tauto.
Qed.

Lemma bool_iff_eq : forall a b : bool, (a = true <-> b = true) -> a = b.
Proof.
  intros [] [] [H1 H2]; auto.
  symmetry; apply H1; reflexivity.
Qed.

(** * The strict order *)

Definition glt (G H : pgame) : Prop := gle G H = true /\ gle H G = false.

Lemma glt_irrefl : forall G, ~ glt G G.
Proof. intros G [_ H2]; rewrite gle_refl in H2; discriminate. Qed.

Lemma glt_trans : forall G H K, glt G H -> glt H K -> glt G K.
Proof.
  intros G H K [H1 H2] [H3 H4]; split.
  - apply (gle_trans G H K); auto.
  - destruct (gle K G) eqn:E; auto.
    exfalso.
    assert (gle K H = true) by (apply (gle_trans K G H); auto).
    congruence.
Qed.

Lemma glt_gequiv_l :
  forall G G' H, gequiv G G' = true -> glt G H -> glt G' H.
Proof.
  intros G G' H He [H1 H2]; split.
  - apply (gle_gequiv_l G); auto.
  - destruct (gle H G') eqn:E; auto.
    exfalso.
    assert (gle H G = true).
    { apply (gle_gequiv_r H G'); auto; apply gequiv_sym; auto. }
    congruence.
Qed.

Lemma glt_gequiv_r :
  forall G H H', gequiv H H' = true -> glt G H -> glt G H'.
Proof.
  intros G H H' He [H1 H2]; split.
  - apply (gle_gequiv_r G H); auto.
  - destruct (gle H' G) eqn:E; auto.
    exfalso.
    assert (gle H G = true).
    { apply (gle_gequiv_l H'); auto; apply gequiv_sym; auto. }
    congruence.
Qed.

Lemma glt_padd_r : forall G H K, glt G H -> glt (padd G K) (padd H K).
Proof.
  intros G H K [Hle Hnle]; split.
  - apply gle_padd_r; auto.
  - destruct (gle (padd H K) (padd G K)) eqn:E; auto.
    exfalso.
    apply gle_padd_cancel in E; congruence.
Qed.

Lemma glt_padd_l : forall G H K, glt G H -> glt (padd K G) (padd K H).
Proof.
  intros G H K Hlt.
  apply (glt_gequiv_l (padd G K)); [apply padd_comm|].
  apply (glt_gequiv_r _ (padd H K)); [apply padd_comm|].
  apply glt_padd_r; auto.
Qed.

(** A positive game strictly increases every game it is added to. *)
Lemma glt_padd_pos : forall G H, glt zero H -> glt G (padd G H).
Proof.
  intros G H Hpos.
  pose proof (glt_padd_l zero H G Hpos) as Hstep.
  rewrite padd_zero_r in Hstep.
  exact Hstep.
Qed.

Lemma glt_zero_padd :
  forall G H, glt zero G -> glt zero H -> glt zero (padd G H).
Proof.
  intros G H Hg Hh.
  apply (glt_trans zero G (padd G H)); auto.
  apply glt_padd_pos; auto.
Qed.

(** Negation reverses the order. *)
Lemma gle_pneg : forall G H, gle (pneg H) (pneg G) = gle G H.
Proof.
  intros G H; apply bool_iff_eq; split.
  - intros Hle.
    apply gle_diff in Hle.
    rewrite pneg_pneg in Hle.
    apply gle_diff.
    rewrite (lwin_padd_comm (rank H + rank (pneg G)) H (pneg G) false) by lia.
    exact Hle.
  - intros Hle.
    apply gle_diff in Hle.
    apply gle_diff.
    rewrite pneg_pneg.
    rewrite (lwin_padd_comm (rank (pneg G) + rank H) (pneg G) H false) by lia.
    exact Hle.
Qed.

Lemma gequiv_pneg :
  forall G H, gequiv G H = true -> gequiv (pneg G) (pneg H) = true.
Proof.
  intros G H He; apply gequiv_true_iff in He; destruct He as [H1 H2].
  apply gequiv_true_iff; split; rewrite gle_pneg; auto.
Qed.

(** * Simplification *)

(** All but a maximal left option may be deleted; dually for Right. *)
Lemma collapse_lopts :
  forall G x0,
    In x0 (lopts G) ->
    (forall x, In x (lopts G) -> gle x x0 = true) ->
    gequiv G (PG [x0] (ropts G)) = true.
Proof.
  intros G x0 Hin Hmax.
  set (H := PG [x0] (ropts G)).
  apply gequiv_true_iff; split.
  - apply gle_true_iff; split.
    + intros r Hr.
      change (ropts H) with (ropts G) in Hr.
      apply gle_ropt; auto.
    + intros l Hl.
      destruct (gle H l) eqn:E; auto.
      exfalso.
      assert (Hx : gle H x0 = true) by (apply (gle_trans H l x0); auto).
      rewrite (gle_lopt H x0) in Hx; [discriminate | left; auto].
  - apply gle_of_opts.
    + intros y Hy; exists y; split; [exact Hy | apply gequiv_refl].
    + intros x Hx.
      change (lopts H) with [x0] in Hx.
      destruct Hx as [<- | []].
      exists x0; split; [exact Hin | apply gequiv_refl].
Qed.

Lemma collapse_ropts :
  forall G y0,
    In y0 (ropts G) ->
    (forall y, In y (ropts G) -> gle y0 y = true) ->
    gequiv G (PG (lopts G) [y0]) = true.
Proof.
  intros G y0 Hin Hmin.
  set (H := PG (lopts G) [y0]).
  apply gequiv_true_iff; split.
  - apply gle_of_opts.
    + intros y Hy.
      change (ropts H) with [y0] in Hy.
      destruct Hy as [<- | []].
      exists y0; split; [exact Hin | apply gequiv_refl].
    + intros x Hx; exists x; split; [exact Hx | apply gequiv_refl].
  - apply gle_true_iff; split.
    + intros r Hr.
      destruct (gle r H) eqn:E; auto.
      exfalso.
      assert (Hy : gle y0 H = true) by (apply (gle_trans y0 r H); auto).
      rewrite (gle_ropt H y0) in Hy; [discriminate | left; auto].
    + intros l Hl.
      change (lopts H) with (lopts G) in Hl.
      apply gle_lopt; auto.
Qed.

(** A left option another left option dominates may be deleted outright. *)
Theorem gequiv_dominated_l :
  forall L R x y,
    In y L -> gle x y = true ->
    gequiv (PG (x :: L) R) (PG L R) = true.
Proof.
  intros L R x y Hy Hxy.
  apply gequiv_true_iff; split.
  - apply gle_true_iff; split.
    + intros r Hr.
      change (ropts (PG L R)) with R in Hr.
      apply gle_ropt; auto.
    + intros l Hl.
      change (lopts (PG (x :: L) R)) with (x :: L) in Hl.
      destruct Hl as [<- | Hl].
      * destruct (gle (PG L R) x) eqn:E; auto.
        exfalso.
        assert (Hbad : gle (PG L R) y = true)
          by (apply (gle_trans (PG L R) x y); auto).
        rewrite (gle_lopt (PG L R) y) in Hbad; [discriminate | exact Hy].
      * apply gle_lopt; exact Hl.
  - apply gle_of_opts.
    + intros r Hr; exists r; split; [exact Hr | apply gequiv_refl].
    + intros l Hl.
      exists l; split; [right; exact Hl | apply gequiv_refl].
Qed.

Theorem gequiv_dominated_r :
  forall L R x y,
    In x R -> gle x y = true ->
    gequiv (PG L (y :: R)) (PG L R) = true.
Proof.
  intros L R x y Hx Hxy.
  apply gequiv_true_iff; split.
  - apply gle_of_opts.
    + intros r Hr; exists r; split; [right; exact Hr | apply gequiv_refl].
    + intros l Hl; exists l; split; [exact Hl | apply gequiv_refl].
  - apply gle_true_iff; split.
    + intros r Hr.
      change (ropts (PG L (y :: R))) with (y :: R) in Hr.
      destruct Hr as [<- | Hr].
      * destruct (gle y (PG L R)) eqn:E; auto.
        exfalso.
        assert (Hbad : gle x (PG L R) = true)
          by (apply (gle_trans x y (PG L R)); auto).
        rewrite (gle_ropt (PG L R) x) in Hbad; [discriminate | exact Hx].
      * apply gle_ropt; exact Hr.
    + intros l Hl.
      change (lopts (PG L R)) with L in Hl.
      apply gle_lopt; auto.
Qed.

(** A reversible left option may be replaced by its own left options. *)
Theorem gequiv_reversible_l :
  forall L R x xr,
    In xr (ropts x) ->
    gle xr (PG (x :: L) R) = true ->
    gequiv (PG (x :: L) R) (PG (lopts xr ++ L) R) = true.
Proof.
  intros L R x xr Hxr Hle.
  set (G := PG (x :: L) R).
  set (H := PG (lopts xr ++ L) R).
  assert (HlH : lopts H = lopts xr ++ L) by reflexivity.
  assert (HrH : ropts H = R) by reflexivity.
  assert (Hxr_H : gle xr H = true).
  { apply gle_true_iff; split.
    - intros r Hr.
      rewrite HrH in Hr.
      apply (proj1 (proj1 (gle_true_iff xr G) Hle)); exact Hr.
    - intros w Hw.
      apply gle_lopt; rewrite HlH; apply in_or_app; left; exact Hw. }
  apply gequiv_true_iff; split.
  - apply gle_true_iff; split.
    + intros r Hr; rewrite HrH in Hr; apply gle_ropt; exact Hr.
    + intros l Hl.
      change (lopts G) with (x :: L) in Hl.
      destruct Hl as [<- | Hl].
      * destruct (gle H x) eqn:E; auto.
        exfalso.
        assert (Hbad : gle xr x = true) by (apply (gle_trans xr H x); auto).
        rewrite (gle_ropt x xr) in Hbad; [discriminate | exact Hxr].
      * apply gle_lopt; rewrite HlH; apply in_or_app; right; exact Hl.
  - apply gle_true_iff; split.
    + intros r Hr.
      change (ropts G) with R in Hr.
      apply gle_ropt; rewrite HrH; exact Hr.
    + intros l Hl.
      rewrite HlH in Hl.
      apply in_app_or in Hl; destruct Hl as [Hl | Hl].
      * destruct (gle G l) eqn:E; auto.
        exfalso.
        assert (Hbad : gle xr l = true) by (apply (gle_trans xr G l); auto).
        rewrite (gle_lopt xr l) in Hbad; [discriminate | exact Hl].
      * apply gle_lopt; change (lopts G) with (x :: L); right; exact Hl.
Qed.

Theorem gequiv_reversible_r :
  forall L R y yl,
    In yl (lopts y) ->
    gle (PG L (y :: R)) yl = true ->
    gequiv (PG L (y :: R)) (PG L (ropts yl ++ R)) = true.
Proof.
  intros L R y yl Hyl Hle.
  set (G := PG L (y :: R)).
  set (H := PG L (ropts yl ++ R)).
  assert (HlH : lopts H = L) by reflexivity.
  assert (HrH : ropts H = ropts yl ++ R) by reflexivity.
  assert (Hyl_H : gle H yl = true).
  { apply gle_true_iff; split.
    - intros r Hr.
      apply gle_ropt; rewrite HrH; apply in_or_app; left; exact Hr.
    - intros w Hw.
      rewrite HlH in Hw.
      apply (proj2 (proj1 (gle_true_iff G yl) Hle)); exact Hw. }
  apply gequiv_true_iff; split.
  - apply gle_true_iff; split.
    + intros r Hr.
      rewrite HrH in Hr.
      apply in_app_or in Hr; destruct Hr as [Hr | Hr].
      * destruct (gle r G) eqn:E; auto.
        exfalso.
        assert (Hbad : gle r yl = true) by (apply (gle_trans r G yl); auto).
        rewrite (gle_ropt yl r) in Hbad; [discriminate | exact Hr].
      * apply gle_ropt; change (ropts G) with (y :: R); right; exact Hr.
    + intros l Hl.
      change (lopts G) with L in Hl.
      apply gle_lopt; rewrite HlH; exact Hl.
  - apply gle_true_iff; split.
    + intros r Hr.
      change (ropts G) with (y :: R) in Hr.
      destruct Hr as [<- | Hr].
      * destruct (gle y H) eqn:E; auto.
        exfalso.
        assert (Hbad : gle y yl = true) by (apply (gle_trans y H yl); auto).
        rewrite (gle_lopt y yl) in Hbad; [discriminate | exact Hyl].
      * apply gle_ropt; rewrite HrH; apply in_or_app; right; exact Hr.
    + intros l Hl; rewrite HlH in Hl; apply gle_lopt; exact Hl.
Qed.

(** * Reduced games *)

(** A game is reduced when no option is dominated and none is reversible. *)
Definition reduced (G : pgame) : Prop :=
  (forall x y, In x (lopts G) -> In y (lopts G) -> gle x y = true -> x = y) /\
  (forall x y, In x (ropts G) -> In y (ropts G) -> gle x y = true -> x = y) /\
  (forall x xr, In x (lopts G) -> In xr (ropts x) -> gle xr G = false) /\
  (forall y yl, In y (ropts G) -> In yl (lopts y) -> gle G yl = false).

(** Equivalent reduced games have the same left options up to equivalence. *)
Theorem reduced_lopts_match :
  forall G H x,
    reduced G -> reduced H -> gequiv G H = true ->
    In x (lopts G) -> exists y, In y (lopts H) /\ gequiv x y = true.
Proof.
  intros G H x HcG HcH He Hx.
  destruct HcG as (HdomG & _ & HrevG & _).
  destruct HcH as (_ & _ & HrevH & _).
  apply gequiv_true_iff in He; destruct He as [Hgh Hhg].
  assert (Hno : gle H x = false).
  { destruct (gle H x) eqn:E; auto.
    exfalso.
    assert (Hbad : gle G x = true) by (apply (gle_trans G H x); auto).
    rewrite (gle_lopt G x) in Hbad; [discriminate | exact Hx]. }
  apply gle_false_iff in Hno.
  destruct Hno as [[r [Hr Hrx]] | [y [Hy Hxy]]].
  - exfalso.
    assert (Hbad : gle r G = true) by (apply (gle_trans r H G); auto).
    rewrite (HrevG x r Hx Hr) in Hbad; discriminate.
  - exists y; split; [exact Hy|].
    assert (Hno2 : gle G y = false).
    { destruct (gle G y) eqn:E; auto.
      exfalso.
      assert (Hbad : gle H y = true) by (apply (gle_trans H G y); auto).
      rewrite (gle_lopt H y) in Hbad; [discriminate | exact Hy]. }
    apply gle_false_iff in Hno2.
    destruct Hno2 as [[r [Hr Hry]] | [x' [Hx' Hyx']]].
    + exfalso.
      assert (Hbad : gle r H = true) by (apply (gle_trans r G H); auto).
      rewrite (HrevH y r Hy Hr) in Hbad; discriminate.
    + assert (Hxx' : gle x x' = true) by (apply (gle_trans x y x'); auto).
      assert (Heqx : x = x') by (apply HdomG; auto).
      apply gequiv_true_iff; split; [exact Hxy | rewrite Heqx; exact Hyx'].
Qed.

(** Equivalent reduced games have the same right options up to equivalence. *)
Theorem reduced_ropts_match :
  forall G H y,
    reduced G -> reduced H -> gequiv G H = true ->
    In y (ropts G) -> exists x, In x (ropts H) /\ gequiv y x = true.
Proof.
  intros G H y HcG HcH He Hy.
  destruct HcG as (_ & HdomG & _ & HrevG).
  destruct HcH as (_ & _ & _ & HrevH).
  apply gequiv_true_iff in He; destruct He as [Hgh Hhg].
  assert (Hno : gle y H = false).
  { destruct (gle y H) eqn:E; auto.
    exfalso.
    assert (Hbad : gle y G = true) by (apply (gle_trans y H G); auto).
    rewrite (gle_ropt G y) in Hbad; [discriminate | exact Hy]. }
  apply gle_false_iff in Hno.
  destruct Hno as [[r [Hr Hry]] | [w [Hw Hyw]]].
  - exists r; split; [exact Hr|].
    assert (Hno2 : gle r G = false).
    { destruct (gle r G) eqn:E; auto.
      exfalso.
      assert (Hbad : gle r H = true) by (apply (gle_trans r G H); auto).
      rewrite (gle_ropt H r) in Hbad; [discriminate | exact Hr]. }
    apply gle_false_iff in Hno2.
    destruct Hno2 as [[r' [Hr' Hr'r]] | [w [Hw Hrw]]].
    + assert (Hr'y : gle r' y = true) by (apply (gle_trans r' r y); auto).
      assert (Heqy : r' = y) by (apply HdomG; auto).
      apply gequiv_true_iff; split; [rewrite <- Heqy; exact Hr'r | exact Hry].
    + exfalso.
      assert (Hbad : gle H w = true) by (apply (gle_trans H G w); auto).
      rewrite (HrevH r w Hr Hw) in Hbad; discriminate.
  - exfalso.
    assert (Hbad : gle G w = true) by (apply (gle_trans G H w); auto).
    rewrite (HrevG y w Hy Hw) in Hbad; discriminate.
Qed.

(** Distinct options of a reduced game are inequivalent. *)
Theorem reduced_lopt_unique :
  forall H x y y',
    reduced H ->
    In y (lopts H) -> In y' (lopts H) ->
    gequiv x y = true -> gequiv x y' = true -> y = y'.
Proof.
  intros H x y y' HcH Hy Hy' He He'.
  destruct HcH as (HdomH & _).
  apply gequiv_true_iff in He; apply gequiv_true_iff in He'.
  apply HdomH; auto.
  apply (gle_trans y x y'); tauto.
Qed.

Theorem reduced_ropt_unique :
  forall H x y y',
    reduced H ->
    In y (ropts H) -> In y' (ropts H) ->
    gequiv y x = true -> gequiv y' x = true -> y = y'.
Proof.
  intros H x y y' HcH Hy Hy' He He'.
  destruct HcH as (_ & HdomH & _).
  apply gequiv_true_iff in He; apply gequiv_true_iff in He'.
  apply HdomH; auto.
  apply (gle_trans y x y'); tauto.
Qed.

(** * Outcome classification *)

(** The four outcome classes: Left, Right, first player, second player. *)
Inductive outcome : Type :=
| Lwins : outcome
| Rwins : outcome
| Firstwins : outcome
| Secondwins : outcome.

Definition outc (G : pgame) : outcome :=
  match lwin G true, lwin G false with
  | true, true => Lwins
  | false, false => Rwins
  | true, false => Firstwins
  | false, true => Secondwins
  end.

(** Each outcome class is a comparison with [zero]. *)
Theorem outc_spec :
  forall G,
    (outc G = Secondwins <-> gequiv G zero = true) /\
    (outc G = Firstwins <-> gfuzzy G zero = true) /\
    (outc G = Lwins <-> (gle zero G = true /\ gle G zero = false)) /\
    (outc G = Rwins <-> (gle G zero = true /\ gle zero G = false)).
Proof.
  intros G.
  assert (Hl : gle zero G = lwin G false)
    by (apply bool_iff_eq, gle_zero_l).
  assert (Hr : gle G zero = negb (lwin G true)).
  { apply bool_iff_eq; rewrite negb_true_iff; apply gle_zero_r. }
  unfold outc, gequiv, gfuzzy.
  rewrite Hl, Hr.
  clear Hl Hr.
  destruct (lwin G true); destruct (lwin G false); cbn;
    repeat split; intros;
    repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end;
    repeat split; congruence.
Qed.

(** * Canonical values *)

(** The star game, in which either player moves to [zero]. *)
Definition star : pgame := PG [zero] [zero].

Definition one : pgame := PG [zero] [].
Definition minus_one : pgame := PG [] [zero].

(** The integer [n] as a game: [n] free moves for Left. *)
Fixpoint num (n : nat) : pgame :=
  match n with
  | 0 => zero
  | S k => PG [num k] []
  end.

(** The infinitesimal [up], positive but below every positive number. *)
Definition up : pgame := PG [zero] [star].
Definition down : pgame := pneg up.

(** The nimbers: both players may move to any smaller nimber. *)
Fixpoint nimber_list (n : nat) : list pgame :=
  match n with
  | 0 => []
  | S k => nimber_list k ++ [PG (nimber_list k) (nimber_list k)]
  end.

Definition nimber (n : nat) : pgame := PG (nimber_list n) (nimber_list n).

Lemma nimber_1 : nimber 1 = star.
Proof. reflexivity. Qed.

(** An impartial game is its own negation. *)
Lemma pneg_nimber_list :
  forall n, map pneg (nimber_list n) = nimber_list n.
Proof.
  induction n as [|n IH]; auto.
  simpl nimber_list; rewrite map_app, IH; simpl map.
  change (pneg (PG (nimber_list n) (nimber_list n)))
    with (PG (map pneg (nimber_list n)) (map pneg (nimber_list n))).
  rewrite IH; auto.
Qed.

Lemma pneg_nimber : forall n, pneg (nimber n) = nimber n.
Proof.
  intros n; unfold nimber.
  change (pneg (PG (nimber_list n) (nimber_list n)))
    with (PG (map pneg (nimber_list n)) (map pneg (nimber_list n))).
  rewrite pneg_nimber_list; auto.
Qed.

Theorem nimber_self_inverse :
  forall n, gequiv (padd (nimber n) (nimber n)) zero = true.
Proof.
  intros n.
  rewrite <- (pneg_nimber n) at 2.
  apply padd_inv.
Qed.

(** Numbers add as numbers do. *)
Theorem num_padd :
  forall n m, gequiv (padd (num n) (num m)) (num (n + m)) = true.
Proof.
  assert (Haux : forall N n m, n + m <= N ->
            gequiv (padd (num n) (num m)) (num (n + m)) = true).
  { induction N as [|N IH]; intros n m HN.
    - assert (n = 0) by lia; assert (m = 0) by lia; subst.
      change (gequiv (padd zero zero) zero = true).
      rewrite padd_zero_l; apply gequiv_refl.
    - destruct n as [|k].
      + change (gequiv (padd zero (num m)) (num m) = true).
        rewrite padd_zero_l; apply gequiv_refl.
      + destruct m as [|j].
        * rewrite padd_zero_r, Nat.add_0_r; apply gequiv_refl.
        * apply gequiv_of_opts.
          -- rewrite lopts_padd.
             change (lopts (num (S k))) with [num k].
             change (lopts (num (S j))) with [num j].
             replace (S k + S j) with (S (k + S j)) by lia.
             change (lopts (num (S (k + S j)))) with [num (k + S j)].
             split.
             ++ intros x Hx; exists (num (k + S j)); split; [left; auto|].
                cbn [map app] in Hx; destruct Hx as [<- | [<- | []]].
                ** apply IH; lia.
                ** replace (k + S j) with (S k + j) by lia.
                   apply IH; lia.
             ++ intros y [<- | []].
                exists (padd (num k) (num (S j))); split; [left; auto|].
                apply IH; lia.
          -- rewrite ropts_padd.
             change (ropts (num (S k))) with (@nil pgame).
             change (ropts (num (S j))) with (@nil pgame).
             replace (S k + S j) with (S (k + S j)) by lia.
             change (ropts (num (S (k + S j)))) with (@nil pgame).
             split; intros x [].  }
  intros n m; apply (Haux (n + m)); lia.
Qed.

(** * Solved positions *)

(** * Shared option and value machinery *)

(** These serve every game built on this core: the pointwise option-matching
    lemmas, and the dyadic halves, whose arithmetic is Conway theory rather
    than anything about a particular board. *)

(** The commuted form of positivity strictly increasing a sum. *)
Lemma glt_padd_pos_comm :
  forall G H, glt zero H -> gle (padd H G) G = false.
Proof.
  intros G H Hpos.
  destruct (glt_padd_pos G H Hpos) as [_ Hne].
  destruct (gle (padd H G) G) eqn:E; auto.
  exfalso.
  assert (Hbad : gle (padd G H) G = true).
  { apply (gle_gequiv_l (padd H G)); [apply padd_comm | exact E]. }
  congruence.
Qed.

(** Games whose option lists are matched pointwise are equivalent. *)
Lemma opts_equiv_map :
  forall {A : Type} (f f' : A -> pgame) (L : list A),
    (forall x, In x L -> gequiv (f x) (f' x) = true) ->
    opts_equiv (map f L) (map f' L).
Proof.
  intros A f f' L H; split.
  - intros x Hx; apply in_map_iff in Hx; destruct Hx as [a [<- Ha]].
    exists (f' a); split; [| apply H; auto].
    apply in_map_iff; eexists; split; [reflexivity | auto].
  - intros y Hy; apply in_map_iff in Hy; destruct Hy as [a [<- Ha]].
    exists (f a); split; [| apply H; auto].
    apply in_map_iff; eexists; split; [reflexivity | auto].
Qed.

Lemma opts_equiv_app_map :
  forall {A B : Type} (f f' : A -> pgame) (g g' : B -> pgame)
         (L : list A) (M : list B),
    (forall x, In x L -> gequiv (f x) (f' x) = true) ->
    (forall x, In x M -> gequiv (g x) (g' x) = true) ->
    opts_equiv (map f L ++ map g M) (map f' L ++ map g' M).
Proof.
  intros A B f f' g g' L M HL HM; split.
  - intros x Hx; apply in_app_or in Hx; destruct Hx as [Hx | Hx];
      apply in_map_iff in Hx; destruct Hx as [a [<- Ha]].
    + exists (f' a); split; [| apply HL; auto].
      apply in_or_app; left; apply in_map_iff; eexists; split;
        [reflexivity | auto].
    + exists (g' a); split; [| apply HM; auto].
      apply in_or_app; right; apply in_map_iff; eexists; split;
        [reflexivity | auto].
  - intros y Hy; apply in_app_or in Hy; destruct Hy as [Hy | Hy];
      apply in_map_iff in Hy; destruct Hy as [a [<- Ha]].
    + exists (f a); split; [| apply HL; auto].
      apply in_or_app; left; apply in_map_iff; eexists; split;
        [reflexivity | auto].
    + exists (g a); split; [| apply HM; auto].
      apply in_or_app; right; apply in_map_iff; eexists; split;
        [reflexivity | auto].
Qed.

(** * Halves *)

(** [half 0] is [1] and [half (k+1)] is [{0 | half k}]. *)
Fixpoint half (k : nat) : pgame :=
  match k with
  | 0 => one
  | S j => PG [zero] [half j]
  end.

Lemma half_pos : forall k, glt zero (half k).
Proof.
  induction k as [|j IH]; split.
  - reflexivity.
  - reflexivity.
  - apply gle_true_iff; split.
    + intros r Hr.
      change (ropts (half (S j))) with [half j] in Hr.
      destruct Hr as [<- | []].
      destruct IH as [_ Hne]; exact Hne.
    + intros g Hg; destruct Hg.
  - apply gle_lopt.
    change (lopts (half (S j))) with [zero]; left; auto.
Qed.

Lemma half_decreasing : forall k, glt (half (S k)) (half k).
Proof.
  assert (Haux : forall N k, k <= N -> glt (half (S k)) (half k)).
  { induction N as [|N IH]; intros k HN.
    - assert (k = 0) by lia; subst; split.
      + apply gle_true_iff; split.
        * intros r Hr; change (ropts (half 0)) with (@nil pgame) in Hr;
            destruct Hr.
        * intros l Hl.
          change (lopts (half 1)) with [zero] in Hl.
          destruct Hl as [<- | []].
          destruct (half_pos 0) as [_ Hne]; exact Hne.
      + apply gle_ropt; change (ropts (half 1)) with [half 0]; left; auto.
    - split.
      + apply gle_true_iff; split.
        * intros r Hr.
          destruct k as [|j].
          -- change (ropts (half 0)) with (@nil pgame) in Hr; destruct Hr.
          -- change (ropts (half (S j))) with [half j] in Hr.
             destruct Hr as [<- | []].
             destruct (gle (half j) (half (S (S j)))) eqn:E; auto.
             exfalso.
             destruct (IH j) as [Hle _]; [lia|].
             assert (Hbad : gle (half (S j)) (half (S (S j))) = true).
             { apply (gle_trans (half (S j)) (half j)); auto. }
             rewrite (gle_ropt (half (S (S j))) (half (S j))) in Hbad;
               [discriminate | change (ropts (half (S (S j)))) with [half (S j)];
                left; auto].
        * intros l Hl.
          change (lopts (half (S k))) with [zero] in Hl.
          destruct Hl as [<- | []].
          destruct (half_pos k) as [_ Hne]; exact Hne.
      + apply gle_ropt; change (ropts (half (S k))) with [half k]; left; auto. }
  intros k; apply (Haux k); lia.
Qed.

Lemma half_le : forall i j, i <= j -> gle (half j) (half i) = true.
Proof.
  intros i j; induction j as [|k IH]; intros Hij.
  - assert (i = 0) by lia; subst; apply gle_refl.
  - destruct (Nat.eq_dec i (S k)) as [-> | Hne]; [apply gle_refl|].
    apply (gle_trans (half (S k)) (half k)).
    + destruct (half_decreasing k) as [Hle _]; exact Hle.
    + apply IH; lia.
Qed.

(** Two copies of [half (k+1)] make [half k]. *)

Theorem half_double :
  forall k, gequiv (padd (half (S k)) (half (S k))) (half k) = true.
Proof.
  induction k as [|j IH].
  - apply gequiv_true_iff; split.
    + apply gle_true_iff; split.
      * intros r Hr; change (ropts (half 0)) with (@nil pgame) in Hr;
          destruct Hr.
      * intros l Hl.
        rewrite lopts_padd in Hl.
        change (lopts (half 1)) with [zero] in Hl.
        apply in_app_or in Hl; destruct Hl as [Hl | Hl];
          apply in_map_iff in Hl; destruct Hl as [a [<- Ha]];
          destruct Ha as [<- | []].
        -- rewrite padd_zero_l.
           destruct (half_decreasing 0) as [_ Hne]; exact Hne.
        -- rewrite padd_zero_r.
           destruct (half_decreasing 0) as [_ Hne]; exact Hne.
    + apply gle_true_iff; split.
      * intros r Hr.
        rewrite ropts_padd in Hr.
        change (ropts (half 1)) with [half 0] in Hr.
        apply in_app_or in Hr; destruct Hr as [Hr | Hr];
          apply in_map_iff in Hr; destruct Hr as [a [<- Ha]];
          destruct Ha as [<- | []].
        -- destruct (glt_padd_pos (half 0) (half 1) (half_pos 1)) as [_ Hne].
           exact Hne.
        -- apply glt_padd_pos_comm, half_pos.
      * intros l Hl.
        change (lopts (half 0)) with [zero] in Hl.
        destruct Hl as [<- | []].
        destruct (glt_zero_padd (half 1) (half 1) (half_pos 1) (half_pos 1))
          as [_ Hne]; exact Hne.
  - apply gequiv_true_iff; split.
    + apply gle_true_iff; split.
      * intros r Hr.
        change (ropts (half (S j))) with [half j] in Hr.
        destruct Hr as [<- | []].
        destruct (gle (half j) (padd (half (S (S j))) (half (S (S j))))) eqn:E;
          auto.
        exfalso.
        assert (Hchain : glt (padd (half (S (S j))) (half (S (S j))))
                             (padd (half (S j)) (half (S j)))).
        { apply (glt_trans _ (padd (half (S j)) (half (S (S j))))).
          - apply glt_padd_r, half_decreasing.
          - apply glt_padd_l, half_decreasing. }
        assert (Hlt : glt (padd (half (S (S j))) (half (S (S j)))) (half j)).
        { apply (glt_gequiv_r _ (padd (half (S j)) (half (S j)))); auto. }
        destruct Hlt as [_ Hne]; congruence.
      * intros l Hl.
        rewrite lopts_padd in Hl.
        change (lopts (half (S (S j)))) with [zero] in Hl.
        apply in_app_or in Hl; destruct Hl as [Hl | Hl];
          apply in_map_iff in Hl; destruct Hl as [a [<- Ha]];
          destruct Ha as [<- | []].
        -- rewrite padd_zero_l.
           destruct (half_decreasing (S j)) as [_ Hne]; exact Hne.
        -- rewrite padd_zero_r.
           destruct (half_decreasing (S j)) as [_ Hne]; exact Hne.
    + apply gle_true_iff; split.
      * intros r Hr.
        rewrite ropts_padd in Hr.
        change (ropts (half (S (S j)))) with [half (S j)] in Hr.
        apply in_app_or in Hr; destruct Hr as [Hr | Hr];
          apply in_map_iff in Hr; destruct Hr as [a [<- Ha]];
          destruct Ha as [<- | []].
        -- destruct (glt_padd_pos (half (S j)) (half (S (S j)))
                      (half_pos (S (S j)))) as [_ Hne].
           exact Hne.
        -- apply glt_padd_pos_comm, half_pos.
      * intros l Hl.
        change (lopts (half (S j))) with [zero] in Hl.
        destruct Hl as [<- | []].
        destruct (glt_zero_padd (half (S (S j))) (half (S (S j)))
                   (half_pos (S (S j))) (half_pos (S (S j)))) as [_ Hne].
        exact Hne.
Qed.

(** * Smoke tests *)

Example zero_second : outc zero = Secondwins.
Proof. vm_compute; reflexivity. Qed.

Example star_first : outc star = Firstwins.
Proof. vm_compute; reflexivity. Qed.

Example one_left : outc one = Lwins.
Proof. vm_compute; reflexivity. Qed.

Example minus_one_right : outc minus_one = Rwins.
Proof. vm_compute; reflexivity. Qed.

Example up_left : outc up = Lwins.
Proof. vm_compute; reflexivity. Qed.

Example star_fuzzy_zero : gfuzzy star zero = true.
Proof. vm_compute; reflexivity. Qed.

Example star_star_zero : gequiv (padd star star) zero = true.
Proof. vm_compute; reflexivity. Qed.

Example one_gt_zero : (gle zero one && negb (gle one zero))%bool = true.
Proof. vm_compute; reflexivity. Qed.

(** [up] is confused with [star]: the order on games is only partial. *)
Example up_fuzzy_star : gfuzzy up star = true.
Proof. vm_compute; reflexivity. Qed.

Example up_lt_one : (gle up one && negb (gle one up))%bool = true.
Proof. vm_compute; reflexivity. Qed.

Example down_up_zero : gequiv (padd up down) zero = true.
Proof. vm_compute; reflexivity. Qed.

Example one_one_two : gequiv (padd one one) (num 2) = true.
Proof. vm_compute; reflexivity. Qed.

Example nimber_2_first : outc (nimber 2) = Firstwins.
Proof. vm_compute; reflexivity. Qed.

(** * Canonical forms are unique *)

(** [reduced] constrains a game only through its option lists as sets: it says
    nothing about the order in which the options are listed, nor about repeated
    entries, so two reduced games can be equivalent without being the same
    term. Pinning the term needs a canonical listing, which the structural
    comparison below supplies. *)

(** Lexicographic comparison of option lists under a game comparison. *)
Fixpoint cmp_list (f : pgame -> pgame -> comparison) (l1 l2 : list pgame)
  : comparison :=
  match l1, l2 with
  | [], [] => Eq
  | [], _ :: _ => Lt
  | _ :: _, [] => Gt
  | x :: xs, y :: ys =>
      match f x y with
      | Eq => cmp_list f xs ys
      | c => c
      end
  end.

Fixpoint pcmp (G H : pgame) : comparison :=
  match G, H with
  | PG GL GR, PG HL HR =>
      match cmp_list pcmp GL HL with
      | Eq => cmp_list pcmp GR HR
      | c => c
      end
  end.

(** The strict order the canonical listing is sorted by. *)
Definition plt (G H : pgame) : Prop := pcmp G H = Lt.

Lemma pcmp_refl : forall G, pcmp G G = Eq.
Proof.
  intros G; induction G using pgame_forall_ind.
  assert (Haux : forall l, Forall (fun x => pcmp x x = Eq) l -> cmp_list pcmp l l = Eq).
  { induction l as [|x xs IHl]; intros HF; [reflexivity|].
    inversion HF as [|? ? Hx HF']; subst; simpl.
    rewrite Hx; apply IHl; exact HF'. }
  simpl; rewrite (Haux L H); apply (Haux R H0).
Qed.

Lemma pcmp_eq : forall G H, pcmp G H = Eq -> G = H.
Proof.
  intros G; induction G using pgame_forall_ind; intros [HL HR] Hc.
  assert (Haux : forall l, Forall (fun x => forall H, pcmp x H = Eq -> x = H) l ->
                 forall l', cmp_list pcmp l l' = Eq -> l = l').
  { induction l as [|x xs IHl]; intros HF l' Hl'.
    - destruct l'; [reflexivity | discriminate].
    - destruct l' as [|y ys]; [discriminate|].
      inversion HF as [|? ? Hx HF']; subst; simpl in Hl'.
      destruct (pcmp x y) eqn:Exy; try discriminate.
      rewrite (Hx y Exy), (IHl HF' ys Hl'); reflexivity. }
  simpl in Hc.
  destruct (cmp_list pcmp L HL) eqn:EL; try discriminate.
  rewrite (Haux L H HL EL), (Haux R H0 HR Hc); reflexivity.
Qed.

Lemma pcmp_flip : forall G H, pcmp H G = CompOpp (pcmp G H).
Proof.
  intros G; induction G using pgame_forall_ind; intros [HL HR].
  assert (Haux : forall l,
             Forall (fun x => forall H, pcmp H x = CompOpp (pcmp x H)) l ->
             forall l', cmp_list pcmp l' l = CompOpp (cmp_list pcmp l l')).
  { induction l as [|x xs IHl]; intros HF l'.
    - destruct l'; reflexivity.
    - destruct l' as [|y ys]; [reflexivity|].
      inversion HF as [|? ? Hx HF']; subst; simpl.
      rewrite (Hx y); destruct (pcmp x y); simpl; try reflexivity.
      apply IHl; exact HF'. }
  simpl; rewrite (Haux L H HL); destruct (cmp_list pcmp L HL); simpl;
    try reflexivity.
  apply (Haux R H0 HR).
Qed.

Lemma plt_irrefl : forall G, ~ plt G G.
Proof.
  intros G Hlt; unfold plt in Hlt; rewrite pcmp_refl in Hlt; discriminate.
Qed.

Lemma plt_asym : forall G H, plt G H -> plt H G -> False.
Proof.
  intros G H H1 H2; unfold plt in *.
  rewrite pcmp_flip, H1 in H2; discriminate.
Qed.

(** A sorted list is pinned by its elements. *)
Lemma sorted_incl_eq :
  forall l1 l2,
    StronglySorted plt l1 -> StronglySorted plt l2 ->
    (forall x, In x l1 -> In x l2) ->
    (forall x, In x l2 -> In x l1) ->
    l1 = l2.
Proof.
  induction l1 as [|x xs IH]; intros l2 S1 S2 H12 H21.
  - destruct l2 as [|y ys]; [reflexivity|].
    exfalso; apply (H21 y); left; reflexivity.
  - destruct l2 as [|y ys].
    { exfalso; apply (H12 x); left; reflexivity. }
    inversion S1 as [|? ? S1' F1]; subst.
    inversion S2 as [|? ? S2' F2]; subst.
    assert (Hxy : x = y).
    { destruct (H12 x (or_introl eq_refl)) as [Hxy | Hxin]; [now auto|].
      destruct (H21 y (or_introl eq_refl)) as [Hyx | Hyin]; [now auto|].
      exfalso; apply (plt_asym x y).
      - rewrite Forall_forall in F1; apply F1; exact Hyin.
      - rewrite Forall_forall in F2; apply F2; exact Hxin. }
    subst y; f_equal.
    apply IH; auto.
    + intros z Hz.
      destruct (H12 z (or_intror Hz)) as [<- | Hz']; [|exact Hz'].
      exfalso; apply (plt_irrefl x).
      rewrite Forall_forall in F1; apply F1; exact Hz.
    + intros z Hz.
      destruct (H21 z (or_intror Hz)) as [<- | Hz']; [|exact Hz'].
      exfalso; apply (plt_irrefl x).
      rewrite Forall_forall in F2; apply F2; exact Hz.
Qed.

(** [reduced] reads the option lists as sets, and so does the value: permuting
    them changes the term and disturbs neither. *)
Lemma gequiv_perm :
  forall G H,
    Permutation (lopts G) (lopts H) ->
    Permutation (ropts G) (ropts H) ->
    gequiv G H = true.
Proof.
  assert (Haux : forall l1 l2, Permutation l1 l2 -> opts_equiv l1 l2).
  { intros l1 l2 Hp; split.
    - intros x Hx; exists x; split;
        [apply (Permutation_in _ Hp); exact Hx | apply gequiv_refl].
    - intros y Hy; exists y; split;
        [apply (Permutation_in _ (Permutation_sym Hp)); exact Hy
        | apply gequiv_refl]. }
  intros G H HL HR; apply gequiv_of_opts; apply Haux; assumption.
Qed.

Lemma reduced_perm :
  forall G H,
    Permutation (lopts G) (lopts H) ->
    Permutation (ropts G) (ropts H) ->
    reduced G -> reduced H.
Proof.
  intros G H HL HR (Hdl & Hdr & Hrl & Hrr).
  assert (Heq : gequiv G H = true) by (apply gequiv_perm; assumption).
  apply gequiv_true_iff in Heq; destruct Heq as [Hgh Hhg].
  assert (HinL : forall x, In x (lopts H) -> In x (lopts G))
    by (intros x Hx; apply (Permutation_in _ (Permutation_sym HL)); exact Hx).
  assert (HinR : forall x, In x (ropts H) -> In x (ropts G))
    by (intros x Hx; apply (Permutation_in _ (Permutation_sym HR)); exact Hx).
  repeat split.
  - intros x y Hx Hy; apply Hdl; auto.
  - intros x y Hx Hy; apply Hdr; auto.
  - intros x xr Hx Hxr.
    destruct (gle xr H) eqn:E; auto; exfalso.
    assert (Hbad : gle xr G = true) by (apply (gle_trans xr H G); auto).
    assert (Hno : gle xr G = false) by (apply (Hrl x xr); auto).
    rewrite Hno in Hbad; discriminate.
  - intros y yl Hy Hyl.
    destruct (gle H yl) eqn:E; auto; exfalso.
    assert (Hbad : gle G yl = true) by (apply (gle_trans G H yl); auto).
    assert (Hno : gle G yl = false) by (apply (Hrr y yl); auto).
    rewrite Hno in Hbad; discriminate.
Qed.

(** So reducedness and equivalence together do not pin the term: the nimber
    [star2] with its left options in the other order is a second reduced game
    of the same value. *)
Example reduced_not_unique :
  reduced (PG [zero; star] [zero; star]) /\
  reduced (PG [star; zero] [zero; star]) /\
  gequiv (PG [zero; star] [zero; star]) (PG [star; zero] [zero; star]) = true /\
  PG [zero; star] [zero; star] <> PG [star; zero] [zero; star].
Proof.
  assert (Hred : reduced (PG [zero; star] [zero; star])).
  { unfold reduced; repeat split.
    - intros x y [<- | [<- | []]] [<- | [<- | []]] Hle;
        try reflexivity; vm_compute in Hle; discriminate.
    - intros x y [<- | [<- | []]] [<- | [<- | []]] Hle;
        try reflexivity; vm_compute in Hle; discriminate.
    - intros x xr [<- | [<- | []]] Hxr; simpl in Hxr;
        [contradiction | destruct Hxr as [<- | []]];
        vm_compute; reflexivity.
    - intros y yl [<- | [<- | []]] Hyl; simpl in Hyl;
        [contradiction | destruct Hyl as [<- | []]];
        vm_compute; reflexivity. }
  split; [exact Hred | split; [| split]].
  - apply (reduced_perm (PG [zero; star] [zero; star]));
      [apply perm_swap | apply Permutation_refl | exact Hred].
  - apply gequiv_perm; [apply perm_swap | apply Permutation_refl].
  - intros Hterm.
    assert (Hc : pcmp (PG [zero; star] [zero; star])
                      (PG [star; zero] [zero; star]) = Eq)
      by (rewrite Hterm; apply pcmp_refl).
    vm_compute in Hc; discriminate.
Qed.

(** A canonical game is hereditarily reduced and lists each option once, in
    the order given by [plt]. *)
Inductive canonical : pgame -> Prop :=
| canonical_PG :
    forall L R,
      reduced (PG L R) ->
      StronglySorted plt L ->
      StronglySorted plt R ->
      (forall x, In x L -> canonical x) ->
      (forall x, In x R -> canonical x) ->
      canonical (PG L R).

Lemma canonical_reduced : forall G, canonical G -> reduced G.
Proof. intros G HG; destruct HG; assumption. Qed.

Lemma canonical_lsorted : forall G, canonical G -> StronglySorted plt (lopts G).
Proof. intros G HG; destruct HG; assumption. Qed.

Lemma canonical_rsorted : forall G, canonical G -> StronglySorted plt (ropts G).
Proof. intros G HG; destruct HG; assumption. Qed.

Lemma canonical_lopt : forall G x, canonical G -> In x (lopts G) -> canonical x.
Proof. intros G x HG; destruct HG; simpl; auto. Qed.

Lemma canonical_ropt : forall G x, canonical G -> In x (ropts G) -> canonical x.
Proof. intros G x HG; destruct HG; simpl; auto. Qed.

(** Equivalent canonical games are the same game: canonical forms are unique.
    A term-level conclusion needs the hereditary, canonically ordered notion;
    top-level [reduced] alone leaves the option lists free. *)
Theorem canonical_unique :
  forall G H, canonical G -> canonical H -> gequiv G H = true -> G = H.
Proof.
  assert (Haux : forall n G H,
             rank G <= n -> canonical G -> canonical H ->
             gequiv G H = true -> G = H).
  { induction n as [|n IH]; intros G H Hr HG HH He.
    - exfalso; pose proof (rank_pos G); lia.
    - assert (Hl : forall x, In x (lopts G) -> In x (lopts H)).
      { intros x Hx.
        destruct (reduced_lopts_match G H x (canonical_reduced G HG)
                    (canonical_reduced H HH) He Hx) as [y [Hy Hxy]].
        rewrite (IH x y); auto.
        - pose proof (rank_lopt G x Hx); lia.
        - apply (canonical_lopt G); auto.
        - apply (canonical_lopt H); auto. }
      assert (Hl' : forall y, In y (lopts H) -> In y (lopts G)).
      { intros y Hy.
        destruct (reduced_lopts_match H G y (canonical_reduced H HH)
                    (canonical_reduced G HG) (gequiv_sym G H He) Hy)
          as [x [Hx Hyx]].
        rewrite <- (IH x y); auto.
        - pose proof (rank_lopt G x Hx); lia.
        - apply (canonical_lopt G); auto.
        - apply (canonical_lopt H); auto.
        - apply gequiv_sym; exact Hyx. }
      assert (Hr1 : forall x, In x (ropts G) -> In x (ropts H)).
      { intros x Hx.
        destruct (reduced_ropts_match G H x (canonical_reduced G HG)
                    (canonical_reduced H HH) He Hx) as [y [Hy Hxy]].
        rewrite (IH x y); auto.
        - pose proof (rank_ropt G x Hx); lia.
        - apply (canonical_ropt G); auto.
        - apply (canonical_ropt H); auto. }
      assert (Hr2 : forall y, In y (ropts H) -> In y (ropts G)).
      { intros y Hy.
        destruct (reduced_ropts_match H G y (canonical_reduced H HH)
                    (canonical_reduced G HG) (gequiv_sym G H He) Hy)
          as [x [Hx Hyx]].
        rewrite <- (IH x y); auto.
        - pose proof (rank_ropt G x Hx); lia.
        - apply (canonical_ropt G); auto.
        - apply (canonical_ropt H); auto.
        - apply gequiv_sym; exact Hyx. }
      apply pgame_eq.
      + apply sorted_incl_eq; auto using canonical_lsorted.
      + apply sorted_incl_eq; auto using canonical_rsorted. }
  intros G H; apply (Haux (rank G) G H); lia.
Qed.

(** The canonical games are not a vacuous class. *)
Example canonical_zero : canonical zero.
Proof.
  apply canonical_PG.
  - unfold reduced; simpl; repeat split; intros; contradiction.
  - constructor.
  - constructor.
  - intros x [].
  - intros x [].
Qed.

Example canonical_star : canonical star.
Proof.
  apply canonical_PG.
  - unfold reduced, star; simpl; repeat split.
    + intros x y [Hx | []] [Hy | []] _; subst; reflexivity.
    + intros x y [Hx | []] [Hy | []] _; subst; reflexivity.
    + intros x xr [Hx | []] Hxr; subst x; simpl in Hxr; contradiction.
    + intros y yl [Hy | []] Hyl; subst y; simpl in Hyl; contradiction.
  - repeat constructor.
  - repeat constructor.
  - intros x [Hx | []]; subst x; exact canonical_zero.
  - intros x [Hx | []]; subst x; exact canonical_zero.
Qed.
