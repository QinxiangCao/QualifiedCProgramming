(** * MonotonicList: monotonicity predicates for [list Z]

    Four index-based (non-inductive) predicates describing how the elements
    of an integer list are ordered:

      - [mono_inc]     : strictly increasing      (a_i <  a_j for i < j)
      - [mono_nondec]  : non-decreasing / weak up  (a_i <= a_j for i <= j)
      - [mono_dec]     : strictly decreasing      (a_i >  a_j for i < j)
      - [mono_noninc]  : non-increasing / weak down (a_i >= a_j for i <= j)

    The predicates are stated as "all-pairs" facts over [Znth]/[Zlength], so
    they plug directly into QCP/SimpleC specifications.  Each comes with:
      - base cases ([_nil], [_single]);
      - a [_cons] characterization (head bound + tail monotone);
      - an adjacency characterization ([_iff_adjacent]), bridging to the
        "compare [Znth j] with [Znth (j+1)]" style used in C loop proofs.

    [mono_inc => mono_nondec] and [mono_dec => mono_noninc] are provided, as is
    a bridge [mono_nondec_iff_increasing] to the existing [ListLib.increasing]
    (which, despite its name, is the non-decreasing predicate). *)

From AUXLib Require Import ListLib.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

Local Open Scope Z_scope.

(* ================================================================= *)
(** ** Definitions *)
(* ================================================================= *)

Definition mono_inc (l : list Z) : Prop :=
  forall i j, 0 <= i -> i < j -> j < Zlength l -> Znth i l 0 < Znth j l 0.

Definition mono_nondec (l : list Z) : Prop :=
  forall i j, 0 <= i -> i <= j -> j < Zlength l -> Znth i l 0 <= Znth j l 0.

Definition mono_dec (l : list Z) : Prop :=
  forall i j, 0 <= i -> i < j -> j < Zlength l -> Znth i l 0 > Znth j l 0.

Definition mono_noninc (l : list Z) : Prop :=
  forall i j, 0 <= i -> i <= j -> j < Zlength l -> Znth i l 0 >= Znth j l 0.

(* ================================================================= *)
(** ** A generic [Znth]/[Forall] bridge *)
(* ================================================================= *)

Lemma Forall_Znth {A : Type} (P : A -> Prop) (d : A) (l : list A) :
  Forall P l <-> (forall i, 0 <= i < Zlength l -> P (Znth i l d)).
Proof.
  induction l as [| a l IH].
  - rewrite Zlength_nil. split.
    + intros _ i Hi. lia.
    + intros _. constructor.
  - rewrite Zlength_cons. pose proof (Zlength_nonneg l) as Hnn. split.
    + intros HF i Hi. inversion HF as [| ? ? Ha Hl]; subst.
      destruct (Z.eq_dec i 0) as [-> | Hne].
      * rewrite Znth0_cons. exact Ha.
      * rewrite Znth_cons by lia.
        apply (proj1 IH Hl). lia.
    + intros H. constructor.
      * specialize (H 0 ltac:(lia)). rewrite Znth0_cons in H. exact H.
      * apply (proj2 IH). intros i Hi.
        specialize (H (i + 1) ltac:(lia)).
        rewrite Znth_cons in H by lia.
        replace (i + 1 - 1) with i in H by lia. exact H.
Qed.

(* ================================================================= *)
(** ** Generic adjacency -> all-pairs chaining *)
(* ================================================================= *)

(** For a reflexive-transitive relation, "every adjacent pair is related"
    implies "every ordered pair is related". *)
Lemma adj_pairs_weak (R : Z -> Z -> Prop) (l : list Z)
    (Rrefl : forall x, R x x)
    (Rtrans : forall x y z, R x y -> R y z -> R x z) :
  (forall i, 0 <= i -> i + 1 < Zlength l -> R (Znth i l 0) (Znth (i + 1) l 0)) ->
  forall i j, 0 <= i -> i <= j -> j < Zlength l -> R (Znth i l 0) (Znth j l 0).
Proof.
  intros Hadj i j Hi Hij Hj.
  assert (forall d k, 0 <= k -> k + Z.of_nat d < Zlength l ->
            R (Znth k l 0) (Znth (k + Z.of_nat d) l 0)) as KEY.
  { induction d as [| d IHd]; intros k Hk Hb.
    - replace (k + Z.of_nat 0) with k by (simpl; lia). apply Rrefl.
    - apply Rtrans with (Znth (k + Z.of_nat d) l 0).
      + apply IHd; [lia |]. rewrite Nat2Z.inj_succ in Hb. lia.
      + replace (k + Z.of_nat (S d)) with ((k + Z.of_nat d) + 1)
          by (rewrite Nat2Z.inj_succ; lia).
        apply Hadj; [lia |]. rewrite Nat2Z.inj_succ in Hb. lia. }
  specialize (KEY (Z.to_nat (j - i)) i Hi).
  rewrite Z2Nat.id in KEY by lia.
  replace (i + (j - i)) with j in KEY by lia.
  apply KEY. lia.
Qed.

(** Strict variant: for a transitive relation, "every adjacent pair related"
    implies "every strictly-ordered pair related". *)
Lemma adj_pairs_strict (R : Z -> Z -> Prop) (l : list Z)
    (Rtrans : forall x y z, R x y -> R y z -> R x z) :
  (forall i, 0 <= i -> i + 1 < Zlength l -> R (Znth i l 0) (Znth (i + 1) l 0)) ->
  forall i j, 0 <= i -> i < j -> j < Zlength l -> R (Znth i l 0) (Znth j l 0).
Proof.
  intros Hadj i j Hi Hij Hj.
  assert (forall d k, 0 <= k -> k + Z.of_nat (S d) < Zlength l ->
            R (Znth k l 0) (Znth (k + Z.of_nat (S d)) l 0)) as KEY.
  { induction d as [| d IHd]; intros k Hk Hb.
    - replace (k + Z.of_nat 1) with (k + 1) by (simpl; lia).
      apply Hadj; [lia |]. rewrite Nat2Z.inj_succ in Hb. simpl in Hb. lia.
    - apply Rtrans with (Znth (k + Z.of_nat (S d)) l 0).
      + apply IHd; [lia |]. rewrite Nat2Z.inj_succ in Hb. lia.
      + replace (k + Z.of_nat (S (S d))) with ((k + Z.of_nat (S d)) + 1)
          by (rewrite (Nat2Z.inj_succ (S d)); lia).
        apply Hadj; [lia |]. rewrite (Nat2Z.inj_succ (S d)) in Hb. lia. }
  specialize (KEY (Z.to_nat (j - i - 1)) i Hi).
  rewrite Nat2Z.inj_succ in KEY.
  rewrite Z2Nat.id in KEY by lia.
  replace (i + Z.succ (j - i - 1)) with j in KEY by lia.
  apply KEY. lia.
Qed.

(* ================================================================= *)
(** ** Base cases *)
(* ================================================================= *)

Lemma mono_inc_nil    : mono_inc [].    Proof. intros i j ? ? ?. rewrite Zlength_nil in *. lia. Qed.
Lemma mono_nondec_nil : mono_nondec []. Proof. intros i j ? ? ?. rewrite Zlength_nil in *. lia. Qed.
Lemma mono_dec_nil    : mono_dec [].    Proof. intros i j ? ? ?. rewrite Zlength_nil in *. lia. Qed.
Lemma mono_noninc_nil : mono_noninc []. Proof. intros i j ? ? ?. rewrite Zlength_nil in *. lia. Qed.

Lemma mono_inc_single    : forall x, mono_inc [x].    Proof. intros x i j ? ? ?. rewrite Zlength_cons, Zlength_nil in *. lia. Qed.
Lemma mono_nondec_single : forall x, mono_nondec [x]. Proof. intros x i j ? ? ?. rewrite Zlength_cons, Zlength_nil in *. assert (i = 0) by lia. assert (j = 0) by lia. subst. lia. Qed.
Lemma mono_dec_single    : forall x, mono_dec [x].    Proof. intros x i j ? ? ?. rewrite Zlength_cons, Zlength_nil in *. lia. Qed.
Lemma mono_noninc_single : forall x, mono_noninc [x]. Proof. intros x i j ? ? ?. rewrite Zlength_cons, Zlength_nil in *. assert (i = 0) by lia. assert (j = 0) by lia. subst. lia. Qed.

(* ================================================================= *)
(** ** Strict implies weak *)
(* ================================================================= *)

Lemma mono_inc_nondec : forall l, mono_inc l -> mono_nondec l.
Proof.
  intros l H i j Hi Hij Hj. destruct (Z.eq_dec i j) as [-> | Hne].
  - lia.
  - specialize (H i j Hi ltac:(lia) Hj). lia.
Qed.

Lemma mono_dec_noninc : forall l, mono_dec l -> mono_noninc l.
Proof.
  intros l H i j Hi Hij Hj. destruct (Z.eq_dec i j) as [-> | Hne].
  - lia.
  - specialize (H i j Hi ltac:(lia) Hj). lia.
Qed.

(* ================================================================= *)
(** ** Cons characterizations *)
(* ================================================================= *)

Lemma mono_nondec_cons : forall x l,
  mono_nondec (x :: l) <-> Forall (fun y => x <= y) l /\ mono_nondec l.
Proof.
  intros x l. split.
  - intros H. split.
    + apply (proj2 (Forall_Znth (fun y => x <= y) 0 l)). intros i Hi.
      specialize (H 0 (i + 1) ltac:(lia) ltac:(lia) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth0_cons, Znth_cons in H by lia.
      replace (i + 1 - 1) with i in H by lia. exact H.
    + intros i j Hi Hij Hj.
      specialize (H (i + 1) (j + 1) ltac:(lia) ltac:(lia) ltac:(rewrite Zlength_cons; lia)).
      rewrite !Znth_cons in H by lia.
      replace (i + 1 - 1) with i in H by lia.
      replace (j + 1 - 1) with j in H by lia. exact H.
  - intros [HF Hl]. rewrite (Forall_Znth (fun y => x <= y) 0 l) in HF.
    intros i j Hi Hij Hj. rewrite Zlength_cons in Hj.
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + rewrite Znth0_cons. destruct (Z.eq_dec j 0) as [-> | Hj0].
      * rewrite Znth0_cons. lia.
      * rewrite Znth_cons by lia. apply HF. lia.
    + rewrite !Znth_cons by lia. apply Hl; lia.
Qed.

Lemma mono_noninc_cons : forall x l,
  mono_noninc (x :: l) <-> Forall (fun y => y <= x) l /\ mono_noninc l.
Proof.
  intros x l. split.
  - intros H. split.
    + apply (proj2 (Forall_Znth (fun y => y <= x) 0 l)). intros i Hi.
      specialize (H 0 (i + 1) ltac:(lia) ltac:(lia) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth0_cons, Znth_cons in H by lia.
      replace (i + 1 - 1) with i in H by lia. lia.
    + intros i j Hi Hij Hj.
      specialize (H (i + 1) (j + 1) ltac:(lia) ltac:(lia) ltac:(rewrite Zlength_cons; lia)).
      rewrite !Znth_cons in H by lia.
      replace (i + 1 - 1) with i in H by lia.
      replace (j + 1 - 1) with j in H by lia. exact H.
  - intros [HF Hl]. rewrite (Forall_Znth (fun y => y <= x) 0 l) in HF.
    intros i j Hi Hij Hj. rewrite Zlength_cons in Hj.
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + rewrite Znth0_cons. destruct (Z.eq_dec j 0) as [-> | Hj0].
      * rewrite Znth0_cons. lia.
      * rewrite Znth_cons by lia. assert (x >= Znth (j - 1) l 0); [| lia].
        specialize (HF (j - 1) ltac:(lia)). lia.
    + rewrite !Znth_cons by lia. apply Hl; lia.
Qed.

Lemma mono_inc_cons : forall x l,
  mono_inc (x :: l) <-> Forall (fun y => x < y) l /\ mono_inc l.
Proof.
  intros x l. split.
  - intros H. split.
    + apply (proj2 (Forall_Znth (fun y => x < y) 0 l)). intros i Hi.
      specialize (H 0 (i + 1) ltac:(lia) ltac:(lia) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth0_cons, Znth_cons in H by lia.
      replace (i + 1 - 1) with i in H by lia. exact H.
    + intros i j Hi Hij Hj.
      specialize (H (i + 1) (j + 1) ltac:(lia) ltac:(lia) ltac:(rewrite Zlength_cons; lia)).
      rewrite !Znth_cons in H by lia.
      replace (i + 1 - 1) with i in H by lia.
      replace (j + 1 - 1) with j in H by lia. exact H.
  - intros [HF Hl]. rewrite (Forall_Znth (fun y => x < y) 0 l) in HF.
    intros i j Hi Hij Hj. rewrite Zlength_cons in Hj.
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + rewrite Znth0_cons, Znth_cons by lia. apply HF. lia.
    + rewrite !Znth_cons by lia. apply Hl; lia.
Qed.

Lemma mono_dec_cons : forall x l,
  mono_dec (x :: l) <-> Forall (fun y => y < x) l /\ mono_dec l.
Proof.
  intros x l. split.
  - intros H. split.
    + apply (proj2 (Forall_Znth (fun y => y < x) 0 l)). intros i Hi.
      specialize (H 0 (i + 1) ltac:(lia) ltac:(lia) ltac:(rewrite Zlength_cons; lia)).
      rewrite Znth0_cons, Znth_cons in H by lia.
      replace (i + 1 - 1) with i in H by lia. lia.
    + intros i j Hi Hij Hj.
      specialize (H (i + 1) (j + 1) ltac:(lia) ltac:(lia) ltac:(rewrite Zlength_cons; lia)).
      rewrite !Znth_cons in H by lia.
      replace (i + 1 - 1) with i in H by lia.
      replace (j + 1 - 1) with j in H by lia. exact H.
  - intros [HF Hl]. rewrite (Forall_Znth (fun y => y < x) 0 l) in HF.
    intros i j Hi Hij Hj. rewrite Zlength_cons in Hj.
    destruct (Z.eq_dec i 0) as [-> | Hi0].
    + rewrite Znth0_cons, Znth_cons by lia. specialize (HF (j - 1) ltac:(lia)). lia.
    + rewrite !Znth_cons by lia. apply Hl; lia.
Qed.

(* ================================================================= *)
(** ** Adjacency characterizations *)
(* ================================================================= *)

Lemma mono_nondec_iff_adjacent : forall l,
  mono_nondec l <-> (forall i, 0 <= i -> i + 1 < Zlength l -> Znth i l 0 <= Znth (i + 1) l 0).
Proof.
  intros l. split.
  - intros H i Hi Hb. apply H; lia.
  - intros H. unfold mono_nondec. apply (adj_pairs_weak Z.le l);
      [ intros; lia | intros; lia | intros i Hi Hb; apply H; lia ].
Qed.

Lemma mono_noninc_iff_adjacent : forall l,
  mono_noninc l <-> (forall i, 0 <= i -> i + 1 < Zlength l -> Znth i l 0 >= Znth (i + 1) l 0).
Proof.
  intros l. split.
  - intros H i Hi Hb. apply H; lia.
  - intros H. unfold mono_noninc. apply (adj_pairs_weak Z.ge l);
      [ intros; lia | intros; lia | intros i Hi Hb; apply H; lia ].
Qed.

Lemma mono_inc_iff_adjacent : forall l,
  mono_inc l <-> (forall i, 0 <= i -> i + 1 < Zlength l -> Znth i l 0 < Znth (i + 1) l 0).
Proof.
  intros l. split.
  - intros H i Hi Hb. apply H; lia.
  - intros H. unfold mono_inc. apply (adj_pairs_strict Z.lt l);
      [ intros; lia | intros i Hi Hb; apply H; lia ].
Qed.

Lemma mono_dec_iff_adjacent : forall l,
  mono_dec l <-> (forall i, 0 <= i -> i + 1 < Zlength l -> Znth i l 0 > Znth (i + 1) l 0).
Proof.
  intros l. split.
  - intros H i Hi Hb. apply H; lia.
  - intros H. unfold mono_dec. apply (adj_pairs_strict Z.gt l);
      [ intros; lia | intros i Hi Hb; apply H; lia ].
Qed.

(* ================================================================= *)
(** ** Bridge to [ListLib.increasing] (which is the non-decreasing predicate) *)
(* ================================================================= *)

Lemma mono_nondec_iff_increasing : forall l, mono_nondec l <-> increasing l.
Proof.
  induction l as [| a l IH].
  - split; intros _; [exact I | apply mono_nondec_nil].
  - rewrite mono_nondec_cons, IH. split.
    + intros [HF Hinc].
      destruct l as [| b l]; simpl in *; auto.
      rewrite Forall_forall in HF.
      split; [apply HF; left; reflexivity | exact Hinc].
    + intros Hinc. split.
      * rewrite Forall_forall. intros y Hy.
        eapply increasing_aux_head_le_all_In; eauto.
      * apply increasing_aux_tail_increasing with (x := a). exact Hinc.
Qed.

(* ================================================================= *)
(** ** Inductive counterparts (mirroring [ListLib.increasing]) *)
(* ================================================================= *)

(** [mono_chain] captures the all-pairs shape once, generically over the order
    relation [R], and reuses it for all four notions.  For the transitive
    relation [Z.le], [ListLib.increasing]'s adjacent-chain definition is
    equivalent to [mono_chain Z.le] (see [increasing_iff_chain]). *)
Inductive mono_chain (R : Z -> Z -> Prop) : list Z -> Prop :=
  | mono_chain_nil  : mono_chain R []
  | mono_chain_cons : forall x l,
      mono_chain R l -> Forall (R x) l -> mono_chain R (x :: l).

Lemma mono_chain_cons_iff : forall R x l,
  mono_chain R (x :: l) <-> Forall (R x) l /\ mono_chain R l.
Proof.
  intros R x l. split.
  - intros H. inversion H; subst. split; assumption.
  - intros [HF Hc]. constructor; assumption.
Qed.

(** [mono_chain R] holds iff every *strictly earlier* element is [R]-related to
    every later one — no reflexivity or transitivity of [R] required. *)
Lemma mono_chain_iff_index : forall R l,
  mono_chain R l <->
  (forall i j, 0 <= i -> i < j -> j < Zlength l -> R (Znth i l 0) (Znth j l 0)).
Proof.
  intros R l. split.
  - intros H. induction H as [| x l Hc IH HF].
    + intros i j Hi Hij Hj. rewrite Zlength_nil in Hj. lia.
    + intros i j Hi Hij Hj. rewrite Zlength_cons in Hj.
      destruct (Z.eq_dec i 0) as [-> | Hi0].
      * rewrite Znth0_cons, Znth_cons by lia.
        rewrite (Forall_Znth (R x) 0 l) in HF. apply HF. lia.
      * rewrite !Znth_cons by lia. apply IH; lia.
  - induction l as [| x l IH]; intros H.
    + constructor.
    + constructor.
      * apply IH. intros i j Hi Hij Hj.
        specialize (H (i + 1) (j + 1) ltac:(lia) ltac:(lia)
          ltac:(rewrite Zlength_cons; lia)).
        rewrite !Znth_cons in H by lia.
        replace (i + 1 - 1) with i in H by lia.
        replace (j + 1 - 1) with j in H by lia. exact H.
      * apply (proj2 (Forall_Znth (R x) 0 l)). intros k Hk.
        specialize (H 0 (k + 1) ltac:(lia) ltac:(lia)
          ltac:(rewrite Zlength_cons; lia)).
        rewrite Znth0_cons, Znth_cons in H by lia.
        replace (k + 1 - 1) with k in H by lia. exact H.
Qed.

(** App lemma: a concatenation is [mono_chain] iff both parts are and every
    element of the left part is [R]-related to every element of the right. *)
Lemma mono_chain_app : forall R l1 l2,
  mono_chain R (l1 ++ l2) <->
  mono_chain R l1 /\ mono_chain R l2 /\
  (forall a b, In a l1 -> In b l2 -> R a b).
Proof.
  intros R l1. induction l1 as [| x l1 IH]; intros l2; simpl.
  - split.
    + intros H. split; [constructor |]. split; [exact H |]. intros a b [].
    + intros [_ [H _]]. exact H.
  - rewrite !mono_chain_cons_iff. rewrite Forall_app, IH. split.
    + intros [[HFx1 HFx2] [Hc1 [Hc2 Hcr]]].
      repeat split; try assumption.
      intros a b Ha Hb. destruct Ha as [Heq | Ha];
        [ subst a; rewrite Forall_forall in HFx2; apply HFx2; assumption
        | apply Hcr; assumption ].
    + intros [[HFx1 Hc1] [Hc2 Hcr]].
      assert (HFx2 : Forall (R x) l2).
      { rewrite Forall_forall. intros b Hb.
        apply Hcr; [left; reflexivity | assumption]. }
      repeat split; try assumption.
      intros a b Ha Hb. apply Hcr; [right; assumption | assumption].
Qed.

(** [ListLib.increasing] is [mono_chain Z.le]; gives it an app lemma too. *)
Lemma increasing_iff_chain : forall l, increasing l <-> mono_chain Z.le l.
Proof.
  induction l as [| x l IH].
  - split; intros _; constructor.
  - split.
    + intros H. constructor.
      * apply IH. eapply increasing_aux_tail_increasing; eauto.
      * rewrite Forall_forall. intros y Hy.
        eapply increasing_aux_head_le_all_In; eauto.
    + intros H. inversion H as [| ? ? Hchain HF]; subst.
      destruct l as [| y l]; simpl; auto.
      split.
      * rewrite Forall_forall in HF. apply HF. left; reflexivity.
      * apply IH. exact Hchain.
Qed.

Lemma increasing_app : forall l1 l2,
  increasing (l1 ++ l2) <->
  increasing l1 /\ increasing l2 /\ (forall a b, In a l1 -> In b l2 -> a <= b).
Proof.
  intros. rewrite !increasing_iff_chain. apply mono_chain_app.
Qed.

Lemma decreasing_iff_chain : forall l, decreasing l <-> mono_chain Z.ge l.
Proof.
  induction l as [| x l IH].
  - split; intros _; constructor.
  - split.
    + intros H. constructor.
      * apply IH. eapply decreasing_aux_tail_decreasing; eauto.
      * rewrite Forall_forall. intros y Hy.
        pose proof (decreasing_aux_head_ge_all_In _ _ _ H Hy). lia.
    + intros H. inversion H as [| ? ? Hchain HF]; subst.
      destruct l as [| y l]; simpl; auto.
      split.
      * rewrite Forall_forall in HF. specialize (HF y (or_introl eq_refl)). lia.
      * apply IH. exact Hchain.
Qed.

Lemma decreasing_app : forall l1 l2,
  decreasing (l1 ++ l2) <->
  decreasing l1 /\ decreasing l2 /\ (forall a b, In a l1 -> In b l2 -> a >= b).
Proof.
  intros. rewrite !decreasing_iff_chain. apply mono_chain_app.
Qed.

Lemma strict_decreasing_iff_chain : forall l, strict_decreasing l <-> mono_chain Z.gt l.
Proof.
  induction l as [| x l IH].
  - split; intros _; constructor.
  - split.
    + intros H. constructor.
      * apply IH. eapply strict_decreasing_aux_tail_strict_decreasing; eauto.
      * rewrite Forall_forall. intros y Hy.
        pose proof (strict_decreasing_aux_head_gt_all_In _ _ _ H Hy). lia.
    + intros H. inversion H as [| ? ? Hchain HF]; subst.
      destruct l as [| y l]; simpl; auto.
      split.
      * rewrite Forall_forall in HF. specialize (HF y (or_introl eq_refl)). lia.
      * apply IH. exact Hchain.
Qed.

Lemma strict_decreasing_app : forall l1 l2,
  strict_decreasing (l1 ++ l2) <->
  strict_decreasing l1 /\ strict_decreasing l2 /\ (forall a b, In a l1 -> In b l2 -> a > b).
Proof.
  intros. rewrite !strict_decreasing_iff_chain. apply mono_chain_app.
Qed.

Lemma mono_dec_iff_strict_decreasing : forall l, mono_dec l <-> strict_decreasing l.
Proof.
  intros l. unfold mono_dec.
  rewrite strict_decreasing_iff_chain, mono_chain_iff_index. reflexivity.
Qed.

(** Bridge between the weak ("[<=]") and strict ("[<]") index views, for a
    reflexive relation. *)
Lemma weak_iff_strict_index : forall (R : Z -> Z -> Prop) (l : list Z),
  (forall x, R x x) ->
  (forall i j, 0 <= i -> i <= j -> j < Zlength l -> R (Znth i l 0) (Znth j l 0)) <->
  (forall i j, 0 <= i -> i <  j -> j < Zlength l -> R (Znth i l 0) (Znth j l 0)).
Proof.
  intros R l Rrefl. split; intros H i j Hi Hij Hj.
  - apply H; lia.
  - destruct (Z.eq_dec i j) as [-> | Hne]; [ apply Rrefl | apply H; lia ].
Qed.

Lemma mono_noninc_iff_decreasing : forall l, mono_noninc l <-> decreasing l.
Proof.
  intros l. rewrite decreasing_iff_chain, mono_chain_iff_index.
  unfold mono_noninc. apply (weak_iff_strict_index Z.ge l). intros; lia.
Qed.

(* ----- strictly increasing ----- *)

Inductive mono_inc_ind : list Z -> Prop :=
  | mono_inc_ind_nil  : mono_inc_ind []
  | mono_inc_ind_cons : forall x l,
      mono_inc_ind l -> Forall (fun y => x < y) l -> mono_inc_ind (x :: l).

Lemma mono_inc_ind_iff_chain : forall l, mono_inc_ind l <-> mono_chain Z.lt l.
Proof.
  induction l as [| x l IH].
  - split; intros _; constructor.
  - split; intros H; inversion H; subst;
      constructor; solve [ apply IH; assumption | assumption ].
Qed.

Lemma mono_inc_ind_app : forall l1 l2,
  mono_inc_ind (l1 ++ l2) <->
  mono_inc_ind l1 /\ mono_inc_ind l2 /\ (forall a b, In a l1 -> In b l2 -> a < b).
Proof.
  intros. rewrite !mono_inc_ind_iff_chain. apply mono_chain_app.
Qed.

Lemma mono_inc_iff_ind : forall l, mono_inc l <-> mono_inc_ind l.
Proof.
  intros l. unfold mono_inc.
  rewrite mono_inc_ind_iff_chain, mono_chain_iff_index. reflexivity.
Qed.

(* ----- strictly decreasing ----- *)

Inductive mono_dec_ind : list Z -> Prop :=
  | mono_dec_ind_nil  : mono_dec_ind []
  | mono_dec_ind_cons : forall x l,
      mono_dec_ind l -> Forall (fun y => x > y) l -> mono_dec_ind (x :: l).

Lemma mono_dec_ind_iff_chain : forall l, mono_dec_ind l <-> mono_chain Z.gt l.
Proof.
  induction l as [| x l IH].
  - split; intros _; constructor.
  - split; intros H; inversion H; subst;
      constructor; solve [ apply IH; assumption | assumption ].
Qed.

Lemma mono_dec_ind_app : forall l1 l2,
  mono_dec_ind (l1 ++ l2) <->
  mono_dec_ind l1 /\ mono_dec_ind l2 /\ (forall a b, In a l1 -> In b l2 -> a > b).
Proof.
  intros. rewrite !mono_dec_ind_iff_chain. apply mono_chain_app.
Qed.

Lemma mono_dec_iff_ind : forall l, mono_dec l <-> mono_dec_ind l.
Proof.
  intros l. unfold mono_dec.
  rewrite mono_dec_ind_iff_chain, mono_chain_iff_index. reflexivity.
Qed.

(* ----- non-increasing ----- *)

Inductive mono_noninc_ind : list Z -> Prop :=
  | mono_noninc_ind_nil  : mono_noninc_ind []
  | mono_noninc_ind_cons : forall x l,
      mono_noninc_ind l -> Forall (fun y => x >= y) l -> mono_noninc_ind (x :: l).

Lemma mono_noninc_ind_iff_chain : forall l, mono_noninc_ind l <-> mono_chain Z.ge l.
Proof.
  induction l as [| x l IH].
  - split; intros _; constructor.
  - split; intros H; inversion H; subst;
      constructor; solve [ apply IH; assumption | assumption ].
Qed.

Lemma mono_noninc_ind_app : forall l1 l2,
  mono_noninc_ind (l1 ++ l2) <->
  mono_noninc_ind l1 /\ mono_noninc_ind l2 /\ (forall a b, In a l1 -> In b l2 -> a >= b).
Proof.
  intros. rewrite !mono_noninc_ind_iff_chain. apply mono_chain_app.
Qed.

Lemma mono_noninc_iff_ind : forall l, mono_noninc l <-> mono_noninc_ind l.
Proof.
  intros l. rewrite mono_noninc_ind_iff_chain, mono_chain_iff_index.
  unfold mono_noninc. apply (weak_iff_strict_index Z.ge l). intros; lia.
Qed.
