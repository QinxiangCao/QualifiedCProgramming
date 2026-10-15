Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition PieceMove (n : Z) (a b : list Z) : Prop :=
  exists i d, 0 <= i < Zlength a /\ (d = - 1 \/ d = 1) /\
    1 <= Znth i a 0 + d <= n /\ ~In (Znth i a 0 + d) a /\
    b = replace_Znth i (Znth i a 0 + d) a.
Definition SameColor (p : list Z) : Prop :=
  (Forall (fun x => Z.even x = true) p) \/ (Forall (fun x => Z.even x = false) p).
Definition CanPlaceIn (n moves : Z) (start : list Z) : Prop :=
  exists states : list (list Z), Zlength states = moves + 1 /\ Znth 0 states [] = start /\
    (forall i, 0 <= i < moves -> PieceMove n (Znth i states []) (Znth (i + 1) states [])) /\
    SameColor (Znth moves states []).
Definition Pre (n : Z) (p : list Z) : Prop :=
  (* Stated explicitly in the P023 solver Require, so dropped here:
       Zlength p = n / 2 /\
       Forall (fun x => 1 <= x <= n) p /\
       2 <= n <= 100   *)
  Z.even n = true /\
  NoDup p.

Definition Spec (n : Z) (p : list Z) (out : Z) : Prop := min_value_of_subset Z.le (fun d => d >= 0 /\ CanPlaceIn n d p) (fun x => x) out.

Definition OddTarget (i : Z) : Z := 2 * i + 1.
Definition EvenTarget (i : Z) : Z := 2 * i + 2.

Definition ChessCostPrefix
    (sorted : list Z) (done odd even : Z) : Prop :=
  odd = sum (fun i : Z => 0 <= i < done)
            (fun i => Z.abs (Znth i sorted 0 - OddTarget i)) /\
  even = sum (fun i : Z => 0 <= i < done)
             (fun i => Z.abs (Znth i sorted 0 - EvenTarget i)).

Require Import Coq.micromega.Lia.

Lemma ChessCostPrefix_zero :
  forall sorted, ChessCostPrefix sorted 0 0 0.
Proof.
  intros sorted.
  unfold ChessCostPrefix.
  rewrite !sum_Z_range_empty by lia.
  auto.
Qed.

Lemma ChessCostPrefix_step :
  forall sorted done odd even,
    0 <= done ->
    ChessCostPrefix sorted done odd even ->
    ChessCostPrefix sorted (done + 1)
      (odd + Z.abs (Znth done sorted 0 - OddTarget done))
      (even + Z.abs (Znth done sorted 0 - EvenTarget done)).
Proof.
  intros sorted done odd even Hdone [Hodd Heven].
  unfold ChessCostPrefix in *.
  rewrite !sum_Z_range_extend_right by lia.
  split; lia.
Qed.

Lemma ChessDistance_bounds :
  forall x i half,
    0 <= i < half ->
    1 <= x <= 2 * half ->
    2 * half <= 100 ->
    0 <= Z.abs (x - OddTarget i) <= 100 /\
    0 <= Z.abs (x - EvenTarget i) <= 100.
Proof.
  intros x i half Hi Hx Hhalf.
  unfold OddTarget, EvenTarget.
  repeat split; try apply Z.abs_nonneg;
    apply (proj2 (Z.abs_le _ _)); lia.
Qed.

Lemma Permutation_preserves_Znth_bounds :
  forall a b n lo hi,
    Permutation a b ->
    Zlength a = n ->
    (forall i, 0 <= i < n -> lo <= Znth i a 0 <= hi) ->
    forall i, 0 <= i < n -> lo <= Znth i b 0 <= hi.
Proof.
  intros a b n lo hi Hperm Hlen Hbounds.
  assert (Ha : Forall (fun x => lo <= x <= hi) a).
  {
    apply (proj2 (Forall_Znth (fun x => lo <= x <= hi) 0 a)).
    intros i Hi.
    apply Hbounds.
    lia.
  }
  assert (Hb : Forall (fun x => lo <= x <= hi) b).
  {
    eapply Permutation_Forall; eauto.
  }
  pose proof (proj1 (Forall_Znth (fun x => lo <= x <= hi) 0 b) Hb) as Hb'.
  intros i Hi.
  apply Hb'.
  rewrite Zlength_correct.
  rewrite <- (Permutation_length Hperm).
  rewrite Zlength_correct in Hlen.
  lia.
Qed.

(* Proof-only bridge from the ordered distance computed by [solver] to the
   operational, collision-free move semantics in [Spec]. *)
Fixpoint ChessTargets (first : Z) (count : nat) : list Z :=
  match count with
  | O => []
  | S count' => first :: ChessTargets (first + 2) count'
  end.

Fixpoint ChessZipCost (a b : list Z) : Z :=
  match a, b with
  | x :: a', y :: b' => Z.abs (x - y) + ChessZipCost a' b'
  | _, _ => 0
  end.

Inductive ChessMoves (n : Z) : nat -> list Z -> list Z -> Prop :=
| ChessMoves_zero : forall a, ChessMoves n O a a
| ChessMoves_succ : forall k a b c,
    PieceMove n a b -> ChessMoves n k b c -> ChessMoves n (S k) a c.

Lemma ChessTargets_length : forall first count,
  length (ChessTargets first count) = count.
Proof.
  intros first count. revert first.
  induction count; intros; simpl; auto.
Qed.

Lemma ChessTargets_Zlength : forall first count,
  Zlength (ChessTargets first count) = Z.of_nat count.
Proof.
  intros. rewrite Zlength_correct, ChessTargets_length. reflexivity.
Qed.

Lemma ChessTargets_In : forall first count x,
  In x (ChessTargets first count) <->
  exists k, 0 <= k < Z.of_nat count /\ x = first + 2 * k.
Proof.
  intros first count. revert first.
  induction count as [|count IH]; intros first x; simpl.
  - split; [tauto |]. intros [k [Hk _]]. lia.
  - rewrite IH. split.
    + intros [-> | [k [Hk ->]]].
      * exists 0. repeat split; lia.
      * exists (k + 1). repeat split.
        -- lia.
        -- lia.
        -- change (first + 2 + 2 * k = first + 2 * (k + 1)). ring.
    + intros [k [Hk Hx]].
      destruct (Z.eq_dec k 0) as [-> | Hne].
      * left. lia.
      * right. exists (k - 1). repeat split.
        -- lia.
        -- lia.
        -- rewrite Hx.
           change (first + 2 * k = first + 2 + 2 * (k - 1)). ring.
Qed.

Lemma ChessTargets_bounds : forall first count n,
  1 <= first -> first + 2 * Z.of_nat count <= n + 2 ->
  Forall (fun x => 1 <= x <= n) (ChessTargets first count).
Proof.
  intros first count n Hfirst Hlast.
  rewrite Forall_forall. intros x Hin.
  rewrite ChessTargets_In in Hin. destruct Hin as [k [Hk ->]]. lia.
Qed.

Lemma ChessTargets_gap : forall first count,
  mono_inc (ChessTargets first count).
Proof.
  intros first count. revert first.
  induction count as [|count IH]; intros first; simpl.
  - apply mono_inc_nil.
  - apply (proj2 (mono_inc_cons first _)). split.
    + apply (proj2 (Forall_Znth (fun y => first < y) 0 _)).
      intros i Hi.
      pose proof (Znth_In_Zlength (ChessTargets (first + 2) count) 0 i Hi) as Hin.
      rewrite ChessTargets_In in Hin. destruct Hin as [k [Hk ->]]. lia.
    + apply IH.
Qed.

Lemma mono_inc_NoDup : forall l, mono_inc l -> NoDup l.
Proof.
  intros l Hinc.
  induction l as [|x xs IH]; constructor.
  - intro Hin.
    pose proof (proj1 (mono_inc_cons x xs) Hinc) as [Hall _].
    rewrite Forall_forall in Hall. specialize (Hall x Hin). lia.
  - apply IH. exact (proj2 (proj1 (mono_inc_cons x xs) Hinc)).
Qed.

Lemma ChessTargets_NoDup : forall first count,
  NoDup (ChessTargets first count).
Proof. intros. apply mono_inc_NoDup, ChessTargets_gap. Qed.

Lemma ChessTargets_same_color : forall first count,
  (first = 1 -> Forall (fun x => Z.even x = false) (ChessTargets first count)) /\
  (first = 2 -> Forall (fun x => Z.even x = true) (ChessTargets first count)).
Proof.
  intros first count.
  assert (Hpar : Forall (fun x => Z.even x = Z.even first)
                    (ChessTargets first count)).
  { rewrite Forall_forall. intros x Hin.
    rewrite ChessTargets_In in Hin. destruct Hin as [k [Hk ->]].
    rewrite Z.even_add, Z.even_mul. simpl.
    destruct (Z.even first); reflexivity. }
  split; intros ->; exact Hpar.
Qed.

Lemma ChessZipCost_nonneg : forall a b, 0 <= ChessZipCost a b.
Proof.
  induction a as [|x a IH]; intros [|y b]; simpl; try lia.
  pose proof (Z.abs_nonneg (x - y)). specialize (IH b). lia.
Qed.

Lemma ChessZipCost_zero : forall a b,
  length a = length b -> ChessZipCost a b = 0 -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] Hlen Hcost; simpl in *;
    try discriminate; auto.
  assert (Z.abs (x - y) = 0) by
    (pose proof (ChessZipCost_nonneg a b); lia).
  apply Z.abs_0_iff in H. assert (x = y) by lia. subst y.
  f_equal. apply IH; lia.
Qed.

Lemma ChessZipCost_self : forall l, ChessZipCost l l = 0.
Proof.
  induction l as [|x xs IH]; simpl; auto.
  rewrite Z.sub_diag, Z.abs_0, IH. lia.
Qed.

Lemma ChessZipCost_targets : forall sorted first count,
  Zlength sorted = Z.of_nat count ->
  ChessZipCost sorted (ChessTargets first count) =
  sum (fun i : Z => 0 <= i < Z.of_nat count)
      (fun i => Z.abs (Znth i sorted 0 - (first + 2 * i))).
Proof.
  induction sorted as [|x xs IH]; intros first count Hlen;
    destruct count as [|count].
  - simpl. rewrite sum_Z_range_empty by lia. reflexivity.
  - rewrite Zlength_nil, Nat2Z.inj_succ in Hlen. lia.
  - rewrite Zlength_cons in Hlen. pose proof (Zlength_nonneg xs). lia.
  - rewrite Zlength_cons, Nat2Z.inj_succ in Hlen.
  assert (Htail : Zlength xs = Z.of_nat count) by lia.
  simpl.
  change (Z.abs (x - first) +
          ChessZipCost xs (ChessTargets (first + 2) count) =
          sum (fun i : Z => 0 <= i < Z.of_nat (S count))
              (fun i => Z.abs (Znth i (x :: xs) 0 - (first + 2 * i)))).
  rewrite Nat2Z.inj_succ.
  rewrite sum_Z_range_cons by lia.
  rewrite Znth0_cons.
  replace (first + 2 * 0) with first by ring.
  f_equal.
  change (fun z : Z => 1 <= z < Z.of_nat count + 1) with
    (fun z : Z => 0 + 1 <= z < Z.of_nat count + 1).
  replace (Z.succ (Z.of_nat count)) with (Z.of_nat count + 1) by lia.
  rewrite sum_Z_range_shift_1.
  rewrite IH by exact Htail.
  apply sum_Z_range_ext. intros i Hi.
  rewrite Znth_cons by lia.
  replace (i + 1 - 1) with i by lia.
  f_equal. lia.
Qed.

Lemma ChessZipCost_odd_even : forall sorted half odd even,
  0 <= half -> Zlength sorted = half ->
  ChessCostPrefix sorted half odd even ->
  odd = ChessZipCost sorted (ChessTargets 1 (Z.to_nat half)) /\
  even = ChessZipCost sorted (ChessTargets 2 (Z.to_nat half)).
Proof.
  intros sorted half odd even Hhalf Hlen [Hodd Heven].
  split.
  - rewrite ChessZipCost_targets by (rewrite Z2Nat.id by lia; exact Hlen).
    rewrite Z2Nat.id by lia. unfold OddTarget in Hodd. rewrite Hodd.
    apply sum_Z_range_ext. intros i Hi. f_equal. ring.
  - rewrite ChessZipCost_targets by (rewrite Z2Nat.id by lia; exact Hlen).
    rewrite Z2Nat.id by lia. unfold EvenTarget in Heven. rewrite Heven.
    apply sum_Z_range_ext. intros i Hi. f_equal. ring.
Qed.

Lemma PieceMove_length : forall n a b,
  PieceMove n a b -> Zlength b = Zlength a.
Proof.
  intros n a b [i [d [Hi [_ [_ [_ ->]]]]]].
  rewrite ListLib.Zlength_replace_Znth. reflexivity.
Qed.

Lemma PieceMove_preserves_bounds : forall n a b,
  PieceMove n a b ->
  Forall (fun x => 1 <= x <= n) a ->
  Forall (fun x => 1 <= x <= n) b.
Proof.
  intros n a b [i [d [Hi [_ [Hnew [_ ->]]]]]] Hall.
  apply (proj2 (Forall_Znth (fun x => 1 <= x <= n) 0 _)).
  intros j Hj. rewrite ListLib.Zlength_replace_Znth in Hj.
  destruct (Z.eq_dec j i) as [-> | Hne].
  - rewrite Znth_replace_Znth_Same by exact Hi. exact Hnew.
  - rewrite Znth_replace_Znth_Diff by (try exact Hi; try exact Hj; lia).
    apply (proj1 (Forall_Znth (fun x => 1 <= x <= n) 0 a) Hall). exact Hj.
Qed.

Lemma Chess_replace_nth_In : forall (l : list Z) k v x,
  In x (replace_nth k l v) -> x = v \/ In x l.
Proof.
  induction l as [|a l IH]; intros [|k] v x Hin; simpl in *.
  - contradiction.
  - contradiction.
  - destruct Hin as [H | H].
    + left. symmetry. exact H.
    + right. right. exact H.
  - destruct Hin as [-> | Hin]; [tauto |].
    specialize (IH k v x Hin). tauto.
Qed.

Lemma Chess_replace_nth_NoDup : forall (l : list Z) k v,
  ~ In v l -> NoDup l -> NoDup (replace_nth k l v).
Proof.
  induction l as [|a l IH]; intros [|k] v Hfresh Hnd; simpl; auto.
  - inversion Hnd as [|? ? Hnotin Htail]; subst. constructor.
    + intro Hin. apply Hfresh. right. exact Hin.
    + exact Htail.
  - inversion Hnd as [|? ? Hnotin Htail]; subst.
    constructor.
    + intro Hin. apply Chess_replace_nth_In in Hin.
      destruct Hin as [Hav | Hin].
      * apply Hfresh. left. exact Hav.
      * apply Hnotin. exact Hin.
    + apply IH.
      * intro Hin. apply Hfresh. right. exact Hin.
      * exact Htail.
Qed.

Lemma PieceMove_preserves_NoDup : forall n a b,
  PieceMove n a b -> NoDup a -> NoDup b.
Proof.
  intros n a b [i [d [Hi [_ [_ [Hfresh ->]]]]]] Hnd.
  unfold replace_Znth. apply Chess_replace_nth_NoDup; assumption.
Qed.

Lemma Chess_replace_at_split : forall (pre suf : list Z) x v,
  replace_Znth (Zlength pre) v (pre ++ x :: suf) = pre ++ v :: suf.
Proof.
  induction pre as [|a pre IH]; intros suf x v.
  - simpl. reflexivity.
  - cbn [app]. rewrite Zlength_cons. rewrite replace_Znth_cons by
      (pose proof (Zlength_nonneg pre); lia).
    replace (Z.succ (Zlength pre) - 1) with (Zlength pre) by lia.
    simpl. rewrite IH. reflexivity.
Qed.

Lemma Chess_split_Znth : forall (l : list Z) i,
  0 <= i < Zlength l ->
  exists pre suf, l = pre ++ Znth i l 0 :: suf /\ Zlength pre = i.
Proof.
  intros l i Hi.
  unfold Znth. rewrite Zlength_correct in Hi.
  destruct (nth_split (n := Z.to_nat i) l 0) as [pre [suf [Hl Hpre]]].
  - lia.
  - exists pre, suf. split; [exact Hl |].
    rewrite Zlength_correct, Hpre, Z2Nat.id by lia. reflexivity.
Qed.

Lemma PieceMove_transport : forall n source source' base,
  NoDup source -> Permutation base source -> PieceMove n source source' ->
  exists base', PieceMove n base base' /\ Permutation base' source'.
Proof.
  intros n source source' base Hnd Hperm
    [i [d [Hi [Hd [Hbound [Hfresh Hsource']]]]]].
  set (old := Znth i source 0) in *.
  set (new := old + d) in *.
  destruct (Chess_split_Znth source i Hi) as [sp [ss [Hs Hslen]]].
  assert (Hs_old : source = sp ++ old :: ss).
  { unfold old. exact Hs. }
  assert (Hinold_source : In old source).
  { subst old. apply Znth_In_Zlength. exact Hi. }
  assert (Hinold_base : In old base).
  { eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hinold_source]. }
  destruct (in_split old base Hinold_base) as [bp [bs Hb]].
  assert (Hfresh_base : ~ In new base).
  { intro Hin. apply Hfresh. eapply Permutation_in; [exact Hperm | exact Hin]. }
  exists (bp ++ new :: bs). split.
  - exists (Zlength bp), d. split.
    + split; [apply Zlength_nonneg |].
      rewrite Hb, Zlength_app, Zlength_cons. pose proof (Zlength_nonneg bs). lia.
    + split; [exact Hd |]. split.
      * rewrite Hb, app_Znth2 by lia.
        replace (Zlength bp - Zlength bp) with 0 by lia.
        rewrite Znth0_cons. exact Hbound.
      * split.
        -- rewrite Hb, app_Znth2 by lia.
           replace (Zlength bp - Zlength bp) with 0 by lia.
           rewrite Znth0_cons. unfold new in Hfresh_base.
           rewrite Hb in Hfresh_base. exact Hfresh_base.
        -- rewrite Hb, app_Znth2 by lia.
           replace (Zlength bp - Zlength bp) with 0 by lia.
           rewrite Znth0_cons. symmetry. apply Chess_replace_at_split.
  - subst source'.
    rewrite Hs. rewrite <- Hslen. rewrite Chess_replace_at_split.
    assert (Hrem : Permutation (bp ++ bs) (sp ++ ss)).
    { assert (Hperm_mid : Permutation (bp ++ old :: bs) (sp ++ old :: ss)).
      { rewrite <- Hb, <- Hs_old. exact Hperm. }
      apply (Permutation_cons_inv (a := old)).
      eapply Permutation_trans.
      - apply Permutation_middle.
      - eapply Permutation_trans; [exact Hperm_mid |].
        apply Permutation_sym, Permutation_middle. }
    eapply Permutation_trans.
    + apply Permutation_sym, Permutation_middle.
    + eapply Permutation_trans.
      * apply perm_skip. exact Hrem.
      * apply Permutation_middle.
Qed.

Lemma ChessMoves_preserves_NoDup : forall n k a b,
  ChessMoves n k a b -> NoDup a -> NoDup b.
Proof.
  intros n k a b Hmoves. induction Hmoves; intros Hnd; auto.
  apply IHHmoves. eapply PieceMove_preserves_NoDup; eauto.
Qed.

Lemma ChessMoves_preserves_bounds : forall n k a b,
  ChessMoves n k a b ->
  Forall (fun x => 1 <= x <= n) a ->
  Forall (fun x => 1 <= x <= n) b.
Proof.
  intros n k a b Hmoves. induction Hmoves; intros Hall; auto.
  apply IHHmoves. eapply PieceMove_preserves_bounds; eauto.
Qed.

Lemma ChessMoves_transport : forall n k source final base,
  ChessMoves n k source final -> NoDup source -> Permutation base source ->
  exists base_final,
    ChessMoves n k base base_final /\ Permutation base_final final.
Proof.
  intros n k source final base Hmoves.
  revert base. induction Hmoves; intros base Hnd Hperm.
  - exists base. split; [constructor | exact Hperm].
  - destruct (PieceMove_transport n a b base Hnd Hperm)
      as [base' [Hstep Hperm']]; auto.
    assert (Hndb : NoDup b) by (eapply PieceMove_preserves_NoDup; eauto).
    destruct (IHHmoves base' Hndb Hperm') as [base_final [Htail Hfinal]].
    exists base_final. split; [econstructor; eauto | exact Hfinal].
Qed.

Lemma ChessMoves_snoc : forall n k a b c,
  ChessMoves n k a b -> PieceMove n b c -> ChessMoves n (S k) a c.
Proof.
  intros n k a b c Hmoves Hstep.
  induction Hmoves.
  - econstructor; [exact Hstep | constructor].
  - econstructor; eauto.
Qed.

Lemma Chess_states_to_moves : forall n states k,
  Z.of_nat k < Zlength states ->
  (forall i, 0 <= i < Z.of_nat k ->
    PieceMove n (Znth i states []) (Znth (i + 1) states [])) ->
  ChessMoves n k (Znth 0 states []) (Znth (Z.of_nat k) states []).
Proof.
  intros n states k. induction k as [|k IH]; intros Hlen Hsteps.
  - constructor.
  - rewrite Nat2Z.inj_succ in Hlen.
    apply ChessMoves_snoc with (b := Znth (Z.of_nat k) states []).
    + apply IH; [lia |]. intros i Hi. apply Hsteps. lia.
    + replace (Z.of_nat (S k)) with (Z.of_nat k + 1)
        by (rewrite Nat2Z.inj_succ; lia).
      apply Hsteps. lia.
Qed.

Lemma CanPlaceIn_to_ChessMoves : forall n moves start,
  0 <= moves -> CanPlaceIn n moves start ->
  exists final,
    ChessMoves n (Z.to_nat moves) start final /\ SameColor final.
Proof.
  intros n moves start Hmoves
    [states [Hlen [Hstart [Hsteps Hcolor]]]].
  exists (Znth moves states []). split.
  - rewrite <- Hstart.
    replace moves with (Z.of_nat (Z.to_nat moves)) at 2 by
      (rewrite Z2Nat.id; lia).
    apply Chess_states_to_moves.
    + rewrite Hlen, Z2Nat.id by lia. lia.
    + intros i Hi. apply Hsteps. rewrite Z2Nat.id in Hi by lia. exact Hi.
  - exact Hcolor.
Qed.

Lemma ChessMoves_to_states : forall n k a b,
  ChessMoves n k a b ->
  exists states,
    Zlength states = Z.of_nat k + 1 /\
    Znth 0 states [] = a /\
    (forall i, 0 <= i < Z.of_nat k ->
      PieceMove n (Znth i states []) (Znth (i + 1) states [])) /\
    Znth (Z.of_nat k) states [] = b.
Proof.
  intros n k a b Hmoves. induction Hmoves.
  - exists [a]. split.
    + reflexivity.
    + split.
      * reflexivity.
      * split.
        -- intros i Hi. lia.
        -- reflexivity.
  - destruct IHHmoves as [states [Hlen [Hhead [Hsteps Hlast]]]].
    exists (a :: states). split.
    + rewrite Zlength_cons, Hlen, Nat2Z.inj_succ. lia.
    + split.
      * reflexivity.
      * split.
        -- intros i Hi. destruct (Z.eq_dec i 0) as [-> | Hne].
           ++ rewrite Znth0_cons, Znth_cons by lia.
              replace (0 + 1 - 1) with 0 by lia. rewrite Hhead. exact H.
           ++ rewrite !Znth_cons by lia.
              replace (i + 1 - 1) with ((i - 1) + 1) by lia.
              apply Hsteps. rewrite Nat2Z.inj_succ in Hi. lia.
        -- rewrite Nat2Z.inj_succ. rewrite Znth_cons by lia.
           replace (Z.succ (Z.of_nat k) - 1) with (Z.of_nat k) by lia.
           exact Hlast.
Qed.

Lemma ChessMoves_to_CanPlaceIn : forall n k a b,
  ChessMoves n k a b -> SameColor b -> CanPlaceIn n (Z.of_nat k) a.
Proof.
  intros n k a b Hmoves Hcolor.
  destruct (ChessMoves_to_states n k a b Hmoves)
    as [states [Hlen [Hstart [Hsteps Hend]]]].
  exists states. split; [exact Hlen |].
  split; [exact Hstart |]. split; [exact Hsteps |].
  rewrite Hend. exact Hcolor.
Qed.

Lemma Chess_abs_neighbor : forall x y d,
  d = -1 \/ d = 1 -> Z.abs (x - y) <= 1 + Z.abs (x + d - y).
Proof.
  intros x y d Hd.
  destruct (Z_le_gt_dec 0 (x - y));
  destruct (Z_le_gt_dec 0 (x + d - y));
  destruct Hd as [-> | ->];
  rewrite ?Z.abs_eq, ?Z.abs_neq by lia; lia.
Qed.

Lemma ChessZipCost_replace_step : forall a target k d,
  length a = length target ->
  (k < length a)%nat ->
  d = -1 \/ d = 1 ->
  ChessZipCost a target <=
    1 + ChessZipCost
          (replace_nth k a (nth k a 0 + d)) target.
Proof.
  induction a as [|x xs IH]; intros [|y ys] [|k] d Hlen Hk Hd;
    simpl in *; try lia.
  - change (Z.abs (x - y) + ChessZipCost xs ys <=
            1 + (Z.abs (x + d - y) + ChessZipCost xs ys)).
    pose proof (Chess_abs_neighbor x y d Hd). lia.
  - apply Nat.succ_inj in Hlen.
    apply Nat.succ_lt_mono in Hk.
    specialize (IH ys k d Hlen Hk Hd).
    change (ChessZipCost xs ys <=
      1 + ChessZipCost (replace_nth k xs (nth k xs 0 + d)) ys) in IH.
    change (Z.abs (x - y) + ChessZipCost xs ys <=
      1 + (Z.abs (x - y) +
        ChessZipCost (replace_nth k xs (nth k xs 0 + d)) ys)).
    lia.
Qed.

Lemma PieceMove_cost_lower : forall n a b target,
  PieceMove n a b ->
  length a = length target ->
  ChessZipCost a target <= 1 + ChessZipCost b target.
Proof.
  intros n a b target [i [d [Hi [Hd [_ [_ ->]]]]]] Hlen.
  unfold replace_Znth, Znth.
  apply ChessZipCost_replace_step; auto.
  rewrite Zlength_correct in Hi.
  apply Nat2Z.inj_lt.
  rewrite Z2Nat.id by lia. exact (proj2 Hi).
Qed.

Lemma ChessMoves_length : forall n k a b,
  ChessMoves n k a b -> length b = length a.
Proof.
  intros n k a b Hmoves. induction Hmoves; auto.
  pose proof (PieceMove_length n a b H) as Hstep_len.
  rewrite !Zlength_correct in Hstep_len. lia.
Qed.

Lemma ChessMoves_cost_lower : forall n k a b target,
  ChessMoves n k a b ->
  length a = length target ->
  ChessZipCost a target <= Z.of_nat k + ChessZipCost b target.
Proof.
  intros n k a b target Hmoves. induction Hmoves; intros Hlen.
  - simpl. lia.
  - assert (Hlenb : length b = length target).
    { pose proof (PieceMove_length n a b H) as Hstep_len.
      rewrite !Zlength_correct in Hstep_len. lia. }
    specialize (IHHmoves Hlenb).
    pose proof (PieceMove_cost_lower n a b target H Hlen) as Hstep_cost.
    rewrite Nat2Z.inj_succ.
    lia.
Qed.

Lemma Chess_odd_in_targets : forall half l,
  0 <= half ->
  Forall (fun x => 1 <= x <= 2 * half) l ->
  Forall (fun x => Z.even x = false) l ->
  incl l (ChessTargets 1 (Z.to_nat half)).
Proof.
  intros half l Hhalf Hbounds Hodd x Hin.
  rewrite Forall_forall in Hbounds, Hodd.
  specialize (Hbounds x Hin). specialize (Hodd x Hin).
  assert (Hodd' : Z.odd x = true).
  { rewrite <- Z.negb_even, Hodd. reflexivity. }
  apply Z.odd_spec in Hodd'. destruct Hodd' as [k Hx].
  rewrite ChessTargets_In. exists k.
  rewrite Z2Nat.id by lia. split; [lia | lia].
Qed.

Lemma Chess_even_in_targets : forall half l,
  0 <= half ->
  Forall (fun x => 1 <= x <= 2 * half) l ->
  Forall (fun x => Z.even x = true) l ->
  incl l (ChessTargets 2 (Z.to_nat half)).
Proof.
  intros half l Hhalf Hbounds Heven x Hin.
  rewrite Forall_forall in Hbounds, Heven.
  specialize (Hbounds x Hin). specialize (Heven x Hin).
  apply Z.even_spec in Heven. destruct Heven as [k Hx].
  rewrite ChessTargets_In. exists (k - 1).
  rewrite Z2Nat.id by lia. split; [lia | lia].
Qed.

Lemma Chess_same_color_targets : forall half l,
  0 <= half ->
  Zlength l = half ->
  Forall (fun x => 1 <= x <= 2 * half) l ->
  NoDup l ->
  SameColor l ->
  Permutation l (ChessTargets 1 (Z.to_nat half)) \/
  Permutation l (ChessTargets 2 (Z.to_nat half)).
Proof.
  intros half l Hhalf Hlen Hbounds Hnd [Heven | Hodd].
  - right. apply NoDup_Permutation_bis; [exact Hnd | |].
    + rewrite ChessTargets_length. rewrite Zlength_correct in Hlen.
      rewrite <- Hlen, Nat2Z.id. apply Nat.le_refl.
    + eapply Chess_even_in_targets; eauto.
  - left. apply NoDup_Permutation_bis; [exact Hnd | |].
    + rewrite ChessTargets_length. rewrite Zlength_correct in Hlen.
      rewrite <- Hlen, Nat2Z.id. apply Nat.le_refl.
    + eapply Chess_odd_in_targets; eauto.
Qed.

Lemma Chess_abs_uncross : forall x x' y y',
  x <= x' -> y <= y' ->
  Z.abs (x - y) + Z.abs (x' - y') <=
  Z.abs (x - y') + Z.abs (x' - y).
Proof.
  intros x x' y y' Hx Hy.
  destruct (Z_le_gt_dec 0 (x - y));
  destruct (Z_le_gt_dec 0 (x' - y'));
  destruct (Z_le_gt_dec 0 (x - y'));
  destruct (Z_le_gt_dec 0 (x' - y));
  rewrite ?Z.abs_eq, ?Z.abs_neq by lia; lia.
Qed.

Lemma Chess_bubble_min : forall pre a suf y,
  mono_nondec a ->
  length a = length (pre ++ y :: suf) ->
  Forall (fun z => y <= z) pre ->
  ChessZipCost a (y :: pre ++ suf) <=
  ChessZipCost a (pre ++ y :: suf).
Proof.
  induction pre as [|z pre IH]; intros a suf y Hmono Hlen Hall.
  - simpl. apply Z.le_refl.
  - destruct a as [|x xs]; simpl in Hlen; [discriminate |].
    destruct xs as [|x' xs].
    + rewrite length_app in Hlen. simpl in Hlen. lia.
    + simpl in Hlen.
    inversion Hall as [|? ? Hyz Hallpre]; subst.
    pose proof (proj1 (mono_nondec_cons x (x' :: xs)) Hmono)
      as [Hxall Hmono_tail].
    inversion Hxall as [|? ? Hxx' _]; subst.
    assert (Htail_len : length (x' :: xs) = length (pre ++ y :: suf)).
    { simpl in *. lia. }
    specialize (IH (x' :: xs) suf y Hmono_tail Htail_len Hallpre).
    simpl in *.
    pose proof (Chess_abs_uncross x x' y z Hxx' Hyz) as Hcross.
    lia.
Qed.

Lemma ChessZipCost_sorted_min : forall target a q,
  mono_inc target ->
  mono_nondec a ->
  length a = length target ->
  Permutation target q ->
  ChessZipCost a target <= ChessZipCost a q.
Proof.
  induction target as [|y ys IH]; intros a q Htarget Ha Hlen Hperm.
  - apply Permutation_nil in Hperm. subst q.
    destruct a; simpl in Hlen; [reflexivity | discriminate].
  - destruct a as [|x xs]; simpl in Hlen; [discriminate |].
    assert (Hinyq : In y q).
    { eapply Permutation_in; [exact Hperm |]. simpl. auto. }
    destruct (in_split y q Hinyq) as [pre [suf Hq]]. subst q.
    pose proof (proj1 (mono_inc_cons y ys) Htarget)
      as [Hyall Htarget_tail].
    pose proof (proj1 (mono_nondec_cons x xs) Ha)
      as [_ Ha_tail].
    assert (Hpre : Forall (fun z => y <= z) pre).
    { rewrite Forall_forall. intros z Hz.
      assert (Hzq : In z (pre ++ y :: suf)).
      { apply in_or_app. left. exact Hz. }
      assert (Hzt : In z (y :: ys)).
      { eapply Permutation_in; [apply Permutation_sym; exact Hperm | exact Hzq]. }
      destruct Hzt as [-> | Hzys]; [lia |].
      rewrite Forall_forall in Hyall. specialize (Hyall z Hzys). lia. }
    assert (Hrem : Permutation ys (pre ++ suf)).
    { apply (Permutation_cons_inv (a := y)).
      eapply Permutation_trans; [exact Hperm |].
      apply Permutation_sym, Permutation_middle. }
    assert (Htail_len : length xs = length ys) by lia.
    specialize (IH xs (pre ++ suf) Htarget_tail Ha_tail Htail_len Hrem).
    assert (Hbubble :
      ChessZipCost (x :: xs) (y :: pre ++ suf) <=
      ChessZipCost (x :: xs) (pre ++ y :: suf)).
    { apply Chess_bubble_min; auto.
      pose proof (Permutation_length Hrem) as Hrem_len.
      rewrite !length_app in Hrem_len |- *. simpl in *. lia. }
    simpl in *. lia.
Qed.

Lemma PieceMove_cons_lower : forall n x a b,
  PieceMove n a b ->
  Forall (fun y => x < y) b ->
  PieceMove n (x :: a) (x :: b).
Proof.
  intros n x a b [i [d [Hi [Hd [Hbound [Hfresh ->]]]]]] Hlow.
  set (new := Znth i a 0 + d) in *.
  assert (Hnew_in : In new (replace_Znth i new a)).
  { pose proof (Znth_In_Zlength (replace_Znth i new a) 0 i) as Hin.
    rewrite ListLib.Zlength_replace_Znth in Hin.
    specialize (Hin Hi).
    rewrite Znth_replace_Znth_Same in Hin by exact Hi. exact Hin. }
  rewrite Forall_forall in Hlow. specialize (Hlow new Hnew_in).
  exists (i + 1), d. split.
  - rewrite Zlength_cons. lia.
  - split; [exact Hd |]. split.
    + rewrite Znth_cons by lia.
      replace (i + 1 - 1) with i by lia. exact Hbound.
    + split.
      * rewrite Znth_cons by lia.
        replace (i + 1 - 1) with i by lia.
        simpl. intros [Heq | Hin].
        -- lia.
        -- exact (Hfresh Hin).
      * rewrite Znth_cons by lia.
        replace (i + 1 - 1) with i by lia.
        rewrite replace_Znth_cons by lia.
        replace (i + 1 - 1) with i by lia. reflexivity.
Qed.

Lemma Chess_Forall_succ_strict : forall x n l,
  Forall (fun y => x + 1 <= y <= n) l ->
  Forall (fun y => x < y) l.
Proof.
  intros x n l Hall. induction Hall; constructor; auto; lia.
Qed.

Lemma Chess_Forall_weaken_lower : forall lo mid n l,
  lo <= mid ->
  Forall (fun y => mid <= y <= n) l ->
  Forall (fun y => lo <= y <= n) l.
Proof.
  intros lo mid n l Hle Hall. induction Hall; constructor; auto; lia.
Qed.

Lemma Chess_Forall_strict_weaken : forall lo mid l,
  lo <= mid ->
  Forall (fun y => mid < y) l ->
  Forall (fun y => lo < y) l.
Proof.
  intros lo mid l Hle Hall. induction Hall; constructor; auto; lia.
Qed.

Lemma Chess_step_toward : forall count s first n lo,
  length s = count ->
  mono_inc s ->
  Forall (fun x => lo <= x <= n) s ->
  1 <= lo -> lo <= first ->
  first + 2 * Z.of_nat count <= n + 2 ->
  s <> ChessTargets first count ->
  exists s',
    PieceMove n s s' /\
    mono_inc s' /\
    Forall (fun x => lo <= x <= n) s' /\
    ChessZipCost s' (ChessTargets first count) =
      ChessZipCost s (ChessTargets first count) - 1.
Proof.
  induction count as [|count IH]; intros s first n lo Hlen Hinc Hbounds
    Hlo Hfirst Hcap Hneq.
  - destruct s; simpl in Hlen; [exfalso; apply Hneq; reflexivity | discriminate].
  - destruct s as [|x xs]; simpl in Hlen; [discriminate |].
    assert (Hlen_tail : length xs = count) by lia.
    pose proof (proj1 (mono_inc_cons x xs) Hinc) as [Hxall Hinc_tail].
    inversion Hbounds as [|x' xs' Hxbounds Hbounds_tail]; subst x' xs'.
    assert (Htail_lower : Forall (fun y => x + 1 <= y <= n) xs).
    { rewrite Forall_forall in Hxall, Hbounds_tail |- *.
      intros y Hy. specialize (Hxall y Hy). specialize (Hbounds_tail y Hy). lia. }
    assert (Hfirst_n : first <= n).
    { pose proof Hcap as Hcap'. rewrite Nat2Z.inj_succ in Hcap'.
      pose proof (Nat2Z.is_nonneg count). lia. }
    destruct (Z.lt_trichotomy x first) as [Hlt | [Heq | Hgt]].
    + destruct xs as [|z zs].
      * exists [x + 1]. split.
        -- exists 0, 1. split; [rewrite Zlength_cons, Zlength_nil; lia |].
           split; [right; reflexivity |]. split.
           ++ change (1 <= x + 1 <= n). lia.
           ++ split.
              ** change (~ In (x + 1) [x]). simpl. lia.
              ** reflexivity.
        -- split.
           ++ apply mono_inc_single.
           ++ split.
              ** constructor; [lia | constructor].
              ** simpl. rewrite !Z.abs_neq by lia. lia.
      * destruct (Z.eq_dec z (x + 1)) as [Hz | Hz].
        -- assert (Htail_neq : z :: zs <> ChessTargets (first + 2) count).
           { intro Heqtail.
             assert (Hzin : In z (ChessTargets (first + 2) count)).
             { rewrite <- Heqtail. simpl. auto. }
             rewrite ChessTargets_In in Hzin.
             destruct Hzin as [k [Hk Hzk]]. lia. }
           destruct (IH (z :: zs) (first + 2) n (x + 1) Hlen_tail Hinc_tail
             Htail_lower ltac:(lia) ltac:(lia) ltac:(rewrite Nat2Z.inj_succ in Hcap; lia)
             Htail_neq) as [tail' [Hstep [Hinc' [Hbounds' Hcost]]]].
           exists (x :: tail'). split.
           ++ apply PieceMove_cons_lower; [exact Hstep |].
              apply Chess_Forall_succ_strict with (n := n). exact Hbounds'.
           ++ split.
              ** apply (proj2 (mono_inc_cons x tail')). split.
                 --- apply Chess_Forall_succ_strict with (n := n). exact Hbounds'.
                 --- exact Hinc'.
              ** split.
                 --- constructor; [exact Hxbounds |].
                     apply Chess_Forall_weaken_lower with (mid := x + 1);
                       [lia | exact Hbounds'].
                 --- simpl in Hcost |- *. lia.
        -- exists ((x + 1) :: z :: zs). split.
           ++ exists 0, 1. split.
              ** rewrite Zlength_cons. pose proof (Zlength_nonneg (z :: zs)). lia.
              ** split; [right; reflexivity |]. split.
                 --- change (1 <= x + 1 <= n). lia.
                 --- split.
                     +++ change (~ In (x + 1) (x :: z :: zs)).
                     simpl. intro Hin. destruct Hin as [He | Hin]; [lia |].
                     destruct Hin as [He | Hin].
                     { apply Hz. exact He. }
                     pose proof (Forall_inv Hxall) as Hxz.
                     pose proof (proj1 (mono_inc_cons z zs) Hinc_tail)
                       as [Hzall _].
                     rewrite Forall_forall in Hzall.
                     specialize (Hzall (x + 1) Hin).
                     pose proof (Zlt_le_succ x z Hxz) as Hsucc.
                     change (x + 1 <= z) in Hsucc.
                     exact (Z.lt_irrefl z (Z.lt_le_trans _ _ _ Hzall Hsucc)).
                     +++ reflexivity.
           ++ split.
              ** apply (proj2 (mono_inc_cons (x + 1) (z :: zs))). split.
                 --- pose proof (Forall_inv Hxall) as Hxz.
                     pose proof (Zlt_le_succ x z Hxz) as Hsucc.
                     change (x + 1 <= z) in Hsucc.
                     assert (Hnewz : x + 1 < z).
                     { destruct (proj1 (Z.lt_eq_cases _ _) Hsucc) as [Hltz | Heqz].
                       - exact Hltz.
                       - exfalso. apply Hz. symmetry. exact Heqz. }
                     pose proof (proj1 (mono_inc_cons z zs) Hinc_tail)
                       as [Hzall _].
                     constructor; [exact Hnewz |].
                     eapply Forall_impl; [|exact Hzall].
                     intros y Hy. eapply Z.lt_trans; eauto.
                 --- exact Hinc_tail.
              ** split.
                 --- constructor; [lia | exact Hbounds_tail].
                 --- simpl. rewrite !Z.abs_neq by lia. lia.
    + subst x.
      assert (Htail_neq : xs <> ChessTargets (first + 2) count).
      { intro Heqtail. apply Hneq. simpl. f_equal. exact Heqtail. }
      destruct (IH xs (first + 2) n (first + 1) Hlen_tail Hinc_tail
        Htail_lower ltac:(lia) ltac:(lia) ltac:(rewrite Nat2Z.inj_succ in Hcap; lia)
        Htail_neq) as [tail' [Hstep [Hinc' [Hbounds' Hcost]]]].
      exists (first :: tail'). split.
      * apply PieceMove_cons_lower; [exact Hstep |].
        apply Chess_Forall_succ_strict with (n := n). exact Hbounds'.
      * split.
        -- apply (proj2 (mono_inc_cons first tail')). split.
           ++ apply Chess_Forall_succ_strict with (n := n). exact Hbounds'.
           ++ exact Hinc'.
        -- split.
           ++ constructor; [exact Hxbounds |].
              apply Chess_Forall_weaken_lower with (mid := first + 1);
                [lia | exact Hbounds'].
           ++ simpl in Hcost |- *. lia.
    + exists ((x - 1) :: xs). split.
      * exists 0, (-1). split.
        -- rewrite Zlength_cons. pose proof (Zlength_nonneg xs). lia.
        -- split; [left; reflexivity |]. split.
           ++ change (1 <= x - 1 <= n). lia.
           ++ split.
              ** change (~ In (x - 1) (x :: xs)).
                 simpl. intro Hin. destruct Hin as [He | Hin]; [lia |].
                 rewrite Forall_forall in Hxall.
                 specialize (Hxall (x - 1) Hin). lia.
              ** reflexivity.
      * split.
        -- apply (proj2 (mono_inc_cons (x - 1) xs)). split.
           ++ apply Chess_Forall_strict_weaken with (mid := x);
                [lia | exact Hxall].
           ++ exact Hinc_tail.
        -- split.
           ++ constructor; [lia | exact Hbounds_tail].
           ++ simpl. rewrite !Z.abs_eq by lia. lia.
Qed.

Lemma Chess_moves_to_targets_fuel : forall fuel count s first n lo,
  length s = count ->
  mono_inc s ->
  Forall (fun x => lo <= x <= n) s ->
  1 <= lo -> lo <= first ->
  first + 2 * Z.of_nat count <= n + 2 ->
  Z.to_nat (ChessZipCost s (ChessTargets first count)) = fuel ->
  exists k,
    Z.of_nat k = ChessZipCost s (ChessTargets first count) /\
    ChessMoves n k s (ChessTargets first count).
Proof.
  induction fuel as [|fuel IH]; intros count s first n lo Hlen Hinc Hbounds
    Hlo Hfirst Hcap Hfuel.
  - assert (Hcost_nonneg : 0 <= ChessZipCost s (ChessTargets first count))
      by apply ChessZipCost_nonneg.
    assert (Hcost_zero : ChessZipCost s (ChessTargets first count) = 0).
    { rewrite <- (Z2Nat.id _ Hcost_nonneg). rewrite Hfuel. reflexivity. }
    assert (Hs : s = ChessTargets first count).
    { apply ChessZipCost_zero; [rewrite ChessTargets_length; exact Hlen | exact Hcost_zero]. }
    subst s. exists O. split; [simpl; symmetry; exact Hcost_zero | constructor].
  - assert (Hcost_nonneg : 0 <= ChessZipCost s (ChessTargets first count))
      by apply ChessZipCost_nonneg.
    assert (Hcost_nat :
      ChessZipCost s (ChessTargets first count) = Z.of_nat (S fuel)).
    { rewrite <- Hfuel. symmetry. apply Z2Nat.id. exact Hcost_nonneg. }
    assert (Hneq : s <> ChessTargets first count).
    { intro Heq. subst s. rewrite ChessZipCost_self in Hcost_nat. lia. }
    destruct (Chess_step_toward count s first n lo Hlen Hinc Hbounds Hlo
      Hfirst Hcap Hneq) as [s' [Hstep [Hinc' [Hbounds' Hstepcost]]]].
    assert (Hlen' : length s' = count).
    { pose proof (PieceMove_length n s s' Hstep) as Hmove_len.
      rewrite !Zlength_correct in Hmove_len. lia. }
    assert (Hfuel' :
      Z.to_nat (ChessZipCost s' (ChessTargets first count)) = fuel).
    { rewrite Hstepcost, Hcost_nat, Nat2Z.inj_succ.
      replace (Z.succ (Z.of_nat fuel) - 1) with (Z.of_nat fuel) by lia.
      apply Nat2Z.id. }
    destruct (IH count s' first n lo Hlen' Hinc' Hbounds' Hlo Hfirst Hcap
      Hfuel') as [k [Hk Hmoves]].
    exists (S k). split.
    + rewrite Nat2Z.inj_succ, Hk, Hstepcost. lia.
    + econstructor; eauto.
Qed.

Lemma Chess_moves_to_targets : forall count s first n lo,
  length s = count ->
  mono_inc s ->
  Forall (fun x => lo <= x <= n) s ->
  1 <= lo -> lo <= first ->
  first + 2 * Z.of_nat count <= n + 2 ->
  exists k,
    Z.of_nat k = ChessZipCost s (ChessTargets first count) /\
    ChessMoves n k s (ChessTargets first count).
Proof.
  intros count s first n lo Hlen Hinc Hbounds Hlo Hfirst Hcap.
  eapply Chess_moves_to_targets_fuel; eauto.
Qed.

Lemma mono_nondec_NoDup_inc : forall l,
  mono_nondec l -> NoDup l -> mono_inc l.
Proof.
  induction l as [|x xs IH]; intros Hmono Hnd; [apply mono_inc_nil |].
  pose proof (proj1 (mono_nondec_cons x xs) Hmono) as [Hxle Hmono_tail].
  inversion Hnd as [|? ? Hnotin Hndtail]; subst.
  apply (proj2 (mono_inc_cons x xs)). split.
  - rewrite Forall_forall in Hxle |- *. intros y Hy.
    specialize (Hxle y Hy).
    destruct (proj1 (Z.lt_eq_cases x y) Hxle) as [Hlt | Heq]; [exact Hlt |].
    exfalso. apply Hnotin. rewrite Heq. exact Hy.
  - apply IH; assumption.
Qed.

Lemma SameColor_Permutation : forall a b,
  Permutation a b -> SameColor a -> SameColor b.
Proof.
  intros a b Hperm [Heven | Hodd].
  - left. eapply Permutation_Forall; eauto.
  - right. eapply Permutation_Forall; eauto.
Qed.

Lemma Chess_target_reachable : forall half positions sorted first,
  0 <= half ->
  first = 1 \/ first = 2 ->
  Zlength sorted = half ->
  Forall (fun x => 1 <= x <= 2 * half) sorted ->
  mono_nondec sorted ->
  NoDup sorted ->
  Permutation positions sorted ->
  CanPlaceIn (2 * half)
    (ChessZipCost sorted (ChessTargets first (Z.to_nat half))) positions.
Proof.
  intros half positions sorted first Hhalf Hfirst Hlen Hbounds Hmono Hnd Hperm.
  assert (Hnatlen : length sorted = Z.to_nat half).
  { rewrite Zlength_correct in Hlen.
    apply Nat2Z.inj. rewrite Hlen, Z2Nat.id by lia. reflexivity. }
  assert (Hinc : mono_inc sorted) by (apply mono_nondec_NoDup_inc; assumption).
  destruct (Chess_moves_to_targets (Z.to_nat half) sorted first (2 * half) 1
    Hnatlen Hinc Hbounds ltac:(lia) ltac:(destruct Hfirst; lia)
    ltac:(rewrite Z2Nat.id by lia; destruct Hfirst; lia))
    as [k [Hk Hmoves]].
  destruct (ChessMoves_transport (2 * half) k sorted
    (ChessTargets first (Z.to_nat half)) positions Hmoves Hnd Hperm)
    as [final [Hmoves' Hfinalperm]].
  rewrite <- Hk. apply ChessMoves_to_CanPlaceIn with (b := final); [exact Hmoves' |].
  apply SameColor_Permutation with (a := ChessTargets first (Z.to_nat half)).
  - apply Permutation_sym. exact Hfinalperm.
  - destruct (ChessTargets_same_color first (Z.to_nat half)) as [Hodd Heven].
    destruct Hfirst as [-> | ->]; [right; apply Hodd; reflexivity | left; apply Heven; reflexivity].
Qed.

Lemma Chess_any_reachable_lower : forall half positions sorted d,
  0 <= half ->
  Zlength positions = half ->
  Forall (fun x => 1 <= x <= 2 * half) positions ->
  NoDup positions ->
  Permutation positions sorted ->
  mono_nondec sorted ->
  0 <= d ->
  CanPlaceIn (2 * half) d positions ->
  Z.min
    (ChessZipCost sorted (ChessTargets 1 (Z.to_nat half)))
    (ChessZipCost sorted (ChessTargets 2 (Z.to_nat half))) <= d.
Proof.
  intros half positions sorted d Hhalf Hlen Hbounds Hnd Hperm Hmono Hd Hcan.
  destruct (CanPlaceIn_to_ChessMoves (2 * half) d positions Hd Hcan)
    as [final [Hmoves Hcolor]].
  destruct (ChessMoves_transport (2 * half) (Z.to_nat d) positions final sorted
    Hmoves Hnd (Permutation_sym Hperm)) as [sorted_final [Hsortedmoves Hfinalperm]].
  assert (Hsorted_bounds : Forall (fun x => 1 <= x <= 2 * half) sorted).
  { eapply Permutation_Forall; eauto. }
  assert (Hsf_bounds : Forall (fun x => 1 <= x <= 2 * half) sorted_final).
  { eapply ChessMoves_preserves_bounds; eauto. }
  assert (Hsf_nd : NoDup sorted_final).
  { eapply ChessMoves_preserves_NoDup; [exact Hsortedmoves |].
    eapply Permutation_NoDup; eauto. }
  assert (Hsf_len : Zlength sorted_final = half).
  { pose proof (ChessMoves_length (2 * half) (Z.to_nat d) sorted sorted_final
      Hsortedmoves) as Hmlen.
    rewrite !Zlength_correct. rewrite Hmlen.
    rewrite <- (Permutation_length Hperm), <- Zlength_correct. exact Hlen. }
  assert (Hsf_color : SameColor sorted_final).
  { apply SameColor_Permutation with (a := final).
    - apply Permutation_sym. exact Hfinalperm.
    - exact Hcolor. }
  assert (Hsorted_natlen : length sorted = Z.to_nat half).
  { rewrite <- (Permutation_length Hperm).
    apply Nat2Z.inj. rewrite <- Zlength_correct, Hlen, Z2Nat.id by lia.
    reflexivity. }
  assert (Hsorted_sflen : length sorted = length sorted_final).
  { symmetry. eapply ChessMoves_length; exact Hsortedmoves. }
  destruct (Chess_same_color_targets half sorted_final Hhalf Hsf_len Hsf_bounds
    Hsf_nd Hsf_color) as [Hoddperm | Hevenperm].
  - assert (Hordered :
      ChessZipCost sorted (ChessTargets 1 (Z.to_nat half)) <=
      ChessZipCost sorted sorted_final).
    { apply ChessZipCost_sorted_min.
      - apply ChessTargets_gap.
      - exact Hmono.
      - rewrite ChessTargets_length. exact Hsorted_natlen.
      - apply Permutation_sym. exact Hoddperm. }
    assert (Hmoves_lower : ChessZipCost sorted sorted_final <= d).
    { pose proof (ChessMoves_cost_lower (2 * half) (Z.to_nat d) sorted
        sorted_final sorted_final Hsortedmoves Hsorted_sflen) as Hlower.
      rewrite ChessZipCost_self, Z2Nat.id in Hlower by lia. lia. }
    eapply Z.le_trans; [apply Z.le_min_l |]. lia.
  - assert (Hordered :
      ChessZipCost sorted (ChessTargets 2 (Z.to_nat half)) <=
      ChessZipCost sorted sorted_final).
    { apply ChessZipCost_sorted_min.
      - apply ChessTargets_gap.
      - exact Hmono.
      - rewrite ChessTargets_length. exact Hsorted_natlen.
      - apply Permutation_sym. exact Hevenperm. }
    assert (Hmoves_lower : ChessZipCost sorted sorted_final <= d).
    { pose proof (ChessMoves_cost_lower (2 * half) (Z.to_nat d) sorted
        sorted_final sorted_final Hsortedmoves Hsorted_sflen) as Hlower.
      rewrite ChessZipCost_self, Z2Nat.id in Hlower by lia. lia. }
    eapply Z.le_trans; [apply Z.le_min_r |]. lia.
Qed.

Lemma ChessCostPrefix_Spec : forall half positions sorted odd even,
  0 <= half ->
  Zlength positions = half ->
  Zlength sorted = half ->
  (forall i, 0 <= i < half -> 1 <= Znth i sorted 0 <= 2 * half) ->
  Pre (2 * half) positions ->
  Permutation positions sorted ->
  mono_nondec sorted ->
  ChessCostPrefix sorted half odd even ->
  Spec (2 * half) positions (Z.min odd even).
Proof.
  intros half positions sorted odd even Hhalf Hposlen Hsortedlen Hsortedbounds
    Hpre Hperm Hmono Hprefix.
  destruct Hpre as [Hevenn Hposnd].
  assert (Hsorted_forall : Forall (fun x => 1 <= x <= 2 * half) sorted).
  { apply (proj2 (Forall_Znth (fun x => 1 <= x <= 2 * half) 0 sorted)).
    intros i Hi. apply Hsortedbounds. lia. }
  assert (Hpositions_forall : Forall (fun x => 1 <= x <= 2 * half) positions).
  { eapply Permutation_Forall; [apply Permutation_sym; exact Hperm | exact Hsorted_forall]. }
  assert (Hsorted_nd : NoDup sorted).
  { eapply Permutation_NoDup; eauto. }
  destruct (ChessZipCost_odd_even sorted half odd even Hhalf Hsortedlen Hprefix)
    as [Hodd Heven].
  unfold Spec, min_value_of_subset, min_object_of_subset. sets_unfold.
  exists (Z.min odd even). split.
  - split.
    + split.
      * apply Z.le_ge.
        destruct (Z_le_gt_dec odd even) as [Hoe | Heo].
        -- rewrite Z.min_l by lia. rewrite Hodd. apply ChessZipCost_nonneg.
        -- rewrite Z.min_r by lia. rewrite Heven. apply ChessZipCost_nonneg.
      * destruct (Z_le_gt_dec odd even) as [Hoe | Heo].
        -- rewrite Z.min_l by lia. rewrite Hodd.
           eapply Chess_target_reachable with (sorted := sorted) (first := 1).
           ++ exact Hhalf.
           ++ left. reflexivity.
           ++ exact Hsortedlen.
           ++ exact Hsorted_forall.
           ++ exact Hmono.
           ++ exact Hsorted_nd.
           ++ exact Hperm.
        -- rewrite Z.min_r by lia. rewrite Heven.
           eapply Chess_target_reachable with (sorted := sorted) (first := 2).
           ++ exact Hhalf.
           ++ right. reflexivity.
           ++ exact Hsortedlen.
           ++ exact Hsorted_forall.
           ++ exact Hmono.
           ++ exact Hsorted_nd.
           ++ exact Hperm.
    + intros d [Hd Hcan]. apply Z.ge_le in Hd.
      rewrite Hodd, Heven.
      exact (Chess_any_reachable_lower half positions sorted d
        Hhalf Hposlen Hpositions_forall Hposnd Hperm Hmono Hd Hcan).
  - reflexivity.
Qed.

Lemma ChessCostPrefix_Spec_odd : forall half positions sorted odd even,
  0 <= half ->
  Zlength positions = half ->
  Zlength sorted = half ->
  (forall i, 0 <= i < half -> 1 <= Znth i sorted 0 <= 2 * half) ->
  Pre (2 * half) positions ->
  Permutation positions sorted ->
  mono_nondec sorted ->
  ChessCostPrefix sorted half odd even ->
  odd < even ->
  Spec (2 * half) positions odd.
Proof.
  intros half positions sorted odd even Hhalf Hposlen Hsortedlen Hbounds
    Hpre Hperm Hmono Hprefix Hlt.
  pose proof (ChessCostPrefix_Spec half positions sorted odd even Hhalf
    Hposlen Hsortedlen Hbounds Hpre Hperm Hmono Hprefix) as Hspec.
  rewrite Z.min_l in Hspec by lia. exact Hspec.
Qed.

Lemma ChessCostPrefix_Spec_even : forall half positions sorted odd even,
  0 <= half ->
  Zlength positions = half ->
  Zlength sorted = half ->
  (forall i, 0 <= i < half -> 1 <= Znth i sorted 0 <= 2 * half) ->
  Pre (2 * half) positions ->
  Permutation positions sorted ->
  mono_nondec sorted ->
  ChessCostPrefix sorted half odd even ->
  even <= odd ->
  Spec (2 * half) positions even.
Proof.
  intros half positions sorted odd even Hhalf Hposlen Hsortedlen Hbounds
    Hpre Hperm Hmono Hprefix Hle.
  pose proof (ChessCostPrefix_Spec half positions sorted odd even Hhalf
    Hposlen Hsortedlen Hbounds Hpre Hperm Hmono Hprefix) as Hspec.
  rewrite Z.min_r in Hspec by lia. exact Hspec.
Qed.
