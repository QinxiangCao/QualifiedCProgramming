Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition AlmostIncreasing (a : list Z) : Prop :=
  mono_inc a \/ exists i, 0 <= i < Zlength a /\
    mono_inc (sublist 0 i a ++ sublist (i + 1) (Zlength a) a).
Definition DifferenceCount (a b : list Z) : Z :=
  #(fun i : Z => 0 <= i < Zlength a /\ Znth i a 0 <> Znth i b 0).
Definition Pre (a : list Z) : Prop :=
  (* Stated explicitly in the P089 solver Require, so dropped here:
       2 <= Zlength a <= 200000 /\
       Forall (fun x => 1 <= x <= 1000000000) a  *)
  True.

Definition Spec (a : list Z) (out : Z) : Prop :=
  min_value_of_subset Z.le (fun v => exists b, Zlength b = Zlength a /\ AlmostIncreasing b /\ v = DifferenceCount a b) (fun x => x) out.

(* ================================================================= *)
(** ** Compressed value array: membership, strict order and ranks    *)
(* ================================================================= *)

(** [MemberPrefix l len v] : [v] occurs in the first [len] entries of [l]. *)
Definition MemberPrefix (l : list Z) (len v : Z) : Prop :=
  exists k, 0 <= k < len /\ Znth k l 0 = v.

(** [StrictIncPrefix l len] : the first [len] entries of [l] are strictly
    increasing.  Only a prefix is constrained because the physical array
    keeps unused slots behind the compressed part. *)
Definition StrictIncPrefix (l : list Z) (len : Z) : Prop :=
  forall p q, 0 <= p -> p < q -> q < len -> Znth p l 0 < Znth q l 0.

(** [RankResult l len v r] : [r] is the 1-based rank of the value [v] inside
    the strictly increasing prefix [l[0..len)].  For a member [v] this pins
    [r] uniquely, and ranks are order-isomorphic to values. *)
Definition RankResult (l : list Z) (len v r : Z) : Prop :=
  1 <= r <= len /\
  Znth (r - 1) l 0 = v /\
  (forall k, 0 <= k < r - 1 -> Znth k l 0 < v).

(* ================================================================= *)
(** ** Fenwick tree of prefix maxima                                 *)
(* ================================================================= *)

(** Sentinel used by the implementation for "no value inserted yet". *)
Definition MaxBitNeg : Z := -1000000000.

(** The C expression [i & (-i)] is interpreted as [Z.land i (-i)]. *)
Definition MaxBitLowbit (t : Z) : Z := Z.land t (-t).

(** Fenwick node [t] covers the closed 1-based interval
    [[t - lowbit t + 1, t]]. *)
Definition MaxBitNodeLo (t : Z) : Z := t - MaxBitLowbit t + 1.

Definition MaxBitCovers (t target : Z) : Prop :=
  MaxBitNodeLo t <= target <= t.

(** [RangeMax m lo hi] is the maximum of [m] over the half-open index range
    [[lo, hi)], floored at the sentinel; an empty range yields the
    sentinel. *)
Definition RangeMax (m : list Z) (lo hi : Z) : Z :=
  fold_right Z.max MaxBitNeg (map (fun r => Znth r m 0) (Zrange lo hi)).

(** [m] is the logical rank-indexed table (rank |-> best value inserted at
    that rank, sentinel when nothing was inserted) that the concrete tree
    [bit] represents.  Only slots [1..nvals] carry information. *)
Definition MaxBitRep (m bit : list Z) (nvals : Z) : Prop :=
  Zlength m = nvals + 1 /\
  forall t, 1 <= t <= nvals -> Znth t bit 0 = RangeMax m (MaxBitNodeLo t) (t + 1).

(** Inserting value [v] at rank [r] keeps the running maximum. *)
Definition MaxBitInsert (m : list Z) (r v : Z) : list Z :=
  replace_Znth r (Z.max (Znth r m 0) v) m.

(* ================================================================= *)
(** ** Keys: the coordinate change behind the whole reduction        *)
(* ================================================================= *)

(** Under [KeyAt], "the kept values are strictly increasing" is equivalent to
    "the kept keys are non-decreasing", because there is always room to fill
    the gaps with unconstrained replacements. *)
Definition KeyAt (a : list Z) (i : Z) : Z := Znth i a 0 - i.

(** Deleting position [d] shifts every later index left by one, so the key of
    a later kept position gains one. *)
Definition KeyShift (a : list Z) (d i : Z) : Z :=
  KeyAt a i + (if Z.ltb d i then 1 else 0).

Definition KeyPrefix (a c : list Z) (k : Z) : Prop :=
  forall j, 0 <= j < k -> Znth j c 0 = KeyAt a j.

Definition ValsRawPrefix (a vals : list Z) (k : Z) : Prop :=
  forall j, 0 <= j < k ->
    Znth (2 * j) vals 0 = KeyAt a j /\
    Znth (2 * j + 1) vals 0 = KeyAt a j + 1.

(* ================================================================= *)
(** ** Coordinate compression                                        *)
(* ================================================================= *)

Definition DedupState (sorted cur : list Z) (uniq scanned : Z) : Prop :=
  StrictIncPrefix cur uniq /\
  (forall p, 0 <= p < scanned ->
     exists q, 0 <= q < uniq /\ Znth q cur 0 = Znth p sorted 0) /\
  (forall q, 0 <= q < uniq ->
     exists p, 0 <= p < scanned /\ Znth q cur 0 = Znth p sorted 0) /\
  (0 < scanned -> 0 < uniq /\ Znth (uniq - 1) cur 0 = Znth (scanned - 1) sorted 0) /\
  (forall p, scanned <= p < Zlength sorted -> Znth p cur 0 = Znth p sorted 0).

Definition CompressedKeys (a vals : list Z) (uniq : Z) : Prop :=
  StrictIncPrefix vals uniq /\
  (forall i, 0 <= i < Zlength a ->
     MemberPrefix vals uniq (KeyAt a i) /\
     MemberPrefix vals uniq (KeyAt a i + 1)) /\
  (forall r, 0 <= r < uniq ->
     exists i, 0 <= i < Zlength a /\
       (Znth r vals 0 = KeyAt a i \/ Znth r vals 0 = KeyAt a i + 1)).

(* ================================================================= *)
(** ** The combinatorial meaning of the two DP layers                *)
(* ================================================================= *)

(** A kept index set is recorded as the strictly increasing list of its
    elements, so its cardinality is just its length. *)
Definition Keep0List (a s : list Z) : Prop :=
  mono_inc s /\
  (forall p, 0 <= p < Zlength s -> 0 <= Znth p s 0 < Zlength a) /\
  (forall p q, 0 <= p -> p < q -> q < Zlength s ->
     KeyAt a (Znth p s 0) <= KeyAt a (Znth q s 0)).

Definition Keep1List (a : list Z) (d : Z) (s : list Z) : Prop :=
  0 <= d < Zlength a /\
  mono_inc s /\
  (forall p, 0 <= p < Zlength s ->
     0 <= Znth p s 0 < Zlength a /\ Znth p s 0 <> d) /\
  (forall p q, 0 <= p -> p < q -> q < Zlength s ->
     KeyShift a d (Znth p s 0) <= KeyShift a d (Znth q s 0)).

Definition Best0EndingAt (a : list Z) (i v : Z) : Prop :=
  max_value_of_subset Z.le
    (fun s : list Z =>
       Keep0List a s /\ 0 < Zlength s /\ Znth (Zlength s - 1) s 0 = i)
    (fun s : list Z => Zlength s)
    v.

(** The deletion layer: the last kept element is [i] and it lies after the
    deleted position, so at [i = 0] no such set exists and the maximum is
    unattainable, which is exactly the sentinel case of the implementation. *)
Definition Best1EndingAt (a : list Z) (i v : Z) : Prop :=
  max_value_of_subset Z.le
    (fun s : list Z =>
       (exists d, Keep1List a d s /\ d < i) /\
       0 < Zlength s /\ Znth (Zlength s - 1) s 0 = i)
    (fun s : list Z => Zlength s)
    v.

Definition DP0Prefix (a dp : list Z) (k : Z) : Prop :=
  forall j, 0 <= j < k -> Best0EndingAt a j (Znth j dp 0).

Definition ClampedPrefixMax (l : list Z) (k v : Z) : Prop :=
  0 <= v /\
  (forall j, 0 <= j < k -> Znth j l 0 <= v) /\
  (v = 0 \/ exists j, 0 <= j < k /\ Znth j l 0 = v).

Definition ClampedBest1Upto (a : list Z) (k v : Z) : Prop :=
  0 <= v /\
  (forall j w, 0 <= j < k -> Best1EndingAt a j w -> w <= v) /\
  (v = 0 \/ exists j w, 0 <= j < k /\ Best1EndingAt a j w /\ w = v).

(* ================================================================= *)
(** ** What the three Fenwick trees store                            *)
(* ================================================================= *)

(** [m] is the per-rank maximum of the values inserted so far.  Used both for
    the plain tree over indices below [k] and, with [k] lowered by one, for
    the lagging tree that only exposes indices at distance two or more. *)
Definition Bit0Model (a vals dp m : list Z) (k uniq : Z) : Prop :=
  Zlength m = uniq + 1 /\
  forall r, 1 <= r <= uniq ->
    ((forall j, 0 <= j < k ->
        RankResult vals uniq (KeyAt a j) r ->
        Znth j dp 0 <= Znth r m 0) /\
     (Znth r m 0 = MaxBitNeg \/
      exists j, 0 <= j < k /\
        RankResult vals uniq (KeyAt a j) r /\
        Znth r m 0 = Znth j dp 0)).

Definition Bit1Model (a vals m : list Z) (k uniq : Z) : Prop :=
  Zlength m = uniq + 1 /\
  forall r, 1 <= r <= uniq ->
    ((forall j w, 0 <= j < k ->
        Best1EndingAt a j w ->
        RankResult vals uniq (KeyAt a j + 1) r ->
        w <= Znth r m 0) /\
     (Znth r m 0 = MaxBitNeg \/
      exists j w, 0 <= j < k /\
        Best1EndingAt a j w /\
        RankResult vals uniq (KeyAt a j + 1) r /\
        Znth r m 0 = w)).

(* ================================================================= *)
(** ** Loop states of the three helper functions                     *)
(* ================================================================= *)

Definition MaxBitAddProgress
    (entry current : list Z) (nvals target cursor v : Z) : Prop :=
  Zlength current = Zlength entry /\
  (cursor <= nvals -> MaxBitCovers cursor target) /\
  forall t, 1 <= t <= nvals ->
    ((MaxBitCovers t target /\ t < cursor) ->
       Znth t current 0 = Z.max (Znth t entry 0) v) /\
    ((~ MaxBitCovers t target \/ cursor <= t) ->
       Znth t current 0 = Znth t entry 0).

Definition MaxBitQueryState (m : list Z) (target cursor acc : Z) : Prop :=
  acc = RangeMax m (cursor + 1) (target + 1).

Definition RankSearchState (l : list Z) (v lo hi : Z) : Prop :=
  (forall k, 0 <= k < lo -> Znth k l 0 < v) /\
  v <= Znth hi l 0.

Notation mono_nondec := AUXLib.MonotonicList.mono_nondec.

Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.Zbitwise.
Require Import Coq.micromega.Psatz.
Lemma lowbit_positive__bit_update_fenwick :
  forall x, 0 < x -> 0 < MaxBitLowbit x.
Proof.
  intros x Hx.
  unfold MaxBitLowbit.
  assert (Hnonneg : 0 <= Z.land x (-x)).
  { apply Z.land_nonneg. left. lia. }
  assert (Hnonzero : Z.land x (-x) <> 0).
  {
    intros Hzero.
    pose proof (Z.add_nocarry_lxor x (-x) Hzero) as Hxor.
    assert (Z.lxor x (-x) = 0) by lia.
    apply Z.lxor_eq in H.
    lia.
  }
  lia.
Qed.
Lemma lowbit_le__bit_update_fenwick :
  forall x, 0 <= x -> MaxBitLowbit x <= x.
Proof.
  intros x Hx.
  unfold MaxBitLowbit.
  set (u := Z.land x (-x)).
  set (v := Z.ldiff x (-x)).
  assert (Hu : 0 <= u).
  { subst u. apply Z.land_nonneg. left; exact Hx. }
  assert (Hv : 0 <= v).
  { subst v. apply Z.ldiff_nonneg. left; exact Hx. }
  assert (Hdisjoint : Z.land v u = 0).
  {
    subst u v.
    rewrite Z.land_assoc.
    rewrite (Z.land_comm (Z.ldiff x (-x)) x).
    rewrite <- Z.land_assoc.
    rewrite Z.land_ldiff.
    apply Z.land_0_r.
  }
  assert (Hsum : v + u = x).
  {
    rewrite Z.add_nocarry_lxor by exact Hdisjoint.
    rewrite Z.lxor_lor by exact Hdisjoint.
    subst u v.
    apply Z.lor_ldiff_and.
  }
  lia.
Qed.
Lemma lowbit_pos_le__bit_update_fenwick :
  forall t, 0 < t -> 0 < Z.land t (-t) <= t.
Proof.
  intros t Ht.
  pose proof (lowbit_positive__bit_update_fenwick t Ht) as Hpos.
  pose proof (lowbit_le__bit_update_fenwick t ltac:(lia)) as Hle.
  unfold MaxBitLowbit in Hpos, Hle.
  lia.
Qed.
Lemma maxbit_nodelo_bounds__bit_update_fenwick :
  forall t, 0 < t -> 1 <= MaxBitNodeLo t <= t.
Proof.
  intros t Ht.
  unfold MaxBitNodeLo.
  pose proof (lowbit_pos_le__bit_update_fenwick t Ht) as Hb.
  unfold MaxBitLowbit.
  lia.
Qed.
Lemma maxbit_covers_self__bit_update_fenwick :
  forall t, 0 < t -> MaxBitCovers t t.
Proof.
  intros t Ht.
  unfold MaxBitCovers.
  pose proof (maxbit_nodelo_bounds__bit_update_fenwick t Ht).
  lia.
Qed.
Lemma lowbit_double__bit_update_fenwick :
  forall x, 0 < x -> MaxBitLowbit (2 * x) = 2 * MaxBitLowbit x.
Proof.
  intros x Hx.
  unfold MaxBitLowbit.
  apply Z.bits_inj'; intros n Hn.
  replace (- (2 * x)) with (2 * (-x)) by ring.
  rewrite Z.land_spec.
  rewrite !Z.double_bits.
  rewrite Z.land_spec.
  reflexivity.
Qed.
Lemma lowbit_odd__bit_update_fenwick :
  forall x, 0 <= x -> MaxBitLowbit (2 * x + 1) = 1.
Proof.
  intros x Hx.
  unfold MaxBitLowbit.
  apply Z.bits_inj'; intros n Hn.
  destruct (Z.eq_dec n 0) as [-> | Hnz].
  - rewrite Z.land_spec.
    replace (- (2 * x + 1)) with (2 * (-x - 1) + 1) by ring.
    rewrite !Z.testbit_odd_0.
    reflexivity.
  - assert (Hpos : 0 < n) by lia.
    rewrite Z.land_spec.
    rewrite Z.bits_opp by exact Hn.
    replace (Z.pred (2 * x + 1)) with (2 * x) by lia.
    replace n with (Z.succ (Z.pred n)) by lia.
    rewrite Z.testbit_odd_succ by lia.
    rewrite Z.testbit_even_succ by lia.
    rewrite (Z.bits_above_log2 1 (Z.succ (Z.pred n))) by (simpl; lia).
    destruct (Z.testbit x (Z.pred n)); reflexivity.
Qed.
Lemma lowbit_successor_growth__bit_update_fenwick :
  forall x,
    0 < x ->
    2 * MaxBitLowbit x <= MaxBitLowbit (x + MaxBitLowbit x).
Proof.
  intros [|p|p] Hx; try lia.
  clear Hx.
  revert p.
  fix IH 1.
  intros [p|p|].
  - rewrite Pos2Z.pos_xI.
    rewrite lowbit_odd__bit_update_fenwick by lia.
    replace (2 * Z.pos p + 1 + 1) with (2 * (Z.pos p + 1)) by ring.
    rewrite lowbit_double__bit_update_fenwick by lia.
    pose proof (lowbit_positive__bit_update_fenwick (Z.pos p + 1) ltac:(lia)).
    lia.
  - assert (Hdouble : MaxBitLowbit (Z.pos p~0) =
        2 * MaxBitLowbit (Z.pos p)).
    {
      rewrite Pos2Z.pos_xO.
      apply lowbit_double__bit_update_fenwick; lia.
    }
    rewrite Hdouble.
    assert (Harg : Z.pos p~0 + 2 * MaxBitLowbit (Z.pos p) =
        2 * (Z.pos p + MaxBitLowbit (Z.pos p))).
    {
      rewrite Pos2Z.pos_xO.
      ring.
    }
    rewrite Harg.
    assert (Hnextpos : 0 < Z.pos p + MaxBitLowbit (Z.pos p)).
    {
      pose proof (lowbit_positive__bit_update_fenwick (Z.pos p) ltac:(lia)).
      lia.
    }
    pose proof
      (lowbit_double__bit_update_fenwick
         (Z.pos p + MaxBitLowbit (Z.pos p)) Hnextpos) as Hnextdouble.
    pose proof (IH p) as Hrec.
    rewrite Hnextdouble.
    lia.
  - change (2 * MaxBitLowbit 1 <=
      MaxBitLowbit (1 + MaxBitLowbit 1)).
    vm_compute.
  all: try lia.
  all: easy.
Qed.
Lemma lowbit_gap_bound__bit_update_fenwick :
  forall x node,
    0 < x ->
    x < node < x + MaxBitLowbit x ->
    MaxBitLowbit node <= node - x.
Proof.
  intros [|p|p] node Hx; try lia.
  clear Hx.
  revert node.
  induction p as [p IHp | p IHp |]; intros node Hgap.
  - rewrite Pos2Z.pos_xI in Hgap.
    rewrite lowbit_odd__bit_update_fenwick in Hgap by lia.
    lia.
  - rewrite Pos2Z.pos_xO in Hgap |- *.
    rewrite lowbit_double__bit_update_fenwick in Hgap by lia.
    destruct node as [|q|q]; try lia.
    destruct q as [q|q|].
    + rewrite Pos2Z.pos_xI.
      rewrite lowbit_odd__bit_update_fenwick by lia.
      lia.
    + rewrite Pos2Z.pos_xO.
      rewrite lowbit_double__bit_update_fenwick by lia.
      specialize (IHp (Z.pos q) ltac:(lia)).
      lia.
    + lia.
  - change (1 < node < 1 + MaxBitLowbit 1) in Hgap.
    change (1 < node < 1 + MaxBitLowbit (2 * 0 + 1)) in Hgap.
    rewrite lowbit_odd__bit_update_fenwick in Hgap by lia.
    lia.
  all: easy.
Qed.
Lemma maxbit_covers_ancestor__bit_update_fenwick :
  forall t target,
    0 < t ->
    MaxBitCovers t target ->
    MaxBitCovers (t + Z.land t (-t)) target.
Proof.
  intros t target Ht Hcovers.
  pose proof (lowbit_successor_growth__bit_update_fenwick t Ht) as Hgrowth.
  pose proof (lowbit_positive__bit_update_fenwick t Ht) as Hpos.
  unfold MaxBitCovers, MaxBitNodeLo, MaxBitLowbit in *.
  lia.
Qed.
Lemma maxbit_nodelo_gap__bit_update_fenwick :
  forall t node,
    0 < t ->
    t < node < t + Z.land t (-t) ->
    t < MaxBitNodeLo node.
Proof.
  intros t node Ht Hgap.
  unfold MaxBitNodeLo.
  assert (Hgap' : t < node < t + MaxBitLowbit t)
    by (unfold MaxBitLowbit; lia).
  pose proof (lowbit_gap_bound__bit_update_fenwick t node Ht Hgap') as Hbound.
  unfold MaxBitLowbit in Hbound |- *.
  lia.
Qed.

(* ================================================================= *)
(** ** List helpers for the rank-indexed maximum table               *)
(* ================================================================= *)
Lemma replace_nth_length__bit_update_fenwick :
  forall {A : Type} (l : list A) (n : nat) (a : A),
    length (replace_nth n l a) = length l.
Proof.
  intros A l.
  induction l as [| h t IH]; intros n a; simpl.
  - reflexivity.
  - destruct n as [| n']; simpl.
    + reflexivity.
    + rewrite IH. reflexivity.
Qed.
Lemma zlength_replace_Znth__bit_update_fenwick :
  forall {A : Type} (n : Z) (v : A) (l : list A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A n v l.
  unfold replace_Znth.
  rewrite !Zlength_correct.
  rewrite replace_nth_length__bit_update_fenwick.
  reflexivity.
Qed.
Lemma fold_max_map_ext__bit_update_fenwick :
  forall (l : list Z) (F G : Z -> Z) (d : Z),
    (forall t, In t l -> F t = G t) ->
    fold_right Z.max d (map F l) = fold_right Z.max d (map G l).
Proof.
  induction l as [| a l IH]; intros F G d Hext; simpl.
  - reflexivity.
  - rewrite (Hext a ltac:(left; reflexivity)).
    rewrite (IH F G d ltac:(intros t Ht; apply Hext; right; exact Ht)).
    reflexivity.
Qed.
Lemma fold_max_upd_notin__bit_update_fenwick :
  forall (l : list Z) (F G : Z -> Z) (d r : Z),
    (forall t, In t l -> t <> r -> G t = F t) ->
    ~ In r l ->
    fold_right Z.max d (map G l) = fold_right Z.max d (map F l).
Proof.
  intros l F G d r Hne Hnin.
  apply fold_max_map_ext__bit_update_fenwick.
  intros t Ht.
  apply Hne; [exact Ht |].
  intros Heq. subst t. contradiction.
Qed.
Lemma fold_max_upd_in__bit_update_fenwick :
  forall (l : list Z) (F G : Z -> Z) (d r v : Z),
    (forall t, In t l -> t <> r -> G t = F t) ->
    G r = Z.max (F r) v ->
    In r l ->
    fold_right Z.max d (map G l) = Z.max (fold_right Z.max d (map F l)) v.
Proof.
  induction l as [| a l IH]; intros F G d r v Hne Hr Hin; simpl in *.
  - contradiction.
  - destruct (Z.eq_dec a r) as [Haeq | Hneq].
    + subst a.
      rewrite Hr.
      destruct (In_dec Z.eq_dec r l) as [Hin' | Hnin'].
      * rewrite (IH F G d r v
          ltac:(intros t Ht Htr; apply Hne; [right; exact Ht | exact Htr])
          Hr Hin').
        lia.
      * rewrite (fold_max_upd_notin__bit_update_fenwick l F G d r
          ltac:(intros t Ht Htr; apply Hne; [right; exact Ht | exact Htr])
          Hnin').
        lia.
    + rewrite (Hne a ltac:(left; reflexivity) Hneq).
      assert (Hin' : In r l).
      { destruct Hin as [Heq | Hin']; [congruence | exact Hin']. }
      rewrite (IH F G d r v
        ltac:(intros t Ht Htr; apply Hne; [right; exact Ht | exact Htr])
        Hr Hin').
      lia.
Qed.
Lemma rangemax_replace_raise__bit_update_fenwick :
  forall (m : list Z) (lo hi r v : Z),
    0 <= lo ->
    hi <= Zlength m ->
    0 <= r < Zlength m ->
    (lo <= r < hi ->
       RangeMax (MaxBitInsert m r v) lo hi = Z.max (RangeMax m lo hi) v) /\
    (~ (lo <= r < hi) ->
       RangeMax (MaxBitInsert m r v) lo hi = RangeMax m lo hi).
Proof.
  intros m lo hi r v Hlo Hhi Hr.
  unfold RangeMax, MaxBitInsert.
  assert (Hne : forall t, In t (Zrange lo hi) -> t <> r ->
            Znth t (replace_Znth r (Z.max (Znth r m 0) v) m) 0 = Znth t m 0).
  {
    intros t Ht Htr.
    rewrite <- In_Zrange in Ht.
    apply Znth_replace_Znth_Diff; lia.
  }
  assert (Hat : Znth r (replace_Znth r (Z.max (Znth r m 0) v) m) 0
                = Z.max (Znth r m 0) v).
  { apply Znth_replace_Znth_Same. lia. }
  split.
  - intros Hin.
    apply (fold_max_upd_in__bit_update_fenwick (Zrange lo hi)
             (fun t => Znth t m 0)
             (fun t => Znth t (replace_Znth r (Z.max (Znth r m 0) v) m) 0)
             MaxBitNeg r v Hne Hat).
    rewrite <- In_Zrange. exact Hin.
  - intros Hout.
    apply (fold_max_upd_notin__bit_update_fenwick (Zrange lo hi)
             (fun t => Znth t m 0)
             (fun t => Znth t (replace_Znth r (Z.max (Znth r m 0) v) m) 0)
             MaxBitNeg r Hne).
    rewrite <- In_Zrange. exact Hout.
Qed.
Lemma maxbit_rep_of_progress__bit_update_fenwick :
  forall (m bit_l bit_cur : list Z) (nvals i_pre cursor v : Z),
    1 <= i_pre <= nvals ->
    nvals < cursor ->
    MaxBitRep m bit_l nvals ->
    MaxBitAddProgress bit_l bit_cur nvals i_pre cursor v ->
    MaxBitRep (MaxBitInsert m i_pre v) bit_cur nvals.
Proof.
  intros m bit_l bit_cur nvals i_pre cursor v Hipre Hcursor Hrep Hprog.
  destruct Hrep as [Hmlen Hnodes].
  destruct Hprog as [Hlen [Hcov Hstep]].
  unfold MaxBitRep.
  split.
  - unfold MaxBitInsert.
    rewrite zlength_replace_Znth__bit_update_fenwick. exact Hmlen.
  - intros t Ht.
    pose proof (maxbit_nodelo_bounds__bit_update_fenwick t ltac:(lia)) as Hlob.
    specialize (Hnodes t Ht).
    specialize (Hstep t Ht).
    destruct Hstep as [Hupd Hold].
    pose proof (rangemax_replace_raise__bit_update_fenwick
                  m (MaxBitNodeLo t) (t + 1) i_pre v
                  ltac:(lia) ltac:(lia) ltac:(lia)) as [Hin Hout].
    assert (Hdec : MaxBitCovers t i_pre \/ ~ MaxBitCovers t i_pre).
    { unfold MaxBitCovers.
      destruct (Z_le_gt_dec (MaxBitNodeLo t) i_pre) as [Ha | Ha];
      destruct (Z_le_gt_dec i_pre t) as [Hb | Hb];
      [ left; lia | right; lia | right; lia | right; lia ]. }
    destruct Hdec as [Hc | Hnc].
    + unfold MaxBitCovers in Hc.
      rewrite Hin by lia.
      rewrite <- Hnodes.
      apply Hupd.
      unfold MaxBitCovers. lia.
    + rewrite Hout by (unfold MaxBitCovers in Hnc; lia).
      rewrite <- Hnodes.
      apply Hold.
      left. exact Hnc.
Qed.
Lemma land_ldiff_zero__bit_query_fenwick : forall a b, Z.land (Z.ldiff a b) (Z.land a b) = 0.
Proof.
  intros a b. apply Z.bits_inj_0. intros n.
  rewrite Z.land_spec, Z.ldiff_spec, Z.land_spec.
  destruct (Z.testbit a n), (Z.testbit b n); reflexivity.
Qed.
Lemma land_le__bit_query_fenwick : forall a b, 0 <= a -> Z.land a b <= a.
Proof.
  intros a b Ha.
  pose proof (land_ldiff_zero__bit_query_fenwick a b) as H0.
  pose proof (Z.add_nocarry_lxor _ _ H0) as Hadd.
  pose proof (Z.lxor_lor _ _ H0) as Hlx.
  rewrite Hlx in Hadd.
  rewrite Z.lor_ldiff_and in Hadd.
  assert (0 <= Z.ldiff a b) by (apply Z.ldiff_nonneg; left; exact Ha).
  lia.
Qed.
Lemma lowbit_pos_le__bit_query_fenwick : forall t, 0 < t -> 0 < Z.land t (-t) <= t.
Proof.
  intros t Ht. split.
  - assert (Hnn : 0 <= Z.land t (-t)) by (apply Z.land_nonneg; left; lia).
    assert (Hne : Z.land t (-t) <> 0).
    { intros Hz. pose proof (Z.add_nocarry_lxor _ _ Hz) as Hadd.
      assert (Hsum : t + - t = 0) by lia. rewrite Hsum in Hadd.
      symmetry in Hadd.
      pose proof (proj1 (Z.lxor_eq_0_iff t (- t)) Hadd) as Heq. lia. }
    lia.
  - apply land_le__bit_query_fenwick. lia.
Qed.
Lemma fold_max_ge__bit_query_fenwick : forall (l : list Z) (d : Z),
  d <= fold_right Z.max d l.
Proof.
  induction l as [|x l IH]; intros d; simpl.
  - lia.
  - specialize (IH d). lia.
Qed.
Lemma fold_max_app__bit_query_fenwick : forall (l1 l2 : list Z) (d : Z),
  fold_right Z.max d (l1 ++ l2) = Z.max (fold_right Z.max d l1) (fold_right Z.max d l2).
Proof.
  induction l1 as [|x l1 IH]; intros l2 d; simpl.
  - pose proof (fold_max_ge__bit_query_fenwick l2 d). lia.
  - rewrite IH. lia.
Qed.
Lemma zrange_app__bit_query_fenwick : forall lo mid hi,
  lo <= mid -> mid <= hi ->
  Zrange lo hi = Zrange lo mid ++ Zrange mid hi.
Proof.
  intros lo mid hi H1 H2. unfold Zrange.
  replace (hi - lo) with ((mid - lo) + (hi - mid)) by lia.
  rewrite Z2Nat.inj_add by lia.
  rewrite Zrange_aux_app.
  rewrite Z2Nat.id by lia.
  replace (lo + (mid - lo)) with mid by lia.
  reflexivity.
Qed.
Lemma rangemax_empty__bit_query_fenwick : forall m lo hi,
  hi <= lo -> RangeMax m lo hi = MaxBitNeg.
Proof.
  intros m lo hi H. unfold RangeMax, Zrange.
  replace (Z.to_nat (hi - lo)) with 0%nat by lia.
  simpl. reflexivity.
Qed.
Lemma rangemax_concat__bit_query_fenwick : forall m lo mid hi,
  lo <= mid -> mid <= hi ->
  RangeMax m lo hi = Z.max (RangeMax m lo mid) (RangeMax m mid hi).
Proof.
  intros m lo mid hi H1 H2. unfold RangeMax.
  rewrite (zrange_app__bit_query_fenwick lo mid hi) by lia.
  rewrite map_app.
  rewrite fold_max_app__bit_query_fenwick.
  reflexivity.
Qed.
Lemma rank_search_pin__rank_binary_search :
  forall (l : list Z) (len v lo : Z),
    StrictIncPrefix l len ->
    MemberPrefix l len v ->
    RankSearchState l v lo lo ->
    0 <= lo < len ->
    Znth lo l 0 = v.
Proof.
  intros l len v lo Hinc Hmem Hstate Hlo.
  destruct Hmem as [k0 [Hk0 Hk0v]].
  destruct Hstate as [Hleft Hright].
  destruct (Z.lt_trichotomy k0 lo) as [Hlt | [Heq | Hgt]].
  - assert (Znth k0 l 0 < v) by (apply Hleft; lia).
    lia.
  - subst k0. exact Hk0v.
  - assert (Znth lo l 0 < Znth k0 l 0) by (apply Hinc; lia).
    lia.
Qed.
Lemma keyprefix_extend__key_and_vals_fill : forall (a c c' : list Z) (k : Z),
  0 <= k ->
  KeyPrefix a c k ->
  Znth k c' 0 = KeyAt a k ->
  (forall j, 0 <= j < k -> Znth j c' 0 = Znth j c 0) ->
  KeyPrefix a c' (k + 1).
Proof.
  intros a c c' k Hk HK Heq Hsame j Hj.
  destruct (Z.eq_dec j k) as [Hjk | Hjk].
  - subst j. exact Heq.
  - rewrite Hsame by lia. apply HK. lia.
Qed.
Lemma valsraw_extend__key_and_vals_fill : forall (a vals vals' : list Z) (k : Z),
  0 <= k ->
  ValsRawPrefix a vals k ->
  Znth (2 * k) vals' 0 = KeyAt a k ->
  Znth (2 * k + 1) vals' 0 = KeyAt a k + 1 ->
  (forall j, 0 <= j < 2 * k -> Znth j vals' 0 = Znth j vals 0) ->
  ValsRawPrefix a vals' (k + 1).
Proof.
  intros a vals vals' k Hk HV H0 H1 Hsame j Hj.
  destruct (Z.eq_dec j k) as [Hjk | Hjk].
  - subst j. split; assumption.
  - destruct (HV j ltac:(lia)) as [Ha Hb].
    split.
    + rewrite Hsame by lia. exact Ha.
    + rewrite Hsame by lia. exact Hb.
Qed.
Lemma perm_Zlength__dedup_scan : forall (la lb : list Z),
  Permutation la lb -> Zlength la = Zlength lb.
Proof.
  intros la lb H. apply Permutation_length in H.
  rewrite !Zlength_correct, H. reflexivity.
Qed.
Lemma perm_range_bound__dedup_scan : forall (la lb : list Z) (lo hi : Z),
  Permutation la lb ->
  (forall k, 0 <= k < Zlength la -> lo <= Znth k la 0 <= hi) ->
  (forall k, 0 <= k < Zlength lb -> lo <= Znth k lb 0 <= hi).
Proof.
  intros la lb lo hi Hperm Hb k Hk.
  assert (Hin : In (Znth k lb 0) lb).
  { unfold Znth. apply nth_In. rewrite Zlength_correct in Hk. lia. }
  apply Permutation_sym in Hperm.
  apply (Permutation_in _ Hperm) in Hin.
  apply (In_nth la) with (d := 0) in Hin.
  destruct Hin as [n [Hn Hnv]].
  specialize (Hb (Z.of_nat n)).
  unfold Znth in Hb. rewrite Nat2Z.id in Hb.
  rewrite Hnv in Hb. apply Hb. rewrite Zlength_correct. lia.
Qed.
Lemma dedup_keep_step__dedup_scan : forall (sorted cur : list Z) (uniq i : Z),
  0 <= uniq ->
  uniq <= i ->
  i < Zlength sorted ->
  Zlength cur = Zlength sorted ->
  mono_nondec sorted ->
  (forall p, uniq <= p < Zlength sorted -> Znth p cur 0 = Znth p sorted 0) ->
  DedupState sorted cur uniq i ->
  (i = 0 \/ Znth i cur 0 <> Znth (i - 1) cur 0) ->
  DedupState sorted (replace_Znth uniq (Znth i cur 0) cur) (uniq + 1) (i + 1).
Proof.
  intros sorted cur uniq i Hu0 Hui Hi Hlen Hmono Htail Hstate Hguard.
  unfold DedupState in Hstate |- *.
  destruct Hstate as [Hsi [Hfwd [Hbwd [Hlast Htl]]]].
  assert (Hcur_i : Znth i cur 0 = Znth i sorted 0) by (apply Htail; lia).
  assert (Hsame : Znth uniq (replace_Znth uniq (Znth i cur 0) cur) 0 = Znth i cur 0)
    by (apply Znth_replace_Znth_Same; lia).
  assert (Hdiff : forall j, 0 <= j < Zlength cur -> j <> uniq ->
                  Znth j (replace_Znth uniq (Znth i cur 0) cur) 0 = Znth j cur 0).
  { intros j Hj Hne. apply Znth_replace_Znth_Diff; lia. }
  assert (Hle : forall q, 0 <= q < uniq -> Znth q cur 0 <= Znth (uniq - 1) cur 0).
  { intros q Hq. destruct (Z.eq_dec q (uniq - 1)) as [Heq | Hne].
    - subst q. lia.
    - specialize (Hsi q (uniq - 1) ltac:(lia) ltac:(lia) ltac:(lia)). lia. }
  assert (Hgrow : forall q, 0 <= q < uniq -> Znth q cur 0 < Znth i cur 0).
  { intros q Hq.
    destruct (Z.eq_dec i 0) as [Hi0 | Hi0]; [lia |].
    assert (Hguard' : Znth i cur 0 <> Znth (i - 1) cur 0)
      by (destruct Hguard as [Hz | Hz]; [lia | exact Hz]).
    destruct (Hlast ltac:(lia)) as [Hu Hlv].
    assert (Hprev : Znth (i - 1) cur 0 = Znth (i - 1) sorted 0).
    { destruct (Z.eq_dec uniq i) as [He | He].
      - rewrite <- Hlv, He. reflexivity.
      - apply Htail; lia. }
    assert (Hmn : Znth (i - 1) sorted 0 <= Znth i sorted 0) by (apply Hmono; lia).
    specialize (Hle q Hq). lia. }
  split; [| split; [| split; [| split]]].
  - intros p q Hp Hpq Hq.
    destruct (Z.eq_dec q uniq) as [Hqe | Hqe].
    + subst q. rewrite Hsame. rewrite (Hdiff p) by lia. apply Hgrow; lia.
    + rewrite (Hdiff p) by lia. rewrite (Hdiff q) by lia. apply Hsi; lia.
  - intros p Hp.
    destruct (Z.eq_dec p i) as [Hpe | Hpe].
    + subst p. exists uniq. split; [lia |]. rewrite Hsame. exact Hcur_i.
    + destruct (Hfwd p ltac:(lia)) as [q [Hq Hqv]].
      exists q. split; [lia |]. rewrite (Hdiff q) by lia. exact Hqv.
  - intros q Hq.
    destruct (Z.eq_dec q uniq) as [Hqe | Hqe].
    + subst q. exists i. split; [lia |]. rewrite Hsame. exact Hcur_i.
    + destruct (Hbwd q ltac:(lia)) as [p [Hp Hpv]].
      exists p. split; [lia |]. rewrite (Hdiff q) by lia. exact Hpv.
  - intros _. split; [lia |].
    replace (uniq + 1 - 1) with uniq by lia.
    replace (i + 1 - 1) with i by lia.
    rewrite Hsame. exact Hcur_i.
  - intros p Hp. rewrite (Hdiff p) by lia. apply Htail; lia.
Qed.
Lemma dedup_skip_step__dedup_scan : forall (sorted cur : list Z) (uniq i : Z),
  0 <= uniq ->
  uniq <= i ->
  0 < i ->
  i < Zlength sorted ->
  Zlength cur = Zlength sorted ->
  (forall p, uniq <= p < Zlength sorted -> Znth p cur 0 = Znth p sorted 0) ->
  DedupState sorted cur uniq i ->
  Znth i cur 0 = Znth (i - 1) cur 0 ->
  DedupState sorted cur uniq (i + 1).
Proof.
  intros sorted cur uniq i Hu0 Hui Hi0 Hi Hlen Htail Hstate Hguard.
  unfold DedupState in Hstate |- *.
  destruct Hstate as [Hsi [Hfwd [Hbwd [Hlast Htl]]]].
  destruct (Hlast ltac:(lia)) as [Hu Hlv].
  assert (Hcur_i : Znth i cur 0 = Znth i sorted 0) by (apply Htail; lia).
  assert (Hprev : Znth (i - 1) cur 0 = Znth (i - 1) sorted 0).
  { destruct (Z.eq_dec uniq i) as [He | He].
    - rewrite <- Hlv, He. reflexivity.
    - apply Htail; lia. }
  assert (Heq : Znth i sorted 0 = Znth (i - 1) sorted 0) by lia.
  split; [exact Hsi | split; [| split; [| split]]].
  - intros p Hp.
    destruct (Z.eq_dec p i) as [Hpe | Hpe].
    + subst p. exists (uniq - 1). split; [lia |]. rewrite Hlv. lia.
    + apply Hfwd; lia.
  - intros q Hq. destruct (Hbwd q ltac:(lia)) as [p [Hp Hpv]].
    exists p. split; [lia |]. exact Hpv.
  - intros _. split; [lia |].
    replace (i + 1 - 1) with i by lia. lia.
  - intros p Hp. apply Htl; lia.
Qed.
Lemma Znth_In_bridge__compressed_keys : forall (l : list Z) (i : Z),
  0 <= i < Zlength l -> In (Znth i l 0) l.
Proof.
  intros l i Hi.
  unfold Znth.
  apply nth_In.
  replace (List.length l) with (Z.to_nat (Zlength l)).
  - apply Z2Nat.inj_lt; lia.
  - rewrite Zlength_correct. rewrite Nat2Z.id. reflexivity.
Qed.
Lemma In_Znth_bridge__compressed_keys : forall (l : list Z) (v : Z),
  In v l -> exists i, 0 <= i < Zlength l /\ Znth i l 0 = v.
Proof.
  intros l v Hin.
  pose proof (In_nth l v 0 Hin) as [k [Hk Hnth]].
  exists (Z.of_nat k).
  split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. exact Hnth.
Qed.
Lemma perm_member_transfer__compressed_keys : forall (l1 l2 : list Z) (v : Z),
  Permutation l1 l2 ->
  ((exists p, 0 <= p < Zlength l1 /\ Znth p l1 0 = v) <->
   (exists q, 0 <= q < Zlength l2 /\ Znth q l2 0 = v)).
Proof.
  intros l1 l2 v Hperm.
  split; intros [p [Hp Hv]].
  - apply In_Znth_bridge__compressed_keys.
    rewrite <- Hv.
    apply (Permutation_in _ Hperm).
    apply Znth_In_bridge__compressed_keys. exact Hp.
  - apply In_Znth_bridge__compressed_keys.
    rewrite <- Hv.
    apply (Permutation_in _ (Permutation_sym Hperm)).
    apply Znth_In_bridge__compressed_keys. exact Hp.
Qed.
Lemma dedup_to_compressed__compressed_keys :
  forall (a raw sorted cur : list Z) (n uniq scanned : Z),
    n = Zlength a ->
    0 < n ->
    Zlength raw = 2 * n ->
    Zlength sorted = 2 * n ->
    scanned = 2 * n ->
    Permutation raw sorted ->
    ValsRawPrefix a raw n ->
    DedupState sorted cur uniq scanned ->
    CompressedKeys a cur uniq.
Proof.
  intros a raw sorted cur n uniq scanned Hn Ha Hraw Hsorted Hscan Hperm Hvr Hdedup.
  subst n.
  unfold DedupState in Hdedup.
  destruct Hdedup as [Hsi [Hfwd [Hbwd [Hne Hrest]]]].
  unfold CompressedKeys.
  split; [exact Hsi | split].
  - intros i Hi.
    destruct (Hvr i Hi) as [Hr0 Hr1].
    split.
    + assert (exists q, 0 <= q < Zlength sorted /\ Znth q sorted 0 = KeyAt a i)
        as [q [Hq Hqv]].
      { apply (proj1 (perm_member_transfer__compressed_keys raw sorted (KeyAt a i) Hperm)).
        exists (2 * i). split; [lia | exact Hr0]. }
      destruct (Hfwd q ltac:(lia)) as [k [Hk Hkv]].
      exists k. split; [exact Hk | ]. rewrite Hkv. exact Hqv.
    + assert (exists q, 0 <= q < Zlength sorted /\ Znth q sorted 0 = KeyAt a i + 1)
        as [q [Hq Hqv]].
      { apply (proj1 (perm_member_transfer__compressed_keys raw sorted (KeyAt a i + 1) Hperm)).
        exists (2 * i + 1). split; [lia | exact Hr1]. }
      destruct (Hfwd q ltac:(lia)) as [k [Hk Hkv]].
      exists k. split; [exact Hk | ]. rewrite Hkv. exact Hqv.
  - intros r Hr.
    destruct (Hbwd r Hr) as [p [Hp Hpv]].
    assert (exists q, 0 <= q < Zlength raw /\ Znth q raw 0 = Znth p sorted 0)
      as [q [Hq Hqv]].
    { apply (proj2 (perm_member_transfer__compressed_keys raw sorted (Znth p sorted 0) Hperm)).
      exists p. split; [lia | reflexivity]. }
    assert (0 <= q / 2 < Zlength a) as Hj.
    { split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; lia. }
    pose proof (Z.div_mod q 2 ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound q 2 ltac:(lia)) as Hmb.
    destruct (Hvr (q / 2) Hj) as [Hq0 Hq1].
    remember (q / 2) as j eqn:Hje.
    exists j.
    split; [exact Hj | ].
    assert (q = 2 * j \/ q = 2 * j + 1) as [Heq | Heq] by lia.
    + left. rewrite Hpv, <- Hqv, Heq. exact Hq0.
    + right. rewrite Hpv, <- Hqv, Heq. exact Hq1.
Qed.
Lemma maxbit_lowbit_bounds__bit_clear_loop : forall t, 0 < t -> 0 < MaxBitLowbit t <= t.
Proof.
  intros t Ht. unfold MaxBitLowbit. split.
  - pose proof (Z.add_lor_land t (-t)) as Hlor.
    assert (Hneg : Z.lor t (-t) < 0).
    { destruct (Z_lt_le_dec (Z.lor t (-t)) 0) as [Hl | Hl]; [ exact Hl | ].
      exfalso. apply Z.lor_nonneg in Hl. lia. }
    lia.
  - pose proof (Z.sub_land_same_l t (-t)) as Hsub.
    assert (0 <= Z.land t (Z.lnot (-t))) by (apply Z.land_nonneg; lia).
    lia.
Qed.
Lemma range_max_sentinel__bit_clear_loop : forall m lo hi,
  (forall r, lo <= r < hi -> Znth r m 0 = MaxBitNeg) ->
  RangeMax m lo hi = MaxBitNeg.
Proof.
  intros m lo hi H. unfold RangeMax.
  assert (Hgen : forall L : list Z, (forall r, In r L -> Znth r m 0 = MaxBitNeg) ->
      fold_right Z.max MaxBitNeg (map (fun r => Znth r m 0) L) = MaxBitNeg).
  { intros L. induction L as [| a L IHL]; simpl; intros HL; [ reflexivity | ].
    rewrite (HL a) by (left; reflexivity).
    rewrite IHL by (intros r Hr; apply HL; right; exact Hr).
    apply Z.max_id. }
  apply Hgen. intros r Hr. apply H. rewrite In_Zrange. exact Hr.
Qed.
Lemma maxbit_rep_sentinel__bit_clear_loop : forall m bit nvals,
  0 <= nvals ->
  Zlength m = nvals + 1 ->
  (forall k, 0 <= k <= nvals -> Znth k m 0 = MaxBitNeg) ->
  (forall t, 1 <= t <= nvals -> Znth t bit 0 = MaxBitNeg) ->
  MaxBitRep m bit nvals.
Proof.
  intros m bit nvals Hn Hlen Hm Hb. unfold MaxBitRep. split; [ exact Hlen | ].
  intros t Ht. rewrite (Hb t Ht). symmetry. apply range_max_sentinel__bit_clear_loop.
  intros r Hr. apply Hm.
  pose proof (maxbit_lowbit_bounds__bit_clear_loop t ltac:(lia)) as Hlb.
  unfold MaxBitNodeLo in Hr. lia.
Qed.
Lemma bit0_model_sentinel__bit_clear_loop : forall a vals dp m k uniq,
  k <= 0 ->
  Zlength m = uniq + 1 ->
  (forall r, 1 <= r <= uniq -> Znth r m 0 = MaxBitNeg) ->
  Bit0Model a vals dp m k uniq.
Proof.
  intros a vals dp m k uniq Hk Hlen Hm. unfold Bit0Model. split; [ exact Hlen | ].
  intros r Hr. split.
  - intros j Hj Hrank. lia.
  - left. apply Hm. exact Hr.
Qed.
Lemma bit1_model_sentinel__bit_clear_loop : forall a vals m k uniq,
  k <= 0 ->
  Zlength m = uniq + 1 ->
  (forall r, 1 <= r <= uniq -> Znth r m 0 = MaxBitNeg) ->
  Bit1Model a vals m k uniq.
Proof.
  intros a vals m k uniq Hk Hlen Hm. unfold Bit1Model. split; [ exact Hlen | ].
  intros r Hr. split.
  - intros j w Hj Hb Hrank. lia.
  - left. apply Hm. exact Hr.
Qed.
Lemma clamped_prefix_max_zero__bit_clear_loop : forall l k,
  k <= 0 -> ClampedPrefixMax l k 0.
Proof.
  intros l k Hk. unfold ClampedPrefixMax. split; [ lia | ]. split.
  - intros j Hj. lia.
  - left. reflexivity.
Qed.
Lemma clamped_best1_zero__bit_clear_loop : forall a k,
  k <= 0 -> ClampedBest1Upto a k 0.
Proof.
  intros a k Hk. unfold ClampedBest1Upto. split; [ lia | ]. split.
  - intros j w Hj Hb. lia.
  - left. reflexivity.
Qed.
Lemma dp0_prefix_zero__bit_clear_loop : forall a dp k,
  k <= 0 -> DP0Prefix a dp k.
Proof.
  intros a dp k Hk. unfold DP0Prefix. intros j Hj. lia.
Qed.
Lemma zrange_aux_Zlength__solver_result_spec : forall n low,
  Zlength (Zrange_aux low n) = Z.of_nat n.
Proof.
  induction n; intros; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons. rewrite IHn. lia.
Qed.
Lemma Zlength_Zrange__solver_result_spec : forall lo hi,
  lo <= hi -> Zlength (Zrange lo hi) = hi - lo.
Proof.
  intros. unfold Zrange. rewrite zrange_aux_Zlength__solver_result_spec. lia.
Qed.
Lemma Znth_Zrange_aux__solver_result_spec : forall n low k,
  0 <= k < Z.of_nat n -> Znth k (Zrange_aux low n) 0 = low + k.
Proof.
  induction n; intros low k Hk; simpl.
  - lia.
  - destruct (Z.eq_dec k 0) as [-> | Hne].
    + rewrite Znth0_cons. lia.
    + rewrite Znth_cons by lia. rewrite IHn by lia. lia.
Qed.
Lemma Znth_Zrange__solver_result_spec : forall lo hi k,
  0 <= k < hi - lo -> Znth k (Zrange lo hi) 0 = lo + k.
Proof.
  intros. unfold Zrange. rewrite Znth_Zrange_aux__solver_result_spec by lia. lia.
Qed.
Lemma mono_inc_filter__solver_result_spec : forall (p : Z -> bool) (l : list Z),
  mono_inc l -> mono_inc (filter p l).
Proof.
  intros p l.
  rewrite !mono_inc_iff_ind.
  induction l as [| x l IH]; simpl; intros H.
  - constructor.
  - inversion H as [| x0 l0 Hl Hfa]; subst.
    destruct (p x) eqn:Hpx.
    + constructor.
      * apply IH; assumption.
      * rewrite Forall_forall in *. intros y Hy.
        apply filter_In in Hy as [Hy _]. apply Hfa; assumption.
    + apply IH; assumption.
Qed.
Lemma mono_inc_Zrange__solver_result_spec : forall lo hi,
  mono_inc (Zrange lo hi).
Proof.
  intros lo hi i j Hi Hij Hj.
  destruct (Z_le_gt_dec lo hi) as [Hle | Hgt].
  - rewrite Zlength_Zrange__solver_result_spec in Hj by lia.
    rewrite !Znth_Zrange__solver_result_spec by lia. lia.
  - unfold Zrange in Hj.
    rewrite zrange_aux_Zlength__solver_result_spec in Hj. lia.
Qed.
Lemma mono_inc_NoDup__solver_result_spec : forall l, mono_inc l -> NoDup l.
Proof.
  intros l H. rewrite mono_inc_iff_ind in H.
  induction H as [| x l Hl IH Hfa].
  - constructor.
  - constructor; [| assumption].
    rewrite Forall_forall in Hfa. intros Hin. specialize (Hfa x Hin). lia.
Qed.
Lemma Zlength_incl__solver_result_spec : forall (l1 l2 : list Z),
  NoDup l1 -> incl l1 l2 -> Zlength l1 <= Zlength l2.
Proof.
  intros l1 l2 Hnd Hincl.
  pose proof (NoDup_incl_length Hnd Hincl) as H.
  rewrite !Zlength_correct. lia.
Qed.
Lemma fold_count_Zlength__solver_result_spec : forall (l : list Z),
  fold_right (fun _ acc : Z => 1 + acc) 0 l = Zlength l.
Proof.
  induction l as [| x l IH].
  - reflexivity.
  - cbn [fold_right]. rewrite IH, Zlength_cons. lia.
Qed.

(* ============ Part B: DifferenceCount bridges ============ *)
Lemma DifferenceCount_filter__solver_result_spec : forall (a b : list Z),
  DifferenceCount a b =
  Zlength (filter (fun x : Z => if prop_dec (Znth x a 0 <> Znth x b 0) then true else false)
                  (Zrange 0 (Zlength a))).
Proof.
  intros a b.
  unfold DifferenceCount, set_card, sum, enum, finite_Z_range'.
  apply fold_count_Zlength__solver_result_spec.
Qed.
Lemma Zlength_filter_split__solver_result_spec : forall (p : Z -> bool) (l : list Z),
  Zlength (filter p l) + Zlength (filter (fun x => negb (p x)) l) = Zlength l.
Proof.
  intros p l. induction l as [| x l IH]; cbn [filter].
  - reflexivity.
  - destruct (p x); cbn [negb]; rewrite !Zlength_cons; lia.
Qed.
Lemma agree_diff_sel__solver_result_spec : forall (a b : list Z) (x : Z),
  (if prop_dec (Znth x a 0 <> Znth x b 0) then true else false)
  = negb (if prop_dec (Znth x a 0 = Znth x b 0) then true else false).
Proof.
  intros a b x.
  destruct (prop_dec (Znth x a 0 <> Znth x b 0)) as [H1 | H1];
  destruct (prop_dec (Znth x a 0 = Znth x b 0)) as [H2 | H2];
  cbn [negb]; try reflexivity; try contradiction.
Qed.
Lemma agree_count__solver_result_spec : forall (a b : list Z),
  Zlength (filter (fun x : Z => if prop_dec (Znth x a 0 = Znth x b 0) then true else false)
                  (Zrange 0 (Zlength a)))
  + DifferenceCount a b = Zlength a.
Proof.
  intros a b.
  pose proof (Zlength_nonneg a) as Hn.
  rewrite DifferenceCount_filter__solver_result_spec.
  erewrite filter_ext with
    (f := fun x : Z => if prop_dec (Znth x a 0 <> Znth x b 0) then true else false)
    (g := fun x : Z => negb (if prop_dec (Znth x a 0 = Znth x b 0) then true else false))
    by (intros; apply agree_diff_sel__solver_result_spec).
  rewrite Zlength_filter_split__solver_result_spec.
  rewrite Zlength_Zrange__solver_result_spec by lia. lia.
Qed.
Lemma count_agree_bound__solver_result_spec : forall (a b s : list Z),
  NoDup s ->
  (forall x, In x s -> 0 <= x < Zlength a /\ Znth x a 0 = Znth x b 0) ->
  DifferenceCount a b + Zlength s <= Zlength a.
Proof.
  intros a b s Hnd Hs.
  pose proof (agree_count__solver_result_spec a b) as Hcnt.
  assert (Hincl : incl s (filter (fun x : Z => if prop_dec (Znth x a 0 = Znth x b 0) then true else false)
                                 (Zrange 0 (Zlength a)))).
  { intros x Hx. apply filter_In. specialize (Hs x Hx) as [Hrange Heq].
    split.
    - apply In_Zrange. lia.
    - destruct (prop_dec (Znth x a 0 = Znth x b 0)); [reflexivity | contradiction]. }
  pose proof (Zlength_incl__solver_result_spec _ _ Hnd Hincl). lia.
Qed.
Lemma agree_set_exists__solver_result_spec : forall (a b : list Z),
  exists s, mono_inc s /\ Zlength s = Zlength a - DifferenceCount a b /\
    (forall x, In x s <-> (0 <= x < Zlength a /\ Znth x a 0 = Znth x b 0)).
Proof.
  intros a b.
  exists (filter (fun x : Z => if prop_dec (Znth x a 0 = Znth x b 0) then true else false)
                 (Zrange 0 (Zlength a))).
  split; [| split].
  - apply mono_inc_filter__solver_result_spec. apply mono_inc_Zrange__solver_result_spec.
  - pose proof (agree_count__solver_result_spec a b). lia.
  - intros x. rewrite filter_In. rewrite <- In_Zrange.
    split.
    + intros [Hr Hb]. split; [lia |].
      destruct (prop_dec (Znth x a 0 = Znth x b 0)); [assumption | discriminate].
    + intros [Hr Heq]. split; [lia |].
      destruct (prop_dec (Znth x a 0 = Znth x b 0)); [reflexivity | contradiction].
Qed.

(* ============ Part C: gap lemma and list builder ============ *)
Lemma mono_inc_gap__solver_result_spec : forall (l : list Z) (i j : Z),
  mono_inc l -> 0 <= i -> i <= j -> j < Zlength l ->
  Znth i l 0 + (j - i) <= Znth j l 0.
Proof.
  intros l i j Hm Hi Hij Hj.
  remember (Z.to_nat (j - i)) as k.
  revert j Heqk Hij Hj.
  induction k as [| k IH]; intros j Heqk Hij Hj.
  - assert (j = i) by lia. subst. lia.
  - assert (Hlt : Znth (j - 1) l 0 < Znth j l 0) by (apply Hm; lia).
    specialize (IH (j - 1) ltac:(lia) ltac:(lia) ltac:(lia)).
    lia.
Qed.
Lemma build_list__solver_result_spec : forall (n : Z) (g : Z -> Z),
  0 <= n ->
  exists b, Zlength b = n /\ (forall i, 0 <= i < n -> Znth i b 0 = g i).
Proof.
  intros n g Hn.
  assert (Hlen : Zlength (map g (Zrange 0 n)) = n).
  { rewrite Zlength_correct, length_map, <- Zlength_correct.
    rewrite Zlength_Zrange__solver_result_spec by lia. lia. }
  exists (map g (Zrange 0 n)).
  split; [exact Hlen |].
  intros i Hi.
  rewrite (Znth_indep (map g (Zrange 0 n)) i 0 (g 0)) by lia.
  unfold Znth. rewrite map_nth.
  change (nth (Z.to_nat i) (Zrange 0 n) 0) with (Znth i (Zrange 0 n) 0).
  rewrite Znth_Zrange__solver_result_spec by lia. f_equal; lia.
Qed.
Lemma build_mono__solver_result_spec : forall (n : Z) (g : Z -> Z),
  0 <= n ->
  (forall i, 0 <= i -> i + 1 < n -> g i < g (i + 1)) ->
  exists b, Zlength b = n /\ mono_inc b /\ (forall i, 0 <= i < n -> Znth i b 0 = g i).
Proof.
  intros n g Hn Hstep.
  destruct (build_list__solver_result_spec n g Hn) as [b [Hlen Hb]].
  exists b. split; [exact Hlen | split; [| exact Hb]].
  rewrite mono_inc_iff_adjacent.
  intros i Hi Hb1. rewrite Hlen in Hb1.
  rewrite !Hb by lia. apply Hstep; lia.
Qed.

(* ============ Part D: prefix-max fold over a kept-index list ============ *)
Lemma In_index__solver_result_spec : forall (l : list Z) (x : Z),
  In x l -> exists q, 0 <= q < Zlength l /\ Znth q l 0 = x.
Proof.
  induction l as [| y l IH]; intros x Hin; simpl in Hin.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + exists 0. rewrite Zlength_cons. pose proof (Zlength_nonneg l).
      split; [lia |]. apply Znth0_cons.
    + destruct (IH x Hin) as [q [Hq Hval]].
      exists (q + 1). rewrite Zlength_cons. split; [lia |].
      rewrite Znth_cons by lia. replace (q + 1 - 1) with q by lia. exact Hval.
Qed.
Lemma foldmax_mono__solver_result_spec :
  forall (K : Z -> Z) (s : list Z) (K0 i j : Z),
  i <= j ->
  fold_right (fun x acc => if Z.leb x i then Z.max (K x) acc else acc) K0 s
  <= fold_right (fun x acc => if Z.leb x j then Z.max (K x) acc else acc) K0 s.
Proof.
  intros K s K0 i j Hij.
  induction s as [| x s IH]; cbn [fold_right].
  - lia.
  - destruct (Z.leb x i) eqn:Hi; destruct (Z.leb x j) eqn:Hj;
      try (apply Z.leb_le in Hi); try (apply Z.leb_gt in Hi);
      try (apply Z.leb_le in Hj); try (apply Z.leb_gt in Hj); try lia.
Qed.
Lemma foldmax_ub__solver_result_spec :
  forall (K : Z -> Z) (s : list Z) (K0 i v : Z),
  K0 <= v ->
  (forall x, In x s -> x <= i -> K x <= v) ->
  fold_right (fun x acc => if Z.leb x i then Z.max (K x) acc else acc) K0 s <= v.
Proof.
  intros K s K0 i v HK0 Hall.
  induction s as [| x s IH]; cbn [fold_right].
  - exact HK0.
  - assert (IHs : fold_right (fun y acc => if Z.leb y i then Z.max (K y) acc else acc) K0 s <= v).
    { apply IH. intros y Hy Hyi. apply Hall; [right; exact Hy | exact Hyi]. }
    destruct (Z.leb x i) eqn:Hi; [| exact IHs].
    apply Z.leb_le in Hi.
    assert (K x <= v) by (apply Hall; [left; reflexivity | exact Hi]).
    lia.
Qed.
Lemma foldmax_lb__solver_result_spec :
  forall (K : Z -> Z) (s : list Z) (K0 i x : Z),
  In x s -> x <= i ->
  K x <= fold_right (fun y acc => if Z.leb y i then Z.max (K y) acc else acc) K0 s.
Proof.
  intros K s K0 i x Hin Hxi.
  induction s as [| y s IH]; simpl in Hin.
  - contradiction.
  - cbn [fold_right].
    destruct Hin as [-> | Hin].
    + apply Z.leb_le in Hxi. rewrite Hxi. lia.
    + specialize (IH Hin).
      destruct (Z.leb y i); lia.
Qed.

(* ============ Part E: realising a Keep0List as an array ============ *)
Lemma mono_inc_head_le__solver_result_spec : forall (s : list Z) (x : Z),
  mono_inc s -> In x s -> In (Znth 0 s 0) s /\ Znth 0 s 0 <= x.
Proof.
  intros s x Hm Hin.
  destruct (In_index__solver_result_spec s x Hin) as [q [Hq Hv]].
  split.
  - apply (Znth_In_Zlength s 0 0). lia.
  - destruct (Z.eq_dec q 0) as [-> | Hne]; [lia |].
    assert (Znth 0 s 0 < Znth q s 0) by (apply Hm; lia). lia.
Qed.
Lemma keep0_In_bound__solver_result_spec : forall (a s : list Z),
  Keep0List a s -> forall x, In x s -> 0 <= x < Zlength a.
Proof.
  intros a s [Hm [Hb Hk]] x Hin.
  destruct (In_index__solver_result_spec s x Hin) as [q [Hq Hv]].
  rewrite <- Hv. apply Hb. lia.
Qed.
Lemma keep0_key_mono__solver_result_spec : forall (a s : list Z),
  Keep0List a s -> forall x y, In x s -> In y s -> y <= x -> KeyAt a y <= KeyAt a x.
Proof.
  intros a s Hk0 x y Hx Hy Hle.
  destruct Hk0 as [Hm [Hb Hk]].
  destruct (In_index__solver_result_spec s x Hx) as [qx [Hqx Hvx]].
  destruct (In_index__solver_result_spec s y Hy) as [qy [Hqy Hvy]].
  rewrite <- Hvx, <- Hvy.
  destruct (Z.lt_trichotomy qy qx) as [Hlt | [Heq | Hgt]].
  - apply Hk; lia.
  - subst qy. lia.
  - exfalso. assert (Znth qx s 0 < Znth qy s 0) by (apply Hm; lia). lia.
Qed.
Lemma keep0_realise__solver_result_spec : forall (a s : list Z),
  Keep0List a s ->
  exists b, Zlength b = Zlength a /\ mono_inc b /\
            DifferenceCount a b + Zlength s <= Zlength a.
Proof.
  intros a s Hk0.
  pose proof Hk0 as Hk0copy.
  destruct Hk0copy as [Hm [Hb Hk]].
  pose proof (Zlength_nonneg a) as Hna.
  pose (M := fun i : Z =>
    fold_right (fun x acc => if Z.leb x i then Z.max (KeyAt a x) acc else acc)
               (KeyAt a (Znth 0 s 0)) s).
  assert (Hstep : forall i : Z, 0 <= i -> i + 1 < Zlength a -> i + M i < (i + 1) + M (i + 1)).
  { intros i Hi Hi1. unfold M.
    pose proof (foldmax_mono__solver_result_spec (KeyAt a) s (KeyAt a (Znth 0 s 0)) i (i + 1)
                  ltac:(lia)).
    lia. }
  destruct (build_mono__solver_result_spec (Zlength a) (fun i : Z => i + M i) Hna Hstep)
    as [b [Hlen [Hmb Hval]]].
  exists b. split; [exact Hlen | split; [exact Hmb |]].
  apply count_agree_bound__solver_result_spec.
  - apply mono_inc_NoDup__solver_result_spec. exact Hm.
  - intros x Hx.
    assert (Hxr : 0 <= x < Zlength a)
      by (apply (keep0_In_bound__solver_result_spec a s Hk0); exact Hx).
    split; [exact Hxr |].
    rewrite Hval by lia. cbv beta.
    destruct (mono_inc_head_le__solver_result_spec s x Hm Hx) as [Hhin Hhle].
    assert (HM : M x = KeyAt a x).
    { apply Z.le_antisymm.
      - unfold M. apply foldmax_ub__solver_result_spec.
        + apply (keep0_key_mono__solver_result_spec a s Hk0); assumption.
        + intros y Hy Hyx. apply (keep0_key_mono__solver_result_spec a s Hk0); assumption.
      - unfold M. apply foldmax_lb__solver_result_spec; [exact Hx | lia]. }
    unfold KeyAt in HM. lia.
Qed.

(* ============ Part F: inverting a mono_inc array into a Keep0List ============ *)
Lemma mono_inc_to_keep0__solver_result_spec : forall (a b : list Z),
  Zlength b = Zlength a -> mono_inc b ->
  exists s, Keep0List a s /\ Zlength s = Zlength a - DifferenceCount a b.
Proof.
  intros a b Hlen Hmb.
  destruct (agree_set_exists__solver_result_spec a b) as [s [Hms [Hslen Hmem]]].
  exists s. split; [| exact Hslen].
  split; [exact Hms | split].
  - intros p Hp.
    assert (Hin : In (Znth p s 0) s) by (apply (Znth_In_Zlength s 0 p); lia).
    apply Hmem in Hin. tauto.
  - intros p q Hp Hpq Hq.
    assert (Hip : In (Znth p s 0) s) by (apply (Znth_In_Zlength s 0 p); lia).
    assert (Hiq : In (Znth q s 0) s) by (apply (Znth_In_Zlength s 0 q); lia).
    apply Hmem in Hip. apply Hmem in Hiq.
    destruct Hip as [Hpr Hpe]. destruct Hiq as [Hqr Hqe].
    assert (Hlt : Znth p s 0 < Znth q s 0) by (apply Hms; lia).
    pose proof (mono_inc_gap__solver_result_spec b (Znth p s 0) (Znth q s 0) Hmb
                  ltac:(lia) ltac:(lia) ltac:(lia)).
    unfold KeyAt. lia.
Qed.

(* ============ Part G0: the array with one index removed ============ *)
Lemma remove_Zlength__solver_result_spec : forall (b : list Z) (d : Z),
  0 <= d < Zlength b ->
  Zlength (sublist 0 d b ++ sublist (d + 1) (Zlength b) b) = Zlength b - 1.
Proof.
  intros b d Hd.
  rewrite Zlength_app.
  rewrite (Zlength_sublist 0 d b) by lia.
  rewrite (Zlength_sublist (d + 1) (Zlength b) b) by lia.
  lia.
Qed.
Lemma remove_Znth__solver_result_spec : forall (b : list Z) (d q : Z),
  0 <= d < Zlength b -> 0 <= q < Zlength b - 1 ->
  Znth q (sublist 0 d b ++ sublist (d + 1) (Zlength b) b) 0
  = Znth (if Z.ltb q d then q else q + 1) b 0.
Proof.
  intros b d q Hd Hq.
  assert (Hl1 : Zlength (sublist 0 d b) = d) by (rewrite Zlength_sublist by lia; lia).
  destruct (Z.ltb q d) eqn:Hlt.
  - apply Z.ltb_lt in Hlt.
    rewrite app_Znth1 by lia.
    rewrite Znth_sublist by lia. f_equal; lia.
  - apply Z.ltb_ge in Hlt.
    rewrite app_Znth2 by lia.
    rewrite Hl1.
    rewrite Znth_sublist by lia. f_equal; lia.
Qed.

(* ============ Part G: realising a Keep1List as an almost increasing array ============ *)
Lemma keep1_In_bound__solver_result_spec : forall (a s : list Z) (d : Z),
  Keep1List a d s -> forall x, In x s -> 0 <= x < Zlength a /\ x <> d.
Proof.
  intros a s d [Hd [Hm [Hb Hk]]] x Hin.
  destruct (In_index__solver_result_spec s x Hin) as [q [Hq Hv]].
  rewrite <- Hv. apply Hb. lia.
Qed.
Lemma keep1_key_mono__solver_result_spec : forall (a s : list Z) (d : Z),
  Keep1List a d s ->
  forall x y, In x s -> In y s -> y <= x -> KeyShift a d y <= KeyShift a d x.
Proof.
  intros a s d [Hd [Hm [Hb Hk]]] x y Hx Hy Hle.
  destruct (In_index__solver_result_spec s x Hx) as [qx [Hqx Hvx]].
  destruct (In_index__solver_result_spec s y Hy) as [qy [Hqy Hvy]].
  rewrite <- Hvx, <- Hvy.
  destruct (Z.lt_trichotomy qy qx) as [Hlt | [Heq | Hgt]].
  - apply Hk; lia.
  - subst qy. lia.
  - exfalso. assert (Znth qx s 0 < Znth qy s 0) by (apply Hm; lia). lia.
Qed.
Lemma keep1_realise__solver_result_spec : forall (a s : list Z) (d : Z),
  Keep1List a d s ->
  exists b, Zlength b = Zlength a /\ AlmostIncreasing b /\
            DifferenceCount a b + Zlength s + 1 <= Zlength a.
Proof.
  intros a s d Hk1.
  pose proof Hk1 as Hk1copy.
  destruct Hk1copy as [Hd [Hm [Hb Hk]]].
  pose proof (Zlength_nonneg a) as Hna.
  pose (M := fun i : Z =>
    fold_right (fun x acc => if Z.leb x i then Z.max (KeyShift a d x) acc else acc)
               (KeyShift a d (Znth 0 s 0)) s).
  pose (g := fun i : Z =>
    if Z.eqb i d then Znth d a 0 else (i - (if Z.ltb d i then 1 else 0)) + M i).
  destruct (build_list__solver_result_spec (Zlength a) g Hna) as [b [Hlen Hval]].
  assert (Hne : forall i j, 0 <= i < Zlength a -> 0 <= j < Zlength a ->
                  i <> d -> j <> d -> i < j -> Znth i b 0 < Znth j b 0).
  { intros i j Hi Hj Hid Hjd Hij.
    rewrite !Hval by lia. cbv beta. unfold g.
    destruct (Z.eqb i d) eqn:Ei; [apply Z.eqb_eq in Ei; contradiction |].
    destruct (Z.eqb j d) eqn:Ej; [apply Z.eqb_eq in Ej; contradiction |].
    assert (HMle : M i <= M j).
    { unfold M. apply foldmax_mono__solver_result_spec. lia. }
    destruct (Z.ltb d i) eqn:Di; destruct (Z.ltb d j) eqn:Dj;
      try (apply Z.ltb_lt in Di); try (apply Z.ltb_ge in Di);
      try (apply Z.ltb_lt in Dj); try (apply Z.ltb_ge in Dj); lia. }
  assert (Hkeep : forall x, In x s -> Znth x a 0 = Znth x b 0).
  { intros x Hx.
    destruct (keep1_In_bound__solver_result_spec a s d Hk1 x Hx) as [Hxr Hxd].
    destruct (mono_inc_head_le__solver_result_spec s x Hm Hx) as [Hhin Hhle].
    assert (HM : M x = KeyShift a d x).
    { apply Z.le_antisymm.
      - unfold M. apply foldmax_ub__solver_result_spec.
        + apply (keep1_key_mono__solver_result_spec a s d Hk1); assumption.
        + intros y Hy Hyx. apply (keep1_key_mono__solver_result_spec a s d Hk1); assumption.
      - unfold M. apply foldmax_lb__solver_result_spec; [exact Hx | lia]. }
    rewrite Hval by lia. cbv beta. unfold g.
    destruct (Z.eqb x d) eqn:Ex; [apply Z.eqb_eq in Ex; contradiction |].
    rewrite HM. unfold KeyShift, KeyAt.
    destruct (Z.ltb d x); lia. }
  assert (Hdkeep : Znth d a 0 = Znth d b 0).
  { rewrite Hval by lia. cbv beta. unfold g.
    rewrite Z.eqb_refl. reflexivity. }
  exists b. split; [exact Hlen | split].
  - right. exists d. split; [lia |].
    intros p q Hp Hpq Hq.
    rewrite remove_Zlength__solver_result_spec in Hq by lia.
    rewrite !remove_Znth__solver_result_spec by lia.
    destruct (Z.ltb p d) eqn:Ep; destruct (Z.ltb q d) eqn:Eq;
      try (apply Z.ltb_lt in Ep); try (apply Z.ltb_ge in Ep);
      try (apply Z.ltb_lt in Eq); try (apply Z.ltb_ge in Eq);
      apply Hne; lia.
  - assert (Hnodup : NoDup (d :: s)).
    { constructor.
      - intros Hin. destruct (keep1_In_bound__solver_result_spec a s d Hk1 d Hin) as [_ Hcon].
        apply Hcon. reflexivity.
      - apply mono_inc_NoDup__solver_result_spec. exact Hm. }
    pose proof (count_agree_bound__solver_result_spec a b (d :: s) Hnodup) as Hcnt.
    rewrite Zlength_cons in Hcnt.
    assert (Hall : forall x, In x (d :: s) -> 0 <= x < Zlength a /\ Znth x a 0 = Znth x b 0).
    { intros x [Heq | Hin].
      - subst x. split; [lia | exact Hdkeep].
      - destruct (keep1_In_bound__solver_result_spec a s d Hk1 x Hin) as [Hxr _].
        split; [exact Hxr | apply Hkeep; exact Hin]. }
    specialize (Hcnt Hall). lia.
Qed.

(* ============ Part H: inverting an almost increasing array ============ *)
Lemma remove_Znth_at__solver_result_spec : forall (b : list Z) (d i : Z),
  0 <= d < Zlength b -> 0 <= i < Zlength b -> i <> d ->
  0 <= (if Z.ltb d i then i - 1 else i) < Zlength b - 1 /\
  Znth (if Z.ltb d i then i - 1 else i)
       (sublist 0 d b ++ sublist (d + 1) (Zlength b) b) 0 = Znth i b 0.
Proof.
  intros b d i Hd Hi Hid.
  destruct (Z.ltb d i) eqn:Di.
  - apply Z.ltb_lt in Di.
    split; [lia |].
    rewrite remove_Znth__solver_result_spec by lia.
    destruct (Z.ltb (i - 1) d) eqn:E.
    + apply Z.ltb_lt in E. lia.
    + f_equal. lia.
  - apply Z.ltb_ge in Di.
    assert (Hlt : i < d) by lia.
    split; [lia |].
    rewrite remove_Znth__solver_result_spec by lia.
    destruct (Z.ltb i d) eqn:E.
    + reflexivity.
    + apply Z.ltb_ge in E. lia.
Qed.
Lemma almost_del_to_keep1__solver_result_spec : forall (a b : list Z) (d : Z),
  Zlength b = Zlength a -> 0 <= d < Zlength b ->
  mono_inc (sublist 0 d b ++ sublist (d + 1) (Zlength b) b) ->
  exists s, Keep1List a d s /\ Zlength s + 1 + DifferenceCount a b >= Zlength a.
Proof.
  intros a b d Hlen Hd Hmc.
  destruct (agree_set_exists__solver_result_spec a b) as [A [HmA [HAlen HmemA]]].
  exists (filter (fun x => negb (Z.eqb x d)) A).
  assert (Hmem : forall x, In x (filter (fun x => negb (Z.eqb x d)) A) <->
                   ((0 <= x < Zlength a /\ Znth x a 0 = Znth x b 0) /\ x <> d)).
  { intros x. rewrite filter_In. rewrite HmemA.
    split.
    - intros [H1 H2]. split; [exact H1 |].
      destruct (Z.eqb x d) eqn:E; [discriminate | apply Z.eqb_neq in E; exact E].
    - intros [H1 H2]. split; [exact H1 |].
      destruct (Z.eqb x d) eqn:E; [apply Z.eqb_eq in E; contradiction | reflexivity]. }
  assert (Hms : mono_inc (filter (fun x => negb (Z.eqb x d)) A))
    by (apply mono_inc_filter__solver_result_spec; exact HmA).
  split.
  - split; [lia | split; [exact Hms | split]].
    + intros p Hp.
      assert (Hin : In (Znth p (filter (fun x => negb (Z.eqb x d)) A) 0)
                       (filter (fun x => negb (Z.eqb x d)) A))
        by (apply (Znth_In_Zlength _ 0 p); lia).
      apply Hmem in Hin. destruct Hin as [[Hr _] Hnd]. split; [lia | exact Hnd].
    + intros p q Hp Hpq Hq.
      remember (filter (fun x => negb (Z.eqb x d)) A) as s eqn:Hs.
      assert (Hip : In (Znth p s 0) s) by (apply (Znth_In_Zlength s 0 p); lia).
      assert (Hiq : In (Znth q s 0) s) by (apply (Znth_In_Zlength s 0 q); lia).
      apply Hmem in Hip. apply Hmem in Hiq.
      destruct Hip as [[Hpr Hpe] Hpd]. destruct Hiq as [[Hqr Hqe] Hqd].
      assert (Hlt : Znth p s 0 < Znth q s 0) by (apply Hms; lia).
      destruct (remove_Znth_at__solver_result_spec b d (Znth p s 0) Hd ltac:(lia) Hpd)
        as [Hbp Hep].
      destruct (remove_Znth_at__solver_result_spec b d (Znth q s 0) Hd ltac:(lia) Hqd)
        as [Hbq Heq].
      assert (Hposlt : (if Z.ltb d (Znth p s 0) then Znth p s 0 - 1 else Znth p s 0)
                       <= (if Z.ltb d (Znth q s 0) then Znth q s 0 - 1 else Znth q s 0)).
      { destruct (Z.ltb d (Znth p s 0)) eqn:Dp; destruct (Z.ltb d (Znth q s 0)) eqn:Dq;
          try (apply Z.ltb_lt in Dp); try (apply Z.ltb_ge in Dp);
          try (apply Z.ltb_lt in Dq); try (apply Z.ltb_ge in Dq); lia. }
      pose proof (mono_inc_gap__solver_result_spec
                    (sublist 0 d b ++ sublist (d + 1) (Zlength b) b)
                    (if Z.ltb d (Znth p s 0) then Znth p s 0 - 1 else Znth p s 0)
                    (if Z.ltb d (Znth q s 0) then Znth q s 0 - 1 else Znth q s 0)
                    Hmc ltac:(lia) Hposlt
                    ltac:(rewrite remove_Zlength__solver_result_spec by lia; lia)) as Hgap.
      rewrite Hep, Heq in Hgap.
      unfold KeyShift, KeyAt.
      destruct (Z.ltb d (Znth p s 0)) eqn:Dp; destruct (Z.ltb d (Znth q s 0)) eqn:Dq;
        try (apply Z.ltb_lt in Dp); try (apply Z.ltb_ge in Dp);
        try (apply Z.ltb_lt in Dq); try (apply Z.ltb_ge in Dq); lia.
  - assert (Hincl : incl A (d :: filter (fun x => negb (Z.eqb x d)) A)).
    { intros x Hx. destruct (Z.eq_dec x d) as [-> | Hnd]; [left; reflexivity |].
      right. apply Hmem. split; [apply HmemA; exact Hx | exact Hnd]. }
    pose proof (Zlength_incl__solver_result_spec A _
                  (mono_inc_NoDup__solver_result_spec A HmA) Hincl) as Hle.
    rewrite Zlength_cons in Hle. lia.
Qed.
Lemma almost_increasing_to_keep__solver_result_spec : forall (a b : list Z),
  Zlength b = Zlength a -> AlmostIncreasing b ->
  (exists s, Keep0List a s /\ Zlength s + DifferenceCount a b >= Zlength a)
  \/ (exists d s, Keep1List a d s /\ Zlength s + 1 + DifferenceCount a b >= Zlength a).
Proof.
  intros a b Hlen [Hmb | [d [Hd Hmc]]].
  - left. destruct (mono_inc_to_keep0__solver_result_spec a b Hlen Hmb) as [s [Hk Hs]].
    exists s. split; [exact Hk | lia].
  - right. destruct (almost_del_to_keep1__solver_result_spec a b d Hlen Hd Hmc) as [s [Hk Hs]].
    exists d, s. split; [exact Hk | lia].
Qed.
Lemma max_value_sound__solver_result_spec : forall (A : Type) (X : A -> Prop) (f : A -> Z) (v : Z),
  max_value_of_subset Z.le X f v -> (forall x, X x -> f x <= v) /\ (exists x, X x /\ f x = v).
Proof.
  intros A X f v H.
  unfold max_value_of_subset, max_object_of_subset in H.
  destruct H as [x0 [[Hx0 Hub] Hfv]].
  split.
  - intros x Hx. rewrite <- Hfv. apply Hub. exact Hx.
  - exists x0. split; [exact Hx0 | exact Hfv].
Qed.
Lemma max_value_exists__solver_result_spec : forall (A : Type) (X : A -> Prop) (f : A -> Z) (K : Z),
  0 <= K ->
  (forall x, X x -> 0 <= f x <= K) ->
  (exists x, X x) ->
  exists v, max_value_of_subset Z.le X f v.
Proof.
  intros A X f K HK Hbd [x0 Hx0].
  assert (Hne : exists k, 0 <= k <= K /\ (exists x, X x /\ f x = k)).
  { exists (f x0). split; [apply Hbd; exact Hx0 | exists x0; split; [exact Hx0 | reflexivity]]. }
  destruct (max_n_in_range (fun k => exists x, X x /\ f x = k) K HK Hne)
    as [m [[xm [Hxm Hfm]] [Hmr Hmax]]].
  exists m.
  unfold max_value_of_subset, max_object_of_subset.
  exists xm. split; [split |].
  - exact Hxm.
  - intros y Hy. rewrite Hfm. apply Hmax; [apply Hbd; exact Hy |].
    exists y. split; [exact Hy | reflexivity].
  - exact Hfm.
Qed.
Lemma keep0_card_bound__solver_result_spec : forall (a s : list Z),
  Keep0List a s -> 0 <= Zlength s <= Zlength a.
Proof.
  intros a s Hk. pose proof (Zlength_nonneg a) as Hna.
  split; [apply Zlength_nonneg |].
  assert (Hincl : incl s (Zrange 0 (Zlength a))).
  { intros x Hx. apply In_Zrange.
    apply (keep0_In_bound__solver_result_spec a s Hk x Hx). }
  pose proof (Zlength_incl__solver_result_spec s (Zrange 0 (Zlength a))
                (mono_inc_NoDup__solver_result_spec s (proj1 Hk)) Hincl) as H.
  rewrite Zlength_Zrange__solver_result_spec in H by lia. lia.
Qed.
Lemma keep1_card_bound__solver_result_spec : forall (a s : list Z) (d : Z),
  Keep1List a d s -> 0 <= Zlength s <= Zlength a.
Proof.
  intros a s d Hk. pose proof (Zlength_nonneg a) as Hna.
  split; [apply Zlength_nonneg |].
  assert (Hincl : incl s (Zrange 0 (Zlength a))).
  { intros x Hx. apply In_Zrange.
    apply (keep1_In_bound__solver_result_spec a s d Hk x Hx). }
  destruct Hk as [Hd [Hm Hrest]].
  pose proof (Zlength_incl__solver_result_spec s (Zrange 0 (Zlength a))
                (mono_inc_NoDup__solver_result_spec s Hm) Hincl) as H.
  rewrite Zlength_Zrange__solver_result_spec in H by lia. lia.
Qed.
Lemma mono_inc_last_max__solver_result_spec : forall (s : list Z) (x : Z),
  mono_inc s -> In x s -> x <= Znth (Zlength s - 1) s 0.
Proof.
  intros s x Hm Hin.
  destruct (In_index__solver_result_spec s x Hin) as [q [Hq Hv]].
  destruct (Z.eq_dec q (Zlength s - 1)) as [-> | Hne]; [lia |].
  assert (Znth q s 0 < Znth (Zlength s - 1) s 0) by (apply Hm; lia). lia.
Qed.
Lemma keep0_to_keep1__solver_result_spec : forall (a s : list Z) (d : Z),
  Keep0List a s -> 0 <= d < Zlength a -> (forall x, In x s -> x < d) ->
  Keep1List a d s.
Proof.
  intros a s d Hk Hd Hlt.
  pose proof Hk as Hkc. destruct Hkc as [Hm [Hb Hkey]].
  split; [exact Hd | split; [exact Hm | split]].
  - intros p Hp.
    assert (Hin : In (Znth p s 0) s) by (apply (Znth_In_Zlength s 0 p); lia).
    specialize (Hlt _ Hin). split; [apply Hb; lia | lia].
  - intros p q Hp Hpq Hq.
    assert (Hip : In (Znth p s 0) s) by (apply (Znth_In_Zlength s 0 p); lia).
    assert (Hiq : In (Znth q s 0) s) by (apply (Znth_In_Zlength s 0 q); lia).
    pose proof (Hlt _ Hip) as Hlp. pose proof (Hlt _ Hiq) as Hlq.
    pose proof (Hkey p q Hp Hpq Hq) as Hk2.
    unfold KeyShift.
    destruct (Z.ltb d (Znth p s 0)) eqn:E1; destruct (Z.ltb d (Znth q s 0)) eqn:E2;
      try (apply Z.ltb_lt in E1); try (apply Z.ltb_ge in E1);
      try (apply Z.ltb_lt in E2); try (apply Z.ltb_ge in E2); lia.
Qed.
Lemma keep1_below_to_keep0__solver_result_spec : forall (a s : list Z) (d : Z),
  Keep1List a d s -> (forall x, In x s -> x < d) -> Keep0List a s.
Proof.
  intros a s d Hk Hlt.
  pose proof Hk as Hkc. destruct Hkc as [Hd [Hm [Hb Hkey]]].
  split; [exact Hm | split].
  - intros p Hp. apply Hb; lia.
  - intros p q Hp Hpq Hq.
    assert (Hip : In (Znth p s 0) s) by (apply (Znth_In_Zlength s 0 p); lia).
    assert (Hiq : In (Znth q s 0) s) by (apply (Znth_In_Zlength s 0 q); lia).
    pose proof (Hlt _ Hip) as Hlp. pose proof (Hlt _ Hiq) as Hlq.
    pose proof (Hkey p q Hp Hpq Hq) as Hk2.
    unfold KeyShift in Hk2.
    destruct (Z.ltb d (Znth p s 0)) eqn:E1; destruct (Z.ltb d (Znth q s 0)) eqn:E2;
      try (apply Z.ltb_lt in E1); try (apply Z.ltb_ge in E1);
      try (apply Z.ltb_lt in E2); try (apply Z.ltb_ge in E2); lia.
Qed.
Lemma keep0_nil__solver_result_spec : forall (a : list Z), Keep0List a nil.
Proof.
  intros a. split; [apply mono_inc_nil | split];
  intros; rewrite Zlength_nil in *; lia.
Qed.
Lemma keep1_nil__solver_result_spec : forall (a : list Z) (d : Z),
  0 <= d < Zlength a -> Keep1List a d nil.
Proof.
  intros a d Hd. split; [exact Hd | split; [apply mono_inc_nil | split]];
  intros; rewrite Zlength_nil in *; lia.
Qed.
Lemma best0_max__solver_result_spec : forall (a dp0 : list Z) (n best0 : Z),
  n = Zlength a ->
  DP0Prefix a dp0 n ->
  ClampedPrefixMax dp0 n best0 ->
  (forall s, Keep0List a s -> Zlength s <= best0)
  /\ (exists s, Keep0List a s /\ Zlength s = best0).
Proof.
  intros a dp0 n best0 Hn Hdp Hcl.
  unfold DP0Prefix in Hdp. unfold ClampedPrefixMax in Hcl.
  destruct Hcl as [Hnn [Hub Hat]].
  split.
  - intros s Hk.
    pose proof (Zlength_nonneg s) as Hsn.
    destruct (Z.eq_dec (Zlength s) 0) as [Hz | Hnz]; [lia |].
    assert (Hjr : 0 <= Znth (Zlength s - 1) s 0 < Zlength a)
      by (apply (proj1 (proj2 Hk)); lia).
    pose proof (Hdp (Znth (Zlength s - 1) s 0) ltac:(lia)) as Hbe.
    unfold Best0EndingAt in Hbe.
    destruct (max_value_sound__solver_result_spec _ _ _ _ Hbe) as [Hsound _].
    assert (Hmem : Keep0List a s /\ 0 < Zlength s /\
                   Znth (Zlength s - 1) s 0 = Znth (Zlength s - 1) s 0)
      by (split; [exact Hk | split; [lia | reflexivity]]).
    pose proof (Hsound s Hmem) as H1.
    pose proof (Hub (Znth (Zlength s - 1) s 0) ltac:(lia)) as H2.
    lia.
  - destruct Hat as [Hz | [j [Hj Hval]]].
    + exists nil. split; [apply keep0_nil__solver_result_spec | rewrite Zlength_nil; lia].
    + pose proof (Hdp j ltac:(lia)) as Hbe. rewrite Hval in Hbe.
      unfold Best0EndingAt in Hbe.
      destruct (max_value_sound__solver_result_spec _ _ _ _ Hbe) as [_ [s [[Hk _] Hlen]]].
      exists s. split; [exact Hk | exact Hlen].
Qed.
Lemma keep1_max__solver_result_spec : forall (a dp0 : list Z) (n best1 best0_prefix : Z),
  n = Zlength a -> 2 <= n ->
  DP0Prefix a dp0 n ->
  ClampedBest1Upto a n best1 ->
  ClampedPrefixMax dp0 (n - 1) best0_prefix ->
  (forall d s, Keep1List a d s -> Zlength s <= Z.max best1 best0_prefix)
  /\ (exists d s, Keep1List a d s /\ Zlength s = Z.max best1 best0_prefix).
Proof.
  intros a dp0 n best1 best0_prefix Hn Hn2 Hdp Hb1 Hpx.
  unfold DP0Prefix in Hdp.
  unfold ClampedBest1Upto in Hb1. unfold ClampedPrefixMax in Hpx.
  destruct Hb1 as [Hb1nn [Hb1ub Hb1at]].
  destruct Hpx as [Hpnn [Hpub Hpat]].
  split.
  - intros d s Hk.
    pose proof (Zlength_nonneg s) as Hsn.
    destruct (Z.eq_dec (Zlength s) 0) as [Hz | Hnz]; [lia |].
    pose proof Hk as Hkc. destruct Hkc as [Hd [Hm [Hbnd Hkey]]].
    assert (Hir : 0 <= Znth (Zlength s - 1) s 0 < Zlength a /\
                  Znth (Zlength s - 1) s 0 <> d) by (apply Hbnd; lia).
    destruct Hir as [Hir1 Hir2].
    destruct (Z.lt_trichotomy d (Znth (Zlength s - 1) s 0)) as [Hlt | [Heq | Hgt]].
    + assert (Hmemb : (exists d0, Keep1List a d0 s /\ d0 < Znth (Zlength s - 1) s 0) /\
        0 < Zlength s /\ Znth (Zlength s - 1) s 0 = Znth (Zlength s - 1) s 0).
      { split; [exists d; split; [exact Hk | lia] |].
        split; [lia | reflexivity]. }
      assert (Hnonempty : exists s0 : list Z,
        (exists d0, Keep1List a d0 s0 /\ d0 < Znth (Zlength s - 1) s 0) /\
        0 < Zlength s0 /\ Znth (Zlength s0 - 1) s0 0 = Znth (Zlength s - 1) s 0)
        by (exists s; exact Hmemb).
      destruct (max_value_exists__solver_result_spec (list Z)
                  (fun s0 : list Z =>
                     (exists d0, Keep1List a d0 s0 /\ d0 < Znth (Zlength s - 1) s 0) /\
                     0 < Zlength s0 /\ Znth (Zlength s0 - 1) s0 0 = Znth (Zlength s - 1) s 0)
                  (fun s0 : list Z => Zlength s0) (Zlength a)
                  (Zlength_nonneg a)
                  ltac:(intros x Hx; destruct Hx as [[d0 [Hkd _]] _];
                        apply (keep1_card_bound__solver_result_spec a x d0 Hkd))
                  Hnonempty) as [w Hw].
      destruct (max_value_sound__solver_result_spec _ _ _ _ Hw) as [Hsound _].
      pose proof (Hsound s Hmemb) as Hle1.
      pose proof (Hb1ub (Znth (Zlength s - 1) s 0) w ltac:(lia) Hw) as Hle2.
      lia.
    + exfalso. apply Hir2. lia.
    + assert (Hallb : forall x, In x s -> x < d).
      { intros x Hx. pose proof (mono_inc_last_max__solver_result_spec s x Hm Hx). lia. }
      assert (Hk0 : Keep0List a s)
        by (apply (keep1_below_to_keep0__solver_result_spec a s d Hk Hallb)).
      pose proof (Hdp (Znth (Zlength s - 1) s 0) ltac:(lia)) as Hbe.
      unfold Best0EndingAt in Hbe.
      destruct (max_value_sound__solver_result_spec _ _ _ _ Hbe) as [Hsound _].
      assert (Hmem : Keep0List a s /\ 0 < Zlength s /\
                     Znth (Zlength s - 1) s 0 = Znth (Zlength s - 1) s 0)
        by (split; [exact Hk0 | split; [lia | reflexivity]]).
      pose proof (Hsound s Hmem) as H1.
      pose proof (Hpub (Znth (Zlength s - 1) s 0) ltac:(lia)) as H2.
      lia.
  - destruct (Z_le_gt_dec best0_prefix best1) as [Hle | Hgt].
    + destruct Hb1at as [Hz | [j [w [Hj [Hbe Hw]]]]].
      * exists 0, nil. split;
        [apply keep1_nil__solver_result_spec; lia | rewrite Zlength_nil; lia].
      * unfold Best1EndingAt in Hbe.
        destruct (max_value_sound__solver_result_spec _ _ _ _ Hbe)
          as [_ [s [[[d0 [Hkd _]] _] Hlen]]].
        exists d0, s. split; [exact Hkd | lia].
    + destruct Hpat as [Hz | [j [Hj Hval]]].
      * exists 0, nil. split;
        [apply keep1_nil__solver_result_spec; lia | rewrite Zlength_nil; lia].
      * pose proof (Hdp j ltac:(lia)) as Hbe. rewrite Hval in Hbe.
        unfold Best0EndingAt in Hbe.
        destruct (max_value_sound__solver_result_spec _ _ _ _ Hbe)
          as [_ [s [[Hk0 [Hpos Hlast]] Hlen]]].
        exists (j + 1), s. split; [| lia].
        apply keep0_to_keep1__solver_result_spec; [exact Hk0 | lia |].
        intros x Hx.
        pose proof (mono_inc_last_max__solver_result_spec s x (proj1 Hk0) Hx). lia.
Qed.
Lemma spec_min_value__solver_result_spec : forall (a : list Z) (best0 keptDel out : Z),
  2 <= Zlength a ->
  (forall s, Keep0List a s -> Zlength s <= best0) ->
  (exists s, Keep0List a s /\ Zlength s = best0) ->
  (forall d s, Keep1List a d s -> Zlength s <= keptDel) ->
  (exists d s, Keep1List a d s /\ Zlength s = keptDel) ->
  out = Z.min (Zlength a - best0) (Zlength a - 1 - keptDel) ->
  Spec a out.
Proof.
  intros a best0 keptDel out Hn2 Hub0 Hat0 Hub1 Hat1 Hout.
  destruct Hat0 as [s0 [Hs0 Hs0len]].
  destruct Hat1 as [d1 [s1 [Hs1 Hs1len]]].
  assert (Hlow : forall b, Zlength b = Zlength a -> AlmostIncreasing b ->
                   out <= DifferenceCount a b).
  { intros b Hlen Hai.
    destruct (almost_increasing_to_keep__solver_result_spec a b Hlen Hai)
      as [[s [Hk Hge]] | [d [s [Hk Hge]]]].
    - pose proof (Hub0 s Hk). lia.
    - pose proof (Hub1 d s Hk). lia. }
  assert (Hattain : exists b, Zlength b = Zlength a /\ AlmostIncreasing b /\
                              DifferenceCount a b = out).
  { destruct (Z_le_gt_dec (Zlength a - best0) (Zlength a - 1 - keptDel)) as [Hc | Hc].
    - destruct (keep0_realise__solver_result_spec a s0 Hs0) as [b [Hlen [Hmb Hcnt]]].
      assert (Hai : AlmostIncreasing b) by (left; exact Hmb).
      exists b. split; [exact Hlen | split; [exact Hai |]].
      pose proof (Hlow b Hlen Hai). lia.
    - destruct (keep1_realise__solver_result_spec a s1 d1 Hs1) as [b [Hlen [Hai Hcnt]]].
      exists b. split; [exact Hlen | split; [exact Hai |]].
      pose proof (Hlow b Hlen Hai). lia. }
  destruct Hattain as [b0 [Hb0len [Hb0ai Hb0cnt]]].
  unfold Spec, min_value_of_subset, min_object_of_subset.
  exists out. split; [split |].
  - exists b0. split; [exact Hb0len | split; [exact Hb0ai | symmetry; exact Hb0cnt]].
  - intros w Hw. destruct Hw as [b [Hlen [Hai Hweq]]]. subst w.
    apply Hlow; assumption.
  - reflexivity.
Qed.
Lemma best_maxima_of_invariant__solver_result_spec :
  forall (a dp0 : list Z) (n best0 best1 best0_prefix : Z),
    n = Zlength a -> 2 <= n ->
    DP0Prefix a dp0 n ->
    ClampedPrefixMax dp0 n best0 ->
    ClampedBest1Upto a n best1 ->
    ClampedPrefixMax dp0 (n - 1) best0_prefix ->
    (forall s, Keep0List a s -> Zlength s <= best0)
    /\ (exists s, Keep0List a s /\ Zlength s = best0)
    /\ (forall d s, Keep1List a d s -> Zlength s <= Z.max best1 best0_prefix)
    /\ (exists d s, Keep1List a d s /\ Zlength s = Z.max best1 best0_prefix).
Proof.
  intros a dp0 n best0 best1 best0_prefix Hn Hn2 Hdp Hc0 Hb1 Hpx.
  destruct (best0_max__solver_result_spec a dp0 n best0 Hn Hdp Hc0) as [Hub0 Hat0].
  destruct (keep1_max__solver_result_spec a dp0 n best1 best0_prefix Hn Hn2 Hdp Hb1 Hpx)
    as [Hub1 Hat1].
  split; [exact Hub0 | split; [exact Hat0 | split; [exact Hub1 | exact Hat1]]].
Qed.
Lemma solver_spec_from_invariant__solver_result_spec :
  forall (a dp0 : list Z) (n best0 best1 best0_prefix out : Z),
    n = Zlength a -> 2 <= n ->
    DP0Prefix a dp0 n ->
    ClampedPrefixMax dp0 n best0 ->
    ClampedBest1Upto a n best1 ->
    ClampedPrefixMax dp0 (n - 1) best0_prefix ->
    out = Z.min (n - best0) ((n - 1) - Z.max best1 best0_prefix) ->
    Spec a out.
Proof.
  intros a dp0 n best0 best1 best0_prefix out Hn Hn2 Hdp Hc0 Hb1 Hpx Hout.
  destruct (best_maxima_of_invariant__solver_result_spec a dp0 n best0 best1 best0_prefix
              Hn Hn2 Hdp Hc0 Hb1 Hpx) as [Hub0 [Hat0 [Hub1 Hat1]]].
  apply (spec_min_value__solver_result_spec a best0 (Z.max best1 best0_prefix) out);
    try assumption; lia.
Qed.
Lemma mvs_intro__dp_body_branches_k1 :
  forall {A : Type} (X : A -> Prop) (f : A -> Z) (a : A),
    X a -> (forall b, X b -> f b <= f a) ->
    max_value_of_subset Z.le X f (f a).
Proof.
  intros A X f a Ha Hmax.
  exists a. split; [split |]; auto.
Qed.
Lemma mvs_ub__dp_body_branches_k1 :
  forall {A : Type} (X : A -> Prop) (f : A -> Z) (v : Z) (b : A),
    max_value_of_subset Z.le X f v -> X b -> f b <= v.
Proof.
  intros A X f v b Hv Hb.
  destruct Hv as [a [[Ha Hmax] Hfa]].
  subst v. apply Hmax; auto.
Qed.
Lemma mvs_unique__dp_body_branches_k1 :
  forall {A : Type} (X : A -> Prop) (f : A -> Z) (v1 v2 : Z),
    max_value_of_subset Z.le X f v1 ->
    max_value_of_subset Z.le X f v2 -> v1 = v2.
Proof.
  intros A X f v1 v2 H1 H2.
  destruct H1 as [a1 [[Ha1 Hm1] Hf1]].
  destruct H2 as [a2 [[Ha2 Hm2] Hf2]].
  specialize (Hm1 a2 Ha2). specialize (Hm2 a1 Ha1).
  lia.
Qed.
Lemma bounded_max_exists__dp_body_branches_k1 :
  forall {A : Type} (X : A -> Prop) (f : A -> Z) (B : Z),
    (forall a, X a -> f a <= B) ->
    (forall a, X a -> exists v, max_value_of_subset Z.le X f v).
Proof.
  intros A X f B Hb.
  assert (Haux : forall n : nat, forall a0, X a0 -> B - f a0 <= Z.of_nat n ->
                 exists v, max_value_of_subset Z.le X f v).
  { induction n; intros a0 Ha0 Hle.
    - exists (f a0). exists a0. split; [split |]; auto.
      intros c Hc. pose proof (Hb c Hc). simpl in Hle. lia.
    - destruct (classic (exists b, X b /\ f a0 < f b)) as [[b [Hb1 Hb2]] | Hno].
      + apply (IHn b); auto. lia.
      + exists (f a0). exists a0. split; [split |]; auto.
        intros c Hc. destruct (Z_le_gt_dec (f c) (f a0)); auto.
        exfalso. apply Hno. exists c. split; auto. lia. }
  intros a0 Ha0. apply (Haux (Z.to_nat (B - f a0)) a0); auto. lia.
Qed.
Lemma rank_order_iso__dp_body_branches_k1 :
  forall (vals : list Z) (uniq x rx y ry : Z),
    StrictIncPrefix vals uniq ->
    RankResult vals uniq x rx ->
    RankResult vals uniq y ry ->
    (x <= y <-> rx <= ry).
Proof.
  intros vals uniq x rx y ry Hs Hx Hy.
  destruct Hx as [Hrx [Hxv _]]. destruct Hy as [Hry [Hyv _]].
  unfold StrictIncPrefix in Hs.
  split; intros Hle.
  - destruct (Z_le_gt_dec rx ry) as [| Hgt]; auto.
    assert (Znth (ry - 1) vals 0 < Znth (rx - 1) vals 0) by (apply Hs; lia).
    lia.
  - destruct (Z.eq_dec rx ry) as [Heq |].
    + subst ry. lia.
    + assert (Znth (rx - 1) vals 0 < Znth (ry - 1) vals 0) by (apply Hs; lia).
      lia.
Qed.
Lemma rank_unique__dp_body_branches_k1 :
  forall (vals : list Z) (uniq x rx ry : Z),
    StrictIncPrefix vals uniq ->
    RankResult vals uniq x rx ->
    RankResult vals uniq x ry ->
    rx = ry.
Proof.
  intros vals uniq x rx ry Hs Hx Hy.
  pose proof (rank_order_iso__dp_body_branches_k1 vals uniq x rx x ry Hs Hx Hy) as H1.
  pose proof (rank_order_iso__dp_body_branches_k1 vals uniq x ry x rx Hs Hy Hx) as H2.
  lia.
Qed.
Lemma fold_max_ub__dp_body_branches_k1 :
  forall (l : list Z) (d x : Z), In x l -> x <= fold_right Z.max d l.
Proof.
  induction l as [| h t IH]; intros d x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin]; [lia |].
    pose proof (IH d x Hin). lia.
Qed.
Lemma fold_max_attain__dp_body_branches_k1 :
  forall (l : list Z) (d : Z),
    fold_right Z.max d l = d \/ In (fold_right Z.max d l) l.
Proof.
  induction l as [| h t IH]; intros d; simpl.
  - left; reflexivity.
  - destruct (IH d) as [He | Hin].
    + rewrite He. destruct (Z_le_gt_dec h d).
      * left. lia.
      * right. left. lia.
    + destruct (Z_le_gt_dec h (fold_right Z.max d t)).
      * right. right. replace (Z.max h (fold_right Z.max d t)) with (fold_right Z.max d t) by lia. auto.
      * right. left. lia.
Qed.
Lemma rangemax_ub__dp_body_branches_k1 :
  forall (m : list Z) (lo hi q : Z),
    lo <= q < hi -> Znth q m 0 <= RangeMax m lo hi.
Proof.
  intros m lo hi q Hq. unfold RangeMax.
  apply fold_max_ub__dp_body_branches_k1.
  apply (in_map (fun r : Z => Znth r m 0) (Zrange lo hi) q).
  apply In_Zrange. auto.
Qed.
Lemma rangemax_attain__dp_body_branches_k1 :
  forall (m : list Z) (lo hi : Z),
    RangeMax m lo hi = MaxBitNeg \/
    exists q, lo <= q < hi /\ RangeMax m lo hi = Znth q m 0.
Proof.
  intros m lo hi. unfold RangeMax.
  destruct (fold_max_attain__dp_body_branches_k1
              (map (fun r => Znth r m 0) (Zrange lo hi)) MaxBitNeg) as [He | Hin].
  - left; auto.
  - right. apply in_map_iff in Hin. destruct Hin as [q [Hq Hin]].
    exists q. split.
    + apply In_Zrange; auto.
    + lia.
Qed.
Lemma rangemax_prefix_char__dp_body_branches_k1 :
  forall (m : list Z) (r : Z),
    (forall q, 1 <= q <= r -> Znth q m 0 <= RangeMax m 1 (r + 1)) /\
    (RangeMax m 1 (r + 1) = MaxBitNeg \/
     exists q, 1 <= q <= r /\ RangeMax m 1 (r + 1) = Znth q m 0).
Proof.
  intros m r. split.
  - intros q Hq. apply rangemax_ub__dp_body_branches_k1. lia.
  - destruct (rangemax_attain__dp_body_branches_k1 m 1 (r + 1)) as [He | [q [Hq He]]].
    + left; auto.
    + right. exists q. split; [lia | auto].
Qed.
Lemma monoinc_ge__dp_body_branches_k1 :
  forall (s : list Z), mono_inc s ->
    forall p, 0 <= p < Zlength s -> Znth 0 s 0 + p <= Znth p s 0.
Proof.
  intros s Hs.
  assert (Haux : forall n : nat, forall p, p = Z.of_nat n -> 0 <= p < Zlength s ->
                 Znth 0 s 0 + p <= Znth p s 0).
  { induction n; intros p Hp Hb.
    - subst p. simpl. lia.
    - assert (Hn : 0 <= Z.of_nat n < Zlength s) by lia.
      specialize (IHn (Z.of_nat n) eq_refl Hn).
      assert (Znth (Z.of_nat n) s 0 < Znth p s 0) by (apply Hs; lia).
      lia. }
  intros p Hb. apply (Haux (Z.to_nat p)); lia.
Qed.
Lemma seq_len_bound__dp_body_branches_k1 :
  forall (s : list Z) (i : Z),
    mono_inc s -> 0 < Zlength s ->
    0 <= Znth 0 s 0 ->
    Znth (Zlength s - 1) s 0 = i ->
    Zlength s <= i + 1.
Proof.
  intros s i Hm Hlen Hnn Hlast.
  pose proof (monoinc_ge__dp_body_branches_k1 s Hm (Zlength s - 1) ltac:(lia)).
  lia.
Qed.
Lemma app_one_facts__dp_body_branches_k1 :
  forall (s : list Z) (v : Z),
    Zlength (s ++ [v]) = Zlength s + 1 /\
    (forall p, 0 <= p < Zlength s -> Znth p (s ++ [v]) 0 = Znth p s 0) /\
    Znth (Zlength s) (s ++ [v]) 0 = v.
Proof.
  intros s v. split; [| split].
  - rewrite Zlength_app. rewrite Zlength_cons, Zlength_nil. lia.
  - intros p Hp. apply app_Znth1. auto.
  - rewrite app_Znth2 by lia.
    replace (Zlength s - Zlength s) with 0 by lia.
    reflexivity.
Qed.
Lemma monoinc_le_last__dp_body_branches_k1 :
  forall (s : list Z) (p : Z),
    mono_inc s -> 0 <= p < Zlength s ->
    Znth p s 0 <= Znth (Zlength s - 1) s 0.
Proof.
  intros s p Hm Hp.
  destruct (Z.eq_dec p (Zlength s - 1)) as [-> | Hne]; [lia |].
  assert (Znth p s 0 < Znth (Zlength s - 1) s 0) by (apply Hm; lia).
  lia.
Qed.
Lemma sublist_prefix_facts__dp_body_branches_k1 :
  forall (s : list Z) (L : Z),
    0 <= L <= Zlength s ->
    Zlength (sublist 0 L s) = L /\
    (forall p, 0 <= p < L -> Znth p (sublist 0 L s) 0 = Znth p s 0).
Proof.
  intros s L HL. split.
  - apply Zlength_sublist0. lia.
  - intros p Hp. apply Znth_sublist0. lia.
Qed.
Lemma keep0_prefix__dp_body_branches_k1 :
  forall (a s : list Z) (L : Z),
    Keep0List a s -> 0 <= L <= Zlength s ->
    Keep0List a (sublist 0 L s) /\ Zlength (sublist 0 L s) = L.
Proof.
  intros a s L [Hm [Hb Hk]] HL.
  destruct (sublist_prefix_facts__dp_body_branches_k1 s L HL) as [Hlen Hnth].
  split; [| auto].
  split; [| split].
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    rewrite !Hnth by lia. apply Hm; lia.
  - intros p Hp. rewrite Hlen in Hp. rewrite Hnth by lia. apply Hb; lia.
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    rewrite !Hnth by lia. apply Hk; lia.
Qed.
Lemma keep1_prefix__dp_body_branches_k1 :
  forall (a s : list Z) (d L : Z),
    Keep1List a d s -> 0 <= L <= Zlength s ->
    Keep1List a d (sublist 0 L s) /\ Zlength (sublist 0 L s) = L.
Proof.
  intros a s d L [Hd [Hm [Hb Hk]]] HL.
  destruct (sublist_prefix_facts__dp_body_branches_k1 s L HL) as [Hlen Hnth].
  split; [| auto].
  split; [auto | split; [| split]].
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    rewrite !Hnth by lia. apply Hm; lia.
  - intros p Hp. rewrite Hlen in Hp. rewrite Hnth by lia. apply Hb; lia.
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    rewrite !Hnth by lia. apply Hk; lia.
Qed.
Lemma keyshift_lt__dp_body_branches_k1 :
  forall (a : list Z) (d x : Z), x < d -> KeyShift a d x = KeyAt a x.
Proof.
  intros a d x H. unfold KeyShift.
  destruct (Z.ltb_spec d x); [lia | lia].
Qed.
Lemma keyshift_gt__dp_body_branches_k1 :
  forall (a : list Z) (d x : Z), d < x -> KeyShift a d x = KeyAt a x + 1.
Proof.
  intros a d x H. unfold KeyShift.
  destruct (Z.ltb_spec d x); [lia | lia].
Qed.
Lemma keep1_to_keep0__dp_body_branches_k1 :
  forall (a s : list Z) (d : Z),
    Keep1List a d s ->
    (forall p, 0 <= p < Zlength s -> Znth p s 0 < d) ->
    Keep0List a s.
Proof.
  intros a s d [Hd [Hm [Hb Hk]]] Hlt.
  split; [auto | split].
  - intros p Hp. apply Hb; auto.
  - intros p q Hp Hpq Hq.
    specialize (Hk p q Hp Hpq Hq).
    rewrite !keyshift_lt__dp_body_branches_k1 in Hk by (apply Hlt; lia).
    auto.
Qed.
Lemma keep0_to_keep1__dp_body_branches_k1 :
  forall (a s : list Z) (d : Z),
    Keep0List a s -> 0 <= d < Zlength a ->
    (forall p, 0 <= p < Zlength s -> Znth p s 0 < d) ->
    Keep1List a d s.
Proof.
  intros a s d [Hm [Hb Hk]] Hd Hlt.
  split; [auto | split; [auto | split]].
  - intros p Hp. split; [apply Hb; auto |].
    pose proof (Hlt p Hp). lia.
  - intros p q Hp Hpq Hq.
    rewrite !keyshift_lt__dp_body_branches_k1 by (apply Hlt; lia).
    apply Hk; auto.
Qed.
Lemma keep0_extend__dp_body_branches_k1 :
  forall (a s0 : list Z) (j i : Z),
    Keep0List a s0 -> 0 < Zlength s0 ->
    Znth (Zlength s0 - 1) s0 0 = j ->
    j < i -> 0 <= i < Zlength a ->
    KeyAt a j <= KeyAt a i ->
    Keep0List a (s0 ++ [i]).
Proof.
  intros a s0 j i HK Hpos Hlast Hji Hi Hkey.
  destruct (app_one_facts__dp_body_branches_k1 s0 i) as [Hlen [Hlt Heq]].
  destruct HK as [Hm [Hb Hk]].
  split; [| split].
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    destruct (Z.eq_dec q (Zlength s0)) as [Hq0 | Hqn].
    + subst q. rewrite Heq. rewrite Hlt by lia.
      pose proof (monoinc_le_last__dp_body_branches_k1 s0 p Hm ltac:(lia)). lia.
    + rewrite !Hlt by lia. apply Hm; lia.
  - intros p Hp. rewrite Hlen in Hp.
    destruct (Z.eq_dec p (Zlength s0)) as [Hp0 | Hpn].
    + subst p. rewrite Heq. lia.
    + rewrite Hlt by lia. apply Hb; lia.
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    destruct (Z.eq_dec q (Zlength s0)) as [Hq0 | Hqn].
    + subst q. rewrite Heq. rewrite Hlt by lia.
      destruct (Z.eq_dec p (Zlength s0 - 1)) as [Hp0 | Hpn].
      * subst p. rewrite Hlast. lia.
      * assert (KeyAt a (Znth p s0 0) <= KeyAt a (Znth (Zlength s0 - 1) s0 0))
          by (apply Hk; lia).
        rewrite Hlast in *. lia.
    + rewrite !Hlt by lia. apply Hk; lia.
Qed.
Lemma keep1_extend__dp_body_branches_k1 :
  forall (a s0 : list Z) (d j i : Z),
    Keep1List a d s0 -> 0 < Zlength s0 ->
    Znth (Zlength s0 - 1) s0 0 = j ->
    d < i -> j < i -> 0 <= i < Zlength a ->
    KeyShift a d j <= KeyAt a i + 1 ->
    Keep1List a d (s0 ++ [i]).
Proof.
  intros a s0 d j i HK Hpos Hlast Hdi Hji Hi Hkey.
  destruct (app_one_facts__dp_body_branches_k1 s0 i) as [Hlen [Hlt Heq]].
  destruct HK as [Hd [Hm [Hb Hk]]].
  split; [auto | split; [| split]].
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    destruct (Z.eq_dec q (Zlength s0)) as [Hq0 | Hqn].
    + subst q. rewrite Heq. rewrite Hlt by lia.
      pose proof (monoinc_le_last__dp_body_branches_k1 s0 p Hm ltac:(lia)). lia.
    + rewrite !Hlt by lia. apply Hm; lia.
  - intros p Hp. rewrite Hlen in Hp.
    destruct (Z.eq_dec p (Zlength s0)) as [Hp0 | Hpn].
    + subst p. rewrite Heq. split; [lia | lia].
    + rewrite Hlt by lia. apply Hb; lia.
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    destruct (Z.eq_dec q (Zlength s0)) as [Hq0 | Hqn].
    + subst q. rewrite Heq. rewrite Hlt by lia.
      rewrite (keyshift_gt__dp_body_branches_k1 a d i) by lia.
      destruct (Z.eq_dec p (Zlength s0 - 1)) as [Hp0 | Hpn].
      * subst p. rewrite Hlast. lia.
      * assert (KeyShift a d (Znth p s0 0) <= KeyShift a d (Znth (Zlength s0 - 1) s0 0))
          by (apply Hk; lia).
        rewrite Hlast in *. lia.
    + rewrite !Hlt by lia. apply Hk; lia.
Qed.
Lemma keep0_singleton__dp_body_branches_k1 :
  forall (a : list Z) (i : Z),
    0 <= i < Zlength a -> Keep0List a [i].
Proof.
  intros a i Hi. split; [| split].
  - intros p q Hp Hpq Hq. rewrite Zlength_cons, Zlength_nil in Hq. lia.
  - intros p Hp. rewrite Zlength_cons, Zlength_nil in Hp.
    assert (p = 0) by lia. subst p. rewrite Znth0_cons. auto.
  - intros p q Hp Hpq Hq. rewrite Zlength_cons, Zlength_nil in Hq. lia.
Qed.
Lemma keep1_singleton__dp_body_branches_k1 :
  forall (a : list Z) (d i : Z),
    0 <= i < Zlength a -> 0 <= d < Zlength a -> d <> i -> Keep1List a d [i].
Proof.
  intros a d i Hi Hd Hne. split; [auto | split; [| split]].
  - intros p q Hp Hpq Hq. rewrite Zlength_cons, Zlength_nil in Hq. lia.
  - intros p Hp. rewrite Zlength_cons, Zlength_nil in Hp.
    assert (p = 0) by lia. subst p. rewrite Znth0_cons. split; [auto | lia].
  - intros p q Hp Hpq Hq. rewrite Zlength_cons, Zlength_nil in Hq. lia.
Qed.
Lemma rank_of_member__dp_body_branches_k1 :
  forall (vals : list Z) (uniq v : Z),
    StrictIncPrefix vals uniq -> MemberPrefix vals uniq v ->
    exists r, RankResult vals uniq v r /\ 1 <= r <= uniq.
Proof.
  intros vals uniq v Hs [k [Hk Hv]].
  exists (k + 1). split; [| lia].
  split; [lia | split].
  - replace (k + 1 - 1) with k by lia. auto.
  - intros q Hq. replace (k + 1 - 1) with k in Hq by lia.
    rewrite <- Hv. apply Hs; lia.
Qed.
Lemma best0_step__dp_body_branches_k1 :
  forall (a vals dp0 m0 : list Z) (i uniq r0 prev0 : Z),
    0 <= i < Zlength a ->
    CompressedKeys a vals uniq ->
    DP0Prefix a dp0 i ->
    Bit0Model a vals dp0 m0 i uniq ->
    RankResult vals uniq (KeyAt a i) r0 ->
    1 <= r0 <= uniq ->
    prev0 = RangeMax m0 1 (r0 + 1) ->
    Best0EndingAt a i (Z.max prev0 0 + 1).
Proof.
  intros a vals dp0 m0 i uniq r0 prev0 Hi HC HDP HB Hr0 Hr0b Hprev.
  destruct HC as [Hsi [Hmem Hrng]].
  destruct HB as [Hm0len HB].
  assert (HUB : forall s : list Z,
            (Keep0List a s /\ 0 < Zlength s /\ Znth (Zlength s - 1) s 0 = i) ->
            Zlength s <= Z.max prev0 0 + 1).
  { intros s [HK [Hpos Hlast]].
    destruct (Z_le_gt_dec (Zlength s) 1) as [Hle1 | Hge2]; [lia |].
    pose proof HK as HK2. destruct HK2 as [Hm [Hb Hk]].
    remember (Znth (Zlength s - 2) s 0) as j eqn:Hjdef.
    assert (Hjb : 0 <= j < Zlength a) by (rewrite Hjdef; apply Hb; lia).
    assert (Hjlt : j < i) by (rewrite Hjdef, <- Hlast; apply Hm; lia).
    assert (Hjkey : KeyAt a j <= KeyAt a i)
      by (rewrite Hjdef, <- Hlast; apply Hk; lia).
    destruct (keep0_prefix__dp_body_branches_k1 a s (Zlength s - 1) HK ltac:(lia))
      as [HKp Hlenp].
    destruct (sublist_prefix_facts__dp_body_branches_k1 s (Zlength s - 1) ltac:(lia))
      as [_ Hnthp].
    assert (Hlastp : Znth (Zlength (sublist 0 (Zlength s - 1) s) - 1)
                          (sublist 0 (Zlength s - 1) s) 0 = j).
    { rewrite Hlenp. rewrite Hnthp by lia.
      rewrite Hjdef. f_equal. lia. }
    pose proof (HDP j ltac:(lia)) as HDPj.
    unfold Best0EndingAt in HDPj.
    assert (Hle : Zlength s - 1 <= Znth j dp0 0).
    { rewrite <- Hlenp.
      apply (mvs_ub__dp_body_branches_k1 _ _ _ (sublist 0 (Zlength s - 1) s) HDPj).
      split; [auto | split; [lia | auto]]. }
    destruct (Hmem j ltac:(lia)) as [Hmem1 _].
    destruct (rank_of_member__dp_body_branches_k1 vals uniq (KeyAt a j) Hsi Hmem1)
      as [rj [Hrj Hrjb]].
    assert (Hrjle : rj <= r0).
    { apply (proj1 (rank_order_iso__dp_body_branches_k1
                      vals uniq (KeyAt a j) rj (KeyAt a i) r0 Hsi Hrj Hr0)). auto. }
    destruct (HB rj Hrjb) as [HB1 _].
    specialize (HB1 j ltac:(lia) Hrj).
    pose proof (rangemax_ub__dp_body_branches_k1 m0 1 (r0 + 1) rj ltac:(lia)).
    lia. }
  unfold Best0EndingAt.
  destruct (Z_le_gt_dec prev0 0) as [Hp0 | Hp0].
  - replace (Z.max prev0 0 + 1) with (Zlength (i :: nil))
      by (rewrite Zlength_cons, Zlength_nil; lia).
    apply (mvs_intro__dp_body_branches_k1
             (fun s : list Z => Keep0List a s /\ 0 < Zlength s /\ Znth (Zlength s - 1) s 0 = i)
             (fun s : list Z => Zlength s) (i :: nil)).
    + split; [apply keep0_singleton__dp_body_branches_k1; auto | split].
      * rewrite Zlength_cons, Zlength_nil; lia.
      * rewrite Zlength_cons, Zlength_nil.
        replace (1 - 1) with 0 by lia. rewrite Znth0_cons. reflexivity.
    + intros b Hb2. apply HUB in Hb2.
      rewrite Zlength_cons, Zlength_nil. lia.
  - destruct (rangemax_prefix_char__dp_body_branches_k1 m0 r0)
      as [_ [Hneg | [q [Hq Hqe]]]].
    + rewrite <- Hprev in Hneg. unfold MaxBitNeg in Hneg. lia.
    + rewrite <- Hprev in Hqe.
      destruct (HB q ltac:(lia)) as [_ HB2].
      destruct HB2 as [Hn | [j [Hjlt [Hjr Hje]]]].
      * unfold MaxBitNeg in Hn. lia.
      * assert (Hkj : KeyAt a j <= KeyAt a i).
        { apply (proj2 (rank_order_iso__dp_body_branches_k1
                          vals uniq (KeyAt a j) q (KeyAt a i) r0 Hsi Hjr Hr0)). lia. }
        pose proof (HDP j ltac:(lia)) as HDPj.
        unfold Best0EndingAt in HDPj.
        destruct HDPj as [s0 [[Hs0X Hs0max] Hs0len]].
        destruct Hs0X as [HK0 [Hpos0 Hlast0]].
        destruct (app_one_facts__dp_body_branches_k1 s0 i) as [HAL [_ HAE]].
        replace (Z.max prev0 0 + 1) with (Zlength (s0 ++ (i :: nil)))
          by (rewrite HAL; lia).
        apply (mvs_intro__dp_body_branches_k1
                 (fun s : list Z => Keep0List a s /\ 0 < Zlength s /\ Znth (Zlength s - 1) s 0 = i)
                 (fun s : list Z => Zlength s) (s0 ++ (i :: nil))).
        -- split; [| split].
           ++ apply (keep0_extend__dp_body_branches_k1 a s0 j i HK0 Hpos0 Hlast0);
              auto; lia.
           ++ rewrite HAL. lia.
           ++ rewrite HAL. replace (Zlength s0 + 1 - 1) with (Zlength s0) by lia.
              exact HAE.
        -- intros b Hb2. apply HUB in Hb2. rewrite HAL. lia.
Qed.
Lemma keep1_len_bound__dp_body_branches_k1 :
  forall (a s : list Z) (j : Z),
    (exists d, Keep1List a d s /\ d < j) -> 0 < Zlength s ->
    Znth (Zlength s - 1) s 0 = j -> Zlength s <= j + 1.
Proof.
  intros a s j [d [[Hd [Hm [Hb Hk]]] Hdj]] Hpos Hlast.
  apply (seq_len_bound__dp_body_branches_k1 s j); auto.
  destruct (Hb 0 ltac:(lia)). lia.
Qed.
Lemma best1_exists__dp_body_branches_k1 :
  forall (a s : list Z) (j : Z),
    ((exists d, Keep1List a d s /\ d < j) /\ 0 < Zlength s /\
     Znth (Zlength s - 1) s 0 = j) ->
    exists w, Best1EndingAt a j w.
Proof.
  intros a s j Hs.
  assert (Hbnd : forall b : list Z,
            ((exists d, Keep1List a d b /\ d < j) /\ 0 < Zlength b /\
             Znth (Zlength b - 1) b 0 = j) -> Zlength b <= j + 1).
  { intros b [Hb1 [Hb2 Hb3]]. apply (keep1_len_bound__dp_body_branches_k1 a b j); auto. }
  unfold Best1EndingAt.
  apply (bounded_max_exists__dp_body_branches_k1
           (fun s0 : list Z =>
              (exists d, Keep1List a d s0 /\ d < j) /\ 0 < Zlength s0 /\
              Znth (Zlength s0 - 1) s0 0 = j)
           (fun s0 : list Z => Zlength s0) (j + 1) Hbnd s Hs).
Qed.
Lemma best1_step__dp_body_branches_k1 :
  forall (a vals dp0 m1 mX : list Z) (i uniq r1 q1 qX : Z),
    1 <= i < Zlength a ->
    CompressedKeys a vals uniq ->
    DP0Prefix a dp0 i ->
    Bit1Model a vals m1 i uniq ->
    Bit0Model a vals dp0 mX (i - 1) uniq ->
    RankResult vals uniq (KeyAt a i + 1) r1 ->
    1 <= r1 <= uniq ->
    q1 = RangeMax m1 1 (r1 + 1) ->
    qX = RangeMax mX 1 (r1 + 1) ->
    Best1EndingAt a i (Z.max (Z.max q1 qX) 0 + 1).
Proof.
  intros a vals dp0 m1 mX i uniq r1 q1 qX Hi HC HDP HBB1 HBBX Hr1 Hr1b Hq1 HqX.
  destruct HC as [Hsi [Hmem Hrng]].
  destruct HBB1 as [Hm1len HB1].
  destruct HBBX as [HmXlen HBX].
  assert (HUB : forall s : list Z,
            ((exists d, Keep1List a d s /\ d < i) /\ 0 < Zlength s /\
             Znth (Zlength s - 1) s 0 = i) ->
            Zlength s <= Z.max (Z.max q1 qX) 0 + 1).
  { intros s [[d [HK Hdi]] [Hpos Hlast]].
    destruct (Z_le_gt_dec (Zlength s) 1) as [Hle1 | Hge2]; [lia |].
    pose proof HK as HK2. destruct HK2 as [Hd [Hm [Hb Hk]]].
    remember (Znth (Zlength s - 2) s 0) as j eqn:Hjdef.
    assert (Hjb : 0 <= j < Zlength a /\ j <> d) by (rewrite Hjdef; apply Hb; lia).
    assert (Hjlt : j < i) by (rewrite Hjdef, <- Hlast; apply Hm; lia).
    assert (Hjkey : KeyShift a d j <= KeyShift a d i)
      by (rewrite Hjdef, <- Hlast; apply Hk; lia).
    rewrite (keyshift_gt__dp_body_branches_k1 a d i) in Hjkey by lia.
    destruct (keep1_prefix__dp_body_branches_k1 a s d (Zlength s - 1) HK ltac:(lia))
      as [HKp Hlenp].
    destruct (sublist_prefix_facts__dp_body_branches_k1 s (Zlength s - 1) ltac:(lia))
      as [_ Hnthp].
    assert (Hlastp : Znth (Zlength (sublist 0 (Zlength s - 1) s) - 1)
                          (sublist 0 (Zlength s - 1) s) 0 = j).
    { rewrite Hlenp. rewrite Hnthp by lia. rewrite Hjdef. f_equal. lia. }
    destruct (Z_lt_ge_dec j d) as [Hjd | Hjd].
    - rewrite (keyshift_lt__dp_body_branches_k1 a d j) in Hjkey by lia.
      assert (Hallt : forall p, 0 <= p < Zlength (sublist 0 (Zlength s - 1) s) ->
                      Znth p (sublist 0 (Zlength s - 1) s) 0 < d).
      { intros p Hp. rewrite Hlenp in Hp. rewrite Hnthp by lia.
        destruct (Z.eq_dec p (Zlength s - 2)) as [Hpe | Hpn].
        - rewrite Hpe. lia.
        - assert (Znth p s 0 < Znth (Zlength s - 2) s 0) by (apply Hm; lia). lia. }
      pose proof (keep1_to_keep0__dp_body_branches_k1
                    a (sublist 0 (Zlength s - 1) s) d HKp Hallt) as HK0p.
      pose proof (HDP j ltac:(lia)) as HDPj. unfold Best0EndingAt in HDPj.
      assert (Hle : Zlength s - 1 <= Znth j dp0 0).
      { rewrite <- Hlenp.
        apply (mvs_ub__dp_body_branches_k1 _ _ _ (sublist 0 (Zlength s - 1) s) HDPj).
        split; [auto | split; [lia | auto]]. }
      destruct (Hmem j ltac:(lia)) as [Hmem1 _].
      destruct (rank_of_member__dp_body_branches_k1 vals uniq (KeyAt a j) Hsi Hmem1)
        as [rj [Hrj Hrjb]].
      assert (Hrjle : rj <= r1).
      { apply (proj1 (rank_order_iso__dp_body_branches_k1
                        vals uniq (KeyAt a j) rj (KeyAt a i + 1) r1 Hsi Hrj Hr1)). lia. }
      destruct (HBX rj Hrjb) as [HBX1 _].
      specialize (HBX1 j ltac:(lia) Hrj).
      pose proof (rangemax_ub__dp_body_branches_k1 mX 1 (r1 + 1) rj ltac:(lia)).
      lia.
    - rewrite (keyshift_gt__dp_body_branches_k1 a d j) in Hjkey by lia.
      assert (Hprefmem :
                (exists d0, Keep1List a d0 (sublist 0 (Zlength s - 1) s) /\ d0 < j) /\
                0 < Zlength (sublist 0 (Zlength s - 1) s) /\
                Znth (Zlength (sublist 0 (Zlength s - 1) s) - 1)
                     (sublist 0 (Zlength s - 1) s) 0 = j).
      { split; [exists d; split; [auto | lia] | split; [lia | auto]]. }
      destruct (best1_exists__dp_body_branches_k1
                  a (sublist 0 (Zlength s - 1) s) j Hprefmem) as [w Hw].
      assert (Hle : Zlength s - 1 <= w).
      { rewrite <- Hlenp. unfold Best1EndingAt in Hw.
        apply (mvs_ub__dp_body_branches_k1 _ _ _ (sublist 0 (Zlength s - 1) s) Hw).
        auto. }
      destruct (Hmem j ltac:(lia)) as [_ Hmem2].
      destruct (rank_of_member__dp_body_branches_k1 vals uniq (KeyAt a j + 1) Hsi Hmem2)
        as [rj [Hrj Hrjb]].
      assert (Hrjle : rj <= r1).
      { apply (proj1 (rank_order_iso__dp_body_branches_k1
                        vals uniq (KeyAt a j + 1) rj (KeyAt a i + 1) r1 Hsi Hrj Hr1)). lia. }
      destruct (HB1 rj Hrjb) as [HB11 _].
      specialize (HB11 j w ltac:(lia) Hw Hrj).
      pose proof (rangemax_ub__dp_body_branches_k1 m1 1 (r1 + 1) rj ltac:(lia)).
      lia. }
  unfold Best1EndingAt.
  destruct (Z_le_gt_dec (Z.max q1 qX) 0) as [Hmx | Hmx].
  - replace (Z.max (Z.max q1 qX) 0 + 1) with (Zlength (i :: nil))
      by (rewrite Zlength_cons, Zlength_nil; lia).
    apply (mvs_intro__dp_body_branches_k1
             (fun s : list Z =>
                (exists d, Keep1List a d s /\ d < i) /\ 0 < Zlength s /\
                Znth (Zlength s - 1) s 0 = i)
             (fun s : list Z => Zlength s) (i :: nil)).
    + split; [| split].
      * exists (i - 1). split; [| lia].
        apply keep1_singleton__dp_body_branches_k1; lia.
      * rewrite Zlength_cons, Zlength_nil; lia.
      * rewrite Zlength_cons, Zlength_nil.
        replace (1 - 1) with 0 by lia. rewrite Znth0_cons. reflexivity.
    + intros b Hb2. apply HUB in Hb2.
      rewrite Zlength_cons, Zlength_nil. lia.
  - destruct (Z_le_gt_dec q1 qX) as [Hcmp | Hcmp].
    + destruct (rangemax_prefix_char__dp_body_branches_k1 mX r1)
        as [_ [Hneg | [q [Hq Hqe]]]].
      * rewrite <- HqX in Hneg. unfold MaxBitNeg in Hneg. lia.
      * rewrite <- HqX in Hqe.
        destruct (HBX q ltac:(lia)) as [_ HBX2].
        destruct HBX2 as [Hn | [j [Hjlt [Hjr Hje]]]].
        -- unfold MaxBitNeg in Hn. lia.
        -- assert (Hkj : KeyAt a j <= KeyAt a i + 1).
           { apply (proj2 (rank_order_iso__dp_body_branches_k1
                             vals uniq (KeyAt a j) q (KeyAt a i + 1) r1 Hsi Hjr Hr1)). lia. }
           pose proof (HDP j ltac:(lia)) as HDPj. unfold Best0EndingAt in HDPj.
           destruct HDPj as [s0 [[Hs0X Hs0max] Hs0len]].
           destruct Hs0X as [HK0 [Hpos0 Hlast0]].
           assert (Hallt : forall p, 0 <= p < Zlength s0 -> Znth p s0 0 < j + 1).
           { intros p Hp. pose proof HK0 as HK0'. destruct HK0' as [Hm0' _].
             pose proof (monoinc_le_last__dp_body_branches_k1 s0 p Hm0' Hp). lia. }
           assert (HK1 : Keep1List a (j + 1) s0).
           { apply (keep0_to_keep1__dp_body_branches_k1 a s0 (j + 1) HK0); auto. lia. }
           destruct (app_one_facts__dp_body_branches_k1 s0 i) as [HAL [_ HAE]].
           replace (Z.max (Z.max q1 qX) 0 + 1) with (Zlength (s0 ++ (i :: nil)))
             by (rewrite HAL; lia).
           apply (mvs_intro__dp_body_branches_k1
                    (fun s : list Z =>
                       (exists d, Keep1List a d s /\ d < i) /\ 0 < Zlength s /\
                       Znth (Zlength s - 1) s 0 = i)
                    (fun s : list Z => Zlength s) (s0 ++ (i :: nil))).
           ++ split; [| split].
              ** exists (j + 1). split; [| lia].
                 apply (keep1_extend__dp_body_branches_k1 a s0 (j + 1) j i HK1 Hpos0 Hlast0);
                   try lia.
                 rewrite (keyshift_lt__dp_body_branches_k1 a (j + 1) j) by lia. lia.
              ** rewrite HAL. lia.
              ** rewrite HAL. replace (Zlength s0 + 1 - 1) with (Zlength s0) by lia.
                 exact HAE.
           ++ intros b Hb2. apply HUB in Hb2. rewrite HAL. lia.
    + destruct (rangemax_prefix_char__dp_body_branches_k1 m1 r1)
        as [_ [Hneg | [q [Hq Hqe]]]].
      * rewrite <- Hq1 in Hneg. unfold MaxBitNeg in Hneg. lia.
      * rewrite <- Hq1 in Hqe.
        destruct (HB1 q ltac:(lia)) as [_ HB12].
        destruct HB12 as [Hn | [j [w [Hjlt [Hbw [Hjr Hje]]]]]].
        -- unfold MaxBitNeg in Hn. lia.
        -- assert (Hkj : KeyAt a j + 1 <= KeyAt a i + 1).
           { apply (proj2 (rank_order_iso__dp_body_branches_k1
                             vals uniq (KeyAt a j + 1) q (KeyAt a i + 1) r1 Hsi Hjr Hr1)). lia. }
           unfold Best1EndingAt in Hbw.
           destruct Hbw as [s0 [[Hs0X Hs0max] Hs0len]].
           destruct Hs0X as [[d [HK1 Hdj]] [Hpos0 Hlast0]].
           destruct (app_one_facts__dp_body_branches_k1 s0 i) as [HAL [_ HAE]].
           replace (Z.max (Z.max q1 qX) 0 + 1) with (Zlength (s0 ++ (i :: nil)))
             by (rewrite HAL; lia).
           apply (mvs_intro__dp_body_branches_k1
                    (fun s : list Z =>
                       (exists d, Keep1List a d s /\ d < i) /\ 0 < Zlength s /\
                       Znth (Zlength s - 1) s 0 = i)
                    (fun s : list Z => Zlength s) (s0 ++ (i :: nil))).
           ++ split; [| split].
              ** exists d. split; [| lia].
                 apply (keep1_extend__dp_body_branches_k1 a s0 d j i HK1 Hpos0 Hlast0);
                   try lia.
                 rewrite (keyshift_gt__dp_body_branches_k1 a d j) by lia. lia.
              ** rewrite HAL. lia.
              ** rewrite HAL. replace (Zlength s0 + 1 - 1) with (Zlength s0) by lia.
                 exact HAE.
           ++ intros b Hb2. apply HUB in Hb2. rewrite HAL. lia.
Qed.
Lemma best0_val_bound__dp_body_branches_k1 :
  forall (a : list Z) (i v : Z), Best0EndingAt a i v -> 0 <= i -> 1 <= v <= i + 1.
Proof.
  intros a i v Hb Hi. unfold Best0EndingAt in Hb.
  destruct Hb as [s [[Hs _] Hlen]].
  destruct Hs as [HK [Hpos Hlast]].
  pose proof HK as HK2. destruct HK2 as [Hm [Hbd Hk]].
  simpl in Hlen.
  split; [lia |].
  rewrite <- Hlen. apply (seq_len_bound__dp_body_branches_k1 s i); auto.
  destruct (Hbd 0 ltac:(lia)). lia.
Qed.
Lemma best1_val_bound__dp_body_branches_k1 :
  forall (a : list Z) (i v : Z), Best1EndingAt a i v -> 0 <= i -> 1 <= v <= i + 1.
Proof.
  intros a i v Hb Hi. unfold Best1EndingAt in Hb.
  destruct Hb as [s [[Hs _] Hlen]].
  destruct Hs as [[d [HK Hdi]] [Hpos Hlast]].
  pose proof HK as HK2. destruct HK2 as [Hd [Hm [Hbd Hk]]].
  simpl in Hlen.
  split; [lia |].
  rewrite <- Hlen. apply (seq_len_bound__dp_body_branches_k1 s i); auto.
  destruct (Hbd 0 ltac:(lia)). lia.
Qed.
Lemma zlength_replace__dp_body_branches_k1 :
  forall (l : list Z) (n v : Z), Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros l n v. unfold replace_Znth.
  set (m := Z.to_nat n). clearbody m. revert m.
  induction l as [| h t IH]; intros m.
  - destruct m; reflexivity.
  - destruct m; simpl.
    + reflexivity.
    + rewrite !Zlength_cons. rewrite IH. reflexivity.
Qed.
Lemma maxbitinsert_len__dp_body_branches_k1 :
  forall (m : list Z) (r v : Z), Zlength (MaxBitInsert m r v) = Zlength m.
Proof.
  intros. unfold MaxBitInsert. apply zlength_replace__dp_body_branches_k1.
Qed.
Lemma maxbitinsert_same__dp_body_branches_k1 :
  forall (m : list Z) (r v : Z), 0 <= r < Zlength m ->
    Znth r (MaxBitInsert m r v) 0 = Z.max (Znth r m 0) v.
Proof.
  intros m r v Hr. unfold MaxBitInsert.
  apply Znth_replace_Znth_Same. auto.
Qed.
Lemma maxbitinsert_diff__dp_body_branches_k1 :
  forall (m : list Z) (r v p : Z), 0 <= r < Zlength m -> 0 <= p < Zlength m -> p <> r ->
    Znth p (MaxBitInsert m r v) 0 = Znth p m 0.
Proof.
  intros m r v p Hr Hp Hne. unfold MaxBitInsert.
  apply Znth_replace_Znth_Diff; auto.
Qed.
Lemma maxbitinsert_ge__dp_body_branches_k1 :
  forall (m : list Z) (r v p : Z), 0 <= r < Zlength m -> 0 <= p < Zlength m ->
    Znth p m 0 <= Znth p (MaxBitInsert m r v) 0.
Proof.
  intros m r v p Hr Hp.
  destruct (Z.eq_dec p r) as [He | Hne].
  - subst p. rewrite maxbitinsert_same__dp_body_branches_k1 by auto. lia.
  - rewrite maxbitinsert_diff__dp_body_branches_k1 by auto. lia.
Qed.
Lemma bit0_model_insert__dp_body_branches_k1 :
  forall (a vals dp0 dp1 m0 : list Z) (k uniq r0 d0 : Z),
    Bit0Model a vals dp0 m0 k uniq ->
    StrictIncPrefix vals uniq ->
    0 <= k ->
    (forall j, 0 <= j < k -> Znth j dp1 0 = Znth j dp0 0) ->
    Znth k dp1 0 = d0 ->
    RankResult vals uniq (KeyAt a k) r0 -> 1 <= r0 <= uniq ->
    d0 > MaxBitNeg ->
    Bit0Model a vals dp1 (MaxBitInsert m0 r0 d0) (k + 1) uniq.
Proof.
  intros a vals dp0 dp1 m0 k uniq r0 d0 [Hlen HB] Hsi Hk Hagree Hdk Hr0 Hr0b Hd0.
  assert (Hr0m : 0 <= r0 < Zlength m0) by lia.
  split; [rewrite maxbitinsert_len__dp_body_branches_k1; auto |].
  intros r Hr.
  assert (Hrm : 0 <= r < Zlength m0) by lia.
  destruct (HB r Hr) as [HB1 HB2].
  split.
  - intros j Hj Hrank.
    destruct (Z.eq_dec j k) as [Hje | Hjn].
    + subst j.
      assert (r = r0) by
        (apply (rank_unique__dp_body_branches_k1 vals uniq (KeyAt a k) r r0); auto).
      subst r. rewrite Hdk.
      rewrite maxbitinsert_same__dp_body_branches_k1 by auto. lia.
    + rewrite Hagree by lia.
      pose proof (HB1 j ltac:(lia) Hrank).
      pose proof (maxbitinsert_ge__dp_body_branches_k1 m0 r0 d0 r Hr0m Hrm). lia.
  - destruct (Z.eq_dec r r0) as [Hre | Hrn].
    + subst r. rewrite maxbitinsert_same__dp_body_branches_k1 by auto.
      right.
      destruct (Z_le_gt_dec (Znth r0 m0 0) d0) as [Hc | Hc].
      * exists k. split; [lia | split; [auto |]].
        rewrite Hdk. lia.
      * destruct HB2 as [Hn | [j [Hj [Hjr Hje]]]].
        -- unfold MaxBitNeg in *. lia.
        -- exists j. split; [lia | split; [auto |]].
           rewrite Hagree by lia. lia.
    + rewrite maxbitinsert_diff__dp_body_branches_k1 by auto.
      destruct HB2 as [Hn | [j [Hj [Hjr Hje]]]].
      * left; auto.
      * right. exists j. split; [lia | split; [auto |]].
        rewrite Hagree by lia. lia.
Qed.
Lemma bit1_model_insert__dp_body_branches_k1 :
  forall (a vals m1 : list Z) (k uniq r1 d1 : Z),
    Bit1Model a vals m1 k uniq ->
    StrictIncPrefix vals uniq ->
    0 <= k ->
    RankResult vals uniq (KeyAt a k + 1) r1 -> 1 <= r1 <= uniq ->
    Best1EndingAt a k d1 ->
    d1 > MaxBitNeg ->
    Bit1Model a vals (MaxBitInsert m1 r1 d1) (k + 1) uniq.
Proof.
  intros a vals m1 k uniq r1 d1 [Hlen HB] Hsi Hk0 Hr1 Hr1b Hbest Hd1.
  assert (Hr1m : 0 <= r1 < Zlength m1) by lia.
  split; [rewrite maxbitinsert_len__dp_body_branches_k1; auto |].
  intros r Hr.
  assert (Hrm : 0 <= r < Zlength m1) by lia.
  destruct (HB r Hr) as [HB1 HB2].
  split.
  - intros j w Hj Hbw Hrank.
    destruct (Z.eq_dec j k) as [Hje | Hjn].
    + subst j.
      assert (r = r1) by
        (apply (rank_unique__dp_body_branches_k1 vals uniq (KeyAt a k + 1) r r1); auto).
      subst r.
      assert (Hwd : w = d1).
      { unfold Best1EndingAt in Hbw, Hbest.
        eapply mvs_unique__dp_body_branches_k1; [exact Hbw | exact Hbest]. }
      subst w. rewrite maxbitinsert_same__dp_body_branches_k1 by auto. lia.
    + pose proof (HB1 j w ltac:(lia) Hbw Hrank).
      pose proof (maxbitinsert_ge__dp_body_branches_k1 m1 r1 d1 r Hr1m Hrm). lia.
  - destruct (Z.eq_dec r r1) as [Hre | Hrn].
    + subst r. rewrite maxbitinsert_same__dp_body_branches_k1 by auto.
      right.
      destruct (Z_le_gt_dec (Znth r1 m1 0) d1) as [Hc | Hc].
      * exists k, d1. split; [lia | split; [auto | split; [auto | lia]]].
      * destruct HB2 as [Hn | [j [w [Hj [Hbw [Hjr Hje]]]]]].
        -- unfold MaxBitNeg in *. lia.
        -- exists j, w. split; [lia | split; [auto | split; [auto | lia]]].
    + rewrite maxbitinsert_diff__dp_body_branches_k1 by auto.
      destruct HB2 as [Hn | [j [w [Hj [Hbw [Hjr Hje]]]]]].
      * left; auto.
      * right. exists j, w. split; [lia | split; [auto | split; [auto | lia]]].
Qed.
Lemma clamped_step_up__dp_body_branches_k1 :
  forall (l l' : list Z) (k v x : Z),
    ClampedPrefixMax l k v -> 0 <= k ->
    (forall j, 0 <= j < k -> Znth j l' 0 = Znth j l 0) ->
    Znth k l' 0 = x -> x > v ->
    ClampedPrefixMax l' (k + 1) x.
Proof.
  intros l l' k v x [Hv [Hub Hw]] Hk Hagree Hxk Hx.
  split; [lia | split].
  - intros j Hj. destruct (Z.eq_dec j k) as [He | Hne].
    + subst j. lia.
    + rewrite Hagree by lia. pose proof (Hub j ltac:(lia)). lia.
  - right. exists k. split; [lia | auto].
Qed.
Lemma clamped_step_keep__dp_body_branches_k1 :
  forall (l l' : list Z) (k v x : Z),
    ClampedPrefixMax l k v -> 0 <= k ->
    (forall j, 0 <= j < k -> Znth j l' 0 = Znth j l 0) ->
    Znth k l' 0 = x -> x <= v ->
    ClampedPrefixMax l' (k + 1) v.
Proof.
  intros l l' k v x [Hv [Hub Hw]] Hk Hagree Hxk Hx.
  split; [lia | split].
  - intros j Hj. destruct (Z.eq_dec j k) as [He | Hne].
    + subst j. lia.
    + rewrite Hagree by lia. apply Hub; lia.
  - destruct Hw as [He | [j [Hj He]]].
    + left; auto.
    + right. exists j. split; [lia |]. rewrite Hagree by lia. auto.
Qed.
Lemma clamped_best1_step__dp_body_branches_k1 :
  forall (a : list Z) (k v x : Z),
    ClampedBest1Upto a k v -> 0 <= k ->
    Best1EndingAt a k x -> x > v ->
    ClampedBest1Upto a (k + 1) x.
Proof.
  intros a k v x [Hv [Hub Hw]] Hk Hbest Hx.
  split; [lia | split].
  - intros j w Hj Hbw. destruct (Z.eq_dec j k) as [He | Hne].
    + subst j. unfold Best1EndingAt in Hbw, Hbest.
      assert (Hwx : w = x) by
        (eapply mvs_unique__dp_body_branches_k1; [exact Hbw | exact Hbest]).
      lia.
    + pose proof (Hub j w ltac:(lia) Hbw). lia.
  - right. exists k, x. split; [lia | split; [auto | reflexivity]].
Qed.
Lemma Zlength_replace_Znth__dp_body_branches_k2 :
  forall {A : Type} (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l. induction l as [| x l IH]; intros n v; simpl; auto.
  unfold replace_Znth in *. destruct (Z.to_nat n) as [| n0].
  - simpl. rewrite !Zlength_cons. lia.
  - simpl. rewrite !Zlength_cons.
    specialize (IH (Z.of_nat n0) v).
    replace (Z.to_nat (Z.of_nat n0)) with n0 in IH by lia.
    lia.
Qed.

(* ---------- generic bounded maximum ---------- *)
Lemma bounded_max_exists_aux__dp_body_branches_k2 :
  forall (n : nat) (P : Z -> Prop) (lo hi : Z),
    hi - lo < Z.of_nat n ->
    (exists x, P x) ->
    (forall x, P x -> lo <= x <= hi) ->
    exists m, P m /\ (forall x, P x -> x <= m).
Proof.
  induction n as [| n IH]; intros P lo hi Hn Hex Hb.
  - destruct Hex as [x Hx]. specialize (Hb x Hx). simpl in Hn. lia.
  - destruct (classic (P hi)) as [Hhi | Hhi].
    + exists hi. split; [exact Hhi |]. intros x Hx. specialize (Hb x Hx). lia.
    + apply (IH P lo (hi - 1)).
      * rewrite Nat2Z.inj_succ in Hn. lia.
      * exact Hex.
      * intros x Hx. specialize (Hb x Hx).
        assert (x <> hi) by (intro Hc; subst x; contradiction). lia.
Qed.
Lemma bounded_max_exists__dp_body_branches_k2 :
  forall (P : Z -> Prop) (lo hi : Z),
    (exists x, P x) ->
    (forall x, P x -> lo <= x <= hi) ->
    exists m, P m /\ (forall x, P x -> x <= m).
Proof.
  intros P lo hi Hex Hb.
  destruct Hex as [x0 Hx0]. pose proof (Hb x0 Hx0) as Hx0b.
  apply (bounded_max_exists_aux__dp_body_branches_k2 (Z.to_nat (hi - lo + 1)) P lo hi).
  - rewrite Z2Nat.id by lia. lia.
  - exists x0; exact Hx0.
  - exact Hb.
Qed.
Lemma set_max_exists__dp_body_branches_k2 :
  forall (X : list Z -> Prop) (hi : Z),
    (exists s, X s) ->
    (forall s, X s -> Zlength s <= hi) ->
    exists v, max_value_of_subset Z.le X (fun s => Zlength s) v.
Proof.
  intros X hi Hex Hb.
  assert (Hmax : exists m, (fun L => exists s, X s /\ Zlength s = L) m /\
                           (forall x, (fun L => exists s, X s /\ Zlength s = L) x -> x <= m)).
  { apply (bounded_max_exists__dp_body_branches_k2 _ 0 hi).
    - destruct Hex as [s Hs]. exists (Zlength s), s. auto.
    - intros x [s [Hs Heq]]. subst x. split; [apply Zlength_nonneg | apply Hb; auto]. }
  destruct Hmax as [m [[s [Hs Hlen]] Hub]].
  exists m. unfold max_value_of_subset, max_object_of_subset.
  exists s. split; [split |]; auto.
  intros b Hb2. simpl. rewrite Hlen. apply Hub. exists b. auto.
Qed.
Lemma max_val_ub__dp_body_branches_k2 :
  forall (X : list Z -> Prop) v t,
    max_value_of_subset Z.le X (fun s => Zlength s) v -> X t -> Zlength t <= v.
Proof.
  intros X v t [s [[H1 H2] H3]] Ht. specialize (H2 t Ht). simpl in *. lia.
Qed.
Lemma max_val_wit__dp_body_branches_k2 :
  forall (X : list Z -> Prop) v,
    max_value_of_subset Z.le X (fun s => Zlength s) v -> exists s, X s /\ Zlength s = v.
Proof.
  intros X v [s [[H1 H2] H3]]. exists s. auto.
Qed.
Lemma max_val_intro__dp_body_branches_k2 :
  forall (X : list Z -> Prop) v s,
    X s -> Zlength s = v -> (forall t, X t -> Zlength t <= v) ->
    max_value_of_subset Z.le X (fun s => Zlength s) v.
Proof.
  intros X v s Hs Hlen Hub.
  unfold max_value_of_subset, max_object_of_subset.
  exists s. split; [split |]; auto.
  intros b Hb. simpl. rewrite Hlen. apply Hub. auto.
Qed.
Lemma max_val_unique__dp_body_branches_k2 :
  forall (X : list Z -> Prop) v w,
    max_value_of_subset Z.le X (fun s => Zlength s) v ->
    max_value_of_subset Z.le X (fun s => Zlength s) w -> v = w.
Proof.
  intros X v w Hv Hw.
  destruct (max_val_wit__dp_body_branches_k2 _ _ Hv) as [s [Hs Hls]].
  destruct (max_val_wit__dp_body_branches_k2 _ _ Hw) as [t [Ht Hlt]].
  pose proof (max_val_ub__dp_body_branches_k2 X v t Hv Ht).
  pose proof (max_val_ub__dp_body_branches_k2 X w s Hw Hs). lia.
Qed.

(* ---------- strictly increasing index lists ---------- *)
Lemma mono_inc_index_lb_aux__dp_body_branches_k2 :
  forall (n : nat) (s : list Z),
    mono_inc s -> forall p, p = Z.of_nat n -> 0 <= p < Zlength s ->
    Znth 0 s 0 + p <= Znth p s 0.
Proof.
  induction n as [| n IH]; intros s Hm p Hp Hr.
  - simpl in Hp. subst p. lia.
  - rewrite Nat2Z.inj_succ in Hp.
    assert (Hp' : 0 <= Z.of_nat n < Zlength s) by lia.
    specialize (IH s Hm (Z.of_nat n) eq_refl Hp').
    assert (Hlt : Znth (Z.of_nat n) s 0 < Znth p s 0)
      by (apply Hm; lia).
    lia.
Qed.
Lemma mono_inc_index_lb__dp_body_branches_k2 :
  forall (s : list Z) p,
    mono_inc s -> 0 <= p < Zlength s -> Znth 0 s 0 + p <= Znth p s 0.
Proof.
  intros s p Hm Hr.
  apply (mono_inc_index_lb_aux__dp_body_branches_k2 (Z.to_nat p) s Hm p).
  - rewrite Z2Nat.id by lia. reflexivity.
  - exact Hr.
Qed.
Lemma mono_inc_card__dp_body_branches_k2 :
  forall (s : list Z) lo hi,
    mono_inc s -> 0 < Zlength s ->
    (forall p, 0 <= p < Zlength s -> lo <= Znth p s 0 <= hi) ->
    Zlength s <= hi - lo + 1.
Proof.
  intros s lo hi Hm Hpos Hb.
  pose proof (mono_inc_index_lb__dp_body_branches_k2 s (Zlength s - 1) Hm ltac:(lia)) as Hlb.
  pose proof (Hb 0 ltac:(lia)) as H0.
  pose proof (Hb (Zlength s - 1) ltac:(lia)) as H1.
  lia.
Qed.

(* ---------- RangeMax ---------- *)
Lemma fold_max_ub__dp_body_branches_k2 :
  forall (l : list Z) x, In x l -> x <= fold_right Z.max MaxBitNeg l.
Proof.
  induction l as [| a l IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + lia.
    + specialize (IH x Hin). lia.
Qed.
Lemma fold_max_wit__dp_body_branches_k2 :
  forall (l : list Z),
    fold_right Z.max MaxBitNeg l = MaxBitNeg \/ In (fold_right Z.max MaxBitNeg l) l.
Proof.
  induction l as [| a l IH]; simpl.
  - left; reflexivity.
  - destruct (Z_le_gt_dec a (fold_right Z.max MaxBitNeg l)) as [Hle | Hgt].
    + rewrite Z.max_r by lia. destruct IH as [IH | IH]; [left; auto | right; right; auto].
    + rewrite Z.max_l by lia. right; left; reflexivity.
Qed.
Lemma rangemax_ub__dp_body_branches_k2 :
  forall (m : list Z) lo hi q,
    lo <= q < hi -> Znth q m 0 <= RangeMax m lo hi.
Proof.
  intros m lo hi q Hq. unfold RangeMax.
  apply fold_max_ub__dp_body_branches_k2.
  apply (in_map (fun r => Znth r m 0)). apply In_Zrange. exact Hq.
Qed.
Lemma rangemax_wit__dp_body_branches_k2 :
  forall (m : list Z) lo hi,
    RangeMax m lo hi = MaxBitNeg \/
    exists q, lo <= q < hi /\ Znth q m 0 = RangeMax m lo hi.
Proof.
  intros m lo hi. unfold RangeMax.
  destruct (fold_max_wit__dp_body_branches_k2 (map (fun r => Znth r m 0) (Zrange lo hi)))
    as [H | H].
  - left; exact H.
  - right. apply in_map_iff in H. destruct H as [q [Heq Hin]].
    exists q. split; [apply In_Zrange; exact Hin | exact Heq].
Qed.

(* ---------- ranks ---------- *)
Lemma rank_of_index__dp_body_branches_k2 :
  forall (l : list Z) len k,
    StrictIncPrefix l len -> 0 <= k < len ->
    RankResult l len (Znth k l 0) (k + 1).
Proof.
  intros l len k Hs Hk. unfold RankResult.
  split; [lia | split].
  - replace (k + 1 - 1) with k by lia. reflexivity.
  - intros k' Hk'. apply Hs; lia.
Qed.
Lemma rank_of_member__dp_body_branches_k2 :
  forall (l : list Z) len v,
    StrictIncPrefix l len -> MemberPrefix l len v ->
    exists r, RankResult l len v r /\ 1 <= r <= len.
Proof.
  intros l len v Hs [k [Hk Heq]].
  exists (k + 1). split; [| lia].
  rewrite <- Heq. apply rank_of_index__dp_body_branches_k2; auto.
Qed.
Lemma rank_order_iso__dp_body_branches_k2 :
  forall (l : list Z) len x rx y ry,
    StrictIncPrefix l len ->
    RankResult l len x rx -> RankResult l len y ry ->
    (x <= y <-> rx <= ry).
Proof.
  intros l len x rx y ry Hs [Hrx [Hx _]] [Hry [Hy _]].
  split; intros H.
  - destruct (Z_le_gt_dec rx ry) as [? | Hgt]; [assumption |].
    assert (Znth (ry - 1) l 0 < Znth (rx - 1) l 0) by (apply Hs; lia).
    lia.
  - destruct (Z.eq_dec rx ry) as [Heq | Hne].
    + subst ry. lia.
    + assert (Znth (rx - 1) l 0 < Znth (ry - 1) l 0) by (apply Hs; lia).
      lia.
Qed.
Lemma rank_unique__dp_body_branches_k2 :
  forall (l : list Z) len v r1 r2,
    StrictIncPrefix l len ->
    RankResult l len v r1 -> RankResult l len v r2 -> r1 = r2.
Proof.
  intros l len v r1 r2 Hs H1 H2.
  pose proof (rank_order_iso__dp_body_branches_k2 l len v r1 v r2 Hs H1 H2) as A.
  pose proof (rank_order_iso__dp_body_branches_k2 l len v r2 v r1 Hs H2 H1) as B.
  assert (r1 <= r2) by (apply A; lia).
  assert (r2 <= r1) by (apply B; lia).
  lia.
Qed.

(* ---------- list surgery ---------- *)
Lemma Zlength_snoc__dp_body_branches_k2 :
  forall (s : list Z) x, Zlength (s ++ [x]) = Zlength s + 1.
Proof. intros. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. Qed.
Lemma Znth_snoc_lt__dp_body_branches_k2 :
  forall (s : list Z) x p, 0 <= p < Zlength s -> Znth p (s ++ [x]) 0 = Znth p s 0.
Proof. intros. apply app_Znth1. lia. Qed.
Lemma Znth_snoc_eq__dp_body_branches_k2 :
  forall (s : list Z) x, Znth (Zlength s) (s ++ [x]) 0 = x.
Proof.
  intros. rewrite app_Znth2 by lia.
  replace (Zlength s - Zlength s) with 0 by lia. reflexivity.
Qed.
Lemma mono_inc_le__dp_body_branches_k2 :
  forall (s : list Z) p q,
    mono_inc s -> 0 <= p -> p <= q -> q < Zlength s -> Znth p s 0 <= Znth q s 0.
Proof.
  intros s p q Hm Hp Hpq Hq.
  destruct (Z.eq_dec p q) as [-> | Hne]; [lia |].
  assert (Znth p s 0 < Znth q s 0) by (apply Hm; lia). lia.
Qed.
Lemma keyshift_lt__dp_body_branches_k2 :
  forall a d x, d < x -> KeyShift a d x = KeyAt a x + 1.
Proof.
  intros. unfold KeyShift. destruct (Z.ltb_spec d x); lia.
Qed.
Lemma keyshift_ge__dp_body_branches_k2 :
  forall a d x, x <= d -> KeyShift a d x = KeyAt a x.
Proof.
  intros. unfold KeyShift. destruct (Z.ltb_spec d x); lia.
Qed.

(* ---------- Keep0List ---------- *)
Lemma keep0_sublist__dp_body_branches_k2 :
  forall a s k, Keep0List a s -> 0 <= k <= Zlength s -> Keep0List a (sublist 0 k s).
Proof.
  intros a s k [Hm [Hb Hk]] Hk0.
  assert (Hlen : Zlength (sublist 0 k s) = k) by (apply Zlength_sublist0; lia).
  assert (Hnth : forall p, 0 <= p < k -> Znth p (sublist 0 k s) 0 = Znth p s 0)
    by (intros; apply Znth_sublist0; lia).
  split; [| split].
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    rewrite !Hnth by lia. apply Hm; lia.
  - intros p Hp. rewrite Hlen in Hp. rewrite Hnth by lia. apply Hb; lia.
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq. rewrite !Hnth by lia. apply Hk; lia.
Qed.
Lemma keep0_last_key__dp_body_branches_k2 :
  forall a s p,
    Keep0List a s -> 0 < Zlength s -> 0 <= p < Zlength s ->
    KeyAt a (Znth p s 0) <= KeyAt a (Znth (Zlength s - 1) s 0).
Proof.
  intros a s p [Hm [Hb Hk]] Hpos Hp.
  destruct (Z.eq_dec p (Zlength s - 1)) as [-> | Hne]; [lia |].
  apply Hk; lia.
Qed.
Lemma keep0_snoc__dp_body_branches_k2 :
  forall a s i,
    Keep0List a s -> 0 <= i < Zlength a ->
    (forall p, 0 <= p < Zlength s -> Znth p s 0 < i /\ KeyAt a (Znth p s 0) <= KeyAt a i) ->
    Keep0List a (s ++ [i]).
Proof.
  intros a s i [Hm [Hb Hk]] Hi Hall.
  assert (Hlen : Zlength (s ++ [i]) = Zlength s + 1)
    by apply Zlength_snoc__dp_body_branches_k2.
  assert (Hlt : forall p, 0 <= p < Zlength s -> Znth p (s ++ [i]) 0 = Znth p s 0)
    by (intros; apply Znth_snoc_lt__dp_body_branches_k2; lia).
  assert (Heq : Znth (Zlength s) (s ++ [i]) 0 = i)
    by apply Znth_snoc_eq__dp_body_branches_k2.
  split; [| split].
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    destruct (Z.eq_dec q (Zlength s)) as [-> | Hne].
    + rewrite Heq, Hlt by lia. apply Hall; lia.
    + rewrite !Hlt by lia. apply Hm; lia.
  - intros p Hp. rewrite Hlen in Hp.
    destruct (Z.eq_dec p (Zlength s)) as [-> | Hne].
    + rewrite Heq. lia.
    + rewrite Hlt by lia. apply Hb; lia.
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    destruct (Z.eq_dec q (Zlength s)) as [-> | Hne].
    + rewrite Heq, Hlt by lia. apply Hall; lia.
    + rewrite !Hlt by lia. apply Hk; lia.
Qed.
Lemma keep0_card__dp_body_branches_k2 :
  forall a s, Keep0List a s -> 0 < Zlength s -> Zlength s <= Zlength a.
Proof.
  intros a s [Hm [Hb _]] Hpos.
  pose proof (mono_inc_card__dp_body_branches_k2 s 0 (Zlength a - 1) Hm Hpos) as H.
  assert (Zlength s <= Zlength a - 1 - 0 + 1) by (apply H; intros p Hp; specialize (Hb p Hp); lia).
  lia.
Qed.

(* ---------- Keep1List ---------- *)
Lemma keep1_sublist__dp_body_branches_k2 :
  forall a d s k, Keep1List a d s -> 0 <= k <= Zlength s -> Keep1List a d (sublist 0 k s).
Proof.
  intros a d s k [Hd [Hm [Hb Hk]]] Hk0.
  assert (Hlen : Zlength (sublist 0 k s) = k) by (apply Zlength_sublist0; lia).
  assert (Hnth : forall p, 0 <= p < k -> Znth p (sublist 0 k s) 0 = Znth p s 0)
    by (intros; apply Znth_sublist0; lia).
  split; [exact Hd | split; [| split]].
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq. rewrite !Hnth by lia. apply Hm; lia.
  - intros p Hp. rewrite Hlen in Hp. rewrite Hnth by lia. apply Hb; lia.
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq. rewrite !Hnth by lia. apply Hk; lia.
Qed.
Lemma keep1_card__dp_body_branches_k2 :
  forall a d s, Keep1List a d s -> 0 < Zlength s -> Zlength s <= Zlength a.
Proof.
  intros a d s [Hd [Hm [Hb _]]] Hpos.
  pose proof (mono_inc_card__dp_body_branches_k2 s 0 (Zlength a - 1) Hm Hpos) as H.
  assert (Zlength s <= Zlength a - 1 - 0 + 1)
    by (apply H; intros p Hp; specialize (Hb p Hp); lia).
  lia.
Qed.
Lemma keep1_snoc__dp_body_branches_k2 :
  forall a d s i,
    Keep1List a d s -> 0 <= i < Zlength a -> i <> d ->
    (forall p, 0 <= p < Zlength s ->
       Znth p s 0 < i /\ KeyShift a d (Znth p s 0) <= KeyShift a d i) ->
    Keep1List a d (s ++ [i]).
Proof.
  intros a d s i [Hd [Hm [Hb Hk]]] Hi Hne0 Hall.
  assert (Hlen : Zlength (s ++ [i]) = Zlength s + 1)
    by apply Zlength_snoc__dp_body_branches_k2.
  assert (Hlt : forall p, 0 <= p < Zlength s -> Znth p (s ++ [i]) 0 = Znth p s 0)
    by (intros; apply Znth_snoc_lt__dp_body_branches_k2; lia).
  assert (Heq : Znth (Zlength s) (s ++ [i]) 0 = i)
    by apply Znth_snoc_eq__dp_body_branches_k2.
  split; [exact Hd | split; [| split]].
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    destruct (Z.eq_dec q (Zlength s)) as [-> | Hne].
    + rewrite Heq, Hlt by lia. apply Hall; lia.
    + rewrite !Hlt by lia. apply Hm; lia.
  - intros p Hp. rewrite Hlen in Hp.
    destruct (Z.eq_dec p (Zlength s)) as [-> | Hne].
    + rewrite Heq. split; [lia | exact Hne0].
    + rewrite Hlt by lia. apply Hb; lia.
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    destruct (Z.eq_dec q (Zlength s)) as [-> | Hne].
    + rewrite Heq, Hlt by lia. apply Hall; lia.
    + rewrite !Hlt by lia. apply Hk; lia.
Qed.
Lemma best1_exists__dp_body_branches_k2 :
  forall a j s,
    ((exists d, Keep1List a d s /\ d < j) /\ 0 < Zlength s /\ Znth (Zlength s - 1) s 0 = j) ->
    exists w, Best1EndingAt a j w.
Proof.
  intros a j s Hs.
  unfold Best1EndingAt.
  apply (set_max_exists__dp_body_branches_k2 _ (Zlength a)).
  - exists s. exact Hs.
  - intros t [[d [Hd _]] [Hpos _]].
    apply (keep1_card__dp_body_branches_k2 a d t Hd Hpos).
Qed.

(* ---------- layer-0 DP step ---------- *)
Lemma best0_step__dp_body_branches_k2 :
  forall (a vals dp m0 : list Z) (i uniq r0 prev0 d0 : Z),
    StrictIncPrefix vals uniq ->
    (forall j, 0 <= j < Zlength a -> MemberPrefix vals uniq (KeyAt a j)) ->
    0 <= i < Zlength a ->
    DP0Prefix a dp i ->
    Bit0Model a vals dp m0 i uniq ->
    RankResult vals uniq (KeyAt a i) r0 -> 1 <= r0 <= uniq ->
    prev0 = RangeMax m0 1 (r0 + 1) ->
    d0 = Z.max prev0 0 + 1 ->
    Best0EndingAt a i d0.
Proof.
  intros a vals dp m0 i uniq r0 prev0 d0 Hsi Hmem Hi Hdp [Hm0len Hm0] Hr0 Hr0b Hprev Hd0.
  (* upper bound *)
  assert (Hub : forall s, (Keep0List a s /\ 0 < Zlength s /\ Znth (Zlength s - 1) s 0 = i) ->
                Zlength s <= d0).
  { intros s [Hkeep [Hpos Hlast]].
    destruct (Z_le_gt_dec (Zlength s) 1) as [Hle | Hgt]; [lia |].
    set (L := Zlength s) in *.
    set (j := Znth (L - 2) s 0).
    destruct Hkeep as [Hmono [Hbnd Hkey]] eqn:Hkeepeq.
    assert (Hkeep' : Keep0List a s) by (split; [| split]; auto).
    assert (Hjlt : j < i).
    { unfold j. rewrite <- Hlast. apply Hmono; lia. }
    assert (Hjb : 0 <= j < Zlength a) by (unfold j; apply Hbnd; lia).
    assert (Hkeyji : KeyAt a j <= KeyAt a i).
    { unfold j. rewrite <- Hlast. apply Hkey; lia. }
    set (s' := sublist 0 (L - 1) s).
    assert (Hs'len : Zlength s' = L - 1) by (unfold s'; apply Zlength_sublist0; lia).
    assert (Hs'nth : forall p, 0 <= p < L - 1 -> Znth p s' 0 = Znth p s 0)
      by (intros; unfold s'; apply Znth_sublist0; lia).
    assert (Hs'keep : Keep0List a s')
      by (unfold s'; apply keep0_sublist__dp_body_branches_k2; auto; lia).
    assert (Hs'last : Znth (Zlength s' - 1) s' 0 = j)
      by (rewrite Hs'len; rewrite Hs'nth by lia; unfold j; f_equal; lia).
    pose proof (Hdp j ltac:(lia)) as Hbj.
    assert (Hle1 : Zlength s' <= Znth j dp 0).
    { apply (max_val_ub__dp_body_branches_k2 _ _ s' Hbj).
      split; [exact Hs'keep | split; [lia | exact Hs'last]]. }
    destruct (rank_of_member__dp_body_branches_k2 vals uniq (KeyAt a j) Hsi (Hmem j Hjb))
      as [rj [Hrj Hrjb]].
    assert (Hrjle : rj <= r0)
      by (apply (rank_order_iso__dp_body_branches_k2 vals uniq (KeyAt a j) rj (KeyAt a i) r0);
          auto).
    destruct (Hm0 rj ltac:(lia)) as [Hdom _].
    specialize (Hdom j ltac:(lia) Hrj).
    pose proof (rangemax_ub__dp_body_branches_k2 m0 1 (r0 + 1) rj ltac:(lia)).
    lia. }
  (* witness *)
  unfold Best0EndingAt.
  destruct (Z_le_gt_dec prev0 0) as [Hle | Hgt].
  - apply (max_val_intro__dp_body_branches_k2 _ _ [i]); [| rewrite Zlength_cons, Zlength_nil; lia | exact Hub].
    split; [| split].
    + split; [apply mono_inc_single | split].
      * intros p Hp. rewrite Zlength_cons, Zlength_nil in Hp.
        assert (p = 0) by lia. subst p. simpl. auto.
      * intros p q Hp Hpq Hq. rewrite Zlength_cons, Zlength_nil in Hq. lia.
    + rewrite Zlength_cons, Zlength_nil. lia.
    + rewrite Zlength_cons, Zlength_nil. simpl. reflexivity.
  - destruct (rangemax_wit__dp_body_branches_k2 m0 1 (r0 + 1)) as [Hneg | [q [Hq Hqeq]]].
    { unfold MaxBitNeg in *. lia. }
    assert (Hqm : Znth q m0 0 = prev0) by (rewrite Hqeq; auto).
    destruct (Hm0 q ltac:(lia)) as [_ Hwit].
    destruct Hwit as [Hneg | [j [Hj [Hrj Hjeq]]]]; [unfold MaxBitNeg in *; lia |].
    assert (Hdpj : Znth j dp 0 = prev0) by lia.
    assert (Hqle : q <= r0) by lia.
    assert (Hkeyji : KeyAt a j <= KeyAt a i)
      by (apply (rank_order_iso__dp_body_branches_k2 vals uniq (KeyAt a j) q (KeyAt a i) r0);
          auto).
    pose proof (Hdp j ltac:(lia)) as Hbj.
    destruct (max_val_wit__dp_body_branches_k2 _ _ Hbj) as [s' [[Hs'keep [Hs'pos Hs'last]] Hs'len]].
    apply (max_val_intro__dp_body_branches_k2 _ _ (s' ++ [i])).
    + split; [| split].
      * apply keep0_snoc__dp_body_branches_k2; [exact Hs'keep | lia |].
        intros p Hp. split.
        { assert (Znth p s' 0 <= Znth (Zlength s' - 1) s' 0)
            by (apply mono_inc_le__dp_body_branches_k2; try lia; apply Hs'keep).
          lia. }
        { pose proof (keep0_last_key__dp_body_branches_k2 a s' p Hs'keep Hs'pos Hp).
          rewrite Hs'last in *. lia. }
      * rewrite Zlength_snoc__dp_body_branches_k2. lia.
      * rewrite Zlength_snoc__dp_body_branches_k2.
        replace (Zlength s' + 1 - 1) with (Zlength s') by lia.
        apply Znth_snoc_eq__dp_body_branches_k2.
    + rewrite Zlength_snoc__dp_body_branches_k2. lia.
    + exact Hub.
Qed.
Lemma Znth0_single__dp_body_branches_k2 : forall (x : Z), Znth 0 [x] 0 = x.
Proof. intros. unfold Znth. simpl. reflexivity. Qed.
Lemma keep1_last_key__dp_body_branches_k2 :
  forall a d s p,
    Keep1List a d s -> 0 < Zlength s -> 0 <= p < Zlength s ->
    KeyShift a d (Znth p s 0) <= KeyShift a d (Znth (Zlength s - 1) s 0).
Proof.
  intros a d s p [Hd [Hm [Hb Hk]]] Hpos Hp.
  destruct (Z.eq_dec p (Zlength s - 1)) as [-> | Hne]; [lia |].
  apply Hk; lia.
Qed.
Lemma keep0_to_keep1__dp_body_branches_k2 :
  forall a s d,
    Keep0List a s -> 0 <= d < Zlength a ->
    (forall p, 0 <= p < Zlength s -> Znth p s 0 < d) ->
    Keep1List a d s.
Proof.
  intros a s d [Hm [Hb Hk]] Hd Hlt.
  split; [exact Hd | split; [exact Hm | split]].
  - intros p Hp. split; [apply Hb; auto |]. specialize (Hlt p Hp). lia.
  - intros p q Hp Hpq Hq.
    rewrite !keyshift_ge__dp_body_branches_k2
      by (match goal with |- _ <= _ => idtac end; try (specialize (Hlt p ltac:(lia)); lia);
          try (specialize (Hlt q ltac:(lia)); lia)).
    apply Hk; lia.
Qed.

(* ---------- layer-1 DP step ---------- *)
Lemma best1_step__dp_body_branches_k2 :
  forall (a vals dp m1 mX : list Z) (i uniq r1 q1 qX d1 : Z),
    StrictIncPrefix vals uniq ->
    (forall j, 0 <= j < Zlength a -> MemberPrefix vals uniq (KeyAt a j)) ->
    (forall j, 0 <= j < Zlength a -> MemberPrefix vals uniq (KeyAt a j + 1)) ->
    1 <= i < Zlength a ->
    DP0Prefix a dp i ->
    Bit1Model a vals m1 i uniq ->
    Bit0Model a vals dp mX (i - 1) uniq ->
    RankResult vals uniq (KeyAt a i + 1) r1 -> 1 <= r1 <= uniq ->
    q1 = RangeMax m1 1 (r1 + 1) ->
    qX = RangeMax mX 1 (r1 + 1) ->
    d1 = Z.max (Z.max q1 qX) 0 + 1 ->
    Best1EndingAt a i d1.
Proof.
  intros a vals dp m1 mX i uniq r1 q1 qX d1
         Hsi Hmem0 Hmem1 Hi Hdp [Hm1len Hm1] [HmXlen HmX] Hr1 Hr1b Hq1 HqX Hd1.
  assert (Hub : forall s, ((exists d, Keep1List a d s /\ d < i) /\ 0 < Zlength s /\
                           Znth (Zlength s - 1) s 0 = i) -> Zlength s <= d1).
  { intros s [[d [Hkeep Hdlt]] [Hpos Hlast]].
    destruct (Z_le_gt_dec (Zlength s) 1) as [Hle | Hgt]; [lia |].
    set (L := Zlength s) in *.
    set (j := Znth (L - 2) s 0).
    assert (Hkeepc : Keep1List a d s) by exact Hkeep.
    destruct Hkeep as [Hdb [Hmono [Hbnd Hkey]]].
    assert (Hjlt : j < i) by (unfold j; rewrite <- Hlast; apply Hmono; lia).
    destruct (Hbnd (L - 2) ltac:(lia)) as [Hjb Hjne].
    fold j in Hjb, Hjne.
    assert (Hkeyji : KeyShift a d j <= KeyShift a d i)
      by (unfold j; rewrite <- Hlast; apply Hkey; lia).
    assert (Hshi : KeyShift a d i = KeyAt a i + 1)
      by (apply keyshift_lt__dp_body_branches_k2; lia).
    set (s' := sublist 0 (L - 1) s).
    assert (Hs'len : Zlength s' = L - 1) by (unfold s'; apply Zlength_sublist0; lia).
    assert (Hs'nth : forall p, 0 <= p < L - 1 -> Znth p s' 0 = Znth p s 0)
      by (intros; unfold s'; apply Znth_sublist0; lia).
    assert (Hs'keep1 : Keep1List a d s')
      by (unfold s'; apply keep1_sublist__dp_body_branches_k2; auto; lia).
    assert (Hs'last : Znth (Zlength s' - 1) s' 0 = j)
      by (rewrite Hs'len; rewrite Hs'nth by lia; unfold j; f_equal; lia).
    assert (Hs'le : forall p, 0 <= p < Zlength s' -> Znth p s' 0 <= j).
    { intros p Hp. rewrite <- Hs'last.
      apply mono_inc_le__dp_body_branches_k2; try lia. apply Hs'keep1. }
    destruct (Z.lt_total d j) as [Hdj | [Hdj | Hdj]]; [| lia |].
    - (* d < j : layer-1 predecessor *)
      assert (Hshj : KeyShift a d j = KeyAt a j + 1)
        by (apply keyshift_lt__dp_body_branches_k2; lia).
      destruct (best1_exists__dp_body_branches_k2 a j s')
        as [w Hw].
      { split; [exists d; split; [exact Hs'keep1 | lia] | split; [lia | exact Hs'last]]. }
      assert (Hlew : Zlength s' <= w).
      { apply (max_val_ub__dp_body_branches_k2 _ _ s' Hw).
        split; [exists d; split; [exact Hs'keep1 | lia] | split; [lia | exact Hs'last]]. }
      destruct (rank_of_member__dp_body_branches_k2 vals uniq (KeyAt a j + 1) Hsi
                  (Hmem1 j Hjb)) as [rj [Hrj Hrjb]].
      assert (Hrjle : rj <= r1)
        by (apply (rank_order_iso__dp_body_branches_k2 vals uniq (KeyAt a j + 1) rj
                     (KeyAt a i + 1) r1); auto; lia).
      destruct (Hm1 rj ltac:(lia)) as [Hdom _].
      specialize (Hdom j w ltac:(lia) Hw Hrj).
      pose proof (rangemax_ub__dp_body_branches_k2 m1 1 (r1 + 1) rj ltac:(lia)).
      lia.
    - (* j < d : layer-0 predecessor, crossing the deletion *)
      assert (Hshj : KeyShift a d j = KeyAt a j)
        by (apply keyshift_ge__dp_body_branches_k2; lia).
      assert (Hs'keep0 : Keep0List a s').
      { split; [apply Hs'keep1 | split].
        - intros p Hp. destruct Hs'keep1 as [_ [_ [Hb' _]]]. apply Hb'; auto.
        - intros p q Hp Hpq Hq.
          destruct Hs'keep1 as [_ [_ [_ Hk']]].
          specialize (Hk' p q Hp Hpq Hq).
          rewrite !keyshift_ge__dp_body_branches_k2 in Hk';
            [exact Hk' | pose proof (Hs'le q ltac:(lia)); lia
                       | pose proof (Hs'le p ltac:(lia)); lia]. }
      pose proof (Hdp j ltac:(lia)) as Hbj.
      assert (Hle0 : Zlength s' <= Znth j dp 0).
      { apply (max_val_ub__dp_body_branches_k2 _ _ s' Hbj).
        split; [exact Hs'keep0 | split; [lia | exact Hs'last]]. }
      destruct (rank_of_member__dp_body_branches_k2 vals uniq (KeyAt a j) Hsi
                  (Hmem0 j Hjb)) as [rj [Hrj Hrjb]].
      assert (Hrjle : rj <= r1)
        by (apply (rank_order_iso__dp_body_branches_k2 vals uniq (KeyAt a j) rj
                     (KeyAt a i + 1) r1); auto; lia).
      destruct (HmX rj ltac:(lia)) as [Hdom _].
      specialize (Hdom j ltac:(lia) Hrj).
      pose proof (rangemax_ub__dp_body_branches_k2 mX 1 (r1 + 1) rj ltac:(lia)).
      lia. }
  unfold Best1EndingAt.
  destruct (Z_le_gt_dec (Z.max q1 qX) 0) as [Hle | Hgt].
  - (* sentinel : the singleton [i] with deletion 0 *)
    apply (max_val_intro__dp_body_branches_k2 _ _ [i]);
      [| rewrite Zlength_cons, Zlength_nil; lia | exact Hub].
    split; [| split].
    + exists 0. split; [| lia].
      split; [lia | split; [apply mono_inc_single | split]].
      * intros p Hp. rewrite Zlength_cons, Zlength_nil in Hp.
        assert (p = 0) by lia. subst p.
        rewrite Znth0_single__dp_body_branches_k2. split; lia.
      * intros p q Hp Hpq Hq. rewrite Zlength_cons, Zlength_nil in Hq. lia.
    + rewrite Zlength_cons, Zlength_nil. lia.
    + rewrite Zlength_cons, Zlength_nil. simpl. reflexivity.
  - destruct (Z_le_gt_dec qX q1) as [HqXle | HqXgt].
    + (* the layer-1 tree wins *)
      assert (Hq1pos : q1 > 0) by lia.
      destruct (rangemax_wit__dp_body_branches_k2 m1 1 (r1 + 1)) as [Hneg | [r [Hr Hreq]]];
        [unfold MaxBitNeg in *; lia |].
      assert (Hrm : Znth r m1 0 = q1) by (rewrite Hreq; auto).
      destruct (Hm1 r ltac:(lia)) as [_ Hwit].
      destruct Hwit as [Hneg | [j [w [Hj [Hw [Hrj Hweq]]]]]];
        [unfold MaxBitNeg in *; lia |].
      assert (Hwq : w = q1) by lia.
      subst w.
      assert (Hrle : r <= r1) by lia.
      assert (Hkeyji : KeyAt a j + 1 <= KeyAt a i + 1)
        by (apply (rank_order_iso__dp_body_branches_k2 vals uniq (KeyAt a j + 1) r
                     (KeyAt a i + 1) r1); auto).
      destruct (max_val_wit__dp_body_branches_k2 _ _ Hw)
        as [s' [[[d [Hs'keep Hdj]] [Hs'pos Hs'last]] Hs'len]].
      assert (Hs'le : forall p, 0 <= p < Zlength s' -> Znth p s' 0 <= j).
      { intros p Hp. rewrite <- Hs'last.
        apply mono_inc_le__dp_body_branches_k2; try lia. apply Hs'keep. }
      assert (Hib : 0 <= i < Zlength a) by lia.
      apply (max_val_intro__dp_body_branches_k2 _ _ (s' ++ [i])).
      * split; [| split].
        { exists d. split; [| lia].
          apply keep1_snoc__dp_body_branches_k2; [exact Hs'keep | lia | lia |].
          intros p Hp. split; [pose proof (Hs'le p Hp); lia |].
          pose proof (keep1_last_key__dp_body_branches_k2 a d s' p Hs'keep Hs'pos Hp) as HK.
          rewrite Hs'last in HK.
          rewrite (keyshift_lt__dp_body_branches_k2 a d j ltac:(lia)) in HK.
          rewrite (keyshift_lt__dp_body_branches_k2 a d i ltac:(lia)).
          lia. }
        { rewrite Zlength_snoc__dp_body_branches_k2. lia. }
        { rewrite Zlength_snoc__dp_body_branches_k2.
          replace (Zlength s' + 1 - 1) with (Zlength s') by lia.
          apply Znth_snoc_eq__dp_body_branches_k2. }
      * rewrite Zlength_snoc__dp_body_branches_k2. lia.
      * exact Hub.
    + (* the lagging layer-0 tree wins : the deletion sits between j and i *)
      assert (HqXpos : qX > 0) by lia.
      destruct (rangemax_wit__dp_body_branches_k2 mX 1 (r1 + 1)) as [Hneg | [r [Hr Hreq]]];
        [unfold MaxBitNeg in *; lia |].
      assert (Hrm : Znth r mX 0 = qX) by (rewrite Hreq; auto).
      destruct (HmX r ltac:(lia)) as [_ Hwit].
      destruct Hwit as [Hneg | [j [Hj [Hrj Hjeq]]]]; [unfold MaxBitNeg in *; lia |].
      assert (Hdpj : Znth j dp 0 = qX) by lia.
      assert (Hrle : r <= r1) by lia.
      assert (Hkeyji : KeyAt a j <= KeyAt a i + 1)
        by (apply (rank_order_iso__dp_body_branches_k2 vals uniq (KeyAt a j) r
                     (KeyAt a i + 1) r1); auto).
      pose proof (Hdp j ltac:(lia)) as Hbj.
      destruct (max_val_wit__dp_body_branches_k2 _ _ Hbj)
        as [s' [[Hs'keep [Hs'pos Hs'last]] Hs'len]].
      assert (Hs'le : forall p, 0 <= p < Zlength s' -> Znth p s' 0 <= j).
      { intros p Hp. rewrite <- Hs'last.
        apply mono_inc_le__dp_body_branches_k2; try lia. apply Hs'keep. }
      assert (Hjb : 0 <= j < Zlength a).
      { destruct Hs'keep as [_ [Hb' _]]. specialize (Hb' (Zlength s' - 1) ltac:(lia)).
        rewrite Hs'last in Hb'. lia. }
      assert (Hs'k1 : Keep1List a (j + 1) s').
      { apply keep0_to_keep1__dp_body_branches_k2; [exact Hs'keep | lia |].
        intros p Hp. pose proof (Hs'le p Hp). lia. }
      apply (max_val_intro__dp_body_branches_k2 _ _ (s' ++ [i])).
      * split; [| split].
        { exists (j + 1). split; [| lia].
          apply keep1_snoc__dp_body_branches_k2; [exact Hs'k1 | lia | lia |].
          intros p Hp. split; [pose proof (Hs'le p Hp); lia |].
          pose proof (keep0_last_key__dp_body_branches_k2 a s' p Hs'keep Hs'pos Hp) as HK.
          rewrite Hs'last in HK.
          rewrite (keyshift_ge__dp_body_branches_k2 a (j + 1) (Znth p s' 0))
            by (pose proof (Hs'le p Hp); lia).
          rewrite (keyshift_lt__dp_body_branches_k2 a (j + 1) i ltac:(lia)).
          lia. }
        { rewrite Zlength_snoc__dp_body_branches_k2. lia. }
        { rewrite Zlength_snoc__dp_body_branches_k2.
          replace (Zlength s' + 1 - 1) with (Zlength s') by lia.
          apply Znth_snoc_eq__dp_body_branches_k2. }
      * rewrite Zlength_snoc__dp_body_branches_k2. lia.
      * exact Hub.
Qed.

(* ---------- MaxBitInsert ---------- *)
Lemma maxbit_insert_len__dp_body_branches_k2 :
  forall m r v, Zlength (MaxBitInsert m r v) = Zlength m.
Proof. intros. unfold MaxBitInsert. apply Zlength_replace_Znth__dp_body_branches_k2. Qed.
Lemma maxbit_insert_same__dp_body_branches_k2 :
  forall m r v, 0 <= r < Zlength m -> Znth r (MaxBitInsert m r v) 0 = Z.max (Znth r m 0) v.
Proof. intros. unfold MaxBitInsert. apply Znth_replace_Znth_Same. lia. Qed.
Lemma maxbit_insert_diff__dp_body_branches_k2 :
  forall m r q v, 0 <= r < Zlength m -> 0 <= q < Zlength m -> q <> r ->
    Znth q (MaxBitInsert m r v) 0 = Znth q m 0.
Proof. intros. unfold MaxBitInsert. apply Znth_replace_Znth_Diff; lia. Qed.
Lemma maxbit_insert_ge__dp_body_branches_k2 :
  forall m r q v, 0 <= r < Zlength m -> 0 <= q < Zlength m ->
    Znth q m 0 <= Znth q (MaxBitInsert m r v) 0.
Proof.
  intros m r q v Hr Hq. destruct (Z.eq_dec q r) as [-> | Hne].
  - rewrite maxbit_insert_same__dp_body_branches_k2 by lia. lia.
  - rewrite maxbit_insert_diff__dp_body_branches_k2 by lia. lia.
Qed.

(* ---------- model congruence and insertion ---------- *)
Lemma bit0_model_dp_cong__dp_body_branches_k2 :
  forall a vals dp dp' m k uniq,
    Bit0Model a vals dp m k uniq ->
    (forall j, 0 <= j < k -> Znth j dp' 0 = Znth j dp 0) ->
    Bit0Model a vals dp' m k uniq.
Proof.
  intros a vals dp dp' m k uniq [Hlen Hm] Hcong.
  split; [exact Hlen |]. intros r Hr. destruct (Hm r Hr) as [Hdom Hwit].
  split.
  - intros j Hj Hrank. rewrite Hcong by lia. apply Hdom; auto.
  - destruct Hwit as [Hneg | [j [Hj [Hrank Heq]]]]; [left; exact Hneg |].
    right. exists j. rewrite Hcong by lia. auto.
Qed.
Lemma bit0_model_insert__dp_body_branches_k2 :
  forall a vals dp m k uniq r v,
    StrictIncPrefix vals uniq ->
    Bit0Model a vals dp m k uniq ->
    RankResult vals uniq (KeyAt a k) r -> 1 <= r <= uniq ->
    0 <= k -> Znth k dp 0 = v -> MaxBitNeg < v ->
    Bit0Model a vals dp (MaxBitInsert m r v) (k + 1) uniq.
Proof.
  intros a vals dp m k uniq r v Hsi [Hlen Hm] Hr Hrb Hk Hdpk Hv.
  assert (Hrm : 0 <= r < Zlength m) by lia.
  split; [rewrite maxbit_insert_len__dp_body_branches_k2; exact Hlen |].
  intros q Hq. assert (Hqm : 0 <= q < Zlength m) by lia.
  destruct (Hm q Hq) as [Hdom Hwit].
  split.
  - intros j Hj Hrank.
    destruct (Z.eq_dec j k) as [-> | Hne].
    + assert (q = r) by (apply (rank_unique__dp_body_branches_k2 vals uniq (KeyAt a k)); auto).
      subst q. rewrite maxbit_insert_same__dp_body_branches_k2 by lia. lia.
    + pose proof (Hdom j ltac:(lia) Hrank).
      pose proof (maxbit_insert_ge__dp_body_branches_k2 m r q v Hrm Hqm). lia.
  - destruct (Z.eq_dec q r) as [-> | Hne].
    + rewrite maxbit_insert_same__dp_body_branches_k2 by lia.
      destruct (Z_le_gt_dec (Znth r m 0) v) as [Hle | Hgt].
      * rewrite Z.max_r by lia. right. exists k. split; [lia | split; [exact Hr | lia]].
      * rewrite Z.max_l by lia.
        destruct Hwit as [Hneg | [j [Hj [Hrank Heq]]]]; [unfold MaxBitNeg in *; lia |].
        right. exists j. split; [lia | split; [exact Hrank | exact Heq]].
    + rewrite maxbit_insert_diff__dp_body_branches_k2 by lia.
      destruct Hwit as [Hneg | [j [Hj [Hrank Heq]]]]; [left; exact Hneg |].
      right. exists j. split; [lia | split; [exact Hrank | exact Heq]].
Qed.
Lemma bit1_model_insert__dp_body_branches_k2 :
  forall a vals m k uniq r v,
    StrictIncPrefix vals uniq ->
    Bit1Model a vals m k uniq ->
    RankResult vals uniq (KeyAt a k + 1) r -> 1 <= r <= uniq ->
    0 <= k -> Best1EndingAt a k v -> MaxBitNeg < v ->
    Bit1Model a vals (MaxBitInsert m r v) (k + 1) uniq.
Proof.
  intros a vals m k uniq r v Hsi [Hlen Hm] Hr Hrb Hk Hbest Hv.
  assert (Hrm : 0 <= r < Zlength m) by lia.
  split; [rewrite maxbit_insert_len__dp_body_branches_k2; exact Hlen |].
  intros q Hq. assert (Hqm : 0 <= q < Zlength m) by lia.
  destruct (Hm q Hq) as [Hdom Hwit].
  split.
  - intros j w Hj Hbj Hrank.
    destruct (Z.eq_dec j k) as [-> | Hne].
    + assert (q = r)
        by (apply (rank_unique__dp_body_branches_k2 vals uniq (KeyAt a k + 1)); auto).
      subst q. rewrite maxbit_insert_same__dp_body_branches_k2 by lia.
      assert (w = v) by (apply (max_val_unique__dp_body_branches_k2 _ _ _ Hbj Hbest)).
      lia.
    + pose proof (Hdom j w ltac:(lia) Hbj Hrank).
      pose proof (maxbit_insert_ge__dp_body_branches_k2 m r q v Hrm Hqm). lia.
  - destruct (Z.eq_dec q r) as [-> | Hne].
    + rewrite maxbit_insert_same__dp_body_branches_k2 by lia.
      destruct (Z_le_gt_dec (Znth r m 0) v) as [Hle | Hgt].
      * rewrite Z.max_r by lia. right. exists k, v.
        split; [lia | split; [exact Hbest | split; [exact Hr | reflexivity]]].
      * rewrite Z.max_l by lia.
        destruct Hwit as [Hneg | [j [w [Hj [Hbj [Hrank Heq]]]]]];
          [unfold MaxBitNeg in *; lia |].
        right. exists j, w. split; [lia | split; [exact Hbj | split; [exact Hrank | exact Heq]]].
    + rewrite maxbit_insert_diff__dp_body_branches_k2 by lia.
      destruct Hwit as [Hneg | [j [w [Hj [Hbj [Hrank Heq]]]]]]; [left; exact Hneg |].
      right. exists j, w. split; [lia | split; [exact Hbj | split; [exact Hrank | exact Heq]]].
Qed.

(* ---------- prefix / clamped steps ---------- *)
Lemma dp0prefix_step__dp_body_branches_k2 :
  forall a dp dp' k,
    DP0Prefix a dp k ->
    (forall j, 0 <= j < k -> Znth j dp' 0 = Znth j dp 0) ->
    Best0EndingAt a k (Znth k dp' 0) ->
    DP0Prefix a dp' (k + 1).
Proof.
  intros a dp dp' k Hdp Hcong Hk j Hj.
  destruct (Z.eq_dec j k) as [-> | Hne]; [exact Hk |].
  rewrite Hcong by lia. apply Hdp; lia.
Qed.
Lemma clamped_prefix_step__dp_body_branches_k2 :
  forall l l' k v x w,
    ClampedPrefixMax l k v ->
    (forall j, 0 <= j < k -> Znth j l' 0 = Znth j l 0) ->
    Znth k l' 0 = x -> 0 <= k -> 0 <= x ->
    ((x <= v /\ w = v) \/ (v < x /\ w = x)) ->
    ClampedPrefixMax l' (k + 1) w.
Proof.
  intros l l' k v x w [Hv [Hub Hwit]] Hcong Hkeq Hk0 Hx Hcase.
  split; [destruct Hcase as [[? ->] | [? ->]]; lia | split].
  - intros j Hj. destruct (Z.eq_dec j k) as [-> | Hne].
    + rewrite Hkeq. destruct Hcase as [[? ->] | [? ->]]; lia.
    + rewrite Hcong by lia. pose proof (Hub j ltac:(lia)).
      destruct Hcase as [[? ->] | [? ->]]; lia.
  - destruct Hcase as [[Hle ->] | [Hlt ->]].
    + destruct Hwit as [-> | [j [Hj Heq]]]; [left; reflexivity |].
      right. exists j. split; [lia | rewrite Hcong by lia; exact Heq].
    + right. exists k. split; [lia | exact Hkeq].
Qed.
Lemma clamped_best1_step__dp_body_branches_k2 :
  forall a k v x w,
    ClampedBest1Upto a k v ->
    Best1EndingAt a k x -> 0 <= k -> 0 <= x ->
    ((x <= v /\ w = v) \/ (v < x /\ w = x)) ->
    ClampedBest1Upto a (k + 1) w.
Proof.
  intros a k v x w [Hv [Hub Hwit]] Hbest Hk Hx Hcase.
  split; [destruct Hcase as [[? ->] | [? ->]]; lia | split].
  - intros j u Hj Hbj. destruct (Z.eq_dec j k) as [-> | Hne].
    + assert (u = x) by (apply (max_val_unique__dp_body_branches_k2 _ _ _ Hbj Hbest)).
      destruct Hcase as [[? ->] | [? ->]]; lia.
    + pose proof (Hub j u ltac:(lia) Hbj). destruct Hcase as [[? ->] | [? ->]]; lia.
  - destruct Hcase as [[Hle ->] | [Hlt ->]].
    + destruct Hwit as [-> | [j [u [Hj [Hbj Heq]]]]]; [left; reflexivity |].
      right. exists j, u. split; [lia | split; [exact Hbj | exact Heq]].
    + right. exists k, x. split; [lia | split; [exact Hbest | reflexivity]].
Qed.

(* ---------- attainability bounds ---------- *)
Lemma best0_bound__dp_body_branches_k2 :
  forall a i v, Best0EndingAt a i v -> 1 <= v <= Zlength a.
Proof.
  intros a i v Hb.
  destruct (max_val_wit__dp_body_branches_k2 _ _ Hb) as [s [[Hkeep [Hpos Hlast]] Hlen]].
  pose proof (keep0_card__dp_body_branches_k2 a s Hkeep Hpos). lia.
Qed.
Lemma best1_bound__dp_body_branches_k2 :
  forall a i v, Best1EndingAt a i v -> 1 <= v <= Zlength a.
Proof.
  intros a i v Hb.
  destruct (max_val_wit__dp_body_branches_k2 _ _ Hb) as [s [[[d [Hkeep Hd]] [Hpos Hlast]] Hlen]].
  pose proof (keep1_card__dp_body_branches_k2 a d s Hkeep Hpos). lia.
Qed.
Lemma maxbit_insert_bound__dp_body_branches_k2 :
  forall m r v lo hi q,
    0 <= r < Zlength m -> 0 <= q < Zlength m ->
    (forall t, 0 <= t < Zlength m -> lo <= Znth t m 0 <= hi) ->
    lo <= v <= hi ->
    lo <= Znth q (MaxBitInsert m r v) 0 <= hi.
Proof.
  intros m r v lo hi q Hr Hq Hall Hv.
  destruct (Z.eq_dec q r) as [-> | Hne].
  - rewrite maxbit_insert_same__dp_body_branches_k2 by lia.
    pose proof (Hall r Hr). lia.
  - rewrite maxbit_insert_diff__dp_body_branches_k2 by lia. apply Hall; lia.
Qed.

(* ---------- the loop-body master step ---------- *)
Lemma dp_body_master__dp_body_branches_k2 :
  forall (a vals c dp dp' m0 m1 mX : list Z)
         (i n uniq r0 r1 rp prev0 q1 qX d0 d1 best0 best1 bp0 b0' b1' : Z),
    2 <= n ->
    n = Zlength a ->
    1 <= uniq ->
    KeyPrefix a c n ->
    Zlength c = n ->
    Zlength dp = n ->
    CompressedKeys a vals uniq ->
    RankResult vals uniq (Znth i c 0) r0 -> 1 <= r0 <= uniq ->
    RankResult vals uniq (Znth i c 0 + 1) r1 -> 1 <= r1 <= uniq ->
    RankResult vals uniq (Znth (i - 1) c 0) rp -> 1 <= rp <= uniq ->
    prev0 = RangeMax m0 1 (r0 + 1) ->
    q1 = RangeMax m1 1 (r1 + 1) ->
    qX = RangeMax mX 1 (r1 + 1) ->
    1 <= i < n ->
    DP0Prefix a dp i ->
    (forall k, 0 <= k < i -> 1 <= Znth k dp 0 <= n) ->
    Bit0Model a vals dp m0 i uniq ->
    Bit1Model a vals m1 i uniq ->
    Bit0Model a vals dp mX (i - 1) uniq ->
    ClampedPrefixMax dp i best0 ->
    ClampedBest1Upto a i best1 ->
    ClampedPrefixMax dp (i - 1) bp0 ->
    (forall r, 0 <= r <= uniq ->
       -1000000000 <= Znth r m0 0 <= n /\ -1000000000 <= Znth r m1 0 <= n /\
       -1000000000 <= Znth r mX 0 <= n) ->
    0 <= best0 <= n ->
    0 <= best1 <= n ->
    d0 = Z.max prev0 0 + 1 ->
    d1 = Z.max (Z.max q1 qX) 0 + 1 ->
    dp' = replace_Znth i d0 dp ->
    bp0 < Znth (i - 1) dp' 0 ->
    ((d0 <= best0 /\ b0' = best0) \/ (best0 < d0 /\ b0' = d0)) ->
    ((d1 <= best1 /\ b1' = best1) \/ (best1 < d1 /\ b1' = d1)) ->
    Zlength dp' = n /\
    (forall r, 0 <= r <= uniq ->
       (((-1000000000 <= Znth r (MaxBitInsert m0 r0 d0) 0 <= n /\
          -1000000000 <= Znth r (MaxBitInsert m1 r1 d1) 0) /\
         Znth r (MaxBitInsert m1 r1 d1) 0 <= n) /\
        -1000000000 <= Znth r (MaxBitInsert mX rp (Znth (i - 1) dp' 0)) 0) /\
       Znth r (MaxBitInsert mX rp (Znth (i - 1) dp' 0)) 0 <= n) /\
    DP0Prefix a dp' (i + 1) /\
    (forall k, 0 <= k < i + 1 -> 1 <= Znth k dp' 0 <= n) /\
    Bit0Model a vals dp' (MaxBitInsert m0 r0 d0) (i + 1) uniq /\
    Bit1Model a vals (MaxBitInsert m1 r1 d1) (i + 1) uniq /\
    Bit0Model a vals dp' (MaxBitInsert mX rp (Znth (i - 1) dp' 0)) (i + 1 - 1) uniq /\
    ClampedPrefixMax dp' (i + 1) b0' /\
    ClampedBest1Upto a (i + 1) b1' /\
    ClampedPrefixMax dp' (i + 1 - 1) (Znth (i - 1) dp' 0) /\
    0 <= b0' <= n /\ 0 <= b1' <= n /\
    0 <= Znth (i - 1) dp' 0 <= n.
Proof.
  intros a vals c dp dp' m0 m1 mX i n uniq r0 r1 rp prev0 q1 qX d0 d1 best0 best1 bp0 b0' b1'
         Hn2 Hna Hu1 Hkp Hcl Hdpl Hck Hr0 Hr0b Hr1 Hr1b Hrp Hrpb
         Hprev Hq1 HqX Hi Hdp Hdpb HB0 HB1 HBX Hcp0 Hcb1 Hcpp Hmb Hb0r Hb1r
         Hd0 Hd1 Hdp' Hbpgt Hcase0 Hcase1.
  destruct Hck as [Hsi [Hmem Hrange]].
  assert (HkeyI : Znth i c 0 = KeyAt a i) by (apply Hkp; lia).
  assert (HkeyP : Znth (i - 1) c 0 = KeyAt a (i - 1)) by (apply Hkp; lia).
  rewrite HkeyI in Hr0, Hr1. rewrite HkeyP in Hrp.
  assert (Hia : 0 <= i < Zlength a) by lia.
  assert (Hdpi_r : 0 <= i < Zlength dp) by lia.
  assert (Hcong : forall j, 0 <= j < i -> Znth j dp' 0 = Znth j dp 0)
    by (intros j Hj; subst dp'; apply Znth_replace_Znth_Diff; lia).
  assert (Hdpi : Znth i dp' 0 = d0)
    by (subst dp'; apply Znth_replace_Znth_Same; lia).
  assert (Hdpl' : Zlength dp' = n)
    by (subst dp'; rewrite Zlength_replace_Znth__dp_body_branches_k2; lia).
  assert (Hbpeq : Znth (i - 1) dp' 0 = Znth (i - 1) dp 0) by (apply Hcong; lia).
  assert (Hbpb : 1 <= Znth (i - 1) dp 0 <= n) by (apply Hdpb; lia).
  assert (Hmem0 : forall j, 0 <= j < Zlength a -> MemberPrefix vals uniq (KeyAt a j))
    by (intros j Hj; apply (Hmem j Hj)).
  assert (Hmem1 : forall j, 0 <= j < Zlength a -> MemberPrefix vals uniq (KeyAt a j + 1))
    by (intros j Hj; apply (Hmem j Hj)).
  assert (Hbest0 : Best0EndingAt a i d0)
    by (apply (best0_step__dp_body_branches_k2 a vals dp m0 i uniq r0 prev0); auto).
  assert (Hbest1 : Best1EndingAt a i d1)
    by (apply (best1_step__dp_body_branches_k2 a vals dp m1 mX i uniq r1 q1 qX); auto; lia).
  pose proof (best0_bound__dp_body_branches_k2 a i d0 Hbest0) as Hd0b.
  pose proof (best1_bound__dp_body_branches_k2 a i d1 Hbest1) as Hd1b.
  assert (Hm0len : Zlength m0 = uniq + 1) by (apply HB0).
  assert (Hm1len : Zlength m1 = uniq + 1) by (apply HB1).
  assert (HmXlen : Zlength mX = uniq + 1) by (apply HBX).
  assert (HB0c : Bit0Model a vals dp' m0 i uniq)
    by (apply (bit0_model_dp_cong__dp_body_branches_k2 a vals dp dp' m0 i uniq HB0 Hcong)).
  assert (HBXc : Bit0Model a vals dp' mX (i - 1) uniq).
  { apply (bit0_model_dp_cong__dp_body_branches_k2 a vals dp dp' mX (i - 1) uniq HBX).
    intros j Hj. apply Hcong; lia. }
  assert (HB0' : Bit0Model a vals dp' (MaxBitInsert m0 r0 d0) (i + 1) uniq).
  { apply (bit0_model_insert__dp_body_branches_k2 a vals dp' m0 i uniq r0 d0);
      auto; try lia. unfold MaxBitNeg; lia. }
  assert (HB1' : Bit1Model a vals (MaxBitInsert m1 r1 d1) (i + 1) uniq).
  { apply (bit1_model_insert__dp_body_branches_k2 a vals m1 i uniq r1 d1);
      auto; try lia. unfold MaxBitNeg; lia. }
  assert (HBX' : Bit0Model a vals dp' (MaxBitInsert mX rp (Znth (i - 1) dp' 0))
                   (i + 1 - 1) uniq).
  { replace (i + 1 - 1) with ((i - 1) + 1) by lia.
    apply (bit0_model_insert__dp_body_branches_k2 a vals dp' mX (i - 1) uniq rp
             (Znth (i - 1) dp' 0)).
    - exact Hsi.
    - exact HBXc.
    - exact Hrp.
    - lia.
    - lia.
    - reflexivity.
    - unfold MaxBitNeg. lia. }
  assert (HDP : DP0Prefix a dp' (i + 1)).
  { apply (dp0prefix_step__dp_body_branches_k2 a dp dp' i Hdp Hcong).
    rewrite Hdpi. exact Hbest0. }
  assert (HCP0 : ClampedPrefixMax dp' (i + 1) b0').
  { apply (clamped_prefix_step__dp_body_branches_k2 dp dp' i best0 d0 b0'); auto; lia. }
  assert (HCB1 : ClampedBest1Upto a (i + 1) b1').
  { apply (clamped_best1_step__dp_body_branches_k2 a i best1 d1 b1'); auto; lia. }
  assert (HCPP : ClampedPrefixMax dp' (i + 1 - 1) (Znth (i - 1) dp' 0)).
  { replace (i + 1 - 1) with ((i - 1) + 1) by lia.
    apply (clamped_prefix_step__dp_body_branches_k2 dp dp' (i - 1) bp0
             (Znth (i - 1) dp' 0) (Znth (i - 1) dp' 0)); auto; try lia.
    intros j Hj. apply Hcong; lia. }
  split; [exact Hdpl' | split].
  { intros r Hr.
    assert (Hr0m : 0 <= r0 < Zlength m0) by lia.
    assert (Hr1m : 0 <= r1 < Zlength m1) by lia.
    assert (Hrpm : 0 <= rp < Zlength mX) by lia.
    assert (Hrm0 : 0 <= r < Zlength m0) by lia.
    assert (Hrm1 : 0 <= r < Zlength m1) by lia.
    assert (HrmX : 0 <= r < Zlength mX) by lia.
    pose proof (maxbit_insert_bound__dp_body_branches_k2 m0 r0 d0 (-1000000000) n r
                  Hr0m Hrm0 ltac:(intros t Ht; apply (Hmb t ltac:(lia))) ltac:(lia)).
    pose proof (maxbit_insert_bound__dp_body_branches_k2 m1 r1 d1 (-1000000000) n r
                  Hr1m Hrm1 ltac:(intros t Ht; apply (Hmb t ltac:(lia))) ltac:(lia)).
    pose proof (maxbit_insert_bound__dp_body_branches_k2 mX rp (Znth (i - 1) dp' 0)
                  (-1000000000) n r Hrpm HrmX
                  ltac:(intros t Ht; apply (Hmb t ltac:(lia))) ltac:(lia)).
    lia. }
  split; [exact HDP | split].
  { intros k Hk. destruct (Z.eq_dec k i) as [-> | Hne].
    - rewrite Hdpi. lia.
    - rewrite Hcong by lia. apply Hdpb; lia. }
  split; [exact HB0' | split; [exact HB1' | split; [exact HBX' |]]].
  split; [exact HCP0 | split; [exact HCB1 | split; [exact HCPP |]]].
  split; [lia | split; lia].
Qed.
Lemma zlength_replace_Znth__dp_body_branches_k3 :
  forall (l : list Z) (n v : Z), Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros l n v.
  assert (H : forall (l0 : list Z) (k : nat),
            length (replace_nth k l0 v) = length l0).
  { induction l0 as [| x l0 IH]; intros k; destruct k; simpl; auto. }
  unfold replace_Znth. rewrite !Zlength_correct, H. reflexivity.
Qed.

(* ---------- fold_right Z.max helpers ---------- *)
Lemma fold_max_ub__dp_body_branches_k3 :
  forall (l : list Z) (x : Z),
    In x l -> x <= fold_right Z.max MaxBitNeg l.
Proof.
  induction l as [| a l IH]; intros x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + lia.
    + specialize (IH x Hin). lia.
Qed.
Lemma fold_max_attained__dp_body_branches_k3 :
  forall (l : list Z),
    fold_right Z.max MaxBitNeg l = MaxBitNeg \/
    In (fold_right Z.max MaxBitNeg l) l.
Proof.
  induction l as [| a l IH]; simpl.
  - left; reflexivity.
  - destruct IH as [Heq | Hin].
    + rewrite Heq. destruct (Z_le_gt_dec a MaxBitNeg).
      * left. lia.
      * right. left. lia.
    + destruct (Z_le_gt_dec a (fold_right Z.max MaxBitNeg l)).
      * right. right. replace (Z.max a (fold_right Z.max MaxBitNeg l))
          with (fold_right Z.max MaxBitNeg l) by lia. exact Hin.
      * right. left. lia.
Qed.
Lemma rangemax_ub__dp_body_branches_k3 :
  forall (m : list Z) (lo hi q : Z),
    lo <= q < hi -> Znth q m 0 <= RangeMax m lo hi.
Proof.
  intros m lo hi q Hq. unfold RangeMax.
  apply fold_max_ub__dp_body_branches_k3.
  apply in_map_iff. exists q. split; [reflexivity |].
  apply In_Zrange. lia.
Qed.
Lemma rangemax_attained__dp_body_branches_k3 :
  forall (m : list Z) (lo hi : Z),
    RangeMax m lo hi = MaxBitNeg \/
    exists q, lo <= q < hi /\ RangeMax m lo hi = Znth q m 0.
Proof.
  intros m lo hi. unfold RangeMax.
  destruct (fold_max_attained__dp_body_branches_k3
              (map (fun r => Znth r m 0) (Zrange lo hi))) as [Heq | Hin].
  - left. exact Heq.
  - right. apply in_map_iff in Hin. destruct Hin as [q [Hq Hin]].
    exists q. split.
    + apply In_Zrange. exact Hin.
    + symmetry. exact Hq.
Qed.

(* ---------- ranks ---------- *)
Lemma rank_unique__dp_body_branches_k3 :
  forall (l : list Z) (len v r r' : Z),
    RankResult l len v r -> RankResult l len v r' -> r = r'.
Proof.
  intros l len v r r' [Hr1 [Hr2 Hr3]] [Hs1 [Hs2 Hs3]].
  destruct (Z.lt_trichotomy r r') as [H | [H | H]]; [| exact H |].
  - specialize (Hs3 (r - 1) ltac:(lia)). lia.
  - specialize (Hr3 (r' - 1) ltac:(lia)). lia.
Qed.
Lemma rank_order_iso__dp_body_branches_k3 :
  forall (l : list Z) (len x y rx ry : Z),
    StrictIncPrefix l len ->
    RankResult l len x rx ->
    RankResult l len y ry ->
    (x <= y <-> rx <= ry).
Proof.
  intros l len x y rx ry Hinc [Hx1 [Hx2 _]] [Hy1 [Hy2 _]].
  split; intros H.
  - destruct (Z_le_gt_dec rx ry) as [? | Hgt]; [assumption |].
    specialize (Hinc (ry - 1) (rx - 1) ltac:(lia) ltac:(lia) ltac:(lia)). lia.
  - destruct (Z.eq_dec rx ry) as [Heq | Hne].
    + subst ry. lia.
    + specialize (Hinc (rx - 1) (ry - 1) ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.

(* ---------- bounded maximum existence ---------- *)
Lemma bounded_max_exists__dp_body_branches_k3 :
  forall (X : list Z -> Prop) (B : Z),
    0 <= B ->
    (exists s, X s) ->
    (forall s, X s -> Zlength s <= B) ->
    exists v, max_value_of_subset Z.le X (fun s => Zlength s) v.
Proof.
  intros X B HB [s0 Hs0] Hbd.
  destruct (max_n_in_range (fun n => exists s, X s /\ Zlength s = n) B HB)
    as [m [[sm [Hsm Hlen]] [Hmrange Hmax]]].
  - exists (Zlength s0). split.
    + split; [apply Zlength_nonneg | apply Hbd; exact Hs0].
    + exists s0. split; [exact Hs0 | reflexivity].
  - exists (Zlength sm). exists sm. split; [| reflexivity].
    split; [exact Hsm |].
    intros b Hb. simpl.
    assert (Hle : Zlength b <= m).
    { apply Hmax.
      - split; [apply Zlength_nonneg | apply Hbd; exact Hb].
      - exists b. split; [exact Hb | reflexivity]. }
    lia.
Qed.

(* ---------- monotone index lists ---------- *)
Lemma mono_inc_span__dp_body_branches_k3 :
  forall (s : list Z) (p q : Z),
    mono_inc s -> 0 <= p -> p <= q -> q < Zlength s ->
    Znth p s 0 + (q - p) <= Znth q s 0.
Proof.
  intros s p q Hm Hp Hpq Hq.
  remember (Z.to_nat (q - p)) as n eqn:Hn.
  revert p q Hp Hpq Hq Hn.
  induction n as [| n IH]; intros p q Hp Hpq Hq Hn.
  - assert (q = p) by lia. subst q. lia.
  - assert (Hq1 : p <= q - 1) by lia.
    specialize (IH p (q - 1) Hp Hq1 ltac:(lia) ltac:(lia)).
    specialize (Hm (q - 1) q ltac:(lia) ltac:(lia) Hq).
    lia.
Qed.
Lemma keep_len_bound__dp_body_branches_k3 :
  forall (s : list Z) (i : Z),
    mono_inc s ->
    (forall p, 0 <= p < Zlength s -> 0 <= Znth p s 0) ->
    0 < Zlength s ->
    Znth (Zlength s - 1) s 0 = i ->
    Zlength s <= i + 1.
Proof.
  intros s i Hm Hnn Hpos Hlast.
  pose proof (mono_inc_span__dp_body_branches_k3 s 0 (Zlength s - 1) Hm
                ltac:(lia) ltac:(lia) ltac:(lia)) as Hspan.
  specialize (Hnn 0 ltac:(lia)).
  lia.
Qed.
Lemma member_rank__dp_body_branches_k3 :
  forall (l : list Z) (len v : Z),
    StrictIncPrefix l len -> MemberPrefix l len v ->
    exists r, 1 <= r <= len /\ RankResult l len v r.
Proof.
  intros l len v Hinc [k [Hk Hnth]].
  exists (k + 1). split; [lia |].
  unfold RankResult. split; [lia |]. split.
  - replace (k + 1 - 1) with k by lia. exact Hnth.
  - intros k' Hk'. specialize (Hinc k' k ltac:(lia) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma keep0_peel__dp_body_branches_k3 :
  forall (a t : list Z),
    Keep0List a t -> 1 < Zlength t ->
    Keep0List a (sublist 0 (Zlength t - 1) t).
Proof.
  intros a t [Hmono [Hbd Hkey]] Hlen.
  assert (HL : Zlength (sublist 0 (Zlength t - 1) t) = Zlength t - 1)
    by (rewrite Zlength_sublist0 by lia; reflexivity).
  assert (HN : forall p, 0 <= p < Zlength t - 1 ->
                 Znth p (sublist 0 (Zlength t - 1) t) 0 = Znth p t 0)
    by (intros; rewrite Znth_sublist0 by lia; reflexivity).
  split; [| split].
  - intros p q Hp Hpq Hq. rewrite HL in Hq.
    rewrite !HN by lia. apply Hmono; lia.
  - intros p Hp. rewrite HL in Hp. rewrite HN by lia. apply Hbd; lia.
  - intros p q Hp Hpq Hq. rewrite HL in Hq.
    rewrite !HN by lia. apply Hkey; lia.
Qed.
Lemma best0_step__dp_body_branches_k3 :
  forall (a vals dp0 m0 : list Z) (uniq i r0 prev0 : Z),
    0 <= i < Zlength a ->
    StrictIncPrefix vals uniq ->
    (forall j, 0 <= j < Zlength a -> MemberPrefix vals uniq (KeyAt a j)) ->
    RankResult vals uniq (KeyAt a i) r0 ->
    1 <= r0 <= uniq ->
    DP0Prefix a dp0 i ->
    Bit0Model a vals dp0 m0 i uniq ->
    prev0 = RangeMax m0 1 (r0 + 1) ->
    Best0EndingAt a i (Z.max prev0 0 + 1).
Proof.
  intros a vals dp0 m0 uniq i r0 prev0 Hi Hinc Hmem Hr0 Hr0b Hdp Hbit Hprev.
  assert (Hdom : forall t : list Z,
            Keep0List a t /\ 0 < Zlength t /\ Znth (Zlength t - 1) t 0 = i ->
            Zlength t <= Z.max prev0 0 + 1).
  { intros t [Ht [Htpos Htlast]].
    destruct (Z_le_gt_dec (Zlength t) 1) as [Hle | Hgt]; [lia |].
    pose proof (keep0_peel__dp_body_branches_k3 a t Ht ltac:(lia)) as Ht'.
    destruct Ht as [Hmono [Hbd Hkey]].
    assert (HL : Zlength (sublist 0 (Zlength t - 1) t) = Zlength t - 1)
      by (rewrite Zlength_sublist0 by lia; reflexivity).
    assert (HN : forall p, 0 <= p < Zlength t - 1 ->
                   Znth p (sublist 0 (Zlength t - 1) t) 0 = Znth p t 0)
      by (intros; rewrite Znth_sublist0 by lia; reflexivity).
    assert (Hjlt : Znth (Zlength t - 2) t 0 < i)
      by (rewrite <- Htlast; apply Hmono; lia).
    assert (Hjbd : 0 <= Znth (Zlength t - 2) t 0 < Zlength a)
      by (apply Hbd; lia).
    assert (Hjkey : KeyAt a (Znth (Zlength t - 2) t 0) <= KeyAt a i)
      by (rewrite <- Htlast; apply Hkey; lia).
    destruct (Hdp (Znth (Zlength t - 2) t 0) ltac:(lia))
      as [s0 [[Hs0in Hs0max] Hs0eq]].
    assert (Ht'in : Keep0List a (sublist 0 (Zlength t - 1) t) /\
                    0 < Zlength (sublist 0 (Zlength t - 1) t) /\
                    Znth (Zlength (sublist 0 (Zlength t - 1) t) - 1)
                         (sublist 0 (Zlength t - 1) t) 0
                    = Znth (Zlength t - 2) t 0).
    { split; [exact Ht' |]. split; [lia |].
      rewrite HL. rewrite HN by lia. f_equal. lia. }
    specialize (Hs0max _ Ht'in). simpl in Hs0max.
    pose proof (Hmem (Znth (Zlength t - 2) t 0) Hjbd) as Hmemj.
    destruct (member_rank__dp_body_branches_k3 vals uniq
                (KeyAt a (Znth (Zlength t - 2) t 0)) Hinc Hmemj)
      as [rj [Hrjb Hrj]].
    assert (Hrjle : rj <= r0)
      by (apply (proj1 (rank_order_iso__dp_body_branches_k3 vals uniq
                          (KeyAt a (Znth (Zlength t - 2) t 0)) (KeyAt a i)
                          rj r0 Hinc Hrj Hr0)); exact Hjkey).
    destruct Hbit as [Hm0len Hbit].
    destruct (Hbit rj ltac:(lia)) as [Hbitdom _].
    specialize (Hbitdom (Znth (Zlength t - 2) t 0) ltac:(lia) Hrj).
    pose proof (rangemax_ub__dp_body_branches_k3 m0 1 (r0 + 1) rj ltac:(lia)).
    lia. }
  assert (Hsing : Znth 0 (i :: nil) 0 = i) by reflexivity.
  destruct (Z_le_gt_dec prev0 0) as [Hneg | Hpos].
  - exists (i :: nil). split.
    + split.
      * split; [| split].
        -- split; [| split].
           ++ intros p q Hp Hpq Hq.
              rewrite Zlength_cons, Zlength_nil in Hq. lia.
           ++ intros p Hp. rewrite Zlength_cons, Zlength_nil in Hp.
              assert (p = 0) by lia. subst p. rewrite Hsing. exact Hi.
           ++ intros p q Hp Hpq Hq.
              rewrite Zlength_cons, Zlength_nil in Hq. lia.
        -- rewrite Zlength_cons, Zlength_nil. lia.
        -- rewrite Zlength_cons, Zlength_nil.
           replace (0 + 1 - 1) with 0 by lia. exact Hsing.
      * intros b Hb. simpl. specialize (Hdom b Hb).
        rewrite Zlength_cons, Zlength_nil. lia.
    + rewrite Zlength_cons, Zlength_nil. lia.
  - destruct (rangemax_attained__dp_body_branches_k3 m0 1 (r0 + 1))
      as [Hnegm | [q [Hq Hqeq]]]; [unfold MaxBitNeg in *; lia |].
    destruct Hbit as [Hm0len Hbit].
    destruct (Hbit q ltac:(lia)) as [_ Hwit].
    destruct Hwit as [Hwneg | [j [Hjb [Hjrank Hjeq]]]];
      [unfold MaxBitNeg in *; lia |].
    assert (Hqle : q <= r0) by lia.
    assert (Hjkey : KeyAt a j <= KeyAt a i)
      by (apply (proj2 (rank_order_iso__dp_body_branches_k3 vals uniq
                          (KeyAt a j) (KeyAt a i) q r0 Hinc Hjrank Hr0)); lia).
    destruct (Hdp j Hjb) as [t0 [[Ht0in Ht0max] Ht0eq]].
    destruct Ht0in as [Ht0keep [Ht0pos Ht0last]].
    assert (Ht0len : Zlength t0 = prev0) by (simpl in Ht0eq; lia).
    destruct Ht0keep as [Hmono0 [Hbd0 Hkey0]].
    assert (HLa : Zlength (t0 ++ (i :: nil)) = Zlength t0 + 1)
      by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
    assert (HNa : forall p, 0 <= p < Zlength t0 ->
                    Znth p (t0 ++ (i :: nil)) 0 = Znth p t0 0)
      by (intros; rewrite app_Znth1 by lia; reflexivity).
    assert (HNb : Znth (Zlength t0) (t0 ++ (i :: nil)) 0 = i).
    { rewrite app_Znth2 by lia.
      replace (Zlength t0 - Zlength t0) with 0 by lia. exact Hsing. }
    assert (Hprefkey : forall p, 0 <= p < Zlength t0 ->
              KeyAt a (Znth p t0 0) <= KeyAt a i).
    { intros p Hp.
      destruct (Z.eq_dec p (Zlength t0 - 1)) as [Heq | Hne].
      - subst p. rewrite Ht0last. exact Hjkey.
      - assert (Hstep : KeyAt a (Znth p t0 0)
                        <= KeyAt a (Znth (Zlength t0 - 1) t0 0))
          by (apply Hkey0; lia).
        rewrite Ht0last in Hstep. lia. }
    assert (Hpreflt : forall p, 0 <= p < Zlength t0 -> Znth p t0 0 < i).
    { intros p Hp.
      destruct (Z.eq_dec p (Zlength t0 - 1)) as [Heq | Hne].
      - subst p. rewrite Ht0last. lia.
      - assert (Hstep : Znth p t0 0 < Znth (Zlength t0 - 1) t0 0)
          by (apply Hmono0; lia).
        rewrite Ht0last in Hstep. lia. }
    exists (t0 ++ (i :: nil)). split.
    + split.
      * split; [| split].
        -- split; [| split].
           ++ intros p q' Hp Hpq Hq'. rewrite HLa in Hq'.
              destruct (Z.eq_dec q' (Zlength t0)) as [Heq | Hne].
              ** subst q'. rewrite HNb, HNa by lia. apply Hpreflt; lia.
              ** rewrite !HNa by lia. apply Hmono0; lia.
           ++ intros p Hp. rewrite HLa in Hp.
              destruct (Z.eq_dec p (Zlength t0)) as [Heq | Hne].
              ** subst p. rewrite HNb. exact Hi.
              ** rewrite HNa by lia. apply Hbd0; lia.
           ++ intros p q' Hp Hpq Hq'. rewrite HLa in Hq'.
              destruct (Z.eq_dec q' (Zlength t0)) as [Heq | Hne].
              ** subst q'. rewrite HNb, HNa by lia. apply Hprefkey; lia.
              ** rewrite !HNa by lia. apply Hkey0; lia.
        -- rewrite HLa. lia.
        -- rewrite HLa. replace (Zlength t0 + 1 - 1) with (Zlength t0) by lia.
           exact HNb.
      * intros b Hb. simpl. specialize (Hdom b Hb). rewrite HLa. lia.
    + simpl. rewrite HLa. lia.
Qed.
Lemma keyshift_le__dp_body_branches_k3 :
  forall (a : list Z) (d x : Z), x <= d -> KeyShift a d x = KeyAt a x.
Proof.
  intros a d x H. unfold KeyShift.
  destruct (Z.ltb d x) eqn:Hb; [| lia].
  apply Z.ltb_lt in Hb. lia.
Qed.
Lemma keyshift_gt__dp_body_branches_k3 :
  forall (a : list Z) (d x : Z), d < x -> KeyShift a d x = KeyAt a x + 1.
Proof.
  intros a d x H. unfold KeyShift.
  destruct (Z.ltb d x) eqn:Hb; [lia |].
  apply Z.ltb_ge in Hb. lia.
Qed.
Lemma keep1_peel__dp_body_branches_k3 :
  forall (a t : list Z) (d : Z),
    Keep1List a d t -> 1 < Zlength t ->
    Keep1List a d (sublist 0 (Zlength t - 1) t).
Proof.
  intros a t d [Hd [Hmono [Hbd Hkey]]] Hlen.
  assert (HL : Zlength (sublist 0 (Zlength t - 1) t) = Zlength t - 1)
    by (rewrite Zlength_sublist0 by lia; reflexivity).
  assert (HN : forall p, 0 <= p < Zlength t - 1 ->
                 Znth p (sublist 0 (Zlength t - 1) t) 0 = Znth p t 0)
    by (intros; rewrite Znth_sublist0 by lia; reflexivity).
  split; [exact Hd |]. split; [| split].
  - intros p q Hp Hpq Hq. rewrite HL in Hq. rewrite !HN by lia.
    apply Hmono; lia.
  - intros p Hp. rewrite HL in Hp. rewrite HN by lia. apply Hbd; lia.
  - intros p q Hp Hpq Hq. rewrite HL in Hq. rewrite !HN by lia.
    apply Hkey; lia.
Qed.
Lemma keep1_peel_low__dp_body_branches_k3 :
  forall (a t : list Z) (d : Z),
    Keep1List a d t -> 1 < Zlength t ->
    Znth (Zlength t - 2) t 0 < d ->
    Keep0List a (sublist 0 (Zlength t - 1) t).
Proof.
  intros a t d [Hd [Hmono [Hbd Hkey]]] Hlen Hlow.
  assert (HL : Zlength (sublist 0 (Zlength t - 1) t) = Zlength t - 1)
    by (rewrite Zlength_sublist0 by lia; reflexivity).
  assert (HN : forall p, 0 <= p < Zlength t - 1 ->
                 Znth p (sublist 0 (Zlength t - 1) t) 0 = Znth p t 0)
    by (intros; rewrite Znth_sublist0 by lia; reflexivity).
  assert (Hsmall : forall p, 0 <= p < Zlength t - 1 -> Znth p t 0 < d).
  { intros p Hp.
    destruct (Z.eq_dec p (Zlength t - 2)) as [Heq | Hne]; [subst p; lia |].
    assert (Znth p t 0 < Znth (Zlength t - 2) t 0) by (apply Hmono; lia). lia. }
  split; [| split].
  - intros p q Hp Hpq Hq. rewrite HL in Hq. rewrite !HN by lia.
    apply Hmono; lia.
  - intros p Hp. rewrite HL in Hp. rewrite HN by lia.
    destruct (Hbd p ltac:(lia)). lia.
  - intros p q Hp Hpq Hq. rewrite HL in Hq. rewrite !HN by lia.
    specialize (Hkey p q Hp Hpq ltac:(lia)).
    rewrite !keyshift_le__dp_body_branches_k3 in Hkey
      by (apply Z.lt_le_incl, Hsmall; lia).
    exact Hkey.
Qed.
Lemma best1_exists__dp_body_branches_k3 :
  forall (a : list Z) (j : Z),
    0 <= j ->
    (exists s, (exists d, Keep1List a d s /\ d < j) /\
               0 < Zlength s /\ Znth (Zlength s - 1) s 0 = j) ->
    exists w, Best1EndingAt a j w.
Proof.
  intros a j Hj Hex.
  apply (bounded_max_exists__dp_body_branches_k3 _ (j + 1)); [lia | exact Hex |].
  intros s [[d [Hk Hd]] [Hpos Hlast]].
  destruct Hk as [Hd0 [Hmono [Hbd Hkey]]].
  apply (keep_len_bound__dp_body_branches_k3 s j); auto.
  intros p Hp. destruct (Hbd p Hp). lia.
Qed.
Lemma best1_step__dp_body_branches_k3 :
  forall (a vals dp0 m1 mX : list Z) (uniq i r1 bp : Z),
    1 <= i < Zlength a ->
    StrictIncPrefix vals uniq ->
    (forall j, 0 <= j < Zlength a -> MemberPrefix vals uniq (KeyAt a j)) ->
    (forall j, 0 <= j < Zlength a -> MemberPrefix vals uniq (KeyAt a j + 1)) ->
    RankResult vals uniq (KeyAt a i + 1) r1 ->
    1 <= r1 <= uniq ->
    DP0Prefix a dp0 i ->
    Bit1Model a vals m1 i uniq ->
    Bit0Model a vals dp0 mX (i - 1) uniq ->
    bp = Z.max (Z.max (RangeMax m1 1 (r1 + 1)) (RangeMax mX 1 (r1 + 1))) 0 ->
    Best1EndingAt a i (bp + 1).
Proof.
  intros a vals dp0 m1 mX uniq i r1 bp Hi Hinc Hmem Hmem1 Hr1 Hr1b Hdp
         Hb1 HbX Hbp.
  destruct Hb1 as [Hm1len Hb1].
  destruct HbX as [HmXlen HbX].
  assert (Hsing : Znth 0 (i :: nil) 0 = i) by reflexivity.
  assert (Hdom : forall t : list Z,
            ((exists d, Keep1List a d t /\ d < i) /\
             0 < Zlength t /\ Znth (Zlength t - 1) t 0 = i) ->
            Zlength t <= bp + 1).
  { intros t [[d [Hk Hdi]] [Htpos Htlast]].
    destruct (Z_le_gt_dec (Zlength t) 1) as [Hle | Hgt]; [lia |].
    assert (HL : Zlength (sublist 0 (Zlength t - 1) t) = Zlength t - 1)
      by (rewrite Zlength_sublist0 by lia; reflexivity).
    assert (HN : forall p, 0 <= p < Zlength t - 1 ->
                   Znth p (sublist 0 (Zlength t - 1) t) 0 = Znth p t 0)
      by (intros; rewrite Znth_sublist0 by lia; reflexivity).
    pose proof Hk as Hkcopy.
    destruct Hkcopy as [Hd0 [Hmono [Hbd Hkey]]].
    assert (Hjlt : Znth (Zlength t - 2) t 0 < i)
      by (rewrite <- Htlast; apply Hmono; lia).
    assert (Hjbd : 0 <= Znth (Zlength t - 2) t 0 < Zlength a /\
                   Znth (Zlength t - 2) t 0 <> d) by (apply Hbd; lia).
    assert (Hjkey : KeyShift a d (Znth (Zlength t - 2) t 0)
                    <= KeyShift a d i)
      by (rewrite <- Htlast; apply Hkey; lia).
    rewrite (keyshift_gt__dp_body_branches_k3 a d i) in Hjkey by lia.
    assert (Hlast' : Znth (Zlength (sublist 0 (Zlength t - 1) t) - 1)
                          (sublist 0 (Zlength t - 1) t) 0
                     = Znth (Zlength t - 2) t 0).
    { rewrite HL. rewrite HN by lia. f_equal. lia. }
    destruct (Z_lt_le_dec d (Znth (Zlength t - 2) t 0)) as [Hdj | Hjd].
    - (* the deletion point is before the previous kept index: layer-1 step *)
      rewrite (keyshift_gt__dp_body_branches_k3 a d) in Hjkey by lia.
      pose proof (keep1_peel__dp_body_branches_k3 a t d Hk ltac:(lia)) as Ht'.
      assert (Ht'in : (exists d', Keep1List a d' (sublist 0 (Zlength t - 1) t)
                                  /\ d' < Znth (Zlength t - 2) t 0) /\
                      0 < Zlength (sublist 0 (Zlength t - 1) t) /\
                      Znth (Zlength (sublist 0 (Zlength t - 1) t) - 1)
                           (sublist 0 (Zlength t - 1) t) 0
                      = Znth (Zlength t - 2) t 0).
      { split; [exists d; split; [exact Ht' | lia] |].
        split; [lia | exact Hlast']. }
      destruct (best1_exists__dp_body_branches_k3 a (Znth (Zlength t - 2) t 0)
                  ltac:(lia) (ex_intro _ _ Ht'in)) as [w Hw].
      pose proof Hw as Hwcopy.
      destruct Hwcopy as [sw [[Hswin Hswmax] Hsweq]].
      specialize (Hswmax _ Ht'in). simpl in Hswmax.
      destruct (member_rank__dp_body_branches_k3 vals uniq
                  (KeyAt a (Znth (Zlength t - 2) t 0) + 1) Hinc
                  (Hmem1 (Znth (Zlength t - 2) t 0) ltac:(lia)))
        as [rj [Hrjb Hrj]].
      assert (Hrjle : rj <= r1)
        by (apply (proj1 (rank_order_iso__dp_body_branches_k3 vals uniq
                            (KeyAt a (Znth (Zlength t - 2) t 0) + 1)
                            (KeyAt a i + 1) rj r1 Hinc Hrj Hr1)); lia).
      destruct (Hb1 rj ltac:(lia)) as [Hb1dom _].
      specialize (Hb1dom (Znth (Zlength t - 2) t 0) w ltac:(lia) Hw Hrj).
      pose proof (rangemax_ub__dp_body_branches_k3 m1 1 (r1 + 1) rj
                    ltac:(lia)).
      lia.
    - (* the previous kept index is before the deletion point: cross step *)
      assert (Hjdlt : Znth (Zlength t - 2) t 0 < d) by lia.
      rewrite (keyshift_le__dp_body_branches_k3 a d) in Hjkey by lia.
      pose proof (keep1_peel_low__dp_body_branches_k3 a t d Hk ltac:(lia)
                    Hjdlt) as Ht'.
      assert (Ht'in : Keep0List a (sublist 0 (Zlength t - 1) t) /\
                      0 < Zlength (sublist 0 (Zlength t - 1) t) /\
                      Znth (Zlength (sublist 0 (Zlength t - 1) t) - 1)
                           (sublist 0 (Zlength t - 1) t) 0
                      = Znth (Zlength t - 2) t 0).
      { split; [exact Ht' |]. split; [lia | exact Hlast']. }
      destruct (Hdp (Znth (Zlength t - 2) t 0) ltac:(lia))
        as [s0 [[Hs0in Hs0max] Hs0eq]].
      specialize (Hs0max _ Ht'in). simpl in Hs0max.
      destruct (member_rank__dp_body_branches_k3 vals uniq
                  (KeyAt a (Znth (Zlength t - 2) t 0)) Hinc
                  (Hmem (Znth (Zlength t - 2) t 0) ltac:(lia)))
        as [rj [Hrjb Hrj]].
      assert (Hrjle : rj <= r1)
        by (apply (proj1 (rank_order_iso__dp_body_branches_k3 vals uniq
                            (KeyAt a (Znth (Zlength t - 2) t 0))
                            (KeyAt a i + 1) rj r1 Hinc Hrj Hr1)); lia).
      destruct (HbX rj ltac:(lia)) as [HbXdom _].
      specialize (HbXdom (Znth (Zlength t - 2) t 0) ltac:(lia) Hrj).
      pose proof (rangemax_ub__dp_body_branches_k3 mX 1 (r1 + 1) rj
                    ltac:(lia)).
      lia. }
  destruct (Z_le_gt_dec (Z.max (RangeMax m1 1 (r1 + 1))
                               (RangeMax mX 1 (r1 + 1))) 0) as [Hz | Hpos].
  - (* nothing to continue: keep only index i, deleting i - 1 *)
    exists (i :: nil). split.
    + split.
      * split; [| split].
        -- exists (i - 1). split; [| lia]. split; [lia |]. split; [| split].
           ++ intros p q Hp Hpq Hq.
              rewrite Zlength_cons, Zlength_nil in Hq. lia.
           ++ intros p Hp. rewrite Zlength_cons, Zlength_nil in Hp.
              assert (p = 0) by lia. subst p. rewrite Hsing. split; lia.
           ++ intros p q Hp Hpq Hq.
              rewrite Zlength_cons, Zlength_nil in Hq. lia.
        -- rewrite Zlength_cons, Zlength_nil. lia.
        -- rewrite Zlength_cons, Zlength_nil.
           replace (0 + 1 - 1) with 0 by lia. exact Hsing.
      * intros b Hb. simpl. specialize (Hdom b Hb).
        rewrite Zlength_cons, Zlength_nil. lia.
    + rewrite Zlength_cons, Zlength_nil. lia.
  - destruct (Z_le_gt_dec (RangeMax mX 1 (r1 + 1))
                          (RangeMax m1 1 (r1 + 1))) as [Hsame | Hcross].
    + (* viaSame wins: extend a layer-1 set that ends before i *)
      destruct (rangemax_attained__dp_body_branches_k3 m1 1 (r1 + 1))
        as [Hnegm | [q [Hq Hqeq]]]; [unfold MaxBitNeg in *; lia |].
      destruct (Hb1 q ltac:(lia)) as [_ Hwit].
      destruct Hwit as [Hwneg | [j [w [Hjb [Hjbest [Hjrank Hjeq]]]]]];
        [unfold MaxBitNeg in *; lia |].
      assert (Hkeyj : KeyAt a j <= KeyAt a i)
        by (pose proof (proj2 (rank_order_iso__dp_body_branches_k3 vals uniq
                                 (KeyAt a j + 1) (KeyAt a i + 1) q r1 Hinc
                                 Hjrank Hr1) ltac:(lia)); lia).
      destruct Hjbest as [t0 [[Ht0in Ht0max] Ht0eq]].
      destruct Ht0in as [[d [Ht0keep Hdj]] [Ht0pos Ht0last]].
      pose proof Ht0keep as Ht0keep2.
      destruct Ht0keep2 as [Hd0 [Hmono0 [Hbd0 Hkey0]]].
      assert (Ht0len : Zlength t0 = bp) by (simpl in Ht0eq; lia).
      assert (HLa : Zlength (t0 ++ (i :: nil)) = Zlength t0 + 1)
        by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      assert (HNa : forall p, 0 <= p < Zlength t0 ->
                      Znth p (t0 ++ (i :: nil)) 0 = Znth p t0 0)
        by (intros; rewrite app_Znth1 by lia; reflexivity).
      assert (HNb : Znth (Zlength t0) (t0 ++ (i :: nil)) 0 = i).
      { rewrite app_Znth2 by lia.
        replace (Zlength t0 - Zlength t0) with 0 by lia. exact Hsing. }
      assert (Hpreflt : forall p, 0 <= p < Zlength t0 -> Znth p t0 0 <= j).
      { intros p Hp.
        destruct (Z.eq_dec p (Zlength t0 - 1)) as [Heq | Hne]; [subst p; lia |].
        assert (Hstep : Znth p t0 0 < Znth (Zlength t0 - 1) t0 0)
          by (apply Hmono0; lia).
        lia. }
      assert (Hprefkey : forall p, 0 <= p < Zlength t0 ->
                KeyShift a d (Znth p t0 0) <= KeyShift a d j).
      { intros p Hp.
        destruct (Z.eq_dec p (Zlength t0 - 1)) as [Heq | Hne].
        - subst p. rewrite Ht0last. lia.
        - assert (Hstep : KeyShift a d (Znth p t0 0)
                          <= KeyShift a d (Znth (Zlength t0 - 1) t0 0))
            by (apply Hkey0; lia).
          rewrite Ht0last in Hstep. lia. }
      exists (t0 ++ (i :: nil)). split.
      * split.
        -- split; [| split].
           ++ exists d. split; [| lia]. split; [exact Hd0 |]. split; [| split].
              ** intros p q' Hp Hpq Hq'. rewrite HLa in Hq'.
                 destruct (Z.eq_dec q' (Zlength t0)) as [Heq | Hne].
                 --- subst q'. rewrite HNb, HNa by lia.
                     pose proof (Hpreflt p ltac:(lia)). lia.
                 --- rewrite !HNa by lia. apply Hmono0; lia.
              ** intros p Hp. rewrite HLa in Hp.
                 destruct (Z.eq_dec p (Zlength t0)) as [Heq | Hne].
                 --- subst p. rewrite HNb. split; [lia | lia].
                 --- rewrite HNa by lia. apply Hbd0; lia.
              ** intros p q' Hp Hpq Hq'. rewrite HLa in Hq'.
                 destruct (Z.eq_dec q' (Zlength t0)) as [Heq | Hne].
                 --- subst q'. rewrite HNb, HNa by lia.
                     pose proof (Hprefkey p ltac:(lia)) as Hpk.
                     rewrite (keyshift_gt__dp_body_branches_k3 a d j) in Hpk
                       by lia.
                     rewrite (keyshift_gt__dp_body_branches_k3 a d i) by lia.
                     lia.
                 --- rewrite !HNa by lia. apply Hkey0; lia.
           ++ rewrite HLa. lia.
           ++ rewrite HLa. replace (Zlength t0 + 1 - 1) with (Zlength t0) by lia.
              exact HNb.
        -- intros b Hb. simpl. specialize (Hdom b Hb). rewrite HLa. lia.
      * simpl. rewrite HLa. lia.
    + (* viaCross wins: extend a layer-0 set and delete a position after it *)
      destruct (rangemax_attained__dp_body_branches_k3 mX 1 (r1 + 1))
        as [Hnegm | [q [Hq Hqeq]]]; [unfold MaxBitNeg in *; lia |].
      destruct (HbX q ltac:(lia)) as [_ Hwit].
      destruct Hwit as [Hwneg | [j [Hjb [Hjrank Hjeq]]]];
        [unfold MaxBitNeg in *; lia |].
      assert (Hkeyj : KeyAt a j <= KeyAt a i + 1)
        by (apply (proj2 (rank_order_iso__dp_body_branches_k3 vals uniq
                            (KeyAt a j) (KeyAt a i + 1) q r1 Hinc Hjrank Hr1));
            lia).
      destruct (Hdp j ltac:(lia)) as [t0 [[Ht0in Ht0max] Ht0eq]].
      destruct Ht0in as [Ht0keep [Ht0pos Ht0last]].
      pose proof Ht0keep as Ht0keep2.
      destruct Ht0keep2 as [Hmono0 [Hbd0 Hkey0]].
      assert (Ht0len : Zlength t0 = bp) by (simpl in Ht0eq; lia).
      assert (HLa : Zlength (t0 ++ (i :: nil)) = Zlength t0 + 1)
        by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      assert (HNa : forall p, 0 <= p < Zlength t0 ->
                      Znth p (t0 ++ (i :: nil)) 0 = Znth p t0 0)
        by (intros; rewrite app_Znth1 by lia; reflexivity).
      assert (HNb : Znth (Zlength t0) (t0 ++ (i :: nil)) 0 = i).
      { rewrite app_Znth2 by lia.
        replace (Zlength t0 - Zlength t0) with 0 by lia. exact Hsing. }
      assert (Hpreflt : forall p, 0 <= p < Zlength t0 -> Znth p t0 0 <= j).
      { intros p Hp.
        destruct (Z.eq_dec p (Zlength t0 - 1)) as [Heq | Hne]; [subst p; lia |].
        assert (Hstep : Znth p t0 0 < Znth (Zlength t0 - 1) t0 0)
          by (apply Hmono0; lia).
        lia. }
      assert (Hprefkey : forall p, 0 <= p < Zlength t0 ->
                KeyAt a (Znth p t0 0) <= KeyAt a j).
      { intros p Hp.
        destruct (Z.eq_dec p (Zlength t0 - 1)) as [Heq | Hne].
        - subst p. rewrite Ht0last. lia.
        - assert (Hstep : KeyAt a (Znth p t0 0)
                          <= KeyAt a (Znth (Zlength t0 - 1) t0 0))
            by (apply Hkey0; lia).
          rewrite Ht0last in Hstep. lia. }
      exists (t0 ++ (i :: nil)). split.
      * split.
        -- split; [| split].
           ++ exists (j + 1). split; [| lia]. split; [lia |]. split; [| split].
              ** intros p q' Hp Hpq Hq'. rewrite HLa in Hq'.
                 destruct (Z.eq_dec q' (Zlength t0)) as [Heq | Hne].
                 --- subst q'. rewrite HNb, HNa by lia.
                     pose proof (Hpreflt p ltac:(lia)). lia.
                 --- rewrite !HNa by lia. apply Hmono0; lia.
              ** intros p Hp. rewrite HLa in Hp.
                 destruct (Z.eq_dec p (Zlength t0)) as [Heq | Hne].
                 --- subst p. rewrite HNb. split; lia.
                 --- rewrite HNa by lia.
                     pose proof (Hbd0 p ltac:(lia)).
                     pose proof (Hpreflt p ltac:(lia)). split; [lia | lia].
              ** intros p q' Hp Hpq Hq'. rewrite HLa in Hq'.
                 destruct (Z.eq_dec q' (Zlength t0)) as [Heq | Hne].
                 --- subst q'. rewrite HNb, HNa by lia.
                     rewrite (keyshift_le__dp_body_branches_k3 a (j + 1))
                       by (pose proof (Hpreflt p ltac:(lia)); lia).
                     rewrite (keyshift_gt__dp_body_branches_k3 a (j + 1) i)
                       by lia.
                     pose proof (Hprefkey p ltac:(lia)). lia.
                 --- rewrite !HNa by lia.
                     rewrite !(keyshift_le__dp_body_branches_k3 a (j + 1))
                       by (pose proof (Hpreflt p ltac:(lia));
                           pose proof (Hpreflt q' ltac:(lia)); lia).
                     apply Hkey0; lia.
           ++ rewrite HLa. lia.
           ++ rewrite HLa. replace (Zlength t0 + 1 - 1) with (Zlength t0) by lia.
              exact HNb.
        -- intros b Hb. simpl. specialize (Hdom b Hb). rewrite HLa. lia.
      * simpl. rewrite HLa. lia.
Qed.

(* ---------- Fenwick logical table updates ---------- *)
Lemma maxbitinsert_len__dp_body_branches_k3 :
  forall (m : list Z) (r v : Z), Zlength (MaxBitInsert m r v) = Zlength m.
Proof. intros. unfold MaxBitInsert. apply zlength_replace_Znth__dp_body_branches_k3. Qed.
Lemma maxbitinsert_same__dp_body_branches_k3 :
  forall (m : list Z) (r v : Z),
    0 <= r < Zlength m ->
    Znth r (MaxBitInsert m r v) 0 = Z.max (Znth r m 0) v.
Proof.
  intros m r v H. unfold MaxBitInsert.
  apply Znth_replace_Znth_Same. exact H.
Qed.
Lemma maxbitinsert_diff__dp_body_branches_k3 :
  forall (m : list Z) (r v p : Z),
    0 <= r < Zlength m -> 0 <= p < Zlength m -> p <> r ->
    Znth p (MaxBitInsert m r v) 0 = Znth p m 0.
Proof.
  intros m r v p Hr Hp Hne. unfold MaxBitInsert.
  apply Znth_replace_Znth_Diff; auto.
Qed.
Lemma bit0_model_insert__dp_body_branches_k3 :
  forall (a vals dp dp' m : list Z) (k uniq rk v : Z),
    Bit0Model a vals dp m k uniq ->
    0 <= k ->
    (forall j, 0 <= j < k -> Znth j dp' 0 = Znth j dp 0) ->
    Znth k dp' 0 = v ->
    RankResult vals uniq (KeyAt a k) rk ->
    1 <= rk <= uniq ->
    Bit0Model a vals dp' (MaxBitInsert m rk v) (k + 1) uniq.
Proof.
  intros a vals dp dp' m k uniq rk v [Hmlen Hmod] Hk Hsame Hnew Hrk Hrkb.
  split; [rewrite maxbitinsert_len__dp_body_branches_k3; exact Hmlen |].
  intros r Hr.
  assert (Hrkin : 0 <= rk < Zlength m) by lia.
  assert (Hrin : 0 <= r < Zlength m) by lia.
  destruct (Hmod r Hr) as [Hdom Hwit].
  split.
  - intros j Hj Hjrank.
    destruct (Z.eq_dec j k) as [Hjk | Hjk].
    + subst j.
      assert (r = rk)
        by (apply (rank_unique__dp_body_branches_k3 vals uniq (KeyAt a k));
            assumption).
      subst r. rewrite maxbitinsert_same__dp_body_branches_k3 by lia.
      rewrite Hnew. lia.
    + specialize (Hdom j ltac:(lia) Hjrank).
      rewrite (Hsame j ltac:(lia)).
      destruct (Z.eq_dec r rk) as [Hrr | Hrr].
      * subst r. rewrite maxbitinsert_same__dp_body_branches_k3 by lia. lia.
      * rewrite maxbitinsert_diff__dp_body_branches_k3 by lia. lia.
  - destruct (Z.eq_dec r rk) as [Hrr | Hrr].
    + subst r. rewrite maxbitinsert_same__dp_body_branches_k3 by lia.
      destruct (Z_le_gt_dec (Znth rk m 0) v) as [Hle | Hgt].
      * right. exists k. split; [lia |]. split; [exact Hrk |].
        rewrite Hnew. lia.
      * replace (Z.max (Znth rk m 0) v) with (Znth rk m 0) by lia.
        destruct Hwit as [Hneg | [j [Hjb [Hjrank Hjeq]]]]; [left; exact Hneg |].
        right. exists j. split; [lia |]. split; [exact Hjrank |].
        rewrite (Hsame j ltac:(lia)). exact Hjeq.
    + rewrite maxbitinsert_diff__dp_body_branches_k3 by lia.
      destruct Hwit as [Hneg | [j [Hjb [Hjrank Hjeq]]]]; [left; exact Hneg |].
      right. exists j. split; [lia |]. split; [exact Hjrank |].
      rewrite (Hsame j ltac:(lia)). exact Hjeq.
Qed.
Lemma best1_unique__dp_body_branches_k3 :
  forall (a : list Z) (k w v : Z),
    Best1EndingAt a k w -> Best1EndingAt a k v -> w = v.
Proof.
  intros a k w v Hw Hv. unfold Best1EndingAt in Hw, Hv.
  eapply (max_unique Z.le); eauto.
Qed.
Lemma bit1_model_insert__dp_body_branches_k3 :
  forall (a vals m : list Z) (k uniq rk v : Z),
    Bit1Model a vals m k uniq ->
    0 <= k ->
    Best1EndingAt a k v ->
    RankResult vals uniq (KeyAt a k + 1) rk ->
    1 <= rk <= uniq ->
    Bit1Model a vals (MaxBitInsert m rk v) (k + 1) uniq.
Proof.
  intros a vals m k uniq rk v [Hmlen Hmod] Hk Hbest Hrk Hrkb.
  split; [rewrite maxbitinsert_len__dp_body_branches_k3; exact Hmlen |].
  intros r Hr.
  assert (Hrkin : 0 <= rk < Zlength m) by lia.
  assert (Hrin : 0 <= r < Zlength m) by lia.
  destruct (Hmod r Hr) as [Hdom Hwit].
  split.
  - intros j w Hj Hjbest Hjrank.
    destruct (Z.eq_dec j k) as [Hjk | Hjk].
    + subst j.
      assert (Hwv : w = v)
        by (apply (best1_unique__dp_body_branches_k3 a k w v Hjbest Hbest)).
      assert (r = rk)
        by (apply (rank_unique__dp_body_branches_k3 vals uniq (KeyAt a k + 1));
            assumption).
      subst r. rewrite maxbitinsert_same__dp_body_branches_k3 by lia. lia.
    + specialize (Hdom j w ltac:(lia) Hjbest Hjrank).
      destruct (Z.eq_dec r rk) as [Hrr | Hrr].
      * subst r. rewrite maxbitinsert_same__dp_body_branches_k3 by lia. lia.
      * rewrite maxbitinsert_diff__dp_body_branches_k3 by lia. lia.
  - destruct (Z.eq_dec r rk) as [Hrr | Hrr].
    + subst r. rewrite maxbitinsert_same__dp_body_branches_k3 by lia.
      destruct (Z_le_gt_dec (Znth rk m 0) v) as [Hle | Hgt].
      * right. exists k, v. split; [lia |]. split; [exact Hbest |].
        split; [exact Hrk | lia].
      * replace (Z.max (Znth rk m 0) v) with (Znth rk m 0) by lia.
        destruct Hwit as [Hneg | [j [w [Hjb [Hjbest [Hjrank Hjeq]]]]]];
          [left; exact Hneg |].
        right. exists j, w. split; [lia |]. split; [exact Hjbest |].
        split; [exact Hjrank | exact Hjeq].
    + rewrite maxbitinsert_diff__dp_body_branches_k3 by lia.
      destruct Hwit as [Hneg | [j [w [Hjb [Hjbest [Hjrank Hjeq]]]]]];
        [left; exact Hneg |].
      right. exists j, w. split; [lia |]. split; [exact Hjbest |].
      split; [exact Hjrank | exact Hjeq].
Qed.

(* ---------- clamped running maxima ---------- *)
Lemma clamped_keep__dp_body_branches_k3 :
  forall (l l' : list Z) (k v x : Z),
    ClampedPrefixMax l k v ->
    0 <= k ->
    (forall j, 0 <= j < k -> Znth j l' 0 = Znth j l 0) ->
    Znth k l' 0 = x ->
    x <= v ->
    ClampedPrefixMax l' (k + 1) v.
Proof.
  intros l l' k v x [Hv [Hall Hwit]] Hk Hsame Hnew Hle.
  split; [exact Hv |]. split.
  - intros j Hj. destruct (Z.eq_dec j k) as [Heq | Hne].
    + subst j. rewrite Hnew. exact Hle.
    + rewrite (Hsame j ltac:(lia)). apply Hall; lia.
  - destruct Hwit as [Hz | [j [Hj Hjeq]]]; [left; exact Hz |].
    right. exists j. split; [lia |]. rewrite (Hsame j ltac:(lia)). exact Hjeq.
Qed.
Lemma clamped_update__dp_body_branches_k3 :
  forall (l l' : list Z) (k v x : Z),
    ClampedPrefixMax l k v ->
    0 <= k -> 0 <= x ->
    (forall j, 0 <= j < k -> Znth j l' 0 = Znth j l 0) ->
    Znth k l' 0 = x ->
    v <= x ->
    ClampedPrefixMax l' (k + 1) x.
Proof.
  intros l l' k v x [Hv [Hall Hwit]] Hk Hx Hsame Hnew Hle.
  split; [exact Hx |]. split.
  - intros j Hj. destruct (Z.eq_dec j k) as [Heq | Hne].
    + subst j. rewrite Hnew. lia.
    + rewrite (Hsame j ltac:(lia)). specialize (Hall j ltac:(lia)). lia.
  - right. exists k. split; [lia | exact Hnew].
Qed.
Lemma clamped_best1_keep__dp_body_branches_k3 :
  forall (a : list Z) (k v x : Z),
    ClampedBest1Upto a k v ->
    0 <= k ->
    Best1EndingAt a k x ->
    x <= v ->
    ClampedBest1Upto a (k + 1) v.
Proof.
  intros a k v x [Hv [Hall Hwit]] Hk Hbest Hle.
  split; [exact Hv |]. split.
  - intros j w Hj Hjbest. destruct (Z.eq_dec j k) as [Heq | Hne].
    + subst j.
      assert (w = x)
        by (apply (best1_unique__dp_body_branches_k3 a k w x Hjbest Hbest)).
      lia.
    + apply (Hall j w ltac:(lia) Hjbest).
  - destruct Hwit as [Hz | [j [w [Hj [Hjbest Hjeq]]]]]; [left; exact Hz |].
    right. exists j, w. split; [lia | split; [exact Hjbest | exact Hjeq]].
Qed.
Lemma clamped_best1_update__dp_body_branches_k3 :
  forall (a : list Z) (k v x : Z),
    ClampedBest1Upto a k v ->
    0 <= k -> 0 <= x ->
    Best1EndingAt a k x ->
    v <= x ->
    ClampedBest1Upto a (k + 1) x.
Proof.
  intros a k v x [Hv [Hall Hwit]] Hk Hx Hbest Hle.
  split; [exact Hx |]. split.
  - intros j w Hj Hjbest. destruct (Z.eq_dec j k) as [Heq | Hne].
    + subst j.
      assert (w = x)
        by (apply (best1_unique__dp_body_branches_k3 a k w x Hjbest Hbest)).
      lia.
    + specialize (Hall j w ltac:(lia) Hjbest). lia.
  - right. exists k, x. split; [lia | split; [exact Hbest | reflexivity]].
Qed.

(* ---------- ranges of the two DP layers ---------- *)
Lemma best0_range__dp_body_branches_k3 :
  forall (a : list Z) (i v : Z),
    0 <= i -> Best0EndingAt a i v -> 1 <= v <= i + 1.
Proof.
  intros a i v Hi [s [[[[Hmono [Hbd Hkey]] [Hpos Hlast]] _] Heq]].
  simpl in Heq. subst v. split; [lia |].
  apply (keep_len_bound__dp_body_branches_k3 s i); auto.
  intros p Hp. destruct (Hbd p Hp). lia.
Qed.
Lemma best1_range__dp_body_branches_k3 :
  forall (a : list Z) (i v : Z),
    0 <= i -> Best1EndingAt a i v -> 1 <= v <= i + 1.
Proof.
  intros a i v Hi [s [[[[d [[Hd0 [Hmono [Hbd Hkey]]] Hdi]] [Hpos Hlast]] _]
                     Heq]].
  simpl in Heq. subst v. split; [lia |].
  apply (keep_len_bound__dp_body_branches_k3 s i); auto.
  intros p Hp. destruct (Hbd p Hp). lia.
Qed.

(* ---------- one loop-body step of the DP over i ---------- *)
Lemma dp_core__dp_body_branches_k3 :
  forall (values vals_l c_l dp0_l m0 m1 mX dp0' : list Z)
         (n_pre nvals i r0 r1 rX d0 d1 : Z),
    1 <= i -> i < n_pre -> n_pre = Zlength values ->
    Zlength c_l = n_pre -> Zlength dp0_l = n_pre ->
    KeyPrefix values c_l n_pre ->
    CompressedKeys values vals_l nvals ->
    RankResult vals_l nvals (Znth i c_l 0) r0 -> 1 <= r0 <= nvals ->
    RankResult vals_l nvals (Znth i c_l 0 + 1) r1 -> 1 <= r1 <= nvals ->
    RankResult vals_l nvals (Znth (i - 1) c_l 0) rX -> 1 <= rX <= nvals ->
    DP0Prefix values dp0_l i ->
    Bit0Model values vals_l dp0_l m0 i nvals ->
    Bit1Model values vals_l m1 i nvals ->
    Bit0Model values vals_l dp0_l mX (i - 1) nvals ->
    d0 = Z.max (RangeMax m0 1 (r0 + 1)) 0 + 1 ->
    d1 = Z.max (Z.max (RangeMax m1 1 (r1 + 1)) (RangeMax mX 1 (r1 + 1))) 0 + 1 ->
    dp0' = replace_Znth i d0 dp0_l ->
    Best0EndingAt values i d0 /\
    Best1EndingAt values i d1 /\
    1 <= d0 <= i + 1 /\
    1 <= d1 <= i + 1 /\
    (forall j, 0 <= j < n_pre -> j <> i -> Znth j dp0' 0 = Znth j dp0_l 0) /\
    Znth i dp0' 0 = d0 /\
    Zlength dp0' = n_pre /\
    DP0Prefix values dp0' (i + 1) /\
    Bit0Model values vals_l dp0' (MaxBitInsert m0 r0 d0) (i + 1) nvals /\
    Bit1Model values vals_l (MaxBitInsert m1 r1 d1) (i + 1) nvals /\
    Bit0Model values vals_l dp0'
      (MaxBitInsert mX rX (Znth (i - 1) dp0_l 0)) i nvals.
Proof.
  intros values vals_l c_l dp0_l m0 m1 mX dp0' n_pre nvals i r0 r1 rX d0 d1
         Hi1 Hin Hn Hcl Hdpl Hkey Hcomp Hr0 Hr0b Hr1 Hr1b HrX HrXb
         Hdp Hb0 Hb1 HbX Hd0 Hd1 Hdp0'.
  destruct Hcomp as [Hinc [Hmemall _]].
  assert (Hmem : forall j, 0 <= j < Zlength values ->
                   MemberPrefix vals_l nvals (KeyAt values j))
    by (intros j Hj; apply (Hmemall j Hj)).
  assert (Hmem1 : forall j, 0 <= j < Zlength values ->
                    MemberPrefix vals_l nvals (KeyAt values j + 1))
    by (intros j Hj; apply (Hmemall j Hj)).
  assert (Hci : Znth i c_l 0 = KeyAt values i) by (apply Hkey; lia).
  assert (HciX : Znth (i - 1) c_l 0 = KeyAt values (i - 1)) by (apply Hkey; lia).
  rewrite Hci in Hr0, Hr1. rewrite HciX in HrX.
  assert (Hbest0 : Best0EndingAt values i d0).
  { rewrite Hd0.
    apply (best0_step__dp_body_branches_k3 values vals_l dp0_l m0 nvals i r0
             (RangeMax m0 1 (r0 + 1))); auto; lia. }
  assert (Hbest1 : Best1EndingAt values i d1).
  { rewrite Hd1.
    apply (best1_step__dp_body_branches_k3 values vals_l dp0_l m1 mX nvals i r1
             (Z.max (Z.max (RangeMax m1 1 (r1 + 1)) (RangeMax mX 1 (r1 + 1))) 0));
    auto; lia. }
  pose proof (best0_range__dp_body_branches_k3 values i d0 ltac:(lia) Hbest0).
  pose proof (best1_range__dp_body_branches_k3 values i d1 ltac:(lia) Hbest1).
  assert (Hdiff : forall j, 0 <= j < n_pre -> j <> i ->
                    Znth j dp0' 0 = Znth j dp0_l 0)
    by (intros j Hj Hne; subst dp0';
        apply Znth_replace_Znth_Diff; lia).
  assert (Hsame : Znth i dp0' 0 = d0)
    by (subst dp0'; apply Znth_replace_Znth_Same; lia).
  assert (Hlen' : Zlength dp0' = n_pre)
    by (subst dp0'; rewrite zlength_replace_Znth__dp_body_branches_k3; exact Hdpl).
  split; [exact Hbest0 |]. split; [exact Hbest1 |].
  split; [lia |]. split; [lia |].
  split; [exact Hdiff |]. split; [exact Hsame |]. split; [exact Hlen' |].
  split.
  - intros j Hj. destruct (Z.eq_dec j i) as [Heq | Hne].
    + subst j. rewrite Hsame. exact Hbest0.
    + rewrite (Hdiff j ltac:(lia) Hne). apply Hdp; lia.
  - split.
    + apply (bit0_model_insert__dp_body_branches_k3 values vals_l dp0_l dp0' m0
               i nvals r0 d0); auto; try lia.
      intros j Hj. apply Hdiff; lia.
    + split.
      * apply (bit1_model_insert__dp_body_branches_k3 values vals_l m1 i nvals
                 r1 d1); auto; lia.
      * assert (Hstep : Bit0Model values vals_l dp0'
                   (MaxBitInsert mX rX (Znth (i - 1) dp0_l 0))
                   (i - 1 + 1) nvals).
        { apply (bit0_model_insert__dp_body_branches_k3 values vals_l dp0_l dp0'
                   mX (i - 1) nvals rX (Znth (i - 1) dp0_l 0)); auto; try lia.
          - intros j Hj. apply Hdiff; lia.
          - apply Hdiff; lia. }
        replace (i - 1 + 1) with i in Hstep by lia. exact Hstep.
Qed.
Lemma maxbitinsert_bound__dp_body_branches_k3 :
  forall (m : list Z) (r v p lo hi : Z),
    0 <= r < Zlength m -> 0 <= p < Zlength m ->
    (forall q, 0 <= q < Zlength m -> lo <= Znth q m 0 <= hi) ->
    lo <= v <= hi ->
    lo <= Znth p (MaxBitInsert m r v) 0 <= hi.
Proof.
  intros m r v p lo hi Hr Hp Hall Hv.
  destruct (Z.eq_dec p r) as [Heq | Hne].
  - subst p. rewrite maxbitinsert_same__dp_body_branches_k3 by lia.
    specialize (Hall r Hr). lia.
  - rewrite maxbitinsert_diff__dp_body_branches_k3 by lia. apply Hall; lia.
Qed.
Lemma fold_max_ub__dp_body_branches_k4 :
  forall (f : Z -> Z) (l : list Z) (d x : Z),
    In x l -> f x <= fold_right Z.max d (map f l).
Proof.
  intros f l. induction l as [| y l IH]; intros d x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Hy | Hin].
    + subst y. apply Z.le_max_l.
    + eapply Z.le_trans; [apply (IH d x Hin) | apply Z.le_max_r].
Qed.
Lemma fold_max_attain__dp_body_branches_k4 :
  forall (f : Z -> Z) (l : list Z) (d : Z),
    fold_right Z.max d (map f l) = d \/
    exists x, In x l /\ fold_right Z.max d (map f l) = f x.
Proof.
  intros f l. induction l as [| y l IH]; intros d; simpl.
  - left; reflexivity.
  - destruct (IH d) as [Heq | [x [Hin Heq]]]; rewrite Heq.
    + destruct (Z.max_spec (f y) d) as [[H1 H2] | [H1 H2]]; rewrite H2.
      * left; reflexivity.
      * right; exists y; split; [left; reflexivity | reflexivity].
    + destruct (Z.max_spec (f y) (f x)) as [[H1 H2] | [H1 H2]]; rewrite H2.
      * right; exists x; split; [right; exact Hin | reflexivity].
      * right; exists y; split; [left; reflexivity | reflexivity].
Qed.
Lemma rangemax_prefix_char__dp_body_branches_k4 :
  forall (m : list Z) (lo hi : Z),
    (forall q, lo <= q < hi -> Znth q m 0 <= RangeMax m lo hi) /\
    (RangeMax m lo hi = MaxBitNeg \/
     exists q, lo <= q < hi /\ RangeMax m lo hi = Znth q m 0).
Proof.
  intros m lo hi. unfold RangeMax. split.
  - intros q Hq.
    exact (fold_max_ub__dp_body_branches_k4 (fun r => Znth r m 0) (Zrange lo hi)
             MaxBitNeg q (proj1 (In_Zrange lo hi q) Hq)).
  - destruct (fold_max_attain__dp_body_branches_k4 (fun r => Znth r m 0) (Zrange lo hi) MaxBitNeg)
      as [Heq | [x [Hin Heq]]].
    + left; exact Heq.
    + right. exists x. split; [apply In_Zrange; exact Hin | exact Heq].
Qed.
Lemma max_exists_bounded__dp_body_branches_k4 :
  forall (A : Type) (X : A -> Prop) (f : A -> Z) (K : Z) (a0 : A),
    X a0 -> (forall a, X a -> 0 <= f a <= K) ->
    exists v, max_value_of_subset Z.le X f v.
Proof.
  intros A X f K a0 Ha0 Hb.
  destruct (Hb a0 Ha0) as [Hlo Hhi].
  assert (HK : 0 <= K) by lia.
  destruct (max_n_in_range (fun n => exists a, X a /\ f a = n) K HK)
    as [mv [[a [HXa Hfa]] [Hmv Hmax]]].
  { exists (f a0). split; [lia | ]. exists a0. split; [exact Ha0 | reflexivity]. }
  exists mv. unfold max_value_of_subset, max_object_of_subset.
  exists a. split; [split | exact Hfa].
  - exact HXa.
  - intros b HXb. cbv beta in HXb.
    destruct (Hb b HXb) as [H1 H2].
    rewrite Hfa. apply Hmax; [lia | ]. exists b. split; [exact HXb | reflexivity].
Qed.
Lemma rank_exists__dp_body_branches_k4 :
  forall vals uniq v,
    StrictIncPrefix vals uniq ->
    MemberPrefix vals uniq v ->
    exists r, RankResult vals uniq v r.
Proof.
  intros vals uniq v Hsi [k [Hk Hv]].
  exists (k + 1). unfold RankResult. split; [lia | split].
  - replace (k + 1 - 1) with k by lia. exact Hv.
  - intros k' Hk'. rewrite <- Hv. apply Hsi; lia.
Qed.
Lemma rank_order_iso__dp_body_branches_k4 :
  forall vals uniq x y rx ry,
    StrictIncPrefix vals uniq ->
    RankResult vals uniq x rx ->
    RankResult vals uniq y ry ->
    (x <= y <-> rx <= ry).
Proof.
  intros vals uniq x y rx ry Hsi [[Hx1 Hx2] [Hxv Hxlt]] [[Hy1 Hy2] [Hyv Hylt]].
  split; intros H.
  - destruct (Z.le_gt_cases rx ry) as [Hle | Hgt]; [exact Hle | exfalso].
    specialize (Hxlt (ry - 1) ltac:(lia)).
    rewrite Hyv in Hxlt. lia.
  - destruct (Z.eq_dec rx ry) as [Heq | Hne].
    + subst ry. assert (x = y) by congruence. lia.
    + pose proof (Hsi (rx - 1) (ry - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as Hlt.
      rewrite Hxv in Hlt. rewrite Hyv in Hlt. lia.
Qed.
Lemma rank_unique__dp_body_branches_k4 :
  forall vals uniq v r1 r2,
    StrictIncPrefix vals uniq ->
    RankResult vals uniq v r1 -> RankResult vals uniq v r2 -> r1 = r2.
Proof.
  intros vals uniq v r1 r2 Hsi H1 H2.
  pose proof (rank_order_iso__dp_body_branches_k4 vals uniq v v r1 r2 Hsi H1 H2) as Ha.
  pose proof (rank_order_iso__dp_body_branches_k4 vals uniq v v r2 r1 Hsi H2 H1) as Hb.
  assert (r1 <= r2) by (apply Ha; lia).
  assert (r2 <= r1) by (apply Hb; lia).
  lia.
Qed.
Lemma mono_inc_index_le__dp_body_branches_k4 :
  forall (s : list Z),
    mono_inc s ->
    (forall p, 0 <= p < Zlength s -> 0 <= Znth p s 0) ->
    forall p, 0 <= p < Zlength s -> p <= Znth p s 0.
Proof.
  intros s Hm Hnn.
  assert (Hall : forall n : nat, forall p, p = Z.of_nat n -> 0 <= p < Zlength s -> p <= Znth p s 0).
  { induction n as [| n IH]; intros p Hp Hr.
    - subst p. simpl. apply Hnn. lia.
    - assert (Hn : Z.of_nat n <= Znth (Z.of_nat n) s 0).
      { apply IH; [reflexivity | ]. rewrite Nat2Z.inj_succ in Hp. lia. }
      assert (Hlt : Znth (Z.of_nat n) s 0 < Znth p s 0).
      { apply Hm; [lia | rewrite Nat2Z.inj_succ in Hp; lia | lia]. }
      rewrite Nat2Z.inj_succ in Hp. lia. }
  intros p Hp. apply (Hall (Z.to_nat p)); lia.
Qed.
Lemma split_last__dp_body_branches_k4 :
  forall (s : list Z), 0 < Zlength s ->
  exists s' x, s = s' ++ [x] /\ Zlength s' = Zlength s - 1 /\ x = Znth (Zlength s - 1) s 0.
Proof.
  intros s Hs.
  assert (Hne : s <> []).
  { intros ->. rewrite Zlength_nil in Hs. lia. }
  destruct (exists_last Hne) as [s' [x Hx]].
  exists s', x. split; [exact Hx | ].
  assert (HL : Zlength s = Zlength s' + 1).
  { rewrite Hx. rewrite Zlength_app. rewrite Zlength_cons, Zlength_nil. lia. }
  split; [lia | ].
  replace (Zlength s - 1) with (Zlength s') by lia.
  rewrite Hx. rewrite (app_Znth2 0 s' [x] (Zlength s')) by lia.
  replace (Zlength s' - Zlength s') with 0 by lia.
  reflexivity.
Qed.
Lemma Zlength_snoc__dp_body_branches_k4 :
  forall (s : list Z) (x : Z), Zlength (s ++ [x]) = Zlength s + 1.
Proof.
  intros. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia.
Qed.
Lemma Znth_snoc_last__dp_body_branches_k4 :
  forall (s : list Z) (x : Z), Znth (Zlength s) (s ++ [x]) 0 = x.
Proof.
  intros. rewrite (app_Znth2 0 s [x] (Zlength s)) by lia.
  replace (Zlength s - Zlength s) with 0 by lia. reflexivity.
Qed.
Lemma Znth_snoc_lt__dp_body_branches_k4 :
  forall (s : list Z) (x p : Z), 0 <= p < Zlength s -> Znth p (s ++ [x]) 0 = Znth p s 0.
Proof.
  intros. rewrite (app_Znth1 0 s [x] p) by lia. reflexivity.
Qed.
Lemma keep0_prefix__dp_body_branches_k4 :
  forall a s' x, Keep0List a (s' ++ [x]) -> Keep0List a s'.
Proof.
  intros a s' x [Hm [Hb Hk]].
  pose proof (Zlength_snoc__dp_body_branches_k4 s' x) as HL.
  pose proof (Zlength_nonneg s') as Hnn.
  split; [| split].
  - intros p q Hp Hpq Hq.
    rewrite <- (Znth_snoc_lt__dp_body_branches_k4 s' x p) by lia.
    rewrite <- (Znth_snoc_lt__dp_body_branches_k4 s' x q) by lia.
    apply Hm; lia.
  - intros p Hp. rewrite <- (Znth_snoc_lt__dp_body_branches_k4 s' x p) by lia.
    apply (Hb p). lia.
  - intros p q Hp Hpq Hq.
    rewrite <- (Znth_snoc_lt__dp_body_branches_k4 s' x p) by lia.
    rewrite <- (Znth_snoc_lt__dp_body_branches_k4 s' x q) by lia.
    apply Hk; lia.
Qed.
Lemma keep1_prefix__dp_body_branches_k4 :
  forall a d s' x, Keep1List a d (s' ++ [x]) -> Keep1List a d s'.
Proof.
  intros a d s' x [Hd [Hm [Hb Hk]]].
  pose proof (Zlength_snoc__dp_body_branches_k4 s' x) as HL.
  pose proof (Zlength_nonneg s') as Hnn.
  split; [exact Hd |]. split; [| split].
  - intros p q Hp Hpq Hq.
    rewrite <- (Znth_snoc_lt__dp_body_branches_k4 s' x p) by lia.
    rewrite <- (Znth_snoc_lt__dp_body_branches_k4 s' x q) by lia.
    apply Hm; lia.
  - intros p Hp. rewrite <- (Znth_snoc_lt__dp_body_branches_k4 s' x p) by lia.
    apply (Hb p). lia.
  - intros p q Hp Hpq Hq.
    rewrite <- (Znth_snoc_lt__dp_body_branches_k4 s' x p) by lia.
    rewrite <- (Znth_snoc_lt__dp_body_branches_k4 s' x q) by lia.
    apply Hk; lia.
Qed.
Lemma keep0_last_dominates__dp_body_branches_k4 :
  forall a s j, Keep0List a s -> 0 < Zlength s -> Znth (Zlength s - 1) s 0 = j ->
  forall p, 0 <= p < Zlength s ->
    Znth p s 0 <= j /\ KeyAt a (Znth p s 0) <= KeyAt a j.
Proof.
  intros a s j [Hm [Hb Hk]] Hpos Hlast p Hp.
  destruct (Z.eq_dec p (Zlength s - 1)) as [He | Hne].
  - subst p. rewrite Hlast. split; lia.
  - assert (Hlt : p < Zlength s - 1) by lia.
    pose proof (Hm p (Zlength s - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as H1.
    pose proof (Hk p (Zlength s - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as H2.
    rewrite Hlast in H1, H2. split; lia.
Qed.
Lemma keep1_last_dominates__dp_body_branches_k4 :
  forall a d s j, Keep1List a d s -> 0 < Zlength s -> Znth (Zlength s - 1) s 0 = j ->
  forall p, 0 <= p < Zlength s ->
    Znth p s 0 <= j /\ KeyShift a d (Znth p s 0) <= KeyShift a d j.
Proof.
  intros a d s j [Hd [Hm [Hb Hk]]] Hpos Hlast p Hp.
  destruct (Z.eq_dec p (Zlength s - 1)) as [He | Hne].
  - subst p. rewrite Hlast. split; lia.
  - assert (Hlt : p < Zlength s - 1) by lia.
    pose proof (Hm p (Zlength s - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as H1.
    pose proof (Hk p (Zlength s - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as H2.
    rewrite Hlast in H1, H2. split; lia.
Qed.
Lemma keep0_extend__dp_body_branches_k4 :
  forall a s i,
    Keep0List a s -> 0 <= i < Zlength a ->
    (forall p, 0 <= p < Zlength s -> Znth p s 0 < i) ->
    (forall p, 0 <= p < Zlength s -> KeyAt a (Znth p s 0) <= KeyAt a i) ->
    Keep0List a (s ++ [i]).
Proof.
  intros a s i [Hm [Hb Hk]] Hi Hlt Hkey.
  pose proof (Zlength_snoc__dp_body_branches_k4 s i) as HL.
  pose proof (Zlength_nonneg s) as Hnn.
  split; [| split].
  - intros p q Hp Hpq Hq.
    destruct (Z.eq_dec q (Zlength s)) as [He | Hne].
    + subst q. rewrite Znth_snoc_last__dp_body_branches_k4.
      rewrite Znth_snoc_lt__dp_body_branches_k4 by lia. apply Hlt; lia.
    + rewrite !Znth_snoc_lt__dp_body_branches_k4 by lia. apply Hm; lia.
  - intros p Hp. destruct (Z.eq_dec p (Zlength s)) as [He | Hne].
    + subst p. rewrite Znth_snoc_last__dp_body_branches_k4. lia.
    + rewrite Znth_snoc_lt__dp_body_branches_k4 by lia. apply (Hb p); lia.
  - intros p q Hp Hpq Hq.
    destruct (Z.eq_dec q (Zlength s)) as [He | Hne].
    + subst q. rewrite Znth_snoc_last__dp_body_branches_k4.
      rewrite Znth_snoc_lt__dp_body_branches_k4 by lia. apply Hkey; lia.
    + rewrite !Znth_snoc_lt__dp_body_branches_k4 by lia. apply Hk; lia.
Qed.
Lemma keep1_extend__dp_body_branches_k4 :
  forall a d s i,
    Keep1List a d s -> 0 <= i < Zlength a -> i <> d ->
    (forall p, 0 <= p < Zlength s -> Znth p s 0 < i) ->
    (forall p, 0 <= p < Zlength s -> KeyShift a d (Znth p s 0) <= KeyShift a d i) ->
    Keep1List a d (s ++ [i]).
Proof.
  intros a d s i [Hd [Hm [Hb Hk]]] Hi Hne0 Hlt Hkey.
  pose proof (Zlength_snoc__dp_body_branches_k4 s i) as HL.
  pose proof (Zlength_nonneg s) as Hnn.
  split; [exact Hd |]. split; [| split].
  - intros p q Hp Hpq Hq.
    destruct (Z.eq_dec q (Zlength s)) as [He | Hne].
    + subst q. rewrite Znth_snoc_last__dp_body_branches_k4.
      rewrite Znth_snoc_lt__dp_body_branches_k4 by lia. apply Hlt; lia.
    + rewrite !Znth_snoc_lt__dp_body_branches_k4 by lia. apply Hm; lia.
  - intros p Hp. destruct (Z.eq_dec p (Zlength s)) as [He | Hne].
    + subst p. rewrite Znth_snoc_last__dp_body_branches_k4. split; [lia | exact Hne0].
    + rewrite Znth_snoc_lt__dp_body_branches_k4 by lia. apply (Hb p); lia.
  - intros p q Hp Hpq Hq.
    destruct (Z.eq_dec q (Zlength s)) as [He | Hne].
    + subst q. rewrite Znth_snoc_last__dp_body_branches_k4.
      rewrite Znth_snoc_lt__dp_body_branches_k4 by lia. apply Hkey; lia.
    + rewrite !Znth_snoc_lt__dp_body_branches_k4 by lia. apply Hk; lia.
Qed.
Lemma keep0_length_bound__dp_body_branches_k4 :
  forall a s i, Keep0List a s -> 0 < Zlength s -> Znth (Zlength s - 1) s 0 = i ->
  Zlength s <= i + 1.
Proof.
  intros a s i [Hm [Hb Hk]] Hpos Hlast.
  pose proof (mono_inc_index_le__dp_body_branches_k4 s Hm
                ltac:(intros p Hp; apply (Hb p); lia) (Zlength s - 1) ltac:(lia)) as H.
  rewrite Hlast in H. lia.
Qed.
Lemma keep1_length_bound__dp_body_branches_k4 :
  forall a d s i, Keep1List a d s -> 0 < Zlength s -> Znth (Zlength s - 1) s 0 = i ->
  Zlength s <= i + 1.
Proof.
  intros a d s i [Hd [Hm [Hb Hk]]] Hpos Hlast.
  pose proof (mono_inc_index_le__dp_body_branches_k4 s Hm
                ltac:(intros p Hp; apply (Hb p); lia) (Zlength s - 1) ltac:(lia)) as H.
  rewrite Hlast in H. lia.
Qed.
Lemma keyshift_below__dp_body_branches_k4 :
  forall a d j, j < d -> KeyShift a d j = KeyAt a j.
Proof.
  intros a d j Hj. unfold KeyShift.
  destruct (Z.ltb_spec d j); lia.
Qed.
Lemma keyshift_above__dp_body_branches_k4 :
  forall a d j, d < j -> KeyShift a d j = KeyAt a j + 1.
Proof.
  intros a d j Hj. unfold KeyShift.
  destruct (Z.ltb_spec d j); lia.
Qed.
Lemma keep0_to_keep1__dp_body_branches_k4 :
  forall a d s, Keep0List a s -> 0 <= d < Zlength a ->
    (forall p, 0 <= p < Zlength s -> Znth p s 0 < d) ->
    Keep1List a d s.
Proof.
  intros a d s [Hm [Hb Hk]] Hd Hlt.
  split; [exact Hd |]. split; [exact Hm | split].
  - intros p Hp. pose proof (Hlt p Hp). pose proof (Hb p Hp). split; [lia | lia].
  - intros p q Hp Hpq Hq.
    rewrite !keyshift_below__dp_body_branches_k4 by (apply Hlt; lia).
    apply Hk; lia.
Qed.
Lemma keep1_to_keep0__dp_body_branches_k4 :
  forall a d s, Keep1List a d s ->
    (forall p, 0 <= p < Zlength s -> Znth p s 0 < d) ->
    Keep0List a s.
Proof.
  intros a d s [Hd [Hm [Hb Hk]]] Hlt.
  split; [exact Hm | split].
  - intros p Hp. apply (Hb p); lia.
  - intros p q Hp Hpq Hq.
    pose proof (Hk p q Hp Hpq Hq) as H.
    rewrite !keyshift_below__dp_body_branches_k4 in H by (apply Hlt; lia).
    exact H.
Qed.
Lemma best0_intro__dp_body_branches_k4 :
  forall a i s v,
    Keep0List a s -> 0 < Zlength s -> Znth (Zlength s - 1) s 0 = i -> Zlength s = v ->
    (forall t, Keep0List a t -> 0 < Zlength t -> Znth (Zlength t - 1) t 0 = i ->
       Zlength t <= v) ->
    Best0EndingAt a i v.
Proof.
  intros a i s v Hk Hpos Hlast Hlen Hub.
  unfold Best0EndingAt, max_value_of_subset, max_object_of_subset.
  exists s. split; [split | exact Hlen].
  - split; [exact Hk | split; [exact Hpos | exact Hlast]].
  - intros b Hb. destruct Hb as [Hb1 [Hb2 Hb3]].
    rewrite Hlen. apply Hub; assumption.
Qed.
Lemma best0_elim__dp_body_branches_k4 :
  forall a i v,
    Best0EndingAt a i v ->
    (exists s, Keep0List a s /\ 0 < Zlength s /\ Znth (Zlength s - 1) s 0 = i /\
               Zlength s = v) /\
    (forall t, Keep0List a t -> 0 < Zlength t -> Znth (Zlength t - 1) t 0 = i ->
       Zlength t <= v).
Proof.
  intros a i v H.
  unfold Best0EndingAt, max_value_of_subset, max_object_of_subset in H.
  destruct H as [s [[[Hk [Hpos Hlast]] Hmax] Hlen]].
  split.
  - exists s. split; [exact Hk | split; [exact Hpos | split; [exact Hlast | exact Hlen]]].
  - intros t Ht Htp Htl. rewrite <- Hlen.
    apply Hmax. split; [exact Ht | split; [exact Htp | exact Htl]].
Qed.
Lemma best1_intro__dp_body_branches_k4 :
  forall a i s d v,
    Keep1List a d s -> d < i -> 0 < Zlength s -> Znth (Zlength s - 1) s 0 = i ->
    Zlength s = v ->
    (forall t e, Keep1List a e t -> e < i -> 0 < Zlength t ->
       Znth (Zlength t - 1) t 0 = i -> Zlength t <= v) ->
    Best1EndingAt a i v.
Proof.
  intros a i s d v Hk Hd Hpos Hlast Hlen Hub.
  unfold Best1EndingAt, max_value_of_subset, max_object_of_subset.
  exists s. split; [split | exact Hlen].
  - split; [exists d; split; [exact Hk | exact Hd] | split; [exact Hpos | exact Hlast]].
  - intros b Hb. destruct Hb as [[e [He1 He2]] [Hb2 Hb3]].
    rewrite Hlen. apply (Hub b e); assumption.
Qed.
Lemma best1_elim__dp_body_branches_k4 :
  forall a i v,
    Best1EndingAt a i v ->
    (exists s d, Keep1List a d s /\ d < i /\ 0 < Zlength s /\
                 Znth (Zlength s - 1) s 0 = i /\ Zlength s = v) /\
    (forall t e, Keep1List a e t -> e < i -> 0 < Zlength t ->
       Znth (Zlength t - 1) t 0 = i -> Zlength t <= v).
Proof.
  intros a i v H.
  unfold Best1EndingAt, max_value_of_subset, max_object_of_subset in H.
  destruct H as [s [[[[d [Hk Hd]] [Hpos Hlast]] Hmax] Hlen]].
  split.
  - exists s, d. split; [exact Hk | split; [exact Hd | split; [exact Hpos |
      split; [exact Hlast | exact Hlen]]]].
  - intros t e Ht He Htp Htl. rewrite <- Hlen.
    apply Hmax. split; [exists e; split; [exact Ht | exact He] |
      split; [exact Htp | exact Htl]].
Qed.
Lemma keep0_singleton__dp_body_branches_k4 :
  forall a i, 0 <= i < Zlength a ->
    Keep0List a [i] /\ Zlength [i] = 1 /\ Znth (Zlength [i] - 1) [i] 0 = i.
Proof.
  intros a i Hi.
  assert (HL : Zlength [i] = 1) by (rewrite Zlength_cons, Zlength_nil; lia).
  split; [| split; [exact HL |]].
  - split; [apply mono_inc_single | split].
    + intros p Hp. rewrite HL in Hp. assert (p = 0) by lia. subst p.
      rewrite Znth0_cons. exact Hi.
    + intros p q Hp Hpq Hq. rewrite HL in Hq. lia.
  - rewrite HL. replace (1 - 1) with 0 by lia. rewrite Znth0_cons. reflexivity.
Qed.
Lemma keep1_singleton__dp_body_branches_k4 :
  forall a i, 1 <= i < Zlength a -> Keep1List a 0 [i].
Proof.
  intros a i Hi.
  assert (HL : Zlength [i] = 1) by (rewrite Zlength_cons, Zlength_nil; lia).
  split; [lia |]. split; [apply mono_inc_single | split].
  - intros p Hp. rewrite HL in Hp. assert (p = 0) by lia. subst p.
    rewrite Znth0_cons. split; [lia | lia].
  - intros p q Hp Hpq Hq. rewrite HL in Hq. lia.
Qed.
Lemma best0_exists__dp_body_branches_k4 :
  forall a i, 0 <= i < Zlength a -> exists v, Best0EndingAt a i v.
Proof.
  intros a i Hi.
  destruct (keep0_singleton__dp_body_branches_k4 a i Hi) as [Hk [HL Hlast]].
  apply (max_exists_bounded__dp_body_branches_k4 (list Z)
           (fun s : list Z => Keep0List a s /\ 0 < Zlength s /\ Znth (Zlength s - 1) s 0 = i)
           (fun s : list Z => Zlength s) (i + 1) [i]).
  - split; [exact Hk | split; [lia | exact Hlast]].
  - intros t [Ht1 [Ht2 Ht3]]. split.
    + apply Zlength_nonneg.
    + apply (keep0_length_bound__dp_body_branches_k4 a t i Ht1 Ht2 Ht3).
Qed.
Lemma best1_exists__dp_body_branches_k4 :
  forall a i, 1 <= i < Zlength a -> exists v, Best1EndingAt a i v.
Proof.
  intros a i Hi.
  pose proof (keep1_singleton__dp_body_branches_k4 a i Hi) as Hk.
  assert (HL : Zlength [i] = 1) by (rewrite Zlength_cons, Zlength_nil; lia).
  apply (max_exists_bounded__dp_body_branches_k4 (list Z)
           (fun s : list Z =>
              (exists d, Keep1List a d s /\ d < i) /\ 0 < Zlength s /\
              Znth (Zlength s - 1) s 0 = i)
           (fun s : list Z => Zlength s) (i + 1) [i]).
  - split; [exists 0; split; [exact Hk | lia] | split; [lia |]].
    rewrite HL. replace (1 - 1) with 0 by lia. rewrite Znth0_cons. reflexivity.
  - intros t [[e [Ht1 Ht4]] [Ht2 Ht3]]. split.
    + apply Zlength_nonneg.
    + apply (keep1_length_bound__dp_body_branches_k4 a e t i Ht1 Ht2 Ht3).
Qed.
Lemma best0_value_bound__dp_body_branches_k4 :
  forall a i v, 0 <= i < Zlength a -> Best0EndingAt a i v -> 1 <= v <= i + 1.
Proof.
  intros a i v Hi H.
  destruct (best0_elim__dp_body_branches_k4 a i v H) as [[s [Hk [Hpos [Hlast Hlen]]]] Hub].
  destruct (keep0_singleton__dp_body_branches_k4 a i Hi) as [Hk1 [HL Hlast1]].
  pose proof (Hub [i] Hk1 ltac:(lia) Hlast1) as H1.
  pose proof (keep0_length_bound__dp_body_branches_k4 a s i Hk Hpos Hlast) as H2.
  lia.
Qed.
Lemma best1_value_bound__dp_body_branches_k4 :
  forall a i v, 1 <= i < Zlength a -> Best1EndingAt a i v -> 1 <= v <= i + 1.
Proof.
  intros a i v Hi H.
  destruct (best1_elim__dp_body_branches_k4 a i v H) as [[s [d [Hk [Hd [Hpos [Hlast Hlen]]]]]] Hub].
  pose proof (keep1_singleton__dp_body_branches_k4 a i Hi) as Hk1.
  assert (HL : Zlength [i] = 1) by (rewrite Zlength_cons, Zlength_nil; lia).
  assert (Hlast1 : Znth (Zlength [i] - 1) [i] 0 = i).
  { rewrite HL. replace (1 - 1) with 0 by lia. rewrite Znth0_cons. reflexivity. }
  pose proof (Hub [i] 0 Hk1 ltac:(lia) ltac:(lia) Hlast1) as H1.
  pose proof (keep1_length_bound__dp_body_branches_k4 a d s i Hk Hpos Hlast) as H2.
  lia.
Qed.
Lemma best0_step__dp_body_branches_k4 :
  forall a vals dp0 m0 uniq i r0,
    0 <= i < Zlength a ->
    CompressedKeys a vals uniq ->
    DP0Prefix a dp0 i ->
    Bit0Model a vals dp0 m0 i uniq ->
    RankResult vals uniq (KeyAt a i) r0 ->
    Best0EndingAt a i (Z.max (RangeMax m0 1 (r0 + 1)) 0 + 1).
Proof.
  intros a vals dp0 m0 uniq i r0 Hi HCK HDP HB0 Hr0.
  destruct HCK as [Hsi [Hmem Hrep]].
  destruct HB0 as [Hlen0 HB0].
  assert (Hr0b : 1 <= r0 <= uniq) by (destruct Hr0 as [HH _]; exact HH).
  set (prev0 := RangeMax m0 1 (r0 + 1)) in *.
  pose proof (rangemax_prefix_char__dp_body_branches_k4 m0 1 (r0 + 1)) as [Hrmub Hrmat].
  assert (Hub : forall t, Keep0List a t -> 0 < Zlength t ->
                  Znth (Zlength t - 1) t 0 = i -> Zlength t <= Z.max prev0 0 + 1).
  { intros t Ht Htp Htl.
    destruct (Z.eq_dec (Zlength t) 1) as [He | Hne]; [lia |].
    destruct (split_last__dp_body_branches_k4 t Htp) as [t' [x [Hx [HLt Hxv]]]].
    assert (Hxi : x = i) by (rewrite Hxv; exact Htl).
    rewrite Hxi in Hx. clear Hxi Hxv. subst t.
    pose proof (Zlength_snoc__dp_body_branches_k4 t' i) as HL.
    assert (Ht'p : 0 < Zlength t') by lia.
    pose proof (keep0_prefix__dp_body_branches_k4 a t' i Ht) as Ht'.
    destruct Ht as [Hm [Hb Hk]].
    set (j := Znth (Zlength t' - 1) t' 0) in *.
    assert (Hjlt : j < i).
    { pose proof (Hm (Zlength t' - 1) (Zlength t') ltac:(lia) ltac:(lia) ltac:(lia)) as HH.
      rewrite Znth_snoc_lt__dp_body_branches_k4 in HH by lia.
      rewrite Znth_snoc_last__dp_body_branches_k4 in HH. exact HH. }
    assert (Hjkey : KeyAt a j <= KeyAt a i).
    { pose proof (Hk (Zlength t' - 1) (Zlength t') ltac:(lia) ltac:(lia) ltac:(lia)) as HH.
      rewrite Znth_snoc_lt__dp_body_branches_k4 in HH by lia.
      rewrite Znth_snoc_last__dp_body_branches_k4 in HH. exact HH. }
    assert (Hjb : 0 <= j < Zlength a).
    { pose proof (Hb (Zlength t' - 1) ltac:(lia)) as HH.
      rewrite Znth_snoc_lt__dp_body_branches_k4 in HH by lia. exact HH. }
    destruct (rank_exists__dp_body_branches_k4 vals uniq (KeyAt a j) Hsi
                (proj1 (Hmem j Hjb))) as [rj Hrj].
    assert (Hrjb : 1 <= rj <= uniq) by (destruct Hrj as [HH _]; exact HH).
    assert (Hrjle : rj <= r0).
    { apply (proj1 (rank_order_iso__dp_body_branches_k4 vals uniq (KeyAt a j) (KeyAt a i)
                      rj r0 Hsi Hrj Hr0)). exact Hjkey. }
    destruct (HB0 rj Hrjb) as [Hdom Hwit].
    pose proof (Hdom j ltac:(lia) Hrj) as Hd1.
    pose proof (Hrmub rj ltac:(lia)) as Hd2.
    pose proof (HDP j ltac:(lia)) as Hbest.
    destruct (best0_elim__dp_body_branches_k4 a j (Znth j dp0 0) Hbest) as [_ Hubj].
    assert (Hlastj : Znth (Zlength t' - 1) t' 0 = j) by reflexivity.
    pose proof (Hubj t' Ht' Ht'p Hlastj) as Hd3.
    lia. }
  destruct (Z_le_gt_dec prev0 0) as [Hle0 | Hgt0].
  - destruct (keep0_singleton__dp_body_branches_k4 a i Hi) as [Hk1 [HL1 Hlast1]].
    apply (best0_intro__dp_body_branches_k4 a i [i] (Z.max prev0 0 + 1) Hk1
             ltac:(lia) Hlast1 ltac:(lia) Hub).
  - destruct Hrmat as [Hbad | [q [Hq Heq]]].
    { unfold MaxBitNeg in Hbad. lia. }
    assert (Hqb : 1 <= q <= uniq) by lia.
    destruct (HB0 q Hqb) as [_ Hwit].
    destruct Hwit as [Hbad | [j [Hji [Hrj Hval]]]].
    { unfold MaxBitNeg in Hbad. lia. }
    assert (Hjb : 0 <= j < Zlength a) by lia.
    assert (Hdpj : Znth j dp0 0 = prev0) by lia.
    pose proof (HDP j ltac:(lia)) as Hbest.
    destruct (best0_elim__dp_body_branches_k4 a j (Znth j dp0 0) Hbest)
      as [[s' [Hk' [Hpos' [Hlast' Hlen']]]] _].
    assert (Hjkey : KeyAt a j <= KeyAt a i).
    { apply (proj2 (rank_order_iso__dp_body_branches_k4 vals uniq (KeyAt a j) (KeyAt a i)
                      q r0 Hsi Hrj Hr0)). lia. }
    pose proof (keep0_last_dominates__dp_body_branches_k4 a s' j Hk' Hpos' Hlast') as Hdom'.
    assert (Hext : Keep0List a (s' ++ [i])).
    { apply keep0_extend__dp_body_branches_k4; [exact Hk' | exact Hi | |].
      - intros p Hp. pose proof (Hdom' p Hp). lia.
      - intros p Hp. pose proof (Hdom' p Hp). lia. }
    pose proof (Zlength_snoc__dp_body_branches_k4 s' i) as HLs.
    apply (best0_intro__dp_body_branches_k4 a i (s' ++ [i]) (Z.max prev0 0 + 1) Hext
             ltac:(lia)); [| lia | exact Hub].
    replace (Zlength (s' ++ [i]) - 1) with (Zlength s') by lia.
    apply Znth_snoc_last__dp_body_branches_k4.
Qed.
Lemma best0_step_val__dp_body_branches_k4 :
  forall a vals dp0 m0 uniq i r0 prev0 d0,
    0 <= i < Zlength a ->
    CompressedKeys a vals uniq ->
    DP0Prefix a dp0 i ->
    Bit0Model a vals dp0 m0 i uniq ->
    RankResult vals uniq (KeyAt a i) r0 ->
    prev0 = RangeMax m0 1 (r0 + 1) ->
    d0 = Z.max prev0 0 + 1 ->
    Best0EndingAt a i d0.
Proof.
  intros. subst prev0 d0.
  apply (best0_step__dp_body_branches_k4 a vals dp0 m0 uniq i r0); assumption.
Qed.
Lemma best1_step__dp_body_branches_k4 :
  forall a vals dp0 m1 mX uniq i r1 viaSame viaCross bp,
    1 <= i < Zlength a ->
    CompressedKeys a vals uniq ->
    DP0Prefix a dp0 i ->
    Bit1Model a vals m1 i uniq ->
    Bit0Model a vals dp0 mX (i - 1) uniq ->
    RankResult vals uniq (KeyAt a i + 1) r1 ->
    viaSame = RangeMax m1 1 (r1 + 1) ->
    viaCross = RangeMax mX 1 (r1 + 1) ->
    bp = Z.max 0 (Z.max viaSame viaCross) ->
    Best1EndingAt a i (bp + 1).
Proof.
  intros a vals dp0 m1 mX uniq i r1 viaSame viaCross bp
         Hi HCK HDP HB1 HBX Hr1 Hvs Hvc Hbp.
  destruct HCK as [Hsi [Hmem Hrep]].
  destruct HB1 as [Hlen1 HB1].
  destruct HBX as [HlenX HBX].
  assert (Hr1b : 1 <= r1 <= uniq) by (destruct Hr1 as [HH _]; exact HH).
  pose proof (rangemax_prefix_char__dp_body_branches_k4 m1 1 (r1 + 1)) as [Hm1ub Hm1at].
  pose proof (rangemax_prefix_char__dp_body_branches_k4 mX 1 (r1 + 1)) as [HmXub HmXat].
  rewrite <- Hvs in Hm1ub, Hm1at. rewrite <- Hvc in HmXub, HmXat.
  assert (Hub : forall t e, Keep1List a e t -> e < i -> 0 < Zlength t ->
                  Znth (Zlength t - 1) t 0 = i -> Zlength t <= bp + 1).
  { intros t e Ht Hei Htp Htl.
    destruct (Z.eq_dec (Zlength t) 1) as [He | Hne]; [lia |].
    destruct (split_last__dp_body_branches_k4 t Htp) as [t' [x [Hx [HLt Hxv]]]].
    assert (Hxi : x = i) by (rewrite Hxv; exact Htl).
    rewrite Hxi in Hx. clear Hxi Hxv. subst t.
    pose proof (Zlength_snoc__dp_body_branches_k4 t' i) as HL.
    assert (Ht'p : 0 < Zlength t') by lia.
    pose proof (keep1_prefix__dp_body_branches_k4 a e t' i Ht) as Ht'.
    destruct Ht as [Hd [Hm [Hb Hk]]].
    set (j := Znth (Zlength t' - 1) t' 0) in *.
    assert (Hjlt : j < i).
    { pose proof (Hm (Zlength t' - 1) (Zlength t') ltac:(lia) ltac:(lia) ltac:(lia)) as HH.
      rewrite Znth_snoc_lt__dp_body_branches_k4 in HH by lia.
      rewrite Znth_snoc_last__dp_body_branches_k4 in HH. exact HH. }
    assert (Hjshift : KeyShift a e j <= KeyShift a e i).
    { pose proof (Hk (Zlength t' - 1) (Zlength t') ltac:(lia) ltac:(lia) ltac:(lia)) as HH.
      rewrite Znth_snoc_lt__dp_body_branches_k4 in HH by lia.
      rewrite Znth_snoc_last__dp_body_branches_k4 in HH. exact HH. }
    assert (Hjb : 0 <= j < Zlength a /\ j <> e).
    { pose proof (Hb (Zlength t' - 1) ltac:(lia)) as HH.
      rewrite Znth_snoc_lt__dp_body_branches_k4 in HH by lia. exact HH. }
    destruct Hjb as [Hjrange Hjne].
    pose proof (keep1_last_dominates__dp_body_branches_k4 a e t' j Ht' Ht'p eq_refl) as Hdom'.
    destruct (Z_lt_le_dec e j) as [Hej | Hje].
    - rewrite (keyshift_above__dp_body_branches_k4 a e j Hej) in Hjshift.
      rewrite (keyshift_above__dp_body_branches_k4 a e i ltac:(lia)) in Hjshift.
      destruct (best1_exists__dp_body_branches_k4 a j ltac:(lia)) as [w Hw].
      destruct (best1_elim__dp_body_branches_k4 a j w Hw) as [_ Hubw].
      pose proof (Hubw t' e Ht' Hej Ht'p eq_refl) as Hlt'.
      destruct (rank_exists__dp_body_branches_k4 vals uniq (KeyAt a j + 1) Hsi
                  (proj2 (Hmem j Hjrange))) as [rj Hrj].
      assert (Hrjb : 1 <= rj <= uniq) by (destruct Hrj as [HH _]; exact HH).
      assert (Hrjle : rj <= r1).
      { apply (proj1 (rank_order_iso__dp_body_branches_k4 vals uniq (KeyAt a j + 1)
                        (KeyAt a i + 1) rj r1 Hsi Hrj Hr1)). lia. }
      destruct (HB1 rj Hrjb) as [Hdom _].
      pose proof (Hdom j w ltac:(lia) Hw Hrj) as Hd1.
      pose proof (Hm1ub rj ltac:(lia)) as Hd2.
      lia.
    - assert (Hjlte : j < e) by lia.
      rewrite (keyshift_below__dp_body_branches_k4 a e j Hjlte) in Hjshift.
      rewrite (keyshift_above__dp_body_branches_k4 a e i ltac:(lia)) in Hjshift.
      assert (Hk0 : Keep0List a t').
      { apply (keep1_to_keep0__dp_body_branches_k4 a e t' Ht').
        intros p Hp. pose proof (Hdom' p Hp). lia. }
      destruct (rank_exists__dp_body_branches_k4 vals uniq (KeyAt a j) Hsi
                  (proj1 (Hmem j Hjrange))) as [rj Hrj].
      assert (Hrjb : 1 <= rj <= uniq) by (destruct Hrj as [HH _]; exact HH).
      assert (Hrjle : rj <= r1).
      { apply (proj1 (rank_order_iso__dp_body_branches_k4 vals uniq (KeyAt a j)
                        (KeyAt a i + 1) rj r1 Hsi Hrj Hr1)). lia. }
      pose proof (HDP j ltac:(lia)) as Hbest.
      destruct (best0_elim__dp_body_branches_k4 a j (Znth j dp0 0) Hbest) as [_ Hubj].
      pose proof (Hubj t' Hk0 Ht'p eq_refl) as Hd0.
      destruct (HBX rj Hrjb) as [Hdom _].
      pose proof (Hdom j ltac:(lia) Hrj) as Hd1.
      pose proof (HmXub rj ltac:(lia)) as Hd2.
      lia. }
  destruct (Z_le_gt_dec bp 0) as [Hle0 | Hgt0].
  - assert (Hbp0 : bp = 0) by lia.
    pose proof (keep1_singleton__dp_body_branches_k4 a i Hi) as Hk1.
    assert (HL1 : Zlength [i] = 1) by (rewrite Zlength_cons, Zlength_nil; lia).
    assert (Hlast1 : Znth (Zlength [i] - 1) [i] 0 = i).
    { rewrite HL1. replace (1 - 1) with 0 by lia. rewrite Znth0_cons. reflexivity. }
    apply (best1_intro__dp_body_branches_k4 a i [i] 0 (bp + 1) Hk1
             ltac:(lia) ltac:(lia) Hlast1 ltac:(lia) Hub).
  - destruct (Z_le_gt_dec viaCross viaSame) as [Hcs | Hcs].
    + assert (Hbpv : bp = viaSame) by lia.
      destruct Hm1at as [Hbad | [q [Hq Heq]]]; [unfold MaxBitNeg in Hbad; lia |].
      assert (Hqb : 1 <= q <= uniq) by lia.
      destruct (HB1 q Hqb) as [_ Hwit].
      destruct Hwit as [Hbad | [j [w [Hji [Hw [Hrj Hval]]]]]];
        [unfold MaxBitNeg in Hbad; lia |].
      assert (Hwv : w = bp) by lia.
      destruct (best1_elim__dp_body_branches_k4 a j w Hw)
        as [[s' [e [Hk' [He' [Hpos' [Hlast' Hlen']]]]]] _].
      assert (Hjkey : KeyAt a j + 1 <= KeyAt a i + 1).
      { apply (proj2 (rank_order_iso__dp_body_branches_k4 vals uniq (KeyAt a j + 1)
                        (KeyAt a i + 1) q r1 Hsi Hrj Hr1)). lia. }
      assert (Hjb : 0 <= j < Zlength a) by lia.
      pose proof (keep1_last_dominates__dp_body_branches_k4 a e s' j Hk' Hpos' Hlast') as Hdom'.
      assert (Hshift : KeyShift a e j <= KeyShift a e i).
      { rewrite (keyshift_above__dp_body_branches_k4 a e j He').
        rewrite (keyshift_above__dp_body_branches_k4 a e i ltac:(lia)). lia. }
      assert (Hext : Keep1List a e (s' ++ [i])).
      { apply keep1_extend__dp_body_branches_k4; [exact Hk' | lia | lia | |].
        - intros p Hp. pose proof (Hdom' p Hp). lia.
        - intros p Hp. pose proof (Hdom' p Hp). lia. }
      pose proof (Zlength_snoc__dp_body_branches_k4 s' i) as HLs.
      apply (best1_intro__dp_body_branches_k4 a i (s' ++ [i]) e (bp + 1) Hext
               ltac:(lia) ltac:(lia)); [| lia | exact Hub].
      replace (Zlength (s' ++ [i]) - 1) with (Zlength s') by lia.
      apply Znth_snoc_last__dp_body_branches_k4.
    + assert (Hbpv : bp = viaCross) by lia.
      destruct HmXat as [Hbad | [q [Hq Heq]]]; [unfold MaxBitNeg in Hbad; lia |].
      assert (Hqb : 1 <= q <= uniq) by lia.
      destruct (HBX q Hqb) as [_ Hwit].
      destruct Hwit as [Hbad | [j [Hji [Hrj Hval]]]];
        [unfold MaxBitNeg in Hbad; lia |].
      assert (Hdpj : Znth j dp0 0 = bp) by lia.
      pose proof (HDP j ltac:(lia)) as Hbest.
      destruct (best0_elim__dp_body_branches_k4 a j (Znth j dp0 0) Hbest)
        as [[s' [Hk' [Hpos' [Hlast' Hlen']]]] _].
      assert (Hjkey : KeyAt a j <= KeyAt a i + 1).
      { apply (proj2 (rank_order_iso__dp_body_branches_k4 vals uniq (KeyAt a j)
                        (KeyAt a i + 1) q r1 Hsi Hrj Hr1)). lia. }
      assert (Hjb : 0 <= j < Zlength a) by lia.
      pose proof (keep0_last_dominates__dp_body_branches_k4 a s' j Hk' Hpos' Hlast') as Hdom'.
      assert (Hk1' : Keep1List a (j + 1) s').
      { apply (keep0_to_keep1__dp_body_branches_k4 a (j + 1) s' Hk' ltac:(lia)).
        intros p Hp. pose proof (Hdom' p Hp). lia. }
      assert (Hext : Keep1List a (j + 1) (s' ++ [i])).
      { apply keep1_extend__dp_body_branches_k4; [exact Hk1' | lia | lia | |].
        - intros p Hp. pose proof (Hdom' p Hp). lia.
        - intros p Hp. pose proof (Hdom' p Hp) as HH.
          rewrite (keyshift_below__dp_body_branches_k4 a (j + 1) (Znth p s' 0)) by lia.
          rewrite (keyshift_above__dp_body_branches_k4 a (j + 1) i) by lia. lia. }
      pose proof (Zlength_snoc__dp_body_branches_k4 s' i) as HLs.
      apply (best1_intro__dp_body_branches_k4 a i (s' ++ [i]) (j + 1) (bp + 1) Hext
               ltac:(lia) ltac:(lia)); [| lia | exact Hub].
      replace (Zlength (s' ++ [i]) - 1) with (Zlength s') by lia.
      apply Znth_snoc_last__dp_body_branches_k4.
Qed.
Lemma best0_unique__dp_body_branches_k4 :
  forall a i v w, Best0EndingAt a i v -> Best0EndingAt a i w -> v = w.
Proof.
  intros a i v w H1 H2. unfold Best0EndingAt in *.
  exact (max_unique Z.le (fun s : list Z => Zlength s) _ v w H1 H2).
Qed.
Lemma best1_unique__dp_body_branches_k4 :
  forall a i v w, Best1EndingAt a i v -> Best1EndingAt a i w -> v = w.
Proof.
  intros a i v w H1 H2. unfold Best1EndingAt in *.
  exact (max_unique Z.le (fun s : list Z => Zlength s) _ v w H1 H2).
Qed.
Lemma length_replace_nth__dp_body_branches_k4 :
  forall {A : Type} (l : list A) (k : nat) (x : A),
    length (replace_nth k l x) = length l.
Proof.
  intros A l. induction l as [| y l IH]; intros k x; destruct k; simpl; auto.
Qed.
Lemma Zlength_replace_Znth__dp_body_branches_k4 :
  forall {A : Type} (n : Z) (x : A) (l : list A),
    Zlength (replace_Znth n x l) = Zlength l.
Proof.
  intros A n x l. unfold replace_Znth.
  rewrite !Zlength_correct. f_equal.
  apply length_replace_nth__dp_body_branches_k4.
Qed.
Lemma Zlength_maxbitinsert__dp_body_branches_k4 :
  forall m r v, Zlength (MaxBitInsert m r v) = Zlength m.
Proof.
  intros. unfold MaxBitInsert. apply Zlength_replace_Znth__dp_body_branches_k4.
Qed.
Lemma maxbitinsert_same__dp_body_branches_k4 :
  forall m r v, 0 <= r < Zlength m ->
    Znth r (MaxBitInsert m r v) 0 = Z.max (Znth r m 0) v.
Proof.
  intros. unfold MaxBitInsert. apply Znth_replace_Znth_Same. exact H.
Qed.
Lemma maxbitinsert_diff__dp_body_branches_k4 :
  forall m r v q, 0 <= r < Zlength m -> 0 <= q < Zlength m -> q <> r ->
    Znth q (MaxBitInsert m r v) 0 = Znth q m 0.
Proof.
  intros. unfold MaxBitInsert. apply Znth_replace_Znth_Diff; [exact H | exact H0 | lia].
Qed.
Lemma maxbitinsert_ge__dp_body_branches_k4 :
  forall m r v q, 0 <= r < Zlength m -> 0 <= q < Zlength m ->
    Znth q m 0 <= Znth q (MaxBitInsert m r v) 0.
Proof.
  intros m r v q Hr Hq. destruct (Z.eq_dec q r) as [He | Hne].
  - subst q. rewrite maxbitinsert_same__dp_body_branches_k4 by exact Hr. lia.
  - rewrite maxbitinsert_diff__dp_body_branches_k4 by assumption. lia.
Qed.
Lemma maxbitinsert_bound__dp_body_branches_k4 :
  forall m r v lo hi uniq,
    Zlength m = uniq + 1 -> 0 <= r < uniq + 1 ->
    (forall q, 0 <= q <= uniq -> lo <= Znth q m 0 <= hi) ->
    lo <= v <= hi ->
    forall q, 0 <= q <= uniq -> lo <= Znth q (MaxBitInsert m r v) 0 <= hi.
Proof.
  intros m r v lo hi uniq HL Hr Hb Hv q Hq.
  destruct (Z.eq_dec q r) as [He | Hne].
  - subst q. rewrite maxbitinsert_same__dp_body_branches_k4 by lia.
    pose proof (Hb r ltac:(lia)). lia.
  - rewrite maxbitinsert_diff__dp_body_branches_k4 by lia. apply Hb; lia.
Qed.
Lemma bit_model_insert__dp_body_branches_k4 :
  forall a vals dp dp' m uniq k r v,
    0 <= k ->
    StrictIncPrefix vals uniq ->
    Bit0Model a vals dp m k uniq ->
    RankResult vals uniq (KeyAt a k) r ->
    (forall j, 0 <= j < k -> Znth j dp' 0 = Znth j dp 0) ->
    Znth k dp' 0 = v ->
    Bit0Model a vals dp' (MaxBitInsert m r v) (k + 1) uniq.
Proof.
  intros a vals dp dp' m uniq k r v Hk0 Hsi [HLm HB] Hr Hkeep Hnew.
  assert (Hrb : 1 <= r <= uniq) by (destruct Hr as [HH _]; exact HH).
  assert (HrL : 0 <= r < Zlength m) by lia.
  split; [rewrite Zlength_maxbitinsert__dp_body_branches_k4; exact HLm |].
  intros q Hq.
  assert (HqL : 0 <= q < Zlength m) by lia.
  destruct (HB q Hq) as [Hdom Hwit].
  split.
  - intros j Hj Hrj.
    destruct (Z.eq_dec j k) as [Hjk | Hjk].
    + subst j. assert (Hqr : q = r).
      { apply (rank_unique__dp_body_branches_k4 vals uniq (KeyAt a k) q r Hsi Hrj Hr). }
      subst q. rewrite Hnew. rewrite maxbitinsert_same__dp_body_branches_k4 by lia. lia.
    + rewrite (Hkeep j ltac:(lia)).
      pose proof (Hdom j ltac:(lia) Hrj).
      pose proof (maxbitinsert_ge__dp_body_branches_k4 m r v q HrL HqL). lia.
  - destruct (Z.eq_dec q r) as [Hqr | Hqr].
    + subst q. rewrite maxbitinsert_same__dp_body_branches_k4 by lia.
      destruct (Z_le_gt_dec (Znth r m 0) v) as [Hle | Hgt].
      * right. exists k. split; [lia | split; [exact Hr |]].
        rewrite Hnew. lia.
      * destruct Hwit as [Hneg | [j [Hj [Hrj Hval]]]].
        -- left. lia.
        -- right. exists j. split; [lia | split; [exact Hrj |]].
           rewrite (Hkeep j ltac:(lia)). lia.
    + rewrite maxbitinsert_diff__dp_body_branches_k4 by lia.
      destruct Hwit as [Hneg | [j [Hj [Hrj Hval]]]].
      * left. exact Hneg.
      * right. exists j. split; [lia | split; [exact Hrj |]].
        rewrite (Hkeep j ltac:(lia)). exact Hval.
Qed.
Lemma bit1_model_insert__dp_body_branches_k4 :
  forall a vals m uniq k r v,
    0 <= k ->
    StrictIncPrefix vals uniq ->
    Bit1Model a vals m k uniq ->
    RankResult vals uniq (KeyAt a k + 1) r ->
    Best1EndingAt a k v ->
    Bit1Model a vals (MaxBitInsert m r v) (k + 1) uniq.
Proof.
  intros a vals m uniq k r v Hk0 Hsi [HLm HB] Hr Hbest.
  assert (Hrb : 1 <= r <= uniq) by (destruct Hr as [HH _]; exact HH).
  assert (HrL : 0 <= r < Zlength m) by lia.
  split; [rewrite Zlength_maxbitinsert__dp_body_branches_k4; exact HLm |].
  intros q Hq.
  assert (HqL : 0 <= q < Zlength m) by lia.
  destruct (HB q Hq) as [Hdom Hwit].
  split.
  - intros j w Hj Hw Hrj.
    destruct (Z.eq_dec j k) as [Hjk | Hjk].
    + subst j. assert (Hqr : q = r).
      { apply (rank_unique__dp_body_branches_k4 vals uniq (KeyAt a k + 1) q r Hsi Hrj Hr). }
      subst q. rewrite maxbitinsert_same__dp_body_branches_k4 by lia.
      assert (w = v) by (apply (best1_unique__dp_body_branches_k4 a k w v Hw Hbest)).
      lia.
    + pose proof (Hdom j w ltac:(lia) Hw Hrj).
      pose proof (maxbitinsert_ge__dp_body_branches_k4 m r v q HrL HqL). lia.
  - destruct (Z.eq_dec q r) as [Hqr | Hqr].
    + subst q. rewrite maxbitinsert_same__dp_body_branches_k4 by lia.
      destruct (Z_le_gt_dec (Znth r m 0) v) as [Hle | Hgt].
      * right. exists k, v. split; [lia | split; [exact Hbest | split; [exact Hr | lia]]].
      * destruct Hwit as [Hneg | [j [w [Hj [Hw [Hrj Hval]]]]]].
        -- left. lia.
        -- right. exists j, w. split; [lia | split; [exact Hw | split; [exact Hrj | lia]]].
    + rewrite maxbitinsert_diff__dp_body_branches_k4 by lia.
      destruct Hwit as [Hneg | [j [w [Hj [Hw [Hrj Hval]]]]]].
      * left. exact Hneg.
      * right. exists j, w. split; [lia | split; [exact Hw | split; [exact Hrj | exact Hval]]].
Qed.
Lemma dp0prefix_step__dp_body_branches_k4 :
  forall a dp dp' k d0,
    DP0Prefix a dp k -> 0 <= k ->
    (forall j, 0 <= j < k -> Znth j dp' 0 = Znth j dp 0) ->
    Znth k dp' 0 = d0 ->
    Best0EndingAt a k d0 ->
    DP0Prefix a dp' (k + 1).
Proof.
  intros a dp dp' k d0 HDP Hk Hkeep Hnew Hbest j Hj.
  destruct (Z.eq_dec j k) as [He | Hne].
  - subst j. rewrite Hnew. exact Hbest.
  - rewrite (Hkeep j ltac:(lia)). apply HDP. lia.
Qed.
Lemma clamped_step__dp_body_branches_k4 :
  forall dp dp' k best d0 v,
    0 <= k ->
    ClampedPrefixMax dp k best ->
    (forall j, 0 <= j < k -> Znth j dp' 0 = Znth j dp 0) ->
    Znth k dp' 0 = d0 ->
    0 <= d0 ->
    v = Z.max best d0 ->
    ClampedPrefixMax dp' (k + 1) v.
Proof.
  intros dp dp' k best d0 v Hk [Hnn [Hall Hwit]] Hkeep Hnew Hd0 Hv.
  split; [lia | split].
  - intros j Hj. destruct (Z.eq_dec j k) as [He | Hne].
    + subst j. rewrite Hnew. lia.
    + rewrite (Hkeep j ltac:(lia)). pose proof (Hall j ltac:(lia)). lia.
  - destruct (Z_le_gt_dec best d0) as [Hle | Hgt].
    + right. exists k. split; [lia | rewrite Hnew; lia].
    + destruct Hwit as [Hz | [j [Hj Hval]]].
      * left. lia.
      * right. exists j. split; [lia | rewrite (Hkeep j ltac:(lia)); lia].
Qed.
Lemma clamped_keep_step__dp_body_branches_k4 :
  forall dp dp' k best,
    0 <= k ->
    ClampedPrefixMax dp k best ->
    (forall j, 0 <= j < k -> Znth j dp' 0 = Znth j dp 0) ->
    Znth k dp' 0 <= best ->
    ClampedPrefixMax dp' (k + 1) best.
Proof.
  intros dp dp' k best Hk [Hnn [Hall Hwit]] Hkeep Hnew.
  split; [lia | split].
  - intros j Hj. destruct (Z.eq_dec j k) as [He | Hne].
    + subst j. exact Hnew.
    + rewrite (Hkeep j ltac:(lia)). apply Hall. lia.
  - destruct Hwit as [Hz | [j [Hj Hval]]].
    + left. exact Hz.
    + right. exists j. split; [lia | rewrite (Hkeep j ltac:(lia)); exact Hval].
Qed.
Lemma clamped_best1_step__dp_body_branches_k4 :
  forall a k best1 d1 v,
    0 <= k ->
    ClampedBest1Upto a k best1 ->
    Best1EndingAt a k d1 ->
    0 <= d1 ->
    v = Z.max best1 d1 ->
    ClampedBest1Upto a (k + 1) v.
Proof.
  intros a k best1 d1 v Hk [Hnn [Hall Hwit]] Hbest Hd1 Hv.
  split; [lia | split].
  - intros j w Hj Hw. destruct (Z.eq_dec j k) as [He | Hne].
    + subst j. assert (w = d1) by (apply (best1_unique__dp_body_branches_k4 a k w d1 Hw Hbest)).
      lia.
    + pose proof (Hall j w ltac:(lia) Hw). lia.
  - destruct (Z_le_gt_dec best1 d1) as [Hle | Hgt].
    + right. exists k, d1. split; [lia | split; [exact Hbest | lia]].
    + destruct Hwit as [Hz | [j [w [Hj [Hw Hval]]]]].
      * left. lia.
      * right. exists j, w. split; [lia | split; [exact Hw | lia]].
Qed.
Lemma Zlength_replace_Znth__dp_body_branches_k5 :
  forall {A : Type} (n : Z) (v : A) (l : list A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A n v l. unfold replace_Znth.
  generalize (Z.to_nat n) as k. clear n.
  induction l as [| x l IH]; intros k; simpl.
  - destruct k; reflexivity.
  - destruct k; simpl.
    + reflexivity.
    + rewrite !Zlength_cons. rewrite IH. reflexivity.
Qed.
Lemma fold_max_ub__dp_body_branches_k5 :
  forall (l : list Z) (b x : Z), In x l -> x <= fold_right Z.max b l.
Proof.
  induction l as [| a l IH]; intros b x Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Z.le_max_l.
    + specialize (IH b x Hin). lia.
Qed.
Lemma fold_max_char__dp_body_branches_k5 :
  forall (l : list Z) (b : Z),
    fold_right Z.max b l = b \/ In (fold_right Z.max b l) l.
Proof.
  induction l as [| a l IH]; intros b; simpl.
  - left; reflexivity.
  - destruct (IH b) as [Heq | Hin].
    + rewrite Heq. destruct (Z.max_spec a b) as [[_ ->] | [_ ->]].
      * left; reflexivity.
      * right; left; reflexivity.
    + destruct (Z.max_spec a (fold_right Z.max b l)) as [[_ Hm] | [_ Hm]];
        rewrite Hm.
      * right; right; exact Hin.
      * right; left; reflexivity.
Qed.
Lemma rangemax_ub__dp_body_branches_k5 :
  forall (m : list Z) (lo hi q : Z),
    lo <= q < hi -> Znth q m 0 <= RangeMax m lo hi.
Proof.
  intros m lo hi q Hq. unfold RangeMax.
  apply fold_max_ub__dp_body_branches_k5.
  apply in_map_iff. exists q. split; [reflexivity |].
  apply In_Zrange. exact Hq.
Qed.
Lemma rangemax_prefix_char__dp_body_branches_k5 :
  forall (m : list Z) (lo hi : Z),
    RangeMax m lo hi = MaxBitNeg \/
    exists q, lo <= q < hi /\ RangeMax m lo hi = Znth q m 0.
Proof.
  intros m lo hi. unfold RangeMax.
  destruct (fold_max_char__dp_body_branches_k5
              (map (fun r => Znth r m 0) (Zrange lo hi)) MaxBitNeg) as [Heq | Hin].
  - left; exact Heq.
  - right. apply in_map_iff in Hin. destruct Hin as [q [Hq Hin]].
    exists q. split.
    + apply In_Zrange. exact Hin.
    + symmetry. exact Hq.
Qed.
Lemma rangemax_le__dp_body_branches_k5 :
  forall (m : list Z) (lo hi B : Z),
    MaxBitNeg <= B ->
    (forall q, lo <= q < hi -> Znth q m 0 <= B) ->
    RangeMax m lo hi <= B.
Proof.
  intros m lo hi B HB Hall.
  destruct (rangemax_prefix_char__dp_body_branches_k5 m lo hi) as [Heq | [q [Hq Heq]]].
  - rewrite Heq. exact HB.
  - rewrite Heq. apply Hall. exact Hq.
Qed.
Lemma rank_unique__dp_body_branches_k5 :
  forall (l : list Z) (len v r1 r2 : Z),
    RankResult l len v r1 -> RankResult l len v r2 -> r1 = r2.
Proof.
  intros l len v r1 r2 [H1 [H2 H3]] [K1 [K2 K3]].
  destruct (Z.lt_trichotomy r1 r2) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
  - specialize (K3 (r1 - 1) ltac:(lia)). rewrite H2 in K3. lia.
  - specialize (H3 (r2 - 1) ltac:(lia)). rewrite K2 in H3. lia.
Qed.
Lemma rank_exists__dp_body_branches_k5 :
  forall (vals uniq : _) (v : Z),
    StrictIncPrefix vals uniq ->
    MemberPrefix vals uniq v ->
    exists r, RankResult vals uniq v r.
Proof.
  intros vals uniq v Hsi [k [Hk Hv]].
  exists (k + 1). unfold RankResult. split; [lia | split].
  - replace (k + 1 - 1) with k by lia. exact Hv.
  - intros j Hj. rewrite <- Hv. apply Hsi; lia.
Qed.
Lemma rank_order_iso__dp_body_branches_k5 :
  forall (vals uniq x rx y ry : _),
    StrictIncPrefix vals uniq ->
    RankResult vals uniq x rx ->
    RankResult vals uniq y ry ->
    (x <= y <-> rx <= ry).
Proof.
  intros vals uniq x rx y ry Hsi Hx Hy.
  destruct Hx as [Hx1 [Hx2 Hx3]]. destruct Hy as [Hy1 [Hy2 Hy3]].
  split; intros Hle.
  - destruct (Z.le_gt_cases rx ry) as [? | Hgt]; [assumption |].
    specialize (Hx3 (ry - 1) ltac:(lia)). rewrite Hy2 in Hx3. lia.
  - destruct (Z.eq_dec rx ry) as [-> | Hne].
    + rewrite Hx2 in Hy2. lia.
    + assert (Hlt : Znth (rx - 1) vals 0 < Znth (ry - 1) vals 0)
        by (apply Hsi; lia).
      rewrite Hx2, Hy2 in Hlt. lia.
Qed.
Lemma bounded_max_exists_aux__dp_body_branches_k5 :
  forall (k : nat) (Q : Z -> Prop) (lo B : Z),
    B - lo < Z.of_nat k ->
    (exists n, Q n) ->
    (forall n, Q n -> lo <= n <= B) ->
    exists m, Q m /\ (forall n, Q n -> n <= m).
Proof.
  induction k as [| k IH]; intros Q lo B Hk Hex Hbnd.
  - destruct Hex as [n Hn]. specialize (Hbnd n Hn). simpl in Hk. lia.
  - destruct (excluded_middle_informative (Q B)) as [HB | HB].
    + exists B. split; [exact HB |]. intros n Hn. specialize (Hbnd n Hn). lia.
    + apply (IH Q lo (B - 1)).
      * rewrite Nat2Z.inj_succ in Hk. lia.
      * exact Hex.
      * intros n Hn. specialize (Hbnd n Hn).
        assert (n <> B) by (intros ->; contradiction). lia.
Qed.
Lemma bounded_max_exists__dp_body_branches_k5 :
  forall (Q : Z -> Prop) (lo B : Z),
    (exists n, Q n) ->
    (forall n, Q n -> lo <= n <= B) ->
    exists m, Q m /\ (forall n, Q n -> n <= m).
Proof.
  intros Q lo B Hex Hbnd.
  apply (bounded_max_exists_aux__dp_body_branches_k5
           (Z.to_nat (B - lo + 1)) Q lo B).
  - destruct Hex as [n Hn]. specialize (Hbnd n Hn). lia.
  - exact Hex.
  - exact Hbnd.
Qed.
Lemma max_len_exists__dp_body_branches_k5 :
  forall (P : list Z -> Prop) (B : Z),
    (exists s, P s) ->
    (forall s, P s -> Zlength s <= B) ->
    exists v, max_value_of_subset Z.le P (fun s : list Z => Zlength s) v.
Proof.
  intros P B Hex Hbnd.
  destruct (bounded_max_exists__dp_body_branches_k5
              (fun n => exists s, P s /\ Zlength s = n) 0 B) as [m [[s0 [Hs0 Hlen]] Hmax]].
  - destruct Hex as [s Hs]. exists (Zlength s), s. split; [exact Hs | reflexivity].
  - intros n [s [Hs <-]]. split; [apply Zlength_nonneg | apply Hbnd; exact Hs].
  - exists m. unfold max_value_of_subset, max_object_of_subset.
    exists s0. split; [split |].
    + exact Hs0.
    + intros b Hb. rewrite Hlen. apply Hmax. exists b. split; [exact Hb | reflexivity].
    + exact Hlen.
Qed.
Lemma max_value_unique__dp_body_branches_k5 :
  forall (P : list Z -> Prop) (u v : Z),
    max_value_of_subset Z.le P (fun s : list Z => Zlength s) u ->
    max_value_of_subset Z.le P (fun s : list Z => Zlength s) v ->
    u = v.
Proof.
  intros P u v [a [[Ha Hamax] Hau]] [b [[Hb Hbmax] Hbv]].
  specialize (Hamax b Hb). specialize (Hbmax a Ha). lia.
Qed.
Lemma mono_inc_gap__dp_body_branches_k5 :
  forall (k : nat) (s : list Z) (p q : Z),
    mono_inc s -> 0 <= p -> p <= q -> q < Zlength s -> q - p <= Z.of_nat k ->
    Znth p s 0 + (q - p) <= Znth q s 0.
Proof.
  induction k as [| k IH]; intros s p q Hmono Hp Hpq Hq Hk.
  - simpl in Hk. assert (q = p) by lia. subst q. lia.
  - destruct (Z.eq_dec q p) as [-> | Hne]; [lia |].
    assert (Hlt : Znth (q - 1) s 0 < Znth q s 0) by (apply Hmono; lia).
    specialize (IH s p (q - 1) Hmono Hp ltac:(lia) ltac:(lia)).
    rewrite Nat2Z.inj_succ in Hk.
    specialize (IH ltac:(lia)). lia.
Qed.
Lemma mono_inc_span__dp_body_branches_k5 :
  forall (s : list Z) (p q : Z),
    mono_inc s -> 0 <= p -> p <= q -> q < Zlength s ->
    Znth p s 0 + (q - p) <= Znth q s 0.
Proof.
  intros s p q Hmono Hp Hpq Hq.
  apply (mono_inc_gap__dp_body_branches_k5 (Z.to_nat (q - p)) s p q); try assumption.
  lia.
Qed.

(* ---- list surgery on keep sets ---- *)
Lemma Znth_app_lt__dp_body_branches_k5 :
  forall (s : list Z) (x p : Z),
    0 <= p < Zlength s -> Znth p (s ++ [x]) 0 = Znth p s 0.
Proof. intros. apply app_Znth1. lia. Qed.
Lemma Znth_app_last__dp_body_branches_k5 :
  forall (s : list Z) (x : Z), Znth (Zlength s) (s ++ [x]) 0 = x.
Proof.
  intros. rewrite app_Znth2 by lia.
  replace (Zlength s - Zlength s) with 0 by lia. reflexivity.
Qed.
Lemma Zlength_snoc__dp_body_branches_k5 :
  forall (s : list Z) (x : Z), Zlength (s ++ [x]) = Zlength s + 1.
Proof. intros. rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. Qed.
Lemma Zlength_peel__dp_body_branches_k5 :
  forall (s : list Z), 0 < Zlength s ->
    Zlength (sublist 0 (Zlength s - 1) s) = Zlength s - 1.
Proof. intros. rewrite Zlength_sublist by lia. lia. Qed.
Lemma Znth_peel__dp_body_branches_k5 :
  forall (s : list Z) (p : Z),
    0 <= p < Zlength s - 1 -> Znth p (sublist 0 (Zlength s - 1) s) 0 = Znth p s 0.
Proof. intros. rewrite Znth_sublist by lia. f_equal. lia. Qed.
Lemma mono_inc_le_last__dp_body_branches_k5 :
  forall (s : list Z) (p : Z),
    mono_inc s -> 0 < Zlength s -> 0 <= p < Zlength s ->
    Znth p s 0 <= Znth (Zlength s - 1) s 0.
Proof.
  intros s p Hm Hs Hp.
  destruct (Z.eq_dec p (Zlength s - 1)) as [-> | Hne]; [lia |].
  assert (Znth p s 0 < Znth (Zlength s - 1) s 0) by (apply Hm; lia). lia.
Qed.
Lemma keep_last_len_bound__dp_body_branches_k5 :
  forall (s : list Z) (j : Z),
    mono_inc s -> 0 < Zlength s ->
    (forall p, 0 <= p < Zlength s -> 0 <= Znth p s 0) ->
    Znth (Zlength s - 1) s 0 = j ->
    Zlength s <= j + 1.
Proof.
  intros s j Hm Hs Hnn Hlast.
  pose proof (mono_inc_span__dp_body_branches_k5 s 0 (Zlength s - 1) Hm
                ltac:(lia) ltac:(lia) ltac:(lia)) as Hgap.
  specialize (Hnn 0 ltac:(lia)). lia.
Qed.
Lemma keep0_peel__dp_body_branches_k5 :
  forall a s, Keep0List a s -> 0 < Zlength s ->
    Keep0List a (sublist 0 (Zlength s - 1) s).
Proof.
  intros a s [Hm [Hb Hk]] Hs.
  rewrite ?Zlength_peel__dp_body_branches_k5 by lia.
  split; [| split].
  - intros p q Hp Hpq Hq.
    rewrite Zlength_peel__dp_body_branches_k5 in Hq by lia.
    rewrite !Znth_peel__dp_body_branches_k5 by lia. apply Hm; lia.
  - intros p Hp. rewrite Zlength_peel__dp_body_branches_k5 in Hp by lia.
    rewrite Znth_peel__dp_body_branches_k5 by lia. apply Hb; lia.
  - intros p q Hp Hpq Hq.
    rewrite Zlength_peel__dp_body_branches_k5 in Hq by lia.
    rewrite !Znth_peel__dp_body_branches_k5 by lia. apply Hk; lia.
Qed.
Lemma keep1_peel__dp_body_branches_k5 :
  forall a d s, Keep1List a d s -> 0 < Zlength s ->
    Keep1List a d (sublist 0 (Zlength s - 1) s).
Proof.
  intros a d s [Hd [Hm [Hb Hk]]] Hs.
  split; [exact Hd | split; [| split]].
  - intros p q Hp Hpq Hq.
    rewrite Zlength_peel__dp_body_branches_k5 in Hq by lia.
    rewrite !Znth_peel__dp_body_branches_k5 by lia. apply Hm; lia.
  - intros p Hp. rewrite Zlength_peel__dp_body_branches_k5 in Hp by lia.
    rewrite Znth_peel__dp_body_branches_k5 by lia. apply Hb; lia.
  - intros p q Hp Hpq Hq.
    rewrite Zlength_peel__dp_body_branches_k5 in Hq by lia.
    rewrite !Znth_peel__dp_body_branches_k5 by lia. apply Hk; lia.
Qed.
Lemma keep0_snoc__dp_body_branches_k5 :
  forall a s x,
    Keep0List a s ->
    0 <= x < Zlength a ->
    (forall p, 0 <= p < Zlength s -> Znth p s 0 < x) ->
    (forall p, 0 <= p < Zlength s -> KeyAt a (Znth p s 0) <= KeyAt a x) ->
    Keep0List a (s ++ [x]).
Proof.
  intros a s x [Hm [Hb Hk]] Hx Hlt Hkey.
  split; [| split].
  - intros p q Hp Hpq Hq.
    rewrite Zlength_snoc__dp_body_branches_k5 in Hq.
    rewrite Znth_app_lt__dp_body_branches_k5 by lia.
    destruct (Z.eq_dec q (Zlength s)) as [-> | Hne].
    + rewrite Znth_app_last__dp_body_branches_k5. apply Hlt; lia.
    + rewrite Znth_app_lt__dp_body_branches_k5 by lia. apply Hm; lia.
  - intros p Hp. rewrite Zlength_snoc__dp_body_branches_k5 in Hp.
    destruct (Z.eq_dec p (Zlength s)) as [-> | Hne].
    + rewrite Znth_app_last__dp_body_branches_k5. lia.
    + rewrite Znth_app_lt__dp_body_branches_k5 by lia. apply Hb; lia.
  - intros p q Hp Hpq Hq.
    rewrite Zlength_snoc__dp_body_branches_k5 in Hq.
    rewrite Znth_app_lt__dp_body_branches_k5 by lia.
    destruct (Z.eq_dec q (Zlength s)) as [-> | Hne].
    + rewrite Znth_app_last__dp_body_branches_k5. apply Hkey; lia.
    + rewrite Znth_app_lt__dp_body_branches_k5 by lia. apply Hk; lia.
Qed.
Lemma keep1_snoc__dp_body_branches_k5 :
  forall a d s x,
    Keep1List a d s ->
    0 <= x < Zlength a -> x <> d ->
    (forall p, 0 <= p < Zlength s -> Znth p s 0 < x) ->
    (forall p, 0 <= p < Zlength s -> KeyShift a d (Znth p s 0) <= KeyShift a d x) ->
    Keep1List a d (s ++ [x]).
Proof.
  intros a d s x [Hd [Hm [Hb Hk]]] Hx Hxd Hlt Hkey.
  split; [exact Hd | split; [| split]].
  - intros p q Hp Hpq Hq.
    rewrite Zlength_snoc__dp_body_branches_k5 in Hq.
    rewrite Znth_app_lt__dp_body_branches_k5 by lia.
    destruct (Z.eq_dec q (Zlength s)) as [-> | Hne].
    + rewrite Znth_app_last__dp_body_branches_k5. apply Hlt; lia.
    + rewrite Znth_app_lt__dp_body_branches_k5 by lia. apply Hm; lia.
  - intros p Hp. rewrite Zlength_snoc__dp_body_branches_k5 in Hp.
    destruct (Z.eq_dec p (Zlength s)) as [-> | Hne].
    + rewrite Znth_app_last__dp_body_branches_k5. split; [lia | exact Hxd].
    + rewrite Znth_app_lt__dp_body_branches_k5 by lia. apply Hb; lia.
  - intros p q Hp Hpq Hq.
    rewrite Zlength_snoc__dp_body_branches_k5 in Hq.
    rewrite Znth_app_lt__dp_body_branches_k5 by lia.
    destruct (Z.eq_dec q (Zlength s)) as [-> | Hne].
    + rewrite Znth_app_last__dp_body_branches_k5. apply Hkey; lia.
    + rewrite Znth_app_lt__dp_body_branches_k5 by lia. apply Hk; lia.
Qed.
Lemma keyshift_lt__dp_body_branches_k5 :
  forall a d x, x < d -> KeyShift a d x = KeyAt a x.
Proof.
  intros. unfold KeyShift.
  destruct (Z.ltb_spec d x); [lia | lia].
Qed.
Lemma keyshift_gt__dp_body_branches_k5 :
  forall a d x, d < x -> KeyShift a d x = KeyAt a x + 1.
Proof.
  intros. unfold KeyShift.
  destruct (Z.ltb_spec d x); [lia | lia].
Qed.
Lemma keep0_to_keep1__dp_body_branches_k5 :
  forall a d s,
    Keep0List a s -> 0 <= d < Zlength a ->
    (forall p, 0 <= p < Zlength s -> Znth p s 0 < d) ->
    Keep1List a d s.
Proof.
  intros a d s [Hm [Hb Hk]] Hd Hlt.
  split; [exact Hd | split; [exact Hm | split]].
  - intros p Hp. split; [apply Hb; lia |].
    specialize (Hlt p Hp). lia.
  - intros p q Hp Hpq Hq.
    rewrite !keyshift_lt__dp_body_branches_k5 by (apply Hlt; lia).
    apply Hk; lia.
Qed.
Lemma keep1_to_keep0__dp_body_branches_k5 :
  forall a d s,
    Keep1List a d s ->
    (forall p, 0 <= p < Zlength s -> Znth p s 0 < d) ->
    Keep0List a s.
Proof.
  intros a d s [Hd [Hm [Hb Hk]]] Hlt.
  split; [exact Hm | split].
  - intros p Hp. apply Hb; lia.
  - intros p q Hp Hpq Hq.
    specialize (Hk p q Hp Hpq Hq).
    rewrite !keyshift_lt__dp_body_branches_k5 in Hk by (apply Hlt; lia).
    exact Hk.
Qed.

(* ---- Fenwick model insertion ---- *)
Lemma maxbitinsert_len__dp_body_branches_k5 :
  forall m r v, Zlength (MaxBitInsert m r v) = Zlength m.
Proof.
  intros. unfold MaxBitInsert. apply Zlength_replace_Znth__dp_body_branches_k5.
Qed.
Lemma maxbitinsert_same__dp_body_branches_k5 :
  forall m r v, 0 <= r < Zlength m ->
    Znth r (MaxBitInsert m r v) 0 = Z.max (Znth r m 0) v.
Proof.
  intros. unfold MaxBitInsert. apply Znth_replace_Znth_Same. lia.
Qed.
Lemma maxbitinsert_diff__dp_body_branches_k5 :
  forall m r v t, 0 <= r < Zlength m -> 0 <= t < Zlength m -> t <> r ->
    Znth t (MaxBitInsert m r v) 0 = Znth t m 0.
Proof.
  intros. unfold MaxBitInsert. apply Znth_replace_Znth_Diff; lia.
Qed.
Lemma maxbitinsert_ge__dp_body_branches_k5 :
  forall m r v t, 0 <= r < Zlength m -> 0 <= t < Zlength m ->
    Znth t m 0 <= Znth t (MaxBitInsert m r v) 0.
Proof.
  intros m r v t Hr Ht. destruct (Z.eq_dec t r) as [-> | Hne].
  - rewrite maxbitinsert_same__dp_body_branches_k5 by lia. apply Z.le_max_l.
  - rewrite maxbitinsert_diff__dp_body_branches_k5 by lia. lia.
Qed.
Lemma bit0_model_dp_congr__dp_body_branches_k5 :
  forall values vals dp dp' m k uniq,
    Bit0Model values vals dp m k uniq ->
    (forall j, 0 <= j < k -> Znth j dp' 0 = Znth j dp 0) ->
    Bit0Model values vals dp' m k uniq.
Proof.
  intros values vals dp dp' m k uniq [Hlen Hmod] Hagree.
  split; [exact Hlen |]. intros r Hr. specialize (Hmod r Hr).
  destruct Hmod as [Hdom Hwit]. split.
  - intros j Hj Hrank. rewrite Hagree by lia. apply Hdom; assumption.
  - destruct Hwit as [Hneg | [j [Hj [Hrank Heq]]]].
    + left; exact Hneg.
    + right. exists j. rewrite Hagree by lia. auto.
Qed.
Lemma bit0_model_insert__dp_body_branches_k5 :
  forall values vals dp0 m0 k uniq r v,
    Bit0Model values vals dp0 m0 k uniq ->
    0 <= k ->
    RankResult vals uniq (KeyAt values k) r ->
    1 <= r <= uniq ->
    Znth k dp0 0 = v ->
    Bit0Model values vals dp0 (MaxBitInsert m0 r v) (k + 1) uniq.
Proof.
  intros values vals dp0 m0 k uniq r v [Hlen Hmod] Hk Hrank Hrb Hv.
  assert (Hm : 0 <= r < Zlength m0) by lia.
  split; [rewrite maxbitinsert_len__dp_body_branches_k5; exact Hlen |].
  intros t Ht. assert (Htm : 0 <= t < Zlength m0) by lia.
  specialize (Hmod t Ht). destruct Hmod as [Hdom Hwit].
  split.
  - intros j Hj Hrj.
    destruct (Z.eq_dec j k) as [-> | Hne].
    + assert (t = r) by (apply (rank_unique__dp_body_branches_k5 vals uniq (KeyAt values k)); assumption).
      subst t. rewrite maxbitinsert_same__dp_body_branches_k5 by lia.
      rewrite Hv. apply Z.le_max_r.
    + pose proof (maxbitinsert_ge__dp_body_branches_k5 m0 r v t Hm Htm).
      assert (Znth j dp0 0 <= Znth t m0 0) by (apply Hdom; [lia | assumption]).
      lia.
  - destruct (Z.eq_dec t r) as [-> | Hne].
    + rewrite maxbitinsert_same__dp_body_branches_k5 by lia.
      destruct (Z.max_spec (Znth r m0 0) v) as [[Hlt Hmx] | [Hle Hmx]]; rewrite Hmx.
      * right. exists k. split; [lia | split; [exact Hrank | auto]].
      * destruct Hwit as [Hneg | [j [Hj [Hrj Heq]]]].
        -- left; exact Hneg.
        -- right. exists j. split; [lia | split; assumption].
    + rewrite maxbitinsert_diff__dp_body_branches_k5 by lia.
      destruct Hwit as [Hneg | [j [Hj [Hrj Heq]]]].
      * left; exact Hneg.
      * right. exists j. split; [lia | split; assumption].
Qed.
Lemma bit1_model_insert__dp_body_branches_k5 :
  forall values vals m1 k uniq r v,
    Bit1Model values vals m1 k uniq ->
    0 <= k ->
    RankResult vals uniq (KeyAt values k + 1) r ->
    1 <= r <= uniq ->
    Best1EndingAt values k v ->
    Bit1Model values vals (MaxBitInsert m1 r v) (k + 1) uniq.
Proof.
  intros values vals m1 k uniq r v [Hlen Hmod] Hk Hrank Hrb Hbest.
  assert (Hm : 0 <= r < Zlength m1) by lia.
  split; [rewrite maxbitinsert_len__dp_body_branches_k5; exact Hlen |].
  intros t Ht. assert (Htm : 0 <= t < Zlength m1) by lia.
  specialize (Hmod t Ht). destruct Hmod as [Hdom Hwit].
  split.
  - intros j w Hj Hbj Hrj.
    destruct (Z.eq_dec j k) as [-> | Hne].
    + assert (t = r) by (apply (rank_unique__dp_body_branches_k5 vals uniq (KeyAt values k + 1)); assumption).
      subst t.
      assert (w = v) by (apply (max_value_unique__dp_body_branches_k5 _ _ _ Hbj Hbest)).
      subst w. rewrite maxbitinsert_same__dp_body_branches_k5 by lia.
      apply Z.le_max_r.
    + pose proof (maxbitinsert_ge__dp_body_branches_k5 m1 r v t Hm Htm).
      assert (w <= Znth t m1 0) by (apply (Hdom j w); [lia | assumption | assumption]).
      lia.
  - destruct (Z.eq_dec t r) as [-> | Hne].
    + rewrite maxbitinsert_same__dp_body_branches_k5 by lia.
      destruct (Z.max_spec (Znth r m1 0) v) as [[Hlt Hmx] | [Hle Hmx]]; rewrite Hmx.
      * right. exists k, v. split; [lia | split; [exact Hbest | split; [exact Hrank | reflexivity]]].
      * destruct Hwit as [Hneg | [j [w [Hj [Hbj [Hrj Heq]]]]]].
        -- left; exact Hneg.
        -- right. exists j, w. split; [lia | split; [exact Hbj | split; assumption]].
    + rewrite maxbitinsert_diff__dp_body_branches_k5 by lia.
      destruct Hwit as [Hneg | [j [w [Hj [Hbj [Hrj Heq]]]]]].
      * left; exact Hneg.
      * right. exists j, w. split; [lia | split; [exact Hbj | split; assumption]].
Qed.

(* ---- clamped running maxima ---- *)
Lemma clamped_step__dp_body_branches_k5 :
  forall l l' k v x w,
    ClampedPrefixMax l k v ->
    (forall j, 0 <= j < k -> Znth j l' 0 = Znth j l 0) ->
    Znth k l' 0 = x ->
    0 <= k -> 0 <= x ->
    ((w = x /\ v <= x) \/ (w = v /\ x <= v)) ->
    ClampedPrefixMax l' (k + 1) w.
Proof.
  intros l l' k v x w [Hv0 [Hub Hwit]] Hagree Hnew Hk Hx Hcase.
  assert (Hw : 0 <= w) by (destruct Hcase as [[-> _] | [-> _]]; lia).
  split; [exact Hw | split].
  - intros j Hj. destruct (Z.eq_dec j k) as [-> | Hne].
    + rewrite Hnew. destruct Hcase as [[-> _] | [-> ?]]; lia.
    + rewrite Hagree by lia. specialize (Hub j ltac:(lia)).
      destruct Hcase as [[-> ?] | [-> ?]]; lia.
  - destruct Hcase as [[-> Hvx] | [-> Hxv]].
    + right. exists k. split; [lia | exact Hnew].
    + destruct Hwit as [Hzero | [j [Hj Heq]]].
      * left; exact Hzero.
      * right. exists j. split; [lia | rewrite Hagree by lia; exact Heq].
Qed.
Lemma clamped_best1_step__dp_body_branches_k5 :
  forall a k v d1 w,
    ClampedBest1Upto a k v ->
    Best1EndingAt a k d1 ->
    0 <= k -> 0 <= d1 ->
    ((w = d1 /\ v <= d1) \/ (w = v /\ d1 <= v)) ->
    ClampedBest1Upto a (k + 1) w.
Proof.
  intros a k v d1 w [Hv0 [Hub Hwit]] Hbest Hk Hd1 Hcase.
  assert (Hw : 0 <= w) by (destruct Hcase as [[-> _] | [-> _]]; lia).
  split; [exact Hw | split].
  - intros j u Hj Hbj. destruct (Z.eq_dec j k) as [-> | Hne].
    + assert (u = d1) by (apply (max_value_unique__dp_body_branches_k5 _ _ _ Hbj Hbest)).
      subst u. destruct Hcase as [[-> _] | [-> ?]]; lia.
    + specialize (Hub j u ltac:(lia) Hbj).
      destruct Hcase as [[-> ?] | [-> ?]]; lia.
  - destruct Hcase as [[-> Hvd] | [-> Hdv]].
    + right. exists k, d1. split; [lia | split; [exact Hbest | reflexivity]].
    + destruct Hwit as [Hzero | [j [u [Hj [Hbj Heq]]]]].
      * left; exact Hzero.
      * right. exists j, u. split; [lia | split; assumption].
Qed.

(* ---- the layer-0 DP step ---- *)
Lemma best0_step__dp_body_branches_k5 :
  forall values vals dp0 m0 uniq i r0 prev0,
    0 <= i < Zlength values ->
    StrictIncPrefix vals uniq ->
    (forall j, 0 <= j < Zlength values -> MemberPrefix vals uniq (KeyAt values j)) ->
    DP0Prefix values dp0 i ->
    Bit0Model values vals dp0 m0 i uniq ->
    RankResult vals uniq (KeyAt values i) r0 ->
    prev0 = RangeMax m0 1 (r0 + 1) ->
    Best0EndingAt values i (Z.max prev0 0 + 1).
Proof.
  intros values vals dp0 m0 uniq i r0 prev0 Hi Hsi Hmem Hdp Hbit Hr0 Hprev.
  assert (Hr0b : 1 <= r0 <= uniq) by (destruct Hr0 as [HH _]; lia).
  destruct Hbit as [Hbitlen Hbitmod].
  assert (F1 : forall j, 0 <= j < i -> KeyAt values j <= KeyAt values i ->
                 Znth j dp0 0 <= prev0).
  { intros j Hj Hkey.
    destruct (rank_exists__dp_body_branches_k5 vals uniq (KeyAt values j) Hsi
                (Hmem j ltac:(lia))) as [rj Hrj].
    assert (Hrjb : 1 <= rj <= uniq) by (destruct Hrj as [HH _]; lia).
    assert (Hle : rj <= r0).
    { apply (rank_order_iso__dp_body_branches_k5 vals uniq (KeyAt values j) rj
               (KeyAt values i) r0 Hsi Hrj Hr0). exact Hkey. }
    destruct (Hbitmod rj Hrjb) as [Hdom _].
    specialize (Hdom j ltac:(lia) Hrj).
    pose proof (rangemax_ub__dp_body_branches_k5 m0 1 (r0 + 1) rj ltac:(lia)).
    lia. }
  assert (F2 : 0 < prev0 -> exists j, 0 <= j < i /\ KeyAt values j <= KeyAt values i /\
                                      Znth j dp0 0 = prev0).
  { intros Hpos.
    destruct (rangemax_prefix_char__dp_body_branches_k5 m0 1 (r0 + 1))
      as [Hneg | [q [Hq Heq]]].
    - rewrite <- Hprev in Hneg. unfold MaxBitNeg in Hneg. lia.
    - rewrite <- Hprev in Heq.
      assert (Hqb : 1 <= q <= uniq) by lia.
      destruct (Hbitmod q Hqb) as [_ Hwit].
      destruct Hwit as [Hn | [j [Hj [Hrj Hval]]]].
      + rewrite Hn in Heq. unfold MaxBitNeg in Heq. lia.
      + exists j. split; [exact Hj | split; [| lia]].
        apply (rank_order_iso__dp_body_branches_k5 vals uniq (KeyAt values j) q
                 (KeyAt values i) r0 Hsi Hrj Hr0). lia. }
  assert (UB : forall b, (Keep0List values b /\ 0 < Zlength b /\
                          Znth (Zlength b - 1) b 0 = i) ->
                 Zlength b <= Z.max prev0 0 + 1).
  { intros b [Hkb [Hbpos Hblast]].
    destruct (Z.le_gt_cases (Zlength b) 1) as [Hle1 | Hgt1]; [lia |].
    pose proof Hkb as Hkbc.
    destruct Hkb as [Hbm [Hbb Hbk]].
    remember (Znth (Zlength b - 2) b 0) as j eqn:Hjdef.
    assert (Hjlt : j < i).
    { rewrite Hjdef, <- Hblast. apply Hbm; lia. }
    assert (Hjnn : 0 <= j).
    { rewrite Hjdef. specialize (Hbb (Zlength b - 2) ltac:(lia)). lia. }
    assert (Hjkey : KeyAt values j <= KeyAt values i).
    { rewrite Hjdef, <- Hblast. apply Hbk; lia. }
    assert (Hpeel : Keep0List values (sublist 0 (Zlength b - 1) b))
      by (apply keep0_peel__dp_body_branches_k5; [exact Hkbc | lia]).
    assert (Hplen : Zlength (sublist 0 (Zlength b - 1) b) = Zlength b - 1)
      by (apply Zlength_peel__dp_body_branches_k5; lia).
    assert (Hplast : Znth (Zlength (sublist 0 (Zlength b - 1) b) - 1)
                          (sublist 0 (Zlength b - 1) b) 0 = j).
    { rewrite Hplen. replace (Zlength b - 1 - 1) with (Zlength b - 2) by lia.
      rewrite Znth_peel__dp_body_branches_k5 by lia. auto. }
    pose proof (Hdp j ltac:(lia)) as Hbj.
    destruct Hbj as [a0 [[Ha0in Ha0max] Ha0len]].
    assert (Hmemb : Keep0List values (sublist 0 (Zlength b - 1) b) /\
                    0 < Zlength (sublist 0 (Zlength b - 1) b) /\
                    Znth (Zlength (sublist 0 (Zlength b - 1) b) - 1)
                         (sublist 0 (Zlength b - 1) b) 0 = j)
      by (split; [exact Hpeel | split; [lia | exact Hplast]]).
    pose proof (Ha0max _ Hmemb) as Hle. cbv beta in Hle.
    pose proof (F1 j ltac:(lia) Hjkey) as Hf1.
    lia. }
  unfold Best0EndingAt, max_value_of_subset, max_object_of_subset.
  destruct (Z.le_gt_cases prev0 0) as [Hle0 | Hpos].
  - assert (Hin : Keep0List values [i] /\ 0 < Zlength [i] /\
                  Znth (Zlength [i] - 1) [i] 0 = i).
    { split; [split; [| split] | split].
      - intros p q Hp Hpq Hq. rewrite Zlength_cons, Zlength_nil in Hq. lia.
      - intros p Hp. rewrite Zlength_cons, Zlength_nil in Hp.
        assert (p = 0) by lia. subst p. rewrite Znth0_cons. lia.
      - intros p q Hp Hpq Hq. rewrite Zlength_cons, Zlength_nil in Hq. lia.
      - rewrite Zlength_cons, Zlength_nil. lia.
      - rewrite Zlength_cons, Zlength_nil.
        replace (0 + 1 - 1) with 0 by lia. apply Znth0_cons. }
    replace (Z.max prev0 0 + 1) with 1 by lia.
    exists [i]. split; [split |].
    + exact Hin.
    + intros b Hb. cbv beta. pose proof (UB b Hb) as Hub.
      rewrite Zlength_cons, Zlength_nil. lia.
    + cbv beta. rewrite Zlength_cons, Zlength_nil. lia.
  - destruct (F2 Hpos) as [j [Hj [Hjkey Hjval]]].
    pose proof (Hdp j Hj) as Hbj.
    destruct Hbj as [sj [[Hsjin Hsjmax] Hsjlen]].
    destruct Hsjin as [Hsjk [Hsjpos Hsjlast]].
    assert (Hsjle : forall p, 0 <= p < Zlength sj -> Znth p sj 0 <= j).
    { intros p Hp. rewrite <- Hsjlast.
      apply mono_inc_le_last__dp_body_branches_k5;
        [exact (proj1 Hsjk) | lia | lia]. }
    assert (Hsjkey : forall p, 0 <= p < Zlength sj ->
                       KeyAt values (Znth p sj 0) <= KeyAt values i).
    { intros p Hp.
      assert (Hstep : KeyAt values (Znth p sj 0) <= KeyAt values j).
      { destruct (Z.eq_dec p (Zlength sj - 1)) as [-> | Hne].
        - rewrite Hsjlast. lia.
        - pose proof (proj2 (proj2 Hsjk) p (Zlength sj - 1) ltac:(lia) ltac:(lia)
                        ltac:(lia)) as Hk3.
          rewrite Hsjlast in Hk3. lia. }
      lia. }
    assert (Hsnoc : Keep0List values (sj ++ [i])).
    { apply keep0_snoc__dp_body_branches_k5.
      - exact Hsjk.
      - lia.
      - intros p Hp. specialize (Hsjle p Hp). lia.
      - exact Hsjkey. }
    assert (Hin : Keep0List values (sj ++ [i]) /\ 0 < Zlength (sj ++ [i]) /\
                  Znth (Zlength (sj ++ [i]) - 1) (sj ++ [i]) 0 = i).
    { split; [exact Hsnoc | split].
      - rewrite Zlength_snoc__dp_body_branches_k5. lia.
      - rewrite Zlength_snoc__dp_body_branches_k5.
        replace (Zlength sj + 1 - 1) with (Zlength sj) by lia.
        apply Znth_app_last__dp_body_branches_k5. }
    replace (Z.max prev0 0 + 1) with (Zlength sj + 1) by lia.
    exists (sj ++ [i]). split; [split |].
    + exact Hin.
    + intros b Hb. cbv beta. rewrite Zlength_snoc__dp_body_branches_k5.
      pose proof (UB b Hb) as Hub. lia.
    + cbv beta. apply Zlength_snoc__dp_body_branches_k5.
Qed.

(* ---- the layer-1 DP step ---- *)
Lemma best1_exists__dp_body_branches_k5 :
  forall values j s,
    ((exists d, Keep1List values d s /\ d < j) /\ 0 < Zlength s /\
     Znth (Zlength s - 1) s 0 = j) ->
    exists w, Best1EndingAt values j w.
Proof.
  intros values j s Hs.
  unfold Best1EndingAt.
  apply (max_len_exists__dp_body_branches_k5 _ (j + 1)).
  - exists s. exact Hs.
  - intros b Hb. destruct Hb as [[d [Hk Hd]] [Hpos Hlast]].
    destruct Hk as [Hdb [Hm [Hbnd Hkey]]].
    apply (keep_last_len_bound__dp_body_branches_k5 b j Hm Hpos);
      [| exact Hlast].
    intros p Hp. specialize (Hbnd p Hp). lia.
Qed.
Lemma best1_step__dp_body_branches_k5 :
  forall values vals dp0 m1 mX uniq i r1 vs vc,
    1 <= i < Zlength values ->
    StrictIncPrefix vals uniq ->
    (forall j, 0 <= j < Zlength values ->
       MemberPrefix vals uniq (KeyAt values j) /\
       MemberPrefix vals uniq (KeyAt values j + 1)) ->
    DP0Prefix values dp0 i ->
    Bit1Model values vals m1 i uniq ->
    Bit0Model values vals dp0 mX (i - 1) uniq ->
    RankResult vals uniq (KeyAt values i + 1) r1 ->
    vs = RangeMax m1 1 (r1 + 1) ->
    vc = RangeMax mX 1 (r1 + 1) ->
    Best1EndingAt values i (Z.max 0 (Z.max vs vc) + 1).
Proof.
  intros values vals dp0 m1 mX uniq i r1 vs vc Hi Hsi Hmem Hdp Hb1 HbX Hr1 Hvs Hvc.
  assert (Hr1b : 1 <= r1 <= uniq) by (destruct Hr1 as [HH _]; lia).
  destruct Hb1 as [Hb1len Hb1mod].
  destruct HbX as [HbXlen HbXmod].
  assert (G1 : forall j w, 0 <= j < i -> Best1EndingAt values j w ->
                 KeyAt values j <= KeyAt values i -> w <= vs).
  { intros j w Hj Hbj Hkey.
    destruct (rank_exists__dp_body_branches_k5 vals uniq (KeyAt values j + 1) Hsi
                (proj2 (Hmem j ltac:(lia)))) as [rj Hrj].
    assert (Hrjb : 1 <= rj <= uniq) by (destruct Hrj as [HH _]; lia).
    assert (Hle : rj <= r1).
    { apply (rank_order_iso__dp_body_branches_k5 vals uniq (KeyAt values j + 1) rj
               (KeyAt values i + 1) r1 Hsi Hrj Hr1). lia. }
    destruct (Hb1mod rj Hrjb) as [Hdom _].
    specialize (Hdom j w ltac:(lia) Hbj Hrj).
    pose proof (rangemax_ub__dp_body_branches_k5 m1 1 (r1 + 1) rj ltac:(lia)).
    lia. }
  assert (G2 : forall j, 0 <= j < i - 1 -> KeyAt values j <= KeyAt values i + 1 ->
                 Znth j dp0 0 <= vc).
  { intros j Hj Hkey.
    destruct (rank_exists__dp_body_branches_k5 vals uniq (KeyAt values j) Hsi
                (proj1 (Hmem j ltac:(lia)))) as [rj Hrj].
    assert (Hrjb : 1 <= rj <= uniq) by (destruct Hrj as [HH _]; lia).
    assert (Hle : rj <= r1).
    { apply (rank_order_iso__dp_body_branches_k5 vals uniq (KeyAt values j) rj
               (KeyAt values i + 1) r1 Hsi Hrj Hr1). exact Hkey. }
    destruct (HbXmod rj Hrjb) as [Hdom _].
    specialize (Hdom j ltac:(lia) Hrj).
    pose proof (rangemax_ub__dp_body_branches_k5 mX 1 (r1 + 1) rj ltac:(lia)).
    lia. }
  assert (G3 : 0 < vs -> exists j w, 0 <= j < i /\ Best1EndingAt values j w /\
                                     w = vs /\ KeyAt values j <= KeyAt values i).
  { intros Hpos.
    destruct (rangemax_prefix_char__dp_body_branches_k5 m1 1 (r1 + 1))
      as [Hneg | [q [Hq Heq]]].
    - rewrite <- Hvs in Hneg. unfold MaxBitNeg in Hneg. lia.
    - rewrite <- Hvs in Heq.
      assert (Hqb : 1 <= q <= uniq) by lia.
      destruct (Hb1mod q Hqb) as [_ Hwit].
      destruct Hwit as [Hn | [j [w [Hj [Hbj [Hrj Hval]]]]]].
      + rewrite Hn in Heq. unfold MaxBitNeg in Heq. lia.
      + exists j, w. split; [exact Hj | split; [exact Hbj | split; [lia |]]].
        assert (KeyAt values j + 1 <= KeyAt values i + 1).
        { apply (rank_order_iso__dp_body_branches_k5 vals uniq (KeyAt values j + 1) q
                   (KeyAt values i + 1) r1 Hsi Hrj Hr1). lia. }
        lia. }
  assert (G4 : 0 < vc -> exists j, 0 <= j < i - 1 /\ Znth j dp0 0 = vc /\
                                   KeyAt values j <= KeyAt values i + 1).
  { intros Hpos.
    destruct (rangemax_prefix_char__dp_body_branches_k5 mX 1 (r1 + 1))
      as [Hneg | [q [Hq Heq]]].
    - rewrite <- Hvc in Hneg. unfold MaxBitNeg in Hneg. lia.
    - rewrite <- Hvc in Heq.
      assert (Hqb : 1 <= q <= uniq) by lia.
      destruct (HbXmod q Hqb) as [_ Hwit].
      destruct Hwit as [Hn | [j [Hj [Hrj Hval]]]].
      + rewrite Hn in Heq. unfold MaxBitNeg in Heq. lia.
      + exists j. split; [exact Hj | split; [lia |]].
        apply (rank_order_iso__dp_body_branches_k5 vals uniq (KeyAt values j) q
                 (KeyAt values i + 1) r1 Hsi Hrj Hr1). lia. }
  assert (UB : forall b, ((exists d, Keep1List values d b /\ d < i) /\
                          0 < Zlength b /\ Znth (Zlength b - 1) b 0 = i) ->
                 Zlength b <= Z.max 0 (Z.max vs vc) + 1).
  { intros b [[d [Hk Hdi]] [Hpos Hlast]].
    destruct (Z.le_gt_cases (Zlength b) 1) as [Hle1 | Hgt1]; [lia |].
    pose proof Hk as Hkc.
    destruct Hk as [Hdb [Hm [Hbnd Hkey]]].
    remember (Znth (Zlength b - 2) b 0) as j eqn:Hjdef.
    assert (Hjlt : j < i).
    { rewrite Hjdef, <- Hlast. apply Hm; lia. }
    assert (Hjb : 0 <= j < Zlength values /\ j <> d).
    { rewrite Hjdef. apply Hbnd; lia. }
    assert (Hjkey : KeyShift values d j <= KeyShift values d i).
    { assert (Hstep : KeyShift values d j <=
                      KeyShift values d (Znth (Zlength b - 1) b 0)).
      { rewrite Hjdef. apply Hkey; lia. }
      rewrite Hlast in Hstep. exact Hstep. }
    assert (Hpeel : Keep1List values d (sublist 0 (Zlength b - 1) b))
      by (apply keep1_peel__dp_body_branches_k5; [exact Hkc | lia]).
    assert (Hplen : Zlength (sublist 0 (Zlength b - 1) b) = Zlength b - 1)
      by (apply Zlength_peel__dp_body_branches_k5; lia).
    assert (Hplast : Znth (Zlength (sublist 0 (Zlength b - 1) b) - 1)
                          (sublist 0 (Zlength b - 1) b) 0 = j).
    { rewrite Hplen. replace (Zlength b - 1 - 1) with (Zlength b - 2) by lia.
      rewrite Znth_peel__dp_body_branches_k5 by lia. auto. }
    assert (Hpelem : forall p, 0 <= p < Zlength (sublist 0 (Zlength b - 1) b) ->
                       Znth p (sublist 0 (Zlength b - 1) b) 0 <= j).
    { intros p Hp. rewrite <- Hplast.
      apply mono_inc_le_last__dp_body_branches_k5;
        [exact (proj1 (proj2 Hpeel)) | lia | lia]. }
    destruct (Z.lt_trichotomy j d) as [Hjd | [Hjd | Hjd]].
    - assert (Hk0 : Keep0List values (sublist 0 (Zlength b - 1) b)).
      { apply (keep1_to_keep0__dp_body_branches_k5 values d); [exact Hpeel |].
        intros p Hp. specialize (Hpelem p Hp). lia. }
      pose proof (Hdp j ltac:(lia)) as Hbj.
      destruct Hbj as [a0 [[Ha0in Ha0max] Ha0len]].
      assert (Hmemb : Keep0List values (sublist 0 (Zlength b - 1) b) /\
                      0 < Zlength (sublist 0 (Zlength b - 1) b) /\
                      Znth (Zlength (sublist 0 (Zlength b - 1) b) - 1)
                           (sublist 0 (Zlength b - 1) b) 0 = j)
        by (split; [exact Hk0 | split; [lia | exact Hplast]]).
      pose proof (Ha0max _ Hmemb) as Hle. cbv beta in Hle.
      assert (Hkj : KeyAt values j <= KeyAt values i + 1).
      { rewrite (keyshift_lt__dp_body_branches_k5 values d j ltac:(lia)) in Hjkey.
        rewrite (keyshift_gt__dp_body_branches_k5 values d i ltac:(lia)) in Hjkey.
        lia. }
      pose proof (G2 j ltac:(lia) Hkj) as Hg2. lia.
    - exfalso. destruct Hjb as [_ Hne]. lia.
    - assert (Hbest : exists w, Best1EndingAt values j w).
      { apply (best1_exists__dp_body_branches_k5 values j
                 (sublist 0 (Zlength b - 1) b)).
        split; [exists d; split; [exact Hpeel | lia] |].
        split; [lia | exact Hplast]. }
      destruct Hbest as [w Hw].
      pose proof Hw as Hw'.
      destruct Hw' as [a0 [[Ha0in Ha0max] Ha0len]].
      assert (Hmemb : (exists dd, Keep1List values dd (sublist 0 (Zlength b - 1) b) /\
                                  dd < j) /\
                      0 < Zlength (sublist 0 (Zlength b - 1) b) /\
                      Znth (Zlength (sublist 0 (Zlength b - 1) b) - 1)
                           (sublist 0 (Zlength b - 1) b) 0 = j)
        by (split; [exists d; split; [exact Hpeel | lia] |
                    split; [lia | exact Hplast]]).
      pose proof (Ha0max _ Hmemb) as Hle. cbv beta in Hle.
      assert (Hkj : KeyAt values j <= KeyAt values i).
      { rewrite (keyshift_gt__dp_body_branches_k5 values d j ltac:(lia)) in Hjkey.
        rewrite (keyshift_gt__dp_body_branches_k5 values d i ltac:(lia)) in Hjkey.
        lia. }
      pose proof (G1 j w ltac:(lia) Hw Hkj) as Hg1. lia. }
  unfold Best1EndingAt, max_value_of_subset, max_object_of_subset.
  destruct (Z.le_gt_cases (Z.max vs vc) 0) as [Hm0 | Hmpos].
  - assert (Hin : (exists dd, Keep1List values dd [i] /\ dd < i) /\
                  0 < Zlength [i] /\ Znth (Zlength [i] - 1) [i] 0 = i).
    { split.
      - exists (i - 1). split; [| lia].
        split; [lia | split; [| split]].
        + intros p q Hp Hpq Hq. rewrite Zlength_cons, Zlength_nil in Hq. lia.
        + intros p Hp. rewrite Zlength_cons, Zlength_nil in Hp.
          assert (p = 0) by lia. subst p. rewrite Znth0_cons. split; lia.
        + intros p q Hp Hpq Hq. rewrite Zlength_cons, Zlength_nil in Hq. lia.
      - split.
        + rewrite Zlength_cons, Zlength_nil. lia.
        + rewrite Zlength_cons, Zlength_nil.
          replace (0 + 1 - 1) with 0 by lia. apply Znth0_cons. }
    replace (Z.max 0 (Z.max vs vc) + 1) with 1 by lia.
    exists [i]. split; [split |].
    + exact Hin.
    + intros b Hb. cbv beta. pose proof (UB b Hb) as Hub.
      rewrite Zlength_cons, Zlength_nil. lia.
    + cbv beta. rewrite Zlength_cons, Zlength_nil. lia.
  - destruct (Z.le_ge_cases vc vs) as [Hcs | Hsc].
    + destruct (G3 ltac:(lia)) as [j [w [Hj [Hbj [Hwvs Hkj]]]]].
      pose proof Hbj as Hbj'.
      destruct Hbj' as [sj [[Hsjin Hsjmax] Hsjlen]].
      destruct Hsjin as [[d [Hkd Hdj]] [Hsjpos Hsjlast]].
      assert (Hsjle : forall p, 0 <= p < Zlength sj -> Znth p sj 0 <= j).
      { intros p Hp. rewrite <- Hsjlast.
        apply mono_inc_le_last__dp_body_branches_k5;
          [exact (proj1 (proj2 Hkd)) | lia | lia]. }
      assert (Hsjkey : forall p, 0 <= p < Zlength sj ->
                         KeyShift values d (Znth p sj 0) <= KeyShift values d i).
      { intros p Hp.
        assert (Hstep : KeyShift values d (Znth p sj 0) <= KeyShift values d j).
        { destruct (Z.eq_dec p (Zlength sj - 1)) as [-> | Hne].
          - rewrite Hsjlast. lia.
          - pose proof (proj2 (proj2 (proj2 Hkd)) p (Zlength sj - 1) ltac:(lia)
                          ltac:(lia) ltac:(lia)) as Hk4.
            rewrite Hsjlast in Hk4. lia. }
        rewrite (keyshift_gt__dp_body_branches_k5 values d j Hdj) in Hstep.
        rewrite (keyshift_gt__dp_body_branches_k5 values d i ltac:(lia)).
        lia. }
      assert (Hsnoc : Keep1List values d (sj ++ [i])).
      { apply keep1_snoc__dp_body_branches_k5.
        - exact Hkd.
        - lia.
        - lia.
        - intros p Hp. specialize (Hsjle p Hp). lia.
        - exact Hsjkey. }
      assert (Hin : (exists dd, Keep1List values dd (sj ++ [i]) /\ dd < i) /\
                    0 < Zlength (sj ++ [i]) /\
                    Znth (Zlength (sj ++ [i]) - 1) (sj ++ [i]) 0 = i).
      { split; [exists d; split; [exact Hsnoc | lia] | split].
        - rewrite Zlength_snoc__dp_body_branches_k5. lia.
        - rewrite Zlength_snoc__dp_body_branches_k5.
          replace (Zlength sj + 1 - 1) with (Zlength sj) by lia.
          apply Znth_app_last__dp_body_branches_k5. }
      replace (Z.max 0 (Z.max vs vc) + 1) with (Zlength sj + 1) by lia.
      exists (sj ++ [i]). split; [split |].
      * exact Hin.
      * intros b Hb. cbv beta. rewrite Zlength_snoc__dp_body_branches_k5.
        pose proof (UB b Hb) as Hub. lia.
      * cbv beta. apply Zlength_snoc__dp_body_branches_k5.
    + destruct (G4 ltac:(lia)) as [j [Hj [Hjval Hkj]]].
      pose proof (Hdp j ltac:(lia)) as Hbj.
      destruct Hbj as [sj [[Hsjin Hsjmax] Hsjlen]].
      destruct Hsjin as [Hsjk [Hsjpos Hsjlast]].
      assert (Hsjle : forall p, 0 <= p < Zlength sj -> Znth p sj 0 <= j).
      { intros p Hp. rewrite <- Hsjlast.
        apply mono_inc_le_last__dp_body_branches_k5;
          [exact (proj1 Hsjk) | lia | lia]. }
      assert (Hkd : Keep1List values (j + 1) sj).
      { apply (keep0_to_keep1__dp_body_branches_k5 values (j + 1) sj Hsjk);
          [lia | intros p Hp; specialize (Hsjle p Hp); lia]. }
      assert (Hsjkey : forall p, 0 <= p < Zlength sj ->
                         KeyShift values (j + 1) (Znth p sj 0) <=
                         KeyShift values (j + 1) i).
      { intros p Hp.
        assert (Hple : Znth p sj 0 <= j) by (apply Hsjle; lia).
        rewrite (keyshift_lt__dp_body_branches_k5 values (j + 1) (Znth p sj 0)
                   ltac:(lia)).
        rewrite (keyshift_gt__dp_body_branches_k5 values (j + 1) i ltac:(lia)).
        assert (Hstep : KeyAt values (Znth p sj 0) <= KeyAt values j).
        { destruct (Z.eq_dec p (Zlength sj - 1)) as [-> | Hne].
          - rewrite Hsjlast. lia.
          - pose proof (proj2 (proj2 Hsjk) p (Zlength sj - 1) ltac:(lia)
                          ltac:(lia) ltac:(lia)) as Hk3.
            rewrite Hsjlast in Hk3. lia. }
        lia. }
      assert (Hsnoc : Keep1List values (j + 1) (sj ++ [i])).
      { apply keep1_snoc__dp_body_branches_k5.
        - exact Hkd.
        - lia.
        - lia.
        - intros p Hp. specialize (Hsjle p Hp). lia.
        - exact Hsjkey. }
      assert (Hin : (exists dd, Keep1List values dd (sj ++ [i]) /\ dd < i) /\
                    0 < Zlength (sj ++ [i]) /\
                    Znth (Zlength (sj ++ [i]) - 1) (sj ++ [i]) 0 = i).
      { split; [exists (j + 1); split; [exact Hsnoc | lia] | split].
        - rewrite Zlength_snoc__dp_body_branches_k5. lia.
        - rewrite Zlength_snoc__dp_body_branches_k5.
          replace (Zlength sj + 1 - 1) with (Zlength sj) by lia.
          apply Znth_app_last__dp_body_branches_k5. }
      replace (Z.max 0 (Z.max vs vc) + 1) with (Zlength sj + 1) by lia.
      exists (sj ++ [i]). split; [split |].
      * exact Hin.
      * intros b Hb. cbv beta. rewrite Zlength_snoc__dp_body_branches_k5.
        pose proof (UB b Hb) as Hub. lia.
      * cbv beta. apply Zlength_snoc__dp_body_branches_k5.
Qed.

(* ---- assembling one loop-body step ---- *)
Lemma best0_bounds__dp_body_branches_k5 :
  forall a i v, Best0EndingAt a i v -> 1 <= v <= i + 1.
Proof.
  intros a i v Hb. destruct Hb as [s [[Hin _] Hlen]]. cbv beta in Hlen.
  destruct Hin as [Hk [Hpos Hlast]]. subst v. split; [lia |].
  apply (keep_last_len_bound__dp_body_branches_k5 s i (proj1 Hk) Hpos);
    [| exact Hlast].
  intros p Hp. pose proof (proj1 (proj2 Hk) p Hp) as HH. lia.
Qed.
Lemma best1_bounds__dp_body_branches_k5 :
  forall a i v, Best1EndingAt a i v -> 1 <= v <= i + 1.
Proof.
  intros a i v Hb. destruct Hb as [s [[Hin _] Hlen]]. cbv beta in Hlen.
  destruct Hin as [[d [Hk Hd]] [Hpos Hlast]]. subst v. split; [lia |].
  apply (keep_last_len_bound__dp_body_branches_k5 s i (proj1 (proj2 Hk)) Hpos);
    [| exact Hlast].
  intros p Hp. pose proof (proj1 (proj2 (proj2 Hk)) p Hp) as HH. lia.
Qed.
Lemma dp_step_core__dp_body_branches_k5 :
  forall values vals c_l dp0 m0 m1 mX uniq i r0 r1 rX prev0 vs vc d0 d1 dp0',
    1 <= i < Zlength values ->
    Zlength dp0 = Zlength values ->
    CompressedKeys values vals uniq ->
    KeyPrefix values c_l (Zlength values) ->
    DP0Prefix values dp0 i ->
    Bit0Model values vals dp0 m0 i uniq ->
    Bit1Model values vals m1 i uniq ->
    Bit0Model values vals dp0 mX (i - 1) uniq ->
    RankResult vals uniq (Znth i c_l 0) r0 ->
    RankResult vals uniq (Znth i c_l 0 + 1) r1 ->
    RankResult vals uniq (Znth (i - 1) c_l 0) rX ->
    1 <= r0 <= uniq -> 1 <= r1 <= uniq -> 1 <= rX <= uniq ->
    prev0 = RangeMax m0 1 (r0 + 1) ->
    vs = RangeMax m1 1 (r1 + 1) ->
    vc = RangeMax mX 1 (r1 + 1) ->
    d0 = Z.max prev0 0 + 1 ->
    d1 = Z.max 0 (Z.max vs vc) + 1 ->
    dp0' = replace_Znth i d0 dp0 ->
    Best0EndingAt values i d0 /\
    Best1EndingAt values i d1 /\
    1 <= d0 <= i + 1 /\
    1 <= d1 <= i + 1 /\
    Znth i dp0' 0 = d0 /\
    (forall j, 0 <= j < i -> Znth j dp0' 0 = Znth j dp0 0) /\
    Zlength dp0' = Zlength values /\
    DP0Prefix values dp0' (i + 1) /\
    Bit0Model values vals dp0' (MaxBitInsert m0 r0 d0) (i + 1) uniq /\
    Bit1Model values vals (MaxBitInsert m1 r1 d1) (i + 1) uniq /\
    Bit0Model values vals dp0' (MaxBitInsert mX rX (Znth (i - 1) dp0' 0)) i uniq.
Proof.
  intros values vals c_l dp0 m0 m1 mX uniq i r0 r1 rX prev0 vs vc d0 d1 dp0'
         Hi Hdplen Hck Hkp Hdp Hbit0 Hbit1 HbitX Hr0 Hr1 HrX Hr0b Hr1b HrXb
         Hprev Hvs Hvc Hd0 Hd1 Hdp0'.
  assert (Hci : Znth i c_l 0 = KeyAt values i) by (apply Hkp; lia).
  assert (HciX : Znth (i - 1) c_l 0 = KeyAt values (i - 1)) by (apply Hkp; lia).
  rewrite Hci in Hr0, Hr1. rewrite HciX in HrX.
  destruct Hck as [Hsi [Hmem _]].
  assert (Hbest0 : Best0EndingAt values i d0).
  { subst d0. apply (best0_step__dp_body_branches_k5 values vals dp0 m0 uniq i r0);
      try assumption; try lia.
    intros j Hj. exact (proj1 (Hmem j Hj)). }
  assert (Hbest1 : Best1EndingAt values i d1).
  { subst d1.
    apply (best1_step__dp_body_branches_k5 values vals dp0 m1 mX uniq i r1);
      try assumption; try lia. }
  pose proof (best0_bounds__dp_body_branches_k5 _ _ _ Hbest0) as Hd0b.
  pose proof (best1_bounds__dp_body_branches_k5 _ _ _ Hbest1) as Hd1b.
  assert (Hnew : Znth i dp0' 0 = d0)
    by (subst dp0'; apply Znth_replace_Znth_Same; lia).
  assert (Hagree : forall j, 0 <= j < i -> Znth j dp0' 0 = Znth j dp0 0)
    by (intros j Hj; subst dp0'; apply Znth_replace_Znth_Diff; lia).
  assert (Hlen' : Zlength dp0' = Zlength values)
    by (subst dp0'; rewrite Zlength_replace_Znth__dp_body_branches_k5; exact Hdplen).
  assert (Hdp' : DP0Prefix values dp0' (i + 1)).
  { intros j Hj. destruct (Z.eq_dec j i) as [-> | Hne].
    - rewrite Hnew. exact Hbest0.
    - rewrite Hagree by lia. apply Hdp; lia. }
  assert (Hbit0c : Bit0Model values vals dp0' m0 i uniq).
  { apply (bit0_model_dp_congr__dp_body_branches_k5 values vals dp0 dp0' m0 i uniq
             Hbit0). intros j Hj. apply Hagree; lia. }
  assert (Hbit0' : Bit0Model values vals dp0' (MaxBitInsert m0 r0 d0) (i + 1) uniq).
  { apply (bit0_model_insert__dp_body_branches_k5 values vals dp0'
             m0 i uniq r0 d0 Hbit0c ltac:(lia) Hr0 Hr0b). exact Hnew. }
  assert (Hbit1' : Bit1Model values vals (MaxBitInsert m1 r1 d1) (i + 1) uniq).
  { apply (bit1_model_insert__dp_body_branches_k5 values vals m1 i uniq r1 d1
             Hbit1 ltac:(lia) Hr1 Hr1b Hbest1). }
  assert (HbitXc : Bit0Model values vals dp0' mX (i - 1) uniq).
  { apply (bit0_model_dp_congr__dp_body_branches_k5 values vals dp0 dp0' mX
             (i - 1) uniq HbitX). intros j Hj. apply Hagree; lia. }
  assert (HbitX0 : Bit0Model values vals dp0'
                     (MaxBitInsert mX rX (Znth (i - 1) dp0' 0)) (i - 1 + 1) uniq).
  { apply (bit0_model_insert__dp_body_branches_k5 values vals dp0'
             mX (i - 1) uniq rX (Znth (i - 1) dp0' 0) HbitXc ltac:(lia) HrX HrXb).
    reflexivity. }
  assert (Hii : i - 1 + 1 = i) by lia.
  rewrite Hii in HbitX0.
  assert (HbitX' : Bit0Model values vals dp0'
                     (MaxBitInsert mX rX (Znth (i - 1) dp0' 0)) i uniq)
    by exact HbitX0.
  split; [exact Hbest0 |].
  split; [exact Hbest1 |].
  split; [lia |].
  split; [lia |].
  split; [exact Hnew |].
  split; [exact Hagree |].
  split; [exact Hlen' |].
  split; [exact Hdp' |].
  split; [exact Hbit0' |].
  split; [exact Hbit1' |].
  exact HbitX'.
Qed.
Lemma maxbitinsert_bounds__dp_body_branches_k5 :
  forall m r v t lo hi,
    0 <= r < Zlength m -> 0 <= t < Zlength m ->
    lo <= Znth t m 0 <= hi -> lo <= v <= hi ->
    lo <= Znth t (MaxBitInsert m r v) 0 <= hi.
Proof.
  intros m r v t lo hi Hr Ht Hm Hv.
  destruct (Z.eq_dec t r) as [-> | Hne].
  - rewrite maxbitinsert_same__dp_body_branches_k5 by lia. lia.
  - rewrite maxbitinsert_diff__dp_body_branches_k5 by lia. lia.
Qed.
Lemma fold_max_ub__dp_body_branches_k6 :
  forall (l : list Z) (B : Z),
    MaxBitNeg <= B ->
    (forall x, In x l -> x <= B) ->
    fold_right Z.max MaxBitNeg l <= B.
Proof.
  induction l as [| a l IH]; intros B HB Hall; simpl.
  - exact HB.
  - apply Z.max_lub.
    + apply Hall. left. reflexivity.
    + apply IH; auto. intros x Hx. apply Hall. right. exact Hx.
Qed.
Lemma fold_max_lb__dp_body_branches_k6 :
  forall (l : list Z) (x : Z), In x l -> x <= fold_right Z.max MaxBitNeg l.
Proof.
  induction l as [| a l IH]; intros x Hx; simpl in *.
  - contradiction.
  - destruct Hx as [Hx | Hx].
    + subst a. apply Z.le_max_l.
    + eapply Z.le_trans; [apply IH; exact Hx | apply Z.le_max_r].
Qed.
Lemma fold_max_attained__dp_body_branches_k6 :
  forall (l : list Z),
    fold_right Z.max MaxBitNeg l = MaxBitNeg \/ In (fold_right Z.max MaxBitNeg l) l.
Proof.
  induction l as [| a l IH]; simpl.
  - left; reflexivity.
  - destruct (Z.le_ge_cases a (fold_right Z.max MaxBitNeg l)) as [Hle | Hge].
    + rewrite (Z.max_r _ _ Hle).
      destruct IH as [H | H]; [left; exact H | right; right; exact H].
    + rewrite (Z.max_l _ _ Hge). right; left; reflexivity.
Qed.
Lemma rangemax_ub__dp_body_branches_k6 :
  forall m lo hi B,
    MaxBitNeg <= B ->
    (forall q, lo <= q < hi -> Znth q m 0 <= B) ->
    RangeMax m lo hi <= B.
Proof.
  intros m lo hi B HB Hall. unfold RangeMax.
  apply fold_max_ub__dp_body_branches_k6; [exact HB |].
  intros x Hx. apply in_map_iff in Hx. destruct Hx as [q [Heq Hin]].
  subst x. apply Hall. apply (proj2 (In_Zrange lo hi q)). exact Hin.
Qed.
Lemma rangemax_lb__dp_body_branches_k6 :
  forall m lo hi q, lo <= q < hi -> Znth q m 0 <= RangeMax m lo hi.
Proof.
  intros m lo hi q Hq. unfold RangeMax.
  apply fold_max_lb__dp_body_branches_k6.
  apply in_map_iff. exists q. split; [reflexivity |].
  apply (proj1 (In_Zrange lo hi q)). exact Hq.
Qed.
Lemma rangemax_prefix_char__dp_body_branches_k6 :
  forall m lo hi,
    RangeMax m lo hi = MaxBitNeg \/
    exists q, lo <= q < hi /\ RangeMax m lo hi = Znth q m 0.
Proof.
  intros m lo hi. unfold RangeMax.
  destruct (fold_max_attained__dp_body_branches_k6
              (map (fun r => Znth r m 0) (Zrange lo hi))) as [H | H].
  - left; exact H.
  - right. apply in_map_iff in H. destruct H as [q [Heq Hin]].
    exists q. split.
    + apply (proj2 (In_Zrange lo hi q)). exact Hin.
    + symmetry. exact Heq.
Qed.
Lemma bit0_model_empty__dp_body_branches_k6 :
  forall a vals dp m k uniq,
    Bit0Model a vals dp m k uniq -> k <= 0 ->
    forall r, 1 <= r <= uniq -> Znth r m 0 = MaxBitNeg.
Proof.
  intros a vals dp m k uniq [Hlen HM] Hk r Hr.
  destruct (HM r Hr) as [_ [H | [j [Hj _]]]].
  - exact H.
  - lia.
Qed.
Lemma bit0_query_empty__dp_body_branches_k6 :
  forall a vals dp m k uniq r,
    Bit0Model a vals dp m k uniq -> k <= 0 -> r <= uniq ->
    RangeMax m 1 (r + 1) <= MaxBitNeg.
Proof.
  intros a vals dp m k uniq r HM Hk Hr.
  apply rangemax_ub__dp_body_branches_k6; [lia |].
  intros q Hq.
  rewrite (bit0_model_empty__dp_body_branches_k6 a vals dp m k uniq HM Hk q ltac:(lia)).
  lia.
Qed.
Lemma Znth_app1__dp_body_branches_k6 : forall (A : Type) (d : A) (l1 l2 : list A) (p : Z),
  0 <= p < Zlength l1 -> Znth p (l1 ++ l2) d = Znth p l1 d.
Proof.
  intros A d l1 l2 p H. unfold Znth. rewrite Zlength_correct in H.
  apply app_nth1. lia.
Qed.
Lemma Znth_app2__dp_body_branches_k6 : forall (A : Type) (d : A) (l1 l2 : list A) (p : Z),
  Zlength l1 <= p -> Znth p (l1 ++ l2) d = Znth (p - Zlength l1) l2 d.
Proof.
  intros A d l1 l2 p H. unfold Znth. rewrite Zlength_correct in *.
  rewrite app_nth2 by lia. f_equal. lia.
Qed.
Lemma rank_mono__dp_body_branches_k6 :
  forall vals uniq x rx y ry,
    StrictIncPrefix vals uniq ->
    RankResult vals uniq x rx ->
    RankResult vals uniq y ry ->
    rx < ry -> x < y.
Proof.
  intros vals uniq x rx y ry HS [Hbx [Hx _]] [Hby [Hy _]] Hlt.
  subst x y. apply HS; lia.
Qed.
Lemma rank_order_iso__dp_body_branches_k6 :
  forall vals uniq x rx y ry,
    StrictIncPrefix vals uniq ->
    RankResult vals uniq x rx ->
    RankResult vals uniq y ry ->
    (x <= y <-> rx <= ry).
Proof.
  intros vals uniq x rx y ry HS Hx Hy. split; intros H.
  - destruct (Z.le_gt_cases rx ry) as [Hle | Hgt]; [exact Hle |].
    pose proof (rank_mono__dp_body_branches_k6 vals uniq y ry x rx HS Hy Hx ltac:(lia)). lia.
  - destruct (Z.eq_dec rx ry) as [He | Hne].
    + subst ry. destruct Hx as [_ [Hx1 _]]. destruct Hy as [_ [Hy1 _]]. lia.
    + pose proof (rank_mono__dp_body_branches_k6 vals uniq x rx y ry HS Hx Hy ltac:(lia)). lia.
Qed.
Lemma rank_exists__dp_body_branches_k6 :
  forall vals uniq v,
    StrictIncPrefix vals uniq ->
    MemberPrefix vals uniq v ->
    exists r, RankResult vals uniq v r.
Proof.
  intros vals uniq v HS [k [Hk Hv]].
  exists (k + 1). unfold RankResult. split; [lia | split].
  - replace (k + 1 - 1) with k by lia. exact Hv.
  - intros k' Hk'. rewrite <- Hv. apply HS; lia.
Qed.
Lemma keep0_sublist__dp_body_branches_k6 :
  forall a s k,
    Keep0List a s -> 0 <= k <= Zlength s ->
    Keep0List a (sublist 0 k s).
Proof.
  intros a s k [Hmono [Hbnd Hkey]] Hk.
  assert (Hlen : Zlength (sublist 0 k s) = k) by (apply Zlength_sublist0; lia).
  unfold Keep0List. split; [| split].
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    rewrite !Znth_sublist0 by lia. apply Hmono; lia.
  - intros p Hp. rewrite Hlen in Hp.
    rewrite Znth_sublist0 by lia. apply Hbnd; lia.
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    rewrite !Znth_sublist0 by lia. apply Hkey; lia.
Qed.
Lemma best0_upper__dp_body_branches_k6 :
  forall a vals dp m i uniq r0 s,
    0 <= i ->
    CompressedKeys a vals uniq ->
    DP0Prefix a dp i ->
    Bit0Model a vals dp m i uniq ->
    RankResult vals uniq (KeyAt a i) r0 ->
    Keep0List a s ->
    0 < Zlength s ->
    Znth (Zlength s - 1) s 0 = i ->
    Zlength s <= Z.max (RangeMax m 1 (r0 + 1)) 0 + 1.
Proof.
  intros a vals dp m i uniq r0 s Hi HC HDP HB Hr0 HK Hpos Hlast.
  destruct HC as [HS [Hmem _]].
  remember (Zlength s) as L eqn:HL.
  destruct (Z.le_gt_cases L 1) as [Hsmall | Hbig]; [lia |].
  assert (HKcopy : Keep0List a s) by exact HK.
  destruct HK as [Hmono [Hbnd Hkey]].
  assert (Hjlt : Znth (L - 2) s 0 < i).
  { rewrite <- Hlast. apply Hmono; lia. }
  assert (Hjb : 0 <= Znth (L - 2) s 0 < Zlength a) by (apply Hbnd; lia).
  pose proof (keep0_sublist__dp_body_branches_k6 a s (L - 1) HKcopy ltac:(lia)) as HKp.
  assert (Hplen : Zlength (sublist 0 (L - 1) s) = L - 1)
    by (apply Zlength_sublist0; lia).
  assert (Hplast : Znth (Zlength (sublist 0 (L - 1) s) - 1) (sublist 0 (L - 1) s) 0
                   = Znth (L - 2) s 0).
  { rewrite Hplen. rewrite Znth_sublist0 by lia. f_equal. lia. }
  pose proof (HDP (Znth (L - 2) s 0) ltac:(lia)) as Hbest.
  unfold Best0EndingAt, max_value_of_subset, max_object_of_subset in Hbest.
  destruct Hbest as [w [[Hwin Hwmax] Hweq]].
  assert (Hin : Keep0List a (sublist 0 (L - 1) s) /\
                0 < Zlength (sublist 0 (L - 1) s) /\
                Znth (Zlength (sublist 0 (L - 1) s) - 1) (sublist 0 (L - 1) s) 0
                = Znth (L - 2) s 0).
  { split; [exact HKp | split; [lia | exact Hplast]]. }
  pose proof (Hwmax _ Hin) as Hle.
  rewrite Hplen in Hle.
  destruct (rank_exists__dp_body_branches_k6 vals uniq (KeyAt a (Znth (L - 2) s 0))
              HS (proj1 (Hmem _ Hjb))) as [rj Hrj].
  assert (Hkeyle : KeyAt a (Znth (L - 2) s 0) <= KeyAt a i).
  { rewrite <- Hlast. apply Hkey; lia. }
  assert (Hrjle : rj <= r0).
  { apply (proj1 (rank_order_iso__dp_body_branches_k6 vals uniq
                    (KeyAt a (Znth (L - 2) s 0)) rj (KeyAt a i) r0 HS Hrj Hr0)).
    exact Hkeyle. }
  assert (Hrjb : 1 <= rj <= uniq) by (destruct Hrj as [HH _]; exact HH).
  destruct HB as [Hmlen HBm].
  pose proof (proj1 (HBm rj Hrjb) (Znth (L - 2) s 0) ltac:(lia) Hrj) as Hdom.
  pose proof (rangemax_lb__dp_body_branches_k6 m 1 (r0 + 1) rj ltac:(lia)) as Hlb.
  lia.
Qed.
Lemma best0_step__dp_body_branches_k6 :
  forall a vals dp m i uniq r0,
    0 <= i < Zlength a ->
    CompressedKeys a vals uniq ->
    DP0Prefix a dp i ->
    Bit0Model a vals dp m i uniq ->
    RankResult vals uniq (KeyAt a i) r0 ->
    Best0EndingAt a i (Z.max (RangeMax m 1 (r0 + 1)) 0 + 1).
Proof.
  intros a vals dp m i uniq r0 Hi HC HDP HB Hr0.
  assert (HCc := HC). destruct HCc as [HS [Hmem _]].
  assert (HBc := HB). destruct HBc as [Hmlen HBm].
  unfold Best0EndingAt, max_value_of_subset, max_object_of_subset.
  destruct (Z.le_gt_cases (RangeMax m 1 (r0 + 1)) 0) as [Hneg | Hpos].
  - exists (i :: nil).
    assert (Hlen1 : Zlength (i :: nil) = 1)
      by (rewrite Zlength_cons, Zlength_nil; lia).
    assert (Hnth0 : Znth 0 (i :: nil) 0 = i) by (unfold Znth; simpl; reflexivity).
    assert (HK : Keep0List a (i :: nil)).
    { unfold Keep0List. split; [| split].
      - intros p q Hp Hpq Hq. rewrite Hlen1 in Hq. lia.
      - intros p Hp. rewrite Hlen1 in Hp.
        replace p with 0 by lia. rewrite Hnth0. lia.
      - intros p q Hp Hpq Hq. rewrite Hlen1 in Hq. lia. }
    split; [split |].
    + split; [exact HK | split; [lia |]].
      rewrite Hlen1. replace (1 - 1) with 0 by lia. exact Hnth0.
    + intros b Hb. destruct Hb as [HKb [Hposb Hlastb]].
      pose proof (best0_upper__dp_body_branches_k6 a vals dp m i uniq r0 b
                    ltac:(lia) HC HDP HB Hr0 HKb Hposb Hlastb) as Hub.
      rewrite Hlen1. lia.
    + rewrite Hlen1. lia.
  - destruct (rangemax_prefix_char__dp_body_branches_k6 m 1 (r0 + 1))
      as [Hmn | [q [Hq Heq]]].
    { rewrite Hmn in Hpos. unfold MaxBitNeg in Hpos. lia. }
    assert (Hr0b : 1 <= r0 <= uniq) by (destruct Hr0 as [HH _]; exact HH).
    assert (Hrq : 1 <= q <= uniq) by lia.
    destruct (proj2 (HBm q Hrq)) as [Hnegq | [j [Hj [Hrj Hdpj]]]].
    { rewrite Heq, Hnegq in Hpos. unfold MaxBitNeg in Hpos. lia. }
    pose proof (HDP j ltac:(lia)) as Hbest.
    unfold Best0EndingAt, max_value_of_subset, max_object_of_subset in Hbest.
    destruct Hbest as [s0 [[Hs0in Hs0max] Hs0eq]].
    destruct Hs0in as [HK0 [Hpos0 Hlast0]].
    assert (HlenS0 : Zlength s0 = RangeMax m 1 (r0 + 1)).
    { rewrite Hs0eq. rewrite <- Hdpj. rewrite <- Heq. reflexivity. }
    assert (HK0c := HK0). destruct HK0c as [Hm0 [Hb0 Hk0]].
    assert (Hle_j : forall p, 0 <= p < Zlength s0 -> Znth p s0 0 <= j).
    { intros p Hp. destruct (Z.eq_dec p (Zlength s0 - 1)) as [He | Hne].
      - subst p. lia.
      - assert (Hlt : Znth p s0 0 < Znth (Zlength s0 - 1) s0 0) by (apply Hm0; lia).
        lia. }
    assert (Hkey_j : forall p, 0 <= p < Zlength s0 ->
                     KeyAt a (Znth p s0 0) <= KeyAt a j).
    { intros p Hp. destruct (Z.eq_dec p (Zlength s0 - 1)) as [He | Hne].
      - subst p. rewrite Hlast0. lia.
      - assert (Hlt : KeyAt a (Znth p s0 0) <= KeyAt a (Znth (Zlength s0 - 1) s0 0))
          by (apply Hk0; lia).
        rewrite Hlast0 in Hlt. lia. }
    assert (Hji : KeyAt a j <= KeyAt a i).
    { apply (proj2 (rank_order_iso__dp_body_branches_k6 vals uniq
                      (KeyAt a j) q (KeyAt a i) r0 HS Hrj Hr0)). lia. }
    assert (Hlen : Zlength (s0 ++ (i :: nil)) = Zlength s0 + 1).
    { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
    assert (Hnth_lt : forall p, 0 <= p < Zlength s0 ->
                      Znth p (s0 ++ (i :: nil)) 0 = Znth p s0 0).
    { intros p Hp. apply Znth_app1__dp_body_branches_k6. lia. }
    assert (Hnth_last : Znth (Zlength s0) (s0 ++ (i :: nil)) 0 = i).
    { rewrite Znth_app2__dp_body_branches_k6 by lia.
      replace (Zlength s0 - Zlength s0) with 0 by lia.
      unfold Znth; simpl; reflexivity. }
    assert (HKnew : Keep0List a (s0 ++ (i :: nil))).
    { unfold Keep0List. split; [| split].
      - intros p q' Hp Hpq Hq'. rewrite Hlen in Hq'.
        destruct (Z.eq_dec q' (Zlength s0)) as [He' | Hne'].
        + subst q'. rewrite Hnth_last. rewrite Hnth_lt by lia.
          assert (Hlej : Znth p s0 0 <= j) by (apply Hle_j; lia). lia.
        + rewrite !Hnth_lt by lia. apply Hm0; lia.
      - intros p Hp. rewrite Hlen in Hp.
        destruct (Z.eq_dec p (Zlength s0)) as [He' | Hne'].
        + subst p. rewrite Hnth_last. lia.
        + rewrite Hnth_lt by lia. apply Hb0; lia.
      - intros p q' Hp Hpq Hq'. rewrite Hlen in Hq'.
        destruct (Z.eq_dec q' (Zlength s0)) as [He' | Hne'].
        + subst q'. rewrite Hnth_last. rewrite Hnth_lt by lia.
          assert (Hkj : KeyAt a (Znth p s0 0) <= KeyAt a j) by (apply Hkey_j; lia).
          lia.
        + rewrite !Hnth_lt by lia. apply Hk0; lia. }
    exists (s0 ++ (i :: nil)).
    split; [split |].
    + split; [exact HKnew | split; [lia |]].
      rewrite Hlen. replace (Zlength s0 + 1 - 1) with (Zlength s0) by lia.
      exact Hnth_last.
    + intros b Hb. destruct Hb as [HKb [Hposb Hlastb]].
      pose proof (best0_upper__dp_body_branches_k6 a vals dp m i uniq r0 b
                    ltac:(lia) HC HDP HB Hr0 HKb Hposb Hlastb) as Hub.
      rewrite Hlen. lia.
    + rewrite Hlen. lia.
Qed.
Lemma mono_inc_index_lb__dp_body_branches_k6 :
  forall s, mono_inc s ->
    (forall p, 0 <= p < Zlength s -> 0 <= Znth p s 0) ->
    forall p, 0 <= p < Zlength s -> p <= Znth p s 0.
Proof.
  intros s Hm Hb p.
  remember (Z.to_nat p) as n eqn:Hn.
  revert p Hn.
  induction n as [| n IH]; intros p Hn Hp.
  - replace p with 0 by lia. apply Hb. lia.
  - assert (Hlt : Znth (p - 1) s 0 < Znth p s 0) by (apply Hm; lia).
    specialize (IH (p - 1) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma best0_unique__dp_body_branches_k6 :
  forall a i v w, Best0EndingAt a i v -> Best0EndingAt a i w -> v = w.
Proof.
  intros a i v w [s [[Hs Hsm] Hse]] [t [[Ht Htm] Hte]].
  pose proof (Hsm t Ht). pose proof (Htm s Hs). lia.
Qed.
Lemma best1_unique__dp_body_branches_k6 :
  forall a i v w, Best1EndingAt a i v -> Best1EndingAt a i w -> v = w.
Proof.
  intros a i v w [s [[Hs Hsm] Hse]] [t [[Ht Htm] Hte]].
  pose proof (Hsm t Ht). pose proof (Htm s Hs). lia.
Qed.
Lemma best0_bounds__dp_body_branches_k6 :
  forall a i v, Best0EndingAt a i v -> 0 <= i -> 1 <= v <= i + 1.
Proof.
  intros a i v [s [[[HK [Hpos Hlast]] Hmax] Heq]] Hi.
  assert (HKc := HK). destruct HKc as [Hm [Hb Hk]].
  assert (Hlb : Zlength s - 1 <= Znth (Zlength s - 1) s 0).
  { apply mono_inc_index_lb__dp_body_branches_k6; [exact Hm | | lia].
    intros p Hp. apply (proj1 (Hb p Hp)). }
  rewrite Hlast in Hlb. lia.
Qed.
Lemma best1_absurd_zero__dp_body_branches_k6 :
  forall a w, ~ Best1EndingAt a 0 w.
Proof.
  intros a w H. destruct H as [s [[Hin _] _]].
  destruct Hin as [[d [HK Hd]] _].
  destruct HK as [Hdb _]. lia.
Qed.
Lemma rank_unique__dp_body_branches_k6 :
  forall vals uniq v r1 r2,
    StrictIncPrefix vals uniq ->
    RankResult vals uniq v r1 -> RankResult vals uniq v r2 -> r1 = r2.
Proof.
  intros vals uniq v r1 r2 HS H1 H2.
  pose proof (proj1 (rank_order_iso__dp_body_branches_k6 vals uniq v r1 v r2 HS H1 H2)
                ltac:(lia)).
  pose proof (proj1 (rank_order_iso__dp_body_branches_k6 vals uniq v r2 v r1 HS H2 H1)
                ltac:(lia)).
  lia.
Qed.
Lemma Znth_maxbitinsert_same__dp_body_branches_k6 :
  forall m r v, 0 <= r < Zlength m ->
    Znth r (MaxBitInsert m r v) 0 = Z.max (Znth r m 0) v.
Proof.
  intros m r v H. unfold MaxBitInsert. apply Znth_replace_Znth_Same. exact H.
Qed.
Lemma Znth_maxbitinsert_diff__dp_body_branches_k6 :
  forall m r v q, 0 <= r < Zlength m -> 0 <= q < Zlength m -> r <> q ->
    Znth q (MaxBitInsert m r v) 0 = Znth q m 0.
Proof.
  intros m r v q H1 H2 H3. unfold MaxBitInsert.
  apply Znth_replace_Znth_Diff; auto.
Qed.
Lemma replace_nth_length__dp_body_branches_k6 :
  forall (A : Type) (v : A) (l : list A) (k : nat),
    length (replace_nth k l v) = length l.
Proof.
  intros A v l. induction l as [| x l IH]; intros [| k]; simpl; try reflexivity.
  f_equal. apply IH.
Qed.
Lemma Zlength_maxbitinsert__dp_body_branches_k6 :
  forall m r v, Zlength (MaxBitInsert m r v) = Zlength m.
Proof.
  intros m r v. unfold MaxBitInsert, replace_Znth.
  rewrite !Zlength_correct. f_equal. apply replace_nth_length__dp_body_branches_k6.
Qed.
Lemma Znth_maxbitinsert_bound__dp_body_branches_k6 :
  forall m r v q B C,
    0 <= r < Zlength m -> 0 <= q < Zlength m ->
    (forall t, 0 <= t < Zlength m -> B <= Znth t m 0 <= C) ->
    B <= v -> v <= C ->
    B <= Znth q (MaxBitInsert m r v) 0 <= C.
Proof.
  intros m r v q B C Hr Hq Hall Hv1 Hv2.
  destruct (Z.eq_dec r q) as [He | Hne].
  - subst q. rewrite Znth_maxbitinsert_same__dp_body_branches_k6 by lia.
    pose proof (Hall r Hr). lia.
  - rewrite Znth_maxbitinsert_diff__dp_body_branches_k6 by lia. apply Hall; lia.
Qed.
Lemma bit0_model_insert__dp_body_branches_k6 :
  forall a vals dp dp' m i uniq r0 d0,
    0 <= i ->
    StrictIncPrefix vals uniq ->
    Bit0Model a vals dp m i uniq ->
    (forall j, 0 <= j < i -> Znth j dp' 0 = Znth j dp 0) ->
    Znth i dp' 0 = d0 ->
    RankResult vals uniq (KeyAt a i) r0 ->
    Bit0Model a vals dp' (MaxBitInsert m r0 d0) (i + 1) uniq.
Proof.
  intros a vals dp dp' m i uniq r0 d0 Hi HS [Hlen HM] Hext Hdi Hr0.
  assert (Hr0b : 1 <= r0 <= uniq) by (destruct Hr0 as [HH _]; exact HH).
  split.
  { rewrite Zlength_maxbitinsert__dp_body_branches_k6. exact Hlen. }
  intros r Hr.
  destruct (HM r Hr) as [Hdom Hw].
  split.
  - intros j Hj HRj.
    destruct (Z.eq_dec j i) as [He | Hne].
    + subst j.
      assert (r = r0) by
        (apply (rank_unique__dp_body_branches_k6 vals uniq (KeyAt a i)); assumption).
      subst r. rewrite Znth_maxbitinsert_same__dp_body_branches_k6 by lia.
      rewrite Hdi. lia.
    + rewrite Hext by lia.
      destruct (Z.eq_dec r r0) as [He2 | Hne2].
      * subst r. rewrite Znth_maxbitinsert_same__dp_body_branches_k6 by lia.
        pose proof (Hdom j ltac:(lia) HRj). lia.
      * rewrite Znth_maxbitinsert_diff__dp_body_branches_k6 by lia.
        apply Hdom; [lia | exact HRj].
  - destruct (Z.eq_dec r r0) as [He2 | Hne2].
    + subst r. rewrite Znth_maxbitinsert_same__dp_body_branches_k6 by lia.
      destruct (Z.le_gt_cases (Znth r0 m 0) d0) as [Hle | Hgt].
      * rewrite Z.max_r by lia. right. exists i.
        split; [lia | split; [exact Hr0 | rewrite Hdi; reflexivity]].
      * rewrite Z.max_l by lia.
        destruct Hw as [H | [j [Hj [HRj Hval]]]]; [left; exact H |].
        right. exists j. split; [lia | split; [exact HRj |]].
        rewrite Hext by lia. exact Hval.
    + rewrite Znth_maxbitinsert_diff__dp_body_branches_k6 by lia.
      destruct Hw as [H | [j [Hj [HRj Hval]]]]; [left; exact H |].
      right. exists j. split; [lia | split; [exact HRj |]].
      rewrite Hext by lia. exact Hval.
Qed.
Lemma bit0_model_neg__dp_body_branches_k6 :
  forall a vals dp dp' m k uniq,
    Bit0Model a vals dp m k uniq -> k <= 0 ->
    Bit0Model a vals dp' m 0 uniq.
Proof.
  intros a vals dp dp' m k uniq [Hlen HM] Hk.
  split; [exact Hlen |]. intros r Hr.
  destruct (HM r Hr) as [_ Hw].
  split.
  - intros j Hj HR. lia.
  - destruct Hw as [H | [j [Hj _]]]; [left; exact H | lia].
Qed.
Lemma bit1_model_step_zero__dp_body_branches_k6 :
  forall a vals m k uniq,
    Bit1Model a vals m k uniq -> k <= 0 -> Bit1Model a vals m 1 uniq.
Proof.
  intros a vals m k uniq [Hlen HM] Hk.
  split; [exact Hlen |]. intros r Hr.
  destruct (HM r Hr) as [_ Hw].
  split.
  - intros j w Hj HB HR. replace j with 0 in HB by lia.
    exfalso. apply (best1_absurd_zero__dp_body_branches_k6 a w). exact HB.
  - destruct Hw as [H | [j [w [Hj _]]]]; [left; exact H | lia].
Qed.
Lemma clamped_prefix_ext__dp_body_branches_k6 :
  forall l l' k v,
    ClampedPrefixMax l k v ->
    (forall j, 0 <= j < k -> Znth j l' 0 = Znth j l 0) ->
    ClampedPrefixMax l' k v.
Proof.
  intros l l' k v [Hv [Hall Hw]] Hext.
  split; [exact Hv | split].
  - intros j Hj. rewrite Hext by lia. apply Hall; lia.
  - destruct Hw as [H | [j [Hj Hj2]]]; [left; exact H |].
    right. exists j. split; [lia |]. rewrite Hext by lia. exact Hj2.
Qed.
Lemma clamped_prefix_neg__dp_body_branches_k6 :
  forall l l' k k' v,
    ClampedPrefixMax l k v -> k <= 0 -> k' <= 0 -> ClampedPrefixMax l' k' v.
Proof.
  intros l l' k k' v [Hv [_ Hw]] Hk Hk'.
  split; [exact Hv | split].
  - intros j Hj. lia.
  - destruct Hw as [H | [j [Hj _]]]; [left; exact H | lia].
Qed.
Lemma clamped_prefix_step_up__dp_body_branches_k6 :
  forall l k v x,
    ClampedPrefixMax l k v -> 0 <= k -> Znth k l 0 = x -> v <= x -> 0 <= x ->
    ClampedPrefixMax l (k + 1) x.
Proof.
  intros l k v x [Hv [Hall _]] Hk Hx Hvx Hx0.
  split; [exact Hx0 | split].
  - intros j Hj. destruct (Z.eq_dec j k) as [He | Hne].
    + subst j. lia.
    + pose proof (Hall j ltac:(lia)). lia.
  - right. exists k. split; [lia | exact Hx].
Qed.
Lemma clamped_prefix_step_keep__dp_body_branches_k6 :
  forall l k v x,
    ClampedPrefixMax l k v -> 0 <= k -> Znth k l 0 = x -> x <= v ->
    ClampedPrefixMax l (k + 1) v.
Proof.
  intros l k v x [Hv [Hall Hw]] Hk Hx Hxv.
  split; [exact Hv | split].
  - intros j Hj. destruct (Z.eq_dec j k) as [He | Hne].
    + subst j. lia.
    + apply Hall; lia.
  - destruct Hw as [H | [j [Hj Hj2]]]; [left; exact H |].
    right. exists j. split; [lia | exact Hj2].
Qed.
Lemma clamped_best1_zero_step__dp_body_branches_k6 :
  forall a v, ClampedBest1Upto a 0 v -> ClampedBest1Upto a 1 v.
Proof.
  intros a v [Hv [_ Hw]].
  split; [exact Hv | split].
  - intros j w Hj HB. replace j with 0 in HB by lia.
    exfalso. apply (best1_absurd_zero__dp_body_branches_k6 a w). exact HB.
  - destruct Hw as [H | [j [w [Hj _]]]]; [left; exact H | lia].
Qed.
Lemma clamped_best1_step_keep__dp_body_branches_k6 :
  forall a k v x,
    ClampedBest1Upto a k v -> 0 <= k -> Best1EndingAt a k x -> x <= v ->
    ClampedBest1Upto a (k + 1) v.
Proof.
  intros a k v x [Hv [Hall Hw]] Hk Hx Hxv.
  split; [exact Hv | split].
  - intros j w Hj HB. destruct (Z.eq_dec j k) as [He | Hne].
    + subst j.
      assert (w = x) by
        (apply (best1_unique__dp_body_branches_k6 a k); assumption).
      lia.
    + apply (Hall j w); [lia | exact HB].
  - destruct Hw as [H | [j [w [Hj [HB Hval]]]]]; [left; exact H |].
    right. exists j, w. split; [lia | split; [exact HB | exact Hval]].
Qed.
Lemma clamped_best1_step_up__dp_body_branches_k6 :
  forall a k v x,
    ClampedBest1Upto a k v -> 0 <= k -> Best1EndingAt a k x -> v <= x -> 0 <= x ->
    ClampedBest1Upto a (k + 1) x.
Proof.
  intros a k v x [Hv [Hall _]] Hk Hx Hvx Hx0.
  split; [exact Hx0 | split].
  - intros j w Hj HB. destruct (Z.eq_dec j k) as [He | Hne].
    + subst j.
      assert (w = x) by
        (apply (best1_unique__dp_body_branches_k6 a k); assumption).
      lia.
    + pose proof (Hall j w ltac:(lia) HB). lia.
  - right. exists k, x. split; [lia | split; [exact Hx | reflexivity]].
Qed.
Lemma clamped_prefix_zero__dp_body_branches_k6 :
  forall l k v, ClampedPrefixMax l k v -> k <= 0 -> v = 0.
Proof.
  intros l k v [Hv [_ Hw]] Hk.
  destruct Hw as [H | [j [Hj _]]]; [exact H | lia].
Qed.
Lemma Zlength_replace_Znth__dp_body_branches_k6 :
  forall (A : Type) (l : list A) n (v : A),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros A l n v. unfold replace_Znth. rewrite !Zlength_correct. f_equal.
  apply replace_nth_length__dp_body_branches_k6.
Qed.
Lemma bounded_max_aux__dp_body_branches_k6 :
  forall (Q : Z -> Prop) (k : nat) (n0 B : Z),
    Q n0 -> (forall n, Q n -> n <= B) -> B - n0 <= Z.of_nat k ->
    exists m, Q m /\ (forall n, Q n -> n <= m).
Proof.
  intros Q k. induction k as [| k IH]; intros n0 B Hn0 Hub Hk.
  - exists n0. split; [exact Hn0 |]. intros n Hn. pose proof (Hub n Hn). simpl in Hk. lia.
  - destruct (excluded_middle_informative (exists n, Q n /\ n0 < n))
      as [[n1 [Hn1 Hgt]] | Hno].
    + apply (IH n1 B); [exact Hn1 | exact Hub |].
      pose proof (Hub n1 Hn1). rewrite Nat2Z.inj_succ in Hk. lia.
    + exists n0. split; [exact Hn0 |]. intros n Hn.
      destruct (Z.le_gt_cases n n0) as [Hle | Hgt]; [exact Hle |].
      exfalso. apply Hno. exists n. split; [exact Hn | lia].
Qed.
Lemma bounded_max_exists__dp_body_branches_k6 :
  forall (Q : Z -> Prop) (n0 B : Z),
    Q n0 -> (forall n, Q n -> n <= B) ->
    exists m, Q m /\ (forall n, Q n -> n <= m).
Proof.
  intros Q n0 B H1 H2.
  apply (bounded_max_aux__dp_body_branches_k6 Q (Z.to_nat (B - n0)) n0 B);
    [exact H1 | exact H2 | lia].
Qed.
Lemma keyshift_lt__dp_body_branches_k6 :
  forall a d p, p < d -> KeyShift a d p = KeyAt a p.
Proof.
  intros a d p H. unfold KeyShift. destruct (Z.ltb_spec d p); lia.
Qed.
Lemma keyshift_gt__dp_body_branches_k6 :
  forall a d p, d < p -> KeyShift a d p = KeyAt a p + 1.
Proof.
  intros a d p H. unfold KeyShift. destruct (Z.ltb_spec d p); lia.
Qed.
Lemma keep1_sublist__dp_body_branches_k6 :
  forall a d s k,
    Keep1List a d s -> 0 <= k <= Zlength s ->
    Keep1List a d (sublist 0 k s).
Proof.
  intros a d s k [Hd [Hmono [Hbnd Hkey]]] Hk.
  assert (Hlen : Zlength (sublist 0 k s) = k) by (apply Zlength_sublist0; lia).
  unfold Keep1List. split; [exact Hd | split; [| split]].
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    rewrite !Znth_sublist0 by lia. apply Hmono; lia.
  - intros p Hp. rewrite Hlen in Hp.
    rewrite Znth_sublist0 by lia. apply Hbnd; lia.
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    rewrite !Znth_sublist0 by lia. apply Hkey; lia.
Qed.
Lemma keep1_to_keep0__dp_body_branches_k6 :
  forall a d s,
    Keep1List a d s ->
    (forall p, 0 <= p < Zlength s -> Znth p s 0 < d) ->
    Keep0List a s.
Proof.
  intros a d s [Hd [Hmono [Hbnd Hkey]]] Hlt.
  unfold Keep0List. split; [exact Hmono | split].
  - intros p Hp. apply (proj1 (Hbnd p Hp)).
  - intros p q Hp Hpq Hq.
    pose proof (Hkey p q Hp Hpq Hq) as HK.
    rewrite (keyshift_lt__dp_body_branches_k6 a d (Znth p s 0)) in HK
      by (apply Hlt; lia).
    rewrite (keyshift_lt__dp_body_branches_k6 a d (Znth q s 0)) in HK
      by (apply Hlt; lia).
    exact HK.
Qed.
Lemma keep1_len_bound__dp_body_branches_k6 :
  forall a d s j,
    Keep1List a d s -> 0 < Zlength s -> Znth (Zlength s - 1) s 0 = j ->
    Zlength s <= j + 1.
Proof.
  intros a d s j [Hd [Hmono [Hbnd _]]] Hpos Hlast.
  assert (Hlb : Zlength s - 1 <= Znth (Zlength s - 1) s 0).
  { apply mono_inc_index_lb__dp_body_branches_k6; [exact Hmono | | lia].
    intros p Hp. apply (proj1 (proj1 (Hbnd p Hp))). }
  lia.
Qed.
Lemma best1_exists__dp_body_branches_k6 :
  forall a j s,
    (exists d, Keep1List a d s /\ d < j) ->
    0 < Zlength s -> Znth (Zlength s - 1) s 0 = j ->
    exists w, Best1EndingAt a j w.
Proof.
  intros a j s Hd Hpos Hlast.
  pose (X := fun t : list Z =>
               (exists d, Keep1List a d t /\ d < j) /\
               0 < Zlength t /\ Znth (Zlength t - 1) t 0 = j).
  pose (Q := fun n : Z => exists t, X t /\ Zlength t = n).
  assert (HQ0 : Q (Zlength s)).
  { exists s. split; [split; [exact Hd | split; [exact Hpos | exact Hlast]] | reflexivity]. }
  assert (HQub : forall n, Q n -> n <= j + 1).
  { intros n [t [[[d [HK Hdj]] [Hp Hl]] Hn]]. subst n.
    apply (keep1_len_bound__dp_body_branches_k6 a d t j HK Hp Hl). }
  destruct (bounded_max_exists__dp_body_branches_k6 Q (Zlength s) (j + 1) HQ0 HQub)
    as [m [[t [HXt Hlt]] Hmax]].
  subst m.
  exists (Zlength t). unfold Best1EndingAt, max_value_of_subset, max_object_of_subset.
  exists t. split; [split |].
  - exact HXt.
  - intros b Hb. apply Hmax. exists b. split; [exact Hb | reflexivity].
  - reflexivity.
Qed.
Lemma best1_upper__dp_body_branches_k6 :
  forall a vals dp m1 mX i uniq r1 s,
    1 <= i ->
    CompressedKeys a vals uniq ->
    DP0Prefix a dp i ->
    Bit1Model a vals m1 i uniq ->
    Bit0Model a vals dp mX (i - 1) uniq ->
    RankResult vals uniq (KeyAt a i + 1) r1 ->
    (exists d, Keep1List a d s /\ d < i) ->
    0 < Zlength s ->
    Znth (Zlength s - 1) s 0 = i ->
    Zlength s <= Z.max (Z.max (RangeMax m1 1 (r1 + 1)) (RangeMax mX 1 (r1 + 1))) 0 + 1.
Proof.
  intros a vals dp m1 mX i uniq r1 s Hi HC HDP HB1 HB0 Hr1 Hex Hpos Hlast.
  destruct Hex as [d [HK Hdi]].
  assert (HCc := HC). destruct HCc as [HS [Hmem _]].
  remember (Zlength s) as L eqn:HL.
  destruct (Z.le_gt_cases L 1) as [Hsmall | Hbig]; [lia |].
  assert (HKc := HK). destruct HKc as [Hdb [Hmono [Hbnd Hkey]]].
  assert (Hjlt : Znth (L - 2) s 0 < i).
  { rewrite <- Hlast. apply Hmono; lia. }
  assert (Hjb : 0 <= Znth (L - 2) s 0 < Zlength a)
    by (apply (proj1 (Hbnd (L - 2) ltac:(lia)))).
  assert (Hjd : Znth (L - 2) s 0 <> d)
    by (apply (proj2 (Hbnd (L - 2) ltac:(lia)))).
  assert (HKp : Keep1List a d (sublist 0 (L - 1) s))
    by (apply keep1_sublist__dp_body_branches_k6; [exact HK | lia]).
  assert (Hplen : Zlength (sublist 0 (L - 1) s) = L - 1)
    by (apply Zlength_sublist0; lia).
  assert (Hplast : Znth (Zlength (sublist 0 (L - 1) s) - 1) (sublist 0 (L - 1) s) 0
                   = Znth (L - 2) s 0).
  { rewrite Hplen. rewrite Znth_sublist0 by lia. f_equal. lia. }
  assert (Hpelem : forall p, 0 <= p < Zlength (sublist 0 (L - 1) s) ->
                   Znth p (sublist 0 (L - 1) s) 0 <= Znth (L - 2) s 0).
  { intros p Hp. rewrite Hplen in Hp. rewrite Znth_sublist0 by lia.
    destruct (Z.eq_dec p (L - 2)) as [He | Hne]; [subst p; lia |].
    assert (Hmm : Znth p s 0 < Znth (L - 2) s 0) by (apply Hmono; lia). lia. }
  assert (Hkeyrel : KeyShift a d (Znth (L - 2) s 0) <= KeyAt a i + 1).
  { pose proof (Hkey (L - 2) (L - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as HH.
    rewrite Hlast in HH.
    rewrite (keyshift_gt__dp_body_branches_k6 a d i Hdi) in HH. exact HH. }
  destruct (Z.lt_total d (Znth (L - 2) s 0)) as [Hd1 | [Hd2 | Hd3]].
  - rewrite (keyshift_gt__dp_body_branches_k6 a d (Znth (L - 2) s 0) Hd1) in Hkeyrel.
    destruct (rank_exists__dp_body_branches_k6 vals uniq (KeyAt a (Znth (L - 2) s 0) + 1)
                HS (proj2 (Hmem _ Hjb))) as [rj Hrj].
    assert (Hrjle : rj <= r1).
    { apply (proj1 (rank_order_iso__dp_body_branches_k6 vals uniq
                      (KeyAt a (Znth (L - 2) s 0) + 1) rj (KeyAt a i + 1) r1 HS Hrj Hr1)).
      lia. }
    assert (Hrjb : 1 <= rj <= uniq) by (destruct Hrj as [HH _]; exact HH).
    destruct (best1_exists__dp_body_branches_k6 a (Znth (L - 2) s 0) (sublist 0 (L - 1) s)
                ltac:(exists d; split; [exact HKp | lia]) ltac:(lia) Hplast) as [w Hw].
    assert (Hwle : L - 1 <= w).
    { destruct Hw as [t [[Htin Htmax] Hteq]].
      assert (Hin : (exists d0, Keep1List a d0 (sublist 0 (L - 1) s) /\
                                d0 < Znth (L - 2) s 0) /\
                    0 < Zlength (sublist 0 (L - 1) s) /\
                    Znth (Zlength (sublist 0 (L - 1) s) - 1) (sublist 0 (L - 1) s) 0
                    = Znth (L - 2) s 0).
      { split; [exists d; split; [exact HKp | lia] | split; [lia | exact Hplast]]. }
      pose proof (Htmax _ Hin). lia. }
    destruct HB1 as [Hm1len HB1m].
    pose proof (proj1 (HB1m rj Hrjb) (Znth (L - 2) s 0) w ltac:(lia) Hw Hrj) as Hdom.
    pose proof (rangemax_lb__dp_body_branches_k6 m1 1 (r1 + 1) rj ltac:(lia)) as Hlb.
    lia.
  - lia.
  - rewrite (keyshift_lt__dp_body_branches_k6 a d (Znth (L - 2) s 0) Hd3) in Hkeyrel.
    assert (HK0 : Keep0List a (sublist 0 (L - 1) s)).
    { apply (keep1_to_keep0__dp_body_branches_k6 a d); [exact HKp |].
      intros p Hp. pose proof (Hpelem p Hp). lia. }
    destruct (rank_exists__dp_body_branches_k6 vals uniq (KeyAt a (Znth (L - 2) s 0))
                HS (proj1 (Hmem _ Hjb))) as [rj Hrj].
    assert (Hrjle : rj <= r1).
    { apply (proj1 (rank_order_iso__dp_body_branches_k6 vals uniq
                      (KeyAt a (Znth (L - 2) s 0)) rj (KeyAt a i + 1) r1 HS Hrj Hr1)).
      lia. }
    assert (Hrjb : 1 <= rj <= uniq) by (destruct Hrj as [HH _]; exact HH).
    pose proof (HDP (Znth (L - 2) s 0) ltac:(lia)) as Hbest.
    unfold Best0EndingAt, max_value_of_subset, max_object_of_subset in Hbest.
    destruct Hbest as [t [[Htin Htmax] Hteq]].
    assert (Hin : Keep0List a (sublist 0 (L - 1) s) /\
                  0 < Zlength (sublist 0 (L - 1) s) /\
                  Znth (Zlength (sublist 0 (L - 1) s) - 1) (sublist 0 (L - 1) s) 0
                  = Znth (L - 2) s 0).
    { split; [exact HK0 | split; [lia | exact Hplast]]. }
    pose proof (Htmax _ Hin) as Hle.
    destruct HB0 as [HmXlen HB0m].
    pose proof (proj1 (HB0m rj Hrjb) (Znth (L - 2) s 0) ltac:(lia) Hrj) as Hdom.
    pose proof (rangemax_lb__dp_body_branches_k6 mX 1 (r1 + 1) rj ltac:(lia)) as Hlb.
    lia.
Qed.
Lemma keep_last_bound__dp_body_branches_k6 :
  forall s j p, mono_inc s -> 0 < Zlength s -> Znth (Zlength s - 1) s 0 = j ->
    0 <= p < Zlength s -> Znth p s 0 <= j.
Proof.
  intros s j p Hm Hpos Hlast Hp.
  destruct (Z.eq_dec p (Zlength s - 1)) as [He | Hne]; [subst p; lia |].
  assert (Hlt : Znth p s 0 < Znth (Zlength s - 1) s 0) by (apply Hm; lia). lia.
Qed.
Lemma keep1_extend__dp_body_branches_k6 :
  forall a d s0 j i,
    Keep1List a d s0 -> d < j -> 0 < Zlength s0 -> Znth (Zlength s0 - 1) s0 0 = j ->
    j < i -> 0 <= i < Zlength a ->
    KeyAt a j + 1 <= KeyAt a i + 1 ->
    Keep1List a d (s0 ++ (i :: nil)).
Proof.
  intros a d s0 j i HK Hdj Hpos Hlast Hji Hib Hkey1.
  assert (HKc := HK). destruct HKc as [Hdb [Hmono [Hbnd Hkey]]].
  assert (Hlen : Zlength (s0 ++ (i :: nil)) = Zlength s0 + 1)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hnth_lt : forall p, 0 <= p < Zlength s0 ->
                    Znth p (s0 ++ (i :: nil)) 0 = Znth p s0 0)
    by (intros p Hp; apply Znth_app1__dp_body_branches_k6; lia).
  assert (Hnth_last : Znth (Zlength s0) (s0 ++ (i :: nil)) 0 = i).
  { rewrite Znth_app2__dp_body_branches_k6 by lia.
    replace (Zlength s0 - Zlength s0) with 0 by lia. unfold Znth; simpl; reflexivity. }
  assert (Hle_j : forall p, 0 <= p < Zlength s0 -> Znth p s0 0 <= j)
    by (intros p Hp; apply (keep_last_bound__dp_body_branches_k6 s0 j p Hmono Hpos Hlast Hp)).
  unfold Keep1List. split; [exact Hdb | split; [| split]].
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    destruct (Z.eq_dec q (Zlength s0)) as [He | Hne].
    + subst q. rewrite Hnth_last. rewrite Hnth_lt by lia.
      pose proof (Hle_j p ltac:(lia)). lia.
    + rewrite !Hnth_lt by lia. apply Hmono; lia.
  - intros p Hp. rewrite Hlen in Hp.
    destruct (Z.eq_dec p (Zlength s0)) as [He | Hne].
    + subst p. rewrite Hnth_last. split; lia.
    + rewrite Hnth_lt by lia. apply Hbnd; lia.
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    destruct (Z.eq_dec q (Zlength s0)) as [He | Hne].
    + subst q. rewrite Hnth_last. rewrite Hnth_lt by lia.
      rewrite (keyshift_gt__dp_body_branches_k6 a d i ltac:(lia)).
      destruct (Z.eq_dec p (Zlength s0 - 1)) as [He2 | Hne2].
      * subst p. rewrite Hlast.
        rewrite (keyshift_gt__dp_body_branches_k6 a d j Hdj). lia.
      * pose proof (Hkey p (Zlength s0 - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as HH.
        rewrite Hlast in HH.
        rewrite (keyshift_gt__dp_body_branches_k6 a d j Hdj) in HH. lia.
    + rewrite !Hnth_lt by lia. apply Hkey; lia.
Qed.
Lemma keep0_extend_cross__dp_body_branches_k6 :
  forall a s0 j i,
    Keep0List a s0 -> 0 < Zlength s0 -> Znth (Zlength s0 - 1) s0 0 = j ->
    j < i - 1 -> 1 <= i < Zlength a ->
    KeyAt a j <= KeyAt a i + 1 ->
    Keep1List a (i - 1) (s0 ++ (i :: nil)).
Proof.
  intros a s0 j i HK Hpos Hlast Hji Hib Hkey1.
  assert (HKc := HK). destruct HKc as [Hmono [Hbnd Hkey]].
  assert (Hlen : Zlength (s0 ++ (i :: nil)) = Zlength s0 + 1)
    by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
  assert (Hnth_lt : forall p, 0 <= p < Zlength s0 ->
                    Znth p (s0 ++ (i :: nil)) 0 = Znth p s0 0)
    by (intros p Hp; apply Znth_app1__dp_body_branches_k6; lia).
  assert (Hnth_last : Znth (Zlength s0) (s0 ++ (i :: nil)) 0 = i).
  { rewrite Znth_app2__dp_body_branches_k6 by lia.
    replace (Zlength s0 - Zlength s0) with 0 by lia. unfold Znth; simpl; reflexivity. }
  assert (Hle_j : forall p, 0 <= p < Zlength s0 -> Znth p s0 0 <= j)
    by (intros p Hp; apply (keep_last_bound__dp_body_branches_k6 s0 j p Hmono Hpos Hlast Hp)).
  unfold Keep1List. split; [lia | split; [| split]].
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    destruct (Z.eq_dec q (Zlength s0)) as [He | Hne].
    + subst q. rewrite Hnth_last. rewrite Hnth_lt by lia.
      pose proof (Hle_j p ltac:(lia)). lia.
    + rewrite !Hnth_lt by lia. apply Hmono; lia.
  - intros p Hp. rewrite Hlen in Hp.
    destruct (Z.eq_dec p (Zlength s0)) as [He | Hne].
    + subst p. rewrite Hnth_last. split; lia.
    + rewrite Hnth_lt by lia.
      pose proof (Hle_j p ltac:(lia)). pose proof (Hbnd p ltac:(lia)).
      split; lia.
  - intros p q Hp Hpq Hq. rewrite Hlen in Hq.
    assert (Hpd : Znth p s0 0 < i - 1)
      by (pose proof (Hle_j p ltac:(lia)); lia).
    destruct (Z.eq_dec q (Zlength s0)) as [He | Hne].
    + subst q. rewrite Hnth_last. rewrite Hnth_lt by lia.
      rewrite (keyshift_gt__dp_body_branches_k6 a (i - 1) i ltac:(lia)).
      rewrite (keyshift_lt__dp_body_branches_k6 a (i - 1) (Znth p s0 0) Hpd).
      destruct (Z.eq_dec p (Zlength s0 - 1)) as [He2 | Hne2].
      * subst p. rewrite Hlast. lia.
      * pose proof (Hkey p (Zlength s0 - 1) ltac:(lia) ltac:(lia) ltac:(lia)) as HH.
        rewrite Hlast in HH. lia.
    + assert (Hqd : Znth q s0 0 < i - 1)
        by (pose proof (Hle_j q ltac:(lia)); lia).
      rewrite !Hnth_lt by lia.
      rewrite (keyshift_lt__dp_body_branches_k6 a (i - 1) (Znth p s0 0) Hpd).
      rewrite (keyshift_lt__dp_body_branches_k6 a (i - 1) (Znth q s0 0) Hqd).
      apply Hkey; lia.
Qed.
Lemma best1_step__dp_body_branches_k6 :
  forall a vals dp m1 mX i uniq r1,
    1 <= i < Zlength a ->
    CompressedKeys a vals uniq ->
    DP0Prefix a dp i ->
    Bit1Model a vals m1 i uniq ->
    Bit0Model a vals dp mX (i - 1) uniq ->
    RankResult vals uniq (KeyAt a i + 1) r1 ->
    Best1EndingAt a i
      (Z.max (Z.max (RangeMax m1 1 (r1 + 1)) (RangeMax mX 1 (r1 + 1))) 0 + 1).
Proof.
  intros a vals dp m1 mX i uniq r1 Hi HC HDP HB1 HB0 Hr1.
  assert (HCc := HC). destruct HCc as [HS [Hmem _]].
  assert (Hr1b : 1 <= r1 <= uniq) by (destruct Hr1 as [HH _]; exact HH).
  unfold Best1EndingAt, max_value_of_subset, max_object_of_subset.
  destruct (Z.le_gt_cases (Z.max (RangeMax m1 1 (r1 + 1)) (RangeMax mX 1 (r1 + 1))) 0)
    as [Hneg | Hpos].
  - exists (i :: nil).
    assert (Hlen1 : Zlength (i :: nil) = 1) by (rewrite Zlength_cons, Zlength_nil; lia).
    assert (Hnth0 : Znth 0 (i :: nil) 0 = i) by (unfold Znth; simpl; reflexivity).
    assert (HK : Keep1List a 0 (i :: nil)).
    { unfold Keep1List. split; [lia | split; [| split]].
      - intros p q Hp Hpq Hq. rewrite Hlen1 in Hq. lia.
      - intros p Hp. rewrite Hlen1 in Hp. replace p with 0 by lia.
        rewrite Hnth0. split; lia.
      - intros p q Hp Hpq Hq. rewrite Hlen1 in Hq. lia. }
    split; [split |].
    + split; [exists 0; split; [exact HK | lia] |].
      split; [lia |]. rewrite Hlen1. replace (1 - 1) with 0 by lia. exact Hnth0.
    + intros b Hb. destruct Hb as [Hbex [Hbpos Hblast]].
      pose proof (best1_upper__dp_body_branches_k6 a vals dp m1 mX i uniq r1 b
                    ltac:(lia) HC HDP HB1 HB0 Hr1 Hbex Hbpos Hblast) as Hub.
      rewrite Hlen1. lia.
    + rewrite Hlen1. lia.
  - destruct (Z.le_ge_cases (RangeMax mX 1 (r1 + 1)) (RangeMax m1 1 (r1 + 1)))
      as [HQ | HQ].
    + assert (HQ1pos : RangeMax m1 1 (r1 + 1) > 0) by lia.
      destruct (rangemax_prefix_char__dp_body_branches_k6 m1 1 (r1 + 1))
        as [Hmn | [q [Hq Heq]]].
      { rewrite Hmn in HQ1pos. unfold MaxBitNeg in HQ1pos. lia. }
      assert (Hrq : 1 <= q <= uniq) by lia.
      assert (HB1c := HB1). destruct HB1c as [Hm1len HB1m].
      destruct (proj2 (HB1m q Hrq)) as [Hnegq | [j [w [Hj [HBest [HRj Hval]]]]]].
      { rewrite Heq, Hnegq in HQ1pos. unfold MaxBitNeg in HQ1pos. lia. }
      assert (Hkeyji : KeyAt a j + 1 <= KeyAt a i + 1).
      { apply (proj2 (rank_order_iso__dp_body_branches_k6 vals uniq
                        (KeyAt a j + 1) q (KeyAt a i + 1) r1 HS HRj Hr1)). lia. }
      destruct HBest as [s0 [[Hs0in Hs0max] Hs0eq]].
      destruct Hs0in as [[d [HK0 Hdj]] [Hpos0 Hlast0]].
      assert (HKnew : Keep1List a d (s0 ++ (i :: nil)))
        by (apply (keep1_extend__dp_body_branches_k6 a d s0 j i HK0 Hdj Hpos0 Hlast0
                     ltac:(lia) ltac:(lia) Hkeyji)).
      assert (Hlen : Zlength (s0 ++ (i :: nil)) = Zlength s0 + 1)
        by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      assert (Hnth_last : Znth (Zlength s0) (s0 ++ (i :: nil)) 0 = i).
      { rewrite Znth_app2__dp_body_branches_k6 by lia.
        replace (Zlength s0 - Zlength s0) with 0 by lia.
        unfold Znth; simpl; reflexivity. }
      exists (s0 ++ (i :: nil)).
      split; [split |].
      * split; [exists d; split; [exact HKnew | lia] |].
        split; [lia |]. rewrite Hlen.
        replace (Zlength s0 + 1 - 1) with (Zlength s0) by lia. exact Hnth_last.
      * intros b Hb. destruct Hb as [Hbex [Hbpos Hblast]].
        pose proof (best1_upper__dp_body_branches_k6 a vals dp m1 mX i uniq r1 b
                      ltac:(lia) HC HDP HB1 HB0 Hr1 Hbex Hbpos Hblast) as Hub.
        rewrite Hlen. lia.
      * rewrite Hlen. lia.
    + assert (HQXpos : RangeMax mX 1 (r1 + 1) > 0) by lia.
      destruct (rangemax_prefix_char__dp_body_branches_k6 mX 1 (r1 + 1))
        as [Hmn | [q [Hq Heq]]].
      { rewrite Hmn in HQXpos. unfold MaxBitNeg in HQXpos. lia. }
      assert (Hrq : 1 <= q <= uniq) by lia.
      assert (HB0c := HB0). destruct HB0c as [HmXlen HB0m].
      destruct (proj2 (HB0m q Hrq)) as [Hnegq | [j [Hj [HRj Hval]]]].
      { rewrite Heq, Hnegq in HQXpos. unfold MaxBitNeg in HQXpos. lia. }
      assert (Hkeyji : KeyAt a j <= KeyAt a i + 1).
      { apply (proj2 (rank_order_iso__dp_body_branches_k6 vals uniq
                        (KeyAt a j) q (KeyAt a i + 1) r1 HS HRj Hr1)). lia. }
      pose proof (HDP j ltac:(lia)) as Hbest.
      unfold Best0EndingAt, max_value_of_subset, max_object_of_subset in Hbest.
      destruct Hbest as [s0 [[Hs0in Hs0max] Hs0eq]].
      destruct Hs0in as [HK0 [Hpos0 Hlast0]].
      assert (HKnew : Keep1List a (i - 1) (s0 ++ (i :: nil)))
        by (apply (keep0_extend_cross__dp_body_branches_k6 a s0 j i HK0 Hpos0 Hlast0
                     ltac:(lia) ltac:(lia) Hkeyji)).
      assert (Hlen : Zlength (s0 ++ (i :: nil)) = Zlength s0 + 1)
        by (rewrite Zlength_app, Zlength_cons, Zlength_nil; lia).
      assert (Hnth_last : Znth (Zlength s0) (s0 ++ (i :: nil)) 0 = i).
      { rewrite Znth_app2__dp_body_branches_k6 by lia.
        replace (Zlength s0 - Zlength s0) with 0 by lia.
        unfold Znth; simpl; reflexivity. }
      exists (s0 ++ (i :: nil)).
      split; [split |].
      * split; [exists (i - 1); split; [exact HKnew | lia] |].
        split; [lia |]. rewrite Hlen.
        replace (Zlength s0 + 1 - 1) with (Zlength s0) by lia. exact Hnth_last.
      * intros b Hb. destruct Hb as [Hbex [Hbpos Hblast]].
        pose proof (best1_upper__dp_body_branches_k6 a vals dp m1 mX i uniq r1 b
                      ltac:(lia) HC HDP HB1 HB0 Hr1 Hbex Hbpos Hblast) as Hub.
        rewrite Hlen. lia.
      * rewrite Hlen. lia.
Qed.
Lemma best1_bounds__dp_body_branches_k6 :
  forall a i v, Best1EndingAt a i v -> 1 <= v <= i + 1.
Proof.
  intros a i v [s [[[[d [HK Hd]] [Hpos Hlast]] Hmax] Heq]].
  pose proof (keep1_len_bound__dp_body_branches_k6 a d s i HK Hpos Hlast). lia.
Qed.
Lemma bit1_model_insert__dp_body_branches_k6 :
  forall a vals m1 i uniq r1 d1,
    0 <= i ->
    StrictIncPrefix vals uniq ->
    Bit1Model a vals m1 i uniq ->
    Best1EndingAt a i d1 ->
    RankResult vals uniq (KeyAt a i + 1) r1 ->
    Bit1Model a vals (MaxBitInsert m1 r1 d1) (i + 1) uniq.
Proof.
  intros a vals m1 i uniq r1 d1 Hi HS [Hlen HM] HBi Hr1.
  assert (Hr1b : 1 <= r1 <= uniq) by (destruct Hr1 as [HH _]; exact HH).
  split.
  { rewrite Zlength_maxbitinsert__dp_body_branches_k6. exact Hlen. }
  intros r Hr.
  destruct (HM r Hr) as [Hdom Hw].
  split.
  - intros j w Hj HBj HRj.
    destruct (Z.eq_dec j i) as [He | Hne].
    + subst j.
      assert (Hweq : w = d1)
        by (apply (best1_unique__dp_body_branches_k6 a i); assumption).
      assert (r = r1) by
        (apply (rank_unique__dp_body_branches_k6 vals uniq (KeyAt a i + 1)); assumption).
      subst r. rewrite Znth_maxbitinsert_same__dp_body_branches_k6 by lia. lia.
    + destruct (Z.eq_dec r r1) as [He2 | Hne2].
      * subst r. rewrite Znth_maxbitinsert_same__dp_body_branches_k6 by lia.
        pose proof (Hdom j w ltac:(lia) HBj HRj). lia.
      * rewrite Znth_maxbitinsert_diff__dp_body_branches_k6 by lia.
        apply (Hdom j w); [lia | exact HBj | exact HRj].
  - destruct (Z.eq_dec r r1) as [He2 | Hne2].
    + subst r. rewrite Znth_maxbitinsert_same__dp_body_branches_k6 by lia.
      destruct (Z.le_gt_cases (Znth r1 m1 0) d1) as [Hle | Hgt].
      * rewrite Z.max_r by lia. right. exists i, d1.
        split; [lia | split; [exact HBi | split; [exact Hr1 | reflexivity]]].
      * rewrite Z.max_l by lia.
        destruct Hw as [H | [j [w [Hj [HBj [HRj Hval]]]]]]; [left; exact H |].
        right. exists j, w. split; [lia | split; [exact HBj | split; [exact HRj | exact Hval]]].
    + rewrite Znth_maxbitinsert_diff__dp_body_branches_k6 by lia.
      destruct Hw as [H | [j [w [Hj [HBj [HRj Hval]]]]]]; [left; exact H |].
      right. exists j, w. split; [lia | split; [exact HBj | split; [exact HRj | exact Hval]]].
Qed.
Lemma rangemax_le_bound__pure_d1_bound_bit0 :
  forall (m : list Z) (lo hi B : Z),
    MaxBitNeg <= B ->
    (forall r, lo <= r < hi -> Znth r m 0 <= B) ->
    RangeMax m lo hi <= B.
Proof.
  intros m lo hi B HB Hr.
  unfold RangeMax.
  assert (Haux : forall l : list Z,
             (forall x, In x l -> x <= B) ->
             fold_right Z.max MaxBitNeg l <= B).
  { induction l as [| y l IH]; simpl; intros H.
    - exact HB.
    - apply Z.max_lub.
      + apply H. left. reflexivity.
      + apply IH. intros x Hx. apply H. right. exact Hx. }
  apply Haux.
  intros x Hx.
  apply in_map_iff in Hx.
  destruct Hx as [r [Heq Hin]].
  subst x.
  apply Hr.
  apply In_Zrange. exact Hin.
Qed.
Lemma rangemax_le_bound__pure_d1_bound_bit1 :
  forall (m : list Z) (lo hi B : Z),
    MaxBitNeg <= B ->
    (forall r : Z, lo <= r < hi -> Znth r m 0 <= B) ->
    RangeMax m lo hi <= B.
Proof.
  intros m lo hi B HB Hall.
  unfold RangeMax.
  assert (Hgen : forall L : list Z,
            (forall x : Z, In x L -> lo <= x < hi) ->
            fold_right Z.max MaxBitNeg (map (fun r => Znth r m 0) L) <= B).
  { induction L as [| a L IH]; intros HL; simpl.
    - exact HB.
    - apply Z.max_lub.
      + apply Hall. apply HL. left. reflexivity.
      + apply IH. intros x Hx. apply HL. right. exact Hx. }
  apply Hgen. intros x Hx. apply (proj2 (In_Zrange lo hi x)). exact Hx.
Qed.
