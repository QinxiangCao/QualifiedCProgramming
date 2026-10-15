Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition SpreadStep (a b : list Z) : Prop :=
  exists i j, 0 <= i < j /\ j < Zlength a /\ Znth i a 0 = 1 /\ Znth j a 0 = 1 /\
   2 * (fold_right Z.add 0) (sublist i (j + 1) a) >= j - i + 1 /\ Zlength b = Zlength a /\
   (forall q, 0 <= q < Zlength a -> Znth q b 0 = if (Z.leb i q && Z.leb q j)%bool then 1 else Znth q a 0).
Definition Rated (s : list Z) : Prop :=
  exists st : list (list Z), st <> [] /\ Znth 0 st [] = s /\ Forall (fun x => x = 1) (Znth (Zlength st - 1) st []) /\
  forall i, 0 <= i < Zlength st - 1 -> SpreadStep (Znth i st []) (Znth (i + 1) st []).
Definition AllBinary (n : Z) (ss : list (list Z)) : Prop :=
  NoDup ss /\ forall s, In s ss <-> Zlength s = n /\ Forall (fun x => x = 0 \/ x = 1) s.
Definition Pre (n m : Z) : Prop :=
  (* Stated explicitly in the P093 solver Require, which therefore omits the
     Pre(...) call: 1 <= n <= 5000 /\ 10 <= m <= 1000000000. *)
  True.
Definition Spec (n m out : Z) : Prop :=
  exists ss, AllBinary n ss /\ out = (#(fun i : Z => 0 <= i < Zlength ss /\ Rated (Znth i ss []))) mod m.

(* Closed form of the value the C loop keeps in [pow2]: pow2[k] == 2^k mod m.
   Named here only so the C annotation can state the fact without inlining
   the exponentiation. *)
Definition Pow2Mod (k m : Z) : Z := (2 ^ k) mod m.

(* Lifts a fully-defined content list to the [option Z] cell list [free]'s
   contract expects, so a scratch buffer that was fully written can still be
   handed to the generic (possibly partially-defined) free contract. *)
Definition SomeList (l : list Z) : list (option Z) := map Some l.

(* --- Counting infrastructure for the Spec/Rated bridge (annotation-r3) ---
   These are general-purpose facts about [set_card]/[sum] over a [Finite]
   predicate: they do not mention SpreadStep/Rated/AllBinary at all, and are
   the reusable building blocks a full CF-1750F combinatorial correctness
   proof needs to (a) show the count in [Spec] does not depend on which
   AllBinary witness list is chosen, and (b) classify a finite set into
   disjoint cases and sum the per-case counts (the header-comment argument
   partitions length-i strings by where the first block's greedy merge
   stops). Neither lemma is specific to this DP; they are proved purely from
   the [Finite]/[sum] interface in SumLib.Sum. *)

Require Import Coq.micromega.Lia.

Lemma fold_right_Zadd_permutation :
  forall {A : Type} (f : A -> Z) (l1 l2 : list A),
    Permutation l1 l2 ->
    fold_right (fun x acc => f x + acc) 0 l1 =
    fold_right (fun x acc => f x + acc) 0 l2.
Proof.
  intros A f l1 l2 Hperm.
  induction Hperm.
  - reflexivity.
  - simpl. lia.
  - simpl. lia.
  - lia.
Qed.

Lemma fold_right_Zadd_app :
  forall {A : Type} (f : A -> Z) (l1 l2 : list A),
    fold_right (fun x acc => f x + acc) 0 (l1 ++ l2) =
    fold_right (fun x acc => f x + acc) 0 l1 +
    fold_right (fun x acc => f x + acc) 0 l2.
Proof.
  intros A f l1 l2.
  induction l1 as [|x l1 IH]; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

(* [set_card] does not depend on which [Finite] instance/enum witness is
   used, as long as both witnesses satisfy the same membership predicate
   [P]. Needed because [Spec] only fixes [ss] up to [AllBinary], i.e. up to
   permutation, not as a specific list. *)
Lemma set_card_irrel {A : Type} (P : A -> Prop) (Hf1 Hf2 : Finite P) :
  @set_card A P Hf1 = @set_card A P Hf2.
Proof.
  unfold set_card, sum.
  apply fold_right_Zadd_permutation.
  apply NoDup_Permutation.
  - apply (@enum_nodup A P Hf1).
  - apply (@enum_nodup A P Hf2).
  - intros x.
    rewrite <- (@enum_ok A P Hf1 x).
    rewrite <- (@enum_ok A P Hf2 x).
    tauto.
Qed.

(* Disjoint-union cardinality additivity: the basic counting tool needed to
   classify a finite set into cases and sum the per-case counts. *)
Lemma set_card_disjoint_union {A : Type}
    (P1 P2 : A -> Prop) `{Finite A P1} `{Finite A P2}
    `{Finite A (fun x => P1 x \/ P2 x)} :
  (forall x, ~ (P1 x /\ P2 x)) ->
  @set_card A (fun x => P1 x \/ P2 x) _ = set_card P1 + set_card P2.
Proof.
  intros Hdisj.
  unfold set_card at 1.
  unfold sum at 1.
  transitivity (fold_right (fun x acc => 1 + acc) 0 (@enum A P1 _ ++ @enum A P2 _)).
  - apply fold_right_Zadd_permutation.
    apply NoDup_Permutation.
    + apply (@enum_nodup A (fun x => P1 x \/ P2 x) _).
    + apply NoDup_app.
      * apply (@enum_nodup A P1 _).
      * apply (@enum_nodup A P2 _).
      * intros x Hx1 Hx2.
        apply (Hdisj x).
        split.
        -- apply (@enum_ok A P1 _). exact Hx1.
        -- apply (@enum_ok A P2 _). exact Hx2.
    + intros x.
      rewrite in_app_iff.
      rewrite <- (@enum_ok A (fun x => P1 x \/ P2 x) _ x).
      rewrite <- (@enum_ok A P1 _ x).
      rewrite <- (@enum_ok A P2 _ x).
      tauto.
  - apply fold_right_Zadd_app.
Qed.

(* --- Layer 2: adjacent-block-merge availability (annotation-r4) ---
   Pure list-arithmetic generalization, to arbitrarily many blocks, of the
   fact attempt 3 hand-verified for 3 blocks: if a span made of alternating
   block sizes [ps] (each >= 1) and gap sizes [zs] (each >= 1, one fewer gap
   than blocks) has total block size at least total gap size, then some
   *adjacent* pair of blocks already has enough combined size to cover the
   gap between them. This is the arithmetic core of "any SpreadStep(i,j)
   merge decomposes into adjacent-maximal-block merges": SpreadStep's own
   condition [2 * sum(sublist i (j+1) a) >= j - i + 1] is exactly
   [sum ps >= sum zs] once the span is read as an alternating
   block/gap sequence, and this lemma is what licenses replacing an
   arbitrary-span merge witness by one between two neighboring blocks.
   Proved purely from Zlength/Znth/fold_right list facts; it does not
   mention SpreadStep/Rated/AllBinary. Connecting it to an explicit
   maximal-block decomposition of an actual 0/1 [list Z] (extracting [ps]
   and [zs] from a concrete array and mapping the witness index [t] back to
   real list positions to build a smaller SpreadStep instance) is further
   work, not attempted in this round. *)

Lemma adjacent_merge_exists :
  forall (zs ps : list Z),
    Zlength ps = Zlength zs + 1 ->
    2 <= Zlength ps ->
    Forall (fun p => 1 <= p) ps ->
    Forall (fun z => 1 <= z) zs ->
    fold_right Z.add 0 zs <= fold_right Z.add 0 ps ->
    exists t : Z, 0 <= t < Zlength zs /\
      Znth t zs 0 <= Znth t ps 0 + Znth (t + 1) ps 0.
Proof.
  induction zs as [|z1 zs' IH]; intros ps Hlen Hge2 Hpsp Hzsp Hsum.
  - rewrite Zlength_nil in Hlen. lia.
  - pose proof (Zlength_nonneg zs') as Hnn.
    destruct ps as [|p1 [|p2 ps2]].
    + rewrite Zlength_nil in Hlen. rewrite Zlength_cons in Hlen. lia.
    + rewrite Zlength_cons, Zlength_nil in Hlen. rewrite Zlength_cons in Hlen. lia.
    + assert (Hp1 : 1 <= p1) by (apply (Forall_inv Hpsp)).
      assert (Hpsp1 : Forall (fun p => 1 <= p) (p2 :: ps2)) by (apply (Forall_inv_tail Hpsp)).
      assert (Hp2 : 1 <= p2) by (apply (Forall_inv Hpsp1)).
      assert (Hpsp2 : Forall (fun p => 1 <= p) ps2) by (apply (Forall_inv_tail Hpsp1)).
      assert (Hz1 : 1 <= z1) by (apply (Forall_inv Hzsp)).
      assert (Hzsp' : Forall (fun z => 1 <= z) zs') by (apply (Forall_inv_tail Hzsp)).
      destruct (Z_le_dec z1 (p1 + p2)) as [Hmerge | Hnomerge].
      * exists 0.
        split.
        -- rewrite Zlength_cons. lia.
        -- rewrite Znth0_cons.
           rewrite Znth0_cons.
           replace (0 + 1) with 1 by lia.
           rewrite Znth_cons by lia.
           replace (1 - 1) with 0 by lia.
           rewrite Znth0_cons.
           lia.
      * destruct ps2 as [|p3 ps3].
        -- exfalso.
           rewrite Zlength_cons, Zlength_cons, Zlength_nil in Hlen.
           rewrite Zlength_cons in Hlen.
           assert (Hzs'nil : zs' = []).
           { destruct zs' as [|z' zs'']; [reflexivity |].
             rewrite Zlength_cons in Hlen.
             pose proof (Zlength_nonneg zs'') as Hnn2. lia. }
           subst zs'. simpl in Hsum. lia.
        -- assert (Hge2' : 2 <= Zlength (p2 :: p3 :: ps3)).
           { rewrite Zlength_cons, Zlength_cons. pose proof (Zlength_nonneg ps3). lia. }
           assert (Hlen' : Zlength (p2 :: p3 :: ps3) = Zlength zs' + 1).
           { rewrite Zlength_cons, Zlength_cons, Zlength_cons, Zlength_cons in Hlen.
             rewrite Zlength_cons, Zlength_cons. lia. }
           assert (Hsum' : fold_right Z.add 0 zs' <= fold_right Z.add 0 (p2 :: p3 :: ps3)).
           { simpl in Hsum. simpl. lia. }
           destruct (IH (p2 :: p3 :: ps3) Hlen' Hge2' Hpsp1 Hzsp' Hsum') as [t [Ht1 Ht2]].
           exists (t + 1).
           split.
           ++ rewrite Zlength_cons. lia.
           ++ rewrite Znth_cons by lia.
              replace (t + 1 - 1) with t by lia.
              rewrite Znth_cons by lia.
              replace (t + 1 - 1) with t by lia.
              rewrite Znth_cons with (n := t + 1 + 1) by lia.
              replace (t + 1 + 1 - 1) with (t + 1) by lia.
              lia.
Qed.

(* --- DP array contents (annotation-r5) ------------------------------------
   Definitions only -- no lemmas, nothing that can fail to be Qed-closed.

   These mirror the arithmetic the C loop body performs on the scratch arrays
   Q / Brow / P, so that the loop invariants can state what those arrays
   *contain* rather than only that they are owned. Without this the value of
   A[i] is unconstrained in the logic at every program point, which is what
   made the old `Spec(i, ...)` assertion unprovable.

   These are deliberately an executable mirror of the C recurrence. That is
   appropriate here precisely because they are invariant vocabulary, not the
   functional specification: the functional specification remains the frozen
   combinatorial [Spec], and relating this recurrence to [Spec] is the single
   remaining proof obligation.

   Note on division: C's int division truncates toward zero while [Z.div]
   floors; they agree on non-negative operands. The only division below is
   [(d + j + 2) / 2] with d, j >= 1, so the two agree here. *)

Definition Zeros (k : Z) : list Z := repeat 0 (Z.to_nat k).

(* The per-(d, j) tail weight W[d][j] the C loop accumulates into `w`. *)
Definition Wfun (lQ : list Z) (d j m : Z) : Z :=
  let w0 := 1 mod m in
  let Lmax := d - (d + j + 2) / 2 in
  let w1 := if Z.geb Lmax 1 then (w0 + Pow2Mod Lmax m - 1 mod m + m) mod m else w0 in
  let D := d - j - 1 in
  if Z.geb D 0 then (w1 + Znth D lQ 0) mod m else w1.

(* Brow[j] for row i, i.e. A[j] * W[i-j][j] mod m. *)
Definition BrowEntry (lA lQ : list Z) (i j m : Z) : Z :=
  (Znth j lA 0 * Wfun lQ (i - j) j m) mod m.

(* `blocked` after columns 1..k of row i have been folded in. *)
Fixpoint BlockedNat (lA lQ : list Z) (i m : Z) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => (BlockedNat lA lQ i m k' + BrowEntry lA lQ i (Z.of_nat (S k')) m) mod m
  end.

Definition Blocked (lA lQ : list Z) (i m c : Z) : Z :=
  BlockedNat lA lQ i m (Z.to_nat c).

(* The value written to A[i] at the end of row i's first inner loop. *)
Definition ARowVal (lA lQ : list Z) (i m : Z) : Z :=
  ((Pow2Mod (i - 1) m - Blocked lA lQ i m (i - 1)) mod m + m) mod m.

(* The summand `c` of the prefix-sum loop at column q. *)
Definition RowC (lA lQ : list Z) (i m q : Z) : Z :=
  if Z.eqb q 0 then 0
  else if Z.ltb q i then BrowEntry lA lQ i q m
  else ARowVal lA lQ i m.

(* `run` after the first k columns (0..k-1) have been folded in. *)
Fixpoint RunNat (lA lQ : list Z) (i m : Z) (k : nat) : Z :=
  match k with
  | O => 0
  | S k' => (RunNat lA lQ i m k' + RowC lA lQ i m (Z.of_nat k')) mod m
  end.

Definition RunUpto (lA lQ : list Z) (i m c : Z) : Z :=
  RunNat lA lQ i m (Z.to_nat c).

(* P[q] = the running prefix sum through column q. *)
Definition PEntry (lA lQ : list Z) (i m q : Z) : Z :=
  RunUpto lA lQ i m (q + 1).

(* Q after the first k of row i's updates (t = 0..k-1) have been applied.
   Note the P values fold in the *incoming* lQ, matching the C: P was
   computed from Brow / A[i], which were computed from the incoming Q. *)
Fixpoint QAfterNat (lQ lA : list Z) (i m n : Z) (k : nat) : list Z :=
  match k with
  | O => lQ
  | S k' =>
      let l' := QAfterNat lQ lA i m n k' in
      let t := Z.of_nat k' in
      if Z.leb (i + t) (2 * n)
      then replace_Znth (i + t) ((Znth (i + t) l' 0 + PEntry lA lQ i m t) mod m) l'
      else l'
  end.

(* The (A, Q) pair after the first k outer rows. Coq has no structural
   recursion on Z, so the recursion is on nat with Z.of_nat / Z.to_nat at the
   boundary. *)
Fixpoint DPNat (m n : Z) (k : nat) : (list Z * list Z) :=
  match k with
  | O => (Zeros (n + 2), Zeros (2 * n + 4))
  | S k' =>
      let st := DPNat m n k' in
      let lA := fst st in
      let lQ := snd st in
      let i := Z.of_nat (S k') in
      (replace_Znth i (ARowVal lA lQ i m) lA,
       QAfterNat lQ lA i m n (Z.to_nat i))
  end.

Definition DPA (m n i : Z) : list Z := fst (DPNat m n (Z.to_nat i)).
Definition DPQ (m n i : Z) : list Z := snd (DPNat m n (Z.to_nat i)).

(* Row-local wrappers, so the C annotations can name row i's intermediate
   values without respelling the incoming (A, Q) state each time. *)
Definition RowBrow (m n i j : Z) : Z :=
  BrowEntry (DPA m n (i - 1)) (DPQ m n (i - 1)) i j m.
Definition RowBlocked (m n i c : Z) : Z :=
  Blocked (DPA m n (i - 1)) (DPQ m n (i - 1)) i m c.
Definition RowP (m n i q : Z) : Z :=
  PEntry (DPA m n (i - 1)) (DPQ m n (i - 1)) i m q.
Definition RowRun (m n i c : Z) : Z :=
  RunUpto (DPA m n (i - 1)) (DPQ m n (i - 1)) i m c.
Definition QPartial (m n i t : Z) : list Z :=
  QAfterNat (DPQ m n (i - 1)) (DPA m n (i - 1)) i m n (Z.to_nat t).

(* --- pow2 tail cell (annotation-r6) ---------------------------------------
   pow2 is allocated with n+2 cells but the program only ever writes indices
   0..n, so its last cell stays uninitialised. [free] accepts uninitialised
   cells through [mixed_full] / [option Z], so the cell list handed to it is
   the written prefix lifted by [SomeList] with a single [None] appended. *)
Definition SomeListUndefTail (l : list Z) : list (option Z) :=
  SomeList l ++ [None].

(* ---------- from dev.v ---------- *)

(* ---------- L1: decidable saturation characterization of Rated ---------- *)

Definition all_ones (n : nat) : list Z := repeat 1 n.

Definition window (s : list Z) (i j : nat) : list Z := firstn (S j - i) (skipn i s).

Definition mergeable (s : list Z) (i j : nat) : bool :=
  let w := Z.of_nat (S j - i) in
  let ones := fold_right Z.add 0 (window s i j) in
  andb (Nat.ltb i j)
  (andb (Z.eqb (nth i s 0) 1)
  (andb (Z.eqb (nth j s 0) 1)
  (andb (Z.geb (2 * ones) w)
        (Z.ltb ones w)))).

Fixpoint fill_from (k i j : nat) (l : list Z) : list Z :=
  match l with
  | nil => nil
  | x :: tl =>
      (if andb (Nat.leb i k) (Nat.leb k j) then 1 else x) :: fill_from (S k) i j tl
  end.

Definition fill (s : list Z) (i j : nat) : list Z := fill_from 0 i j s.

(* first enabled merge in a fixed order, if any *)
Definition pairs (n : nat) : list (nat * nat) :=
  flat_map (fun i => map (fun j => (i, j)) (seq 0 n)) (seq 0 n).

Definition one_step (s : list Z) : option (list Z) :=
  match filter (fun p => mergeable s (fst p) (snd p)) (pairs (length s)) with
  | nil => None
  | p :: _ => Some (fill s (fst p) (snd p))
  end.

Fixpoint saturate_fuel (k : nat) (s : list Z) : list Z :=
  match k with
  | O => s
  | S k' => match one_step s with
            | Some s' => saturate_fuel k' s'
            | None => s
            end
  end.

Definition saturate (s : list Z) : list Z := saturate_fuel (length s) s.

Definition rated_bool (s : list Z) : bool :=
  if list_eq_dec Z.eq_dec (saturate s) (all_ones (length s)) then true else false.

(* --- validation: must match the brute-forced reference --- *)
Definition all_strings (n : nat) : list (list Z) :=
  fold_right (fun _ acc => flat_map (fun s => [0 :: s; 1 :: s]) acc) [[]] (seq 0 n).

Definition count_rated (n : nat) : Z :=
  Z.of_nat (length (filter rated_bool (all_strings n))).

Definition binary (s : list Z) : Prop := Forall (fun x => x = 0 \/ x = 1) s.

(* ===================== supporting development ===================== *)

Definition ones_count (s : list Z) : Z := fold_right Z.add 0 s.

Definition dom (s t : list Z) : Prop := forall k, nth k s 0 = 1 -> nth k t 0 = 1.

Lemma dom_refl : forall s, dom s s.
Proof. intros s k H. exact H. Qed.

Lemma dom_trans : forall s t u, dom s t -> dom t u -> dom s u.
Proof. intros s t u H1 H2 k H. apply H2. apply H1. exact H. Qed.

Lemma nth_one_lt : forall (s : list Z) k, nth k s 0 = 1 -> (k < length s)%nat.
Proof.
  intros s k H.
  destruct (Nat.lt_ge_cases k (length s)) as [Hlt | Hge]; [ exact Hlt |].
  rewrite (nth_overflow s 0 Hge) in H. discriminate.
Qed.

Lemma binary_nth : forall s, binary s -> forall k, nth k s 0 = 0 \/ nth k s 0 = 1.
Proof.
  induction s as [|x s IH]; intros Hb k.
  - destruct k; simpl; left; reflexivity.
  - inversion Hb as [| x0 l0 Hx Hs]; subst.
    destruct k as [|k]; simpl; [ exact Hx | apply IH; exact Hs ].
Qed.

Lemma nth_binary : forall s, (forall k, (k < length s)%nat -> nth k s 0 = 0 \/ nth k s 0 = 1) -> binary s.
Proof.
  induction s as [|x s IH]; intros H.
  - constructor.
  - constructor.
    + specialize (H 0%nat). simpl in H. apply H. simpl. apply Nat.lt_0_succ.
    + apply IH. intros k Hk. specialize (H (S k)). simpl in H. apply H.
      simpl. apply -> Nat.succ_lt_mono. exact Hk.
Qed.

Lemma ones_count_nonneg : forall s, binary s -> 0 <= ones_count s.
Proof.
  induction s as [|x s IH]; intros Hb.
  - unfold ones_count. simpl. lia.
  - inversion Hb as [| x0 l0 Hx Hs]; subst.
    specialize (IH Hs). unfold ones_count in *. simpl. lia.
Qed.

Lemma ones_count_repeat1 : forall n, ones_count (repeat 1 n) = Z.of_nat n.
Proof.
  induction n as [|n IH].
  - reflexivity.
  - unfold ones_count in *. cbn [repeat fold_right].
    rewrite IH, Nat2Z.inj_succ. lia.
Qed.

Lemma binary_repeat1 : forall n, binary (repeat 1 n).
Proof.
  induction n as [|n IH]; simpl; constructor; [ right; reflexivity | exact IH ].
Qed.

Lemma nth_repeat1 : forall n k, (k < n)%nat -> nth k (repeat 1 n) 0 = 1.
Proof.
  induction n as [|n IH]; intros k Hk; [ lia |].
  destruct k as [|k]; simpl; [ reflexivity |].
  apply IH. lia.
Qed.

(* ---------- the dominance / counting core ---------- *)

Lemma dom_sum : forall s t, length s = length t -> binary s -> binary t -> dom s t ->
  ones_count s <= ones_count t /\ (ones_count s = ones_count t -> s = t).
Proof.
  induction s as [|x s IH]; intros t Hlen Hbs Hbt Hd.
  - destruct t as [|y t]; [ | simpl in Hlen; discriminate ].
    split; [ unfold ones_count; simpl; lia | reflexivity ].
  - destruct t as [|y t]; [ simpl in Hlen; discriminate |].
    simpl in Hlen. injection Hlen as Hlen.
    inversion Hbs as [| x0 l0 Hx Hs]; subst.
    inversion Hbt as [| y0 l1 Hy Ht]; subst.
    assert (Hd0 : x = 1 -> y = 1).
    { intros Hx1. specialize (Hd 0%nat). simpl in Hd. apply Hd. exact Hx1. }
    assert (Hdt : dom s t).
    { intros k Hk. specialize (Hd (S k)). simpl in Hd. apply Hd. exact Hk. }
    destruct (IH t Hlen Hs Ht Hdt) as [Hle Heq].
    unfold ones_count in *. simpl fold_right.
    destruct Hx as [Hx | Hx]; destruct Hy as [Hy | Hy]; subst.
    + split; [ lia |]. intros He. f_equal. apply Heq. lia.
    + split; [ lia |]. intros He.
      assert (fold_right Z.add 0 s = fold_right Z.add 0 t) by lia.
      lia.
    + specialize (Hd0 eq_refl). discriminate.
    + split; [ lia |]. intros He. f_equal. apply Heq. lia.
Qed.

Lemma dom_le : forall s t, length s = length t -> binary s -> binary t -> dom s t ->
  ones_count s <= ones_count t.
Proof. intros s t H1 H2 H3 H4. apply (proj1 (dom_sum s t H1 H2 H3 H4)). Qed.

Lemma dom_all_ones : forall s, dom s (repeat 1 (length s)).
Proof.
  intros s k Hk. apply nth_repeat1. apply nth_one_lt with (s := s). exact Hk.
Qed.

Lemma ones_le_length : forall s, binary s -> ones_count s <= Z.of_nat (length s).
Proof.
  intros s Hb.
  rewrite <- (ones_count_repeat1 (length s)).
  apply dom_le.
  - rewrite repeat_length. reflexivity.
  - exact Hb.
  - apply binary_repeat1.
  - apply dom_all_ones.
Qed.

Lemma all_ones_of_nth : forall s, (forall k, (k < length s)%nat -> nth k s 0 = 1) ->
  s = repeat 1 (length s).
Proof.
  induction s as [|x s IH]; intros H; [ reflexivity |].
  simpl. f_equal.
  - specialize (H 0%nat). simpl in H. apply H. simpl. lia.
  - apply IH. intros k Hk. specialize (H (S k)). simpl in H. apply H. simpl. lia.
Qed.

Lemma not_all_ones_sum : forall l, binary l -> l <> repeat 1 (length l) ->
  ones_count l < Z.of_nat (length l).
Proof.
  intros l Hb Hne.
  destruct (dom_sum l (repeat 1 (length l))
              (eq_sym (repeat_length 1 (length l))) Hb (binary_repeat1 _)
              (dom_all_ones l)) as [Hle Heq].
  rewrite ones_count_repeat1 in Hle, Heq.
  destruct (Z.eq_dec (ones_count l) (Z.of_nat (length l))) as [E | E].
  - exfalso. apply Hne. apply Heq. exact E.
  - lia.
Qed.

Lemma binary_zero_witness : forall l, binary l -> ones_count l < Z.of_nat (length l) ->
  exists k, (k < length l)%nat /\ nth k l 0 = 0.
Proof.
  induction l as [|x l IH]; intros Hb Hlt.
  - simpl in Hlt. lia.
  - inversion Hb as [| x0 l0 Hx Hl]; subst.
    destruct Hx as [Hx | Hx]; subst.
    + exists 0%nat. split; [ simpl; lia | reflexivity ].
    + assert (Hlt' : ones_count l < Z.of_nat (length l)).
      { unfold ones_count in *. cbn [fold_right length] in Hlt. lia. }
      destruct (IH Hl Hlt') as [k [Hk Hv]].
      exists (S k). split; [ simpl; lia | simpl; exact Hv ].
Qed.

(* ---------- fill ---------- *)

Lemma fill_from_length : forall l k i j, length (fill_from k i j l) = length l.
Proof.
  induction l as [|x l IH]; intros k i j; [ reflexivity |].
  cbn [fill_from length]. f_equal. apply IH.
Qed.

Lemma fill_length : forall s i j, length (fill s i j) = length s.
Proof. intros. apply fill_from_length. Qed.

Lemma fill_from_nth : forall l k n i j, (n < length l)%nat ->
  nth n (fill_from k i j l) 0 =
  (if andb (Nat.leb i (k + n)) (Nat.leb (k + n) j) then 1 else nth n l 0).
Proof.
  induction l as [|x l IH]; intros k n i j Hn; [ cbn [length] in Hn; lia |].
  destruct n as [|n].
  - cbn [fill_from nth]. rewrite Nat.add_0_r. reflexivity.
  - cbn [fill_from nth]. cbn [length] in Hn.
    rewrite (IH (S k) n i j ltac:(lia)).
    replace (S k + n)%nat with (k + S n)%nat by lia. reflexivity.
Qed.

Lemma fill_nth : forall s i j n, (n < length s)%nat ->
  nth n (fill s i j) 0 = (if andb (Nat.leb i n) (Nat.leb n j) then 1 else nth n s 0).
Proof.
  intros s i j n Hn. unfold fill.
  rewrite (fill_from_nth s 0 n i j Hn). reflexivity.
Qed.

Lemma fill_binary : forall s i j, binary s -> binary (fill s i j).
Proof.
  intros s i j Hb. apply nth_binary. intros k Hk.
  rewrite fill_length in Hk. rewrite (fill_nth s i j k Hk).
  destruct (andb (Nat.leb i k) (Nat.leb k j)).
  - right; reflexivity.
  - apply binary_nth. exact Hb.
Qed.

Lemma dom_fill : forall s i j, dom s (fill s i j).
Proof.
  intros s i j k Hk.
  assert (Hlt : (k < length s)%nat) by (apply nth_one_lt with (s := s); exact Hk).
  rewrite (fill_nth s i j k Hlt).
  destruct (andb (Nat.leb i k) (Nat.leb k j)); [ reflexivity | exact Hk ].
Qed.

(* ---------- window ---------- *)

Lemma window_length : forall s i j, (S j <= length s)%nat ->
  length (window s i j) = (S j - i)%nat.
Proof.
  intros s i j H. unfold window.
  rewrite length_firstn, length_skipn. lia.
Qed.

Lemma window_nth : forall s i j k, (k < S j - i)%nat ->
  nth k (window s i j) 0 = nth (i + k) s 0.
Proof.
  intros s i j k Hk. unfold window.
  rewrite (nth_firstn (skipn i s) k (S j - i) 0 Hk).
  rewrite nth_skipn. reflexivity.
Qed.

Lemma binary_skipn : forall n s, binary s -> binary (skipn n s).
Proof.
  induction n as [|n IH]; intros s Hb; [ exact Hb |].
  destruct s as [|x s]; [ exact Hb |].
  cbn [skipn]. apply IH. inversion Hb; assumption.
Qed.

Lemma binary_firstn : forall n s, binary s -> binary (firstn n s).
Proof.
  induction n as [|n IH]; intros s Hb; [ constructor |].
  destruct s as [|x s]; [ constructor |].
  cbn [firstn]. inversion Hb as [| x0 l0 Hx Hs]; subst.
  constructor; [ exact Hx | apply IH; exact Hs ].
Qed.

Lemma window_binary : forall s i j, binary s -> binary (window s i j).
Proof.
  intros. unfold window. apply binary_firstn. apply binary_skipn. assumption.
Qed.

Lemma window_dom : forall s t i j, (S j <= length s)%nat -> (S j <= length t)%nat ->
  dom s t -> dom (window s i j) (window t i j).
Proof.
  intros s t i j Hs Ht Hd k Hk.
  assert (Hlt : (k < S j - i)%nat).
  { pose proof (nth_one_lt _ _ Hk) as H. rewrite (window_length s i j Hs) in H. exact H. }
  rewrite (window_nth t i j k Hlt).
  rewrite (window_nth s i j k Hlt) in Hk.
  apply Hd. exact Hk.
Qed.

(* ---------- mergeable ---------- *)

Lemma mergeable_inv : forall s i j, mergeable s i j = true ->
  (i < j)%nat /\ nth i s 0 = 1 /\ nth j s 0 = 1 /\
  2 * ones_count (window s i j) >= Z.of_nat (S j - i) /\
  ones_count (window s i j) < Z.of_nat (S j - i).
Proof.
  intros s i j H. unfold mergeable in H.
  repeat rewrite Bool.andb_true_iff in H.
  destruct H as [H1 [H2 [H3 [H4 H5]]]].
  apply Nat.ltb_lt in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3.
  apply Z.geb_le in H4. apply Z.ltb_lt in H5.
  unfold ones_count. repeat split; try assumption; lia.
Qed.

Lemma mergeable_intro : forall s i j,
  (i < j)%nat -> nth i s 0 = 1 -> nth j s 0 = 1 ->
  2 * ones_count (window s i j) >= Z.of_nat (S j - i) ->
  ones_count (window s i j) < Z.of_nat (S j - i) ->
  mergeable s i j = true.
Proof.
  intros s i j H1 H2 H3 H4 H5. unfold mergeable, ones_count in *.
  repeat rewrite Bool.andb_true_iff. repeat split.
  - apply Nat.ltb_lt. exact H1.
  - apply Z.eqb_eq. exact H2.
  - apply Z.eqb_eq. exact H3.
  - apply Z.geb_le. lia.
  - apply Z.ltb_lt. lia.
Qed.

(* ---------- one_step ---------- *)

Lemma in_pairs : forall n i j, In (i, j) (pairs n) <-> ((i < n)%nat /\ (j < n)%nat).
Proof.
  intros n i j. unfold pairs. rewrite in_flat_map. split.
  - intros [i0 [Hi0 Hin]]. rewrite in_map_iff in Hin.
    destruct Hin as [j0 [Heq Hj0]]. injection Heq as Hi Hj. subst.
    rewrite in_seq in Hi0. rewrite in_seq in Hj0. lia.
  - intros [Hi Hj]. exists i. split.
    + rewrite in_seq. lia.
    + rewrite in_map_iff. exists j. split; [ reflexivity | rewrite in_seq; lia ].
Qed.

Lemma filter_cons_inv : forall {A : Type} (f : A -> bool) (l : list A) p rest,
  filter f l = p :: rest -> In p l /\ f p = true.
Proof.
  intros A f l. induction l as [|x l IH]; intros p rest H; [ discriminate |].
  cbn [filter] in H. destruct (f x) eqn:Hfx.
  - injection H as Hp Hr. subst. split; [ left; reflexivity | exact Hfx ].
  - destruct (IH p rest H) as [Hin Hf]. split; [ right; exact Hin | exact Hf ].
Qed.

Lemma one_step_inv : forall s s', one_step s = Some s' ->
  exists i j, mergeable s i j = true /\ (i < length s)%nat /\ (j < length s)%nat /\
              s' = fill s i j.
Proof.
  intros s s' H. unfold one_step in H.
  destruct (filter (fun p => mergeable s (fst p) (snd p)) (pairs (length s)))
    as [|p rest] eqn:E; [ discriminate |].
  destruct (filter_cons_inv _ _ p rest E) as [Hin Hf].
  destruct p as [i j]. cbn [fst snd] in *.
  rewrite in_pairs in Hin.
  injection H as H. exists i, j. repeat split; try tauto. symmetry. exact H.
Qed.

Lemma one_step_none_not_mergeable : forall T i j, one_step T = None ->
  (i < length T)%nat -> (j < length T)%nat -> mergeable T i j = false.
Proof.
  intros T i j H Hi Hj. unfold one_step in H.
  destruct (filter (fun p => mergeable T (fst p) (snd p)) (pairs (length T)))
    as [|p rest] eqn:E; [| discriminate ].
  destruct (mergeable T i j) eqn:Hm; [| reflexivity ].
  exfalso.
  assert (Hin : In (i, j) (filter (fun p => mergeable T (fst p) (snd p)) (pairs (length T)))).
  { rewrite filter_In. split; [ apply in_pairs; tauto | cbn [fst snd]; exact Hm ]. }
  rewrite E in Hin. inversion Hin.
Qed.

Lemma one_step_progress : forall s s', binary s -> one_step s = Some s' ->
  length s' = length s /\ binary s' /\ dom s s' /\ ones_count s < ones_count s'.
Proof.
  intros s s' Hb H.
  destruct (one_step_inv s s' H) as [i [j [Hm [Hi [Hj Hs']]]]]. subst s'.
  destruct (mergeable_inv s i j Hm) as [Hij [Hni [Hnj [Hge Hlt]]]].
  assert (Hlen : (S j <= length s)%nat) by lia.
  assert (Hwl : length (window s i j) = (S j - i)%nat) by (apply window_length; exact Hlen).
  assert (Hwlt : ones_count (window s i j) < Z.of_nat (length (window s i j)))
    by (rewrite Hwl; exact Hlt).
  destruct (binary_zero_witness _ (window_binary s i j Hb) Hwlt) as [k [Hk Hz]].
  rewrite Hwl in Hk.
  rewrite (window_nth s i j k Hk) in Hz.
  assert (Hne : s <> fill s i j).
  { intros Heq.
    assert (Hik : (i + k < length s)%nat) by lia.
    pose proof (fill_nth s i j (i + k) Hik) as Hf.
    rewrite <- Heq in Hf.
    rewrite Hz in Hf.
    assert (Hb1 : Nat.leb i (i + k) = true) by (apply Nat.leb_le; lia).
    assert (Hb2 : Nat.leb (i + k) j = true) by (apply Nat.leb_le; lia).
    rewrite Hb1, Hb2 in Hf. cbn [andb] in Hf. discriminate. }
  split; [ apply fill_length |].
  split; [ apply fill_binary; exact Hb |].
  split; [ apply dom_fill |].
  destruct (dom_sum s (fill s i j) (eq_sym (fill_length s i j)) Hb
              (fill_binary s i j Hb) (dom_fill s i j)) as [Hle Heq].
  destruct (Z.eq_dec (ones_count s) (ones_count (fill s i j))) as [E | E].
  - exfalso. apply Hne. apply Heq. exact E.
  - lia.
Qed.

(* ---------- fuel ---------- *)

Lemma saturate_fuel_props : forall k s, binary s ->
  length (saturate_fuel k s) = length s /\ binary (saturate_fuel k s) /\
  dom s (saturate_fuel k s).
Proof.
  induction k as [|k IH]; intros s Hb.
  - cbn [saturate_fuel]. split; [ reflexivity | split; [ exact Hb | apply dom_refl ] ].
  - cbn [saturate_fuel]. destruct (one_step s) as [s'|] eqn:E.
    + destruct (one_step_progress s s' Hb E) as [Hl [Hb' [Hd _]]].
      destruct (IH s' Hb') as [Hl2 [Hb2 Hd2]].
      split; [| split ].
      * rewrite Hl2. exact Hl.
      * exact Hb2.
      * apply (dom_trans s s'); assumption.
    + split; [ reflexivity | split; [ exact Hb | apply dom_refl ] ].
Qed.

Lemma saturate_fuel_fix : forall k s, binary s ->
  Z.of_nat (length s) - ones_count s <= Z.of_nat k -> one_step (saturate_fuel k s) = None.
Proof.
  induction k as [|k IH]; intros s Hb Hm.
  - cbn [saturate_fuel]. destruct (one_step s) as [s'|] eqn:E; [| reflexivity ].
    exfalso.
    destruct (one_step_progress s s' Hb E) as [Hl [Hb' [_ Hlt]]].
    pose proof (ones_le_length s' Hb') as H1.
    rewrite Hl in H1. cbn [Z.of_nat] in Hm. lia.
  - cbn [saturate_fuel]. destruct (one_step s) as [s'|] eqn:E; [| exact E ].
    destruct (one_step_progress s s' Hb E) as [Hl [Hb' [_ Hlt]]].
    apply (IH s' Hb').
    rewrite Hl. rewrite Nat2Z.inj_succ in Hm. lia.
Qed.

Lemma saturate_fix : forall s, binary s -> one_step (saturate s) = None.
Proof.
  intros s Hb. unfold saturate. apply saturate_fuel_fix; [ exact Hb |].
  pose proof (ones_count_nonneg s Hb). lia.
Qed.

Lemma saturate_props : forall s, binary s ->
  length (saturate s) = length s /\ binary (saturate s) /\ dom s (saturate s).
Proof. intros s Hb. unfold saturate. apply saturate_fuel_props. exact Hb. Qed.

(* ---------- Z / nat bridges ---------- *)

Lemma Zlen_nonneg : forall {A : Type} (l : list A), 0 <= Zlength l.
Proof. intros A l. rewrite Zlength_correct. lia. Qed.

Lemma nat_Z_leb : forall (a b : nat), Z.leb (Z.of_nat a) (Z.of_nat b) = Nat.leb a b.
Proof.
  intros a b. destruct (Nat.leb a b) eqn:E.
  - apply Z.leb_le. apply Nat.leb_le in E. lia.
  - apply Z.leb_gt. apply Nat.leb_gt in E. lia.
Qed.

Lemma sublist_window : forall (s : list Z) i j, 0 <= i -> 0 <= j ->
  sublist i (j + 1) s = window s (Z.to_nat i) (Z.to_nat j).
Proof.
  intros s i j Hi Hj. unfold sublist, window.
  replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  apply skipn_firstn_comm.
Qed.

Lemma Znth_nth : forall (s : list Z) (k : nat), Znth (Z.of_nat k) s 0 = nth k s 0.
Proof. intros s k. unfold Znth. rewrite Nat2Z.id. reflexivity. Qed.

(* ---------- one_step yields a genuine SpreadStep ---------- *)

Lemma mergeable_spreadstep : forall s I J, (J < length s)%nat ->
  mergeable s I J = true -> SpreadStep s (fill s I J).
Proof.
  intros s I J HJ Hm.
  destruct (mergeable_inv s I J Hm) as [Hij [Hni [Hnj [Hge _]]]].
  exists (Z.of_nat I), (Z.of_nat J).
  assert (Hlen : Zlength s = Z.of_nat (length s)) by apply Zlength_correct.
  assert (Hw : Z.of_nat (S J - I) = Z.of_nat J - Z.of_nat I + 1) by lia.
  split; [| split; [| split; [| split; [| split; [| split ] ] ] ] ].
  - split; lia.
  - rewrite Hlen. lia.
  - rewrite Znth_nth. exact Hni.
  - rewrite Znth_nth. exact Hnj.
  - rewrite (sublist_window s (Z.of_nat I) (Z.of_nat J) ltac:(lia) ltac:(lia)).
    rewrite !Nat2Z.id.
    unfold ones_count in Hge. lia.
  - rewrite !Zlength_correct. rewrite fill_length. reflexivity.
  - intros q Hq.
    assert (Hq0 : q = Z.of_nat (Z.to_nat q)) by lia.
    remember (Z.to_nat q) as k eqn:Hk.
    assert (Hklt : (k < length s)%nat) by (rewrite Hlen in Hq; lia).
    rewrite Hq0. rewrite !Znth_nth.
    rewrite (fill_nth s I J k Hklt).
    rewrite !nat_Z_leb. reflexivity.
Qed.

Lemma one_step_spreadstep : forall s s', one_step s = Some s' -> SpreadStep s s'.
Proof.
  intros s s' H.
  destruct (one_step_inv s s' H) as [i [j [Hm [_ [Hj Hs']]]]]. subst s'.
  apply mergeable_spreadstep; assumption.
Qed.

(* ---------- chains ---------- *)

Inductive Chain : list Z -> list Z -> Prop :=
| chain_refl : forall s, Chain s s
| chain_step : forall a b c, SpreadStep a b -> Chain b c -> Chain a c.

Lemma chain_saturate_fuel : forall k s, Chain s (saturate_fuel k s).
Proof.
  induction k as [|k IH]; intros s.
  - cbn [saturate_fuel]. apply chain_refl.
  - cbn [saturate_fuel]. destruct (one_step s) as [s'|] eqn:E.
    + apply (chain_step s s'); [ apply one_step_spreadstep; exact E | apply IH ].
    + apply chain_refl.
Qed.

Lemma chain_rated : forall s t, Chain s t -> Forall (fun x => x = 1) t -> Rated s.
Proof.
  intros s t Hc. induction Hc as [s | a b c Hstep Hc IH]; intros Hall.
  - exists [s]. split; [| split; [| split ] ].
    + intros H. discriminate.
    + rewrite Znth0_cons. reflexivity.
    + rewrite Zlength_cons, Zlength_nil.
      replace (Z.succ 0 - 1) with 0 by lia.
      rewrite Znth0_cons. exact Hall.
    + intros i Hi. rewrite Zlength_cons, Zlength_nil in Hi. lia.
  - destruct (IH Hall) as [st [Hne [H0 [Hlast Hsteps]]]].
    assert (Hpos : 0 < Zlength st).
    { destruct st as [|x st]; [ contradiction |].
      rewrite Zlength_cons. pose proof (Zlen_nonneg st). lia. }
    exists (a :: st). split; [| split; [| split ] ].
    + intros H. discriminate.
    + rewrite Znth0_cons. reflexivity.
    + rewrite Zlength_cons.
      replace (Z.succ (Zlength st) - 1) with (Zlength st) by lia.
      rewrite Znth_cons by lia. exact Hlast.
    + intros i Hi. rewrite Zlength_cons in Hi.
      destruct (Z.eq_dec i 0) as [Hi0 | Hi0].
      * subst i. rewrite Znth0_cons.
        replace (0 + 1) with 1 by lia.
        rewrite Znth_cons by lia.
        replace (1 - 1) with 0 by lia.
        rewrite H0. exact Hstep.
      * rewrite Znth_cons by lia.
        rewrite Znth_cons with (n := i + 1) by lia.
        replace (i + 1 - 1) with (i - 1 + 1) by lia.
        apply Hsteps. lia.
Qed.

Lemma rated_chain : forall st, st <> [] ->
  (forall i, 0 <= i < Zlength st - 1 -> SpreadStep (Znth i st []) (Znth (i + 1) st [])) ->
  Chain (Znth 0 st []) (Znth (Zlength st - 1) st []).
Proof.
  induction st as [|a st IH]; intros Hne Hsteps; [ contradiction |].
  destruct st as [|b st].
  - rewrite Zlength_cons, Zlength_nil.
    replace (Z.succ 0 - 1) with 0 by lia.
    apply chain_refl.
  - assert (Hpos : 0 < Zlength (b :: st)).
    { rewrite Zlength_cons. pose proof (Zlen_nonneg st). lia. }
    assert (Hstep0 : SpreadStep a b).
    { pose proof (Hsteps 0 ltac:(rewrite Zlength_cons; lia)) as H.
      rewrite Znth0_cons in H.
      replace (0 + 1) with 1 in H by lia.
      rewrite Znth_cons in H by lia.
      replace (1 - 1) with 0 in H by lia.
      rewrite Znth0_cons in H. exact H. }
    assert (Hsteps' : forall i, 0 <= i < Zlength (b :: st) - 1 ->
              SpreadStep (Znth i (b :: st) []) (Znth (i + 1) (b :: st) [])).
    { intros i Hi.
      pose proof (Hsteps (i + 1) ltac:(rewrite Zlength_cons; lia)) as H.
      rewrite Znth_cons in H by lia.
      replace (i + 1 - 1) with i in H by lia.
      rewrite Znth_cons with (n := i + 1 + 1) in H by lia.
      replace (i + 1 + 1 - 1) with (i + 1) in H by lia.
      exact H. }
    pose proof (IH ltac:(discriminate) Hsteps') as Hc.
    rewrite Znth0_cons in Hc.
    apply (chain_step a b); [ exact Hstep0 |].
    rewrite Zlength_cons.
    replace (Z.succ (Zlength (b :: st)) - 1) with (Zlength (b :: st)) by lia.
    rewrite Znth_cons by lia.
    exact Hc.
Qed.

(* ---------- the key claim: a saturated dominator stays a dominator ---------- *)

Lemma spread_dom : forall a b T, binary a -> binary T -> length a = length T ->
  dom a T -> one_step T = None -> SpreadStep a b ->
  dom b T /\ binary b /\ length b = length a.
Proof.
  intros a b T Hba HbT Hlen Hd Hnone HS.
  destruct HS as [i [j [[Hi0 Hij] [Hj [Hai [Haj [Hsum [HlenB Hq]]]]]]]].
  remember (Z.to_nat i) as I eqn:HI.
  remember (Z.to_nat j) as J eqn:HJ.
  assert (HiI : i = Z.of_nat I) by (subst I; lia).
  assert (HjJ : j = Z.of_nat J) by (subst J; lia).
  assert (HIJ : (I < J)%nat) by lia.
  rewrite Zlength_correct in Hj.
  assert (HJlen : (J < length a)%nat) by lia.
  assert (HlenBn : length b = length a)
    by (rewrite !Zlength_correct in HlenB; lia).
  (* pointwise description of b *)
  assert (Hbn : forall k, (k < length a)%nat ->
            nth k b 0 = (if andb (Nat.leb I k) (Nat.leb k J) then 1 else nth k a 0)).
  { intros k Hk.
    specialize (Hq (Z.of_nat k) ltac:(rewrite Zlength_correct; lia)).
    rewrite !Znth_nth in Hq. rewrite HiI, HjJ, !nat_Z_leb in Hq. exact Hq. }
  assert (Hbb : binary b).
  { apply nth_binary. intros k Hk. rewrite HlenBn in Hk.
    rewrite (Hbn k Hk).
    destruct (andb (Nat.leb I k) (Nat.leb k J));
      [ right; reflexivity | apply binary_nth; exact Hba ]. }
  (* the window in T is forced to be all ones *)
  assert (HaI : nth I a 0 = 1) by (rewrite <- Znth_nth, <- HiI; exact Hai).
  assert (HaJ : nth J a 0 = 1) by (rewrite <- Znth_nth, <- HjJ; exact Haj).
  assert (HTI : nth I T 0 = 1) by (apply Hd; exact HaI).
  assert (HTJ : nth J T 0 = 1) by (apply Hd; exact HaJ).
  assert (HSJa : (S J <= length a)%nat) by lia.
  assert (HSJT : (S J <= length T)%nat) by lia.
  pose proof (window_length a I J HSJa) as Hwa.
  pose proof (window_length T I J HSJT) as HwT.
  rewrite (sublist_window a i j ltac:(lia) ltac:(lia)) in Hsum.
  rewrite <- HI, <- HJ in Hsum.
  assert (HleW : ones_count (window a I J) <= ones_count (window T I J)).
  { apply dom_le.
    - rewrite Hwa, HwT. reflexivity.
    - apply window_binary; exact Hba.
    - apply window_binary; exact HbT.
    - apply window_dom; assumption. }
  unfold ones_count in HleW.
  assert (Hallw : window T I J = repeat 1 (length (window T I J))).
  { destruct (list_eq_dec Z.eq_dec (window T I J) (repeat 1 (length (window T I J))))
      as [E | E]; [ exact E |].
    exfalso.
    pose proof (not_all_ones_sum _ (window_binary T I J HbT) E) as Hlt.
    rewrite HwT in Hlt.
    assert (Hm : mergeable T I J = true).
    { apply mergeable_intro; try assumption; unfold ones_count; lia. }
    rewrite (one_step_none_not_mergeable T I J Hnone ltac:(lia) ltac:(lia)) in Hm.
    discriminate. }
  assert (HT1 : forall k, (k < S J - I)%nat -> nth (I + k) T 0 = 1).
  { intros k Hk. rewrite <- (window_nth T I J k Hk).
    rewrite Hallw, HwT. apply nth_repeat1. exact Hk. }
  split; [| split; [ exact Hbb | exact HlenBn ] ].
  intros k Hk.
  assert (Hklt : (k < length a)%nat)
    by (pose proof (nth_one_lt _ _ Hk); lia).
  rewrite (Hbn k Hklt) in Hk.
  destruct (andb (Nat.leb I k) (Nat.leb k J)) eqn:Ecase.
  - rewrite Bool.andb_true_iff in Ecase. destruct Ecase as [E1 E2].
    apply Nat.leb_le in E1. apply Nat.leb_le in E2.
    replace k with (I + (k - I))%nat by lia.
    apply HT1. lia.
  - apply Hd. exact Hk.
Qed.

Lemma chain_dom : forall u t, Chain u t -> forall T, binary T -> one_step T = None ->
  length u = length T -> binary u -> dom u T ->
  dom t T /\ length t = length T /\ binary t.
Proof.
  intros u t Hc. induction Hc as [s | a b c Hstep Hc IH];
    intros T HbT Hnone Hlen Hbu Hd.
  - split; [ exact Hd | split; [ exact Hlen | exact Hbu ] ].
  - destruct (spread_dom a b T Hbu HbT Hlen Hd Hnone Hstep) as [Hdb [Hbb Hlb]].
    apply IH; try assumption. rewrite Hlb. exact Hlen.
Qed.

Lemma Forall1_nth : forall (t : list Z) k, Forall (fun x => x = 1) t ->
  (k < length t)%nat -> nth k t 0 = 1.
Proof.
  intros t k H Hk. rewrite Forall_forall in H. apply H. apply nth_In. exact Hk.
Qed.

Lemma Forall1_repeat : forall n, Forall (fun x => x = 1) (repeat 1 n).
Proof.
  induction n as [|n IH]; cbn [repeat]; constructor; [ reflexivity | exact IH ].
Qed.

(* ===================== L1 : the keystone ===================== *)
(* Validated by Compute against brute force for all s with |s| <= 14. *)
Theorem rated_iff_saturate :
  forall s, binary s -> (Rated s <-> saturate s = all_ones (length s)).
Proof.
  intros s Hb. split.
  - intros [st [Hne [H0 [Hlast Hsteps]]]].
    pose proof (rated_chain st Hne Hsteps) as Hc. rewrite H0 in Hc.
    destruct (saturate_props s Hb) as [HlT [HbT HdT]].
    destruct (chain_dom s _ Hc (saturate s) HbT (saturate_fix s Hb)
                (eq_sym HlT) Hb HdT) as [Hdt [Hlt Hbt]].
    unfold all_ones. rewrite <- HlT.
    apply all_ones_of_nth. intros k Hk.
    apply Hdt. apply Forall1_nth; [ exact Hlast |]. rewrite Hlt. exact Hk.
  - intros Heq. apply (chain_rated s (saturate s)).
    + unfold saturate. apply chain_saturate_fuel.
    + rewrite Heq. unfold all_ones. apply Forall1_repeat.
Qed.

Corollary rated_dec_correct :
  forall s, binary s -> (Rated s <-> rated_bool s = true).
Proof.
  intros s Hb. unfold rated_bool.
  destruct (list_eq_dec Z.eq_dec (saturate s) (all_ones (length s))) as [E|E].
  - split; [reflexivity | intros _]. apply (rated_iff_saturate s Hb). exact E.
  - split; [ intros HR; exfalso; apply E; apply (rated_iff_saturate s Hb); exact HR
           | discriminate ].
Qed.

(* ===================== combinatorial layer (validated) ===================== *)

Fixpoint ones_prefix (l : list Z) : nat :=
  match l with
  | nil => O
  | x :: tl => if Z.eqb x 1 then S (ones_prefix tl) else O
  end.

Definition stop_len (s : list Z) : nat := ones_prefix (saturate s).

(* tails of length d that stay blocked behind a merged block of j ones *)
Definition cntW (d j : nat) : Z :=
  Z.of_nat (length (filter
    (fun t => Nat.eqb (stop_len (all_ones j ++ t)) j) (all_strings d))).

(* strings of length i starting with 1 whose saturation stops exactly at j *)
Definition count_stop (i j : nat) : Z :=
  Z.of_nat (length (filter
    (fun s => andb (Z.eqb (nth 0 s 0) 1) (Nat.eqb (stop_len s) j)) (all_strings i))).

(* ---------- from comb.v ---------- *)

(* strings of length L starting with 1 whose saturation stops at or before t *)
Definition cntP (L t : nat) : Z :=
  Z.of_nat (length (filter
    (fun s => andb (Z.eqb (nth 0 s 0) 1) (Nat.leb (stop_len s) t)) (all_strings L))).

(* the C's Q accumulator, combinatorially: split D = L + t with t < L *)
Definition cntQ (D : nat) : Z :=
  fold_right Z.add 0
    (map (fun L => if Nat.ltb (D - L) L then cntP L (D - L) else 0) (seq 1 D)).

Definition Lmax_of (d j : nat) : Z :=
  Z.of_nat d - (Z.of_nat d + Z.of_nat j + 2) / 2.
Definition D_of (d j : nat) : Z := Z.of_nat d - Z.of_nat j - 1.

Definition Wformula (d j : nat) : Z :=
  1 + (if Z.leb 1 (Lmax_of d j) then 2 ^ (Lmax_of d j) - 1 else 0)
    + (if Z.leb 0 (D_of d j) then cntQ (Z.to_nat (D_of d j)) else 0).

(* ---------- from L2.v ---------- *)


(* ================================================================== *)
(* 0. Support lemmas copied from the sealed group_10__final-spec file. *)
(* ================================================================== *)

Lemma Zlength_map_L2 : forall {A B : Type} (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros. rewrite !Zlength_correct, length_map. reflexivity.
Qed.

Lemma fold_right_count_Zlength_L2 :
  forall {A : Type} (l : list A),
    fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l = Zlength l.
Proof.
  induction l as [|a l IH]; cbn [fold_right].
  - rewrite Zlength_nil. reflexivity.
  - rewrite IH, Zlength_cons. lia.
Qed.

Lemma filter_map_comm_L2 :
  forall {A B : Type} (f : A -> B) (p : B -> bool) (l : list A),
    filter p (map f l) = map f (filter (fun x => p (f x)) l).
Proof.
  induction l as [|a l IH]; simpl.
  - reflexivity.
  - destruct (p (f a)); simpl; rewrite IH; reflexivity.
Qed.

Lemma map_Znth_Zrange_aux_L2 :
  forall {A : Type} (l : list A) (d : A) (low : Z),
    map (fun i => Znth (i - low) l d) (Zrange_aux low (length l)) = l.
Proof.
  induction l as [|a l IH]; intros d low; simpl.
  - reflexivity.
  - replace (low - low) with 0 by lia.
    rewrite Znth0_cons.
    f_equal.
    transitivity (map (fun i => Znth (i - (low + 1)) l d)
                      (Zrange_aux (low + 1) (length l))).
    + apply map_ext_in.
      intros i Hi.
      apply In_Zrange_aux_lb in Hi.
      rewrite Znth_cons by lia.
      f_equal. lia.
    + apply IH.
Qed.

Lemma map_Znth_Zrange_L2 :
  forall {A : Type} (l : list A) (d : A),
    map (fun i => Znth i l d) (Zrange 0 (Zlength l)) = l.
Proof.
  intros A l d. unfold Zrange.
  replace (Z.to_nat (Zlength l - 0)) with (length l)
    by (rewrite Zlength_correct; lia).
  transitivity (map (fun i => Znth (i - 0) l d) (Zrange_aux 0 (length l))).
  - apply map_ext. intros i. f_equal. lia.
  - apply map_Znth_Zrange_aux_L2.
Qed.

Lemma Spec_intro_L2 :
  forall n m out : Z,
    0 <= n ->
    (forall Hf : Finite (fun s : list Z =>
                   (Zlength s = n /\ Forall (fun x : Z => x = 0 \/ x = 1) s)
                   /\ Rated s),
        out = (@set_card (list Z) _ Hf) mod m) ->
    Spec n m out.
Proof.
  intros n m out Hn Hcount.
  assert (Hbin : Finite (fun x : Z => x = 0 \/ x = 1)).
  { refine {| enum := 0 :: 1 :: nil |}.
    - intros x. simpl. split.
      + intros [Hx | Hx]; subst; tauto.
      + intros [Hx | [Hx | Hx]]; subst; tauto.
    - constructor.
      + simpl. intros [Hx | Hx]; [lia | contradiction].
      + constructor; [simpl; tauto | constructor]. }
  pose (Hbl := @Finite_bounded_lists Z n (fun x : Z => x = 0 \/ x = 1) Hbin).
  pose (ss := @enum (list Z) _ Hbl).
  exists ss.
  split.
  - unfold AllBinary. split.
    + apply (@enum_nodup (list Z) _ Hbl).
    + intros s. split.
      * intros Hin. apply (@enum_ok (list Z) _ Hbl s). exact Hin.
      * intros Hs. apply (@enum_ok (list Z) _ Hbl s). exact Hs.
  - pose (Hsub := @Finite_subset (list Z)
                    (fun s : list Z =>
                       Zlength s = n /\ Forall (fun x : Z => x = 0 \/ x = 1) s)
                    Rated Hbl).
    rewrite (Hcount Hsub).
    f_equal.
    unfold set_card, sum.
    rewrite !fold_right_count_Zlength_L2.
    unfold Hsub.
    cbn [enum Finite_subset finite_Z_range'].
    fold ss.
    assert (Hfe :
      filter (fun x : list Z => if prop_dec (Rated x) then true else false) ss =
      map (fun i : Z => Znth i ss nil)
        (filter
           (fun x : Z => if prop_dec (Rated (Znth x ss nil)) then true else false)
           (Zrange 0 (Zlength ss)))).
    { transitivity
        (filter (fun x : list Z => if prop_dec (Rated x) then true else false)
           (map (fun i : Z => Znth i ss nil) (Zrange 0 (Zlength ss)))).
      - rewrite map_Znth_Zrange_L2. reflexivity.
      - apply (filter_map_comm_L2 (fun i : Z => Znth i ss nil)
                 (fun x : list Z => if prop_dec (Rated x) then true else false)
                 (Zrange 0 (Zlength ss))). }
    rewrite Hfe, Zlength_map_L2. reflexivity.
Qed.

(* ================================================================== *)
(* 1. [all_strings] enumerates the binary strings, without duplicates. *)
(* ================================================================== *)

Lemma all_strings_fold_len :
  forall (l1 l2 : list nat), length l1 = length l2 ->
    fold_right (fun _ acc => flat_map (fun s : list Z => [0 :: s; 1 :: s]) acc)
               [[]] l1
  = fold_right (fun _ acc => flat_map (fun s : list Z => [0 :: s; 1 :: s]) acc)
               [[]] l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2 H.
  - destruct l2 as [|y l2]; [reflexivity | cbn [length] in H; discriminate].
  - destruct l2 as [|y l2]; [cbn [length] in H; discriminate |].
    cbn [length] in H. injection H as H.
    cbn [fold_right]. rewrite (IH l2 H). reflexivity.
Qed.

Lemma all_strings_S : forall n,
  all_strings (S n) = flat_map (fun s : list Z => [0 :: s; 1 :: s]) (all_strings n).
Proof.
  intros n. unfold all_strings. cbn [seq fold_right].
  f_equal. apply all_strings_fold_len. rewrite !length_seq. reflexivity.
Qed.

Lemma in_flat_cons_inv : forall (b : Z) (a : list Z) (l : list (list Z)),
  In (b :: a) (flat_map (fun s : list Z => [0 :: s; 1 :: s]) l) -> In a l.
Proof.
  intros b a l H. rewrite in_flat_map in H.
  destruct H as [t [Ht Hin]].
  cbn [In] in Hin.
  destruct Hin as [E | [E | []]]; injection E as E1 E2; subst; exact Ht.
Qed.

Lemma in_all_strings : forall n s,
  In s (all_strings n) <-> length s = n /\ binary s.
Proof.
  induction n as [|n IH]; intros s.
  - cbn [all_strings seq fold_right In]. split.
    + intros [H | []]. subst s. split; [reflexivity | constructor].
    + intros [Hl _]. destruct s as [|x s].
      * left. reflexivity.
      * cbn [length] in Hl. discriminate.
  - rewrite all_strings_S, in_flat_map. split.
    + intros [t [Ht Hin]].
      apply IH in Ht. destruct Ht as [Hl Hb].
      cbn [In] in Hin. destruct Hin as [E | [E | []]]; subst s.
      * split; [ cbn [length]; f_equal; exact Hl |].
        constructor; [ left; reflexivity | exact Hb ].
      * split; [ cbn [length]; f_equal; exact Hl |].
        constructor; [ right; reflexivity | exact Hb ].
    + intros [Hl Hb]. destruct s as [|x s]; [ cbn [length] in Hl; discriminate |].
      inversion Hb as [| x0 l0 Hx Hs]; subst.
      exists s. split.
      * apply IH. split; [ cbn [length] in Hl; lia | exact Hs ].
      * cbn [In]. destruct Hx as [Hx | Hx]; subst x; tauto.
Qed.

Lemma NoDup_all_strings : forall n, NoDup (all_strings n).
Proof.
  induction n as [|n IH].
  - cbn [all_strings seq fold_right]. constructor; [ intros [] | constructor ].
  - rewrite all_strings_S.
    induction IH as [| a l Ha Hl IH2].
    + cbn [flat_map]. constructor.
    + cbn [flat_map app]. constructor.
      * intros [E | Hin].
        -- discriminate.
        -- apply in_flat_cons_inv in Hin. contradiction.
      * constructor.
        -- intros Hin. apply in_flat_cons_inv in Hin. contradiction.
        -- exact IH2.
Qed.

(* ================================================================== *)
(* 2. Any NoDup list whose members are exactly the rated binary        *)
(*    strings of length n has cardinality [count_rated n].             *)
(* ================================================================== *)

Lemma perm_count : forall (n : nat) (l : list (list Z)),
  NoDup l ->
  (forall s, In s l <->
     ((Zlength s = Z.of_nat n /\ Forall (fun x : Z => x = 0 \/ x = 1) s)
      /\ Rated s)) ->
  Zlength l = count_rated n.
Proof.
  intros n l Hnd Hmem.
  unfold count_rated.
  rewrite Zlength_correct. f_equal.
  apply Permutation_length.
  apply NoDup_Permutation.
  - exact Hnd.
  - apply NoDup_filter_bool. apply NoDup_all_strings.
  - intros s. rewrite Hmem, filter_In, in_all_strings.
    split.
    + intros [[Hz Hb] Hr]. split; [ split |].
      * rewrite Zlength_correct in Hz. lia.
      * exact Hb.
      * apply (rated_dec_correct s Hb). exact Hr.
    + intros [[Hl Hb] Hr]. split; [ split |].
      * rewrite Zlength_correct. lia.
      * exact Hb.
      * apply (rated_dec_correct s Hb). exact Hr.
Qed.

(* Cardinality over the element-indexed predicate. *)
Lemma card_elem : forall (n : nat)
  (Hf : Finite (fun s : list Z =>
          (Zlength s = Z.of_nat n /\ Forall (fun x : Z => x = 0 \/ x = 1) s)
          /\ Rated s)),
  @set_card (list Z) _ Hf = count_rated n.
Proof.
  intros n Hf. unfold set_card, sum.
  rewrite fold_right_count_Zlength_L2.
  apply perm_count.
  - apply (@enum_nodup (list Z) _ Hf).
  - intros s. symmetry. apply (@enum_ok (list Z) _ Hf s).
Qed.

(* Cardinality over the index-indexed predicate used by [Spec], for an
   arbitrary [AllBinary] witness list. *)
Lemma card_index : forall (n : nat) (ss : list (list Z)),
  AllBinary (Z.of_nat n) ss ->
  forall (Hf : Finite (fun i : Z => 0 <= i < Zlength ss /\ Rated (Znth i ss []))),
    @set_card Z _ Hf = count_rated n.
Proof.
  intros n ss Hab Hf.
  destruct Hab as [Hnd Hmem].
  rewrite (set_card_irrel _ Hf
             (finite_Z_range' 0 (Zlength ss) (fun i => Rated (Znth i ss [])))).
  unfold set_card, sum.
  cbn [enum finite_Z_range'].
  rewrite fold_right_count_Zlength_L2.
  assert (Hfe :
    filter (fun x : list Z => if prop_dec (Rated x) then true else false) ss =
    map (fun i : Z => Znth i ss nil)
      (filter
         (fun x : Z => if prop_dec (Rated (Znth x ss nil)) then true else false)
         (Zrange 0 (Zlength ss)))).
  { transitivity
      (filter (fun x : list Z => if prop_dec (Rated x) then true else false)
         (map (fun i : Z => Znth i ss nil) (Zrange 0 (Zlength ss)))).
    - rewrite map_Znth_Zrange_L2. reflexivity.
    - apply (filter_map_comm_L2 (fun i : Z => Znth i ss nil)
               (fun x : list Z => if prop_dec (Rated x) then true else false)
               (Zrange 0 (Zlength ss))). }
  rewrite <- Zlength_map_L2 with (f := fun i : Z => Znth i ss nil).
  rewrite <- Hfe.
  apply perm_count.
  - apply NoDup_filter_bool. exact Hnd.
  - intros s. rewrite filter_In, Hmem.
    split.
    + intros [Hs Ht]. split; [ exact Hs |].
      destruct (prop_dec (Rated s)) as [Hr | Hr]; [ exact Hr | discriminate ].
    + intros [Hs Hr]. split; [ exact Hs |].
      destruct (prop_dec (Rated s)) as [Hr' | Hr']; [ reflexivity | contradiction ].
Qed.

(* ================================================================== *)
(* 3. The theorem.                                                     *)
(* ================================================================== *)

Theorem spec_iff_count :
  forall (n : nat) (m out : Z), 0 < m ->
    (Spec (Z.of_nat n) m out <-> out = count_rated n mod m).
Proof.
  intros n m out Hm. split.
  - intros [ss [Hab Hout]]. rewrite Hout. f_equal.
    apply (card_index n ss Hab).
  - intros Hout. apply Spec_intro_L2; [ lia |].
    intros Hf. rewrite (card_elem n Hf). exact Hout.
Qed.

(* The [Z]-indexed restatement; [0 <= n] is genuinely needed, since for
   n < 0 the only [AllBinary n] witness is [] (cardinality 0) whereas
   count_rated (Z.to_nat n) = count_rated 0 = 1. *)
Corollary spec_iff_count_Z :
  forall n m out : Z, 0 <= n -> 0 < m ->
    (Spec n m out <-> out = count_rated (Z.to_nat n) mod m).
Proof.
  intros n m out Hn Hm.
  pose proof (spec_iff_count (Z.to_nat n) m out Hm) as H.
  rewrite Z2Nat.id in H by lia.
  exact H.
Qed.


(* ---------- from L3a.v ---------- *)


(* ===================== basic facts about SpreadStep / Chain ===================== *)

Lemma spreadstep_basic : forall a b, SpreadStep a b ->
  length b = length a /\
  (forall k, (k < length a)%nat -> nth k b 0 = 1 \/ nth k b 0 = nth k a 0).
Proof.
  intros a b [i [j [[Hi0 Hij] [Hj [Hai [Haj [Hsum [Hlen Hq]]]]]]]].
  assert (Hl : length b = length a).
  { rewrite !Zlength_correct in Hlen. lia. }
  split; [ exact Hl |].
  intros k Hk.
  specialize (Hq (Z.of_nat k) ltac:(rewrite Zlength_correct; lia)).
  rewrite !Znth_nth in Hq. rewrite Hq.
  destruct (Z.leb i (Z.of_nat k) && Z.leb (Z.of_nat k) j)%bool.
  - left; reflexivity.
  - right; reflexivity.
Qed.

Lemma spreadstep_dom : forall a b, SpreadStep a b -> dom a b.
Proof.
  intros a b HS k Hk.
  destruct (spreadstep_basic a b HS) as [Hl Hp].
  assert (Hklt : (k < length a)%nat) by (apply nth_one_lt with (s := a); exact Hk).
  destruct (Hp k Hklt) as [H | H]; [ exact H | rewrite H; exact Hk ].
Qed.

Lemma spreadstep_binary : forall a b, SpreadStep a b -> binary a -> binary b.
Proof.
  intros a b HS Hb.
  destruct (spreadstep_basic a b HS) as [Hl Hp].
  apply nth_binary. intros k Hk. rewrite Hl in Hk.
  destruct (Hp k Hk) as [H | H].
  - right; exact H.
  - rewrite H. apply binary_nth. exact Hb.
Qed.

Lemma chain_basic : forall a b, Chain a b -> binary a ->
  length b = length a /\ binary b /\ dom a b.
Proof.
  intros a b Hc. induction Hc as [s | x y z Hstep Hc IH]; intros Hb.
  - split; [ reflexivity | split; [ exact Hb | apply dom_refl ] ].
  - destruct (spreadstep_basic x y Hstep) as [Hl _].
    assert (Hby : binary y) by (apply (spreadstep_binary x y); assumption).
    destruct (IH Hby) as [Hl2 [Hb2 Hd2]].
    split; [ rewrite Hl2; exact Hl |].
    split; [ exact Hb2 |].
    apply (dom_trans x y); [ apply spreadstep_dom; exact Hstep | exact Hd2 ].
Qed.

Lemma chain_trans : forall a b c, Chain a b -> Chain b c -> Chain a c.
Proof.
  intros a b c H. induction H as [s | x y z Hstep Hc IH]; intros H2.
  - exact H2.
  - apply (chain_step x y); [ exact Hstep | apply IH; exact H2 ].
Qed.

(* ===================== fill / window under append ===================== *)

Lemma fill_from_app : forall l1 l2 k i j,
  fill_from k i j (l1 ++ l2) = fill_from k i j l1 ++ fill_from (k + length l1) i j l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2 k i j.
  - cbn [app fill_from length]. rewrite Nat.add_0_r. reflexivity.
  - cbn [app fill_from length]. f_equal.
    rewrite (IH l2 (S k) i j). f_equal. f_equal. lia.
Qed.

Lemma fill_from_id : forall l k i j, (j < k)%nat -> fill_from k i j l = l.
Proof.
  induction l as [|x l IH]; intros k i j Hk; [ reflexivity |].
  cbn [fill_from].
  assert (E : Nat.leb k j = false) by (apply Nat.leb_gt; lia).
  rewrite E, Bool.andb_false_r. f_equal. apply IH. lia.
Qed.

Lemma fill_app : forall p t i j, (j < length p)%nat ->
  fill (p ++ t) i j = fill p i j ++ t.
Proof.
  intros p t i j Hj. unfold fill.
  rewrite fill_from_app. f_equal. apply fill_from_id. lia.
Qed.

Lemma window_app : forall p t i j, (i <= j)%nat -> (S j <= length p)%nat ->
  window (p ++ t) i j = window p i j.
Proof.
  intros p t i j Hij Hj. unfold window.
  rewrite skipn_app.
  replace (i - length p)%nat with 0%nat by lia.
  cbn [skipn].
  rewrite firstn_app.
  rewrite length_skipn.
  replace (S j - i - (length p - i))%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma mergeable_app : forall p t i j, (i < j)%nat -> (S j <= length p)%nat ->
  mergeable (p ++ t) i j = mergeable p i j.
Proof.
  intros p t i j Hij Hj. unfold mergeable.
  rewrite (window_app p t i j ltac:(lia) Hj).
  rewrite (app_nth1 p t 0 (n := i)) by lia.
  rewrite (app_nth1 p t 0 (n := j)) by lia.
  reflexivity.
Qed.

Lemma chain_lift : forall k p t, Chain (p ++ t) (saturate_fuel k p ++ t).
Proof.
  induction k as [|k IH]; intros p t; [ cbn [saturate_fuel]; apply chain_refl |].
  cbn [saturate_fuel]. destruct (one_step p) as [p'|] eqn:E; [| apply chain_refl ].
  destruct (one_step_inv p p' E) as [i [j [Hm [Hi [Hj Hp']]]]].
  destruct (mergeable_inv p i j Hm) as [Hij _].
  assert (Hm' : mergeable (p ++ t) i j = true).
  { rewrite (mergeable_app p t i j Hij ltac:(lia)). exact Hm. }
  assert (Hjlen : (j < length (p ++ t))%nat)
    by (rewrite length_app; lia).
  pose proof (mergeable_spreadstep (p ++ t) i j Hjlen Hm') as HS.
  rewrite (fill_app p t i j Hj) in HS.
  rewrite <- Hp' in HS.
  apply (chain_step (p ++ t) (p' ++ t)); [ exact HS | apply IH ].
Qed.

Lemma chain_saturate : forall s, Chain s (saturate s).
Proof. intros s. unfold saturate. apply chain_saturate_fuel. Qed.

Lemma dom_antisym : forall s t, length s = length t -> binary s -> binary t ->
  dom s t -> dom t s -> s = t.
Proof.
  intros s t Hlen Hbs Hbt H1 H2.
  destruct (dom_sum s t Hlen Hbs Hbt H1) as [Hle Heq].
  destruct (dom_sum t s (eq_sym Hlen) Hbt Hbs H2) as [Hle2 _].
  apply Heq. lia.
Qed.

Lemma saturate_unique : forall x T, binary x -> Chain x T -> one_step T = None ->
  T = saturate x.
Proof.
  intros x T Hb Hc Hnone.
  destruct (chain_basic x T Hc Hb) as [HlT [HbT HdT]].
  destruct (saturate_props x Hb) as [HlS [HbS HdS]].
  pose proof (chain_dom x (saturate x) (chain_saturate x) T HbT Hnone
                (eq_sym HlT) Hb HdT) as [Hd1 _].
  pose proof (chain_dom x T Hc (saturate x) HbS (saturate_fix x Hb)
                (eq_sym HlS) Hb HdS) as [Hd2 _].
  apply dom_antisym; try assumption.
  rewrite HlT, HlS. reflexivity.
Qed.

Lemma binary_app : forall a b, binary a -> binary b -> binary (a ++ b).
Proof. intros a b Ha Hb. unfold binary in *. apply Forall_app. split; assumption. Qed.

Lemma binary_all_ones : forall n, binary (all_ones n).
Proof. intros n. unfold all_ones. apply binary_repeat1. Qed.

Lemma all_ones_length : forall n, length (all_ones n) = n.
Proof. intros n. unfold all_ones. apply repeat_length. Qed.

(* ===================== (1) CRUX ===================== *)

Theorem rated_prefix_is_block :
  forall p t, binary p -> binary t -> Rated p ->
    stop_len (p ++ t) = stop_len (all_ones (length p) ++ t).
Proof.
  intros p t Hp Ht HR.
  assert (Hsat : saturate p = all_ones (length p))
    by (apply (rated_iff_saturate p Hp); exact HR).
  assert (Hc1 : Chain (p ++ t) (all_ones (length p) ++ t)).
  { rewrite <- Hsat. unfold saturate. apply chain_lift. }
  set (A := all_ones (length p) ++ t).
  assert (HbA : binary A) by (apply binary_app; [ apply binary_all_ones | exact Ht ]).
  assert (Hc : Chain (p ++ t) (saturate A))
    by (apply (chain_trans _ A); [ exact Hc1 | apply chain_saturate ]).
  assert (Heq : saturate A = saturate (p ++ t)).
  { apply saturate_unique; [ apply binary_app; assumption | exact Hc
                           | apply saturate_fix; exact HbA ]. }
  unfold stop_len. rewrite Heq. reflexivity.
Qed.

(* ===================== (2) preliminaries: ones_prefix ===================== *)

Lemma ones_prefix_firstn : forall l j, ones_prefix l = j -> firstn j l = all_ones j.
Proof.
  induction l as [|x l IH]; intros j Hj.
  - cbn [ones_prefix] in Hj. subst j. reflexivity.
  - cbn [ones_prefix] in Hj. destruct (Z.eqb x 1) eqn:E.
    + apply Z.eqb_eq in E. subst x. subst j.
      cbn [firstn]. unfold all_ones. cbn [repeat]. f_equal.
      apply IH. reflexivity.
    + subst j. reflexivity.
Qed.

Lemma ones_prefix_stop : forall l j, ones_prefix l = j -> (j < length l)%nat ->
  nth j l 0 <> 1.
Proof.
  induction l as [|x l IH]; intros j Hj Hlt; [ cbn [length] in Hlt; lia |].
  cbn [ones_prefix] in Hj. destruct (Z.eqb x 1) eqn:E.
  - subst j. cbn [nth]. apply IH; [ reflexivity |].
    cbn [length] in Hlt. lia.
  - subst j. cbn [nth]. intros Hx. subst x. cbn in E. discriminate.
Qed.

(* ===================== projecting a chain onto a prefix ===================== *)

Lemma Zlen_nat : forall (l : list Z), Zlength l = Z.of_nat (length l).
Proof. intros l. apply Zlength_correct. Qed.

Lemma window_firstn : forall l n I J, (S J <= n)%nat ->
  window (firstn n l) I J = window l I J.
Proof.
  intros l n I J H. unfold window.
  rewrite skipn_firstn_comm. rewrite firstn_firstn.
  f_equal. lia.
Qed.

Lemma chain_firstn : forall a S, Chain a S -> binary a -> forall j, (j < length a)%nat ->
  nth j S 0 = 0 -> Chain (firstn j a) (firstn j S).
Proof.
  intros a S Hc. induction Hc as [s | x y z Hstep Hc IH];
    intros Hb j Hj HSj; [ apply chain_refl |].
  destruct (spreadstep_basic x y Hstep) as [Hlyx _].
  assert (Hby : binary y) by (apply (spreadstep_binary x y); assumption).
  assert (Hjy : (j < length y)%nat) by lia.
  pose proof (IH Hby j Hjy HSj) as Hrest.
  (* now: Chain (firstn j x) (firstn j y) *)
  destruct Hstep as [i0 [j0 [[Hi0 Hij0] [Hjlen [Hxi [Hxj [Hsum [HlenB Hq]]]]]]]].
  rewrite Zlen_nat in Hjlen.
  remember (Z.to_nat i0) as I eqn:HI.
  remember (Z.to_nat j0) as J eqn:HJ.
  assert (HiI : i0 = Z.of_nat I) by (subst I; lia).
  assert (HjJ : j0 = Z.of_nat J) by (subst J; lia).
  assert (HIJ : (I < J)%nat) by lia.
  assert (HJx : (J < length x)%nat) by lia.
  destruct (Nat.lt_ge_cases J j) as [Hcase1 | Hcase1].
  - (* merge strictly inside the prefix : lift it *)
    assert (HSS : SpreadStep (firstn j x) (firstn j y)).
    { exists i0, j0.
      assert (Hlfx : length (firstn j x) = j)
        by (rewrite length_firstn; lia).
      assert (Hlfy : length (firstn j y) = j)
        by (rewrite length_firstn; lia).
      split; [ split; lia |].
      split; [ rewrite Zlen_nat, Hlfx; lia |].
      split.
      { rewrite HiI, Znth_nth, (nth_firstn x I j 0 ltac:(lia)).
        rewrite <- Znth_nth, <- HiI. exact Hxi. }
      split.
      { rewrite HjJ, Znth_nth, (nth_firstn x J j 0 ltac:(lia)).
        rewrite <- Znth_nth, <- HjJ. exact Hxj. }
      split.
      { rewrite (sublist_window (firstn j x) i0 j0 ltac:(lia) ltac:(lia)).
        rewrite <- HI, <- HJ.
        rewrite (window_firstn x j I J ltac:(lia)).
        rewrite (sublist_window x i0 j0 ltac:(lia) ltac:(lia)) in Hsum.
        rewrite <- HI, <- HJ in Hsum. exact Hsum. }
      split; [ rewrite !Zlen_nat, Hlfx, Hlfy; reflexivity |].
      intros q Hqr. rewrite Zlen_nat, Hlfx in Hqr.
      assert (Hqn : q = Z.of_nat (Z.to_nat q)) by lia.
      remember (Z.to_nat q) as k eqn:Hk.
      assert (Hkj : (k < j)%nat) by lia.
      rewrite Hqn, !Znth_nth.
      rewrite (nth_firstn y k j 0 Hkj), (nth_firstn x k j 0 Hkj).
      specialize (Hq (Z.of_nat k) ltac:(rewrite Zlen_nat; lia)).
      rewrite !Znth_nth in Hq. exact Hq. }
    apply (chain_step (firstn j x) (firstn j y)); [ exact HSS | exact Hrest ].
  - destruct (Nat.lt_ge_cases I j) as [Hcase2 | Hcase2].
    + (* I < j <= J : the merge would set position j to 1, contradiction *)
      exfalso.
      specialize (Hq (Z.of_nat j) ltac:(rewrite Zlen_nat; lia)).
      rewrite !Znth_nth in Hq.
      assert (E1 : Z.leb i0 (Z.of_nat j) = true) by (apply Z.leb_le; lia).
      assert (E2 : Z.leb (Z.of_nat j) j0 = true) by (apply Z.leb_le; lia).
      rewrite E1, E2 in Hq. cbn [andb] in Hq.
      destruct (chain_basic y z Hc Hby) as [_ [_ Hdyz]].
      pose proof (Hdyz j Hq) as Hz. rewrite HSj in Hz. discriminate.
    + (* the merge lies entirely after the prefix *)
      assert (Hfeq : firstn j y = firstn j x).
      { apply (nth_ext _ _ 0 0).
        - rewrite !length_firstn. lia.
        - intros k Hk. rewrite length_firstn in Hk.
          assert (Hkj : (k < j)%nat) by lia.
          rewrite (nth_firstn y k j 0 Hkj), (nth_firstn x k j 0 Hkj).
          specialize (Hq (Z.of_nat k) ltac:(rewrite Zlen_nat; lia)).
          rewrite !Znth_nth in Hq. rewrite Hq.
          assert (E1 : Z.leb i0 (Z.of_nat k) = false) by (apply Z.leb_gt; lia).
          rewrite E1. cbn [andb]. reflexivity. }
      rewrite <- Hfeq. exact Hrest.
Qed.

(* ===================== rated strings start with 1 ===================== *)

Lemma spreadstep_head : forall a b, SpreadStep a b -> nth 0 b 0 = 1 -> nth 0 a 0 = 1.
Proof.
  intros a b [i0 [j0 [[Hi0 Hij0] [Hjlen [Hxi [Hxj [_ [_ Hq]]]]]]]] Hhb.
  specialize (Hq 0 ltac:(lia)).
  replace (Znth 0 b 0) with (nth 0 b 0) in Hq
    by (rewrite <- (Znth_nth b 0%nat); reflexivity).
  replace (Znth 0 a 0) with (nth 0 a 0) in Hq
    by (rewrite <- (Znth_nth a 0%nat); reflexivity).
  destruct (Z.leb i0 0 && Z.leb 0 j0)%bool eqn:E.
  - rewrite Bool.andb_true_iff in E. destruct E as [E1 _].
    apply Z.leb_le in E1.
    assert (Hi00 : i0 = 0) by lia.
    rewrite Hi00 in Hxi.
    replace (Znth 0 a 0) with (nth 0 a 0) in Hxi
      by (rewrite <- (Znth_nth a 0%nat); reflexivity).
    exact Hxi.
  - rewrite <- Hq. exact Hhb.
Qed.

Lemma chain_head : forall a b, Chain a b -> nth 0 b 0 = 1 -> nth 0 a 0 = 1.
Proof.
  intros a b Hc. induction Hc as [s | x y z Hstep Hc IH]; intros H; [ exact H |].
  apply (spreadstep_head x y Hstep). apply IH. exact H.
Qed.

Lemma rated_head : forall p, binary p -> Rated p -> (0 < length p)%nat ->
  nth 0 p 0 = 1.
Proof.
  intros p Hb HR Hlen.
  assert (Hsat : saturate p = all_ones (length p))
    by (apply (rated_iff_saturate p Hb); exact HR).
  apply (chain_head p (saturate p)); [ apply chain_saturate |].
  rewrite Hsat. unfold all_ones. apply nth_repeat1. exact Hlen.
Qed.

(* ===================== the enumeration all_strings ===================== *)

Lemma all_strings_shift : forall n k,
  fold_right (fun _ acc => flat_map (fun s : list Z => [0 :: s; 1 :: s]) acc) [[]]
             (seq k n) = all_strings n.
Proof.
  unfold all_strings. induction n as [|n IH]; intros k; [ reflexivity |].
  cbn [seq fold_right]. rewrite (IH (S k)), (IH 1%nat). reflexivity.
Qed.

Lemma all_strings_S__L3a : forall n,
  all_strings (S n) = flat_map (fun s : list Z => [0 :: s; 1 :: s]) (all_strings n).
Proof.
  intros n. unfold all_strings at 1. cbn [seq fold_right]. f_equal.
  apply all_strings_shift.
Qed.

Lemma In_all_strings : forall n s, In s (all_strings n) -> length s = n /\ binary s.
Proof.
  induction n as [|n IH]; intros s Hin.
  - cbn in Hin. destruct Hin as [H | H]; [| contradiction ].
    subst s. split; [ reflexivity | constructor ].
  - rewrite all_strings_S__L3a in Hin. rewrite in_flat_map in Hin.
    destruct Hin as [x [Hx Hs]].
    destruct (IH x Hx) as [Hlx Hbx].
    cbn [In] in Hs. destruct Hs as [H | [H | H]]; try contradiction; subst s.
    + split; [ cbn [length]; lia | constructor; [ left; reflexivity | exact Hbx ] ].
    + split; [ cbn [length]; lia | constructor; [ right; reflexivity | exact Hbx ] ].
Qed.

Lemma filter_len_ext : forall (f g : list Z -> bool) l,
  (forall s, f s = g s) -> length (filter f l) = length (filter g l).
Proof.
  intros f g l H. f_equal. apply filter_ext. exact H.
Qed.

Lemma filter_flat_map_len : forall (f : list Z -> bool) l,
  length (filter f (flat_map (fun s : list Z => [0 :: s; 1 :: s]) l)) =
  (length (filter (fun s : list Z => f (0%Z :: s)) l) +
   length (filter (fun s : list Z => f (1%Z :: s)) l))%nat.
Proof.
  intros f. induction l as [|x l IH]; [ reflexivity |].
  cbn [flat_map filter]. rewrite filter_app, length_app.
  cbn [filter]. rewrite IH.
  destruct (f (0 :: x)); destruct (f (1 :: x)); cbn [length]; lia.
Qed.

Lemma count_prod : forall a Pt b Pp,
  length (filter (fun s => (Pp (firstn a s) && Pt (skipn a s))%bool) (all_strings (a + b)))
  = (length (filter Pp (all_strings a)) * length (filter Pt (all_strings b)))%nat.
Proof.
  induction a as [|a IH]; intros Pt b Pp.
  - cbn [Nat.add]. cbn [firstn skipn].
    cbn [all_strings seq fold_right filter].
    destruct (Pp []) eqn:E.
    + cbn [length]. rewrite Nat.mul_1_l.
      apply filter_len_ext. intros s. reflexivity.
    + cbn [length]. rewrite Nat.mul_0_l.
      rewrite (filter_len_ext _ (fun _ => false)) by (intros s; reflexivity).
      clear. induction (all_strings b) as [|x l IHl]; [ reflexivity | exact IHl ].
  - cbn [Nat.add]. rewrite all_strings_S__L3a, filter_flat_map_len.
    rewrite (filter_len_ext (fun s => (Pp (firstn (S a) (0 :: s)) && Pt (skipn (S a) (0 :: s)))%bool)
                            (fun s => ((fun u : list Z => Pp (0%Z :: u)) (firstn a s) && Pt (skipn a s))%bool))
      by (intros s; reflexivity).
    rewrite (filter_len_ext (fun s => (Pp (firstn (S a) (1 :: s)) && Pt (skipn (S a) (1 :: s)))%bool)
                            (fun s => ((fun u : list Z => Pp (1%Z :: u)) (firstn a s) && Pt (skipn a s))%bool))
      by (intros s; reflexivity).
    rewrite (IH Pt b (fun u : list Z => Pp (0%Z :: u))).
    rewrite (IH Pt b (fun u : list Z => Pp (1%Z :: u))).
    rewrite all_strings_S__L3a, filter_flat_map_len.
    rewrite Nat.mul_add_distr_r. reflexivity.
Qed.

(* ===================== (2) FIBER decomposition ===================== *)

Theorem fiber_count :
  forall i j, (1 <= j)%nat -> (j < i)%nat ->
    count_stop i j = count_rated j * cntW (i - j) j.
Proof.
  intros i j Hj1 Hji.
  remember (i - j)%nat as d eqn:Hd.
  assert (Hi : i = (j + d)%nat) by lia.
  assert (Hd1 : (1 <= d)%nat) by lia.
  unfold count_stop, count_rated, cntW.
  rewrite <- Nat2Z.inj_mul. f_equal.
  rewrite Hi.
  transitivity (length (filter
     (fun s => (rated_bool (firstn j s) &&
                Nat.eqb (stop_len (all_ones j ++ skipn j s)) j)%bool)
     (all_strings (j + d)))).
  - f_equal. apply filter_ext_in. intros s Hin.
    destruct (In_all_strings _ s Hin) as [Hlen Hbin].
    assert (Hjs : (j < length s)%nat) by lia.
    set (p := firstn j s). set (t := skipn j s).
    assert (Hlp : length p = j) by (unfold p; rewrite length_firstn; lia).
    assert (Hbp : binary p) by (unfold p; apply binary_firstn; exact Hbin).
    assert (Hbt : binary t) by (unfold t; apply binary_skipn; exact Hbin).
    assert (Hpt : p ++ t = s) by (unfold p, t; apply firstn_skipn).
    assert (Hcrux : Rated p -> stop_len s = stop_len (all_ones j ++ t)).
    { pose proof (rated_prefix_is_block p t Hbp Hbt) as HC.
      rewrite Hlp, Hpt in HC. exact HC. }
    apply Bool.eq_iff_eq_true. split; intros H.
    + rewrite Bool.andb_true_iff in H. destruct H as [H0 Hst].
      apply Nat.eqb_eq in Hst.
      destruct (saturate_props s Hbin) as [Hls [Hbs _]].
      assert (Hzero : nth j (saturate s) 0 = 0).
      { unfold stop_len in Hst.
        pose proof (ones_prefix_stop (saturate s) j Hst ltac:(lia)) as Hne.
        destruct (binary_nth (saturate s) Hbs j) as [Hv | Hv];
          [ exact Hv | contradiction ]. }
      assert (HRp : Rated p).
      { apply (chain_rated p (firstn j (saturate s))).
        - apply (chain_firstn s (saturate s)); [ apply chain_saturate | exact Hbin
                                               | exact Hjs | exact Hzero ].
        - unfold stop_len in Hst.
          rewrite (ones_prefix_firstn (saturate s) j Hst).
          unfold all_ones. apply Forall1_repeat. }
      rewrite Bool.andb_true_iff. split.
      * apply rated_dec_correct; assumption.
      * apply Nat.eqb_eq. rewrite <- (Hcrux HRp). exact Hst.
    + rewrite Bool.andb_true_iff in H. destruct H as [Hr Hw].
      apply Nat.eqb_eq in Hw.
      assert (HRp : Rated p) by (apply rated_dec_correct; assumption).
      rewrite Bool.andb_true_iff. split.
      * apply Z.eqb_eq.
        rewrite <- (nth_firstn s 0 j 0 ltac:(lia)).
        apply rated_head; [ exact Hbp | exact HRp | rewrite length_firstn; lia ].
      * apply Nat.eqb_eq. rewrite (Hcrux HRp). exact Hw.
  - apply (count_prod j (fun t => Nat.eqb (stop_len (all_ones j ++ t)) j) d rated_bool).
Qed.



(* ---------- from L3b.v ---------- *)

(* ================= block 1 : list helpers ================= *)

Lemma ones_count_app : forall a b, ones_count (a ++ b) = ones_count a + ones_count b.
Proof.
  induction a as [|x a IH]; intros b; unfold ones_count in *; cbn [app fold_right].
  - lia.
  - rewrite IH. lia.
Qed.

Lemma ones_count_repeat0 : forall n, ones_count (repeat 0 n) = 0.
Proof.
  induction n as [|n IH]; unfold ones_count in *; cbn [repeat fold_right]; lia.
Qed.

Lemma nth_app_r : forall (p a : list Z) k, nth (length p + k) (p ++ a) 0 = nth k a 0.
Proof.
  induction p as [|x p IH]; intros a k; cbn [length app plus nth]; [reflexivity|].
  apply IH.
Qed.

Lemma nth_app_l : forall (p a : list Z) k, (k < length p)%nat -> nth k (p ++ a) 0 = nth k p 0.
Proof.
  induction p as [|x p IH]; intros a k Hk; [ cbn [length] in Hk; lia |].
  destruct k as [|k]; cbn [app nth]; [reflexivity|].
  apply IH. cbn [length] in Hk. lia.
Qed.

Lemma skipn_app_exact : forall (p a : list Z), skipn (length p) (p ++ a) = a.
Proof.
  induction p as [|x p IH]; intros a; [reflexivity | cbn [length app skipn]; apply IH].
Qed.

Lemma skipn_app_l : forall (p a : list Z) n, (n <= length p)%nat ->
  skipn n (p ++ a) = skipn n p ++ a.
Proof.
  induction p as [|x p IH]; intros a n Hn.
  - cbn [length] in Hn. destruct n; [reflexivity | lia].
  - destruct n as [|n]; [reflexivity|].
    cbn [app skipn]. apply IH. cbn [length] in Hn. lia.
Qed.

Lemma skipn_repeat1 : forall n i, (i <= n)%nat -> skipn i (repeat 1 n) = repeat 1 (n - i).
Proof.
  induction n as [|n IH]; intros i Hi.
  - destruct i; [reflexivity | lia].
  - destruct i as [|i]; [ cbn [skipn]; f_equal; lia |].
    cbn [repeat skipn]. rewrite IH by lia. f_equal.
Qed.

Lemma firstn_app_gen : forall (p a : list Z) n,
  firstn n (p ++ a) = firstn n p ++ firstn (n - length p) a.
Proof. intros. apply firstn_app. Qed.

Lemma firstn_repeat1_all : forall n m, (n <= m)%nat -> firstn n (repeat 1 m) = repeat (1%Z) n.
Proof.
  induction n as [|n IH]; intros m Hm; [reflexivity|].
  destruct m as [|m]; [lia|].
  cbn [repeat firstn]. f_equal. apply IH. lia.
Qed.

Lemma length_repeatZ : forall (x : Z) n, length (repeat x n) = n.
Proof. intros. apply repeat_length. Qed.

Lemma nth_firstn_lt : forall (l : list Z) n k, (k < n)%nat ->
  nth k (firstn n l) 0 = nth k l 0.
Proof.
  induction l as [|x l IH]; intros n k Hk.
  - rewrite firstn_nil. destruct k; reflexivity.
  - destruct n as [|n]; [ lia |].
    destruct k as [|k]; cbn [firstn nth]; [ reflexivity |].
    apply IH. lia.
Qed.

Lemma binary_app__L3b : forall a b, binary a -> binary b -> binary (a ++ b).
Proof. intros a b Ha Hb. unfold binary in *. apply Forall_app. split; assumption. Qed.

Lemma binary_repeat0 : forall n, binary (repeat 0 n).
Proof.
  induction n as [|n IH]; cbn [repeat]; constructor; [ left; reflexivity | exact IH ].
Qed.

(* ================= block 2 : ones_prefix ================= *)

Lemma ones_prefix_ones : forall v k, (k < ones_prefix v)%nat -> nth k v 0 = 1.
Proof.
  induction v as [|x v IH]; intros k Hk; [ cbn [ones_prefix] in Hk; lia |].
  cbn [ones_prefix] in Hk. destruct (Z.eqb x 1) eqn:Ex; [| lia ].
  apply Z.eqb_eq in Ex.
  destruct k as [|k]; cbn [nth]; [ exact Ex |]. apply IH. lia.
Qed.

Lemma ones_prefix_stop__L3b : forall v, nth (ones_prefix v) v 0 <> 1.
Proof.
  induction v as [|x v IH]; cbn [ones_prefix]; [ cbn [nth]; discriminate |].
  destruct (Z.eqb x 1) eqn:Ex; cbn [nth].
  - exact IH.
  - intros H. rewrite H in Ex. cbn in Ex. discriminate.
Qed.

Lemma ones_prefix_le : forall v, (ones_prefix v <= length v)%nat.
Proof.
  induction v as [|x v IH]; cbn [ones_prefix length]; [ lia |].
  destruct (Z.eqb x 1); lia.
Qed.

Lemma ones_prefix_eq : forall v n, (forall k, (k < n)%nat -> nth k v 0 = 1) ->
  nth n v 0 <> 1 -> ones_prefix v = n.
Proof.
  induction v as [|x v IH]; intros n H1 H2.
  - destruct n as [|n]; [ reflexivity |].
    exfalso. specialize (H1 0%nat ltac:(lia)). cbn in H1. discriminate.
  - destruct n as [|n].
    + cbn [ones_prefix]. cbn [nth] in H2.
      destruct (Z.eqb x 1) eqn:Ex; [| reflexivity ].
      exfalso. apply H2. apply Z.eqb_eq. exact Ex.
    + assert (Hx : x = 1) by (specialize (H1 0%nat ltac:(lia)); cbn in H1; exact H1).
      subst x. cbn [ones_prefix]. cbn in H2. rewrite Z.eqb_refl. f_equal.
      apply IH; [| exact H2 ].
      intros k Hk. specialize (H1 (S k) ltac:(lia)). cbn in H1. exact H1.
Qed.

Lemma firstn_ones_prefix : forall v, firstn (ones_prefix v) v = repeat 1 (ones_prefix v).
Proof.
  induction v as [|x v IH]; [ reflexivity |].
  cbn [ones_prefix]. destruct (Z.eqb x 1) eqn:Ex; [| reflexivity ].
  apply Z.eqb_eq in Ex. subst x. cbn [firstn repeat]. f_equal. exact IH.
Qed.

Lemma stop_len_le : forall s, binary s -> (stop_len s <= length s)%nat.
Proof.
  intros s Hb. unfold stop_len.
  destruct (saturate_props s Hb) as [Hl _].
  rewrite <- Hl. apply ones_prefix_le.
Qed.

Lemma stop_len_pos : forall s, binary s -> nth 0 s 0 = 1 -> (1 <= stop_len s)%nat.
Proof.
  intros s Hb H0. unfold stop_len.
  destruct (saturate_props s Hb) as [_ [_ Hd]].
  specialize (Hd 0%nat H0).
  destruct (saturate s) as [|x v] eqn:E; [ cbn in Hd; discriminate |].
  cbn [nth] in Hd. subst x. cbn [ones_prefix]. rewrite Z.eqb_refl. lia.
Qed.

(* ================= block 3 : shift lemmas ================= *)

Lemma skipn_app_shift : forall (p a : list Z) i, skipn (length p + i) (p ++ a) = skipn i a.
Proof.
  induction p as [|x p IH]; intros a i; [ reflexivity |].
  cbn [length app plus skipn]. apply IH.
Qed.

Lemma window_app_shift : forall (p a : list Z) i k,
  window (p ++ a) (length p + i) (length p + k) = window a i k.
Proof.
  intros p a i k. unfold window.
  replace (S (length p + k) - (length p + i))%nat with (S k - i)%nat by lia.
  rewrite skipn_app_shift. reflexivity.
Qed.

Lemma mergeable_app_shift : forall (p a : list Z) i k,
  mergeable (p ++ a) (length p + i) (length p + k) = mergeable a i k.
Proof.
  intros p a i k. unfold mergeable.
  rewrite !nth_app_r. rewrite window_app_shift.
  replace (S (length p + k) - (length p + i))%nat with (S k - i)%nat by lia.
  destruct (Nat.ltb i k) eqn:E1; destruct (Nat.ltb (length p + i) (length p + k)) eqn:E2;
    try reflexivity.
  - apply Nat.ltb_lt in E1. apply Nat.ltb_ge in E2. lia.
  - apply Nat.ltb_ge in E1. apply Nat.ltb_lt in E2. lia.
Qed.

Lemma fill_app_shift : forall (p a : list Z) i k,
  fill (p ++ a) (length p + i) (length p + k) = p ++ fill a i k.
Proof.
  intros p a i k.
  apply (nth_ext _ _ 0 0).
  - rewrite fill_length, !length_app, fill_length. reflexivity.
  - intros n Hn. rewrite fill_length, length_app in Hn.
    rewrite fill_nth by (rewrite length_app; lia).
    destruct (Nat.lt_ge_cases n (length p)) as [Hlt | Hge].
    + assert (E : Nat.leb (length p + i) n = false)
        by (apply Nat.leb_gt; lia).
      rewrite E. cbn [andb].
      rewrite !nth_app_l by (try rewrite fill_length; lia). reflexivity.
    + replace n with (length p + (n - length p))%nat by lia.
      rewrite !nth_app_r.
      rewrite fill_nth by lia.
      destruct (Nat.leb i (n - length p)) eqn:E1;
      destruct (Nat.leb (n - length p) k) eqn:E2;
      [ assert (Ea : Nat.leb (length p + i) (length p + (n - length p)) = true)
          by (apply Nat.leb_le; apply Nat.leb_le in E1; lia)
      | | | ];
      try (rewrite Bool.andb_false_r).
      * rewrite Ea.
        assert (Eb : Nat.leb (length p + (n - length p)) (length p + k) = true)
          by (apply Nat.leb_le; apply Nat.leb_le in E2; lia).
        rewrite Eb. reflexivity.
      * assert (Eb : Nat.leb (length p + (n - length p)) (length p + k) = false)
          by (apply Nat.leb_gt; apply Nat.leb_gt in E2; lia).
        rewrite Eb, Bool.andb_false_r. reflexivity.
      * assert (Ea : Nat.leb (length p + i) (length p + (n - length p)) = false)
          by (apply Nat.leb_gt; apply Nat.leb_gt in E1; lia).
        rewrite Ea. cbn [andb]. reflexivity.
      * assert (Ea : Nat.leb (length p + i) (length p + (n - length p)) = false)
          by (apply Nat.leb_gt; apply Nat.leb_gt in E1; lia).
        rewrite Ea. cbn [andb]. reflexivity.
Qed.

(* ================= block 4 : chains ================= *)

Lemma one_step_none_intro : forall T,
  (forall i k, (i < length T)%nat -> (k < length T)%nat -> mergeable T i k = false) ->
  one_step T = None.
Proof.
  intros T H. unfold one_step.
  destruct (filter (fun p => mergeable T (fst p) (snd p)) (pairs (length T)))
    as [|p rest] eqn:E; [ reflexivity |].
  exfalso.
  destruct (filter_cons_inv _ _ p rest E) as [Hin Hf].
  destruct p as [i k]. cbn [fst snd] in Hf.
  rewrite in_pairs in Hin.
  rewrite (H i k (proj1 Hin) (proj2 Hin)) in Hf. discriminate.
Qed.

Lemma chain_snoc : forall a b c, Chain a b -> SpreadStep b c -> Chain a c.
Proof.
  intros a b c H. induction H as [s | x y z Hs Hc IH]; intros Hstep.
  - apply (chain_step s c c); [ exact Hstep | apply chain_refl ].
  - apply (chain_step x y); [ exact Hs | apply IH; exact Hstep ].
Qed.

Lemma chain_app_fuel : forall k p a, Chain (p ++ a) (p ++ saturate_fuel k a).
Proof.
  induction k as [|k IH]; intros p a; [ cbn [saturate_fuel]; apply chain_refl |].
  cbn [saturate_fuel]. destruct (one_step a) as [a'|] eqn:E; [| apply chain_refl ].
  destruct (one_step_inv a a' E) as [i [j [Hm [Hi [Hj Ha']]]]].
  apply (chain_step (p ++ a) (p ++ a')); [| subst a'; apply IH ].
  subst a'. rewrite <- (fill_app_shift p a i j).
  apply mergeable_spreadstep.
  - rewrite length_app. lia.
  - rewrite mergeable_app_shift. exact Hm.
Qed.

Lemma chain_app_saturate : forall p a, Chain (p ++ a) (p ++ saturate a).
Proof. intros p a. unfold saturate. apply chain_app_fuel. Qed.

(* transporting a witness of a 1 along a chain into the saturation *)
Lemma chain_nth_saturate : forall s t k, binary s -> Chain s t -> nth k t 0 = 1 ->
  nth k (saturate s) 0 = 1.
Proof.
  intros s t k Hb Hc H1.
  destruct (saturate_props s Hb) as [Hl [HbT Hd]].
  destruct (chain_dom s t Hc (saturate s) HbT (saturate_fix s Hb)
              (eq_sym Hl) Hb Hd) as [Hdt _].
  apply Hdt. exact H1.
Qed.

(* ================= block 5 : the structured string T ================= *)

Definition Tstr (j z : nat) (v : list Z) : list Z := repeat 1 j ++ repeat 0 z ++ v.

Lemma T_length : forall j z v, length (Tstr j z v) = (j + z + length v)%nat.
Proof.
  intros. unfold Tstr. rewrite !length_app, !repeat_length. lia.
Qed.

Lemma T_binary : forall j z v, binary v -> binary (Tstr j z v).
Proof.
  intros. unfold Tstr. apply binary_app__L3b; [ apply binary_repeat1 |].
  apply binary_app__L3b; [ apply binary_repeat0 | assumption ].
Qed.

Lemma T_nth_lo : forall j z v k, (k < j)%nat -> nth k (Tstr j z v) 0 = 1.
Proof.
  intros j z v k Hk. unfold Tstr.
  rewrite nth_app_l by (rewrite repeat_length; lia).
  apply nth_repeat1. exact Hk.
Qed.

Lemma nth_repeat0 : forall z k, nth k (repeat (0%Z) z) 0 = 0.
Proof.
  induction z as [|z IH]; intros k; [ destruct k; reflexivity |].
  destruct k as [|k]; cbn [repeat nth]; [ reflexivity | apply IH ].
Qed.

Lemma T_nth_mid : forall j z v k, (j <= k)%nat -> (k < j + z)%nat ->
  nth k (Tstr j z v) 0 = 0.
Proof.
  intros j z v k H1 H2. unfold Tstr.
  replace k with (length (repeat (1%Z) j) + (k - j))%nat
    by (rewrite repeat_length; lia).
  rewrite nth_app_r.
  rewrite nth_app_l by (rewrite repeat_length; lia).
  apply nth_repeat0.
Qed.

Lemma T_nth_hi : forall j z v m, nth (j + z + m) (Tstr j z v) 0 = nth m v 0.
Proof.
  intros j z v m. unfold Tstr.
  replace (j + z + m)%nat with (length (repeat (1%Z) j) + (z + m))%nat
    by (rewrite repeat_length; lia).
  rewrite nth_app_r.
  replace (z + m)%nat with (length (repeat (0%Z) z) + m)%nat
    by (rewrite repeat_length; lia).
  rewrite nth_app_r. reflexivity.
Qed.

Lemma T_skipn : forall j z v i, (i <= j)%nat ->
  skipn i (Tstr j z v) = repeat 1 (j - i) ++ repeat 0 z ++ v.
Proof.
  intros j z v i Hi. unfold Tstr.
  rewrite skipn_app_l by (rewrite repeat_length; lia).
  rewrite skipn_repeat1 by lia. reflexivity.
Qed.

Lemma T_window_lo : forall j z v i k, (i <= j)%nat -> (k < j)%nat ->
  window (Tstr j z v) i k = repeat 1 (S k - i).
Proof.
  intros j z v i k Hi Hk. unfold window.
  rewrite T_skipn by lia.
  rewrite firstn_app_gen, repeat_length.
  rewrite firstn_repeat1_all by lia.
  replace (S k - i - (j - i))%nat with 0%nat by lia.
  cbn [firstn]. rewrite app_nil_r. reflexivity.
Qed.

Lemma T_window_hi : forall j z v i m, (i <= j)%nat ->
  window (Tstr j z v) i (j + z + m) =
  repeat 1 (j - i) ++ repeat 0 z ++ firstn (S m) v.
Proof.
  intros j z v i m Hi. unfold window.
  rewrite T_skipn by lia.
  rewrite firstn_app_gen, repeat_length.
  rewrite firstn_all2 by (rewrite repeat_length; lia).
  f_equal.
  rewrite firstn_app_gen, repeat_length.
  rewrite firstn_all2 by (rewrite repeat_length; lia).
  f_equal. f_equal. lia.
Qed.

(* ================= block 6 : direction A (blocked) ================= *)

Lemma blockedA : forall j z v, binary v -> one_step v = None ->
  (forall m, (m < length v)%nat -> nth m v 0 = 1 ->
     Z.of_nat j + 2 * ones_count (firstn (S m) v) <= Z.of_nat z + Z.of_nat m) ->
  one_step (Tstr j z v) = None.
Proof.
  intros j z v Hbv Hnone Hkey.
  apply one_step_none_intro. intros i k Hi Hk.
  rewrite T_length in Hi, Hk.
  destruct (mergeable (Tstr j z v) i k) eqn:E; [ exfalso | reflexivity ].
  destruct (mergeable_inv _ _ _ E) as [Hik [Hni [Hnk [Hge Hlt]]]].
  destruct (Nat.lt_ge_cases i j) as [Hij | Hij].
  - (* i inside the leading block of ones *)
    destruct (Nat.lt_ge_cases k j) as [Hkj | Hkj].
    + rewrite (T_window_lo j z v i k ltac:(lia) Hkj) in Hlt.
      rewrite ones_count_repeat1 in Hlt. lia.
    + destruct (Nat.lt_ge_cases k (j + z)) as [Hkz | Hkz].
      * rewrite (T_nth_mid j z v k Hkj Hkz) in Hnk. discriminate.
      * (* k in the v part *)
        remember (k - j - z)%nat as m eqn:Hm.
        assert (Hk' : k = (j + z + m)%nat) by lia.
        subst k.
        rewrite T_nth_hi in Hnk.
        assert (Hmlen : (m < length v)%nat) by lia.
        specialize (Hkey m Hmlen Hnk).
        rewrite (T_window_hi j z v i m ltac:(lia)) in Hge.
        rewrite !ones_count_app, ones_count_repeat1, ones_count_repeat0 in Hge.
        lia.
  - destruct (Nat.lt_ge_cases i (j + z)) as [Hiz | Hiz].
    + rewrite (T_nth_mid j z v i Hij Hiz) in Hni. discriminate.
    + (* both indices inside v *)
      assert (Hsplit : Tstr j z v = (repeat 1 j ++ repeat 0 z) ++ v)
        by (unfold Tstr; rewrite app_assoc; reflexivity).
      assert (Hplen : length (repeat (1%Z) j ++ repeat (0%Z) z) = (j + z)%nat)
        by (rewrite length_app, !repeat_length; reflexivity).
      assert (Hmm : mergeable v (i - j - z) (k - j - z) = true).
      { rewrite <- (mergeable_app_shift (repeat 1 j ++ repeat 0 z) v (i - j - z) (k - j - z)).
        rewrite Hplen.
        replace (j + z + (i - j - z))%nat with i by lia.
        replace (j + z + (k - j - z))%nat with k by lia.
        rewrite <- Hsplit. exact E. }
      rewrite (one_step_none_not_mergeable v (i - j - z) (k - j - z) Hnone
                 ltac:(lia) ltac:(lia)) in Hmm.
      discriminate.
Qed.

(* ================= block 7 : the key inequality ================= *)

Lemma sat_key : forall u j z, binary u ->
  ((0 < length u)%nat -> nth 0 u 0 = 1) ->
  Z.of_nat j + Z.of_nat (stop_len u) < Z.of_nat z ->
  forall m, (m < length (saturate u))%nat -> nth m (saturate u) 0 = 1 ->
    Z.of_nat j + 2 * ones_count (firstn (S m) (saturate u)) <=
    Z.of_nat z + Z.of_nat m.
Proof.
  intros u j z Hbu Hu0 Hlt m Hm Hnm.
  destruct (saturate_props u Hbu) as [Hlen [Hbv Hdom]].
  remember (saturate u) as v eqn:Hv.
  assert (HS : stop_len u = ones_prefix v) by (unfold stop_len; rewrite Hv; reflexivity).
  rewrite HS in Hlt.
  remember (ones_prefix v) as S0 eqn:HS0.
  assert (Hv0 : nth 0 v 0 = 1).
  { apply Hdom. apply Hu0. lia. }
  assert (HS1 : (1 <= S0)%nat).
  { destruct (Nat.eq_dec S0 0) as [E|E]; [| lia ].
    exfalso. apply (ones_prefix_stop__L3b v). rewrite <- HS0, E. exact Hv0. }
  destruct (Nat.lt_ge_cases m S0) as [Hcase | Hcase].
  - (* inside the merged prefix block *)
    assert (Hf : firstn (S m) v = repeat 1 (S m)).
    { transitivity (firstn (S m) (firstn S0 v)).
      - rewrite firstn_firstn. f_equal. lia.
      - rewrite HS0, firstn_ones_prefix.
        apply firstn_repeat1_all. lia. }
    rewrite Hf, ones_count_repeat1, Nat2Z.inj_succ. lia.
  - (* beyond it: saturation forbids the long merge from 0 *)
    assert (Hm0 : (0 < m)%nat) by lia.
    assert (Hwin : window v 0 m = firstn (S m) v) by reflexivity.
    assert (Hflen : length (firstn (S m) v) = S m) by (rewrite length_firstn; lia).
    assert (Hnotall : firstn (S m) v <> repeat 1 (length (firstn (S m) v))).
    { rewrite Hflen. intros Heq.
      assert (Hzero : nth S0 (firstn (S m) v) 0 = nth S0 v 0)
        by (apply nth_firstn_lt; lia).
      rewrite Heq in Hzero.
      rewrite (nth_repeat1 (S m) S0 ltac:(lia)) in Hzero.
      apply (ones_prefix_stop__L3b v). rewrite <- HS0. symmetry. exact Hzero. }
    pose proof (not_all_ones_sum _ (binary_firstn (S m) v Hbv) Hnotall) as Hsum.
    rewrite Hflen in Hsum.
    assert (Hnm2 : mergeable v 0 m = false).
    { apply (one_step_none_not_mergeable v 0 m); [| lia | lia ].
      rewrite Hv. apply saturate_fix. exact Hbu. }
    destruct (Z.lt_ge_cases (2 * ones_count (window v 0 m)) (Z.of_nat (S m - 0)))
      as [Hgood | Hbad].
    + rewrite Hwin in Hgood. lia.
    + exfalso.
      rewrite (mergeable_intro v 0 m ltac:(lia) Hv0 Hnm ltac:(lia)) in Hnm2;
        [ discriminate |].
      rewrite Hwin. lia.
Qed.

Lemma T_dom : forall j z u v, dom u v -> dom (Tstr j z u) (Tstr j z v).
Proof.
  intros j z u v Hd k Hk.
  destruct (Nat.lt_ge_cases k j) as [H1 | H1]; [ apply T_nth_lo; exact H1 |].
  destruct (Nat.lt_ge_cases k (j + z)) as [H2 | H2].
  - rewrite (T_nth_mid j z u k H1 H2) in Hk. discriminate.
  - assert (Hk2 : nth (j + z + (k - j - z)) (Tstr j z u) 0 = 1)
      by (replace (j + z + (k - j - z))%nat with k by lia; exact Hk).
    rewrite T_nth_hi in Hk2.
    replace k with (j + z + (k - j - z))%nat by lia.
    rewrite T_nth_hi. apply Hd. exact Hk2.
Qed.

Lemma stop_len_blocked_gen : forall j z u, binary u ->
  nth j (Tstr j z (saturate u)) 0 <> 1 ->
  (forall m, (m < length (saturate u))%nat -> nth m (saturate u) 0 = 1 ->
     Z.of_nat j + 2 * ones_count (firstn (S m) (saturate u)) <=
     Z.of_nat z + Z.of_nat m) ->
  stop_len (Tstr j z u) = j.
Proof.
  intros j z u Hbu Hnj Hkey.
  destruct (saturate_props u Hbu) as [Hlen [Hbv Hdomu]].
  remember (Tstr j z u) as s eqn:Hs.
  remember (Tstr j z (saturate u)) as T eqn:HT.
  assert (HbS : binary s) by (rewrite Hs; apply T_binary; exact Hbu).
  assert (HbT : binary T) by (rewrite HT; apply T_binary; exact Hbv).
  assert (HnoneT : one_step T = None).
  { rewrite HT. apply blockedA; [ exact Hbv | apply saturate_fix; exact Hbu | exact Hkey ]. }
  assert (HlenT : length s = length T)
    by (rewrite Hs, HT, !T_length, Hlen; reflexivity).
  assert (HdsT : dom s T) by (rewrite Hs, HT; apply T_dom; exact Hdomu).
  destruct (chain_dom s (saturate s) (chain_saturate_fuel (length s) s)
              T HbT HnoneT HlenT HbS HdsT) as [Hdst _].
  unfold stop_len. apply ones_prefix_eq.
  - intros k Hk.
    destruct (saturate_props s HbS) as [_ [_ Hd2]].
    apply Hd2. rewrite Hs. apply T_nth_lo. exact Hk.
  - intros Hcon. apply Hnj. apply Hdst. exact Hcon.
Qed.

(* ================= block 8 : direction B (unblocked) ================= *)

Lemma unblockedB : forall j z u, binary u -> (1 <= j)%nat -> (1 <= z)%nat ->
  nth 0 u 0 = 1 ->
  Z.of_nat z <= Z.of_nat j + Z.of_nat (stop_len u) ->
  nth j (saturate (Tstr j z u)) 0 = 1.
Proof.
  intros j z u Hbu Hj Hz Hu0 Hge.
  destruct (saturate_props u Hbu) as [Hlen [Hbv Hdomu]].
  remember (saturate u) as v eqn:Hv.
  remember (ones_prefix v) as S0 eqn:HS0.
  assert (HS : stop_len u = S0) by (unfold stop_len; rewrite <- Hv, HS0; reflexivity).
  assert (Hv0 : nth 0 v 0 = 1) by (apply Hdomu; exact Hu0).
  assert (HS1 : (1 <= S0)%nat).
  { destruct (Nat.eq_dec S0 0) as [E|E]; [| lia ].
    exfalso. apply (ones_prefix_stop__L3b v). rewrite <- HS0, E. exact Hv0. }
  assert (HSlen : (S0 <= length v)%nat) by (rewrite HS0; apply ones_prefix_le).
  set (p := repeat (1%Z) j ++ repeat (0%Z) z).
  assert (Hplen : length p = (j + z)%nat)
    by (unfold p; rewrite length_app, !repeat_length; reflexivity).
  assert (Hsp : Tstr j z u = p ++ u)
    by (unfold Tstr, p; rewrite app_assoc; reflexivity).
  assert (HTp : Tstr j z v = p ++ v)
    by (unfold Tstr, p; rewrite app_assoc; reflexivity).
  assert (Hchain : Chain (Tstr j z u) (Tstr j z v)).
  { rewrite Hsp, HTp, Hv. apply chain_app_saturate. }
  remember (j + z + (S0 - 1))%nat as K eqn:HK.
  assert (HKlt : (K < length (Tstr j z v))%nat) by (rewrite T_length; lia).
  assert (Hmerge : mergeable (Tstr j z v) 0 K = true).
  { apply mergeable_intro.
    - lia.
    - apply T_nth_lo. lia.
    - rewrite HK, T_nth_hi. apply ones_prefix_ones. lia.
    - rewrite HK, (T_window_hi j z v 0 (S0 - 1) ltac:(lia)).
      rewrite !ones_count_app, ones_count_repeat1, ones_count_repeat0.
      replace (S (S0 - 1))%nat with S0 by lia.
      rewrite HS0, firstn_ones_prefix, <- HS0, ones_count_repeat1.
      replace (j - 0)%nat with j by lia. lia.
    - rewrite HK, (T_window_hi j z v 0 (S0 - 1) ltac:(lia)).
      rewrite !ones_count_app, ones_count_repeat1, ones_count_repeat0.
      replace (S (S0 - 1))%nat with S0 by lia.
      rewrite HS0, firstn_ones_prefix, <- HS0, ones_count_repeat1.
      replace (j - 0)%nat with j by lia. lia. }
  assert (Hstep : SpreadStep (Tstr j z v) (fill (Tstr j z v) 0 K))
    by (apply mergeable_spreadstep; assumption).
  assert (Hchain2 : Chain (Tstr j z u) (fill (Tstr j z v) 0 K))
    by (apply (chain_snoc _ (Tstr j z v)); assumption).
  apply (chain_nth_saturate _ (fill (Tstr j z v) 0 K) j).
  - apply T_binary. exact Hbu.
  - exact Hchain2.
  - rewrite fill_nth by (rewrite T_length; lia).
    assert (E1 : Nat.leb 0 j = true) by (apply Nat.leb_le; lia).
    assert (E2 : Nat.leb j K = true) by (apply Nat.leb_le; lia).
    rewrite E1, E2. reflexivity.
Qed.

(* ================= block 9 : the criterion ================= *)

Fixpoint zpref (t : list Z) : nat :=
  match t with nil => O | x :: tl => if Z.eqb x 0 then S (zpref tl) else O end.

Lemma zpref_le : forall t, (zpref t <= length t)%nat.
Proof.
  induction t as [|x t IH]; cbn [zpref length]; [ lia |].
  destruct (Z.eqb x 0); lia.
Qed.

Lemma zpref_firstn : forall t, firstn (zpref t) t = repeat 0 (zpref t).
Proof.
  induction t as [|x t IH]; [ reflexivity |].
  cbn [zpref]. destruct (Z.eqb x 0) eqn:Ex; [| reflexivity ].
  apply Z.eqb_eq in Ex. subst x. cbn [firstn repeat]. f_equal. exact IH.
Qed.

Lemma zpref_decomp : forall t, t = repeat 0 (zpref t) ++ skipn (zpref t) t.
Proof.
  intros t. rewrite <- zpref_firstn at 1. rewrite firstn_skipn. reflexivity.
Qed.

Lemma zpref_head : forall t, binary t ->
  skipn (zpref t) t = nil \/ nth 0 (skipn (zpref t) t) 0 = 1.
Proof.
  induction t as [|x t IH]; intros Hb; [ left; reflexivity |].
  inversion Hb as [| x0 l0 Hx Ht]; subst.
  cbn [zpref]. destruct (Z.eqb x 0) eqn:Ex.
  - cbn [skipn]. apply IH. exact Ht.
  - right. cbn [skipn nth].
    destruct Hx as [Hx | Hx]; [| exact Hx ].
    subst x. cbn in Ex. discriminate.
Qed.

Definition gcb (c : Z) (t : list Z) : bool :=
  match skipn (zpref t) t with
  | nil => true
  | u => Z.ltb (Z.of_nat (stop_len u)) (Z.of_nat (zpref t) + c)
  end.

Lemma saturate_nil : saturate nil = nil.
Proof. reflexivity. Qed.

Lemma criterion : forall j t, (1 <= j)%nat -> binary t ->
  Nat.eqb (stop_len (all_ones j ++ t)) j = gcb (- Z.of_nat j) t.
Proof.
  intros j t Hj Hbt.
  remember (zpref t) as z eqn:Hz.
  remember (skipn z t) as u eqn:Hu.
  assert (Hbu : binary u) by (rewrite Hu; apply binary_skipn; exact Hbt).
  assert (Hdec : all_ones j ++ t = Tstr j z u).
  { unfold Tstr, all_ones. f_equal. rewrite Hu, Hz. apply zpref_decomp. }
  unfold gcb. rewrite <- Hz, <- Hu.
  destruct u as [|x u'] eqn:Eu.
  - (* all-zero tail *)
    assert (Hstop : stop_len (Tstr j z nil) = j).
    { apply stop_len_blocked_gen.
      - constructor.
      - rewrite saturate_nil. destruct (Nat.eq_dec z 0) as [E|E].
        + subst z. rewrite nth_overflow by (rewrite T_length; cbn [length]; lia).
          discriminate.
        + rewrite (T_nth_mid j z nil j ltac:(lia) ltac:(lia)). discriminate.
      - rewrite saturate_nil. intros m Hm. cbn [length] in Hm. lia. }
    rewrite Hdec, Hstop. apply Nat.eqb_refl.
  - (* tail with a first one at distance z *)
    assert (Hu0 : nth 0 (x :: u') 0 = 1).
    { assert (H := zpref_head t Hbt). rewrite <- Hz, <- Hu in H.
      destruct H as [H | H]; [ discriminate | exact H ]. }
    destruct (Z.ltb_spec (Z.of_nat (stop_len (x :: u')))
                         (Z.of_nat z + - Z.of_nat j)) as [Hlt | Hge].
    + assert (Hstop : stop_len (Tstr j z (x :: u')) = j).
      { apply stop_len_blocked_gen.
        - exact Hbu.
        - assert (Hz1 : (1 <= z)%nat) by lia.
          rewrite (T_nth_mid j z (saturate (x :: u')) j ltac:(lia) ltac:(lia)).
          discriminate.
        - apply sat_key; [ exact Hbu | | lia ].
          intros _. exact Hu0. }
      rewrite Hdec, Hstop, Nat.eqb_refl. reflexivity.
    + assert (Hz1 : (1 <= z)%nat \/ z = 0%nat) by lia.
      assert (Hne : stop_len (Tstr j z (x :: u')) <> j).
      { destruct Hz1 as [Hz1 | Hz0].
        - intros Hcon. unfold stop_len in Hcon.
          apply (ones_prefix_stop__L3b (saturate (Tstr j z (x :: u')))).
          rewrite Hcon. apply unblockedB; try assumption; lia.
        - intros Hcon. unfold stop_len in Hcon. rewrite Hz0 in Hcon.
          apply (ones_prefix_stop__L3b (saturate (Tstr j 0 (x :: u')))).
          rewrite Hcon.
          destruct (saturate_props (Tstr j 0 (x :: u'))
                      (T_binary j 0 _ Hbu)) as [_ [_ Hd]].
          apply Hd.
          replace j with (j + 0 + 0)%nat at 1 by lia.
          rewrite T_nth_hi. exact Hu0. }
      rewrite Hdec.
      destruct (Nat.eqb_spec (stop_len (Tstr j z (x :: u'))) j) as [E|E];
        [ contradiction |].
      reflexivity.
Qed.

(* ================= block 10 : all_strings structure ================= *)

Lemma fold_seq_shift : forall (F : nat -> list (list Z) -> list (list Z)),
  (forall a b l, F a l = F b l) ->
  forall n a b, fold_right F [[]] (seq a n) = fold_right F [[]] (seq b n).
Proof.
  intros F HF. induction n as [|n IH]; intros a b; [ reflexivity |].
  cbn [seq fold_right]. rewrite (IH (S a) (S b)). apply HF.
Qed.

Lemma all_strings_S__L3b : forall n,
  all_strings (S n) = flat_map (fun s => [0 :: s; 1 :: s]) (all_strings n).
Proof.
  intros n. unfold all_strings. cbn [seq fold_right].
  f_equal. apply fold_seq_shift. reflexivity.
Qed.

Lemma all_strings_spec : forall n s, In s (all_strings n) ->
  length s = n /\ binary s.
Proof.
  induction n as [|n IH]; intros s Hin.
  - cbn in Hin. destruct Hin as [H | []]. subst s.
    split; [ reflexivity | constructor ].
  - rewrite all_strings_S__L3b in Hin.
    apply in_flat_map in Hin. destruct Hin as [s' [Hs' Hmem]].
    destruct (IH s' Hs') as [Hl Hb].
    cbn in Hmem. destruct Hmem as [H | [H | []]]; subst s;
      (split; [ cbn [length]; lia | constructor; [ (left; reflexivity) || (right; reflexivity) | exact Hb ] ]).
Qed.

Lemma length_flat_map_pair : forall (l : list (list Z)) (g : list Z -> list Z) (h : list Z -> list Z),
  length (flat_map (fun s => [g s; h s]) l) = (2 * length l)%nat.
Proof.
  induction l as [|x l IH]; intros g h; [ reflexivity |].
  cbn [flat_map length app]. rewrite IH. lia.
Qed.

Lemma all_strings_card : forall n, length (all_strings n) = (2 ^ n)%nat.
Proof.
  induction n as [|n IH]; [ reflexivity |].
  rewrite all_strings_S__L3b, length_flat_map_pair, IH.
  cbn [Nat.pow]. lia.
Qed.

Lemma filter_flat_map_pair : forall (P : list Z -> bool) (l : list (list Z)),
  length (filter P (flat_map (fun s => [0 :: s; 1 :: s]) l)) =
  (length (filter (fun s => P (0%Z :: s)) l) + length (filter (fun s => P (1%Z :: s)) l))%nat.
Proof.
  induction l as [|x l IH]; [ reflexivity |].
  cbn [flat_map].
  rewrite filter_app. cbn [filter length app].
  destruct (P (0%Z :: x)); destruct (P (1%Z :: x)); cbn [length]; rewrite length_app, IH; cbn [length]; lia.
Qed.

Definition cnt (P : list Z -> bool) (n : nat) : Z :=
  Z.of_nat (length (filter P (all_strings n))).

Lemma cnt_S : forall P n,
  cnt P (S n) = cnt (fun s => P (0%Z :: s)) n + cnt (fun s => P (1%Z :: s)) n.
Proof.
  intros P n. unfold cnt.
  rewrite all_strings_S__L3b, filter_flat_map_pair, Nat2Z.inj_add. reflexivity.
Qed.

Lemma cnt_0 : forall P, cnt P 0 = if P nil then 1 else 0.
Proof.
  intros P. unfold cnt. cbn [all_strings seq fold_right filter].
  destruct (P nil); reflexivity.
Qed.

Lemma gcb_cons0 : forall c t, gcb c (0 :: t) = gcb (c + 1) t.
Proof.
  intros c t. unfold gcb. cbn [zpref].
  rewrite Z.eqb_refl. cbn [skipn].
  destruct (skipn (zpref t) t) as [|y w]; [ reflexivity |].
  rewrite Nat2Z.inj_succ. f_equal. lia.
Qed.

Lemma gcb_cons1 : forall c t, gcb c (1 :: t) = Z.ltb (Z.of_nat (stop_len (1 :: t))) c.
Proof.
  intros c t. unfold gcb. cbn [zpref].
  cbn [Z.eqb]. cbn [skipn]. f_equal.
Qed.

Definition cntG (L : nat) (c : Z) : Z :=
  Z.of_nat (length (filter
    (fun s => andb (Z.eqb (nth 0 s 0) 1) (Z.ltb (Z.of_nat (stop_len s)) c))
    (all_strings L))).

Lemma filter_all_false : forall (P : list Z -> bool) (l : list (list Z)),
  (forall a, P a = false) -> filter P l = nil.
Proof.
  induction l as [|x l IH]; intros H; [ reflexivity |].
  cbn [filter]. rewrite H. apply IH. exact H.
Qed.

Lemma cntG_step : forall d c,
  cntG (S d) c = cnt (fun s => Z.ltb (Z.of_nat (stop_len (1 :: s))) c) d.
Proof.
  intros d c. unfold cntG, cnt.
  rewrite all_strings_S__L3b, filter_flat_map_pair.
  rewrite (filter_all_false
    (fun s => andb (Z.eqb (nth 0 (0%Z :: s) 0) 1) (Z.ltb (Z.of_nat (stop_len (0%Z :: s))) c))
    (all_strings d)) by (intros a; cbn [nth]; reflexivity).
  cbn [length plus]. f_equal.
Qed.

(* ================= block 11 : finite sums ================= *)

Definition Ssum (f : nat -> Z) (n : nat) : Z :=
  fold_right Z.add 0 (map f (seq 1 n)).

Lemma fold_add_app : forall l1 l2,
  fold_right Z.add 0 (l1 ++ l2) = fold_right Z.add 0 l1 + fold_right Z.add 0 l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2; cbn [app fold_right]; [ lia |].
  rewrite IH. lia.
Qed.

Lemma Ssum_S : forall f n, Ssum f (S n) = Ssum f n + f (S n).
Proof.
  intros f n. unfold Ssum.
  rewrite seq_S, map_app, fold_add_app. cbn [map fold_right].
  replace (1 + n)%nat with (S n) by lia. lia.
Qed.

Lemma Ssum_ext_in : forall f g n,
  (forall L, (1 <= L)%nat -> (L <= n)%nat -> f L = g L) -> Ssum f n = Ssum g n.
Proof.
  intros f g n. induction n as [|n IH]; intros H; [ reflexivity |].
  rewrite !Ssum_S, IH by (intros L H1 H2; apply H; lia).
  rewrite (H (S n)) by lia. reflexivity.
Qed.

Lemma Ssum_plus : forall f g n,
  Ssum (fun L => f L + g L) n = Ssum f n + Ssum g n.
Proof.
  intros f g n. induction n as [|n IH]; [ reflexivity |].
  rewrite !Ssum_S, IH. lia.
Qed.

Lemma Ssum_trunc : forall f m n, (m <= n)%nat ->
  (forall L, (m < L)%nat -> f L = 0) -> Ssum f n = Ssum f m.
Proof.
  intros f m n. induction n as [|n IH]; intros Hmn H.
  - replace m with 0%nat by lia. reflexivity.
  - destruct (Nat.eq_dec m (S n)) as [E|E]; [ subst m; reflexivity |].
    rewrite Ssum_S, H by lia. rewrite IH by (lia || assumption). lia.
Qed.

Lemma Ssum_zero : forall n, Ssum (fun _ => 0) n = 0.
Proof.
  induction n as [|n IH]; [ reflexivity | rewrite Ssum_S, IH; lia ].
Qed.

Lemma cnt_ext : forall P Q n, (forall s, P s = Q s) -> cnt P n = cnt Q n.
Proof. intros P Q n H. unfold cnt. rewrite (filter_ext P Q H). reflexivity. Qed.

Lemma cnt_gcb : forall d c,
  cnt (gcb c) d = 1 + Ssum (fun L => cntG L (c + Z.of_nat (d - L))) d.
Proof.
  induction d as [|d IH]; intros c.
  - rewrite cnt_0. cbn [Ssum map seq fold_right]. reflexivity.
  - rewrite cnt_S.
    rewrite (cnt_ext (fun s => gcb c (0%Z :: s)) (gcb (c + 1)) d)
      by (intros a; apply gcb_cons0).
    rewrite (cnt_ext (fun s => gcb c (1%Z :: s))
                     (fun s => Z.ltb (Z.of_nat (stop_len (1%Z :: s))) c) d)
      by (intros a; apply gcb_cons1).
    rewrite <- cntG_step.
    rewrite IH.
    rewrite Ssum_S.
    replace (S d - S d)%nat with 0%nat by lia.
    rewrite Nat2Z.inj_0, Z.add_0_r.
    rewrite (Ssum_ext_in (fun L => cntG L (c + Z.of_nat (S d - L)))
                         (fun L => cntG L (c + 1 + Z.of_nat (d - L))) d).
    + lia.
    + intros L H1 H2. f_equal.
      replace (S d - L)%nat with (S (d - L)) by lia.
      rewrite Nat2Z.inj_succ. lia.
Qed.

(* ================= block 12 : cntG vs cntP ================= *)

Lemma filter_all_true : forall (P : list Z -> bool) (l : list (list Z)),
  (forall a, In a l -> P a = true) -> filter P l = l.
Proof.
  induction l as [|x l IH]; intros H; [ reflexivity |].
  cbn [filter]. rewrite (H x ltac:(now left)). f_equal.
  apply IH. intros a Ha. apply H. now right.
Qed.

Lemma filter_ext_in_Z : forall (P Q : list Z -> bool) (l : list (list Z)),
  (forall a, In a l -> P a = Q a) -> filter P l = filter Q l.
Proof.
  induction l as [|x l IH]; intros H; [ reflexivity |].
  cbn [filter]. rewrite (H x ltac:(now left)).
  rewrite IH by (intros a Ha; apply H; now right). reflexivity.
Qed.

Lemma ltb_leb_conv : forall n c, 1 <= c ->
  Z.ltb (Z.of_nat n) c = Nat.leb n (Z.to_nat (c - 1)).
Proof.
  intros n c Hc.
  destruct (Z.ltb_spec (Z.of_nat n) c) as [H1|H1];
  destruct (Nat.leb_spec n (Z.to_nat (c - 1))) as [H2|H2];
    try reflexivity; exfalso; lia.
Qed.

Lemma cntG_zero : forall L c, c <= 0 -> cntG L c = 0.
Proof.
  intros L c Hc. unfold cntG.
  rewrite filter_all_false; [ reflexivity |].
  intros a.
  replace (Z.ltb (Z.of_nat (stop_len a)) c) with false;
    [ destruct (Z.eqb (nth 0 a 0) 1); reflexivity |].
  symmetry. apply Z.ltb_ge. pose proof (Nat2Z.is_nonneg (stop_len a)). lia.
Qed.

Lemma cntG_cntP : forall L c, 1 <= c -> cntG L c = cntP L (Z.to_nat (c - 1)).
Proof.
  intros L c Hc. unfold cntG, cntP. f_equal. f_equal.
  apply filter_ext. intros a. f_equal. apply ltb_leb_conv. exact Hc.
Qed.

Lemma head1_card : forall n,
  length (filter (fun s => Z.eqb (nth 0 s 0) 1) (all_strings (S n))) = (2 ^ n)%nat.
Proof.
  intros n. rewrite all_strings_S__L3b, filter_flat_map_pair.
  rewrite (filter_all_false (fun s => Z.eqb (nth 0 (0%Z :: s) 0) 1) (all_strings n))
    by (intros a; reflexivity).
  rewrite (filter_all_true (fun s => Z.eqb (nth 0 (1%Z :: s) 0) 1) (all_strings n))
    by (intros a _; reflexivity).
  cbn [length]. rewrite all_strings_card. lia.
Qed.

Lemma cntP_full : forall L t, (1 <= L)%nat -> (L <= t)%nat ->
  cntP L t = 2 ^ (Z.of_nat L - 1).
Proof.
  intros L t H1 Ht. unfold cntP.
  rewrite (filter_ext_in_Z _ (fun s => Z.eqb (nth 0 s 0) 1)).
  - destruct L as [|L']; [ lia |].
    rewrite head1_card.
    rewrite Nat2Z.inj_pow, Nat2Z.inj_succ.
    replace (Z.of_nat 2) with 2 by reflexivity. f_equal. lia.
  - intros a Ha. destruct (all_strings_spec L a Ha) as [Hla Hba].
    assert (Hle : Nat.leb (stop_len a) t = true).
    { apply Nat.leb_le. pose proof (stop_len_le a Hba). lia. }
    rewrite Hle. destruct (Z.eqb (nth 0 a 0) 1); reflexivity.
Qed.

Lemma Ssum_pow : forall m, Ssum (fun L => 2 ^ (Z.of_nat L - 1)) m = 2 ^ (Z.of_nat m) - 1.
Proof.
  induction m as [|m IH]; [ reflexivity |].
  rewrite Ssum_S, IH, Nat2Z.inj_succ.
  rewrite Z.pow_succ_r by apply Nat2Z.is_nonneg.
  replace (Z.succ (Z.of_nat m) - 1) with (Z.of_nat m) by lia. lia.
Qed.

Lemma cntW_cnt : forall d j, (1 <= j)%nat ->
  cntW d j = cnt (gcb (- Z.of_nat j)) d.
Proof.
  intros d j Hj. unfold cntW, cnt. f_equal. f_equal.
  apply filter_ext_in_Z. intros a Ha.
  destruct (all_strings_spec d a Ha) as [_ Hb].
  apply criterion; assumption.
Qed.

(* ================= block 13 : arithmetic of Lmax ================= *)

Lemma lmax_facts : forall d j,
  2 * Lmax_of d j <= D_of d j /\ D_of d j <= 2 * Lmax_of d j + 1.
Proof.
  intros d j. unfold Lmax_of, D_of.
  set (a := Z.of_nat d + Z.of_nat j + 2).
  pose proof (Z.div_mod a 2 ltac:(lia)) as Hdm.
  pose proof (Z.mod_pos_bound a 2 ltac:(lia)) as Hmb.
  assert (Ha : a = Z.of_nat d + Z.of_nat j + 2) by reflexivity.
  lia.
Qed.

Lemma sum_split_B : forall d j, (1 <= j)%nat -> 0 <= D_of d j ->
  Ssum (fun L => cntG L (- Z.of_nat j + Z.of_nat (d - L))) d
  = cntQ (Z.to_nat (D_of d j)) + (2 ^ (Lmax_of d j) - 1).
Proof.
  intros d j Hj HD.
  pose proof (lmax_facts d j) as [HL1 HL2].
  assert (HDdef : D_of d j = Z.of_nat d - Z.of_nat j - 1) by reflexivity.
  assert (HLpos : 0 <= Lmax_of d j) by lia.
  remember (Z.to_nat (D_of d j)) as Dn eqn:EDn.
  remember (Z.to_nat (Lmax_of d j)) as m eqn:Em.
  assert (HDnZ : Z.of_nat Dn = D_of d j) by (rewrite EDn; apply Z2Nat.id; lia).
  assert (HmZ : Z.of_nat m = Lmax_of d j) by (rewrite Em; apply Z2Nat.id; lia).
  clear EDn Em.
  assert (Hdn : (Dn <= d)%nat) by lia.
  assert (HmDn1 : (2 * m <= Dn)%nat) by lia.
  assert (HmDn2 : (Dn <= 2 * m + 1)%nat) by lia.
  rewrite (Ssum_trunc _ Dn d Hdn).
  2:{ intros L HL. apply cntG_zero. lia. }
  rewrite (Ssum_ext_in _
    (fun L => (if Nat.ltb (Dn - L) L then cntP L (Dn - L) else 0)
              + (if Nat.ltb (Dn - L) L then 0 else 2 ^ (Z.of_nat L - 1))) Dn).
  2:{ intros L H1 H2.
      rewrite cntG_cntP by lia.
      replace (Z.to_nat (- Z.of_nat j + Z.of_nat (d - L) - 1)) with (Dn - L)%nat by lia.
      destruct (Nat.ltb_spec (Dn - L) L) as [Hc | Hc]; [ lia |].
      rewrite (cntP_full L (Dn - L)%nat ltac:(lia) ltac:(lia)). lia. }
  rewrite Ssum_plus.
  f_equal.
  assert (Htr : forall L, (m < L)%nat ->
    (if Nat.ltb (Dn - L) L then 0 else 2 ^ (Z.of_nat L - 1)) = 0).
  { intros L HL. destruct (Nat.ltb_spec (Dn - L) L); [ reflexivity | lia ]. }
  rewrite (Ssum_trunc (fun L => if Nat.ltb (Dn - L) L then 0 else 2 ^ (Z.of_nat L - 1))
             m Dn ltac:(lia) Htr).
    rewrite (Ssum_ext_in _ (fun L => 2 ^ (Z.of_nat L - 1)) m).
    + rewrite Ssum_pow, HmZ. reflexivity.
    + intros L H1 H2. destruct (Nat.ltb_spec (Dn - L) L); [ lia | reflexivity ].
Qed.

(* ================= block 14 : the formula ================= *)

Theorem W_formula : forall d j, (1 <= j)%nat -> cntW d j = Wformula d j.
Proof.
  intros d j Hj.
  rewrite cntW_cnt by exact Hj. rewrite cnt_gcb. unfold Wformula.
  pose proof (lmax_facts d j) as [HL1 HL2].
  assert (HDdef : D_of d j = Z.of_nat d - Z.of_nat j - 1) by reflexivity.
  destruct (Z.leb_spec 0 (D_of d j)) as [HD | HD].
  - rewrite sum_split_B by assumption.
    assert (HLpos : 0 <= Lmax_of d j) by lia.
    destruct (Z.leb_spec 1 (Lmax_of d j)) as [H1 | H1]; [ lia |].
    assert (HL0 : Lmax_of d j = 0) by lia.
    rewrite HL0, Z.pow_0_r. lia.
  - destruct (Z.leb_spec 1 (Lmax_of d j)) as [H1 | H1]; [ lia |].
    rewrite (Ssum_ext_in _ (fun _ => 0) d).
    + rewrite Ssum_zero. lia.
    + intros L HL1' HL2'. apply cntG_zero. lia.
Qed.


(* ---------- from L4.v ---------- *)


(* ================= block A : fiber decomposition of a filter count ======= *)

Lemma Ssum_0 : forall f, Ssum f 0 = 0.
Proof. intros f. reflexivity. Qed.

Lemma Ssum_indic : forall k N, (1 <= k)%nat ->
  Ssum (fun j => if Nat.eqb k j then 1 else 0) N = if Nat.leb k N then 1 else 0.
Proof.
  intros k N Hk. induction N as [|N IH].
  - rewrite Ssum_0.
    destruct (Nat.leb_spec k 0) as [H|H]; [ lia | reflexivity ].
  - rewrite Ssum_S, IH.
    destruct (Nat.leb_spec k N) as [H1|H1];
    destruct (Nat.eqb_spec k (S N)) as [H2|H2];
    destruct (Nat.leb_spec k (S N)) as [H3|H3]; lia.
Qed.

Lemma fiber_cumul : forall (P : list Z -> bool) (f : list Z -> nat) (N : nat)
                           (l : list (list Z)),
  (forall s, In s l -> P s = true -> (1 <= f s)%nat) ->
  Ssum (fun j => Z.of_nat (length (filter (fun s => andb (P s) (Nat.eqb (f s) j)) l))) N
  = Z.of_nat (length (filter (fun s => andb (P s) (Nat.leb (f s) N)) l)).
Proof.
  intros P f N l. induction l as [|x l IH]; intros Hpos.
  - cbn [filter length]. rewrite (Ssum_ext_in _ (fun _ => 0) N)
      by (intros L _ _; reflexivity).
    rewrite Ssum_zero. reflexivity.
  - assert (Hl : forall s, In s l -> P s = true -> (1 <= f s)%nat)
      by (intros s Hs; apply Hpos; now right).
    specialize (IH Hl).
    destruct (P x) eqn:EPx.
    + assert (Hfx : (1 <= f x)%nat) by (apply Hpos; [ now left | exact EPx ]).
      rewrite (Ssum_ext_in _
        (fun j => (if Nat.eqb (f x) j then 1 else 0)
                  + Z.of_nat (length (filter (fun s => andb (P s) (Nat.eqb (f s) j)) l))) N).
      2:{ intros L _ _. cbn [filter]. rewrite EPx. cbn [andb].
          destruct (Nat.eqb (f x) L); cbn [length]; lia. }
      rewrite Ssum_plus, IH, (Ssum_indic (f x) N Hfx).
      cbn [filter]. rewrite EPx. cbn [andb].
      destruct (Nat.leb (f x) N); cbn [length]; lia.
    + rewrite (Ssum_ext_in _
        (fun j => Z.of_nat (length (filter (fun s => andb (P s) (Nat.eqb (f s) j)) l))) N).
      2:{ intros L _ _. cbn [filter]. rewrite EPx. cbn [andb]. reflexivity. }
      rewrite IH. cbn [filter]. rewrite EPx. cbn [andb]. reflexivity.
Qed.

(* ================= block B : count_stop / cntP / count_rated ============= *)

Lemma stop_cumul : forall i t, Ssum (fun j => count_stop i j) t = cntP i t.
Proof.
  intros i t. unfold count_stop, cntP.
  apply (fiber_cumul (fun s => Z.eqb (nth 0 s 0) 1) stop_len t (all_strings i)).
  intros s Hin Hp. apply Z.eqb_eq in Hp.
  destruct (all_strings_spec i s Hin) as [_ Hb].
  apply stop_len_pos; assumption.
Qed.

Lemma ones_prefix_repeat1 : forall n, ones_prefix (repeat 1 n) = n.
Proof.
  induction n as [|n IH]; [ reflexivity |].
  cbn [repeat ones_prefix]. rewrite IH. reflexivity.
Qed.

Lemma sat_all_ones_iff : forall s, binary s ->
  (saturate s = all_ones (length s) <-> stop_len s = length s).
Proof.
  intros s Hb. unfold stop_len, all_ones. split.
  - intros H. rewrite H. apply ones_prefix_repeat1.
  - intros H.
    destruct (saturate_props s Hb) as [Hlen _].
    pose proof (firstn_ones_prefix (saturate s)) as Hf.
    rewrite H, <- Hlen in Hf. rewrite firstn_all in Hf.
    rewrite Hf, Hlen. reflexivity.
Qed.

Lemma stop_len_head : forall s, binary s -> (1 <= stop_len s)%nat -> nth 0 s 0 = 1.
Proof.
  intros s Hb H.
  apply (chain_head s (saturate s)); [ apply chain_saturate |].
  apply ones_prefix_ones. unfold stop_len in H. lia.
Qed.

Lemma rated_eq_stop : forall i, (1 <= i)%nat -> count_rated i = count_stop i i.
Proof.
  intros i Hi. unfold count_rated, count_stop. f_equal. f_equal.
  apply filter_ext_in_Z. intros a Ha.
  destruct (all_strings_spec i a Ha) as [Hla Hba].
  unfold rated_bool.
  destruct (list_eq_dec Z.eq_dec (saturate a) (all_ones (length a))) as [E|E].
  - assert (Hs : stop_len a = i)
      by (rewrite <- Hla; apply (sat_all_ones_iff a Hba); exact E).
    assert (Hh : nth 0 a 0 = 1)
      by (apply stop_len_head; [ exact Hba | lia ]).
    rewrite Hh, Z.eqb_refl, Hs, Nat.eqb_refl. reflexivity.
  - destruct (Nat.eqb_spec (stop_len a) i) as [Hs|Hs].
    + exfalso. apply E. apply (sat_all_ones_iff a Hba). rewrite Hla. exact Hs.
    + rewrite Bool.andb_false_r. reflexivity.
Qed.

(* ================= block C : the partition lemma ========================= *)

Lemma partition_pow : forall i, (1 <= i)%nat ->
  2 ^ (Z.of_nat i - 1) = count_rated i
                       + fold_right Z.add 0 (map (fun j => count_stop i j) (seq 1 (i-1))).
Proof.
  intros i Hi. destruct i as [|i']; [ lia |].
  replace (S i' - 1)%nat with i' by lia.
  change (fold_right Z.add 0 (map (fun j => count_stop (S i') j) (seq 1 i')))
    with (Ssum (fun j => count_stop (S i') j) i').
  rewrite (rated_eq_stop (S i') Hi).
  rewrite Z.add_comm.
  rewrite <- (Ssum_S (fun j => count_stop (S i') j) i').
  rewrite stop_cumul. symmetry. apply cntP_full; lia.
Qed.

(* ================= block D : small kit =================================== *)

Lemma replace_nth_length : forall {A : Type} k (l : list A) (a : A),
  length (replace_nth k l a) = length l.
Proof.
  intros A k l. revert k. induction l as [|x l IH]; intros k a; [ destruct k; reflexivity |].
  destruct k as [|k]; cbn [replace_nth length]; [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma replace_Znth_length : forall {A : Type} (i : Z) (a : A) (l : list A),
  length (replace_Znth i a l) = length l.
Proof. intros. unfold replace_Znth. apply replace_nth_length. Qed.

Lemma Zeros_Zlength : forall k, 0 <= k -> Zlength (Zeros k) = k.
Proof.
  intros k Hk. unfold Zeros. rewrite Zlength_correct, repeat_length. lia.
Qed.

Lemma Znth_Zeros : forall k i, Znth i (Zeros k) 0 = 0.
Proof. intros k i. unfold Zeros. apply Znth_repeat. Qed.

Definition Qg (D L : nat) : Z := if Nat.ltb (D - L) L then cntP L (D - L) else 0.

Lemma cntQ_Ssum : forall D, cntQ D = Ssum (Qg D) D.
Proof. intros D. reflexivity. Qed.

Lemma cntP_zero : forall L, cntP L 0 = 0.
Proof. intros L. rewrite <- (stop_cumul L 0). apply Ssum_0. Qed.

Lemma Qg_zero_big : forall D L, (D < L)%nat -> Qg D L = 0.
Proof.
  intros D L H. unfold Qg.
  replace (D - L)%nat with 0%nat by lia.
  destruct (Nat.ltb_spec 0 L) as [_|Hc]; [ apply cntP_zero | reflexivity ].
Qed.

Lemma Ssum_Qg_stab : forall D i, (D <= i)%nat -> Ssum (Qg D) i = cntQ D.
Proof.
  intros D i H. rewrite cntQ_Ssum.
  apply (Ssum_trunc (Qg D) D i H). intros L HL. apply Qg_zero_big. exact HL.
Qed.

Definition AOK (m : Z) (lA : list Z) (i : nat) : Prop :=
  forall k, (1 <= k)%nat -> (k <= i)%nat ->
    Znth (Z.of_nat k) lA 0 = count_rated k mod m.

Definition QOK (m : Z) (lQ : list Z) (i : nat) : Prop :=
  forall D, (D <= i)%nat -> Znth (Z.of_nat D) lQ 0 = cntQ D mod m.

(* ================= block E : the row-local W / Brow values =============== *)

Lemma Wfun_w1 : forall m L, 0 < m ->
  (if Z.geb L 1 then (1 mod m + Pow2Mod L m - 1 mod m + m) mod m else 1 mod m)
  = (1 + (if Z.leb 1 L then 2 ^ L - 1 else 0)) mod m.
Proof.
  intros m L Hm. unfold Pow2Mod.
  destruct (Z.geb_spec L 1) as [H|H];
  destruct (Z.leb_spec 1 L) as [H2|H2]; try lia.
  - replace (1 mod m + 2 ^ L mod m - 1 mod m + m) with (2 ^ L mod m + 1 * m) by lia.
    rewrite Z_mod_plus_full, Z.mod_mod by lia.
    f_equal. lia.
  - f_equal.
Qed.

Lemma Wfun_correct : forall m lQ i j, 0 < m -> (1 <= j)%nat -> (j < i)%nat ->
  QOK m lQ (i-1) ->
  Wfun lQ (Z.of_nat i - Z.of_nat j) (Z.of_nat j) m = Wformula (i-j) j mod m.
Proof.
  intros m lQ i j Hm Hj Hji HQ.
  replace (Z.of_nat i - Z.of_nat j) with (Z.of_nat (i - j)%nat) by lia.
  unfold Wfun, Wformula.
  rewrite Wfun_w1 by exact Hm.
  change (Z.of_nat (i - j) - (Z.of_nat (i - j) + Z.of_nat j + 2) / 2)
    with (Lmax_of (i - j) j).
  change (Z.of_nat (i - j) - Z.of_nat j - 1) with (D_of (i - j) j).
  set (X := 1 + (if Z.leb 1 (Lmax_of (i - j) j) then 2 ^ (Lmax_of (i - j) j) - 1 else 0)).
  assert (HD : D_of (i - j) j = Z.of_nat i - 2 * Z.of_nat j - 1)
    by (unfold D_of; lia).
  destruct (Z.geb_spec (D_of (i - j) j) 0) as [H|H];
  destruct (Z.leb_spec 0 (D_of (i - j) j)) as [H2|H2]; try lia.
  - rewrite <- (Z2Nat.id (D_of (i - j) j)) at 1 by lia.
    rewrite (HQ (Z.to_nat (D_of (i - j) j)) ltac:(lia)).
    rewrite Z.add_mod_idemp_l by lia.
    rewrite Z.add_mod_idemp_r by lia. reflexivity.
  - rewrite Z.add_0_r. reflexivity.
Qed.

Lemma Brow_correct : forall m lA lQ i j, 0 < m -> (1 <= j)%nat -> (j < i)%nat ->
  AOK m lA (i-1) -> QOK m lQ (i-1) ->
  BrowEntry lA lQ (Z.of_nat i) (Z.of_nat j) m = count_stop i j mod m.
Proof.
  intros m lA lQ i j Hm Hj Hji HA HQ. unfold BrowEntry.
  rewrite (HA j Hj ltac:(lia)).
  rewrite (Wfun_correct m lQ i j Hm Hj Hji HQ).
  rewrite <- Z.mul_mod by lia.
  rewrite <- (W_formula (i - j) j Hj).
  rewrite (fiber_count i j Hj Hji). reflexivity.
Qed.

Lemma BlockedNat_correct : forall m lA lQ i c, 0 < m -> (c <= i - 1)%nat ->
  AOK m lA (i-1) -> QOK m lQ (i-1) ->
  BlockedNat lA lQ (Z.of_nat i) m c = Ssum (fun j => count_stop i j) c mod m.
Proof.
  intros m lA lQ i c Hm. revert c. induction c as [|c IH]; intros Hc HA HQ.
  - cbn [BlockedNat]. rewrite Ssum_0, Z.mod_0_l by lia. reflexivity.
  - cbn [BlockedNat]. rewrite (IH ltac:(lia) HA HQ).
    rewrite (Brow_correct m lA lQ i (S c) Hm ltac:(lia) ltac:(lia) HA HQ).
    rewrite <- Z.add_mod by lia. rewrite <- Ssum_S. reflexivity.
Qed.

(* ================= block F : A[i] and the prefix sums ==================== *)

Lemma ARowVal_correct : forall m lA lQ i, 0 < m -> (1 <= i)%nat ->
  AOK m lA (i-1) -> QOK m lQ (i-1) ->
  ARowVal lA lQ (Z.of_nat i) m = count_rated i mod m.
Proof.
  intros m lA lQ i Hm Hi HA HQ.
  unfold ARowVal, Blocked, Pow2Mod.
  replace (Z.to_nat (Z.of_nat i - 1)) with (i - 1)%nat by lia.
  rewrite (BlockedNat_correct m lA lQ i (i-1) Hm ltac:(lia) HA HQ).
  rewrite <- Zminus_mod.
  replace ((2 ^ (Z.of_nat i - 1) - Ssum (fun j => count_stop i j) (i - 1)) mod m + m)
    with ((2 ^ (Z.of_nat i - 1) - Ssum (fun j => count_stop i j) (i - 1)) mod m + 1 * m) by lia.
  rewrite Z_mod_plus_full, Z.mod_mod by lia.
  pose proof (partition_pow i Hi) as HP.
  change (fold_right Z.add 0 (map (fun j => count_stop i j) (seq 1 (i-1))))
    with (Ssum (fun j => count_stop i j) (i-1)) in HP.
  f_equal. lia.
Qed.

Lemma RunNat_correct : forall m lA lQ i k, 0 < m -> (k <= i)%nat ->
  AOK m lA (i-1) -> QOK m lQ (i-1) ->
  RunNat lA lQ (Z.of_nat i) m k = Ssum (fun j => count_stop i j) (k - 1) mod m.
Proof.
  intros m lA lQ i k Hm. revert k. induction k as [|k IH]; intros Hk HA HQ.
  - cbn [RunNat]. rewrite Ssum_0, Z.mod_0_l by lia. reflexivity.
  - cbn [RunNat]. rewrite (IH ltac:(lia) HA HQ).
    destruct k as [|k'].
    + cbn [Z.of_nat]. unfold RowC. rewrite Z.eqb_refl.
      rewrite Ssum_0, Z.mod_0_l by lia. reflexivity.
    + unfold RowC.
      replace (Z.eqb (Z.of_nat (S k')) 0) with false
        by (symmetry; apply Z.eqb_neq; lia).
      replace (Z.ltb (Z.of_nat (S k')) (Z.of_nat i)) with true
        by (symmetry; apply Z.ltb_lt; lia).
      rewrite (Brow_correct m lA lQ i (S k') Hm ltac:(lia) ltac:(lia) HA HQ).
      rewrite <- Z.add_mod by lia.
      replace (S k' - 1)%nat with k' by lia.
      replace (S (S k') - 1)%nat with (S k') by lia.
      rewrite <- Ssum_S. reflexivity.
Qed.

Lemma PEntry_correct : forall m lA lQ i t, 0 < m -> (t < i)%nat ->
  AOK m lA (i-1) -> QOK m lQ (i-1) ->
  PEntry lA lQ (Z.of_nat i) m (Z.of_nat t) = cntP i t mod m.
Proof.
  intros m lA lQ i t Hm Ht HA HQ. unfold PEntry, RunUpto.
  replace (Z.to_nat (Z.of_nat t + 1)) with (S t) by lia.
  rewrite (RunNat_correct m lA lQ i (S t) Hm ltac:(lia) HA HQ).
  replace (S t - 1)%nat with t by lia.
  rewrite stop_cumul. reflexivity.
Qed.

(* ================= block G : the Q row update ============================ *)

Lemma QAfterNat_Zlength : forall lQ lA i m n k,
  Zlength (QAfterNat lQ lA i m n k) = Zlength lQ.
Proof.
  intros lQ lA i m n k. induction k as [|k IH]; [ reflexivity |].
  cbn [QAfterNat].
  destruct (Z.leb (i + Z.of_nat k) (2 * n)); [| exact IH ].
  rewrite !Zlength_correct, replace_Znth_length, <- !Zlength_correct. exact IH.
Qed.

Lemma QAfterNat_char : forall lQ lA (m i n : Z) (k D : nat),
  0 <= i ->
  i + Z.of_nat k <= 2 * n + 1 ->
  i + Z.of_nat k <= Zlength lQ ->
  0 <= Z.of_nat D < Zlength lQ ->
  Znth (Z.of_nat D) (QAfterNat lQ lA i m n k) 0 =
    if andb (Z.leb i (Z.of_nat D)) (Z.ltb (Z.of_nat D) (i + Z.of_nat k))
    then (Znth (Z.of_nat D) lQ 0 + PEntry lA lQ i m (Z.of_nat D - i)) mod m
    else Znth (Z.of_nat D) lQ 0.
Proof.
  intros lQ lA m i n k. induction k as [|k IH]; intros D Hi Hk Hlen HD.
  - cbn [QAfterNat].
    destruct (Z.leb_spec i (Z.of_nat D)) as [H1|H1];
    destruct (Z.ltb_spec (Z.of_nat D) (i + Z.of_nat 0)) as [H2|H2];
      cbn [andb]; try reflexivity. exfalso. cbn in H2. lia.
  - rewrite Nat2Z.inj_succ in Hk, Hlen |- *.
    assert (Hg : Z.leb (i + Z.of_nat k) (2 * n) = true) by (apply Z.leb_le; lia).
    assert (Hrng : 0 <= i + Z.of_nat k < Zlength lQ) by lia.
    assert (HIH : forall D', 0 <= Z.of_nat D' < Zlength lQ ->
      Znth (Z.of_nat D') (QAfterNat lQ lA i m n k) 0 =
        if andb (Z.leb i (Z.of_nat D')) (Z.ltb (Z.of_nat D') (i + Z.of_nat k))
        then (Znth (Z.of_nat D') lQ 0 + PEntry lA lQ i m (Z.of_nat D' - i)) mod m
        else Znth (Z.of_nat D') lQ 0)
      by (intros D' HD'; apply IH; lia).
    cbn [QAfterNat]. rewrite Hg.
    pose proof (QAfterNat_Zlength lQ lA i m n k) as HL.
    destruct (Z.eq_dec (Z.of_nat D) (i + Z.of_nat k)) as [E|E].
    + rewrite E. rewrite (Znth_replace_Znth_Same 0 (QAfterNat lQ lA i m n k) (i + Z.of_nat k) _ ltac:(lia)).
      rewrite <- E. rewrite (HIH D HD).
      replace (Z.ltb (Z.of_nat D) (i + Z.of_nat k)) with false
        by (symmetry; apply Z.ltb_ge; lia).
      rewrite Bool.andb_false_r.
      replace (Z.leb i (Z.of_nat D)) with true by (symmetry; apply Z.leb_le; lia).
      replace (Z.ltb (Z.of_nat D) (i + Z.succ (Z.of_nat k))) with true
        by (symmetry; apply Z.ltb_lt; lia).
      cbn [andb]. rewrite E. replace (i + Z.of_nat k - i) with (Z.of_nat k) by lia.
      reflexivity.
    + rewrite (Znth_replace_Znth_Diff 0 (QAfterNat lQ lA i m n k) (i + Z.of_nat k) (Z.of_nat D) _ ltac:(lia) ltac:(lia) ltac:(lia)).
      rewrite (HIH D HD).
      replace (Z.ltb (Z.of_nat D) (i + Z.succ (Z.of_nat k)))
        with (Z.ltb (Z.of_nat D) (i + Z.of_nat k)).
      * reflexivity.
      * destruct (Z.ltb_spec (Z.of_nat D) (i + Z.of_nat k)) as [H1|H1];
        destruct (Z.ltb_spec (Z.of_nat D) (i + Z.succ (Z.of_nat k))) as [H2|H2];
          try reflexivity; exfalso; lia.
Qed.

(* ================= block H : the DP invariant ============================ *)

Definition QINV (m n : Z) (lQ : list Z) (i : nat) : Prop :=
  forall D, Z.of_nat D <= 2 * n -> Znth (Z.of_nat D) lQ 0 = Ssum (Qg D) i mod m.

Lemma QINV_QOK : forall m n lQ i, 0 <= n -> Z.of_nat i <= n ->
  QINV m n lQ i -> QOK m lQ i.
Proof.
  intros m n lQ i Hn Hi H D HD.
  rewrite (H D ltac:(lia)). rewrite (Ssum_Qg_stab D i HD). reflexivity.
Qed.

Lemma DP_inv : forall m n, 0 < m -> 0 <= n -> forall i, Z.of_nat i <= n ->
  Zlength (fst (DPNat m n i)) = n + 2 /\
  Zlength (snd (DPNat m n i)) = 2 * n + 4 /\
  AOK m (fst (DPNat m n i)) i /\
  QINV m n (snd (DPNat m n i)) i.
Proof.
  intros m n Hm Hn i. induction i as [|i IH]; intros Hi.
  - cbn [DPNat fst snd].
    split; [ apply Zeros_Zlength; lia
           | split; [ apply Zeros_Zlength; lia | split ] ].
    + intros k H1 H2. lia.
    + intros D HD. rewrite Znth_Zeros, Ssum_0, Z.mod_0_l by lia. reflexivity.
  - destruct (IH ltac:(lia)) as [HlA [HlQ [HA HQI]]].
    assert (HQ : QOK m (snd (DPNat m n i)) i)
      by (apply (QINV_QOK m n _ i); [ lia | lia | exact HQI ]).
    cbn [DPNat fst snd].
    set (lA := fst (DPNat m n i)) in *.
    set (lQ := snd (DPNat m n i)) in *.
    replace (Z.to_nat (Z.of_nat (S i))) with (S i) by lia.
    assert (HA1 : AOK m lA (S i - 1))
      by (replace (S i - 1)%nat with i by lia; exact HA).
    assert (HQ1 : QOK m lQ (S i - 1))
      by (replace (S i - 1)%nat with i by lia; exact HQ).
    assert (HA' : Zlength (replace_Znth (Z.of_nat (S i))
                    (ARowVal lA lQ (Z.of_nat (S i)) m) lA) = n + 2).
    { rewrite Zlength_correct, replace_Znth_length, <- Zlength_correct. exact HlA. }
    split; [ exact HA' | split; [ rewrite QAfterNat_Zlength; exact HlQ | split ] ].
    + intros k Hk1 Hk2.
      destruct (Nat.eq_dec k (S i)) as [Ek|Ek].
      * subst k.
        rewrite (Znth_replace_Znth_Same 0 lA (Z.of_nat (S i)) _ ltac:(lia)).
        apply (ARowVal_correct m lA lQ (S i) Hm ltac:(lia) HA1 HQ1).
      * rewrite (Znth_replace_Znth_Diff 0 lA (Z.of_nat (S i)) (Z.of_nat k) _
                   ltac:(lia) ltac:(lia) ltac:(lia)).
        apply HA; lia.
    + intros D HD.
      rewrite (QAfterNat_char lQ lA m (Z.of_nat (S i)) n (S i) D
                 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      destruct (Z.leb_spec (Z.of_nat (S i)) (Z.of_nat D)) as [C1|C1];
      destruct (Z.ltb_spec (Z.of_nat D) (Z.of_nat (S i) + Z.of_nat (S i))) as [C2|C2];
        cbn [andb]; rewrite (HQI D HD); rewrite Ssum_S.
      * replace (Z.of_nat D - Z.of_nat (S i)) with (Z.of_nat (D - S i)%nat) by lia.
        rewrite (PEntry_correct m lA lQ (S i) (D - S i)%nat Hm ltac:(lia) HA1 HQ1).
        rewrite <- Z.add_mod by lia. f_equal. unfold Qg.
        destruct (Nat.ltb_spec (D - S i)%nat (S i)) as [C3|C3]; [ reflexivity | lia ].
      * f_equal. unfold Qg.
        destruct (Nat.ltb_spec (D - S i)%nat (S i)) as [C3|C3]; [ lia | lia ].
      * rewrite (Qg_zero_big D (S i) ltac:(lia)). f_equal. lia.
      * rewrite (Qg_zero_big D (S i) ltac:(lia)). f_equal. lia.
Qed.

(* --- the invariant in the two shapes that were asked for --- *)

Corollary DPA_correct : forall m n i k, 0 < m -> 0 <= n -> Z.of_nat i <= n ->
  (1 <= k)%nat -> (k <= i)%nat ->
  Znth (Z.of_nat k) (DPA m n (Z.of_nat i)) 0 = count_rated k mod m.
Proof.
  intros m n i k Hm Hn Hi Hk1 Hk2.
  destruct (DP_inv m n Hm Hn i Hi) as [_ [_ [HA _]]].
  unfold DPA. rewrite Nat2Z.id. apply HA; assumption.
Qed.

Corollary DPQ_correct : forall m n i D, 0 < m -> 0 <= n -> Z.of_nat i <= n ->
  (D <= i)%nat ->
  Znth (Z.of_nat D) (DPQ m n (Z.of_nat i)) 0 = cntQ D mod m.
Proof.
  intros m n i D Hm Hn Hi HD.
  destruct (DP_inv m n Hm Hn i Hi) as [_ [_ [_ HQI]]].
  unfold DPQ. rewrite Nat2Z.id.
  apply (QINV_QOK m n _ i Hn Hi HQI). exact HD.
Qed.

(* ================= block I : the final theorem =========================== *)

Lemma DPA_value : forall m n, 0 < m -> 0 < n ->
  Znth n (DPA m n n) 0 = count_rated (Z.to_nat n) mod m.
Proof.
  intros m n Hm Hn.
  destruct (DP_inv m n Hm ltac:(lia) (Z.to_nat n) ltac:(lia)) as [_ [_ [HA _]]].
  unfold DPA.
  rewrite <- (Z2Nat.id n) at 1 by lia.
  apply (HA (Z.to_nat n) ltac:(lia) ltac:(lia)).
Qed.

Theorem DPA_spec : forall m n, 0 < m -> 0 < n -> Spec n m (Znth n (DPA m n n) 0).
Proof.
  intros m n Hm Hn.
  rewrite (DPA_value m n Hm Hn).
  apply (proj2 (spec_iff_count_Z n m _ ltac:(lia) Hm)). reflexivity.
Qed.

(* The hypothesis [0 < n] is NECESSARY: at n = 0 the DP arrays are still all
   zero while the empty string is (vacuously) Rated, so Spec demands 1 mod m. *)
Remark DPA_spec_fails_at_zero : forall m, 1 < m -> ~ Spec 0 m (Znth 0 (DPA m 0 0) 0).
Proof.
  intros m Hm Hc.
  apply (proj1 (spec_iff_count_Z 0 m _ ltac:(lia) ltac:(lia))) in Hc.
  cbn [Z.to_nat] in Hc.
  replace (count_rated 0) with 1 in Hc by reflexivity.
  replace (Znth 0 (DPA m 0 0) 0) with 0 in Hc by reflexivity.
  rewrite Z.mod_1_l in Hc by lia. discriminate.
Qed.

Require Import Coq.ZArith.Zquot.
Lemma Zeros_basic__init_fill :
  forall k : Z, 0 <= k ->
    Zlength (Zeros k) = k /\
    Zeros 0 = (@nil Z) /\
    Zeros k ++ (0 :: nil) = Zeros (k + 1).
Proof.
  assert (Hlen : forall n : nat, Zlength (repeat (0:Z) n) = Z.of_nat n).
  { induction n as [|n IH].
    - change (repeat (0:Z) 0%nat) with (@nil Z).
      rewrite Zlength_nil. reflexivity.
    - change (repeat (0:Z) (S n)) with (0 :: repeat (0:Z) n).
      rewrite Zlength_cons, IH. lia. }
  assert (Hsnoc : forall n : nat, repeat (0:Z) n ++ (0 :: nil) = repeat (0:Z) (S n)).
  { induction n as [|n IH].
    - reflexivity.
    - change (repeat (0:Z) (S n)) with (0 :: repeat (0:Z) n).
      change ((0 :: repeat (0:Z) n) ++ (0 :: nil)) with (0 :: (repeat (0:Z) n ++ (0 :: nil))).
      rewrite IH. reflexivity. }
  intros k Hk.
  split; [| split].
  - unfold Zeros. rewrite Hlen. rewrite Z2Nat.id by lia. reflexivity.
  - unfold Zeros. reflexivity.
  - unfold Zeros. rewrite Hsnoc. f_equal.
    rewrite Z.add_1_r, Z2Nat.inj_succ by lia. reflexivity.
Qed.
Lemma Zlength_Zeros__init_fill : forall k : Z, 0 <= k -> Zlength (Zeros k) = k.
Proof.
  intros k Hk. exact (proj1 (Zeros_basic__init_fill k Hk)).
Qed.
Lemma Zeros_snoc__init_fill :
  forall k : Z, 0 <= k -> Zeros k ++ (0 :: nil) = Zeros (k + 1).
Proof.
  intros k Hk. exact (proj2 (proj2 (Zeros_basic__init_fill k Hk))).
Qed.
Lemma DP_init_state__pow2_table : forall m n : Z,
  DPA m n 0 = Zeros (n + 2) /\ DPQ m n 0 = Zeros (2 * n + 4).
Proof.
  intros m n.
  unfold DPA, DPQ.
  simpl.
  split; reflexivity.
Qed.
Lemma quot_div_nonneg_bridge__inner_j_entail :
  forall d j : Z, 0 < d + j + 2 -> (d + j + 2) ÷ 2 = (d + j + 2) / 2.
Proof.
  intros d j H.
  apply Z.quot_div_nonneg; lia.
Qed.
Lemma Pow2Mod_bound__w_value_safety :
  forall (k m : Z), 0 < m -> 0 <= Pow2Mod k m < m.
Proof.
  intros k m Hm.
  unfold Pow2Mod.
  apply Z.mod_pos_bound.
  exact Hm.
Qed.
Lemma Forall_nth_default__w_value_safety :
  forall {A : Type} (P : A -> Prop) (l : list A) (k : nat) (d : A),
    Forall P l -> P d -> P (nth k l d).
Proof.
  intros A P l.
  induction l as [| x l IH]; intros k d HF Hd.
  - destruct k as [| k']; simpl; exact Hd.
  - destruct k as [| k']; simpl.
    + exact (Forall_inv HF).
    + apply IH.
      * exact (Forall_inv_tail HF).
      * exact Hd.
Qed.
Lemma Forall_replace_nth__w_value_safety :
  forall {A : Type} (P : A -> Prop) (l : list A) (k : nat) (a : A),
    Forall P l -> P a -> Forall P (replace_nth k l a).
Proof.
  intros A P l.
  induction l as [| x l IH]; intros k a HF Ha.
  - simpl. constructor.
  - destruct k as [| k']; simpl.
    + constructor.
      * exact Ha.
      * exact (Forall_inv_tail HF).
    + constructor.
      * exact (Forall_inv HF).
      * apply IH.
        -- exact (Forall_inv_tail HF).
        -- exact Ha.
Qed.
Lemma Forall_Zeros__w_value_safety :
  forall (P : Z -> Prop) (k : Z), P 0 -> Forall P (Zeros k).
Proof.
  intros P k H.
  unfold Zeros.
  apply Forall_forall.
  intros x Hin.
  apply repeat_spec in Hin.
  subst x.
  exact H.
Qed.
Lemma QAfterNat_bound__w_value_safety :
  forall (m : Z), 0 < m ->
  forall (k : nat) (lQ lA : list Z) (i n : Z),
    Forall (fun x => 0 <= x < m) lQ ->
    Forall (fun x => 0 <= x < m) (QAfterNat lQ lA i m n k).
Proof.
  intros m Hm k.
  induction k as [| k IH]; intros lQ lA i n HF.
  - cbn [QAfterNat]. exact HF.
  - cbn [QAfterNat].
    destruct (Z.leb (i + Z.of_nat k) (2 * n)) eqn:E.
    + unfold replace_Znth.
      apply Forall_replace_nth__w_value_safety.
      * apply IH. exact HF.
      * apply Z.mod_pos_bound. exact Hm.
    + apply IH. exact HF.
Qed.
Lemma DPNat_snd_bound__w_value_safety :
  forall (m n : Z), 0 < m ->
  forall (k : nat), Forall (fun x => 0 <= x < m) (snd (DPNat m n k)).
Proof.
  intros m n Hm k.
  induction k as [| k IH].
  - cbn [DPNat snd].
    apply Forall_Zeros__w_value_safety.
    split; [ apply Z.le_refl | exact Hm ].
  - cbn [DPNat snd].
    apply QAfterNat_bound__w_value_safety.
    + exact Hm.
    + exact IH.
Qed.
Lemma DPQ_entry_bound__w_value_safety :
  forall (m n k d : Z), 0 < m -> 0 <= Znth d (DPQ m n k) 0 < m.
Proof.
  intros m n k d Hm.
  unfold DPQ, Znth.
  apply Forall_nth_default__w_value_safety.
  - apply DPNat_snd_bound__w_value_safety. exact Hm.
  - split; [ apply Z.le_refl | exact Hm ].
Qed.
Lemma DPNat_fst_bound__brow_product_safety :
  forall (m n : Z), 0 < m ->
  forall (k : nat), Forall (fun x => 0 <= x < m) (fst (DPNat m n k)).
Proof.
  intros m n Hm k.
  induction k as [| k IH].
  - cbn [DPNat fst].
    apply Forall_Zeros__w_value_safety.
    split; [ apply Z.le_refl | exact Hm ].
  - cbn [DPNat fst].
    unfold replace_Znth.
    apply Forall_replace_nth__w_value_safety.
    + exact IH.
    + unfold ARowVal. apply Z.mod_pos_bound. exact Hm.
Qed.
Lemma DPA_entry_bound__brow_product_safety :
  forall (m n k d : Z), 0 < m -> 0 <= Znth d (DPA m n k) 0 < m.
Proof.
  intros m n k d Hm.
  unfold DPA, Znth.
  apply Forall_nth_default__w_value_safety.
  - apply DPNat_fst_bound__brow_product_safety. exact Hm.
  - split; [ apply Z.le_refl | exact Hm ].
Qed.
Lemma rem_abs_bound__brow_product_safety :
  forall (x m : Z), 0 < m -> - m < Z.rem x m < m.
Proof.
  intros x m Hm.
  pose proof (Z.rem_bound_abs x m ltac:(lia)) as H.
  rewrite (Z.abs_eq m) in H by lia.
  apply Z.abs_lt in H.
  exact H.
Qed.
Lemma mul_mod_fits_int64__brow_product_safety :
  forall (a b m : Z),
    0 <= a < m -> - m < b < m -> 0 < m <= 1000000000 ->
    -9223372036854775808 <= a * b <= 9223372036854775807.
Proof.
  intros a b m [Ha0 Ham] [Hb1 Hb2] [Hm0 Hm1].
  assert (H1 : a * b <= a * m) by nia.
  assert (H2 : - (a * m) <= a * b) by nia.
  assert (H3 : a * m <= 1000000000 * m) by nia.
  nia.
Qed.
Lemma nth_replace_nth_same__blocked_acc_safety :
  forall (l : list Z) (p : nat) (v : Z),
    (p < Datatypes.length l)%nat -> nth p (replace_nth p l v) 0 = v.
Proof.
  induction l as [| x l IH]; intros p v Hp.
  - simpl in Hp. exfalso. lia.
  - destruct p as [| p]; simpl.
    + reflexivity.
    + apply IH. simpl in Hp. lia.
Qed.
Lemma Znth_replace_Znth_same__blocked_acc_safety :
  forall (l : list Z) (k v : Z),
    0 <= k < Zlength l -> Znth k (replace_Znth k v l) 0 = v.
Proof.
  intros l k v Hk.
  unfold Znth, replace_Znth.
  apply nth_replace_nth_same__blocked_acc_safety.
  destruct Hk as [Hk0 Hk1].
  rewrite Zlength_correct in Hk1.
  lia.
Qed.
Lemma mod_bound__blocked_acc_safety :
  forall a m : Z, 0 < m -> - m < Z.rem a m < m.
Proof.
  intros a m Hm.
  pose proof (Z.rem_bound_abs a m ltac:(lia)) as H.
  rewrite (Z.abs_eq m ltac:(lia)) in H.
  apply Z.abs_lt in H.
  exact H.
Qed.
Lemma blocked_add_row_max__blocked_acc_safety :
  forall (l : list Z) (k v b m : Z),
    0 < m -> m <= 1000000000 -> 0 <= b < m -> 0 <= k < Zlength l ->
    b + Znth k (replace_Znth k (Z.rem v m) l) 0 <= 9223372036854775807.
Proof.
  intros l k v b m Hm0 Hm1 Hb Hk.
  rewrite (Znth_replace_Znth_same__blocked_acc_safety l k (Z.rem v m) Hk).
  pose proof (mod_bound__blocked_acc_safety v m Hm0).
  lia.
Qed.
Lemma blocked_add_row_min__blocked_acc_safety :
  forall (l : list Z) (k v b m : Z),
    0 < m -> m <= 1000000000 -> 0 <= b < m -> 0 <= k < Zlength l ->
    -9223372036854775808 <= b + Znth k (replace_Znth k (Z.rem v m) l) 0.
Proof.
  intros l k v b m Hm0 Hm1 Hb Hk.
  rewrite (Znth_replace_Znth_same__blocked_acc_safety l k (Z.rem v m) Hk).
  pose proof (mod_bound__blocked_acc_safety v m Hm0).
  lia.
Qed.
Lemma quot_div_nonneg__inner_j_entail :
  forall a b : Z, 0 <= a -> 0 < b -> a ÷ b = a / b.
Proof. intros a b Ha Hb. apply Z.quot_div_nonneg; lia. Qed.
Lemma rem_mod_nonneg__inner_j_entail :
  forall a b : Z, 0 <= a -> 0 < b -> Z.rem a b = a mod b.
Proof. intros a b Ha Hb. apply Zrem_Zmod_pos; lia. Qed.
Lemma mod_nonneg__inner_j_entail :
  forall a b : Z, 0 < b -> 0 <= a mod b.
Proof. intros a b Hb. pose proof (Z.mod_pos_bound a b Hb). lia. Qed.
Lemma rem_nonneg__inner_j_entail :
  forall a b : Z, 0 <= a -> 0 < b -> 0 <= Z.rem a b.
Proof. intros a b Ha Hb. pose proof (Zrem_lt_pos_pos a b Ha Hb). lia. Qed.
Lemma rem_lt__inner_j_entail :
  forall a b : Z, 0 < b -> Z.rem a b < b.
Proof.
  intros a b Hb. destruct (Z_le_gt_dec 0 a) as [H | H].
  - pose proof (Zrem_lt_pos_pos a b H Hb). lia.
  - pose proof (Zrem_lt_neg_pos a b ltac:(lia) Hb). lia.
Qed.
Lemma geb_true__inner_j_entail : forall a b : Z, b <= a -> (a >=? b) = true.
Proof.
  intros a b H. rewrite Z.geb_leb. exact (proj2 (Z.leb_le b a) H).
Qed.
Lemma geb_false__inner_j_entail : forall a b : Z, a < b -> (a >=? b) = false.
Proof.
  intros a b H. rewrite Z.geb_leb. exact (proj2 (Z.leb_gt b a) H).
Qed.
Lemma Pow2Mod_nonneg__inner_j_entail :
  forall k m : Z, 0 < m -> 0 <= Pow2Mod k m.
Proof. intros k m Hm. unfold Pow2Mod. apply mod_nonneg__inner_j_entail. exact Hm. Qed.
Lemma replace_nth_length__inner_j_entail :
  forall {A : Type} (l : list A) (k : nat) (a : A),
    Datatypes.length (replace_nth k l a) = Datatypes.length l.
Proof.
  intros A l. induction l as [| x l IH]; intros k a.
  - destruct k; reflexivity.
  - destruct k as [| k].
    + reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.
Lemma Zlength_replace_Znth__inner_j_entail :
  forall {A : Type} (l : list A) (k : Z) (v : A),
    Zlength (replace_Znth k v l) = Zlength l.
Proof.
  intros A l k v. unfold replace_Znth.
  rewrite Zlength_correct, Zlength_correct.
  rewrite replace_nth_length__inner_j_entail. reflexivity.
Qed.
Lemma Forall_nth_default__inner_j_entail :
  forall {A : Type} (P : A -> Prop) (l : list A) (k : nat) (d : A),
    Forall P l -> P d -> P (nth k l d).
Proof.
  intros A P l. induction l as [| x l IH]; intros k d HF Hd.
  - destruct k as [| k']; simpl; exact Hd.
  - destruct k as [| k']; simpl.
    + exact (Forall_inv HF).
    + apply IH; [exact (Forall_inv_tail HF) | exact Hd].
Qed.
Lemma Forall_replace_nth__inner_j_entail :
  forall {A : Type} (P : A -> Prop) (l : list A) (k : nat) (a : A),
    Forall P l -> P a -> Forall P (replace_nth k l a).
Proof.
  intros A P l. induction l as [| x l IH]; intros k a HF Ha.
  - simpl. constructor.
  - destruct k as [| k']; simpl.
    + constructor; [exact Ha | exact (Forall_inv_tail HF)].
    + constructor;
      [exact (Forall_inv HF) | apply IH; [exact (Forall_inv_tail HF) | exact Ha]].
Qed.
Lemma Forall_Zeros__inner_j_entail :
  forall (P : Z -> Prop) (k : Z), P 0 -> Forall P (Zeros k).
Proof.
  intros P k H. unfold Zeros. apply Forall_forall.
  intros x Hin. apply repeat_spec in Hin. subst x. exact H.
Qed.
Lemma QAfterNat_bound__inner_j_entail :
  forall (m : Z), 0 < m ->
  forall (k : nat) (lQ lA : list Z) (i n : Z),
    Forall (fun x => 0 <= x < m) lQ ->
    Forall (fun x => 0 <= x < m) (QAfterNat lQ lA i m n k).
Proof.
  intros m Hm k. induction k as [| k IH]; intros lQ lA i n HF.
  - cbn [QAfterNat]. exact HF.
  - cbn [QAfterNat].
    destruct (Z.leb (i + Z.of_nat k) (2 * n)) eqn:E.
    + unfold replace_Znth. apply Forall_replace_nth__inner_j_entail.
      * apply IH. exact HF.
      * apply Z.mod_pos_bound. exact Hm.
    + apply IH. exact HF.
Qed.
Lemma DPNat_bound__inner_j_entail :
  forall (m n : Z), 0 < m ->
  forall (k : nat),
    Forall (fun x => 0 <= x < m) (fst (DPNat m n k)) /\
    Forall (fun x => 0 <= x < m) (snd (DPNat m n k)).
Proof.
  intros m n Hm k. induction k as [| k IH].
  - cbn [DPNat fst snd]. split; apply Forall_Zeros__inner_j_entail; lia.
  - destruct IH as [IHA IHQ]. cbn [DPNat fst snd]. split.
    + unfold replace_Znth. apply Forall_replace_nth__inner_j_entail.
      * exact IHA.
      * unfold ARowVal. apply Z.mod_pos_bound. exact Hm.
    + apply QAfterNat_bound__inner_j_entail; [exact Hm | exact IHQ].
Qed.
Lemma DPA_entry_bound__inner_j_entail :
  forall (m n k d : Z), 0 < m -> 0 <= Znth d (DPA m n k) 0 < m.
Proof.
  intros m n k d Hm. unfold DPA, Znth.
  apply Forall_nth_default__inner_j_entail.
  - apply (DPNat_bound__inner_j_entail m n Hm (Z.to_nat k)).
  - lia.
Qed.
Lemma DPQ_entry_bound__inner_j_entail :
  forall (m n k d : Z), 0 < m -> 0 <= Znth d (DPQ m n k) 0 < m.
Proof.
  intros m n k d Hm. unfold DPQ, Znth.
  apply Forall_nth_default__inner_j_entail.
  - apply (DPNat_bound__inner_j_entail m n Hm (Z.to_nat k)).
  - lia.
Qed.
Lemma Blocked_step__inner_j_entail :
  forall (lA lQ : list Z) (i m c : Z),
    1 <= c ->
    Blocked lA lQ i m c = (Blocked lA lQ i m (c - 1) + BrowEntry lA lQ i c m) mod m.
Proof.
  intros lA lQ i m c Hc. unfold Blocked.
  replace (Z.to_nat c) with (S (Z.to_nat (c - 1))) by lia.
  cbn [BlockedNat].
  replace (Z.of_nat (S (Z.to_nat (c - 1)))) with c by lia.
  reflexivity.
Qed.
Lemma RowBlocked_step__inner_j_entail :
  forall (m n i c : Z),
    1 <= c ->
    RowBlocked m n i c = (RowBlocked m n i (c - 1) + RowBrow m n i c) mod m.
Proof.
  intros m n i c Hc. unfold RowBlocked, RowBrow.
  apply Blocked_step__inner_j_entail. exact Hc.
Qed.
Lemma RowBrow_nonneg__inner_j_entail :
  forall (m n i j : Z), 0 < m -> 0 <= RowBrow m n i j.
Proof.
  intros m n i j Hm. unfold RowBrow, BrowEntry.
  apply mod_nonneg__inner_j_entail. exact Hm.
Qed.
Lemma BrowEntry_bridge__inner_j_entail :
  forall (lA lQ : list Z) (i j m w : Z),
    0 < m -> 0 <= Znth j lA 0 -> 0 <= w ->
    w mod m = Wfun lQ (i - j) j m ->
    Z.rem (Znth j lA 0 * Z.rem w m) m = BrowEntry lA lQ i j m.
Proof.
  intros lA lQ i j m w Hm Ha Hw HW.
  unfold BrowEntry. rewrite <- HW.
  rewrite (rem_mod_nonneg__inner_j_entail w m Hw Hm).
  apply rem_mod_nonneg__inner_j_entail; [| exact Hm].
  apply Z.mul_nonneg_nonneg; [exact Ha | apply mod_nonneg__inner_j_entail; exact Hm].
Qed.
Lemma blocked_step_eq__inner_j_entail :
  forall (m n i j blocked w : Z) (lA lQ lBrow : list Z),
    0 < m -> 1 <= j -> 0 <= j < Zlength lBrow ->
    0 <= blocked -> blocked = RowBlocked m n i (j - 1) ->
    lA = DPA m n (i - 1) -> lQ = DPQ m n (i - 1) ->
    0 <= w -> w mod m = Wfun lQ (i - j) j m ->
    Z.rem (blocked + Znth j (replace_Znth j (Z.rem (Znth j lA 0 * Z.rem w m) m) lBrow) 0) m
    = RowBlocked m n i (j + 1 - 1).
Proof.
  intros m n i j blocked w lA lQ lBrow Hm Hj Hjb Hb0 Hb HlA HlQ Hw0 HW.
  assert (Ha : 0 <= Znth j lA 0).
  { rewrite HlA. pose proof (DPA_entry_bound__inner_j_entail m n (i - 1) j Hm). lia. }
  assert (Hv : Z.rem (Znth j lA 0 * Z.rem w m) m = RowBrow m n i j).
  { unfold RowBrow. rewrite <- HlA, <- HlQ.
    apply BrowEntry_bridge__inner_j_entail; assumption. }
  rewrite (Znth_replace_Znth_Same 0 lBrow j _ Hjb).
  rewrite Hv.
  replace (j + 1 - 1) with j by lia.
  rewrite (RowBlocked_step__inner_j_entail m n i j Hj).
  rewrite <- Hb.
  pose proof (RowBrow_nonneg__inner_j_entail m n i j Hm).
  apply rem_mod_nonneg__inner_j_entail; [lia | exact Hm].
Qed.
Lemma blocked_step_nonneg__inner_j_entail :
  forall (m j blocked w : Z) (lA lBrow : list Z),
    0 < m -> 0 <= j < Zlength lBrow -> 0 <= blocked ->
    0 <= Znth j lA 0 -> 0 <= w ->
    0 <= Z.rem (blocked + Znth j (replace_Znth j (Z.rem (Znth j lA 0 * Z.rem w m) m) lBrow) 0) m.
Proof.
  intros m j blocked w lA lBrow Hm Hjb Hb Ha Hw.
  rewrite (Znth_replace_Znth_Same 0 lBrow j _ Hjb).
  apply rem_nonneg__inner_j_entail; [| exact Hm].
  assert (0 <= Z.rem (Znth j lA 0 * Z.rem w m) m).
  { apply rem_nonneg__inner_j_entail; [| exact Hm].
    apply Z.mul_nonneg_nonneg;
      [exact Ha | apply rem_nonneg__inner_j_entail; [exact Hw | exact Hm]]. }
  lia.
Qed.

(* --- the four Wfun branch identities --- *)
Lemma Wfun_case1__inner_j_entail :
  forall (lQ lpow2 : list Z) (m n i j : Z),
    0 < m -> 0 < i - j + j + 2 ->
    (forall k : Z, 0 <= k < n + 1 -> Znth k lpow2 0 = Pow2Mod k m) ->
    0 <= i - j - (i - j + j + 2) ÷ 2 ->
    i - j - (i - j + j + 2) ÷ 2 < n + 1 ->
    1 <= i - j - (i - j + j + 2) ÷ 2 ->
    0 <= i - j - j - 1 ->
    (Z.rem (Z.rem 1 m + Znth (i - j - (i - j + j + 2) ÷ 2) lpow2 0 - Z.rem 1 m + m) m
       + Znth (i - j - j - 1) lQ 0) mod m = Wfun lQ (i - j) j m.
Proof.
  intros lQ lpow2 m n i j Hm Hpos Hpow HL0 HLn HL1 HD.
  assert (Hq : (i - j + j + 2) ÷ 2 = (i - j + j + 2) / 2)
    by (apply quot_div_nonneg__inner_j_entail; lia).
  rewrite Hq in HL0, HLn, HL1 |- *.
  rewrite (Hpow (i - j - (i - j + j + 2) / 2) ltac:(lia)).
  assert (Hone : Z.rem 1 m = 1 mod m)
    by (apply rem_mod_nonneg__inner_j_entail; lia).
  rewrite Hone.
  pose proof (Pow2Mod_nonneg__inner_j_entail (i - j - (i - j + j + 2) / 2) m Hm).
  pose proof (mod_nonneg__inner_j_entail 1 m Hm).
  rewrite (rem_mod_nonneg__inner_j_entail
             (1 mod m + Pow2Mod (i - j - (i - j + j + 2) / 2) m - 1 mod m + m) m
             ltac:(lia) Hm).
  unfold Wfun. cbv zeta.
  rewrite (geb_true__inner_j_entail (i - j - (i - j + j + 2) / 2) 1 HL1).
  rewrite (geb_true__inner_j_entail (i - j - j - 1) 0 HD).
  reflexivity.
Qed.
Lemma Wfun_case2__inner_j_entail :
  forall (lQ : list Z) (m i j : Z),
    0 < m -> 0 < i - j + j + 2 ->
    i - j - (i - j + j + 2) ÷ 2 < 1 ->
    0 <= i - j - j - 1 ->
    (Z.rem 1 m + Znth (i - j - j - 1) lQ 0) mod m = Wfun lQ (i - j) j m.
Proof.
  intros lQ m i j Hm Hpos HL1 HD.
  assert (Hq : (i - j + j + 2) ÷ 2 = (i - j + j + 2) / 2)
    by (apply quot_div_nonneg__inner_j_entail; lia).
  rewrite Hq in HL1.
  assert (Hone : Z.rem 1 m = 1 mod m)
    by (apply rem_mod_nonneg__inner_j_entail; lia).
  rewrite Hone.
  unfold Wfun. cbv zeta.
  rewrite (geb_false__inner_j_entail (i - j - (i - j + j + 2) / 2) 1 HL1).
  rewrite (geb_true__inner_j_entail (i - j - j - 1) 0 HD).
  reflexivity.
Qed.
Lemma Wfun_case3__inner_j_entail :
  forall (lQ lpow2 : list Z) (m n i j : Z),
    0 < m -> 0 < i - j + j + 2 ->
    (forall k : Z, 0 <= k < n + 1 -> Znth k lpow2 0 = Pow2Mod k m) ->
    0 <= i - j - (i - j + j + 2) ÷ 2 ->
    i - j - (i - j + j + 2) ÷ 2 < n + 1 ->
    1 <= i - j - (i - j + j + 2) ÷ 2 ->
    i - j - j - 1 < 0 ->
    (Z.rem 1 m + Znth (i - j - (i - j + j + 2) ÷ 2) lpow2 0 - Z.rem 1 m + m) mod m
    = Wfun lQ (i - j) j m.
Proof.
  intros lQ lpow2 m n i j Hm Hpos Hpow HL0 HLn HL1 HD.
  assert (Hq : (i - j + j + 2) ÷ 2 = (i - j + j + 2) / 2)
    by (apply quot_div_nonneg__inner_j_entail; lia).
  rewrite Hq in HL0, HLn, HL1 |- *.
  rewrite (Hpow (i - j - (i - j + j + 2) / 2) ltac:(lia)).
  assert (Hone : Z.rem 1 m = 1 mod m)
    by (apply rem_mod_nonneg__inner_j_entail; lia).
  rewrite Hone.
  unfold Wfun. cbv zeta.
  rewrite (geb_true__inner_j_entail (i - j - (i - j + j + 2) / 2) 1 HL1).
  rewrite (geb_false__inner_j_entail (i - j - j - 1) 0 HD).
  reflexivity.
Qed.
Lemma Wfun_case4__inner_j_entail :
  forall (lQ : list Z) (m i j : Z),
    0 < m -> 0 < i - j + j + 2 ->
    i - j - (i - j + j + 2) ÷ 2 < 1 ->
    i - j - j - 1 < 0 ->
    1 mod m = Wfun lQ (i - j) j m.
Proof.
  intros lQ m i j Hm Hpos HL1 HD.
  assert (Hq : (i - j + j + 2) ÷ 2 = (i - j + j + 2) / 2)
    by (apply quot_div_nonneg__inner_j_entail; lia).
  rewrite Hq in HL1.
  unfold Wfun. cbv zeta.
  rewrite (geb_false__inner_j_entail (i - j - (i - j + j + 2) / 2) 1 HL1).
  rewrite (geb_false__inner_j_entail (i - j - j - 1) 0 HD).
  reflexivity.
Qed.
Lemma replace_nth_length__row_value : forall {A : Type} (l : list A) (k : nat) (a : A),
  Datatypes.length (replace_nth k l a) = Datatypes.length l.
Proof.
  intros A l.
  induction l as [| x l IH]; intros k a.
  - destruct k; reflexivity.
  - destruct k as [| k].
    + reflexivity.
    + simpl. rewrite IH. reflexivity.
Qed.
Lemma Zlength_replace_Znth__row_value : forall {A : Type} (l : list A) (k : Z) (v : A),
  Zlength (replace_Znth k v l) = Zlength l.
Proof.
  intros A l k v.
  unfold replace_Znth.
  rewrite Zlength_correct, Zlength_correct.
  rewrite replace_nth_length__row_value.
  reflexivity.
Qed.
Lemma DPA_length__row_value : forall m n i : Z,
  0 <= n -> Zlength (DPA m n i) = n + 2.
Proof.
  intros m n i Hn.
  unfold DPA.
  assert (H : forall k : nat, Zlength (fst (DPNat m n k)) = n + 2).
  { induction k as [| k IH].
    - simpl. unfold Zeros.
      rewrite Zlength_correct, repeat_length, Z2Nat.id by lia. reflexivity.
    - simpl. rewrite Zlength_replace_Znth__row_value. exact IH. }
  apply H.
Qed.
Lemma rem_bounds__row_value : forall a m : Z, 0 < m -> - m < Z.rem a m < m.
Proof.
  intros a m Hm.
  pose proof (Z.rem_bound_abs a m ltac:(lia)) as H.
  rewrite (Z.abs_eq m ltac:(lia)) in H.
  apply Z.abs_lt in H.
  lia.
Qed.
Lemma rem_small__row_value : forall a m : Z, 0 < m -> - m < a < m -> Z.rem a m = a.
Proof.
  intros a m Hm Ha.
  apply (proj2 (Z.rem_small_iff a m ltac:(lia))).
  rewrite (Z.abs_eq m ltac:(lia)).
  apply Z.abs_lt. lia.
Qed.
Lemma rem_mod_shift__row_value : forall a m : Z,
  0 < m -> - m < a < m ->
  Z.rem (Z.rem a m + m) m = ((a mod m) + m) mod m.
Proof.
  intros a m Hm Ha.
  rewrite (rem_small__row_value a m Hm Ha).
  rewrite Zrem_Zmod_pos by lia.
  rewrite Z.add_mod_idemp_l by lia.
  reflexivity.
Qed.
Lemma DPA_step_nat__row_value : forall (m n : Z) (k : nat),
  fst (DPNat m n (S k)) =
  replace_Znth (Z.of_nat (S k))
    (ARowVal (fst (DPNat m n k)) (snd (DPNat m n k)) (Z.of_nat (S k)) m)
    (fst (DPNat m n k)).
Proof. intros. reflexivity. Qed.
Lemma DPA_step__row_value : forall m n i : Z,
  1 <= i ->
  DPA m n i =
  replace_Znth i (ARowVal (DPA m n (i - 1)) (DPQ m n (i - 1)) i m) (DPA m n (i - 1)).
Proof.
  intros m n i Hi.
  unfold DPA, DPQ.
  assert (H1 : Z.to_nat i = S (Z.to_nat (i - 1))) by lia.
  assert (H2 : Z.of_nat (S (Z.to_nat (i - 1))) = i) by lia.
  rewrite H1.
  rewrite (DPA_step_nat__row_value m n (Z.to_nat (i - 1))).
  rewrite H2.
  reflexivity.
Qed.
Lemma Forall_replace_nth__q_update :
  forall (P : Z -> Prop) (l : list Z) (k : nat) (v : Z),
    Forall P l -> P v -> Forall P (replace_nth k l v).
Proof.
  intros P l.
  induction l as [|x l IH]; intros k v Hl Hv.
  - destruct k; simpl; constructor.
  - destruct k; simpl.
    + constructor; [exact Hv | exact (Forall_inv_tail Hl)].
    + constructor;
      [exact (Forall_inv Hl)
      | apply IH; [exact (Forall_inv_tail Hl) | exact Hv]].
Qed.
Lemma Forall_replace_Znth__q_update :
  forall (P : Z -> Prop) (l : list Z) (k v : Z),
    Forall P l -> P v -> Forall P (replace_Znth k v l).
Proof.
  intros P l k v Hl Hv.
  unfold replace_Znth.
  apply Forall_replace_nth__q_update; assumption.
Qed.
Lemma DPNat_fst_bound__prefix_sum_safety :
  forall (m n : Z), 0 < m ->
  forall (k : nat), Forall (fun x => 0 <= x < m) (fst (DPNat m n k)).
Proof.
  intros m n Hm k.
  induction k as [| k IH].
  - cbn [DPNat fst].
    apply Forall_Zeros__w_value_safety.
    split; [ apply Z.le_refl | exact Hm ].
  - cbn [DPNat fst snd].
    apply Forall_replace_Znth__q_update.
    + exact IH.
    + unfold ARowVal.
      apply Z.mod_pos_bound. exact Hm.
Qed.
Lemma DPA_entry_bound__prefix_sum_safety :
  forall (m n i k : Z), 0 < m -> 0 <= Znth k (DPA m n i) 0 < m.
Proof.
  intros m n i k Hm.
  unfold DPA, Znth.
  apply Forall_nth_default__w_value_safety.
  - apply DPNat_fst_bound__prefix_sum_safety. exact Hm.
  - split; [ apply Z.le_refl | exact Hm ].
Qed.
Lemma RowBrow_bound__prefix_sum_safety :
  forall (m n i j : Z), 0 < m -> 0 <= RowBrow m n i j < m.
Proof.
  intros m n i j Hm.
  unfold RowBrow, BrowEntry.
  apply Z.mod_pos_bound. exact Hm.
Qed.
Lemma RunUpto_step__prefix_sum_entail :
  forall (lA lQ : list Z) (i m q : Z),
    0 <= q ->
    RunUpto lA lQ i m (q + 1) =
    (RunUpto lA lQ i m q + RowC lA lQ i m q) mod m.
Proof.
  intros lA lQ i m q Hq.
  unfold RunUpto.
  replace (Z.to_nat (q + 1)) with (S (Z.to_nat q)) by lia.
  change (RunNat lA lQ i m (S (Z.to_nat q)))
    with ((RunNat lA lQ i m (Z.to_nat q)
           + RowC lA lQ i m (Z.of_nat (Z.to_nat q))) mod m).
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma RowRun_step__prefix_sum_entail :
  forall (m n i q : Z),
    0 <= q ->
    RowRun m n i (q + 1) =
    (RowRun m n i q + RowC (DPA m n (i - 1)) (DPQ m n (i - 1)) i m q) mod m.
Proof.
  intros m n i q Hq.
  unfold RowRun.
  apply RunUpto_step__prefix_sum_entail. exact Hq.
Qed.
Lemma RowRun_zero__prefix_sum_entail :
  forall (m n i : Z), RowRun m n i 0 = 0.
Proof. intros m n i. reflexivity. Qed.
Lemma Zrem_mod_nonneg__prefix_sum_entail :
  forall a b : Z, 0 <= a -> 0 < b -> Z.rem a b = a mod b.
Proof. intros a b Ha Hb. apply Zrem_Zmod_pos; assumption. Qed.
Lemma Zlength_replace_Znth__prefix_sum_entail :
  forall {A : Type} (i : Z) (a : A) (l : list A),
    Zlength (replace_Znth i a l) = Zlength l.
Proof.
  intros A i a l.
  rewrite !Zlength_correct, replace_Znth_length.
  reflexivity.
Qed.
Lemma RowBrow_bound__prefix_sum_entail :
  forall (m n i j : Z), 0 < m -> 0 <= RowBrow m n i j < m.
Proof.
  intros m n i j Hm.
  unfold RowBrow, BrowEntry.
  apply Z.mod_pos_bound. exact Hm.
Qed.
Lemma ARowVal_bound__prefix_sum_entail :
  forall (lA lQ : list Z) (i m : Z), 0 < m -> 0 <= ARowVal lA lQ i m < m.
Proof.
  intros lA lQ i m Hm.
  unfold ARowVal.
  apply Z.mod_pos_bound. exact Hm.
Qed.
Lemma DPA_step_Znth__prefix_sum_entail :
  forall (m n i : Z), 0 < m -> 1 <= i -> i <= n ->
    Znth i (DPA m n i) 0 = ARowVal (DPA m n (i - 1)) (DPQ m n (i - 1)) i m.
Proof.
  intros m n i Hm Hi Hin.
  destruct (DP_inv m n Hm ltac:(lia) (Z.to_nat (i - 1)) ltac:(lia)) as [HA _].
  unfold DPA, DPQ.
  replace (Z.to_nat i) with (S (Z.to_nat (i - 1))) by lia.
  cbn [DPNat fst snd].
  rewrite Nat2Z.inj_succ.
  rewrite Z2Nat.id by lia.
  replace (Z.succ (i - 1)) with i by lia.
  apply Znth_replace_Znth_Same.
  rewrite HA. lia.
Qed.
Lemma QPartial_zero__prefix_sum_entail :
  forall (m n i : Z), QPartial m n i 0 = DPQ m n (i - 1).
Proof. intros m n i. reflexivity. Qed.
Lemma BrowEntry_bound__prefix_sum_entail :
  forall (lA lQ : list Z) (i j m : Z), 0 < m -> 0 <= BrowEntry lA lQ i j m < m.
Proof.
  intros lA lQ i j m Hm.
  unfold BrowEntry.
  apply Z.mod_pos_bound. exact Hm.
Qed.
Lemma Zlength_replace_nth__q_update :
  forall (l : list Z) (k : nat) (v : Z),
    Zlength (replace_nth k l v) = Zlength l.
Proof.
  intros l.
  induction l as [|x l IH]; intros k v.
  - destruct k; simpl; reflexivity.
  - destruct k; simpl.
    + reflexivity.
    + rewrite !Zlength_cons. rewrite IH. reflexivity.
Qed.
Lemma Zlength_replace_Znth__q_update :
  forall (l : list Z) (k v : Z),
    Zlength (replace_Znth k v l) = Zlength l.
Proof.
  intros l k v.
  unfold replace_Znth.
  apply Zlength_replace_nth__q_update.
Qed.
Lemma Zlength_Zeros__q_update :
  forall k : Z, 0 <= k -> Zlength (Zeros k) = k.
Proof.
  intros k Hk.
  unfold Zeros.
  rewrite Zlength_correct, repeat_length.
  lia.
Qed.
Lemma Forall_Zeros__q_update :
  forall (P : Z -> Prop) (k : Z), P 0 -> Forall P (Zeros k).
Proof.
  intros P k HP.
  unfold Zeros.
  apply Forall_forall.
  intros x Hx.
  apply repeat_spec in Hx.
  subst x.
  exact HP.
Qed.
Lemma QAfterNat_props__q_update :
  forall (m n i : Z) (lQ lA : list Z) (k : nat),
    0 < m ->
    Forall (fun x => 0 <= x < m) lQ ->
    Zlength (QAfterNat lQ lA i m n k) = Zlength lQ /\
    Forall (fun x => 0 <= x < m) (QAfterNat lQ lA i m n k).
Proof.
  intros m n i lQ lA k Hm Hf.
  induction k as [|k IH].
  - simpl. split; [reflexivity | exact Hf].
  - destruct IH as [IH1 IH2].
    cbn [QAfterNat].
    destruct (Z.leb (i + Z.of_nat k) (2 * n)).
    + split.
      * rewrite Zlength_replace_Znth__q_update. exact IH1.
      * apply Forall_replace_Znth__q_update; [exact IH2 |].
        apply Z.mod_pos_bound. exact Hm.
    + split; assumption.
Qed.
Lemma DPNat_props__q_update :
  forall (m n : Z) (k : nat),
    0 < m -> 0 <= n ->
    Zlength (fst (DPNat m n k)) = n + 2 /\
    Zlength (snd (DPNat m n k)) = 2 * n + 4 /\
    Forall (fun x => 0 <= x < m) (snd (DPNat m n k)).
Proof.
  intros m n k Hm Hn.
  induction k as [|k IH].
  - cbn [DPNat fst snd].
    split; [| split].
    + apply Zlength_Zeros__q_update. lia.
    + apply Zlength_Zeros__q_update. lia.
    + apply Forall_Zeros__q_update. lia.
  - destruct IH as [IH1 [IH2 IH3]].
    pose proof (QAfterNat_props__q_update m n (Z.of_nat (S k))
                  (snd (DPNat m n k)) (fst (DPNat m n k))
                  (Z.to_nat (Z.of_nat (S k))) Hm IH3) as [HL HF].
    cbn [DPNat fst snd].
    split; [| split].
    + rewrite Zlength_replace_Znth__q_update. exact IH1.
    + rewrite HL. exact IH2.
    + exact HF.
Qed.
Lemma DPQ_length__q_update :
  forall (m n k : Z), 0 < m -> 0 <= n -> Zlength (DPQ m n k) = 2 * n + 4.
Proof.
  intros m n k Hm Hn.
  unfold DPQ.
  pose proof (DPNat_props__q_update m n (Z.to_nat k) Hm Hn) as [H1 [H2 H3]].
  exact H2.
Qed.
Lemma DPQ_bound__q_update :
  forall (m n k : Z), 0 < m -> 0 <= n ->
    Forall (fun x => 0 <= x < m) (DPQ m n k).
Proof.
  intros m n k Hm Hn.
  unfold DPQ.
  pose proof (DPNat_props__q_update m n (Z.to_nat k) Hm Hn) as [H1 [H2 H3]].
  exact H3.
Qed.
Lemma QPartial_length_bound__q_update :
  forall (m n i t : Z), 0 < m -> 0 <= n ->
    Zlength (QPartial m n i t) = 2 * n + 4 /\
    Forall (fun x => 0 <= x < m) (QPartial m n i t).
Proof.
  intros m n i t Hm Hn.
  unfold QPartial.
  pose proof (QAfterNat_props__q_update m n i (DPQ m n (i - 1))
                (DPA m n (i - 1)) (Z.to_nat t) Hm
                (DPQ_bound__q_update m n (i - 1) Hm Hn)) as [HL HF].
  split; [| exact HF].
  rewrite HL.
  apply DPQ_length__q_update; assumption.
Qed.
Lemma QAfterNat_step__q_update :
  forall (m n i t : Z), 0 <= t ->
    QPartial m n i (t + 1) =
    (if Z.leb (i + t) (2 * n)
     then replace_Znth (i + t)
            ((Znth (i + t) (QPartial m n i t) 0
              + PEntry (DPA m n (i - 1)) (DPQ m n (i - 1)) i m t) mod m)
            (QPartial m n i t)
     else QPartial m n i t).
Proof.
  intros m n i t Ht.
  unfold QPartial.
  replace (Z.to_nat (t + 1)) with (S (Z.to_nat t)) by lia.
  cbn [QAfterNat].
  rewrite Z2Nat.id by exact Ht.
  reflexivity.
Qed.
Lemma RunNat_bound__q_update :
  forall (lA lQ : list Z) (i m : Z) (k : nat),
    0 < m -> 0 <= RunNat lA lQ i m k < m.
Proof.
  intros lA lQ i m k Hm.
  destruct k as [| k'].
  - cbn [RunNat]. lia.
  - cbn [RunNat]. apply Z.mod_pos_bound. exact Hm.
Qed.
Lemma RowP_bound__q_update :
  forall (m n i q : Z), 0 < m -> 0 <= RowP m n i q < m.
Proof.
  intros m n i q Hm.
  unfold RowP, PEntry, RunUpto.
  apply RunNat_bound__q_update. exact Hm.
Qed.
Lemma PEntry_bound__q_update :
  forall (lA lQ : list Z) (i m q : Z), 0 < m -> 0 <= PEntry lA lQ i m q < m.
Proof.
  intros lA lQ i m q Hm.
  unfold PEntry, RunUpto.
  apply RunNat_bound__q_update. exact Hm.
Qed.
Lemma QPartial_entry_bound__q_update :
  forall (m n i t D : Z), 0 < m -> 0 <= n ->
    0 <= Znth D (QPartial m n i t) 0 < m.
Proof.
  intros m n i t D Hm Hn.
  pose proof (QPartial_length_bound__q_update m n i t Hm Hn) as [_ HF].
  unfold Znth.
  apply Forall_nth_default__w_value_safety.
  - exact HF.
  - split; [apply Z.le_refl | exact Hm].
Qed.
Lemma QPartial_full__q_update :
  forall (m n i : Z), 1 <= i -> QPartial m n i i = DPQ m n i.
Proof.
  intros m n i Hi.
  unfold QPartial, DPQ, DPA.
  assert (Hi' : Z.to_nat i = S (Z.to_nat (i - 1))) by lia.
  rewrite Hi'.
  cbn [DPNat snd fst].
  rewrite Nat2Z.id.
  assert (Hof : Z.of_nat (S (Z.to_nat (i - 1))) = i) by lia.
  rewrite Hof.
  reflexivity.
Qed.
