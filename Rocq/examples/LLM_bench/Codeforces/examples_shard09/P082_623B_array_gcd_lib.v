Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.ZArith.Znumtheory.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.

Import ListNotations.
Local Open Scope Z_scope.

Definition Count (x : Z) (xs : list Z) : Z :=
  #(fun i : Z => 0 <= i < Zlength xs /\ Znth i xs 0 = x).
Definition IsPositiveGcd (d : Z) (xs : list Z) : Prop :=
  d > 0 /\ xs <> [] /\ d = fold_right Z.gcd 0 xs.

(* What is left after removing one segment: a proper part of the array may go,
   never all of it. *)
Definition KeptAfterRemoval (a : list Z) (l r : Z) (kept : list Z) : Prop :=
  0 <= l <= r /\ r <= Zlength a /\ r - l < Zlength a /\
  kept = sublist 0 l a ++ sublist r (Zlength a) a.

(* Every remaining element may move by at most one. *)
Definition Adjusted (kept delta result : list Z) : Prop :=
  Zlength delta = Zlength kept /\
  Forall (fun d => d = (- 1) \/ d = 0 \/ d = 1) delta /\
  result = map (fun q => fst q + snd q) (combine kept delta).

(* The coins paid: one price per removed element, another per element moved. *)
Definition ChangeCost (del change l r : Z) (delta : list Z) : Z :=
  (r - l) * del + Count (- 1) delta * change + Count 1 delta * change.

(* A way of reaching an array whose greatest common divisor exceeds one, and
   what it costs. *)
Definition GCDChange (a : list Z) (del change cost : Z) : Prop :=
  exists (l r : Z) (kept delta result : list Z),
    KeptAfterRemoval a l r kept /\
    Adjusted kept delta result /\
    (exists g, g > 1 /\ IsPositiveGcd g result) /\
    cost = ChangeCost del change l r delta.
Definition Pre (del change : Z) (a : list Z) : Prop :=
  (* Stated explicitly in the P082 solver Require, so dropped here:
       1 <= Zlength a <= 1000000 /\
       Forall (fun x => 2 <= x <= 1000000000) a /\
       0 <= del <= 1000000000 /\
       0 <= change <= 1000000000  *)
  True.

Definition Spec (del change : Z) (a : list Z) (out : Z) : Prop := min_value_of_subset Z.le (GCDChange a del change) (fun x => x) out.

(* ------------------------------------------------------------------ *)
(* Specification-level additions for the P082 annotation design.       *)
(* Everything above this line is kept unchanged.                       *)
(* ------------------------------------------------------------------ *)

(* The saturating "impossible" sentinel used by the C code, 1LL << 62. *)
Definition INF : Z := 4611686018427387904.

(* Minimum over a set of costs, falling back to the INF sentinel when no
   plan of the described kind exists.  This is exactly the shape the C
   program encodes with its INF guards. *)
Definition DPValue (S : Z -> Prop) (v : Z) : Prop :=
  min_value_of_subset_with_default Z.le S (fun x => x) INF v.

(* A plan that only looks at the first [i] entries of [a]: the segment
   [l, r) is removed, every surviving entry moves by at most one, and every
   surviving entry becomes divisible by [p].  [c] is what such a plan costs. *)
Definition PartialPlanCost (a : list Z) (del change p i l r c : Z) : Prop :=
  0 <= l /\ l <= r /\ r <= i /\ i <= Zlength a /\
  exists (delta result : list Z),
    Adjusted (sublist 0 l a ++ sublist r i a) delta result /\
    Forall (fun y => Z.divide p y) result /\
    c = ChangeCost del change l r delta.

(* The plans that are legal for the whole array and a fixed modulus [p]:
   the removed segment may not be the entire array. *)
Definition PFeasiblePlan (a : list Z) (del change p : Z) : Z -> Prop :=
  fun c => exists l r, r - l < Zlength a /\
             PartialPlanCost a del change p (Zlength a) l r c.

(* The cheapest such plan, or INF when [p] admits none. *)
Definition CostForPrime (a : list Z) (del change p out : Z) : Prop :=
  DPValue (PFeasiblePlan a del change p) out.

(* What one [add_factors] call appends: sound divisors, complete on primes,
   and few enough of them to stay inside the 256-cell scratch array. *)
Definition AddFactorsResult (v0 : Z) (fs : list Z) : Prop :=
  Forall (fun d => 2 <= d /\ Z.divide d v0) fs /\
  (forall q, prime q -> Z.divide q v0 -> In q fs) /\
  Zlength fs <= 30.

(* ------------------------------------------------------------------ *)
(* Internal predicates: they only describe states of the function      *)
(* bodies and never appear in a function contract.                     *)
(* ------------------------------------------------------------------ *)

(* Divisor bookkeeping shared by the three add_factors states. *)
Definition FactorsSoFar (v0 v : Z) (fs : list Z) : Prop :=
  1 <= v /\ Z.divide v v0 /\
  Forall (fun q => 2 <= q /\ Z.divide q v0) fs /\
  (forall q, prime q -> Z.divide q v0 -> Z.divide q v \/ In q fs).

(* Trial-division scan: nothing below d divides the remainder any more. *)
Definition AddFactorsScan (v0 v d : Z) (fs : list Z) : Prop :=
  FactorsSoFar v0 v fs /\
  (forall q, 2 <= q -> q < d -> ~ Z.divide q v) /\
  2 ^ (Zlength fs) * v <= v0.

(* Inside the division loop: d is already recorded but not yet divided out,
   so the doubling bound is one step weaker. *)
Definition AddFactorsExtract (v0 v d : Z) (fs : list Z) : Prop :=
  FactorsSoFar v0 v fs /\
  (forall q, 2 <= q -> q < d -> ~ Z.divide q v) /\
  2 <= d /\ In d fs /\
  2 ^ (Zlength fs - 1) * v <= v0.

(* After the scan the trial divisor is out of scope and the leftover is
   one or prime. *)
Definition AddFactorsResidual (v0 v : Z) (fs : list Z) : Prop :=
  FactorsSoFar v0 v fs /\
  (v = 1 \/ prime v) /\
  2 ^ (Zlength fs) * v <= v0.

(* Cheapest price of keeping one surviving element. *)
Definition ElemCost (change p x : Z) : Z :=
  if Z.eqb (x mod p) 0 then 0
  else if orb (Z.eqb ((x - 1) mod p) 0) (Z.eqb ((x + 1) mod p) 0) then change
  else INF.

(* The four families of partial plans tracked by the sweep. *)
Definition DPKeep (a : list Z) (del change p i : Z) : Z -> Prop :=
  fun c => PartialPlanCost a del change p i i i c.

Definition DPCutFresh (a : list Z) (del change p i : Z) : Z -> Prop :=
  fun c => PartialPlanCost a del change p i 0 i c.

Definition DPCutAfterKeep (a : list Z) (del change p i : Z) : Z -> Prop :=
  fun c => exists l, 1 <= l /\ l < i /\ PartialPlanCost a del change p i l i c.

Definition DPAfter (a : list Z) (del change p i : Z) : Z -> Prop :=
  fun c => exists l r, r < i /\ PartialPlanCost a del change p i l r c.

Definition CostForPrimeState
    (a : list Z) (del change p i keep cutFresh cutAfterKeep after : Z) : Prop :=
  DPValue (DPKeep a del change p i) keep /\
  DPValue (DPCutFresh a del change p i) cutFresh /\
  DPValue (DPCutAfterKeep a del change p i) cutAfterKeep /\
  DPValue (DPAfter a del change p i) after.

(* Soundness plus per-shift completeness of the collected moduli. *)
Definition CandidateCoverage (x y d : Z) (fs : list Z) : Prop :=
  Forall (fun q => 2 <= q) fs /\
  (forall q e, prime q -> -1 <= e -> e < d ->
     (Z.divide q (x + e) \/ Z.divide q (y + e)) -> In q fs).

(* Running minimum over the already examined moduli. *)
Definition BestPrefixCost
    (a : list Z) (del change : Z) (ps : list Z) (i best : Z) : Prop :=
  DPValue (fun c => exists j, 0 <= j < i /\ CostForPrime a del change (Znth j ps 0) c) best.

Require Import Coq.ZArith.Zquot.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.Wf_Z.
Lemma rem_zero_iff_divide__addfac_scan_invariant :
  forall (v d : Z), 0 <= v -> 0 < d -> (Z.rem v d = 0 <-> Z.divide d v).
Proof.
  intros v d Hv Hd.
  rewrite Z.rem_mod_nonneg by lia.
  apply Z.mod_divide. lia.
Qed.
Lemma factors_so_far_append__addfac_scan_invariant :
  forall (v0 v d : Z) (fs : list Z),
    FactorsSoFar v0 v fs -> 2 <= d -> Z.divide d v ->
    FactorsSoFar v0 v (fs ++ [d]).
Proof.
  intros v0 v d fs [Hv [Hvv0 [Hfs Hcomp]]] Hd Hdv.
  split; [ exact Hv | ].
  split; [ exact Hvv0 | ].
  split.
  - apply List.Forall_app.
    split; [ exact Hfs | ].
    constructor; [ | constructor ].
    split; [ lia | ].
    apply Z.divide_trans with v; assumption.
  - intros q Hq Hqv0.
    destruct (Hcomp q Hq Hqv0) as [H | H].
    + left; exact H.
    + right. apply List.in_or_app. left; exact H.
Qed.
Lemma scan_extend_divisor__addfac_scan_invariant :
  forall (v d : Z),
    0 <= v -> 2 <= d ->
    (forall q, 2 <= q -> q < d -> ~ Z.divide q v) ->
    Z.rem v d <> 0 ->
    (forall q, 2 <= q -> q < d + 1 -> ~ Z.divide q v).
Proof.
  intros v d Hv Hd Hscan Hrem q Hq2 Hqd.
  destruct (Z.eq_dec q d) as [Heq | Hne].
  - subst q. intros Hdiv. apply Hrem.
    apply (proj2 (rem_zero_iff_divide__addfac_scan_invariant v d Hv ltac:(lia))).
    exact Hdiv.
  - apply Hscan; lia.
Qed.
Lemma firstn_replace_nth_snoc__addfac_scan_invariant :
  forall (A : Type) (n : nat) (l : list A) (x : A),
    (n < length l)%nat ->
    firstn (S n) (replace_nth n l x) = firstn n l ++ [x].
Proof.
  induction n as [| n IH]; intros l x Hn.
  - destruct l as [| a t]; simpl in *; [ lia | reflexivity ].
  - destruct l as [| a t]; simpl in *; [ lia | ].
    rewrite IH by lia. reflexivity.
Qed.
Lemma replace_Znth_sublist_append__addfac_scan_invariant :
  forall (A : Type) (k : Z) (x : A) (l : list A),
    0 <= k -> k < Zlength l ->
    sublist 0 (k + 1) (replace_Znth k x l) = sublist 0 k l ++ [x].
Proof.
  intros A k x l Hk0 Hk1.
  unfold sublist, replace_Znth.
  change (Z.to_nat 0) with 0%nat.
  simpl skipn.
  replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia.
  apply firstn_replace_nth_snoc__addfac_scan_invariant.
  rewrite Zlength_correct in Hk1. lia.
Qed.
Lemma scan_length_bound__addfac_scan_invariant :
  forall (v0 v L : Z),
    0 <= L -> 1 <= v -> v0 <= 1000000001 -> 2 ^ L * v <= v0 -> L <= 29.
Proof.
  intros v0 v L HL Hv Hv0 Hbound.
  assert (Hpow : 0 < 2 ^ L) by (apply Z.pow_pos_nonneg; lia).
  assert (H2 : 2 ^ L <= 1000000001) by nia.
  destruct (Z_le_gt_dec L 29) as [H | H]; [ exact H | ].
  assert (H30 : 2 ^ 30 <= 2 ^ L) by (apply Z.pow_le_mono_r; lia).
  assert (H30v : 2 ^ 30 = 1073741824) by reflexivity.
  lia.
Qed.
Lemma scan_init__addfac_scan_invariant :
  forall (v0 : Z), 1 <= v0 -> AddFactorsScan v0 v0 2 [].
Proof.
  intros v0 Hv0.
  unfold AddFactorsScan, FactorsSoFar.
  split; [ | split ].
  - split; [ lia | ].
    split; [ apply Z.divide_refl | ].
    split; [ constructor | ].
    intros q Hq Hqv0. left; exact Hqv0.
  - intros q Hq2 Hqd. lia.
  - rewrite Zlength_nil, Z.pow_0_r. lia.
Qed.
Lemma scan_step_divisor__addfac_scan_invariant :
  forall (v0 v d : Z) (fs : list Z),
    AddFactorsScan v0 v d fs -> 2 <= d -> Z.rem v d <> 0 ->
    AddFactorsScan v0 v (d + 1) fs.
Proof.
  intros v0 v d fs [HF [Hscan Hbound]] Hd Hrem.
  assert (Hv : 0 <= v) by (destruct HF as [Hv1 _]; lia).
  split; [ exact HF | ].
  split; [ | exact Hbound ].
  apply scan_extend_divisor__addfac_scan_invariant; assumption.
Qed.
Lemma scan_to_extract__addfac_scan_invariant :
  forall (v0 v d : Z) (fs : list Z),
    AddFactorsScan v0 v d fs -> 2 <= d -> Z.divide d v ->
    AddFactorsExtract v0 v d (fs ++ [d]).
Proof.
  intros v0 v d fs [HF [Hscan Hbound]] Hd Hdv.
  unfold AddFactorsExtract.
  split; [ apply factors_so_far_append__addfac_scan_invariant; assumption | ].
  split; [ exact Hscan | ].
  split; [ lia | ].
  split; [ apply List.in_or_app; right; left; reflexivity | ].
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  replace (Zlength fs + Z.succ 0 - 1) with (Zlength fs) by lia.
  exact Hbound.
Qed.
Lemma factors_so_far_quot__addfac_division_residual :
  forall (v0 v d w : Z) (fs : list Z),
    FactorsSoFar v0 v fs ->
    2 <= d ->
    1 <= w ->
    v = d * w ->
    In d fs ->
    (forall q, 2 <= q -> q < d -> ~ Z.divide q v) ->
    FactorsSoFar v0 w fs.
Proof.
  intros v0 v d w fs HF Hd Hw Heq Hin Hscan.
  destruct HF as [Hv1 [Hvv0 [Hall Hcov]]].
  assert (Hwv : Z.divide w v) by (exists d; rewrite Heq; ring).
  assert (Hdv : Z.divide d v) by (exists w; rewrite Heq; ring).
  split; [ lia | ].
  split; [ apply (Z.divide_trans w v v0); assumption | ].
  split; [ assumption | ].
  intros q Hq Hqv0.
  destruct (Hcov q Hq Hqv0) as [Hqv | Hqin]; [ | right; assumption ].
  destruct (Zdivide_dec q w) as [Hqw | Hnqw]; [ left; assumption | ].
  assert (Hqd : Z.divide q d).
  { assert (Hm : Z.divide q (d * w)) by (rewrite <- Heq; assumption).
    destruct (prime_mult q Hq d w Hm) as [H1 | H1];
      [ assumption | contradiction ]. }
  assert (Hq2 : 2 <= q) by (apply prime_ge_2; assumption).
  assert (Hqle : q <= d) by (apply Z.divide_pos_le; [ lia | assumption ]).
  assert (Hqeq : q = d).
  { destruct (Z.eq_dec q d) as [He | Hne]; [ assumption | ].
    exfalso.
    apply (Hscan q Hq2 ltac:(lia)).
    apply (Z.divide_trans q d v); assumption. }
  subst q. right. assumption.
Qed.
Lemma residual_is_one_or_prime__addfac_division_residual :
  forall (v d : Z),
    1 <= v ->
    2 <= d ->
    d * d > v ->
    (forall q, 2 <= q -> q < d -> ~ Z.divide q v) ->
    v = 1 \/ prime v.
Proof.
  intros v d Hv Hd Hdd Hscan.
  destruct (Z.eq_dec v 1) as [He | Hne]; [ left; assumption | right ].
  assert (Hv1 : 1 < v) by lia.
  destruct (prime_dec v) as [Hp | Hnp]; [ assumption | exfalso ].
  destruct (not_prime_divide v Hv1 Hnp) as [m [[Hm1 Hm2] Hmv]].
  destruct Hmv as [k Hk].
  assert (Hkv : Z.divide k v) by (exists m; rewrite Hk; ring).
  assert (Hk2 : 2 <= k) by nia.
  assert (Hmge : d <= m).
  { destruct (Z_lt_le_dec m d) as [Hlt | Hge]; [ | assumption ].
    exfalso. apply (Hscan m ltac:(lia) Hlt). exists k; assumption. }
  assert (Hkge : d <= k).
  { destruct (Z_lt_le_dec k d) as [Hlt | Hge]; [ | assumption ].
    exfalso. apply (Hscan k Hk2 Hlt). assumption. }
  nia.
Qed.
Lemma doubling_bound_quot__addfac_division_residual :
  forall (k v0 v d w : Z),
    1 <= k ->
    2 <= d ->
    1 <= w ->
    v = d * w ->
    2 ^ (k - 1) * v <= v0 ->
    2 ^ k * w <= v0.
Proof.
  intros k v0 v d w Hk Hd Hw Heq Hle.
  assert (Hp : 0 < 2 ^ (k - 1)) by (apply Z.pow_pos_nonneg; lia).
  assert (Hk2 : 2 ^ k = 2 * 2 ^ (k - 1)).
  { replace k with ((k - 1) + 1) at 1 by lia.
    rewrite Z.pow_add_r by lia.
    rewrite Z.pow_1_r. lia. }
  nia.
Qed.
Lemma add_factors_result_append_prime__addfac_frame_result :
  forall (v0 v : Z) (fs : list Z),
    AddFactorsResidual v0 v fs ->
    v > 1 ->
    Zlength fs <= 29 ->
    AddFactorsResult v0 (fs ++ [v]).
Proof.
  intros v0 v fs Hres Hgt Hlen.
  destruct Hres as [Hsofar [Hone Hbound]].
  destruct Hsofar as [Hv1 [Hvdvd [Hall Hcomp]]].
  assert (Hp : prime v).
  { destruct Hone as [Heq | Hpr]; [ lia | exact Hpr ]. }
  split; [ | split ].
  - apply Forall_app; split.
    + exact Hall.
    + constructor; [ split; [ lia | exact Hvdvd ] | constructor ].
  - intros q Hq Hqd.
    destruct (Hcomp q Hq Hqd) as [Hqv | Hin].
    + apply in_or_app; right.
      assert (q = v) by (apply prime_div_prime; assumption).
      subst q; simpl; left; reflexivity.
    + apply in_or_app; left; exact Hin.
  - rewrite Zlength_app.
    rewrite Zlength_cons, Zlength_nil.
    lia.
Qed.
Lemma add_factors_result_of_residual_one__addfac_frame_result :
  forall (v0 v : Z) (fs : list Z),
    AddFactorsResidual v0 v fs ->
    v <= 1 ->
    Zlength fs <= 29 ->
    AddFactorsResult v0 fs.
Proof.
  intros v0 v fs Hres Hle Hlen.
  destruct Hres as [Hsofar [Hone Hbound]].
  destruct Hsofar as [Hv1 [Hvdvd [Hall Hcomp]]].
  assert (Hv : v = 1) by lia.
  subst v.
  split; [ | split ].
  - exact Hall.
  - intros q Hq Hqd.
    destruct (Hcomp q Hq Hqd) as [Hqv | Hin].
    + apply Z.divide_1_r in Hqv.
      destruct Hq as [Hq1 _].
      destruct Hqv as [Hq' | Hq']; lia.
    + exact Hin.
  - lia.
Qed.
Lemma Zlength_replace_nth__addfac_frame_result :
  forall (l : list Z) (n : nat) (v : Z),
    Zlength (replace_nth n l v) = Zlength l.
Proof.
  induction l; intros n v; simpl.
  - destruct n; reflexivity.
  - destruct n; simpl.
    + reflexivity.
    + rewrite !Zlength_cons. rewrite IHl. reflexivity.
Qed.
Lemma Zlength_replace_Znth__addfac_frame_result :
  forall (l : list Z) (n v : Z),
    Zlength (replace_Znth n v l) = Zlength l.
Proof.
  intros l n v. unfold replace_Znth.
  apply Zlength_replace_nth__addfac_frame_result.
Qed.
Lemma sublist_replace_Znth_snoc__addfac_frame_result :
  forall (l : list Z) (i v : Z),
    0 <= i < Zlength l ->
    sublist 0 (i + 1) (replace_Znth i v l) = sublist 0 i l ++ [v].
Proof.
  intros l i v Hi.
  assert (Hlen : Zlength (replace_Znth i v l) = Zlength l)
    by apply Zlength_replace_Znth__addfac_frame_result.
  assert (Hl1 : Zlength (sublist 0 i l) = i)
    by (rewrite Zlength_sublist; lia).
  assert (Hdec : l = sublist 0 i l ++ sublist i (Zlength l) l).
  { rewrite <- (sublist_split 0 (Zlength l) i l) by lia.
    rewrite (sublist_self l (Zlength l)) by reflexivity.
    reflexivity. }
  assert (Hhead : sublist 0 i (replace_Znth i v l) = sublist 0 i l).
  { transitivity
      (sublist 0 i (replace_Znth i v (sublist 0 i l ++ sublist i (Zlength l) l))).
    - rewrite <- Hdec. reflexivity.
    - rewrite replace_Znth_app_r by (rewrite Hl1; lia).
      rewrite (replace_Znth_nothing i (sublist 0 i l) v) by (rewrite Hl1; lia).
      rewrite sublist_split_app_l by (rewrite ?Hl1; lia).
      rewrite (sublist_self (sublist 0 i l) i) by (rewrite Hl1; reflexivity).
      reflexivity. }
  rewrite (sublist_split 0 (i + 1) i (replace_Znth i v l)) by (rewrite ?Hlen; lia).
  rewrite Hhead.
  f_equal.
  rewrite (sublist_single 0 i (replace_Znth i v l)) by (rewrite Hlen; lia).
  rewrite (Znth_replace_Znth_Same 0 l i v) by lia.
  reflexivity.
Qed.
Lemma set_card_empty__cfp_core_init_elemcost :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    (forall x, ~ P x) -> @set_card A P FP = 0.
Proof.
  intros A P FP Hempty.
  unfold set_card, SumLib.Sum.sum.
  destruct (@enum A P FP) as [|x xs] eqn:Hen; [reflexivity |].
  exfalso.
  apply (Hempty x).
  apply (proj2 (@enum_ok A P FP x)).
  rewrite Hen. simpl. auto.
Qed.
Lemma count_nil__cfp_core_init_elemcost :
  forall x : Z, Count x nil = 0.
Proof.
  intros x.
  unfold Count.
  apply set_card_empty__cfp_core_init_elemcost.
  intros k Hk.
  destruct Hk as [Hk _].
  change (Zlength (@nil Z)) with 0 in Hk.
  lia.
Qed.
Lemma zlength_zero_nil__cfp_core_init_elemcost :
  forall (l : list Z), Zlength l = 0 -> l = nil.
Proof.
  intros l Hl.
  destruct l as [|x xs]; [reflexivity |].
  exfalso.
  rewrite Zlength_cons in Hl.
  pose proof (Zlength_nonneg xs).
  lia.
Qed.
Lemma sublist_00__cfp_core_init_elemcost :
  forall (l : list Z), sublist 0 0 l = nil.
Proof.
  intros l. apply Zsublist_nil. lia.
Qed.
Lemma partial_plan_cost_zero_iff__cfp_core_init_elemcost :
  forall (a : list Z) (del change p c : Z),
    PartialPlanCost a del change p 0 0 0 c <-> 0 = c.
Proof.
  intros a del change p c.
  split.
  - intros [Hl [Hlr [Hr [Hi [delta [result [Hadj [Hdiv Hc]]]]]]]].
    destruct Hadj as [Hlen [Hall Hres]].
    rewrite !sublist_00__cfp_core_init_elemcost in Hlen.
    simpl in Hlen.
    change (Zlength (@nil Z)) with 0 in Hlen.
    apply zlength_zero_nil__cfp_core_init_elemcost in Hlen.
    subst delta.
    unfold ChangeCost in Hc.
    rewrite !count_nil__cfp_core_init_elemcost in Hc.
    lia.
  - intros Hc.
    unfold PartialPlanCost.
    split; [lia |]. split; [lia |]. split; [lia |].
    split; [apply Zlength_nonneg |].
    exists nil, nil.
    split; [| split].
    + unfold Adjusted.
      rewrite !sublist_00__cfp_core_init_elemcost.
      simpl.
      split; [reflexivity |].
      split; [apply Forall_nil | reflexivity].
    + apply Forall_nil.
    + unfold ChangeCost.
      rewrite !count_nil__cfp_core_init_elemcost.
      lia.
Qed.
Lemma cost_for_prime_state_init__cfp_core_init_elemcost :
  forall (a : list Z) (del change p : Z),
    CostForPrimeState a del change p 0 0 0 INF INF.
Proof.
  intros a del change p.
  unfold CostForPrimeState.
  split; [| split; [| split]].
  - unfold DPValue. left. split.
    + apply (min_1 Z.le 0 (DPKeep a del change p 0) (fun x => x)).
      intros c. unfold DPKeep.
      apply partial_plan_cost_zero_iff__cfp_core_init_elemcost.
    + unfold INF. lia.
  - unfold DPValue. left. split.
    + apply (min_1 Z.le 0 (DPCutFresh a del change p 0) (fun x => x)).
      intros c. unfold DPCutFresh.
      apply partial_plan_cost_zero_iff__cfp_core_init_elemcost.
    + unfold INF. lia.
  - unfold DPValue. apply min_default_default.
    intros c Hc. unfold DPCutAfterKeep in Hc.
    destruct Hc as [l [Hl1 [Hl2 _]]]. lia.
  - unfold DPValue. apply min_default_default.
    intros c Hc. unfold DPAfter in Hc.
    destruct Hc as [l [r [Hr [Hl [Hlr [Hri _]]]]]]. lia.
Qed.
Lemma elem_cost_rem_mod__cfp_core_init_elemcost :
  forall change p x, 2 <= x -> 2 <= p ->
    (Z.rem x p = 0 -> ElemCost change p x = 0) /\
    (Z.rem x p <> 0 -> Z.rem (x - 1) p = 0 ->
       ElemCost change p x = change) /\
    (Z.rem x p <> 0 -> Z.rem (x - 1) p <> 0 -> Z.rem (x + 1) p = 0 ->
       ElemCost change p x = change) /\
    (Z.rem x p <> 0 -> Z.rem (x - 1) p <> 0 -> Z.rem (x + 1) p <> 0 ->
       ElemCost change p x = INF).
Proof.
  intros change p x Hx Hp.
  assert (H0 : Z.rem x p = x mod p) by (apply Zrem_Zmod_pos; lia).
  assert (H1 : Z.rem (x - 1) p = (x - 1) mod p) by (apply Zrem_Zmod_pos; lia).
  assert (H2 : Z.rem (x + 1) p = (x + 1) mod p) by (apply Zrem_Zmod_pos; lia).
  unfold ElemCost.
  rewrite <- H0, <- H1, <- H2.
  split; [| split; [| split]].
  - intros Ha. rewrite Ha. reflexivity.
  - intros Ha Hb.
    apply Z.eqb_neq in Ha. rewrite Ha.
    rewrite Hb. reflexivity.
  - intros Ha Hb Hc.
    apply Z.eqb_neq in Ha. rewrite Ha.
    apply Z.eqb_neq in Hb. rewrite Hb.
    rewrite Hc. reflexivity.
  - intros Ha Hb Hc.
    apply Z.eqb_neq in Ha. rewrite Ha.
    apply Z.eqb_neq in Hb. rewrite Hb.
    apply Z.eqb_neq in Hc. rewrite Hc.
    reflexivity.
Qed.
Lemma Zrange_aux_length__cfp_exit_min :
  forall (k : nat) (low : Z), length (Zrange_aux low k) = k.
Proof.
  induction k as [| k IH]; intros low; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.
Lemma fold_right_const_one__cfp_exit_min :
  forall (A : Type) (l : list A),
    fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l = Z.of_nat (length l).
Proof.
  intros A l.
  induction l as [| x l IH]; [reflexivity | ].
  replace (fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 (x :: l))
    with (1 + fold_right (fun (_ : A) (acc : Z) => 1 + acc) 0 l) by reflexivity.
  rewrite IH.
  replace (length (x :: l)) with (S (length l)) by reflexivity.
  lia.
Qed.
Lemma set_card_length__cfp_exit_min :
  forall (A : Type) (P : A -> Prop) (HF : Finite P),
    @set_card A P HF = Z.of_nat (length (@enum A P HF)).
Proof.
  intros A P HF.
  unfold set_card, sum.
  cbv beta.
  apply fold_right_const_one__cfp_exit_min.
Qed.
Lemma set_card_range_bound__cfp_exit_min :
  forall (P : Z -> Prop) (HF : Finite P) (n : Z),
    0 <= n ->
    (forall x, P x -> 0 <= x < n) ->
    0 <= @set_card Z P HF <= n.
Proof.
  intros P HF n Hn Hsub.
  rewrite set_card_length__cfp_exit_min.
  assert (Hincl : incl (@enum Z P HF) (Zrange 0 n)).
  { intros x Hx.
    apply In_Zrange.
    apply Hsub.
    apply (proj2 (@enum_ok Z P HF x)).
    exact Hx. }
  pose proof (NoDup_incl_length (@enum_nodup Z P HF) Hincl) as Hlen.
  assert (Hzr : length (Zrange 0 n) = Z.to_nat n).
  { unfold Zrange. replace (n - 0) with n by lia.
    apply Zrange_aux_length__cfp_exit_min. }
  rewrite Hzr in Hlen.
  lia.
Qed.
Lemma count_bound__cfp_exit_min :
  forall (x : Z) (xs : list Z), 0 <= Count x xs <= Zlength xs.
Proof.
  intros x xs.
  unfold Count.
  apply set_card_range_bound__cfp_exit_min.
  - rewrite Zlength_correct. lia.
  - intros y Hy. destruct Hy as [Hy _]. exact Hy.
Qed.
Lemma partial_plan_cost_bound__cfp_exit_min :
  forall a del change p i l r c,
    0 <= del <= 1000000000 ->
    0 <= change <= 1000000000 ->
    Zlength a <= 1000000 ->
    PartialPlanCost a del change p i l r c ->
    0 <= c <= 2000000000000000.
Proof.
  intros a del change p i l r c Hdel Hchange Hn HP.
  destruct HP as [Hl [Hlr [Hri [Hia [delta [result [HA [_ Hc]]]]]]]].
  destruct HA as [Hlen [_ _]].
  rewrite Zlength_app in Hlen.
  rewrite (Zlength_sublist 0 l a) in Hlen by lia.
  rewrite (Zlength_sublist r i a) in Hlen by lia.
  pose proof (count_bound__cfp_exit_min (- 1) delta) as HC1.
  pose proof (count_bound__cfp_exit_min 1 delta) as HC2.
  unfold ChangeCost in Hc.
  assert (H1 : (r - l) * del <= (r - l) * 1000000000) by nia.
  assert (H2 : Count (- 1) delta * change <= Zlength delta * 1000000000) by nia.
  assert (H3 : Count 1 delta * change <= Zlength delta * 1000000000) by nia.
  assert (H4 : 0 <= (r - l) * del) by nia.
  assert (H5 : 0 <= Count (- 1) delta * change) by nia.
  assert (H6 : 0 <= Count 1 delta * change) by nia.
  lia.
Qed.
Lemma dp_value_in__cfp_exit_min :
  forall (S : Z -> Prop) (v : Z), DPValue S v -> v <> INF -> S v.
Proof.
  intros S v HV Hne.
  destruct HV as [[Hmin _] | [_ Heq]]; [| congruence].
  destruct Hmin as [x [[Hx _] Hfx]].
  cbn in Hfx, Hx.
  subst v.
  exact Hx.
Qed.
Lemma le_min_Z__cfp_exit_min :
  forall x y : Z, le_min Z.le x y = Z.min x y.
Proof.
  intros x y.
  destruct (Z_le_dec x y) as [Hle | Hle].
  - rewrite (min_r Z.le x y Hle). lia.
  - assert (y <= x) by lia.
    rewrite (min_l Z.le x y H). lia.
Qed.
Lemma dp_value_min3__cfp_exit_min :
  forall (S1 S2 S3 R : Z -> Prop) (v1 v2 v3 : Z),
    DPValue S1 v1 -> DPValue S2 v2 -> DPValue S3 v3 ->
    (forall c, S1 c \/ S2 c \/ S3 c <-> R c) ->
    DPValue R (Z.min v1 (Z.min v2 v3)).
Proof.
  intros S1 S2 S3 R v1 v2 v3 H1 H2 H3 Hiff.
  unfold DPValue in *.
  pose proof (min_default_union Z.le v2 v3 (fun x : Z => x) S2 S3
                (fun c => S2 c \/ S3 c) INF H2 H3
                ltac:(intros; tauto)) as H23.
  rewrite le_min_Z__cfp_exit_min in H23.
  pose proof (min_default_union Z.le v1 (Z.min v2 v3) (fun x : Z => x) S1
                (fun c => S2 c \/ S3 c) R INF H1 H23
                ltac:(intros a; specialize (Hiff a); tauto)) as H123.
  rewrite le_min_Z__cfp_exit_min in H123.
  exact H123.
Qed.
Lemma pfeasible_plan_split__cfp_exit_min :
  forall (a : list Z) (del change p c : Z),
    1 <= Zlength a ->
    (DPKeep a del change p (Zlength a) c \/
     (DPCutAfterKeep a del change p (Zlength a) c \/
      DPAfter a del change p (Zlength a) c)) <->
    PFeasiblePlan a del change p c.
Proof.
  intros a del change p c Hpos.
  split.
  - intros [HK | [HC | HA]].
    + unfold DPKeep in HK.
      exists (Zlength a), (Zlength a). split; [lia | exact HK].
    + destruct HC as [l [Hl1 [Hl2 HP]]].
      exists l, (Zlength a). split; [lia | exact HP].
    + destruct HA as [l [r [Hr HP]]].
      assert (Hl : 0 <= l) by (destruct HP as [? _]; lia).
      exists l, r. split; [lia | exact HP].
  - intros [l [r [Hlt HP]]].
    assert (Hb : 0 <= l /\ l <= r /\ r <= Zlength a)
      by (destruct HP as [Ha [Hb1 [Hb2 _]]]; lia).
    destruct (Z_lt_dec r (Zlength a)) as [Hrlt | Hrge].
    + right; right. exists l, r. split; [lia | exact HP].
    + assert (Hr : r = Zlength a) by lia.
      subst r.
      destruct (Z_lt_dec l (Zlength a)) as [Hllt | Hlge].
      * right; left. exists l. split; [lia | split; [lia | exact HP]].
      * assert (Hl : l = Zlength a) by lia.
        subst l. left. exact HP.
Qed.
Lemma cost_for_prime_exit__cfp_exit_min :
  forall (values : list Z) (del change p i keep cutFresh cutAfterKeep after : Z),
    1 <= Zlength values ->
    i = Zlength values ->
    CostForPrimeState values del change p i keep cutFresh cutAfterKeep after ->
    CostForPrime values del change p (Z.min keep (Z.min cutAfterKeep after)).
Proof.
  intros values del change p i keep cutFresh cutAfterKeep after Hpos Hi HS.
  subst i.
  destruct HS as [HK [_ [HC HA]]].
  unfold CostForPrime.
  apply (dp_value_min3__cfp_exit_min
           (DPKeep values del change p (Zlength values))
           (DPCutAfterKeep values del change p (Zlength values))
           (DPAfter values del change p (Zlength values))
           (PFeasiblePlan values del change p)
           keep cutAfterKeep after HK HC HA).
  intros c.
  apply pfeasible_plan_split__cfp_exit_min.
  exact Hpos.
Qed.
Lemma cost_for_prime_bound__cfp_exit_min :
  forall (a : list Z) (del change p out : Z),
    0 <= del <= 1000000000 ->
    0 <= change <= 1000000000 ->
    Zlength a <= 1000000 ->
    CostForPrime a del change p out ->
    out <> INF ->
    0 <= out <= 2000000000000000.
Proof.
  intros a del change p out Hdel Hchange Hn HC Hne.
  unfold CostForPrime in HC.
  apply dp_value_in__cfp_exit_min in HC; [| exact Hne].
  destruct HC as [l [r [_ HP]]].
  exact (partial_plan_cost_bound__cfp_exit_min a del change p (Zlength a) l r out
           Hdel Hchange Hn HP).
Qed.
Lemma sum_empty__cfp_step_01 : forall (A : Type) (P : A -> Prop) (HF : Finite P) (f : A -> Z),
  (forall x, ~ P x) -> @sum A P HF f = 0.
Proof.
  intros A P HF f Hemp.
  unfold sum.
  destruct HF as [e ok nd]. simpl.
  destruct e as [| y e']; [reflexivity |].
  exfalso. apply (Hemp y). apply ok. simpl. left. reflexivity.
Qed.
Lemma count_nil__cfp_step_01 : forall x : Z, Count x nil = 0.
Proof.
  intros x. unfold Count, set_card.
  apply sum_empty__cfp_step_01. intros i [Hi _]. rewrite Zlength_nil in Hi. lia.
Qed.
Lemma sublist_empty__cfp_step_01 : forall (l : list Z) (i j : Z), j <= i -> sublist i j l = nil.
Proof. intros. apply Zsublist_nil. lia. Qed.
Lemma dpcutfresh_iff__cfp_step_01 : forall a del change p i c,
  0 <= i -> i <= Zlength a ->
  (DPCutFresh a del change p i c <-> c = i * del).
Proof.
  intros a del change p i c Hi0 Hi1.
  unfold DPCutFresh, PartialPlanCost.
  rewrite (sublist_empty__cfp_step_01 a 0 0) by lia.
  rewrite (sublist_empty__cfp_step_01 a i i) by lia.
  simpl.
  split.
  - intros [_ [_ [_ [_ [delta [result [Hadj [_ Hc]]]]]]]].
    unfold Adjusted in Hadj. destruct Hadj as [Hlen [_ _]].
    rewrite Zlength_nil in Hlen.
    assert (delta = nil).
    { destruct delta as [| z delta']; [reflexivity |].
      exfalso. rewrite Zlength_cons in Hlen.
      pose proof (Zlength_nonneg delta'). lia. }
    subst delta. unfold ChangeCost in Hc. rewrite !count_nil__cfp_step_01 in Hc. lia.
  - intros ->.
    split; [lia | split; [lia | split; [lia | split; [lia | ]]]].
    exists nil, nil.
    split; [| split].
    + unfold Adjusted. simpl. split; [reflexivity | split; [constructor | reflexivity]].
    + constructor.
    + unfold ChangeCost. rewrite !count_nil__cfp_step_01. lia.
Qed.
Lemma dpvalue_inf_lb__cfp_step_01 : forall (X : Z -> Prop) (c : Z),
  DPValue X INF -> X c -> INF <= c.
Proof.
  intros X c HD HX.
  unfold DPValue, min_value_of_subset_with_default, min_value_of_subset,
         min_object_of_subset in HD.
  sets_unfold in HD.
  destruct HD as [[[m [[Hm Hmin] Heq]] Hle] | [Hall Heq]].
  - cbv beta in Heq. subst m. apply Hmin. exact HX.
  - apply Hall. exact HX.
Qed.
Lemma dpvalue_inf_intro__cfp_step_01 : forall (X : Z -> Prop),
  (forall c, X c -> INF <= c) -> DPValue X INF.
Proof.
  intros X H. unfold DPValue, min_value_of_subset_with_default.
  right. split; [| reflexivity].
  sets_unfold. intros b Hb. apply H. exact Hb.
Qed.
Lemma dpvalue_singleton__cfp_step_01 : forall (X : Z -> Prop) (k v : Z),
  (forall c, X c <-> c = k) -> k < INF -> DPValue X v -> v = k.
Proof.
  intros X k v Hiff Hk HD.
  unfold DPValue, min_value_of_subset_with_default, min_value_of_subset,
         min_object_of_subset in HD.
  sets_unfold in HD.
  destruct HD as [[[m [[Hm _] Heq]] _] | [Hall Heq]].
  - cbv beta in Heq. apply Hiff in Hm. lia.
  - exfalso. assert (Hk0 : X k) by (apply Hiff; reflexivity).
    apply Hall in Hk0. cbv beta in Hk0. lia.
Qed.
Lemma dpvalue_singleton_intro__cfp_step_01 : forall (X : Z -> Prop) (k : Z),
  (forall c, X c <-> c = k) -> k <= INF -> DPValue X k.
Proof.
  intros X k Hiff Hk.
  unfold DPValue, min_value_of_subset_with_default, min_value_of_subset,
         min_object_of_subset.
  left. split; [| exact Hk].
  sets_unfold. exists k. split; [split |].
  - apply Hiff; reflexivity.
  - intros b Hb. apply Hiff in Hb. cbv beta. lia.
  - reflexivity.
Qed.
Lemma cutfresh_bound__cfp_step_01 : forall a del change p i v,
  0 <= i -> i <= 1000000 -> i <= Zlength a -> 0 <= del -> del <= 1000000000 ->
  DPValue (DPCutFresh a del change p i) v ->
  v = i * del /\ v <= 1000000000000000.
Proof.
  intros a del change p i v Hi0 Hi1 Hi2 Hd0 Hd1 HD.
  assert (Hb : i * del <= 1000000 * 1000000000).
  { apply Z.mul_le_mono_nonneg; lia. }
  assert (Hnn : 0 <= i * del) by (apply Z.mul_nonneg_nonneg; lia).
  assert (Hv : v = i * del).
  { apply (dpvalue_singleton__cfp_step_01 (DPCutFresh a del change p i) (i * del) v).
    - intros c. apply dpcutfresh_iff__cfp_step_01; lia.
    - unfold INF. lia.
    - exact HD. }
  split; [exact Hv | lia].
Qed.
Lemma cutfresh_intro__cfp_step_01 : forall a del change p i,
  0 <= i -> i <= Zlength a -> i * del <= INF ->
  DPValue (DPCutFresh a del change p i) (i * del).
Proof.
  intros a del change p i Hi0 Hi1 Hb.
  apply dpvalue_singleton_intro__cfp_step_01; [| exact Hb].
  intros c. apply dpcutfresh_iff__cfp_step_01; lia.
Qed.
Lemma elemcost_inf_not_divide__cfp_step_01 : forall change p x d,
  2 <= p -> 0 <= change -> change < INF ->
  ElemCost change p x = INF ->
  (d = -1 \/ d = 0 \/ d = 1) -> ~ Z.divide p (x + d).
Proof.
  intros change p x d Hp Hc0 Hc1 HE Hd Hdiv.
  unfold ElemCost in HE.
  destruct (Z.eqb (x mod p) 0) eqn:E0.
  { unfold INF in HE. lia. }
  destruct (orb (Z.eqb ((x - 1) mod p) 0) (Z.eqb ((x + 1) mod p) 0)) eqn:E1.
  { lia. }
  apply Z.eqb_neq in E0.
  apply orb_false_iff in E1. destruct E1 as [E1a E1b].
  apply Z.eqb_neq in E1a. apply Z.eqb_neq in E1b.
  assert (Hm : (x + d) mod p = 0) by (apply Z.mod_divide; [lia | exact Hdiv]).
  destruct Hd as [Hd | [Hd | Hd]]; subst d.
  - apply E1a. replace (x - 1) with (x + -1) by lia. exact Hm.
  - apply E0. replace x with (x + 0) at 1 by lia. exact Hm.
  - apply E1b. exact Hm.
Qed.
Lemma nth_map_combine__cfp_step_01 : forall (kept delta : list Z) (n : nat),
  (n < length kept)%nat -> length delta = length kept ->
  nth n (map (fun q : Z * Z => fst q + snd q) (combine kept delta)) 0
  = nth n kept 0 + nth n delta 0.
Proof.
  induction kept as [| x kept IH]; intros delta n Hn Hl; simpl in *; [lia |].
  destruct delta as [| y delta]; simpl in Hl; [lia |].
  destruct n as [| n]; simpl; [reflexivity |].
  apply IH; lia.
Qed.
Lemma adjusted_znth__cfp_step_01 : forall kept delta result j,
  Adjusted kept delta result -> 0 <= j < Zlength kept ->
  exists d, (d = -1 \/ d = 0 \/ d = 1) /\ Znth j result 0 = Znth j kept 0 + d.
Proof.
  intros kept delta result j Hadj Hj.
  destruct Hadj as [Hlen [Hall Hres]].
  assert (Hn : (Z.to_nat j < length kept)%nat) by (rewrite Zlength_correct in Hj; lia).
  assert (Hlen' : length delta = length kept) by (rewrite !Zlength_correct in Hlen; lia).
  exists (Znth j delta 0).
  split.
  - unfold Znth. rewrite Forall_nth in Hall. apply Hall. lia.
  - subst result. unfold Znth.
    apply nth_map_combine__cfp_step_01; lia.
Qed.
Lemma plan_bad_elem__cfp_step_01 : forall a del change p i l r c j,
  2 <= p -> 0 <= change -> change < INF ->
  PartialPlanCost a del change p i l r c ->
  0 <= j < Zlength (sublist 0 l a ++ sublist r i a) ->
  ElemCost change p (Znth j (sublist 0 l a ++ sublist r i a) 0) = INF ->
  False.
Proof.
  intros a del change p i l r c j Hp Hc0 Hc1 Hplan Hj HE.
  destruct Hplan as [_ [_ [_ [_ [delta [result [Hadj [Hdiv Hc]]]]]]]].
  assert (Hlr : length result = length (sublist 0 l a ++ sublist r i a)).
  { destruct Hadj as [Hlen [_ Hres]]. subst result.
    rewrite length_map, length_combine.
    rewrite !Zlength_correct in Hlen. lia. }
  destruct (adjusted_znth__cfp_step_01 _ _ _ _ Hadj Hj) as [d [Hd Heq]].
  apply (elemcost_inf_not_divide__cfp_step_01 change p _ d Hp Hc0 Hc1 HE Hd).
  rewrite <- Heq.
  rewrite Forall_forall in Hdiv. apply Hdiv.
  unfold Znth. apply nth_In.
  rewrite Hlr. rewrite Zlength_correct in Hj. lia.
Qed.
Lemma dpkeep_step_inf__cfp_step_01 : forall a del change p i,
  0 <= i -> i < Zlength a -> 2 <= p -> 0 <= change -> change < INF ->
  ElemCost change p (Znth i a 0) = INF ->
  DPValue (DPKeep a del change p (i + 1)) INF.
Proof.
  intros a del change p i Hi0 Hi1 Hp Hc0 Hc1 HE.
  apply dpvalue_inf_intro__cfp_step_01. intros c Hc. exfalso.
  unfold DPKeep in Hc.
  assert (Hnil : sublist (i + 1) (i + 1) a = nil) by (apply sublist_empty__cfp_step_01; lia).
  apply (plan_bad_elem__cfp_step_01 a del change p (i + 1) (i + 1) (i + 1) c i Hp Hc0 Hc1 Hc).
  - rewrite Zlength_app, Hnil, Zlength_nil.
    rewrite Zlength_sublist0 by lia. lia.
  - rewrite Hnil, app_nil_r. rewrite Znth_sublist0 by lia. exact HE.
Qed.
Lemma dpafter_step_inf__cfp_step_01 : forall a del change p i,
  0 <= i -> i < Zlength a -> 2 <= p -> 0 <= change -> change < INF ->
  ElemCost change p (Znth i a 0) = INF ->
  DPValue (DPAfter a del change p (i + 1)) INF.
Proof.
  intros a del change p i Hi0 Hi1 Hp Hc0 Hc1 HE.
  apply dpvalue_inf_intro__cfp_step_01. intros c Hc. exfalso.
  unfold DPAfter in Hc. destruct Hc as [l [r [Hr Hplan]]].
  assert (Hb := Hplan).
  destruct Hb as [Hl [Hlr [Hri [Hia _]]]].
  assert (Hkl : Zlength (sublist 0 l a) = l) by (apply Zlength_sublist0; lia).
  assert (Hkr : Zlength (sublist r (i + 1) a) = i + 1 - r) by (apply Zlength_sublist; lia).
  apply (plan_bad_elem__cfp_step_01 a del change p (i + 1) l r c (l + (i - r)) Hp Hc0 Hc1 Hplan).
  - rewrite Zlength_app. lia.
  - rewrite app_Znth2 by lia.
    rewrite Hkl.
    replace (l + (i - r) - l) with (i - r) by lia.
    rewrite Znth_sublist by lia.
    replace (i - r + r) with i by lia.
    exact HE.
Qed.
Lemma dpcutafterkeep_step_inf__cfp_step_01 : forall a del change p i,
  0 <= del -> 0 < i -> i <= Zlength a ->
  DPValue (DPKeep a del change p i) INF ->
  DPValue (DPCutAfterKeep a del change p i) INF ->
  DPValue (DPCutAfterKeep a del change p (i + 1)) INF.
Proof.
  intros a del change p i Hdel Hi0 Hi1 HK HC.
  apply dpvalue_inf_intro__cfp_step_01. intros c Hc.
  destruct Hc as [l [Hl1 [Hl2 Hplan]]].
  destruct Hplan as [Hpl [Hplr [Hpri [Hpia [delta [result [Hadj [Hdiv Hcost]]]]]]]].
  assert (Hnil1 : sublist (i + 1) (i + 1) a = nil) by (apply sublist_empty__cfp_step_01; lia).
  assert (Hnil2 : sublist i i a = nil) by (apply sublist_empty__cfp_step_01; lia).
  rewrite Hnil1 in Hadj.
  assert (Hcc : c = ChangeCost del change l i delta + del).
  { rewrite Hcost. unfold ChangeCost.
    replace (i + 1 - l) with ((i - l) + 1) by lia.
    rewrite Z.mul_add_distr_r. lia. }
  destruct (Z.eq_dec l i) as [Hli | Hli].
  - subst l.
    assert (HcK : DPKeep a del change p i (ChangeCost del change i i delta)).
    { unfold DPKeep, PartialPlanCost.
      split; [lia | split; [lia | split; [lia | split; [lia | ]]]].
      exists delta, result. rewrite Hnil2.
      split; [exact Hadj | split; [exact Hdiv | reflexivity]]. }
    pose proof (dpvalue_inf_lb__cfp_step_01 _ _ HK HcK). lia.
  - assert (HcC : DPCutAfterKeep a del change p i (ChangeCost del change l i delta)).
    { unfold DPCutAfterKeep.
      exists l. split; [lia | split; [lia | ]].
      unfold PartialPlanCost.
      split; [lia | split; [lia | split; [lia | split; [lia | ]]]].
      exists delta, result. rewrite Hnil2.
      split; [exact Hadj | split; [exact Hdiv | reflexivity]]. }
    pose proof (dpvalue_inf_lb__cfp_step_01 _ _ HC HcC). lia.
Qed.
Lemma sum_of_empty_set__cfp_step_02 : forall (A : Type) (P : A -> Prop) (HF : Finite P) (f : A -> Z),
  (forall x, ~ P x) -> @sum A P HF f = 0.
Proof.
  intros A P HF f Hemp.
  unfold sum.
  destruct HF as [e ok nd]. simpl.
  destruct e as [| y e']; [reflexivity |].
  exfalso. apply (Hemp y). apply ok. simpl. left. reflexivity.
Qed.
Lemma count_nil__cfp_step_02 : forall (x : Z), Count x nil = 0.
Proof.
  intros x. unfold Count, set_card.
  apply sum_of_empty_set__cfp_step_02.
  intros y [Hy _]. rewrite Zlength_nil in Hy. lia.
Qed.
Lemma sum_ones_enum__cfp_step_02 : forall (P : Z -> Prop) (HF : Finite P),
  @sum Z P HF (fun _ => 1) = Zlength (@enum Z P HF).
Proof.
  intros P HF. unfold sum.
  induction (@enum Z P HF) as [| z l IH].
  - reflexivity.
  - cbn [fold_right]. rewrite IH. rewrite Zlength_cons. lia.
Qed.
Lemma sum_ones_bound__cfp_step_02 : forall (P : Z -> Prop) (HF : Finite P) (N : Z),
  0 <= N -> (forall x, P x -> 0 <= x < N) -> @sum Z P HF (fun _ => 1) <= N.
Proof.
  intros P HF N HN Hb.
  rewrite sum_ones_enum__cfp_step_02.
  assert (Hincl : incl (@enum Z P HF) (map Z.of_nat (seq 0 (Z.to_nat N)))).
  { intros z Hz. apply in_map_iff. exists (Z.to_nat z).
    assert (Hp : 0 <= z < N) by (apply Hb; apply enum_ok; exact Hz).
    split; [lia |]. apply in_seq. lia. }
  pose proof (NoDup_incl_length (@enum_nodup Z P HF) Hincl) as Hle.
  rewrite length_map, length_seq in Hle.
  rewrite Zlength_correct. lia.
Qed.
Lemma count_le_length__cfp_step_02 : forall (x : Z) (xs : list Z), Count x xs <= Zlength xs.
Proof.
  intros x xs. unfold Count, set_card.
  apply sum_ones_bound__cfp_step_02.
  - apply Zlength_nonneg.
  - intros y [Hy _]. lia.
Qed.
Lemma sublist_empty__cfp_step_02 : forall (a : list Z) (x y : Z), y <= x -> sublist x y a = nil.
Proof.
  intros a x y H. unfold sublist. apply skipn_all2.
  rewrite length_firstn. lia.
Qed.
Lemma sublist_first__cfp_step_02 : forall (a : list Z),
  1 <= Zlength a -> sublist 0 1 a = cons (Znth 0 a 0) nil.
Proof.
  intros a H. destruct a as [| x l].
  - rewrite Zlength_nil in H. lia.
  - reflexivity.
Qed.
Lemma Zlength_sublist_ub__cfp_step_02 : forall (a : list Z) (x y : Z),
  0 <= x -> x <= y -> Zlength (sublist x y a) <= y - x.
Proof.
  intros a x y Hx Hxy.
  rewrite Zlength_correct. unfold sublist.
  rewrite length_skipn, length_firstn. lia.
Qed.
Lemma Zlength_zero_nil__cfp_step_02 : forall (l : list Z), Zlength l = 0 -> l = nil.
Proof.
  intros l H. destruct l as [| z l]; [reflexivity |].
  rewrite Zlength_cons in H. pose proof (Zlength_nonneg l). lia.
Qed.
Lemma dpvalue_mem_le__cfp_step_02 : forall (S : Z -> Prop) (v c : Z),
  DPValue S v -> S c -> v <= c.
Proof.
  intros S v c HD HS. unfold DPValue, min_value_of_subset_with_default in HD.
  destruct HD as [[HM Hle] | [Hall Heq]].
  - unfold min_value_of_subset, min_object_of_subset in HM.
    destruct HM as [x [[Hx Hmin] Hfx]]. subst v.
    apply Hmin. sets_unfold. exact HS.
  - subst v. apply Hall. sets_unfold. exact HS.
Qed.
Lemma dpvalue_finite_mem__cfp_step_02 : forall (S : Z -> Prop) (v : Z),
  DPValue S v -> v <> INF -> S v.
Proof.
  intros S v HD Hne. unfold DPValue, min_value_of_subset_with_default in HD.
  destruct HD as [[HM Hle] | [Hall Heq]].
  - unfold min_value_of_subset, min_object_of_subset in HM.
    destruct HM as [x [[Hx Hmin] Hfx]]. subst v. sets_unfold in Hx. exact Hx.
  - contradiction.
Qed.
Lemma dpvalue_empty__cfp_step_02 : forall (S : Z -> Prop) (v : Z),
  DPValue S v -> (forall c, ~ S c) -> v = INF.
Proof.
  intros S v HD Hemp. unfold DPValue, min_value_of_subset_with_default in HD.
  destruct HD as [[HM Hle] | [Hall Heq]].
  - unfold min_value_of_subset, min_object_of_subset in HM.
    destruct HM as [x [[Hx Hmin] Hfx]]. sets_unfold in Hx.
    exfalso. apply (Hemp x). exact Hx.
  - exact Heq.
Qed.
Lemma dpvalue_of_empty__cfp_step_02 : forall (S : Z -> Prop),
  (forall c, ~ S c) -> DPValue S INF.
Proof.
  intros S Hemp. unfold DPValue, min_value_of_subset_with_default.
  right. split; [| reflexivity]. intros c Hc. sets_unfold in Hc.
  exfalso. apply (Hemp c). exact Hc.
Qed.
Lemma dpvalue_intro__cfp_step_02 : forall (S : Z -> Prop) (v : Z),
  S v -> (forall c, S c -> v <= c) -> v <= INF -> DPValue S v.
Proof.
  intros S v Hv Hmin Hle. unfold DPValue, min_value_of_subset_with_default.
  left. split; [| exact Hle].
  unfold min_value_of_subset, min_object_of_subset.
  exists v. split; [| reflexivity]. split.
  - sets_unfold. exact Hv.
  - intros b Hb. sets_unfold in Hb. apply Hmin. exact Hb.
Qed.
Lemma plan_cut_all__cfp_step_02 : forall (a : list Z) (del change p i : Z),
  0 <= i <= Zlength a -> PartialPlanCost a del change p i 0 i (i * del).
Proof.
  intros a del change p i Hi.
  unfold PartialPlanCost.
  split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
  exists nil, nil.
  rewrite (sublist_empty__cfp_step_02 a 0 0) by lia.
  rewrite (sublist_empty__cfp_step_02 a i i) by lia.
  split; [| split].
  - unfold Adjusted. split; [reflexivity |]. split; [constructor | reflexivity].
  - constructor.
  - unfold ChangeCost. rewrite !count_nil__cfp_step_02. lia.
Qed.
Lemma plan_kept_nil_cost__cfp_step_02 : forall (a : list Z) (del change p i l r c : Z),
  sublist 0 l a ++ sublist r i a = nil ->
  PartialPlanCost a del change p i l r c -> c = (r - l) * del.
Proof.
  intros a del change p i l r c Hkept HP.
  destruct HP as [_ [_ [_ [_ [delta [result [HA [_ Hcost]]]]]]]].
  destruct HA as [HZ _].
  rewrite Hkept in HZ. rewrite Zlength_nil in HZ.
  apply Zlength_zero_nil__cfp_step_02 in HZ. subst delta.
  unfold ChangeCost in Hcost. rewrite !count_nil__cfp_step_02 in Hcost. lia.
Qed.
Lemma plan_cost_bound__cfp_step_02 : forall (a : list Z) (del change p i l r c : Z),
  0 <= del -> 0 <= change ->
  PartialPlanCost a del change p i l r c ->
  c <= Zlength a * del + 2 * (Zlength a * change).
Proof.
  intros a del change p i l r c Hd Hch HP.
  destruct HP as [Hl [Hlr [Hri [Hia [delta [result [HA [_ Hcost]]]]]]]].
  destruct HA as [HZ _].
  assert (Hub : Zlength delta <= Zlength a).
  { rewrite HZ. rewrite Zlength_app.
    pose proof (Zlength_sublist_ub__cfp_step_02 a 0 l ltac:(lia) ltac:(lia)).
    pose proof (Zlength_sublist_ub__cfp_step_02 a r i ltac:(lia) ltac:(lia)).
    lia. }
  pose proof (count_le_length__cfp_step_02 (-1) delta) as C1.
  pose proof (count_le_length__cfp_step_02 1 delta) as C2.
  subst c. unfold ChangeCost. nia.
Qed.
Lemma plan_kept_one_infeasible__cfp_step_02 :
  forall (a : list Z) (del change p i l r c x : Z),
  2 <= p -> change <> INF ->
  ElemCost change p x = INF ->
  sublist 0 l a ++ sublist r i a = cons x nil ->
  ~ PartialPlanCost a del change p i l r c.
Proof.
  intros a del change p i l r c x Hp Hch Hec Hkept HP.
  destruct HP as [_ [_ [_ [_ [delta [result [HA [HFo _]]]]]]]].
  destruct HA as [HZ [HD Hres]].
  rewrite Hkept in HZ, Hres.
  rewrite Zlength_cons, Zlength_nil in HZ.
  destruct delta as [| d delta'].
  { rewrite Zlength_nil in HZ. lia. }
  destruct delta' as [| d' delta''].
  2: { rewrite !Zlength_cons in HZ. pose proof (Zlength_nonneg delta''). lia. }
  simpl in Hres. subst result.
  inversion HD as [| ? ? Hd _]; subst.
  inversion HFo as [| ? ? Hdiv _]; subst.
  assert (Hp0 : p <> 0) by lia.
  unfold ElemCost in Hec.
  destruct (Z.eqb_spec (x mod p) 0) as [E1 | E1].
  { unfold INF in Hec. lia. }
  destruct (orb (Z.eqb ((x - 1) mod p) 0) (Z.eqb ((x + 1) mod p) 0)) eqn:E2.
  { contradiction. }
  apply orb_false_elim in E2. destruct E2 as [E2 E3].
  apply Z.eqb_neq in E2. apply Z.eqb_neq in E3.
  apply (Z.mod_divide _ _ Hp0) in Hdiv.
  destruct Hd as [Hd | [Hd | Hd]]; subst d.
  - replace (x + -1) with (x - 1) in Hdiv by lia. contradiction.
  - replace (x + 0) with x in Hdiv by lia. contradiction.
  - contradiction.
Qed.
Lemma cfp_state_zero__cfp_step_02 :
  forall (a : list Z) (del change p keep cutFresh cutAfterKeep after : Z),
  CostForPrimeState a del change p 0 keep cutFresh cutAfterKeep after ->
  keep <= 0 /\ cutFresh <= 0 /\ cutAfterKeep = INF /\ after = INF.
Proof.
  intros a del change p keep cutFresh cutAfterKeep after HS.
  destruct HS as [HK [HCF [HCA HAf]]].
  pose proof (Zlength_nonneg a) as Hna.
  pose proof (plan_cut_all__cfp_step_02 a del change p 0 ltac:(lia)) as Hplan.
  split; [| split; [| split]].
  - pose proof (dpvalue_mem_le__cfp_step_02 _ _ (0 * del) HK Hplan) as H. lia.
  - pose proof (dpvalue_mem_le__cfp_step_02 _ _ (0 * del) HCF Hplan) as H. lia.
  - apply (dpvalue_empty__cfp_step_02 _ _ HCA). intros c Hc. unfold DPCutAfterKeep in Hc.
    destruct Hc as [l [Hl1 [Hl2 _]]]. lia.
  - apply (dpvalue_empty__cfp_step_02 _ _ HAf). intros c Hc. unfold DPAfter in Hc.
    destruct Hc as [l [r [Hr HP]]].
    destruct HP as [Hl [Hlr [Hri _]]]. lia.
Qed.
Lemma cfp_state_cutfresh_le__cfp_step_02 :
  forall (a : list Z) (del change p i keep cutFresh cutAfterKeep after : Z),
  0 <= i <= Zlength a ->
  CostForPrimeState a del change p i keep cutFresh cutAfterKeep after ->
  cutFresh <= i * del.
Proof.
  intros a del change p i keep cutFresh cutAfterKeep after Hi HS.
  destruct HS as [_ [HCF _]].
  apply (dpvalue_mem_le__cfp_step_02 _ _ _ HCF). unfold DPCutFresh.
  apply plan_cut_all__cfp_step_02. lia.
Qed.
Lemma cfp_state_finite_bound__cfp_step_02 :
  forall (a : list Z) (del change p i keep cutFresh cutAfterKeep after : Z),
  0 <= del -> 0 <= change ->
  CostForPrimeState a del change p i keep cutFresh cutAfterKeep after ->
  (keep <> INF -> keep <= Zlength a * del + 2 * (Zlength a * change)) /\
  (cutFresh <> INF -> cutFresh <= Zlength a * del + 2 * (Zlength a * change)) /\
  (cutAfterKeep <> INF -> cutAfterKeep <= Zlength a * del + 2 * (Zlength a * change)) /\
  (after <> INF -> after <= Zlength a * del + 2 * (Zlength a * change)).
Proof.
  intros a del change p i keep cutFresh cutAfterKeep after Hd Hch HS.
  destruct HS as [HK [HCF [HCA HAf]]].
  split; [| split; [| split]].
  - intros Hne. pose proof (dpvalue_finite_mem__cfp_step_02 _ _ HK Hne) as Hm.
    unfold DPKeep in Hm. exact (plan_cost_bound__cfp_step_02 _ _ _ _ _ _ _ _ Hd Hch Hm).
  - intros Hne. pose proof (dpvalue_finite_mem__cfp_step_02 _ _ HCF Hne) as Hm.
    unfold DPCutFresh in Hm. exact (plan_cost_bound__cfp_step_02 _ _ _ _ _ _ _ _ Hd Hch Hm).
  - intros Hne. pose proof (dpvalue_finite_mem__cfp_step_02 _ _ HCA Hne) as Hm.
    unfold DPCutAfterKeep in Hm. destruct Hm as [l [_ [_ Hm]]].
    exact (plan_cost_bound__cfp_step_02 _ _ _ _ _ _ _ _ Hd Hch Hm).
  - intros Hne. pose proof (dpvalue_finite_mem__cfp_step_02 _ _ HAf Hne) as Hm.
    unfold DPAfter in Hm. destruct Hm as [l [r [_ Hm]]].
    exact (plan_cost_bound__cfp_step_02 _ _ _ _ _ _ _ _ Hd Hch Hm).
Qed.
Lemma zlength_zero_nil__cfp_step_03 : forall (l : list Z),
  Zlength l = 0 -> l = [].
Proof.
  intros l H.
  destruct l as [| x l]; [reflexivity |].
  rewrite Zlength_correct in H. simpl in H. lia.
Qed.
Lemma fold_filter_card_bound__cfp_step_03 :
  forall (g : Z -> bool) (l : list Z),
    0 <= fold_right (fun _ acc : Z => 1 + acc) 0 (filter g l) <= Z.of_nat (length l).
Proof.
  intros g l. induction l as [| x l IH]; [cbn [filter fold_right length]; lia |].
  cbn [length]. rewrite Nat2Z.inj_succ. cbn [filter].
  destruct (g x); cbn [fold_right]; lia.
Qed.
Lemma length_Zrange_aux__cfp_step_03 :
  forall (n : nat) (low : Z), length (Zrange_aux low n) = n.
Proof.
  induction n as [| n IH]; intros low; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.
Lemma length_Zrange__cfp_step_03 :
  forall (low high : Z), length (Zrange low high) = Z.to_nat (high - low).
Proof.
  intros low high. unfold Zrange. apply length_Zrange_aux__cfp_step_03.
Qed.
Lemma count_bounds__cfp_step_03 : forall (x : Z) (xs : list Z),
  0 <= Count x xs <= Zlength xs.
Proof.
  intros x xs.
  unfold Count, set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range enum].
  pose proof (fold_filter_card_bound__cfp_step_03
    (fun x0 : Z => if prop_dec (Znth x0 xs 0 = x) then true else false)
    (Zrange 0 (Zlength xs))) as Hb.
  rewrite length_Zrange__cfp_step_03 in Hb.
  pose proof (Zlength_nonneg xs) as Hn.
  replace (Zlength xs - 0) with (Zlength xs) in Hb by lia.
  rewrite Z2Nat.id in Hb by lia.
  exact Hb.
Qed.
Lemma count_nil__cfp_step_03 : forall (x : Z), Count x (@nil Z) = 0.
Proof.
  intros x.
  pose proof (count_bounds__cfp_step_03 x (@nil Z)) as H.
  change (Zlength (@nil Z)) with 0 in H. lia.
Qed.
Lemma nth_map_combine__cfp_step_03 : forall (kept delta : list Z) (n : nat),
  length kept = length delta ->
  nth n (map (fun q : Z * Z => fst q + snd q) (combine kept delta)) 0
  = nth n kept 0 + nth n delta 0.
Proof.
  induction kept as [| x kept IH]; intros delta n Hlen.
  - destruct delta as [| y delta]; [| simpl in Hlen; discriminate].
    destruct n; simpl; reflexivity.
  - destruct delta as [| y delta]; simpl in Hlen; [discriminate |].
    simpl. destruct n as [| n]; simpl; [reflexivity |].
    apply IH. lia.
Qed.
Lemma Znth_map_combine__cfp_step_03 : forall (kept delta : list Z) (k : Z),
  Zlength delta = Zlength kept ->
  Znth k (map (fun q : Z * Z => fst q + snd q) (combine kept delta)) 0
  = Znth k kept 0 + Znth k delta 0.
Proof.
  intros kept delta k Hlen.
  unfold Znth.
  apply nth_map_combine__cfp_step_03.
  rewrite !Zlength_correct in Hlen. lia.
Qed.
Lemma Zlength_map_combine__cfp_step_03 : forall (kept delta : list Z),
  Zlength delta = Zlength kept ->
  Zlength (map (fun q : Z * Z => fst q + snd q) (combine kept delta)) = Zlength kept.
Proof.
  intros kept delta H.
  rewrite !Zlength_correct in H.
  rewrite !Zlength_correct.
  rewrite length_map, length_combine.
  lia.
Qed.
Lemma plan_elem_shift__cfp_step_03 :
  forall (a : list Z) (del change p m l r c j : Z),
    PartialPlanCost a del change p m l r c ->
    (0 <= j < l \/ r <= j < m) ->
    exists d, -1 <= d <= 1 /\ Z.divide p (Znth j a 0 + d).
Proof.
  intros a del change p m l r c j HP Hj.
  destruct HP as [Hl [Hlr [Hrm [Hma [delta [result [Hadj [Hdiv Hc]]]]]]]].
  destruct Hadj as [Hlen [Hdelta Hres]].
  assert (Hkl : Zlength (sublist 0 l a ++ sublist r m a) = l + (m - r)).
  { rewrite Zlength_app.
    rewrite (Zlength_sublist 0 l a) by lia.
    rewrite (Zlength_sublist r m a) by lia. lia. }
  assert (Hex : exists k, 0 <= k < l + (m - r) /\
                  Znth k (sublist 0 l a ++ sublist r m a) 0 = Znth j a 0).
  { destruct Hj as [Hj | Hj].
    - exists j. split; [lia |].
      rewrite app_Znth1 by (rewrite (Zlength_sublist 0 l a) by lia; lia).
      rewrite Znth_sublist0 by lia. reflexivity.
    - exists (l + (j - r)). split; [lia |].
      rewrite app_Znth2 by (rewrite (Zlength_sublist 0 l a) by lia; lia).
      rewrite (Zlength_sublist 0 l a) by lia.
      replace (l + (j - r) - l) with (j - r) by lia.
      rewrite Znth_sublist by lia.
      f_equal. lia. }
  destruct Hex as [k [Hk Hknth]].
  exists (Znth k delta 0).
  split.
  - assert (Hin : (fun d => d = (- 1) \/ d = 0 \/ d = 1) (Znth k delta 0)).
    { apply (Forall_Znth_Zlength _ delta 0 k Hdelta). lia. }
    simpl in Hin. lia.
  - rewrite <- Hknth.
    rewrite <- Znth_map_combine__cfp_step_03 by lia.
    rewrite <- Hres.
    apply (Forall_Znth_Zlength _ result 0 k Hdiv).
    rewrite Hres.
    rewrite Zlength_map_combine__cfp_step_03 by lia. lia.
Qed.
Lemma dpvalue_empty__cfp_step_03 : forall (S : Z -> Prop),
  (forall c, ~ S c) -> DPValue S INF.
Proof.
  intros S H. unfold DPValue, min_value_of_subset_with_default.
  right. split; [| reflexivity].
  intros c Hc. exfalso. apply (H c). exact Hc.
Qed.
Lemma dpvalue_lower__cfp_step_03 : forall (S : Z -> Prop) (v c : Z),
  DPValue S v -> S c -> v <= c.
Proof.
  intros S v c HD HS.
  destruct HD as [[[b [[Hin Hmin] Hb]] Hle] | [Hall Heq]].
  - cbn in Hb. subst b. apply Hmin. exact HS.
  - subst v. apply Hall. exact HS.
Qed.
Lemma dpvalue_attained__cfp_step_03 : forall (S : Z -> Prop) (v : Z),
  DPValue S v -> v <> INF -> S v.
Proof.
  intros S v HD Hne.
  destruct HD as [[[b [[Hin Hmin] Hb]] Hle] | [Hall Heq]].
  - cbn in Hb. subst b. exact Hin.
  - contradiction.
Qed.
Lemma dpvalue_intro__cfp_step_03 : forall (S : Z -> Prop) (v : Z),
  S v -> (forall c, S c -> v <= c) -> v <= INF -> DPValue S v.
Proof.
  intros S v Hv Hmin Hle.
  left. split; [| exact Hle].
  exists v. split; [split |].
  - exact Hv.
  - intros b Hb. cbn. apply Hmin. exact Hb.
  - reflexivity.
Qed.
Lemma dpvalue_unique__cfp_step_03 : forall (S : Z -> Prop) (v w : Z),
  DPValue S v -> DPValue S w -> v = w.
Proof.
  intros S v w H1 H2. unfold DPValue in H1, H2.
  exact (min_default_unique Z.le (fun x : Z => x) S INF v w H1 H2).
Qed.
Lemma dpvalue_finite_bound__cfp_step_03 : forall (S : Z -> Prop) (v B : Z),
  DPValue S v -> v <> INF -> (forall c, S c -> 0 <= c <= B) -> 0 <= v <= B.
Proof.
  intros S v B HD Hne HB.
  apply HB. apply dpvalue_attained__cfp_step_03; assumption.
Qed.
Lemma elem_cost_inf_no_shift__cfp_step_03 : forall (change p x d : Z),
  0 <= change < INF -> 2 <= p ->
  ElemCost change p x = INF ->
  -1 <= d <= 1 ->
  ~ Z.divide p (x + d).
Proof.
  intros change p x d Hch Hp HE Hd.
  unfold ElemCost in HE.
  destruct (Z.eqb (x mod p) 0) eqn:E0;
  destruct (Z.eqb ((x - 1) mod p) 0) eqn:E1;
  destruct (Z.eqb ((x + 1) mod p) 0) eqn:E2;
  cbn in HE; try (unfold INF in HE, Hch; lia).
  apply Z.eqb_neq in E0, E1, E2.
  assert (Hp0 : p <> 0) by lia.
  intros Hdiv.
  assert (Hcase : d = -1 \/ d = 0 \/ d = 1) by lia.
  destruct Hcase as [Hd1 | [Hd0 | Hd2]]; subst d.
  - apply E1. apply (proj2 (Z.mod_divide (x - 1) p Hp0)).
    replace (x - 1) with (x + -1) by lia. exact Hdiv.
  - apply E0. apply (proj2 (Z.mod_divide x p Hp0)).
    replace (x + 0) with x in Hdiv by lia. exact Hdiv.
  - apply E2. apply (proj2 (Z.mod_divide (x + 1) p Hp0)). exact Hdiv.
Qed.
Lemma dpcutfresh_charac__cfp_step_03 : forall (a : list Z) (del change p i c : Z),
  0 <= i <= Zlength a ->
  (DPCutFresh a del change p i c <-> c = i * del).
Proof.
  intros a del change p i c Hi.
  assert (Hk : sublist 0 0 a ++ sublist i i a = []).
  { rewrite (Zsublist_nil a 0 0) by lia. rewrite (Zsublist_nil a i i) by lia. reflexivity. }
  unfold DPCutFresh, PartialPlanCost, ChangeCost.
  split.
  - intros [_ [_ [_ [_ [delta [result [Hadj [Hdiv Hc]]]]]]]].
    destruct Hadj as [Hlen [Hd Hres]].
    rewrite Hk in Hlen.
    assert (Hz : Zlength delta = 0) by (rewrite Hlen; reflexivity).
    apply zlength_zero_nil__cfp_step_03 in Hz. subst delta.
    rewrite !count_nil__cfp_step_03 in Hc.
    replace (i - 0) with i in Hc by lia. lia.
  - intros Hc.
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    exists (@nil Z), (@nil Z).
    split; [| split].
    + unfold Adjusted. rewrite Hk.
      split; [reflexivity |]. split; [constructor |]. reflexivity.
    + constructor.
    + rewrite !count_nil__cfp_step_03.
      replace (i - 0) with i by lia. lia.
Qed.
Lemma dpcutfresh_value__cfp_step_03 : forall (a : list Z) (del change p i : Z),
  0 <= i <= Zlength a -> i * del <= INF ->
  DPValue (DPCutFresh a del change p i) (i * del).
Proof.
  intros a del change p i Hi Hb.
  apply dpvalue_intro__cfp_step_03.
  - apply (dpcutfresh_charac__cfp_step_03 a del change p i (i * del)); [lia | reflexivity].
  - intros c Hc.
    apply (proj1 (dpcutfresh_charac__cfp_step_03 a del change p i c Hi)) in Hc. lia.
  - exact Hb.
Qed.
Lemma plan_cost_bound__cfp_step_03 : forall (a : list Z) (del change p m l r c : Z),
  0 <= del -> 0 <= change ->
  PartialPlanCost a del change p m l r c ->
  0 <= c <= Zlength a * del + 2 * (Zlength a * change).
Proof.
  intros a del change p m l r c Hdel Hch HP.
  destruct HP as [Hl [Hlr [Hrm [Hma [delta [result [Hadj [Hdiv Hc]]]]]]]].
  destruct Hadj as [Hlen [Hd Hres]].
  assert (Hkl : Zlength (sublist 0 l a ++ sublist r m a) = l + (m - r)).
  { rewrite Zlength_app.
    rewrite (Zlength_sublist 0 l a) by lia.
    rewrite (Zlength_sublist r m a) by lia. lia. }
  rewrite Hkl in Hlen.
  pose proof (count_bounds__cfp_step_03 (-1) delta) as C1.
  pose proof (count_bounds__cfp_step_03 1 delta) as C2.
  unfold ChangeCost in Hc.
  assert (Ha : 0 <= Zlength a) by apply Zlength_nonneg.
  assert (H1 : (r - l) * del <= Zlength a * del) by nia.
  assert (H2 : Count (-1) delta * change <= Zlength a * change) by nia.
  assert (H3 : Count 1 delta * change <= Zlength a * change) by nia.
  assert (H4 : 0 <= (r - l) * del) by nia.
  assert (H5 : 0 <= Count (-1) delta * change) by nia.
  assert (H6 : 0 <= Count 1 delta * change) by nia.
  lia.
Qed.
Lemma cfp_state_finite_bound__cfp_step_03 :
  forall (a : list Z) (del change p i keep cutFresh cutAfterKeep after : Z),
    0 <= del -> 0 <= change ->
    CostForPrimeState a del change p i keep cutFresh cutAfterKeep after ->
    (keep <> INF -> 0 <= keep <= Zlength a * del + 2 * (Zlength a * change)) /\
    (cutFresh <> INF -> 0 <= cutFresh <= Zlength a * del + 2 * (Zlength a * change)) /\
    (cutAfterKeep <> INF -> 0 <= cutAfterKeep <= Zlength a * del + 2 * (Zlength a * change)) /\
    (after <> INF -> 0 <= after <= Zlength a * del + 2 * (Zlength a * change)).
Proof.
  intros a del change p i keep cutFresh cutAfterKeep after Hdel Hch HS.
  destruct HS as [HK [HF [HA HB]]].
  split; [| split; [| split]].
  - intros Hne. apply (dpvalue_finite_bound__cfp_step_03 _ _ _ HK Hne).
    intros c Hc. unfold DPKeep in Hc.
    apply (plan_cost_bound__cfp_step_03 a del change p i i i c); assumption.
  - intros Hne. apply (dpvalue_finite_bound__cfp_step_03 _ _ _ HF Hne).
    intros c Hc. unfold DPCutFresh in Hc.
    apply (plan_cost_bound__cfp_step_03 a del change p i 0 i c); assumption.
  - intros Hne. apply (dpvalue_finite_bound__cfp_step_03 _ _ _ HA Hne).
    intros c Hc. unfold DPCutAfterKeep in Hc. destruct Hc as [l [_ [_ Hc]]].
    apply (plan_cost_bound__cfp_step_03 a del change p i l i c); assumption.
  - intros Hne. apply (dpvalue_finite_bound__cfp_step_03 _ _ _ HB Hne).
    intros c Hc. unfold DPAfter in Hc. destruct Hc as [l [r [_ Hc]]].
    apply (plan_cost_bound__cfp_step_03 a del change p i l r c); assumption.
Qed.
Lemma ppc_shift_cut__cfp_step_03 :
  forall (a : list Z) (del change p i l c : Z),
    1 <= l <= i -> i + 1 <= Zlength a ->
    (PartialPlanCost a del change p (i + 1) l (i + 1) c <->
     PartialPlanCost a del change p i l i (c - del)).
Proof.
  intros a del change p i l c Hl Hi.
  assert (E1 : sublist (i + 1) (i + 1) a = []) by (apply Zsublist_nil; lia).
  assert (E2 : sublist i i a = []) by (apply Zsublist_nil; lia).
  assert (Hsh : (i + 1 - l) * del = (i - l) * del + del).
  { replace (i + 1 - l) with ((i - l) + 1) by lia.
    rewrite Z.mul_add_distr_r. lia. }
  unfold PartialPlanCost, ChangeCost.
  rewrite E1, E2.
  split.
  - intros [H1 [H2 [H3 [H4 [delta [result [Hadj [Hdiv Hc]]]]]]]].
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    exists delta, result. split; [exact Hadj | split; [exact Hdiv | lia]].
  - intros [H1 [H2 [H3 [H4 [delta [result [Hadj [Hdiv Hc]]]]]]]].
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    exists delta, result. split; [exact Hadj | split; [exact Hdiv | lia]].
Qed.
Lemma dpcutafterkeep_step__cfp_step_03 :
  forall (a : list Z) (del change p i keep cutAfterKeep : Z),
    0 < i -> i + 1 <= Zlength a -> 0 <= del ->
    DPValue (DPKeep a del change p i) keep ->
    DPValue (DPCutAfterKeep a del change p i) cutAfterKeep ->
    cutAfterKeep <> INF ->
    cutAfterKeep <= keep ->
    cutAfterKeep + del <= INF ->
    DPValue (DPCutAfterKeep a del change p (i + 1)) (cutAfterKeep + del).
Proof.
  intros a del change p i keep cutAfterKeep Hi Hia Hdel HK HA Hne Hle Hb.
  apply dpvalue_intro__cfp_step_03; [| | exact Hb].
  - pose proof (dpvalue_attained__cfp_step_03 _ _ HA Hne) as Hin.
    destruct Hin as [l [Hl1 [Hl2 Hppc]]].
    exists l. split; [lia | split; [lia |]].
    apply (proj2 (ppc_shift_cut__cfp_step_03 a del change p i l (cutAfterKeep + del)
                    ltac:(lia) Hia)).
    replace (cutAfterKeep + del - del) with cutAfterKeep by lia.
    exact Hppc.
  - intros c Hc.
    destruct Hc as [l [Hl1 [Hl2 Hppc]]].
    apply (proj1 (ppc_shift_cut__cfp_step_03 a del change p i l c ltac:(lia) Hia)) in Hppc.
    destruct (Z.eq_dec l i) as [Hli | Hli].
    + subst l.
      pose proof (dpvalue_lower__cfp_step_03 _ _ _ HK Hppc). lia.
    + assert (Hmem : DPCutAfterKeep a del change p i (c - del)).
      { exists l. split; [lia | split; [lia | exact Hppc]]. }
      pose proof (dpvalue_lower__cfp_step_03 _ _ _ HA Hmem). lia.
Qed.
Lemma dpkeep_next_empty__cfp_step_03 :
  forall (a : list Z) (del change p i : Z),
    0 <= change < INF -> 2 <= p -> 0 <= i -> i + 1 <= Zlength a ->
    ElemCost change p (Znth i a 0) = INF ->
    DPValue (DPKeep a del change p (i + 1)) INF.
Proof.
  intros a del change p i Hch Hp Hi Hia HE.
  apply dpvalue_empty__cfp_step_03. intros c HC.
  unfold DPKeep in HC.
  assert (Hj : 0 <= i < i + 1 \/ i + 1 <= i < i + 1) by lia.
  destruct (plan_elem_shift__cfp_step_03 a del change p (i + 1) (i + 1) (i + 1) c i HC Hj)
    as [d [Hd Hdiv]].
  exact (elem_cost_inf_no_shift__cfp_step_03 change p (Znth i a 0) d Hch Hp HE Hd Hdiv).
Qed.
Lemma dpafter_next_empty__cfp_step_03 :
  forall (a : list Z) (del change p i : Z),
    0 <= change < INF -> 2 <= p -> 0 <= i -> i + 1 <= Zlength a ->
    ElemCost change p (Znth i a 0) = INF ->
    DPValue (DPAfter a del change p (i + 1)) INF.
Proof.
  intros a del change p i Hch Hp Hi Hia HE.
  apply dpvalue_empty__cfp_step_03. intros c HC.
  unfold DPAfter in HC.
  destruct HC as [l [r [Hr HC]]].
  assert (Hj : 0 <= i < l \/ r <= i < i + 1) by lia.
  destruct (plan_elem_shift__cfp_step_03 a del change p (i + 1) l r c i HC Hj)
    as [d [Hd Hdiv]].
  exact (elem_cost_inf_no_shift__cfp_step_03 change p (Znth i a 0) d Hch Hp HE Hd Hdiv).
Qed.
Lemma dpcutafterkeep_zero__cfp_step_03 : forall (a : list Z) (del change p : Z),
  DPValue (DPCutAfterKeep a del change p 0) INF.
Proof.
  intros a del change p.
  apply dpvalue_empty__cfp_step_03. intros c [l [H1 [H2 _]]]. lia.
Qed.
Lemma cfp_state_step__cfp_step_03 :
  forall (a : list Z) (del change p i keep cutFresh cutAfterKeep after : Z),
    0 <= del -> 0 <= change < INF -> 2 <= p ->
    0 < i -> i + 1 <= Zlength a ->
    ElemCost change p (Znth i a 0) = INF ->
    CostForPrimeState a del change p i keep cutFresh cutAfterKeep after ->
    cutFresh <> INF ->
    cutAfterKeep <> INF ->
    cutAfterKeep <= keep ->
    cutFresh + del <= INF ->
    cutAfterKeep + del <= INF ->
    CostForPrimeState a del change p (i + 1) INF (cutFresh + del)
      (cutAfterKeep + del) INF.
Proof.
  intros a del change p i keep cutFresh cutAfterKeep after
         Hdel Hch Hp Hi Hia HE HS Hcfne Hakne Hle Hbf Hba.
  destruct HS as [HK [HF [HA HB]]].
  assert (Hib : 0 <= i <= Zlength a) by lia.
  assert (Hib1 : 0 <= i + 1 <= Zlength a) by lia.
  assert (Hcf : cutFresh = i * del).
  { apply (proj1 (dpcutfresh_charac__cfp_step_03 a del change p i cutFresh Hib)).
    apply dpvalue_attained__cfp_step_03; assumption. }
  assert (Hnext : (i + 1) * del = cutFresh + del).
  { rewrite Hcf, Z.mul_add_distr_r. lia. }
  split; [| split; [| split]].
  - apply dpkeep_next_empty__cfp_step_03 with (del := del);
      solve [assumption | lia].
  - rewrite <- Hnext.
    apply dpcutfresh_value__cfp_step_03; [lia | rewrite Hnext; exact Hbf].
  - apply (dpcutafterkeep_step__cfp_step_03 a del change p i keep cutAfterKeep);
      solve [assumption | lia].
  - apply dpafter_next_empty__cfp_step_03 with (del := del);
      solve [assumption | lia].
Qed.
Lemma cfp_state_zero_cak_inf__cfp_step_03 :
  forall (a : list Z) (del change p keep cutFresh cutAfterKeep after : Z),
    CostForPrimeState a del change p 0 keep cutFresh cutAfterKeep after ->
    cutAfterKeep = INF.
Proof.
  intros a del change p keep cutFresh cutAfterKeep after HS.
  destruct HS as [_ [_ [HA _]]].
  exact (dpvalue_unique__cfp_step_03 _ _ _ HA
           (dpcutafterkeep_zero__cfp_step_03 a del change p)).
Qed.
Lemma count_as_sum__cfp_step_04 :
  forall (x : Z) (xs : list Z),
    Count x xs =
    SumLib.Sum.sum (fun k : Z => 0 <= k < Zlength xs)
      (fun k => if prop_dec (Znth k xs 0 = x) then 1 else 0).
Proof.
  intros x xs.
  unfold Count, set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall ks : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun k => if prop_dec (Znth k xs 0 = x) then true else false) ks) =
    fold_right (fun k acc : Z =>
      (if prop_dec (Znth k xs 0 = x) then 1 else 0) + acc) 0 ks).
  {
    induction ks as [|k ks IH]; simpl; [reflexivity |].
    destruct (prop_dec (Znth k xs 0 = x)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma count_bounds__cfp_step_04 :
  forall (x : Z) (xs : list Z), 0 <= Count x xs <= Zlength xs.
Proof.
  intros x xs.
  pose proof Zlength_nonneg xs as Hlen.
  rewrite count_as_sum__cfp_step_04.
  pose proof SumLib.ZRange.sum_Z_range_bounds 0 (Zlength xs)
    (fun k => if prop_dec (Znth k xs 0 = x) then 1 else 0) 0 1
    ltac:(lia)
    ltac:(intros k Hk; cbv beta; destruct (prop_dec (Znth k xs 0 = x)); lia) as Hb.
  lia.
Qed.
Lemma count_ext__cfp_step_04 :
  forall (x : Z) (xs ys : list Z),
    Zlength xs = Zlength ys ->
    (forall k, 0 <= k < Zlength xs -> Znth k xs 0 = Znth k ys 0) ->
    Count x xs = Count x ys.
Proof.
  intros x xs ys Hlen Hnth.
  rewrite !count_as_sum__cfp_step_04.
  rewrite <- Hlen.
  apply SumLib.ZRange.sum_Z_range_ext.
  intros k Hk.
  rewrite (Hnth k Hk).
  reflexivity.
Qed.
Lemma count_app_single__cfp_step_04 :
  forall (x : Z) (xs : list Z) (d : Z),
    Count x (xs ++ [d]) = Count x xs + (if prop_dec (d = x) then 1 else 0).
Proof.
  intros x xs d.
  pose proof Zlength_nonneg xs as Hnn.
  assert (Hlen : Zlength (xs ++ [d]) = Zlength xs + 1).
  { rewrite Zlength_app. rewrite Zlength_cons, Zlength_nil. lia. }
  rewrite !count_as_sum__cfp_step_04.
  rewrite Hlen.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by lia.
  f_equal.
  - apply SumLib.ZRange.sum_Z_range_ext.
    intros k Hk.
    rewrite (app_Znth1 0 xs [d] k ltac:(lia)).
    reflexivity.
  - rewrite (app_Znth2 0 xs [d] (Zlength xs) ltac:(lia)).
    replace (Zlength xs - Zlength xs) with 0 by lia.
    rewrite Znth0_cons.
    reflexivity.
Qed.
Lemma combine_app__cfp_step_04 :
  forall (l1 m1 l2 m2 : list Z),
    length l1 = length m1 ->
    combine (l1 ++ l2) (m1 ++ m2) = combine l1 m1 ++ combine l2 m2.
Proof.
  induction l1 as [|a l1 IH]; intros m1 l2 m2 Hlen.
  - destruct m1; simpl in *; [reflexivity | discriminate].
  - destruct m1 as [|b m1]; simpl in *; [discriminate |].
    rewrite IH by lia.
    reflexivity.
Qed.
Lemma zlength_length__cfp_step_04 :
  forall (l m : list Z), Zlength l = Zlength m -> length l = length m.
Proof.
  intros l m H.
  rewrite !Zlength_correct in H.
  lia.
Qed.
Lemma adjusted_app_single__cfp_step_04 :
  forall (kept delta result : list Z) (y dd : Z),
    Adjusted kept delta result ->
    (dd = -1 \/ dd = 0 \/ dd = 1) ->
    Adjusted (kept ++ [y]) (delta ++ [dd]) (result ++ [y + dd]).
Proof.
  intros kept delta result y dd [Hlen [Hall Hres]] Hdd.
  unfold Adjusted.
  split; [| split].
  - rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. lia.
  - apply Forall_app. split; [exact Hall |].
    constructor; [exact Hdd | constructor].
  - rewrite (combine_app__cfp_step_04 kept delta [y] [dd])
      by (apply zlength_length__cfp_step_04; lia).
    rewrite map_app.
    rewrite <- Hres.
    reflexivity.
Qed.
Lemma adjusted_snoc_inv__cfp_step_04 :
  forall (kept delta result : list Z) (y : Z),
    Adjusted (kept ++ [y]) delta result ->
    exists (delta' result' : list Z) (dd : Z),
      delta = delta' ++ [dd] /\
      result = result' ++ [y + dd] /\
      (dd = -1 \/ dd = 0 \/ dd = 1) /\
      Adjusted kept delta' result'.
Proof.
  intros kept delta result y [Hlen [Hall Hres]].
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen.
  pose proof Zlength_nonneg kept as Hk.
  destruct (list_snoc_destruct delta) as [Hnil | [dd [delta' Hsnoc]]].
  - subst delta. rewrite Zlength_nil in Hlen. lia.
  - subst delta.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen.
    apply Forall_app in Hall.
    destruct Hall as [Hall' Hdd].
    pose proof (Forall_inv Hdd) as Hdd0.
    exists delta', (map (fun q : Z * Z => fst q + snd q) (combine kept delta')), dd.
    assert (Hadj : Adjusted kept delta' (map (fun q : Z * Z => fst q + snd q) (combine kept delta'))).
    { unfold Adjusted. split; [lia | split; [exact Hall' | reflexivity]]. }
    split; [reflexivity | split; [| split; [exact Hdd0 | exact Hadj]]].
    rewrite Hres.
    rewrite (combine_app__cfp_step_04 kept delta' [y] [dd])
      by (apply zlength_length__cfp_step_04; lia).
    rewrite map_app.
    reflexivity.
Qed.
Lemma changecost_snoc__cfp_step_04 :
  forall (del change l r : Z) (delta : list Z) (dd : Z),
    (dd = -1 \/ dd = 0 \/ dd = 1) ->
    ChangeCost del change l r (delta ++ [dd]) =
    ChangeCost del change l r delta + (if Z.eq_dec dd 0 then 0 else change).
Proof.
  intros del change l r delta dd Hdd.
  unfold ChangeCost.
  rewrite !count_app_single__cfp_step_04.
  destruct Hdd as [Hd | [Hd | Hd]]; subst dd;
    repeat (match goal with
            | |- context [prop_dec ?P] => destruct (prop_dec P)
            | |- context [Z.eq_dec ?u ?v] => destruct (Z.eq_dec u v)
            end); try lia.
Qed.
Lemma changecost_cut__cfp_step_04 :
  forall (del change l r : Z) (delta : list Z),
    ChangeCost del change l (r + 1) delta =
    ChangeCost del change l r delta + del.
Proof.
  intros. unfold ChangeCost. lia.
Qed.
Lemma sublist_snoc__cfp_step_04 :
  forall (a : list Z) (r i : Z),
    0 <= r -> r <= i -> i < Zlength a ->
    sublist r (i + 1) a = sublist r i a ++ [Znth i a 0].
Proof.
  intros a r i Hr Hri Hi.
  rewrite (sublist_split r (i + 1) i a) by lia.
  rewrite (sublist_single 0 i a) by lia.
  reflexivity.
Qed.
Lemma plan_extend_keep__cfp_step_04 :
  forall (a : list Z) (del change p i l r c0 dd : Z),
    0 <= i < Zlength a ->
    r <= i ->
    PartialPlanCost a del change p i l r c0 ->
    (dd = -1 \/ dd = 0 \/ dd = 1) ->
    Z.divide p (Znth i a 0 + dd) ->
    PartialPlanCost a del change p (i + 1) l r
      (c0 + (if Z.eq_dec dd 0 then 0 else change)).
Proof.
  intros a del change p i l r c0 dd Hi Hri Hplan Hdd Hdiv.
  destruct Hplan as [Hl [Hlr [Hr [Hia [delta [result [Hadj [Hall Hc]]]]]]]].
  unfold PartialPlanCost.
  split; [lia | split; [lia | split; [lia | split; [lia |]]]].
  exists (delta ++ [dd]), (result ++ [Znth i a 0 + dd]).
  split; [| split].
  - rewrite (sublist_snoc__cfp_step_04 a r i) by lia.
    rewrite app_assoc.
    apply adjusted_app_single__cfp_step_04; assumption.
  - apply Forall_app. split; [exact Hall |].
    constructor; [exact Hdiv | constructor].
  - rewrite changecost_snoc__cfp_step_04 by assumption.
    lia.
Qed.
Lemma plan_shrink_keep__cfp_step_04 :
  forall (a : list Z) (del change p i l r c : Z),
    0 <= i < Zlength a ->
    r <= i ->
    PartialPlanCost a del change p (i + 1) l r c ->
    exists c0 dd,
      PartialPlanCost a del change p i l r c0 /\
      (dd = -1 \/ dd = 0 \/ dd = 1) /\
      Z.divide p (Znth i a 0 + dd) /\
      c = c0 + (if Z.eq_dec dd 0 then 0 else change).
Proof.
  intros a del change p i l r c Hi Hri Hplan.
  destruct Hplan as [Hl [Hlr [Hr [Hia [delta [result [Hadj [Hall Hc]]]]]]]].
  rewrite (sublist_snoc__cfp_step_04 a r i) in Hadj by lia.
  rewrite app_assoc in Hadj.
  destruct (adjusted_snoc_inv__cfp_step_04 _ _ _ _ Hadj)
    as [delta' [result' [dd [Hde [Hre [Hdd Hadj']]]]]].
  exists (ChangeCost del change l r delta'), dd.
  split; [| split; [exact Hdd | split]].
  - unfold PartialPlanCost.
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    exists delta', result'.
    split; [exact Hadj' | split; [| reflexivity]].
    rewrite Hre in Hall.
    apply Forall_app in Hall. tauto.
  - rewrite Hre in Hall.
    apply Forall_app in Hall.
    destruct Hall as [_ Hlast].
    exact (Forall_inv Hlast).
  - subst c. rewrite Hde.
    rewrite changecost_snoc__cfp_step_04 by assumption.
    reflexivity.
Qed.
Lemma plan_extend_cut__cfp_step_04 :
  forall (a : list Z) (del change p i l c0 : Z),
    0 <= i < Zlength a ->
    l <= i ->
    PartialPlanCost a del change p i l i c0 ->
    PartialPlanCost a del change p (i + 1) l (i + 1) (c0 + del).
Proof.
  intros a del change p i l c0 Hi Hli Hplan.
  destruct Hplan as [Hl [Hlr [Hr [Hia [delta [result [Hadj [Hall Hc]]]]]]]].
  rewrite (Zsublist_nil a i i ltac:(lia)) in Hadj.
  unfold PartialPlanCost.
  split; [lia | split; [lia | split; [lia | split; [lia |]]]].
  exists delta, result.
  rewrite (Zsublist_nil a (i + 1) (i + 1) ltac:(lia)).
  split; [exact Hadj | split; [exact Hall |]].
  subst c0. rewrite changecost_cut__cfp_step_04. reflexivity.
Qed.
Lemma plan_shrink_cut__cfp_step_04 :
  forall (a : list Z) (del change p i l c : Z),
    0 <= i < Zlength a ->
    l <= i ->
    PartialPlanCost a del change p (i + 1) l (i + 1) c ->
    exists c0, PartialPlanCost a del change p i l i c0 /\ c = c0 + del.
Proof.
  intros a del change p i l c Hi Hli Hplan.
  destruct Hplan as [Hl [Hlr [Hr [Hia [delta [result [Hadj [Hall Hc]]]]]]]].
  rewrite (Zsublist_nil a (i + 1) (i + 1) ltac:(lia)) in Hadj.
  exists (ChangeCost del change l i delta).
  split.
  - unfold PartialPlanCost.
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    exists delta, result.
    rewrite (Zsublist_nil a i i ltac:(lia)).
    split; [exact Hadj | split; [exact Hall | reflexivity]].
  - subst c. rewrite changecost_cut__cfp_step_04. reflexivity.
Qed.
Lemma dpvalue_le_mem__cfp_step_04 :
  forall (S : Z -> Prop) (v c : Z), DPValue S v -> S c -> v <= c.
Proof.
  intros S v c HD Hc.
  unfold DPValue, min_value_of_subset_with_default, min_value_of_subset,
    min_object_of_subset in HD.
  destruct HD as [[[b [[Hb Hmin] Heq]] Hle] | [Hall Heq]].
  - subst v. apply Hmin. exact Hc.
  - subst v. apply Hall. exact Hc.
Qed.
Lemma dpvalue_mem__cfp_step_04 :
  forall (S : Z -> Prop) (v : Z), DPValue S v -> v <> INF -> S v.
Proof.
  intros S v HD Hne.
  unfold DPValue, min_value_of_subset_with_default, min_value_of_subset,
    min_object_of_subset in HD.
  destruct HD as [[[b [[Hb Hmin] Heq]] Hle] | [Hall Heq]].
  - subst v. exact Hb.
  - contradiction.
Qed.
Lemma dpvalue_le_inf__cfp_step_04 :
  forall (S : Z -> Prop) (v : Z), DPValue S v -> v <= INF.
Proof.
  intros S v HD.
  unfold DPValue, min_value_of_subset_with_default in HD.
  destruct HD as [[_ Hle] | [_ Heq]]; [exact Hle | subst v; apply Z.le_refl].
Qed.
Lemma dpvalue_nonneg__cfp_step_04 :
  forall (S : Z -> Prop) (v : Z),
    (forall c, S c -> 0 <= c) -> DPValue S v -> 0 <= v.
Proof.
  intros S v Hnn HD.
  destruct (Z.eq_dec v INF) as [He | He].
  - subst v. unfold INF. lia.
  - apply Hnn. apply dpvalue_mem__cfp_step_04; assumption.
Qed.
Lemma dpvalue_shift__cfp_step_04 :
  forall (S' : Z -> Prop) (base shift v : Z),
    (forall c, S' c -> base + shift <= c) ->
    (base + shift < INF -> S' (base + shift)) ->
    (base + shift <= INF -> v = base + shift) ->
    (INF <= base + shift -> v = INF) ->
    DPValue S' v.
Proof.
  intros S' base shift v Hlow Hmem Hfin Hsat.
  unfold DPValue, min_value_of_subset_with_default, min_value_of_subset,
    min_object_of_subset.
  destruct (Z_lt_le_dec (base + shift) INF) as [Hlt | Hge].
  - left.
    rewrite (Hfin ltac:(lia)).
    split; [| lia].
    exists (base + shift).
    split; [split | reflexivity].
    + apply Hmem. exact Hlt.
    + intros b Hb. apply Hlow. exact Hb.
  - right.
    split.
    + intros c Hc. pose proof Hlow c Hc. lia.
    + apply Hsat. exact Hge.
Qed.
Lemma elemcost_cases__cfp_step_04 :
  forall (change p x : Z),
    ElemCost change p x = 0 \/ ElemCost change p x = change \/
    ElemCost change p x = INF.
Proof.
  intros change p x. unfold ElemCost.
  destruct (Z.eqb (x mod p) 0); [left; reflexivity |].
  destruct (orb (Z.eqb ((x - 1) mod p) 0) (Z.eqb ((x + 1) mod p) 0));
    [right; left; reflexivity | right; right; reflexivity].
Qed.
Lemma elemcost_nonneg__cfp_step_04 :
  forall (change p x : Z), 0 <= change -> 0 <= ElemCost change p x.
Proof.
  intros change p x Hc.
  destruct (elemcost_cases__cfp_step_04 change p x) as [H | [H | H]];
    rewrite H; unfold INF; lia.
Qed.
Lemma elemcost_witness__cfp_step_04 :
  forall (change p x : Z),
    2 <= p ->
    ElemCost change p x <> INF ->
    exists dd, (dd = -1 \/ dd = 0 \/ dd = 1) /\ Z.divide p (x + dd) /\
      ElemCost change p x = (if Z.eq_dec dd 0 then 0 else change).
Proof.
  intros change p x Hp Hne.
  assert (Hp0 : p <> 0) by lia.
  unfold ElemCost in *.
  destruct (Z.eqb_spec (x mod p) 0) as [H0 | H0].
  - exists 0. split; [right; left; reflexivity | split].
    + replace (x + 0) with x by lia.
      apply (proj1 (Z.mod_divide x p Hp0)). exact H0.
    + destruct (Z.eq_dec 0 0); [reflexivity | contradiction].
  - destruct (Z.eqb_spec ((x - 1) mod p) 0) as [H1 | H1]; simpl in *.
    + exists (-1). split; [left; reflexivity | split].
      * replace (x + -1) with (x - 1) by lia.
        apply (proj1 (Z.mod_divide (x - 1) p Hp0)). exact H1.
      * destruct (Z.eq_dec (-1) 0); [discriminate | reflexivity].
    + destruct (Z.eqb_spec ((x + 1) mod p) 0) as [H2 | H2]; simpl in *.
      * exists 1. split; [right; right; reflexivity | split].
        -- apply (proj1 (Z.mod_divide (x + 1) p Hp0)). exact H2.
        -- destruct (Z.eq_dec 1 0); [discriminate | reflexivity].
      * contradiction.
Qed.
Lemma elemcost_min__cfp_step_04 :
  forall (change p x dd : Z),
    2 <= p -> 0 <= change ->
    (dd = -1 \/ dd = 0 \/ dd = 1) ->
    Z.divide p (x + dd) ->
    ElemCost change p x <= (if Z.eq_dec dd 0 then 0 else change).
Proof.
  intros change p x dd Hp Hch Hdd Hdiv.
  assert (Hp0 : p <> 0) by lia.
  unfold ElemCost.
  destruct Hdd as [Hd | [Hd | Hd]]; subst dd.
  - assert (H1 : (x - 1) mod p = 0).
    { apply (proj2 (Z.mod_divide (x - 1) p Hp0)).
      replace (x - 1) with (x + -1) by lia. exact Hdiv. }
    destruct (Z.eq_dec (-1) 0); [discriminate |].
    destruct (Z.eqb_spec (x mod p) 0); [lia |].
    rewrite H1. simpl. lia.
  - assert (H0 : x mod p = 0).
    { apply (proj2 (Z.mod_divide x p Hp0)).
      replace x with (x + 0) by lia. exact Hdiv. }
    destruct (Z.eq_dec 0 0); [| contradiction].
    rewrite H0. simpl. lia.
  - assert (H1 : (x + 1) mod p = 0).
    { apply (proj2 (Z.mod_divide (x + 1) p Hp0)). exact Hdiv. }
    destruct (Z.eq_dec 1 0); [discriminate |].
    destruct (Z.eqb_spec (x mod p) 0); [lia |].
    rewrite H1. rewrite Bool.orb_true_r. lia.
Qed.
Lemma plan_bounds__cfp_step_04 :
  forall (a : list Z) (del change p i l r c : Z),
    0 <= del -> 0 <= change ->
    PartialPlanCost a del change p i l r c ->
    0 <= c /\ c <= Zlength a * del + 2 * (Zlength a * change).
Proof.
  intros a del change p i l r c Hdel Hch Hplan.
  destruct Hplan as [Hl [Hlr [Hr [Hia [delta [result [Hadj [Hall Hc]]]]]]]].
  destruct Hadj as [Hlen _].
  rewrite Zlength_app in Hlen.
  rewrite (Zlength_sublist 0 l a ltac:(lia)) in Hlen.
  rewrite (Zlength_sublist r i a ltac:(lia)) in Hlen.
  pose proof count_bounds__cfp_step_04 (-1) delta as Hc1.
  pose proof count_bounds__cfp_step_04 1 delta as Hc2.
  subst c. unfold ChangeCost.
  split; nia.
Qed.
Lemma plan_keep_extend__cfp_step_04 :
  forall (a : list Z) (del change p i c0 dd : Z),
    0 <= i < Zlength a ->
    PartialPlanCost a del change p i i i c0 ->
    (dd = -1 \/ dd = 0 \/ dd = 1) ->
    Z.divide p (Znth i a 0 + dd) ->
    PartialPlanCost a del change p (i + 1) (i + 1) (i + 1)
      (c0 + (if Z.eq_dec dd 0 then 0 else change)).
Proof.
  intros a del change p i c0 dd Hi Hplan Hdd Hdiv.
  destruct Hplan as [Hl [Hlr [Hr [Hia [delta [result [Hadj [Hall Hc]]]]]]]].
  rewrite (Zsublist_nil a i i ltac:(lia)), app_nil_r in Hadj.
  unfold PartialPlanCost.
  split; [lia | split; [lia | split; [lia | split; [lia |]]]].
  exists (delta ++ [dd]), (result ++ [Znth i a 0 + dd]).
  rewrite (Zsublist_nil a (i + 1) (i + 1) ltac:(lia)), app_nil_r.
  rewrite (sublist_snoc__cfp_step_04 a 0 i) by lia.
  split; [| split].
  - apply adjusted_app_single__cfp_step_04; assumption.
  - apply Forall_app. split; [exact Hall |].
    constructor; [exact Hdiv | constructor].
  - rewrite changecost_snoc__cfp_step_04 by assumption.
    subst c0. unfold ChangeCost.
    replace (i + 1 - (i + 1)) with (i - i) by lia.
    lia.
Qed.
Lemma plan_keep_shrink__cfp_step_04 :
  forall (a : list Z) (del change p i c : Z),
    0 <= i < Zlength a ->
    PartialPlanCost a del change p (i + 1) (i + 1) (i + 1) c ->
    exists c0 dd,
      PartialPlanCost a del change p i i i c0 /\
      (dd = -1 \/ dd = 0 \/ dd = 1) /\
      Z.divide p (Znth i a 0 + dd) /\
      c = c0 + (if Z.eq_dec dd 0 then 0 else change).
Proof.
  intros a del change p i c Hi Hplan.
  destruct Hplan as [Hl [Hlr [Hr [Hia [delta [result [Hadj [Hall Hc]]]]]]]].
  rewrite (Zsublist_nil a (i + 1) (i + 1) ltac:(lia)), app_nil_r in Hadj.
  rewrite (sublist_snoc__cfp_step_04 a 0 i) in Hadj by lia.
  destruct (adjusted_snoc_inv__cfp_step_04 _ _ _ _ Hadj)
    as [delta' [result' [dd [Hde [Hre [Hdd Hadj']]]]]].
  exists (ChangeCost del change i i delta'), dd.
  split; [| split; [exact Hdd | split]].
  - unfold PartialPlanCost.
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    exists delta', result'.
    rewrite (Zsublist_nil a i i ltac:(lia)), app_nil_r.
    split; [exact Hadj' | split; [| reflexivity]].
    rewrite Hre in Hall.
    apply Forall_app in Hall. tauto.
  - rewrite Hre in Hall.
    apply Forall_app in Hall.
    destruct Hall as [_ Hlast].
    exact (Forall_inv Hlast).
  - subst c. rewrite Hde.
    rewrite changecost_snoc__cfp_step_04 by assumption.
    unfold ChangeCost.
    replace (i + 1 - (i + 1)) with (i - i) by lia.
    lia.
Qed.
Lemma dpkeep_sub_dpafter__cfp_step_04 :
  forall (a : list Z) (del change p i c : Z),
    1 <= i ->
    DPKeep a del change p i c ->
    DPAfter a del change p i c.
Proof.
  intros a del change p i c Hi Hkeep.
  unfold DPAfter.
  exists (i - 1), (i - 1).
  split; [lia |].
  destruct Hkeep as [Hl [Hlr [Hr [Hia [delta [result [Hadj [Hall Hc]]]]]]]].
  rewrite (Zsublist_nil a i i ltac:(lia)), app_nil_r in Hadj.
  unfold PartialPlanCost.
  split; [lia | split; [lia | split; [lia | split; [lia |]]]].
  exists delta, result.
  rewrite <- (sublist_split 0 i (i - 1) a) by lia.
  split; [exact Hadj | split; [exact Hall |]].
  subst c. unfold ChangeCost.
  replace (i - 1 - (i - 1)) with (i - i) by lia.
  lia.
Qed.
Lemma dpkeep_nonneg__cfp_step_04 :
  forall (a : list Z) (del change p i c : Z),
    0 <= del -> 0 <= change -> DPKeep a del change p i c -> 0 <= c.
Proof.
  intros a del change p i c Hd Hc H.
  destruct (plan_bounds__cfp_step_04 a del change p i i i c Hd Hc H). lia.
Qed.
Lemma dpcutfresh_nonneg__cfp_step_04 :
  forall (a : list Z) (del change p i c : Z),
    0 <= del -> 0 <= change -> DPCutFresh a del change p i c -> 0 <= c.
Proof.
  intros a del change p i c Hd Hc H.
  destruct (plan_bounds__cfp_step_04 a del change p i 0 i c Hd Hc H). lia.
Qed.
Lemma dpcutafterkeep_nonneg__cfp_step_04 :
  forall (a : list Z) (del change p i c : Z),
    0 <= del -> 0 <= change -> DPCutAfterKeep a del change p i c -> 0 <= c.
Proof.
  intros a del change p i c Hd Hc [l [_ [_ H]]].
  destruct (plan_bounds__cfp_step_04 a del change p i l i c Hd Hc H). lia.
Qed.
Lemma dpafter_nonneg__cfp_step_04 :
  forall (a : list Z) (del change p i c : Z),
    0 <= del -> 0 <= change -> DPAfter a del change p i c -> 0 <= c.
Proof.
  intros a del change p i c Hd Hc [l [r [_ H]]].
  destruct (plan_bounds__cfp_step_04 a del change p i l r c Hd Hc H). lia.
Qed.
Lemma dp_keep_step__cfp_step_04 :
  forall (a : list Z) (del change p i keep cost v : Z),
    0 <= del -> 0 <= change -> 2 <= p -> 0 <= i < Zlength a ->
    cost = ElemCost change p (Znth i a 0) ->
    DPValue (DPKeep a del change p i) keep ->
    (keep + cost <= INF -> v = keep + cost) ->
    (INF <= keep + cost -> v = INF) ->
    DPValue (DPKeep a del change p (i + 1)) v.
Proof.
  intros a del change p i keep cost v Hdel Hch Hp Hi Hcost HD Hfin Hsat.
  assert (Hkn : 0 <= keep).
  { apply (dpvalue_nonneg__cfp_step_04 _ _
      (fun c H => dpkeep_nonneg__cfp_step_04 a del change p i c Hdel Hch H) HD). }
  pose proof elemcost_nonneg__cfp_step_04 change p (Znth i a 0) Hch as Hcn.
  apply (dpvalue_shift__cfp_step_04 _ keep cost v).
  - intros c Hc.
    destruct (plan_keep_shrink__cfp_step_04 a del change p i c Hi Hc)
      as [c0 [dd [Hp0 [Hdd [Hdiv Hce]]]]].
    pose proof dpvalue_le_mem__cfp_step_04 _ _ _ HD Hp0 as Hk0.
    pose proof elemcost_min__cfp_step_04 change p (Znth i a 0) dd Hp Hch Hdd Hdiv as Hm.
    subst cost. lia.
  - intros Hlt.
    assert (Hkne : keep <> INF) by lia.
    assert (Hcne : ElemCost change p (Znth i a 0) <> INF) by lia.
    destruct (elemcost_witness__cfp_step_04 change p (Znth i a 0) Hp Hcne)
      as [dd [Hdd [Hdiv Heq]]].
    pose proof dpvalue_mem__cfp_step_04 _ _ HD Hkne as Hmem.
    pose proof plan_keep_extend__cfp_step_04 a del change p i keep dd Hi Hmem Hdd Hdiv as Hres.
    subst cost. rewrite Heq. exact Hres.
  - exact Hfin.
  - exact Hsat.
Qed.
Lemma dp_cutfresh_step__cfp_step_04 :
  forall (a : list Z) (del change p i cutFresh v : Z),
    0 <= del -> 0 <= change -> 0 <= i < Zlength a ->
    DPValue (DPCutFresh a del change p i) cutFresh ->
    (cutFresh + del <= INF -> v = cutFresh + del) ->
    (INF <= cutFresh + del -> v = INF) ->
    DPValue (DPCutFresh a del change p (i + 1)) v.
Proof.
  intros a del change p i cutFresh v Hdel Hch Hi HD Hfin Hsat.
  assert (Hkn : 0 <= cutFresh).
  { apply (dpvalue_nonneg__cfp_step_04 _ _
      (fun c H => dpcutfresh_nonneg__cfp_step_04 a del change p i c Hdel Hch H) HD). }
  apply (dpvalue_shift__cfp_step_04 _ cutFresh del v).
  - intros c Hc.
    destruct (plan_shrink_cut__cfp_step_04 a del change p i 0 c Hi ltac:(lia) Hc)
      as [c0 [Hp0 Hce]].
    pose proof dpvalue_le_mem__cfp_step_04 _ _ _ HD Hp0. lia.
  - intros Hlt.
    assert (Hkne : cutFresh <> INF) by lia.
    pose proof dpvalue_mem__cfp_step_04 _ _ HD Hkne as Hmem.
    exact (plan_extend_cut__cfp_step_04 a del change p i 0 cutFresh Hi ltac:(lia) Hmem).
  - exact Hfin.
  - exact Hsat.
Qed.
Lemma dp_cutafterkeep_step__cfp_step_04 :
  forall (a : list Z) (del change p i keep cutAfterKeep m v : Z),
    0 <= del -> 0 <= change -> 0 <= i < Zlength a ->
    DPValue (DPKeep a del change p i) keep ->
    DPValue (DPCutAfterKeep a del change p i) cutAfterKeep ->
    (i > 0 -> m = Z.min keep cutAfterKeep) ->
    (i <= 0 -> m = cutAfterKeep) ->
    (m + del <= INF -> v = m + del) ->
    (INF <= m + del -> v = INF) ->
    DPValue (DPCutAfterKeep a del change p (i + 1)) v.
Proof.
  intros a del change p i keep cutAfterKeep m v Hdel Hch Hi HK HC Hpos Hzero Hfin Hsat.
  assert (Hkn : 0 <= keep).
  { apply (dpvalue_nonneg__cfp_step_04 _ _
      (fun c H => dpkeep_nonneg__cfp_step_04 a del change p i c Hdel Hch H) HK). }
  assert (Hcn : 0 <= cutAfterKeep).
  { apply (dpvalue_nonneg__cfp_step_04 _ _
      (fun c H => dpcutafterkeep_nonneg__cfp_step_04 a del change p i c Hdel Hch H) HC). }
  assert (Hempty : i <= 0 -> cutAfterKeep = INF).
  { intros Hi0.
    destruct (Z.eq_dec cutAfterKeep INF) as [He | He]; [exact He |].
    pose proof dpvalue_mem__cfp_step_04 _ _ HC He as [l [Hl1 [Hl2 _]]]. lia. }
  apply (dpvalue_shift__cfp_step_04 _ m del v).
  - intros c [l [Hl1 [Hl2 Hpl]]].
    destruct (plan_shrink_cut__cfp_step_04 a del change p i l c Hi ltac:(lia) Hpl)
      as [c0 [Hp0 Hce]].
    destruct (Z.eq_dec l i) as [Hli | Hli].
    + subst l.
      pose proof dpvalue_le_mem__cfp_step_04 _ _ _ HK Hp0 as Hk0.
      rewrite (Hpos ltac:(lia)).
      pose proof Z.le_min_l keep cutAfterKeep. lia.
    + assert (Hmem : DPCutAfterKeep a del change p i c0) by (exists l; split; [lia | split; [lia | exact Hp0]]).
      pose proof dpvalue_le_mem__cfp_step_04 _ _ _ HC Hmem as Hk0.
      rewrite (Hpos ltac:(lia)).
      pose proof Z.le_min_r keep cutAfterKeep. lia.
  - intros Hlt.
    assert (Hi0 : i > 0).
    { destruct (Z_le_gt_dec i 0) as [Hle | Hgt]; [| lia].
      rewrite (Hzero Hle) in Hlt. rewrite (Hempty Hle) in Hlt. lia. }
    rewrite (Hpos Hi0) in *.
    destruct (Z.min_dec keep cutAfterKeep) as [Hmin | Hmin]; rewrite Hmin in *.
    + assert (Hkne : keep <> INF) by lia.
      pose proof dpvalue_mem__cfp_step_04 _ _ HK Hkne as Hmem.
      exists i. split; [lia | split; [lia |]].
      exact (plan_extend_cut__cfp_step_04 a del change p i i keep Hi ltac:(lia) Hmem).
    + assert (Hkne : cutAfterKeep <> INF) by lia.
      pose proof dpvalue_mem__cfp_step_04 _ _ HC Hkne as [l [Hl1 [Hl2 Hpl]]].
      exists l. split; [lia | split; [lia |]].
      exact (plan_extend_cut__cfp_step_04 a del change p i l cutAfterKeep Hi ltac:(lia) Hpl).
  - exact Hfin.
  - exact Hsat.
Qed.
Lemma dp_after_step__cfp_step_04 :
  forall (a : list Z) (del change p i cutFresh cutAfterKeep after m cost v : Z),
    0 <= del -> 0 <= change -> 2 <= p -> 0 <= i < Zlength a ->
    cost = ElemCost change p (Znth i a 0) ->
    DPValue (DPCutFresh a del change p i) cutFresh ->
    DPValue (DPCutAfterKeep a del change p i) cutAfterKeep ->
    DPValue (DPAfter a del change p i) after ->
    m = Z.min cutFresh (Z.min cutAfterKeep after) ->
    (m + cost <= INF -> v = m + cost) ->
    (INF <= m + cost -> v = INF) ->
    DPValue (DPAfter a del change p (i + 1)) v.
Proof.
  intros a del change p i cutFresh cutAfterKeep after m cost v
    Hdel Hch Hp Hi Hcost HF HC HA Hm Hfin Hsat.
  assert (Hfn : 0 <= cutFresh).
  { apply (dpvalue_nonneg__cfp_step_04 _ _
      (fun c H => dpcutfresh_nonneg__cfp_step_04 a del change p i c Hdel Hch H) HF). }
  assert (Hcn : 0 <= cutAfterKeep).
  { apply (dpvalue_nonneg__cfp_step_04 _ _
      (fun c H => dpcutafterkeep_nonneg__cfp_step_04 a del change p i c Hdel Hch H) HC). }
  assert (Han : 0 <= after).
  { apply (dpvalue_nonneg__cfp_step_04 _ _
      (fun c H => dpafter_nonneg__cfp_step_04 a del change p i c Hdel Hch H) HA). }
  pose proof elemcost_nonneg__cfp_step_04 change p (Znth i a 0) Hch as Hcostn.
  pose proof Z.le_min_l cutFresh (Z.min cutAfterKeep after) as Hmf.
  pose proof Z.le_min_r cutFresh (Z.min cutAfterKeep after) as Hmr.
  pose proof Z.le_min_l cutAfterKeep after as Hmc.
  pose proof Z.le_min_r cutAfterKeep after as Hma.
  assert (Hmn : 0 <= m) by lia.
  apply (dpvalue_shift__cfp_step_04 _ m cost v).
  - intros c [l [r [Hrlt Hpl]]].
    destruct (plan_shrink_keep__cfp_step_04 a del change p i l r c Hi ltac:(lia) Hpl)
      as [c0 [dd [Hp0 [Hdd [Hdiv Hce]]]]].
    pose proof elemcost_min__cfp_step_04 change p (Znth i a 0) dd Hp Hch Hdd Hdiv as Hmin.
    pose proof Hp0 as Hb. destruct Hb as [Hl [Hlr [Hrr _]]].
    assert (Hmc0 : m <= c0).
    { destruct (Z.eq_dec r i) as [Hri | Hri].
      - subst r.
        destruct (Z.eq_dec l 0) as [Hl0 | Hl0].
        + subst l.
          pose proof dpvalue_le_mem__cfp_step_04 _ _ _ HF Hp0. lia.
        + destruct (Z.eq_dec l i) as [Hli | Hli].
          * subst l.
            pose proof dpkeep_sub_dpafter__cfp_step_04 a del change p i c0
              ltac:(lia) Hp0 as Hin.
            pose proof dpvalue_le_mem__cfp_step_04 _ _ _ HA Hin. lia.
          * assert (Hin : DPCutAfterKeep a del change p i c0)
              by (exists l; split; [lia | split; [lia | exact Hp0]]).
            pose proof dpvalue_le_mem__cfp_step_04 _ _ _ HC Hin. lia.
      - assert (Hin : DPAfter a del change p i c0)
          by (exists l, r; split; [lia | exact Hp0]).
        pose proof dpvalue_le_mem__cfp_step_04 _ _ _ HA Hin. lia. }
    subst cost. lia.
  - intros Hlt.
    assert (Hcne : ElemCost change p (Znth i a 0) <> INF) by lia.
    destruct (elemcost_witness__cfp_step_04 change p (Znth i a 0) Hp Hcne)
      as [dd [Hdd [Hdiv Heq]]].
    subst cost. rewrite Heq.
    destruct (Z.min_dec cutFresh (Z.min cutAfterKeep after)) as [Hd1 | Hd1];
      rewrite Hd1 in Hm.
    + assert (Hne : cutFresh <> INF) by lia.
      pose proof dpvalue_mem__cfp_step_04 _ _ HF Hne as Hmem.
      exists 0, i. split; [lia |].
      rewrite Hm.
      exact (plan_extend_keep__cfp_step_04 a del change p i 0 i cutFresh dd
               Hi ltac:(lia) Hmem Hdd Hdiv).
    + destruct (Z.min_dec cutAfterKeep after) as [Hd2 | Hd2]; rewrite Hd2 in Hm.
      * assert (Hne : cutAfterKeep <> INF) by lia.
        pose proof dpvalue_mem__cfp_step_04 _ _ HC Hne as [l [Hl1 [Hl2 Hpl]]].
        exists l, i. split; [lia |].
        rewrite Hm.
        exact (plan_extend_keep__cfp_step_04 a del change p i l i cutAfterKeep dd
                 Hi ltac:(lia) Hpl Hdd Hdiv).
      * assert (Hne : after <> INF) by lia.
        pose proof dpvalue_mem__cfp_step_04 _ _ HA Hne as [l [r [Hrlt Hpl]]].
        exists l, r. split; [lia |].
        rewrite Hm.
        exact (plan_extend_keep__cfp_step_04 a del change p i l r after dd
                 Hi ltac:(lia) Hpl Hdd Hdiv).
  - exact Hfin.
  - exact Hsat.
Qed.
Lemma cfp_state_finite_bound__cfp_step_04 :
  forall (a : list Z) (del change p i keep cutFresh cutAfterKeep after : Z),
    0 <= del -> 0 <= change ->
    CostForPrimeState a del change p i keep cutFresh cutAfterKeep after ->
    (0 <= keep /\
     (keep <> INF -> keep <= Zlength a * del + 2 * (Zlength a * change))) /\
    (0 <= cutFresh /\
     (cutFresh <> INF -> cutFresh <= Zlength a * del + 2 * (Zlength a * change))) /\
    (0 <= cutAfterKeep /\
     (cutAfterKeep <> INF -> cutAfterKeep <= Zlength a * del + 2 * (Zlength a * change))) /\
    (0 <= after /\
     (after <> INF -> after <= Zlength a * del + 2 * (Zlength a * change))).
Proof.
  intros a del change p i keep cutFresh cutAfterKeep after Hdel Hch [HK [HF [HC HA]]].
  split; [| split; [| split]].
  - split.
    + apply (dpvalue_nonneg__cfp_step_04 _ _
        (fun c H => dpkeep_nonneg__cfp_step_04 a del change p i c Hdel Hch H) HK).
    + intros Hne.
      pose proof dpvalue_mem__cfp_step_04 _ _ HK Hne as Hmem.
      destruct (plan_bounds__cfp_step_04 a del change p i i i keep Hdel Hch Hmem). lia.
  - split.
    + apply (dpvalue_nonneg__cfp_step_04 _ _
        (fun c H => dpcutfresh_nonneg__cfp_step_04 a del change p i c Hdel Hch H) HF).
    + intros Hne.
      pose proof dpvalue_mem__cfp_step_04 _ _ HF Hne as Hmem.
      destruct (plan_bounds__cfp_step_04 a del change p i 0 i cutFresh Hdel Hch Hmem). lia.
  - split.
    + apply (dpvalue_nonneg__cfp_step_04 _ _
        (fun c H => dpcutafterkeep_nonneg__cfp_step_04 a del change p i c Hdel Hch H) HC).
    + intros Hne.
      pose proof dpvalue_mem__cfp_step_04 _ _ HC Hne as [l [_ [_ Hmem]]].
      destruct (plan_bounds__cfp_step_04 a del change p i l i cutAfterKeep Hdel Hch Hmem). lia.
  - split.
    + apply (dpvalue_nonneg__cfp_step_04 _ _
        (fun c H => dpafter_nonneg__cfp_step_04 a del change p i c Hdel Hch H) HA).
    + intros Hne.
      pose proof dpvalue_mem__cfp_step_04 _ _ HA Hne as [l [r [_ Hmem]]].
      destruct (plan_bounds__cfp_step_04 a del change p i l r after Hdel Hch Hmem). lia.
Qed.
Lemma cfp_state_step__cfp_step_04 :
  forall (a : list Z)
         (del change p i keep cutFresh cutAfterKeep after cost mC mA
          keep' cutFresh' cutAfterKeep' after' : Z),
    0 <= del -> 0 <= change -> 2 <= p -> 0 <= i < Zlength a ->
    cost = ElemCost change p (Znth i a 0) ->
    CostForPrimeState a del change p i keep cutFresh cutAfterKeep after ->
    (i > 0 -> mC = Z.min keep cutAfterKeep) ->
    (i <= 0 -> mC = cutAfterKeep) ->
    mA = Z.min cutFresh (Z.min cutAfterKeep after) ->
    (keep + cost <= INF -> keep' = keep + cost) ->
    (INF <= keep + cost -> keep' = INF) ->
    (cutFresh + del <= INF -> cutFresh' = cutFresh + del) ->
    (INF <= cutFresh + del -> cutFresh' = INF) ->
    (mC + del <= INF -> cutAfterKeep' = mC + del) ->
    (INF <= mC + del -> cutAfterKeep' = INF) ->
    (mA + cost <= INF -> after' = mA + cost) ->
    (INF <= mA + cost -> after' = INF) ->
    CostForPrimeState a del change p (i + 1) keep' cutFresh' cutAfterKeep' after'.
Proof.
  intros a del change p i keep cutFresh cutAfterKeep after cost mC mA
    keep' cutFresh' cutAfterKeep' after'
    Hdel Hch Hp Hi Hcost HS HmC1 HmC2 HmA
    Hk1 Hk2 Hf1 Hf2 Hc1 Hc2 Ha1 Ha2.
  destruct HS as [HK [HF [HC HA]]].
  unfold CostForPrimeState.
  split; [| split; [| split]].
  - exact (dp_keep_step__cfp_step_04 a del change p i keep cost keep'
             Hdel Hch Hp Hi Hcost HK Hk1 Hk2).
  - exact (dp_cutfresh_step__cfp_step_04 a del change p i cutFresh cutFresh'
             Hdel Hch Hi HF Hf1 Hf2).
  - exact (dp_cutafterkeep_step__cfp_step_04 a del change p i keep cutAfterKeep mC
             cutAfterKeep' Hdel Hch Hi HK HC HmC1 HmC2 Hc1 Hc2).
  - exact (dp_after_step__cfp_step_04 a del change p i cutFresh cutAfterKeep after mA cost
             after' Hdel Hch Hp Hi Hcost HF HC HA HmA Ha1 Ha2).
Qed.
Lemma dpv_lb__cfp_step_05 : forall (S : Z -> Prop) (v c : Z),
  DPValue S v -> S c -> v <= c.
Proof.
  intros S v c HD HS.
  unfold DPValue, MaxMin.min_value_of_subset_with_default in HD.
  destruct HD as [[[a [[Ha1 Ha2] Ha3]] Hle] | [Hall Heq]].
  - subst v. apply Ha2. exact HS.
  - subst v. apply Hall. exact HS.
Qed.
Lemma dpv_attained__cfp_step_05 : forall (S : Z -> Prop) (v : Z),
  DPValue S v -> v <> INF -> S v.
Proof.
  intros S v HD Hne.
  unfold DPValue, MaxMin.min_value_of_subset_with_default in HD.
  destruct HD as [[[a [[Ha1 Ha2] Ha3]] Hle] | [Hall Heq]].
  - subst v. exact Ha1.
  - unfold INF in Hne. contradiction.
Qed.
Lemma dpv_ge_inf__cfp_step_05 : forall (S : Z -> Prop),
  (forall c, S c -> INF <= c) -> DPValue S INF.
Proof.
  intros S H.
  unfold DPValue, MaxMin.min_value_of_subset_with_default. right.
  split; [| reflexivity]. intros a Ha. apply H. exact Ha.
Qed.
Lemma dpv_min__cfp_step_05 : forall (S : Z -> Prop) (v : Z),
  S v -> (forall c, S c -> v <= c) -> v <= INF -> DPValue S v.
Proof.
  intros S v H1 H2 H3.
  unfold DPValue, MaxMin.min_value_of_subset_with_default,
         MaxMin.min_value_of_subset, MaxMin.min_object_of_subset. left.
  split; [| exact H3].
  exists v. split; [| reflexivity]. split; [exact H1 | exact H2].
Qed.
Lemma fold_one_len__cfp_step_05 : forall (l : list Z),
  fold_right (fun _ acc : Z => 1 + acc) 0 l = Z.of_nat (length l).
Proof.
  induction l as [| a l IH]; [reflexivity |].
  cbn [fold_right length]. rewrite IH. lia.
Qed.
Lemma card_range__cfp_step_05 : forall (n : Z) (P : Z -> Prop),
  @SpecHelpers.set_card Z (fun i => 0 <= i < n /\ P i) (ZRange.finite_Z_range' 0 n P)
  = Z.of_nat (length (filter (fun i => if Sum.prop_dec (P i) then true else false) (ZRange.Zrange 0 n))).
Proof.
  intros n P.
  unfold SpecHelpers.set_card, SumLib.Sum.sum.
  simpl.
  apply fold_one_len__cfp_step_05.
Qed.
Lemma len_Zrange__cfp_step_05 : forall lo hi, length (ZRange.Zrange lo hi) = Z.to_nat (hi - lo).
Proof.
  intros lo hi. unfold ZRange.Zrange.
  generalize (Z.to_nat (hi - lo)) as n. intros n. revert lo.
  induction n as [| n IH]; intros lo; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.
Lemma count_as_filter__cfp_step_05 : forall (x : Z) (xs : list Z),
  Count x xs
  = Z.of_nat (length (filter (fun i => if Sum.prop_dec (Znth i xs 0 = x) then true else false)
                             (ZRange.Zrange 0 (Zlength xs)))).
Proof.
  intros x xs. unfold Count. apply (card_range__cfp_step_05 (Zlength xs) (fun i => Znth i xs 0 = x)).
Qed.
Lemma count_nil__cfp_step_05 : forall (x : Z), Count x [] = 0.
Proof.
  intros x. rewrite count_as_filter__cfp_step_05. rewrite Zlength_nil. reflexivity.
Qed.
Lemma count_bound__cfp_step_05 : forall (x : Z) (xs : list Z),
  0 <= Count x xs <= Zlength xs.
Proof.
  intros x xs. rewrite count_as_filter__cfp_step_05.
  assert (Hnn : 0 <= Zlength xs) by (rewrite Zlength_correct; lia).
  match goal with
  | |- context [filter ?f ?l] => pose proof (filter_length_le f l) as Hle
  end.
  rewrite len_Zrange__cfp_step_05 in Hle. lia.
Qed.
Lemma Zrange_snoc__cfp_step_05 : forall n, 0 <= n -> ZRange.Zrange 0 (n + 1) = ZRange.Zrange 0 n ++ [n].
Proof.
  intros n Hn. unfold ZRange.Zrange.
  replace (Z.to_nat (n + 1 - 0)) with (Z.to_nat (n - 0) + 1)%nat by lia.
  rewrite ZRange.Zrange_aux_app.
  f_equal. simpl. f_equal. lia.
Qed.
Lemma count_snoc__cfp_step_05 : forall (x dd : Z) (l : list Z),
  Count x (l ++ [dd]) = Count x l + (if Sum.prop_dec (dd = x) then 1 else 0).
Proof.
  intros x dd l.
  assert (Hnn : 0 <= Zlength l) by (rewrite Zlength_correct; lia).
  assert (HL : Zlength (l ++ [dd]) = Zlength l + 1)
    by (rewrite !Zlength_correct, length_app; simpl; lia).
  rewrite !count_as_filter__cfp_step_05.
  rewrite HL.
  rewrite (Zrange_snoc__cfp_step_05 (Zlength l) Hnn).
  rewrite filter_app, length_app, Nat2Z.inj_add.
  f_equal.
  - do 2 f_equal. apply filter_ext_in.
    intros i Hi. rewrite <- ZRange.In_Zrange in Hi.
    rewrite (app_Znth1 0 l [dd] i Hi). reflexivity.
  - cbn [filter].
    rewrite (app_Znth2 0 l [dd] (Zlength l)) by lia.
    replace (Zlength l - Zlength l) with 0 by lia.
    replace (Znth 0 [dd] 0) with dd by reflexivity.
    destruct (Sum.prop_dec (dd = x)); cbn [length]; reflexivity.
Qed.
Lemma zlen_nil_inv__cfp_step_05 : forall (l : list Z), Zlength l = 0 -> l = [].
Proof.
  intros l H. destruct l as [| a l]; [reflexivity |].
  rewrite Zlength_cons in H.
  assert (0 <= Zlength l) by (rewrite Zlength_correct; lia). lia.
Qed.
Lemma combine_snoc__cfp_step_05 : forall (l1 l2 : list Z) (x y : Z),
  length l1 = length l2 ->
  combine (l1 ++ [x]) (l2 ++ [y]) = combine l1 l2 ++ [(x, y)].
Proof.
  induction l1 as [| a l1 IH]; intros l2 x y Hlen.
  - destruct l2; [reflexivity | simpl in Hlen; lia].
  - destruct l2 as [| b l2]; [simpl in Hlen; lia |].
    simpl in Hlen. simpl. rewrite IH by lia. reflexivity.
Qed.
Lemma sub_jj__cfp_step_05 : forall (l : list Z) (j : Z), sublist j j l = [].
Proof. intros. apply Zsublist_nil. lia. Qed.
Lemma changecost_snoc__cfp_step_05 : forall del change l r (delta : list Z) (dd : Z),
  dd = -1 \/ dd = 0 \/ dd = 1 ->
  ChangeCost del change l r (delta ++ [dd])
  = ChangeCost del change l r delta + (if Z.eqb dd 0 then 0 else change).
Proof.
  intros del change l r delta dd Hdd.
  unfold ChangeCost.
  rewrite !count_snoc__cfp_step_05.
  destruct Hdd as [-> | [-> | ->]];
    repeat (destruct (Sum.prop_dec _); try lia); cbn [Z.eqb]; lia.
Qed.
Lemma adjusted_snoc__cfp_step_05 : forall (kept delta result : list Z) (x dd : Z),
  Adjusted kept delta result -> (dd = -1 \/ dd = 0 \/ dd = 1) ->
  Adjusted (kept ++ [x]) (delta ++ [dd]) (result ++ [x + dd]).
Proof.
  intros kept delta result x dd HA Hdd.
  destruct HA as (Hlen & Hf & Hres).
  rewrite !Zlength_correct in Hlen.
  unfold Adjusted. split; [| split].
  - rewrite !Zlength_correct, !length_app. simpl. lia.
  - apply Forall_app. split; [exact Hf | constructor; [exact Hdd | constructor]].
  - rewrite combine_snoc__cfp_step_05 by lia. rewrite map_app. cbn [map combine fst snd].
    rewrite Hres. reflexivity.
Qed.
Lemma adjusted_snoc_inv__cfp_step_05 : forall (kept delta result : list Z) (x : Z),
  Adjusted (kept ++ [x]) delta result ->
  exists delta' dd result',
    delta = delta' ++ [dd] /\ result = result' ++ [x + dd] /\
    Adjusted kept delta' result' /\ (dd = -1 \/ dd = 0 \/ dd = 1).
Proof.
  intros kept delta result x HA.
  destruct HA as (Hlen & Hf & Hres).
  rewrite !Zlength_correct, length_app in Hlen. cbn [length] in Hlen.
  assert (Hne : delta <> []).
  { intro Hc. subst delta. cbn [length] in Hlen. lia. }
  destruct (exists_last Hne) as [delta' [dd Hd]].
  subst delta.
  rewrite length_app in Hlen. cbn [length] in Hlen.
  assert (Hl2 : length delta' = length kept) by lia.
  exists delta', dd, (map (fun q => fst q + snd q) (combine kept delta')).
  split; [reflexivity |].
  split.
  { rewrite Hres. rewrite combine_snoc__cfp_step_05 by lia. rewrite map_app.
    cbn [map combine fst snd]. reflexivity. }
  split.
  { unfold Adjusted. split; [rewrite !Zlength_correct; lia |].
    split; [| reflexivity].
    apply (proj1 (proj1 (Forall_app _ _ _) Hf)). }
  { pose proof (proj2 (proj1 (Forall_app _ _ _) Hf)) as Hd2.
    inversion Hd2; subst; assumption. }
Qed.
Lemma plan_cost_bound__cfp_step_05 : forall a del change p i l r c,
  0 <= del -> 0 <= change ->
  PartialPlanCost a del change p i l r c ->
  0 <= c /\ c <= Zlength a * del + 2 * (Zlength a * change).
Proof.
  intros a del change p i l r c Hdel Hch HP.
  destruct HP as (Hl & Hlr & Hri & HiA & delta & result & HA & Hdiv & Hc).
  destruct HA as (Hlen & _ & _).
  assert (Ha0 : 0 <= Zlength a) by (rewrite Zlength_correct; lia).
  assert (Hk : Zlength (sublist 0 l a ++ sublist r i a) = l + (i - r)).
  { rewrite Zlength_app. rewrite (Zlength_sublist 0 l a) by lia.
    rewrite (Zlength_sublist r i a) by lia. lia. }
  rewrite Hk in Hlen.
  pose proof (count_bound__cfp_step_05 (-1) delta) as Hc1.
  pose proof (count_bound__cfp_step_05 1 delta) as Hc2.
  rewrite Hlen in Hc1, Hc2.
  unfold ChangeCost in Hc. subst c.
  split.
  - nia.
  - assert (H1 : (r - l) * del <= Zlength a * del) by nia.
    assert (H2 : Count (-1) delta * change <= Zlength a * change) by nia.
    assert (H3 : Count 1 delta * change <= Zlength a * change) by nia.
    lia.
Qed.
Lemma sub_snoc__cfp_step_05 : forall (a : list Z) (r i : Z),
  0 <= r -> r <= i -> i < Zlength a ->
  sublist r (i + 1) a = sublist r i a ++ [Znth i a 0].
Proof.
  intros a r i H1 H2 H3.
  rewrite (sublist_split r (i + 1) i a) by lia.
  f_equal. apply (@sublist_single Z 0 i a). lia.
Qed.
Lemma ppc_shrink_full_cut__cfp_step_05 : forall a del change p i l c,
  0 <= l -> l <= i -> i + 1 <= Zlength a ->
  PartialPlanCost a del change p (i + 1) l (i + 1) c ->
  PartialPlanCost a del change p i l i (c - del).
Proof.
  intros a del change p i l c Hl Hli HiA HP.
  destruct HP as (H1 & H2 & H3 & H4 & delta & result & HA & Hdiv & Hc).
  rewrite sub_jj__cfp_step_05 in HA.
  unfold PartialPlanCost.
  split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
  exists delta, result.
  rewrite sub_jj__cfp_step_05.
  split; [exact HA |]. split; [exact Hdiv |].
  unfold ChangeCost in *. lia.
Qed.
Lemma ppc_shrink_keep__cfp_step_05 : forall a del change p i c,
  0 <= i -> i + 1 <= Zlength a ->
  PartialPlanCost a del change p (i + 1) (i + 1) (i + 1) c ->
  exists c', PartialPlanCost a del change p i i i c'.
Proof.
  intros a del change p i c Hi HiA HP.
  destruct HP as (H1 & H2 & H3 & H4 & delta & result & HA & Hdiv & Hc).
  rewrite sub_jj__cfp_step_05, app_nil_r in HA.
  rewrite (sub_snoc__cfp_step_05 a 0 i) in HA by lia.
  destruct (adjusted_snoc_inv__cfp_step_05 _ _ _ _ HA) as (delta' & dd & result' & Hd & Hr & HA' & Hdd).
  exists (ChangeCost del change i i delta').
  unfold PartialPlanCost.
  split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
  exists delta', result'.
  rewrite sub_jj__cfp_step_05, app_nil_r.
  split; [exact HA' |]. split; [| reflexivity].
  subst result. apply (proj1 (proj1 (Forall_app _ _ _) Hdiv)).
Qed.
Lemma dpcutfresh_char__cfp_step_05 : forall a del change p j c,
  0 <= j <= Zlength a -> (DPCutFresh a del change p j c <-> c = j * del).
Proof.
  intros a del change p j c Hj. split.
  - intros HP. unfold DPCutFresh in HP.
    destruct HP as (H1 & H2 & H3 & H4 & delta & result & HA & Hdiv & Hc).
    rewrite !sub_jj__cfp_step_05 in HA. cbn [app] in HA.
    destruct HA as (Hlen & _ & _).
    rewrite Zlength_nil in Hlen.
    apply zlen_nil_inv__cfp_step_05 in Hlen. subst delta.
    unfold ChangeCost in Hc. rewrite !count_nil__cfp_step_05 in Hc. lia.
  - intros ->. unfold DPCutFresh, PartialPlanCost.
    split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
    exists (@nil Z), (@nil Z).
    rewrite !sub_jj__cfp_step_05. cbn [app].
    split.
    { unfold Adjusted. split; [reflexivity |].
      split; [constructor | reflexivity]. }
    split; [constructor |].
    unfold ChangeCost. rewrite !count_nil__cfp_step_05. lia.
Qed.
Lemma elemcost_cases__cfp_step_05 : forall change p x,
  ElemCost change p x = 0 \/ ElemCost change p x = change \/ ElemCost change p x = INF.
Proof.
  intros change p x. unfold ElemCost.
  destruct (Z.eqb (x mod p) 0); [tauto |].
  destruct (orb (Z.eqb ((x - 1) mod p) 0) (Z.eqb ((x + 1) mod p) 0)); tauto.
Qed.
Lemma elemcost_le__cfp_step_05 : forall change p x dd,
  2 <= p -> 0 <= change -> (dd = -1 \/ dd = 0 \/ dd = 1) -> Z.divide p (x + dd) ->
  ElemCost change p x <= (if Z.eqb dd 0 then 0 else change).
Proof.
  intros change p x dd Hp Hch Hdd Hdiv.
  unfold ElemCost.
  destruct Hdd as [-> | [-> | ->]].
  - assert (Hm : (x - 1) mod p = 0).
    { apply Z.mod_divide; [lia |]. replace (x - 1) with (x + -1) by lia. exact Hdiv. }
    destruct (Z.eqb (x mod p) 0) eqn:E1; [simpl; lia |].
    rewrite Hm. simpl. lia.
  - assert (Hm : x mod p = 0).
    { apply Z.mod_divide; [lia |]. replace x with (x + 0) by lia. exact Hdiv. }
    rewrite Hm. simpl. lia.
  - assert (Hm : (x + 1) mod p = 0).
    { apply Z.mod_divide; [lia |]. exact Hdiv. }
    destruct (Z.eqb (x mod p) 0) eqn:E1; [simpl; lia |].
    rewrite Hm. rewrite Bool.orb_true_r. simpl. lia.
Qed.
Lemma elemcost_witness__cfp_step_05 : forall change p x,
  2 <= p -> ElemCost change p x <> INF ->
  exists dd, (dd = -1 \/ dd = 0 \/ dd = 1) /\ Z.divide p (x + dd) /\
             ElemCost change p x = (if Z.eqb dd 0 then 0 else change).
Proof.
  intros change p x Hp Hne.
  unfold ElemCost in *.
  destruct (Z.eqb (x mod p) 0) eqn:E1.
  - exists 0. split; [tauto |]. split.
    + replace (x + 0) with x by lia. apply Z.mod_divide; [lia |].
      apply Z.eqb_eq in E1. exact E1.
    + reflexivity.
  - destruct (orb (Z.eqb ((x - 1) mod p) 0) (Z.eqb ((x + 1) mod p) 0)) eqn:E2.
    + apply Bool.orb_true_iff in E2. destruct E2 as [E2 | E2]; apply Z.eqb_eq in E2.
      * exists (-1). split; [tauto |]. split; [| reflexivity].
        replace (x + -1) with (x - 1) by lia. apply Z.mod_divide; [lia | exact E2].
      * exists 1. split; [tauto |]. split; [| reflexivity].
        apply Z.mod_divide; [lia | exact E2].
    + contradiction.
Qed.
Lemma dpv_empty_inf__cfp_step_05 : forall (S : Z -> Prop) (v : Z),
  (forall c, ~ S c) -> DPValue S v -> v = INF.
Proof.
  intros S v Hemp HD.
  destruct (Z.eq_dec v INF) as [E | E]; [exact E |].
  exfalso. apply (Hemp v). apply dpv_attained__cfp_step_05; assumption.
Qed.
Lemma cfp_after_zero__cfp_step_05 : forall a del change p i keep cf cak af,
  CostForPrimeState a del change p i keep cf cak af -> i <= 0 -> af = INF.
Proof.
  intros a del change p i keep cf cak af HS Hi.
  destruct HS as (_ & _ & _ & Haf).
  assert (Hemp : forall c, ~ DPAfter a del change p i c).
  { intros c Hc. unfold DPAfter in Hc.
    destruct Hc as (l & r & Hr & HP).
    destruct HP as (H1 & H2 & H3 & _). lia. }
  exact (dpv_empty_inf__cfp_step_05 _ _ Hemp Haf).
Qed.
Lemma dpcak_succ_inv__cfp_step_05 : forall a del change p i c,
  0 <= i -> i + 1 <= Zlength a ->
  DPCutAfterKeep a del change p (i + 1) c ->
  (DPCutAfterKeep a del change p i (c - del) \/ DPKeep a del change p i (c - del)).
Proof.
  intros a del change p i c Hi HiA HD.
  destruct HD as (l & Hl1 & Hl2 & HP).
  pose proof (ppc_shrink_full_cut__cfp_step_05 a del change p i l c ltac:(lia) ltac:(lia) HiA HP) as HP'.
  destruct (Z.eq_dec l i) as [E | E].
  - right. unfold DPKeep. subst l. exact HP'.
  - left. exists l. split; [lia |]. split; [lia |]. exact HP'.
Qed.
Lemma dpafter_succ_inv__cfp_step_05 : forall a del change p i c,
  0 <= i -> i + 1 <= Zlength a -> 2 <= p -> 0 <= change ->
  DPAfter a del change p (i + 1) c ->
  exists c0,
    ElemCost change p (Znth i a 0) + c0 <= c /\
    (DPAfter a del change p i c0 \/ DPKeep a del change p i c0 \/
     DPCutFresh a del change p i c0 \/ DPCutAfterKeep a del change p i c0).
Proof.
  intros a del change p i c Hi HiA Hp Hch HD.
  destruct HD as (l & r & Hr & HP).
  destruct HP as (H1 & H2 & H3 & H4 & delta & result & HA & Hdiv & Hc).
  assert (Hri : r <= i) by lia.
  rewrite (sub_snoc__cfp_step_05 a r i) in HA by lia.
  rewrite app_assoc in HA.
  destruct (adjusted_snoc_inv__cfp_step_05 _ _ _ _ HA) as (delta' & dd & result' & Hd & Hres & HA' & Hdd).
  subst result.
  pose proof (proj1 (Forall_app _ _ _) Hdiv) as Hsp.
  destruct Hsp as [Hdiv' Hdivlast].
  assert (Hdl : Z.divide p (Znth i a 0 + dd))
    by (inversion Hdivlast; subst; assumption).
  exists (ChangeCost del change l r delta').
  assert (HP0 : PartialPlanCost a del change p i l r (ChangeCost del change l r delta')).
  { unfold PartialPlanCost.
    split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
    exists delta', result'. split; [exact HA' |]. split; [exact Hdiv' | reflexivity]. }
  split.
  { pose proof (elemcost_le__cfp_step_05 change p (Znth i a 0) dd Hp Hch Hdd Hdl) as Hle.
    subst c. rewrite Hd. rewrite (changecost_snoc__cfp_step_05 del change l r delta' dd Hdd).
    destruct (Z.eqb dd 0); lia. }
  destruct (Z_lt_le_dec r i) as [Hlt | Hge].
  - left. exists l, r. split; [lia | exact HP0].
  - assert (Hreq : r = i) by lia. subst r.
    destruct (Z.eq_dec l i) as [El | El].
    + right. left. unfold DPKeep. subst l. exact HP0.
    + destruct (Z.eq_dec l 0) as [E0 | E0].
      * right. right. left. unfold DPCutFresh. subst l. exact HP0.
      * right. right. right. exists l. split; [lia |]. split; [lia | exact HP0].
Qed.
Lemma dpafter_succ_intro__cfp_step_05 : forall a del change p i c0,
  0 <= i -> i + 1 <= Zlength a -> 2 <= p ->
  ElemCost change p (Znth i a 0) <> INF ->
  DPAfter a del change p i c0 ->
  DPAfter a del change p (i + 1) (c0 + ElemCost change p (Znth i a 0)).
Proof.
  intros a del change p i c0 Hi HiA Hp Hne HD.
  destruct HD as (l & r & Hr & HP).
  destruct HP as (H1 & H2 & H3 & H4 & delta & result & HA & Hdiv & Hc).
  destruct (elemcost_witness__cfp_step_05 change p (Znth i a 0) Hp Hne) as (dd & Hdd & Hdiv2 & Hval).
  exists l, r. split; [lia |].
  unfold PartialPlanCost.
  split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
  exists (delta ++ [dd]), (result ++ [Znth i a 0 + dd]).
  rewrite (sub_snoc__cfp_step_05 a r i) by lia.
  rewrite app_assoc.
  split; [apply adjusted_snoc__cfp_step_05; assumption |].
  split.
  { apply Forall_app. split; [exact Hdiv | constructor; [exact Hdiv2 | constructor]]. }
  rewrite (changecost_snoc__cfp_step_05 del change l r delta dd Hdd). rewrite Hval. lia.
Qed.
Lemma dpv_le_inf__cfp_step_05 : forall (S : Z -> Prop) (v : Z), DPValue S v -> v <= INF.
Proof.
  intros S v HD.
  unfold DPValue, MaxMin.min_value_of_subset_with_default in HD.
  destruct HD as [[_ Hle] | [_ Heq]]; [exact Hle | subst v; lia].
Qed.
Lemma cfp_state_finite_bound__cfp_step_05 : forall a del change p i keep cf cak af,
  0 <= del -> 0 <= change ->
  CostForPrimeState a del change p i keep cf cak af ->
  (keep <> INF -> keep <= Zlength a * del + 2 * (Zlength a * change)) /\
  (cf <> INF -> cf <= Zlength a * del + 2 * (Zlength a * change)) /\
  (cak <> INF -> cak <= Zlength a * del + 2 * (Zlength a * change)) /\
  (af <> INF -> af <= Zlength a * del + 2 * (Zlength a * change)).
Proof.
  intros a del change p i keep cf cak af Hdel Hch HS.
  destruct HS as (Hk & Hf & Hc & Ha).
  split; [| split; [| split]].
  - intros Hne. pose proof (dpv_attained__cfp_step_05 _ _ Hk Hne) as HP.
    unfold DPKeep in HP. apply (plan_cost_bound__cfp_step_05 a del change p i i i keep Hdel Hch HP).
  - intros Hne. pose proof (dpv_attained__cfp_step_05 _ _ Hf Hne) as HP.
    unfold DPCutFresh in HP. apply (plan_cost_bound__cfp_step_05 a del change p i 0 i cf Hdel Hch HP).
  - intros Hne. pose proof (dpv_attained__cfp_step_05 _ _ Hc Hne) as HP.
    unfold DPCutAfterKeep in HP. destruct HP as (l & _ & _ & HP).
    apply (plan_cost_bound__cfp_step_05 a del change p i l i cak Hdel Hch HP).
  - intros Hne. pose proof (dpv_attained__cfp_step_05 _ _ Ha Hne) as HP.
    unfold DPAfter in HP. destruct HP as (l & r & _ & HP).
    apply (plan_cost_bound__cfp_step_05 a del change p i l r af Hdel Hch HP).
Qed.
Lemma cfp_state_step__cfp_step_05 : forall a del change p i keep cf cak af cost,
  0 <= del -> 0 <= change -> 2 <= p ->
  0 <= i -> i + 1 <= Zlength a ->
  Zlength a * del + 2 * (Zlength a * change) < INF ->
  cost = ElemCost change p (Znth i a 0) ->
  cost <> INF ->
  keep = INF ->
  cf <> INF -> af <> INF ->
  af <= cf -> af <= cak -> INF <= cak + del ->
  cf + del <= INF -> af + cost <= INF ->
  CostForPrimeState a del change p i keep cf cak af ->
  CostForPrimeState a del change p (i + 1) INF (cf + del) INF (af + cost).
Proof.
  intros a del change p i keep cf cak af cost
         Hdel Hch Hp Hi HiA HB Hcost Hcostne Hkeep Hcfne Hafne
         Hafcf Hafcak Hcak Hcfle Hafle HS.
  pose proof HS as HS'.
  destruct HS as (Hk & Hf & Hc & Ha).
  split; [| split; [| split]].
  - apply dpv_ge_inf__cfp_step_05. intros c Hc2.
    exfalso. unfold DPKeep in Hc2.
    destruct (ppc_shrink_keep__cfp_step_05 a del change p i c Hi HiA Hc2) as (c' & Hc').
    pose proof (dpv_lb__cfp_step_05 _ _ _ Hk Hc') as Hle.
    pose proof (plan_cost_bound__cfp_step_05 a del change p i i i c' Hdel Hch Hc') as [_ Hb].
    rewrite Hkeep in Hle. lia.
  - assert (Hcfv : cf = i * del).
    { apply (proj1 (dpcutfresh_char__cfp_step_05 a del change p i cf ltac:(lia))).
      apply dpv_attained__cfp_step_05; assumption. }
    apply dpv_min__cfp_step_05.
    + apply (proj2 (dpcutfresh_char__cfp_step_05 a del change p (i + 1) (cf + del) ltac:(lia))). lia.
    + intros c Hc2.
      pose proof (proj1 (dpcutfresh_char__cfp_step_05 a del change p (i + 1) c ltac:(lia)) Hc2). lia.
    + exact Hcfle.
  - apply dpv_ge_inf__cfp_step_05. intros c Hc2.
    destruct (dpcak_succ_inv__cfp_step_05 a del change p i c Hi HiA Hc2) as [H1 | H1].
    + pose proof (dpv_lb__cfp_step_05 _ _ _ Hc H1) as Hle. lia.
    + pose proof (dpv_lb__cfp_step_05 _ _ _ Hk H1) as Hle. rewrite Hkeep in Hle. lia.
  - apply dpv_min__cfp_step_05.
    + pose proof (dpv_attained__cfp_step_05 _ _ Ha Hafne) as HA0.
      pose proof (dpafter_succ_intro__cfp_step_05 a del change p i af Hi HiA Hp
                    ltac:(rewrite <- Hcost; exact Hcostne) HA0) as HR.
      rewrite <- Hcost in HR. exact HR.
    + intros c Hc2.
      destruct (dpafter_succ_inv__cfp_step_05 a del change p i c Hi HiA Hp Hch Hc2)
        as (c0 & Hle & [H1 | [H1 | [H1 | H1]]]).
      * pose proof (dpv_lb__cfp_step_05 _ _ _ Ha H1). lia.
      * pose proof (dpv_lb__cfp_step_05 _ _ _ Hk H1) as Hk1. rewrite Hkeep in Hk1.
        pose proof (dpv_le_inf__cfp_step_05 _ _ Ha). lia.
      * pose proof (dpv_lb__cfp_step_05 _ _ _ Hf H1). lia.
      * pose proof (dpv_lb__cfp_step_05 _ _ _ Hc H1). lia.
    + exact Hafle.
Qed.
Lemma count_as_sum__cfp_step_06 :
  forall (x : Z) (xs : list Z),
    Count x xs =
    SumLib.Sum.sum (fun k : Z => 0 <= k < Zlength xs)
      (fun k => if prop_dec (Znth k xs 0 = x) then 1 else 0).
Proof.
  intros x xs.
  unfold Count, set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall ks : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun k => if prop_dec (Znth k xs 0 = x) then true else false) ks) =
    fold_right (fun k acc : Z =>
      (if prop_dec (Znth k xs 0 = x) then 1 else 0) + acc) 0 ks).
  { induction ks as [|k ks IH]; simpl; [reflexivity |].
    destruct (prop_dec (Znth k xs 0 = x)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH. }
  apply Hfilter.
Qed.
Lemma count_nonneg__cfp_step_06 :
  forall (x : Z) (xs : list Z), 0 <= Count x xs.
Proof.
  intros x xs.
  rewrite count_as_sum__cfp_step_06.
  apply sum_nonneg.
  intros k Hk. destruct (prop_dec (Znth k xs 0 = x)); lia.
Qed.
Lemma count_pair_bound__cfp_step_06 :
  forall (xs : list Z), Count (-1) xs + Count 1 xs <= Zlength xs.
Proof.
  intros xs.
  pose proof (Zlength_nonneg xs) as Hlen.
  rewrite !count_as_sum__cfp_step_06.
  rewrite <- sum_Z_range_add.
  transitivity (SumLib.Sum.sum (fun k : Z => 0 <= k < Zlength xs) (fun _ : Z => 1)).
  - apply sum_Z_range_le.
    intros k Hk.
    destruct (prop_dec (Znth k xs 0 = -1)) as [E1 | _];
      destruct (prop_dec (Znth k xs 0 = 1)) as [E2 | _]; lia.
  - rewrite sum_Z_range_const by lia. lia.
Qed.
Lemma count_nil__cfp_step_06 :
  forall (x : Z), Count x nil = 0.
Proof.
  intros x.
  rewrite count_as_sum__cfp_step_06.
  rewrite Zlength_nil.
  apply sum_Z_range_empty. lia.
Qed.
Lemma count_snoc__cfp_step_06 :
  forall (x : Z) (xs : list Z) (d : Z),
    Count x (xs ++ (d :: nil)) =
    Count x xs + (if prop_dec (d = x) then 1 else 0).
Proof.
  intros x xs d.
  pose proof (Zlength_nonneg xs) as Hlen.
  rewrite !count_as_sum__cfp_step_06.
  rewrite Zlength_app, Zlength_cons, Zlength_nil.
  replace (Zlength xs + Z.succ 0) with (Zlength xs + 1) by lia.
  rewrite sum_Z_range_extend_right by lia.
  f_equal.
  - apply sum_Z_range_ext.
    intros k Hk.
    rewrite app_Znth1 by lia. reflexivity.
  - rewrite app_Znth2 by lia.
    replace (Zlength xs - Zlength xs) with 0 by lia.
    rewrite Znth0_cons. reflexivity.
Qed.
Lemma dp_value_mem__cfp_step_06 :
  forall (S : Z -> Prop) (v : Z),
    S v -> (forall c, S c -> v <= c) -> v <= 4611686018427387904 ->
    DPValue S v.
Proof.
  intros S v Hin Hmin Hle.
  unfold DPValue, min_value_of_subset_with_default.
  left. split; [| exact Hle].
  unfold min_value_of_subset, min_object_of_subset.
  exists v. split; [| reflexivity].
  split.
  - sets_unfold. exact Hin.
  - intros b Hb. sets_unfold in Hb. apply Hmin. exact Hb.
Qed.
Lemma dp_value_empty__cfp_step_06 :
  forall (S : Z -> Prop),
    (forall c, ~ S c) -> DPValue S 4611686018427387904.
Proof.
  intros S Hemp.
  unfold DPValue, min_value_of_subset_with_default.
  right. unfold INF. split; [| reflexivity].
  intros c Hc. sets_unfold in Hc. exfalso. apply (Hemp c). exact Hc.
Qed.
Lemma dp_value_char__cfp_step_06 :
  forall (S : Z -> Prop) (v : Z),
    (forall c, S c -> 0 <= c <= 2000000000000000) ->
    DPValue S v ->
    (S v /\ forall c, S c -> v <= c) \/
    (v = 4611686018427387904 /\ forall c, ~ S c).
Proof.
  intros S v Hbound Hdp.
  unfold DPValue, min_value_of_subset_with_default in Hdp.
  destruct Hdp as [[Hmin _] | [Hall Heq]].
  - left. unfold min_value_of_subset, min_object_of_subset in Hmin.
    destruct Hmin as [w [[Hw Hle] Hveq]]. subst w.
    sets_unfold in Hw. split; [exact Hw |].
    intros c Hc. apply Hle. sets_unfold. exact Hc.
  - right. split; [exact Heq |].
    intros c Hc. specialize (Hall c ltac:(sets_unfold; exact Hc)).
    cbv beta in Hall. unfold INF in Hall. specialize (Hbound c Hc). lia.
Qed.
Lemma sublist_empty__cfp_step_06 :
  forall (a : list Z) (j : Z), sublist j j a = nil.
Proof. intros a j. apply Zsublist_nil. lia. Qed.
Lemma zlength_zero_nil__cfp_step_06 :
  forall (l : list Z), Zlength l = 0 -> l = nil.
Proof.
  intros l Hl. destruct l as [| x xs]; [reflexivity |].
  exfalso. rewrite Zlength_cons in Hl. pose proof (Zlength_nonneg xs). lia.
Qed.
Lemma elem_cost_bound__cfp_step_06 :
  forall (ch p x : Z),
    0 <= ch ->
    ElemCost ch p x <> 4611686018427387904 ->
    0 <= ElemCost ch p x <= ch.
Proof.
  intros ch p x Hch Hne. unfold ElemCost in *.
  destruct (Z.eqb (x mod p) 0); [lia |].
  destruct (orb (Z.eqb ((x - 1) mod p) 0) (Z.eqb ((x + 1) mod p) 0)); [lia |].
  unfold INF in Hne. lia.
Qed.
Lemma elem_cost_witness__cfp_step_06 :
  forall (ch p x : Z),
    2 <= p ->
    ElemCost ch p x <> 4611686018427387904 ->
    exists d, (d = -1 \/ d = 0 \/ d = 1) /\ Z.divide p (x + d) /\
              (if Z.eqb d 0 then 0 else ch) = ElemCost ch p x.
Proof.
  intros ch p x Hp Hne. unfold ElemCost in *.
  destruct (Z.eqb (x mod p) 0) eqn:E0.
  - exists 0. split; [right; left; reflexivity |].
    split; [| reflexivity].
    apply Z.eqb_eq in E0. replace (x + 0) with x by lia.
    apply Z.mod_divide; [lia | exact E0].
  - destruct (Z.eqb ((x - 1) mod p) 0) eqn:E1.
    + exists (-1). split; [left; reflexivity |].
      split; [| reflexivity].
      apply Z.eqb_eq in E1. replace (x + -1) with (x - 1) by lia.
      apply Z.mod_divide; [lia | exact E1].
    + destruct (Z.eqb ((x + 1) mod p) 0) eqn:E2.
      * exists 1. split; [right; right; reflexivity |].
        split; [| reflexivity].
        apply Z.eqb_eq in E2.
        apply Z.mod_divide; [lia | exact E2].
      * simpl in Hne. unfold INF in Hne. lia.
Qed.
Lemma elem_cost_le__cfp_step_06 :
  forall (ch p x d : Z),
    0 <= ch -> 2 <= p ->
    (d = -1 \/ d = 0 \/ d = 1) ->
    Z.divide p (x + d) ->
    ElemCost ch p x <= (if Z.eqb d 0 then 0 else ch).
Proof.
  intros ch p x d Hch Hp Hd Hdiv. unfold ElemCost.
  destruct Hd as [-> | [-> | ->]].
  - assert (E : (x - 1) mod p = 0).
    { apply Z.mod_divide; [lia |]. replace (x - 1) with (x + -1) by lia. exact Hdiv. }
    rewrite E. simpl. destruct (Z.eqb (x mod p) 0); simpl; lia.
  - assert (E : x mod p = 0).
    { apply Z.mod_divide; [lia |]. replace x with (x + 0) by lia. exact Hdiv. }
    rewrite E. simpl. lia.
  - assert (E : (x + 1) mod p = 0).
    { apply Z.mod_divide; [lia |]. exact Hdiv. }
    rewrite E. rewrite Bool.orb_true_r.
    destruct (Z.eqb (x mod p) 0); simpl; lia.
Qed.
Lemma partial_plan_cost_bound__cfp_step_06 :
  forall (a : list Z) (del ch p i l r c : Z),
    0 <= del -> del <= 1000000000 ->
    0 <= ch -> ch <= 1000000000 ->
    Zlength a <= 1000000 ->
    PartialPlanCost a del ch p i l r c ->
    0 <= c <= 2000000000000000.
Proof.
  intros a del ch p i l r c Hdel0 Hdel1 Hch0 Hch1 Hlen Hplan.
  unfold PartialPlanCost in Hplan.
  destruct Hplan as [H1 [H2 [H3 [H4 [delta [result [Hadj [Hdiv Hc]]]]]]]].
  unfold Adjusted in Hadj. destruct Hadj as [Hdlen [_ _]].
  rewrite Zlength_app in Hdlen.
  rewrite (Zlength_sublist 0 l a) in Hdlen by lia.
  rewrite (Zlength_sublist r i a) in Hdlen by lia.
  pose proof (count_nonneg__cfp_step_06 (-1) delta) as Hn1.
  pose proof (count_nonneg__cfp_step_06 1 delta) as Hn2.
  pose proof (count_pair_bound__cfp_step_06 delta) as Hpair.
  unfold ChangeCost in Hc.
  assert (Hb1 : (r - l) * del <= (r - l) * 1000000000) by nia.
  assert (Hb2 : (Count (-1) delta + Count 1 delta) * ch <= (l - 0 + (i - r)) * 1000000000) by nia.
  nia.
Qed.
Lemma dp_sets_bound__cfp_step_06 :
  forall (a : list Z) (del ch p i c : Z),
    0 <= del -> del <= 1000000000 ->
    0 <= ch -> ch <= 1000000000 ->
    Zlength a <= 1000000 ->
    (DPKeep a del ch p i c \/ DPCutFresh a del ch p i c \/
     DPCutAfterKeep a del ch p i c \/ DPAfter a del ch p i c) ->
    0 <= c <= 2000000000000000.
Proof.
  intros a del ch p i c Hd0 Hd1 Hc0 Hc1 Hlen Hin.
  unfold DPKeep, DPCutFresh, DPCutAfterKeep, DPAfter in Hin.
  destruct Hin as [H | [H | [[l0 [_ [_ H]]] | [l0 [r0 [_ H]]]]]].
  - exact (partial_plan_cost_bound__cfp_step_06 a del ch p i i i c
             Hd0 Hd1 Hc0 Hc1 Hlen H).
  - exact (partial_plan_cost_bound__cfp_step_06 a del ch p i 0 i c
             Hd0 Hd1 Hc0 Hc1 Hlen H).
  - exact (partial_plan_cost_bound__cfp_step_06 a del ch p i l0 i c
             Hd0 Hd1 Hc0 Hc1 Hlen H).
  - exact (partial_plan_cost_bound__cfp_step_06 a del ch p i l0 r0 c
             Hd0 Hd1 Hc0 Hc1 Hlen H).
Qed.
Lemma cfp_state_finite_bound__cfp_step_06 :
  forall (a : list Z) (del ch p i keep cutFresh cutAfterKeep after : Z),
    0 <= del -> del <= 1000000000 ->
    0 <= ch -> ch <= 1000000000 ->
    Zlength a <= 1000000 ->
    CostForPrimeState a del ch p i keep cutFresh cutAfterKeep after ->
    (keep <> 4611686018427387904 -> keep <= 2000000000000000) /\
    (cutFresh <> 4611686018427387904 -> cutFresh <= 2000000000000000) /\
    (cutAfterKeep <> 4611686018427387904 -> cutAfterKeep <= 2000000000000000) /\
    (after <> 4611686018427387904 -> after <= 2000000000000000).
Proof.
  intros a del ch p i keep cutFresh cutAfterKeep after Hd0 Hd1 Hc0 Hc1 Hlen Hst.
  unfold CostForPrimeState in Hst.
  destruct Hst as [Hk [Hf [Hca Haf]]].
  repeat split; intros Hne.
  - destruct (dp_value_char__cfp_step_06 (DPKeep a del ch p i) keep
      ltac:(intros c Hc; exact (dp_sets_bound__cfp_step_06 a del ch p i c
              Hd0 Hd1 Hc0 Hc1 Hlen (or_introl Hc))) Hk)
      as [[Hin _] | [Heq _]]; [| lia].
    pose proof (dp_sets_bound__cfp_step_06 a del ch p i keep Hd0 Hd1 Hc0 Hc1 Hlen
      (or_introl Hin)). lia.
  - destruct (dp_value_char__cfp_step_06 (DPCutFresh a del ch p i) cutFresh
      ltac:(intros c Hc; exact (dp_sets_bound__cfp_step_06 a del ch p i c
              Hd0 Hd1 Hc0 Hc1 Hlen (or_intror (or_introl Hc)))) Hf)
      as [[Hin _] | [Heq _]]; [| lia].
    pose proof (dp_sets_bound__cfp_step_06 a del ch p i cutFresh Hd0 Hd1 Hc0 Hc1 Hlen
      (or_intror (or_introl Hin))). lia.
  - destruct (dp_value_char__cfp_step_06 (DPCutAfterKeep a del ch p i) cutAfterKeep
      ltac:(intros c Hc; exact (dp_sets_bound__cfp_step_06 a del ch p i c
              Hd0 Hd1 Hc0 Hc1 Hlen (or_intror (or_intror (or_introl Hc))))) Hca)
      as [[Hin _] | [Heq _]]; [| lia].
    pose proof (dp_sets_bound__cfp_step_06 a del ch p i cutAfterKeep Hd0 Hd1 Hc0 Hc1 Hlen
      (or_intror (or_intror (or_introl Hin)))). lia.
  - destruct (dp_value_char__cfp_step_06 (DPAfter a del ch p i) after
      ltac:(intros c Hc; exact (dp_sets_bound__cfp_step_06 a del ch p i c
              Hd0 Hd1 Hc0 Hc1 Hlen (or_intror (or_intror (or_intror Hc))))) Haf)
      as [[Hin _] | [Heq _]]; [| lia].
    pose proof (dp_sets_bound__cfp_step_06 a del ch p i after Hd0 Hd1 Hc0 Hc1 Hlen
      (or_intror (or_intror (or_intror Hin)))). lia.
Qed.
Lemma dp_cut_fresh_set__cfp_step_06 :
  forall (a : list Z) (del ch p i c : Z),
    0 <= i -> i <= Zlength a ->
    (DPCutFresh a del ch p i c <-> c = i * del).
Proof.
  intros a del ch p i c Hi0 Hi1.
  unfold DPCutFresh, PartialPlanCost, ChangeCost. cbv beta.
  rewrite (sublist_empty__cfp_step_06 a 0).
  rewrite (sublist_empty__cfp_step_06 a i).
  simpl (nil ++ nil).
  split.
  - intros [_ [_ [_ [_ [delta [result [Hadj [_ Hc]]]]]]]].
    unfold Adjusted in Hadj. destruct Hadj as [Hdlen [_ _]].
    rewrite Zlength_nil in Hdlen.
    apply zlength_zero_nil__cfp_step_06 in Hdlen. subst delta.
    rewrite !count_nil__cfp_step_06 in Hc. lia.
  - intros ->.
    split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
    exists nil, nil.
    split; [| split].
    + unfold Adjusted. split; [reflexivity |]. split; [constructor | reflexivity].
    + constructor.
    + rewrite !count_nil__cfp_step_06. lia.
Qed.
Lemma dp_cut_fresh_value__cfp_step_06 :
  forall (a : list Z) (del ch p i v : Z),
    0 <= i -> i <= Zlength a -> 0 <= del ->
    i * del <= 2000000000000000 ->
    DPValue (DPCutFresh a del ch p i) v ->
    v = i * del.
Proof.
  intros a del ch p i v Hi0 Hi1 Hd0 Hb Hdp.
  destruct (dp_value_char__cfp_step_06 (DPCutFresh a del ch p i) v
    ltac:(intros c Hc; apply (dp_cut_fresh_set__cfp_step_06 a del ch p i c Hi0 Hi1) in Hc;
          nia) Hdp) as [[Hin _] | [Heq Hemp]].
  - apply (dp_cut_fresh_set__cfp_step_06 a del ch p i v Hi0 Hi1). exact Hin.
  - exfalso. apply (Hemp (i * del)).
    apply (dp_cut_fresh_set__cfp_step_06 a del ch p i (i * del) Hi0 Hi1). reflexivity.
Qed.
Lemma dp_cut_after_keep_zero_empty__cfp_step_06 :
  forall (a : list Z) (del ch p c : Z), ~ DPCutAfterKeep a del ch p 0 c.
Proof.
  intros a del ch p c H.
  unfold DPCutAfterKeep in H. destruct H as [l [H1 [H2 _]]]. lia.
Qed.
Lemma dp_cut_after_keep_zero_value__cfp_step_06 :
  forall (a : list Z) (del ch p v : Z),
    DPValue (DPCutAfterKeep a del ch p 0) v -> v = 4611686018427387904.
Proof.
  intros a del ch p v Hdp.
  destruct (dp_value_char__cfp_step_06 (DPCutAfterKeep a del ch p 0) v
    ltac:(intros c Hc; exfalso;
          exact (dp_cut_after_keep_zero_empty__cfp_step_06 a del ch p c Hc)) Hdp)
    as [[Hin _] | [Heq _]].
  - exfalso. exact (dp_cut_after_keep_zero_empty__cfp_step_06 a del ch p v Hin).
  - exact Heq.
Qed.
Lemma cfp_state_cut_fresh_finite__cfp_step_06 :
  forall (a : list Z) (del ch p i keep cutFresh cutAfterKeep after : Z),
    0 <= del -> del <= 1000000000 ->
    0 <= i -> i <= Zlength a -> Zlength a <= 1000000 ->
    CostForPrimeState a del ch p i keep cutFresh cutAfterKeep after ->
    cutFresh = i * del.
Proof.
  intros a del ch p i keep cutFresh cutAfterKeep after Hd0 Hd1 Hi0 Hi1 Hlen Hst.
  unfold CostForPrimeState in Hst. destruct Hst as [_ [Hf _]].
  apply (dp_cut_fresh_value__cfp_step_06 a del ch p i cutFresh Hi0 Hi1 Hd0); [nia | exact Hf].
Qed.
Lemma cfp_state_zero_cak_inf__cfp_step_06 :
  forall (a : list Z) (del ch p keep cutFresh cutAfterKeep after : Z),
    CostForPrimeState a del ch p 0 keep cutFresh cutAfterKeep after ->
    cutAfterKeep = 4611686018427387904.
Proof.
  intros a del ch p keep cutFresh cutAfterKeep after Hst.
  unfold CostForPrimeState in Hst. destruct Hst as [_ [_ [Hca _]]].
  exact (dp_cut_after_keep_zero_value__cfp_step_06 a del ch p cutAfterKeep Hca).
Qed.
Lemma combine_snoc__cfp_step_06 :
  forall (K D : list Z) (v d : Z),
    Zlength K = Zlength D ->
    combine (K ++ (v :: nil)) (D ++ (d :: nil)) = combine K D ++ ((v, d) :: nil).
Proof.
  induction K as [| x K IH]; intros D v d Hlen.
  - destruct D as [| y D].
    + simpl. reflexivity.
    + exfalso. rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg D). lia.
  - destruct D as [| y D].
    + exfalso. rewrite Zlength_nil, Zlength_cons in Hlen.
      pose proof (Zlength_nonneg K). lia.
    + simpl. f_equal. apply IH.
      rewrite !Zlength_cons in Hlen. lia.
Qed.
Lemma adjusted_snoc_intro__cfp_step_06 :
  forall (K : list Z) (v : Z) (D R : list Z) (d : Z),
    Adjusted K D R -> (d = -1 \/ d = 0 \/ d = 1) ->
    Adjusted (K ++ (v :: nil)) (D ++ (d :: nil)) (R ++ ((v + d) :: nil)).
Proof.
  intros K v D R d [Hlen [Hall Hres]] Hd.
  unfold Adjusted. split; [| split].
  - rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. lia.
  - apply Forall_app. split; [exact Hall |].
    constructor; [exact Hd | constructor].
  - rewrite combine_snoc__cfp_step_06 by lia.
    rewrite map_app. simpl. rewrite <- Hres. reflexivity.
Qed.
Lemma adjusted_snoc_elim__cfp_step_06 :
  forall (K : list Z) (v : Z) (delta result : list Z),
    Adjusted (K ++ (v :: nil)) delta result ->
    exists D d R,
      delta = D ++ (d :: nil) /\ result = R ++ ((v + d) :: nil) /\
      Adjusted K D R /\ (d = -1 \/ d = 0 \/ d = 1).
Proof.
  intros K v delta result [Hlen [Hall Hres]].
  rewrite Zlength_app in Hlen. rewrite Zlength_cons, Zlength_nil in Hlen.
  assert (Hne : delta <> nil).
  { intros ->. rewrite Zlength_nil in Hlen. pose proof (Zlength_nonneg K). lia. }
  destruct (exists_last Hne) as [D [d Hd]].
  subst delta.
  rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen.
  apply Forall_app in Hall. destruct Hall as [HallD Halld].
  assert (Hdval : d = -1 \/ d = 0 \/ d = 1) by (inversion Halld; auto).
  exists D, d, (map (fun q : Z * Z => fst q + snd q) (combine K D)).
  split; [reflexivity |].
  split.
  - rewrite Hres. rewrite combine_snoc__cfp_step_06 by lia.
    rewrite map_app. simpl. reflexivity.
  - split; [| exact Hdval].
    unfold Adjusted. split; [lia |]. split; [exact HallD | reflexivity].
Qed.
Lemma plan_snoc_iff__cfp_step_06 :
  forall (K : list Z) (v ch p c : Z),
    (exists delta result,
       Adjusted (K ++ (v :: nil)) delta result /\
       Forall (fun y => Z.divide p y) result /\
       c = Count (-1) delta * ch + Count 1 delta * ch)
    <->
    (exists m d,
       (exists D R, Adjusted K D R /\ Forall (fun y => Z.divide p y) R /\
          m = Count (-1) D * ch + Count 1 D * ch) /\
       (d = -1 \/ d = 0 \/ d = 1) /\ Z.divide p (v + d) /\
       c = m + (if Z.eqb d 0 then 0 else ch)).
Proof.
  intros K v ch p c. split.
  - intros [delta [result [Hadj [Hdiv Hc]]]].
    destruct (adjusted_snoc_elim__cfp_step_06 K v delta result Hadj)
      as [D [d [R [Hde [Hre [HadjKD Hd]]]]]].
    subst delta result.
    apply Forall_app in Hdiv. destruct Hdiv as [HdivR Hdivd].
    assert (Hdv : Z.divide p (v + d)) by (inversion Hdivd; auto).
    exists (Count (-1) D * ch + Count 1 D * ch), d.
    split; [exists D, R; auto |].
    split; [exact Hd |].
    split; [exact Hdv |].
    rewrite !count_snoc__cfp_step_06 in Hc.
    destruct Hd as [-> | [-> | ->]]; simpl in Hc |- *.
    + destruct (prop_dec ((-1) = -1)) as [_ | Hn]; [| exfalso; apply Hn; reflexivity].
      destruct (prop_dec ((-1) = 1)) as [Hn | _]; [exfalso; lia |].
      lia.
    + destruct (prop_dec (0 = -1)) as [Hn | _]; [exfalso; lia |].
      destruct (prop_dec (0 = 1)) as [Hn | _]; [exfalso; lia |].
      lia.
    + destruct (prop_dec (1 = -1)) as [Hn | _]; [exfalso; lia |].
      destruct (prop_dec (1 = 1)) as [_ | Hn]; [| exfalso; apply Hn; reflexivity].
      lia.
  - intros [m [d [[D [R [HadjKD [HdivR Hm]]]] [Hd [Hdv Hc]]]]].
    exists (D ++ (d :: nil)), (R ++ ((v + d) :: nil)).
    split; [apply adjusted_snoc_intro__cfp_step_06; assumption |].
    split.
    + apply Forall_app. split; [exact HdivR | constructor; [exact Hdv | constructor]].
    + rewrite !count_snoc__cfp_step_06.
      destruct Hd as [-> | [-> | ->]]; simpl in Hc |- *.
      * destruct (prop_dec ((-1) = -1)) as [_ | Hn]; [| exfalso; apply Hn; reflexivity].
        destruct (prop_dec ((-1) = 1)) as [Hn | _]; [exfalso; lia |].
        lia.
      * destruct (prop_dec (0 = -1)) as [Hn | _]; [exfalso; lia |].
        destruct (prop_dec (0 = 1)) as [Hn | _]; [exfalso; lia |].
        lia.
      * destruct (prop_dec (1 = -1)) as [Hn | _]; [exfalso; lia |].
        destruct (prop_dec (1 = 1)) as [_ | Hn]; [| exfalso; apply Hn; reflexivity].
        lia.
Qed.
Lemma sublist_snoc__cfp_step_06 :
  forall (a : list Z) (r i : Z),
    0 <= r -> r <= i -> i < Zlength a ->
    sublist r (i + 1) a = sublist r i a ++ (Znth i a 0 :: nil).
Proof.
  intros a r i Hr Hri Hi.
  rewrite (sublist_split r (i + 1) i a) by lia.
  f_equal.
  apply (@sublist_single Z 0 i a). lia.
Qed.
Lemma ppc_extend_iff__cfp_step_06 :
  forall (a : list Z) (del ch p i l r c : Z),
    0 <= l -> l <= r -> r <= i -> i < Zlength a ->
    (PartialPlanCost a del ch p (i + 1) l r c <->
     exists m d, PartialPlanCost a del ch p i l r m /\
                 (d = -1 \/ d = 0 \/ d = 1) /\ Z.divide p (Znth i a 0 + d) /\
                 c = m + (if Z.eqb d 0 then 0 else ch)).
Proof.
  intros a del ch p i l r c Hl Hlr Hri Hia.
  unfold PartialPlanCost, ChangeCost.
  rewrite (sublist_snoc__cfp_step_06 a r i) by lia.
  rewrite app_assoc.
  split.
  - intros [_ [_ [_ [_ [delta [result [Hadj [Hdiv Hc]]]]]]]].
    assert (Hpre : exists delta0 result0,
              Adjusted ((sublist 0 l a ++ sublist r i a) ++ (Znth i a 0 :: nil)) delta0 result0 /\
              Forall (fun y => Z.divide p y) result0 /\
              c - (r - l) * del = Count (-1) delta0 * ch + Count 1 delta0 * ch).
    { exists delta, result. split; [exact Hadj |]. split; [exact Hdiv |]. lia. }
    apply (plan_snoc_iff__cfp_step_06 (sublist 0 l a ++ sublist r i a) (Znth i a 0) ch p) in Hpre.
    destruct Hpre as [m0 [d [[D [R [HadjD [HdivR Hm0]]]] [Hd [Hdv Hceq]]]]].
    exists ((r - l) * del + m0), d.
    split.
    + split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
      exists D, R. split; [exact HadjD |]. split; [exact HdivR |]. lia.
    + split; [exact Hd |]. split; [exact Hdv |]. lia.
  - intros [m [d [[_ [_ [_ [_ [D [R [HadjD [HdivR Hm]]]]]]]] [Hd [Hdv Hc]]]]].
    assert (Hpost : exists m0 d0,
              (exists D0 R0, Adjusted (sublist 0 l a ++ sublist r i a) D0 R0 /\
                 Forall (fun y => Z.divide p y) R0 /\
                 m0 = Count (-1) D0 * ch + Count 1 D0 * ch) /\
              (d0 = -1 \/ d0 = 0 \/ d0 = 1) /\ Z.divide p (Znth i a 0 + d0) /\
              c - (r - l) * del = m0 + (if Z.eqb d0 0 then 0 else ch)).
    { exists (m - (r - l) * del), d.
      split; [exists D, R; split; [exact HadjD |]; split; [exact HdivR |]; lia |].
      split; [exact Hd |]. split; [exact Hdv |]. lia. }
    apply (plan_snoc_iff__cfp_step_06 (sublist 0 l a ++ sublist r i a) (Znth i a 0) ch p) in Hpost.
    destruct Hpost as [delta [result [Hadj [Hdiv Hceq]]]].
    split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
    exists delta, result. split; [exact Hadj |]. split; [exact Hdiv |]. lia.
Qed.
Lemma ppc_cut_kept__cfp_step_06 :
  forall (a : list Z) (del ch p j l c : Z),
    0 <= l -> l <= j -> j <= Zlength a ->
    (PartialPlanCost a del ch p j l j c <->
     (exists delta result, Adjusted (sublist 0 l a) delta result /\
        Forall (fun y => Z.divide p y) result /\
        c = (j - l) * del + Count (-1) delta * ch + Count 1 delta * ch)).
Proof.
  intros a del ch p j l c Hl Hlj Hja.
  unfold PartialPlanCost, ChangeCost.
  rewrite (sublist_empty__cfp_step_06 a j).
  rewrite app_nil_r.
  split.
  - intros [_ [_ [_ [_ H]]]]. exact H.
  - intros H. split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |]. exact H.
Qed.
Lemma dp_keep_step_iff__cfp_step_06 :
  forall (a : list Z) (del ch p i c : Z),
    0 <= i -> i < Zlength a ->
    (DPKeep a del ch p (i + 1) c <->
     exists m d, DPKeep a del ch p i m /\ (d = -1 \/ d = 0 \/ d = 1) /\
                 Z.divide p (Znth i a 0 + d) /\
                 c = m + (if Z.eqb d 0 then 0 else ch)).
Proof.
  intros a del ch p i c Hi0 Hia.
  unfold DPKeep. cbv beta.
  rewrite (ppc_cut_kept__cfp_step_06 a del ch p (i + 1) (i + 1) c) by lia.
  rewrite (sublist_snoc__cfp_step_06 a 0 i) by lia.
  replace ((i + 1) - (i + 1)) with 0 by lia.
  split.
  - intros [delta [result [Hadj [Hdiv Hc]]]].
    assert (Hpre : exists delta0 result0,
              Adjusted (sublist 0 i a ++ (Znth i a 0 :: nil)) delta0 result0 /\
              Forall (fun y => Z.divide p y) result0 /\
              c = Count (-1) delta0 * ch + Count 1 delta0 * ch).
    { exists delta, result. split; [exact Hadj |]. split; [exact Hdiv |]. lia. }
    apply (plan_snoc_iff__cfp_step_06 (sublist 0 i a) (Znth i a 0) ch p) in Hpre.
    destruct Hpre as [m0 [d [[D [R [HadjD [HdivR Hm0]]]] [Hd [Hdv Hceq]]]]].
    exists m0, d.
    split.
    + apply (ppc_cut_kept__cfp_step_06 a del ch p i i m0); [lia | lia | lia |].
      exists D, R. split; [exact HadjD |]. split; [exact HdivR |].
      replace (i - i) with 0 by lia. lia.
    + split; [exact Hd |]. split; [exact Hdv |]. exact Hceq.
  - intros [m [d [Hm [Hd [Hdv Hc]]]]].
    apply (ppc_cut_kept__cfp_step_06 a del ch p i i m) in Hm; [| lia | lia | lia].
    destruct Hm as [D [R [HadjD [HdivR Hmeq]]]].
    assert (Hpost : exists m0 d0,
              (exists D0 R0, Adjusted (sublist 0 i a) D0 R0 /\
                 Forall (fun y => Z.divide p y) R0 /\
                 m0 = Count (-1) D0 * ch + Count 1 D0 * ch) /\
              (d0 = -1 \/ d0 = 0 \/ d0 = 1) /\ Z.divide p (Znth i a 0 + d0) /\
              c = m0 + (if Z.eqb d0 0 then 0 else ch)).
    { exists m, d.
      split; [exists D, R; split; [exact HadjD |]; split; [exact HdivR |];
              replace (i - i) with 0 in Hmeq by lia; lia |].
      split; [exact Hd |]. split; [exact Hdv |]. exact Hc. }
    apply (plan_snoc_iff__cfp_step_06 (sublist 0 i a) (Znth i a 0) ch p) in Hpost.
    destruct Hpost as [delta [result [Hadj [Hdiv Hceq]]]].
    exists delta, result. split; [exact Hadj |]. split; [exact Hdiv |]. lia.
Qed.
Lemma dp_cak_step_iff__cfp_step_06 :
  forall (a : list Z) (del ch p i c : Z),
    1 <= i -> i < Zlength a ->
    (DPCutAfterKeep a del ch p (i + 1) c <->
     exists m, (DPCutAfterKeep a del ch p i m \/ DPKeep a del ch p i m) /\ c = m + del).
Proof.
  intros a del ch p i c Hi Hia.
  unfold DPCutAfterKeep, DPKeep. cbv beta.
  split.
  - intros [l [Hl1 [Hl2 Hppc]]].
    apply (ppc_cut_kept__cfp_step_06 a del ch p (i + 1) l c) in Hppc; [| lia | lia | lia].
    destruct Hppc as [delta [result [Hadj [Hdiv Hc]]]].
    assert (Hring : (i + 1 - l) * del = (i - l) * del + del) by ring.
    exists ((i - l) * del + Count (-1) delta * ch + Count 1 delta * ch).
    split; [| lia].
    destruct (Z_lt_le_dec l i) as [Hlt | Hge].
    + left. exists l. split; [lia |]. split; [lia |].
      apply (ppc_cut_kept__cfp_step_06 a del ch p i l
               ((i - l) * del + Count (-1) delta * ch + Count 1 delta * ch));
        [lia | lia | lia |].
      exists delta, result. split; [exact Hadj |]. split; [exact Hdiv |]. reflexivity.
    + assert (Hli : l = i) by lia. subst l.
      right.
      apply (ppc_cut_kept__cfp_step_06 a del ch p i i
               ((i - i) * del + Count (-1) delta * ch + Count 1 delta * ch));
        [lia | lia | lia |].
      exists delta, result. split; [exact Hadj |]. split; [exact Hdiv |]. reflexivity.
  - intros [m [[Hcak | Hkeep] Hc]].
    + destruct Hcak as [l [Hl1 [Hl2 Hppc]]].
      apply (ppc_cut_kept__cfp_step_06 a del ch p i l m) in Hppc; [| lia | lia | lia].
      destruct Hppc as [delta [result [Hadj [Hdiv Hm]]]].
      assert (Hring : (i + 1 - l) * del = (i - l) * del + del) by ring.
      exists l. split; [lia |]. split; [lia |].
      apply (ppc_cut_kept__cfp_step_06 a del ch p (i + 1) l c); [lia | lia | lia |].
      exists delta, result. split; [exact Hadj |]. split; [exact Hdiv |]. lia.
    + apply (ppc_cut_kept__cfp_step_06 a del ch p i i m) in Hkeep; [| lia | lia | lia].
      destruct Hkeep as [delta [result [Hadj [Hdiv Hm]]]].
      assert (Hring : (i + 1 - i) * del = (i - i) * del + del) by ring.
      exists i. split; [lia |]. split; [lia |].
      apply (ppc_cut_kept__cfp_step_06 a del ch p (i + 1) i c); [lia | lia | lia |].
      exists delta, result. split; [exact Hadj |]. split; [exact Hdiv |]. lia.
Qed.
Lemma dp_union_iff__cfp_step_06 :
  forall (a : list Z) (del ch p i m : Z),
    (DPAfter a del ch p i m \/ DPCutFresh a del ch p i m \/
     DPCutAfterKeep a del ch p i m \/ DPKeep a del ch p i m)
    <-> (exists l r, 0 <= l /\ l <= r /\ r <= i /\ PartialPlanCost a del ch p i l r m).
Proof.
  intros a del ch p i m.
  unfold DPAfter, DPCutFresh, DPCutAfterKeep, DPKeep. cbv beta.
  split.
  - intros [[l [r [_ Hppc]]] | [Hppc | [[l [_ [_ Hppc]]] | Hppc]]].
    + exists l, r. pose proof Hppc as Hb. destruct Hb as [H1 [H2 [H3 _]]].
      split; [lia |]. split; [lia |]. split; [lia | exact Hppc].
    + exists 0, i. pose proof Hppc as Hb. destruct Hb as [H1 [H2 [H3 _]]].
      split; [lia |]. split; [lia |]. split; [lia | exact Hppc].
    + exists l, i. pose proof Hppc as Hb. destruct Hb as [H1 [H2 [H3 _]]].
      split; [lia |]. split; [lia |]. split; [lia | exact Hppc].
    + exists i, i. pose proof Hppc as Hb. destruct Hb as [H1 [H2 [H3 _]]].
      split; [lia |]. split; [lia |]. split; [lia | exact Hppc].
  - intros [l [r [Hl [Hlr [Hri Hppc]]]]].
    destruct (Z_lt_le_dec r i) as [Hlt | Hge].
    + left. exists l, r. split; [lia | exact Hppc].
    + assert (Hre : r = i) by lia. subst r.
      destruct (Z.eq_dec l 0) as [Hl0 | Hl0].
      * subst l. right. left. exact Hppc.
      * destruct (Z_lt_le_dec l i) as [Hlt2 | Hge2].
        -- right. right. left. exists l. split; [lia |]. split; [lia | exact Hppc].
        -- assert (Hli : l = i) by lia. subst l.
           right. right. right. exact Hppc.
Qed.
Lemma dp_after_step_iff__cfp_step_06 :
  forall (a : list Z) (del ch p i c : Z),
    0 <= i -> i < Zlength a ->
    (DPAfter a del ch p (i + 1) c <->
     exists m d, (DPAfter a del ch p i m \/ DPCutFresh a del ch p i m \/
                  DPCutAfterKeep a del ch p i m \/ DPKeep a del ch p i m) /\
                 (d = -1 \/ d = 0 \/ d = 1) /\ Z.divide p (Znth i a 0 + d) /\
                 c = m + (if Z.eqb d 0 then 0 else ch)).
Proof.
  intros a del ch p i c Hi0 Hia.
  split.
  - intros Hafter.
    unfold DPAfter in Hafter. cbv beta in Hafter.
    destruct Hafter as [l [r [Hr Hppc]]].
    pose proof Hppc as Hppc2. destruct Hppc2 as [Hl [Hlr [_ _]]].
    apply (ppc_extend_iff__cfp_step_06 a del ch p i l r c) in Hppc;
      [| lia | lia | lia | lia].
    destruct Hppc as [m [d [Hm [Hd [Hdv Hc]]]]].
    exists m, d. split; [| split; [exact Hd | split; [exact Hdv | exact Hc]]].
    apply dp_union_iff__cfp_step_06. exists l, r.
    pose proof Hm as Hm2. destruct Hm2 as [H1 [H2 [H3 _]]].
    split; [lia |]. split; [lia |]. split; [lia | exact Hm].
  - intros [m [d [Hunion [Hd [Hdv Hc]]]]].
    apply dp_union_iff__cfp_step_06 in Hunion.
    destruct Hunion as [l [r [Hl [Hlr [Hri Hm]]]]].
    unfold DPAfter. cbv beta.
    exists l, r. split; [lia |].
    apply (ppc_extend_iff__cfp_step_06 a del ch p i l r c); [lia | lia | lia | lia |].
    exists m, d. split; [exact Hm |]. split; [exact Hd |]. split; [exact Hdv | exact Hc].
Qed.
Lemma dp_value_min__cfp_step_06 :
  forall (S : Z -> Prop) (v c : Z),
    (forall x, S x -> 0 <= x <= 2000000000000000) ->
    DPValue S v -> S c -> v <= c.
Proof.
  intros S v c Hb Hdp Hc.
  destruct (dp_value_char__cfp_step_06 S v Hb Hdp) as [[_ Hmin] | [_ Hemp]].
  - apply Hmin. exact Hc.
  - exfalso. exact (Hemp c Hc).
Qed.
Lemma dp_value_in__cfp_step_06 :
  forall (S : Z -> Prop) (v : Z),
    (forall x, S x -> 0 <= x <= 2000000000000000) ->
    DPValue S v -> v <> 4611686018427387904 -> S v.
Proof.
  intros S v Hb Hdp Hne.
  destruct (dp_value_char__cfp_step_06 S v Hb Hdp) as [[Hin _] | [Heq _]].
  - exact Hin.
  - exfalso. apply Hne. exact Heq.
Qed.
Lemma dp_value_empty_of_inf__cfp_step_06 :
  forall (S : Z -> Prop) (v : Z),
    (forall x, S x -> 0 <= x <= 2000000000000000) ->
    DPValue S v -> v = 4611686018427387904 -> forall c, ~ S c.
Proof.
  intros S v Hb Hdp Heq c Hc.
  destruct (dp_value_char__cfp_step_06 S v Hb Hdp) as [[Hin _] | [_ Hemp]].
  - subst v. pose proof (Hb _ Hin). lia.
  - exact (Hemp c Hc).
Qed.
Lemma dp_value_keep_step_fin__cfp_step_06 :
  forall (a : list Z) (del ch p i keep : Z),
    0 <= del -> del <= 1000000000 -> 0 <= ch -> ch <= 1000000000 ->
    Zlength a <= 1000000 -> 0 <= i -> i < Zlength a -> 2 <= p ->
    ElemCost ch p (Znth i a 0) <> 4611686018427387904 ->
    keep <> 4611686018427387904 ->
    DPValue (DPKeep a del ch p i) keep ->
    DPValue (DPKeep a del ch p (i + 1)) (keep + ElemCost ch p (Znth i a 0)).
Proof.
  intros a del ch p i keep Hd0 Hd1 Hc0 Hc1 Hlen Hi0 Hia Hp Hcost Hkne Hk.
  assert (Bk : forall x, DPKeep a del ch p i x -> 0 <= x <= 2000000000000000)
    by (intros x Hx; exact (dp_sets_bound__cfp_step_06 a del ch p i x
          Hd0 Hd1 Hc0 Hc1 Hlen (or_introl Hx))).
  pose proof (dp_value_in__cfp_step_06 _ _ Bk Hk Hkne) as Hkin.
  destruct (elem_cost_witness__cfp_step_06 ch p (Znth i a 0) Hp Hcost)
    as [d [Hd [Hdv Hprice]]].
  pose proof (elem_cost_bound__cfp_step_06 ch p (Znth i a 0) Hc0 Hcost) as Hecb.
  pose proof (Bk _ Hkin) as Hkb.
  apply dp_value_mem__cfp_step_06.
  - apply (dp_keep_step_iff__cfp_step_06 a del ch p i _ Hi0 Hia).
    exists keep, d. split; [exact Hkin |]. split; [exact Hd |]. split; [exact Hdv |].
    rewrite Hprice. reflexivity.
  - intros c Hc.
    apply (dp_keep_step_iff__cfp_step_06 a del ch p i c Hi0 Hia) in Hc.
    destruct Hc as [m [d2 [Hm [Hd2 [Hdv2 Hceq]]]]].
    pose proof (dp_value_min__cfp_step_06 _ _ _ Bk Hk Hm) as Hle.
    pose proof (elem_cost_le__cfp_step_06 ch p (Znth i a 0) d2 Hc0 Hp Hd2 Hdv2) as Hle2.
    lia.
  - lia.
Qed.
Lemma dp_value_keep_step_inf__cfp_step_06 :
  forall (a : list Z) (del ch p i keep : Z),
    0 <= del -> del <= 1000000000 -> 0 <= ch -> ch <= 1000000000 ->
    Zlength a <= 1000000 -> 0 <= i -> i < Zlength a ->
    keep = 4611686018427387904 ->
    DPValue (DPKeep a del ch p i) keep ->
    DPValue (DPKeep a del ch p (i + 1)) 4611686018427387904.
Proof.
  intros a del ch p i keep Hd0 Hd1 Hc0 Hc1 Hlen Hi0 Hia Hkeq Hk.
  assert (Bk : forall x, DPKeep a del ch p i x -> 0 <= x <= 2000000000000000)
    by (intros x Hx; exact (dp_sets_bound__cfp_step_06 a del ch p i x
          Hd0 Hd1 Hc0 Hc1 Hlen (or_introl Hx))).
  pose proof (dp_value_empty_of_inf__cfp_step_06 _ _ Bk Hk Hkeq) as Hemp.
  apply dp_value_empty__cfp_step_06.
  intros c Hc.
  apply (dp_keep_step_iff__cfp_step_06 a del ch p i c Hi0 Hia) in Hc.
  destruct Hc as [m [d [Hm _]]]. exact (Hemp m Hm).
Qed.
Lemma dp_value_cut_fresh_step__cfp_step_06 :
  forall (a : list Z) (del ch p i cf : Z),
    0 <= del -> del <= 1000000000 ->
    Zlength a <= 1000000 -> 0 <= i -> i < Zlength a ->
    DPValue (DPCutFresh a del ch p i) cf ->
    DPValue (DPCutFresh a del ch p (i + 1)) (cf + del).
Proof.
  intros a del ch p i cf Hd0 Hd1 Hlen Hi0 Hia Hf.
  pose proof (dp_cut_fresh_value__cfp_step_06 a del ch p i cf ltac:(lia) ltac:(lia) Hd0
                ltac:(nia) Hf) as Hcf.
  assert (Hring : cf + del = (i + 1) * del) by (subst cf; ring).
  rewrite Hring.
  apply dp_value_mem__cfp_step_06.
  - apply (dp_cut_fresh_set__cfp_step_06 a del ch p (i + 1) ((i + 1) * del)
             ltac:(lia) ltac:(lia)). reflexivity.
  - intros c Hc.
    apply (dp_cut_fresh_set__cfp_step_06 a del ch p (i + 1) c ltac:(lia) ltac:(lia)) in Hc.
    lia.
  - nia.
Qed.
Lemma dp_value_cak_step__cfp_step_06 :
  forall (a : list Z) (del ch p i keep cak : Z),
    0 <= del -> del <= 1000000000 -> 0 <= ch -> ch <= 1000000000 ->
    Zlength a <= 1000000 -> 1 <= i -> i < Zlength a ->
    DPValue (DPKeep a del ch p i) keep ->
    DPValue (DPCutAfterKeep a del ch p i) cak ->
    cak <> 4611686018427387904 -> cak <= keep ->
    DPValue (DPCutAfterKeep a del ch p (i + 1)) (cak + del).
Proof.
  intros a del ch p i keep cak Hd0 Hd1 Hc0 Hc1 Hlen Hi1 Hia Hk Hca Hcane Hle.
  assert (Bk : forall x, DPKeep a del ch p i x -> 0 <= x <= 2000000000000000)
    by (intros x Hx; exact (dp_sets_bound__cfp_step_06 a del ch p i x
          Hd0 Hd1 Hc0 Hc1 Hlen (or_introl Hx))).
  assert (Bc : forall x, DPCutAfterKeep a del ch p i x -> 0 <= x <= 2000000000000000)
    by (intros x Hx; exact (dp_sets_bound__cfp_step_06 a del ch p i x
          Hd0 Hd1 Hc0 Hc1 Hlen (or_intror (or_intror (or_introl Hx))))).
  pose proof (dp_value_in__cfp_step_06 _ _ Bc Hca Hcane) as Hcain.
  pose proof (Bc _ Hcain) as Hcab.
  apply dp_value_mem__cfp_step_06.
  - apply (dp_cak_step_iff__cfp_step_06 a del ch p i _ Hi1 Hia).
    exists cak. split; [left; exact Hcain | reflexivity].
  - intros c Hc.
    apply (dp_cak_step_iff__cfp_step_06 a del ch p i c Hi1 Hia) in Hc.
    destruct Hc as [m [[Hm | Hm] Hceq]].
    + pose proof (dp_value_min__cfp_step_06 _ _ _ Bc Hca Hm). lia.
    + pose proof (dp_value_min__cfp_step_06 _ _ _ Bk Hk Hm). lia.
  - lia.
Qed.
Lemma dp_value_after_step__cfp_step_06 :
  forall (a : list Z) (del ch p i keep cf cak af : Z),
    0 <= del -> del <= 1000000000 -> 0 <= ch -> ch <= 1000000000 ->
    Zlength a <= 1000000 -> 0 <= i -> i < Zlength a -> 2 <= p ->
    DPValue (DPKeep a del ch p i) keep ->
    DPValue (DPCutFresh a del ch p i) cf ->
    DPValue (DPCutAfterKeep a del ch p i) cak ->
    DPValue (DPAfter a del ch p i) af ->
    ElemCost ch p (Znth i a 0) <> 4611686018427387904 ->
    af <> 4611686018427387904 ->
    af <= keep -> af <= cf -> af <= cak ->
    DPValue (DPAfter a del ch p (i + 1)) (af + ElemCost ch p (Znth i a 0)).
Proof.
  intros a del ch p i keep cf cak af Hd0 Hd1 Hc0 Hc1 Hlen Hi0 Hia Hp
         Hk Hf Hca Haf Hcost Hafne Hlk Hlf Hlc.
  assert (Bk : forall x, DPKeep a del ch p i x -> 0 <= x <= 2000000000000000)
    by (intros x Hx; exact (dp_sets_bound__cfp_step_06 a del ch p i x
          Hd0 Hd1 Hc0 Hc1 Hlen (or_introl Hx))).
  assert (Bf : forall x, DPCutFresh a del ch p i x -> 0 <= x <= 2000000000000000)
    by (intros x Hx; exact (dp_sets_bound__cfp_step_06 a del ch p i x
          Hd0 Hd1 Hc0 Hc1 Hlen (or_intror (or_introl Hx)))).
  assert (Bc : forall x, DPCutAfterKeep a del ch p i x -> 0 <= x <= 2000000000000000)
    by (intros x Hx; exact (dp_sets_bound__cfp_step_06 a del ch p i x
          Hd0 Hd1 Hc0 Hc1 Hlen (or_intror (or_intror (or_introl Hx))))).
  assert (Ba : forall x, DPAfter a del ch p i x -> 0 <= x <= 2000000000000000)
    by (intros x Hx; exact (dp_sets_bound__cfp_step_06 a del ch p i x
          Hd0 Hd1 Hc0 Hc1 Hlen (or_intror (or_intror (or_intror Hx))))).
  pose proof (dp_value_in__cfp_step_06 _ _ Ba Haf Hafne) as Hafin.
  pose proof (Ba _ Hafin) as Hafb.
  destruct (elem_cost_witness__cfp_step_06 ch p (Znth i a 0) Hp Hcost)
    as [d [Hd [Hdv Hprice]]].
  pose proof (elem_cost_bound__cfp_step_06 ch p (Znth i a 0) Hc0 Hcost) as Hecb.
  apply dp_value_mem__cfp_step_06.
  - apply (dp_after_step_iff__cfp_step_06 a del ch p i _ Hi0 Hia).
    exists af, d. split; [left; exact Hafin |].
    split; [exact Hd |]. split; [exact Hdv |]. rewrite Hprice. reflexivity.
  - intros c Hc.
    apply (dp_after_step_iff__cfp_step_06 a del ch p i c Hi0 Hia) in Hc.
    destruct Hc as [m [d2 [Hm [Hd2 [Hdv2 Hceq]]]]].
    pose proof (elem_cost_le__cfp_step_06 ch p (Znth i a 0) d2 Hc0 Hp Hd2 Hdv2) as Hle2.
    assert (Hafm : af <= m).
    { destruct Hm as [Hm | [Hm | [Hm | Hm]]].
      - exact (dp_value_min__cfp_step_06 _ _ _ Ba Haf Hm).
      - pose proof (dp_value_min__cfp_step_06 _ _ _ Bf Hf Hm). lia.
      - pose proof (dp_value_min__cfp_step_06 _ _ _ Bc Hca Hm). lia.
      - pose proof (dp_value_min__cfp_step_06 _ _ _ Bk Hk Hm). lia. }
    lia.
  - lia.
Qed.
Lemma cfp_state_step__cfp_step_06 :
  forall (a : list Z) (del ch p i keep cf cak af cost : Z),
    0 <= del -> del <= 1000000000 -> 0 <= ch -> ch <= 1000000000 ->
    Zlength a <= 1000000 -> 1 <= i -> i < Zlength a -> 2 <= p ->
    cost = ElemCost ch p (Znth i a 0) ->
    cost <> 4611686018427387904 ->
    keep <> 4611686018427387904 ->
    cak <> 4611686018427387904 ->
    af <> 4611686018427387904 ->
    cak <= keep -> af <= keep -> af <= cf -> af <= cak ->
    CostForPrimeState a del ch p i keep cf cak af ->
    CostForPrimeState a del ch p (i + 1) (keep + cost) (cf + del) (cak + del) (af + cost).
Proof.
  intros a del ch p i keep cf cak af cost Hd0 Hd1 Hc0 Hc1 Hlen Hi1 Hia Hp
         Hcost Hcne Hkne Hcane Hafne Hck Hak Haf1 Haf2 Hst.
  destruct Hst as [Hk [Hf [Hca Ha]]].
  subst cost.
  unfold CostForPrimeState. split; [| split; [| split]].
  - apply dp_value_keep_step_fin__cfp_step_06 with (keep := keep); try assumption; try lia.
  - apply dp_value_cut_fresh_step__cfp_step_06 with (ch := ch) (p := p); try assumption; try lia.
  - apply dp_value_cak_step__cfp_step_06 with (keep := keep); try assumption; try lia.
  - apply dp_value_after_step__cfp_step_06 with (keep := keep) (cf := cf) (cak := cak); try assumption; try lia.
Qed.
Lemma cfp_state_step_inf_keep__cfp_step_06 :
  forall (a : list Z) (del ch p i keep cf cak af cost : Z),
    0 <= del -> del <= 1000000000 -> 0 <= ch -> ch <= 1000000000 ->
    Zlength a <= 1000000 -> 1 <= i -> i < Zlength a -> 2 <= p ->
    cost = ElemCost ch p (Znth i a 0) ->
    cost <> 4611686018427387904 ->
    keep = 4611686018427387904 ->
    cak <> 4611686018427387904 ->
    af <> 4611686018427387904 ->
    cak <= keep -> af <= keep -> af <= cf -> af <= cak ->
    CostForPrimeState a del ch p i keep cf cak af ->
    CostForPrimeState a del ch p (i + 1) 4611686018427387904
      (cf + del) (cak + del) (af + cost).
Proof.
  intros a del ch p i keep cf cak af cost Hd0 Hd1 Hc0 Hc1 Hlen Hi1 Hia Hp
         Hcost Hcne Hkeq Hcane Hafne Hck Hak Haf1 Haf2 Hst.
  destruct Hst as [Hk [Hf [Hca Ha]]].
  subst cost.
  unfold CostForPrimeState. split; [| split; [| split]].
  - apply dp_value_keep_step_inf__cfp_step_06 with (keep := keep); try assumption; try lia.
  - apply dp_value_cut_fresh_step__cfp_step_06 with (ch := ch) (p := p); try assumption; try lia.
  - apply dp_value_cak_step__cfp_step_06 with (keep := keep); try assumption; try lia.
  - apply dp_value_after_step__cfp_step_06 with (keep := keep) (cf := cf) (cak := cak); try assumption; try lia.
Qed.
Lemma dpvalue_le_mem__cfp_step_07 : forall (S : Z -> Prop) (v c : Z),
  DPValue S v -> S c -> v <= c.
Proof.
  intros S v c HD Hc.
  unfold DPValue, min_value_of_subset_with_default in HD.
  destruct HD as [[[a [[Ha Hmin] Heq]] Hle] | [Hall Heq]].
  - subst v. apply (Hmin c). exact Hc.
  - subst v. apply (Hall c). exact Hc.
Qed.
Lemma dpvalue_empty__cfp_step_07 : forall (S : Z -> Prop) (v : Z),
  DPValue S v -> (forall c, ~ S c) -> v = INF.
Proof.
  intros S v HD Hemp.
  unfold DPValue, min_value_of_subset_with_default in HD.
  destruct HD as [[[a [[Ha Hmin] Heq]] Hle] | [Hall Heq]].
  - exfalso. apply (Hemp a). exact Ha.
  - exact Heq.
Qed.
Lemma dpvalue_fin_mem__cfp_step_07 : forall (S : Z -> Prop) (v : Z),
  DPValue S v -> v <> INF -> S v.
Proof.
  intros S v HD Hne.
  unfold DPValue, min_value_of_subset_with_default in HD.
  destruct HD as [[[a [[Ha Hmin] Heq]] Hle] | [Hall Heq]].
  - subst v. exact Ha.
  - contradiction.
Qed.
Lemma dpvalue_intro__cfp_step_07 : forall (S : Z -> Prop) (v : Z),
  S v -> (forall c, S c -> v <= c) -> v <= INF -> DPValue S v.
Proof.
  intros S v Hv Hmin Hle.
  unfold DPValue, min_value_of_subset_with_default.
  left. split; [ | exact Hle].
  exists v. split; [ split | reflexivity].
  - exact Hv.
  - intros b Hb. apply Hmin. exact Hb.
Qed.
Lemma card_as_len__cfp_step_07 : forall (A : Type) (P : A -> Prop) (HP : Finite P),
  @set_card A P HP = Zlength (@enum A P HP).
Proof.
  intros A P HP. unfold set_card, sum.
  induction (@enum A P HP) as [|a l IH].
  - rewrite Zlength_nil. reflexivity.
  - rewrite Zlength_cons. cbn [fold_right]. rewrite IH. lia.
Qed.
Lemma card_le__cfp_step_07 : forall (A : Type) (P Q : A -> Prop) (HP : Finite P) (HQ : Finite Q),
  (forall x, Q x -> P x) -> @set_card A Q HQ <= @set_card A P HP.
Proof.
  intros A P Q HP HQ Hsub.
  rewrite (card_as_len__cfp_step_07 A Q HQ), (card_as_len__cfp_step_07 A P HP).
  assert (Hn : (length (@enum A Q HQ) <= length (@enum A P HP))%nat).
  { apply NoDup_incl_length.
    - apply (@enum_nodup A Q HQ).
    - intros y Hy. apply (@enum_ok A P HP). apply Hsub. apply (@enum_ok A Q HQ). exact Hy. }
  rewrite !Zlength_correct. lia.
Qed.
Lemma count_nonneg__cfp_step_07 : forall (x : Z) (xs : list Z), 0 <= Count x xs.
Proof.
  intros x xs. unfold Count, set_card.
  apply sum_nonneg. intros. lia.
Qed.
Lemma count_le_len__cfp_step_07 : forall (x : Z) (xs : list Z), Count x xs <= Zlength xs.
Proof.
  intros x xs. unfold Count.
  eapply Z.le_trans.
  - apply (card_le__cfp_step_07 Z (fun i => 0 <= i < Zlength xs)
             (fun i : Z => 0 <= i < Zlength xs /\ Znth i xs 0 = x)
             (finite_Z_range 0 (Zlength xs)) _).
    intros y Hy. apply Hy.
  - unfold set_card. rewrite sum_Z_range_const.
    + lia.
    + rewrite Zlength_correct. lia.
Qed.
Lemma count_nil__cfp_step_07 : forall (x : Z), Count x nil = 0.
Proof.
  intros x.
  pose proof (count_nonneg__cfp_step_07 x nil).
  pose proof (count_le_len__cfp_step_07 x nil).
  rewrite Zlength_nil in *. lia.
Qed.
Lemma sublist_empty__cfp_step_07 : forall (l : list Z) (a b : Z),
  b <= a -> sublist a b l = nil.
Proof.
  intros l a b Hab. unfold sublist.
  apply skipn_all2. rewrite length_firstn. lia.
Qed.
Lemma plancost_bound__cfp_step_07 :
  forall (a : list Z) (del change p i l r c : Z),
    0 <= del <= 1000000000 ->
    0 <= change <= 1000000000 ->
    Zlength a <= 1000000 ->
    PartialPlanCost a del change p i l r c ->
    0 <= c <= 2000000000000000.
Proof.
  intros a del change p i l r c Hdel Hchange Ha HP.
  destruct HP as [Hl [Hlr [Hri [Hia [delta [result [HAdj [Hdiv Hc]]]]]]]].
  destruct HAdj as [Hlen [Hd Hres]].
  assert (Hkept : Zlength (sublist 0 l a ++ sublist r i a) = l + (i - r)).
  { rewrite Zlength_app.
    rewrite (Zlength_sublist 0 l a) by lia.
    rewrite (Zlength_sublist r i a) by lia.
    lia. }
  rewrite Hkept in Hlen.
  pose proof (count_nonneg__cfp_step_07 (-1) delta) as Hn1.
  pose proof (count_nonneg__cfp_step_07 1 delta) as Hn2.
  pose proof (count_le_len__cfp_step_07 (-1) delta) as Hb1.
  pose proof (count_le_len__cfp_step_07 1 delta) as Hb2.
  rewrite Hlen in Hb1, Hb2.
  unfold ChangeCost in Hc.
  assert (H1 : (r - l) * del <= (r - l) * 1000000000) by nia.
  assert (H2 : Count (-1) delta * change <= (l + (i - r)) * 1000000000) by nia.
  assert (H3 : Count 1 delta * change <= (l + (i - r)) * 1000000000) by nia.
  assert (H4 : 0 <= (r - l) * del) by nia.
  assert (H5 : 0 <= Count (-1) delta * change) by nia.
  assert (H6 : 0 <= Count 1 delta * change) by nia.
  assert (H7 : (r - l) + 2 * (l + (i - r)) <= 2 * 1000000) by lia.
  nia.
Qed.
Lemma elemcost_bound__cfp_step_07 : forall (change p x : Z),
  0 <= change -> ElemCost change p x <> 4611686018427387904 ->
  0 <= ElemCost change p x <= change.
Proof.
  intros change p x Hc H. unfold ElemCost in *.
  destruct (Z.eqb (x mod p) 0); [lia | ].
  destruct (orb (Z.eqb ((x - 1) mod p) 0) (Z.eqb ((x + 1) mod p) 0)); [lia | ].
  unfold INF in H. lia.
Qed.
Lemma cfp_state_finite_bound__cfp_step_07 :
  forall (a : list Z) (del change p i keep cutFresh cutAfterKeep after : Z),
    CostForPrimeState a del change p i keep cutFresh cutAfterKeep after ->
    0 <= del <= 1000000000 ->
    0 <= change <= 1000000000 ->
    Zlength a <= 1000000 ->
    (keep <> 4611686018427387904 -> 0 <= keep <= 2000000000000000) /\
    (cutFresh <> 4611686018427387904 -> 0 <= cutFresh <= 2000000000000000) /\
    (cutAfterKeep <> 4611686018427387904 -> 0 <= cutAfterKeep <= 2000000000000000) /\
    (after <> 4611686018427387904 -> 0 <= after <= 2000000000000000).
Proof.
  intros a del change p i keep cutFresh cutAfterKeep after HS Hdel Hchange Ha.
  destruct HS as [HK [HF [HA HT]]].
  split; [| split; [| split]]; intros Hne.
  - pose proof (dpvalue_fin_mem__cfp_step_07 _ _ HK Hne) as Hmem.
    unfold DPKeep in Hmem.
    exact (plancost_bound__cfp_step_07 a del change p i i i keep Hdel Hchange Ha Hmem).
  - pose proof (dpvalue_fin_mem__cfp_step_07 _ _ HF Hne) as Hmem.
    unfold DPCutFresh in Hmem.
    exact (plancost_bound__cfp_step_07 a del change p i 0 i cutFresh Hdel Hchange Ha Hmem).
  - pose proof (dpvalue_fin_mem__cfp_step_07 _ _ HA Hne) as Hmem.
    unfold DPCutAfterKeep in Hmem.
    destruct Hmem as [l [Hl1 [Hl2 Hmem]]].
    exact (plancost_bound__cfp_step_07 a del change p i l i cutAfterKeep Hdel Hchange Ha Hmem).
  - pose proof (dpvalue_fin_mem__cfp_step_07 _ _ HT Hne) as Hmem.
    unfold DPAfter in Hmem.
    destruct Hmem as [l [r [Hr Hmem]]].
    exact (plancost_bound__cfp_step_07 a del change p i l r after Hdel Hchange Ha Hmem).
Qed.
Lemma dpcutfresh_mem__cfp_step_07 : forall (a : list Z) (del change p i : Z),
  0 <= i <= Zlength a -> DPCutFresh a del change p i (i * del).
Proof.
  intros a del change p i Hi.
  unfold DPCutFresh, PartialPlanCost.
  split; [lia | ]. split; [lia | ]. split; [lia | ]. split; [lia | ].
  exists nil, nil.
  rewrite (sublist_empty__cfp_step_07 a 0 0) by lia.
  rewrite (sublist_empty__cfp_step_07 a i i) by lia.
  simpl.
  split; [| split].
  - unfold Adjusted. split; [reflexivity | ]. split; [constructor | reflexivity].
  - constructor.
  - unfold ChangeCost. rewrite !count_nil__cfp_step_07. lia.
Qed.
Lemma dpcutafterkeep_zero_empty__cfp_step_07 : forall (a : list Z) (del change p c : Z),
  ~ DPCutAfterKeep a del change p 0 c.
Proof.
  intros a del change p c H.
  unfold DPCutAfterKeep in H.
  destruct H as [l [Hl1 [Hl2 _]]]. lia.
Qed.
Lemma cfp_cutfresh_finite__cfp_step_07 :
  forall (a : list Z) (del change p i keep cutFresh cutAfterKeep after : Z),
    CostForPrimeState a del change p i keep cutFresh cutAfterKeep after ->
    0 <= del <= 1000000000 ->
    0 <= i <= Zlength a ->
    Zlength a <= 1000000 ->
    cutFresh <= 1000000000000000.
Proof.
  intros a del change p i keep cutFresh cutAfterKeep after HS Hdel Hi Ha.
  destruct HS as [HK [HF [HA HT]]].
  pose proof (dpcutfresh_mem__cfp_step_07 a del change p i Hi) as Hmem.
  pose proof (dpvalue_le_mem__cfp_step_07 _ _ _ HF Hmem) as Hle.
  nia.
Qed.
Lemma cfp_cutafterkeep_zero_inf__cfp_step_07 :
  forall (a : list Z) (del change p i keep cutFresh cutAfterKeep after : Z),
    CostForPrimeState a del change p i keep cutFresh cutAfterKeep after ->
    0 <= i -> i <= 0 ->
    cutAfterKeep = 4611686018427387904.
Proof.
  intros a del change p i keep cutFresh cutAfterKeep after HS H0 H1.
  assert (Hi : i = 0) by lia. subst i.
  destruct HS as [HK [HF [HA HT]]].
  apply (dpvalue_empty__cfp_step_07 _ _ HA).
  intros c. apply dpcutafterkeep_zero_empty__cfp_step_07.
Qed.
Lemma combine_app__cfp_step_07 : forall {A B : Type} (l1 l2 : list A) (l1' l2' : list B),
  length l1 = length l1' ->
  combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2'.
Proof.
  induction l1; destruct l1'; simpl; intros; auto; try discriminate.
  f_equal. auto.
Qed.
Lemma fold_filter_ind__cfp_step_07 : forall (l : list Z) (q : Z -> bool) (f : Z -> Z),
  (forall i, q i = true -> f i = 1) -> (forall i, q i = false -> f i = 0) ->
  fold_right (fun (_ : Z) (acc : Z) => 1 + acc) 0 (filter q l)
  = fold_right (fun (i : Z) (acc : Z) => f i + acc) 0 l.
Proof.
  induction l as [|a l IH]; intros q f H1 H0.
  - reflexivity.
  - replace (filter q (a :: l)) with (if q a then a :: filter q l else filter q l)
      by reflexivity.
    replace (fold_right (fun (i : Z) (acc : Z) => f i + acc) 0 (a :: l))
      with (f a + fold_right (fun (i : Z) (acc : Z) => f i + acc) 0 l)
      by reflexivity.
    destruct (q a) eqn:Hq.
    + replace (fold_right (fun (_ : Z) (acc : Z) => 1 + acc) 0 (a :: filter q l))
        with (1 + fold_right (fun (_ : Z) (acc : Z) => 1 + acc) 0 (filter q l))
        by reflexivity.
      rewrite (H1 a Hq), (IH q f H1 H0). reflexivity.
    + rewrite (H0 a Hq), (IH q f H1 H0). lia.
Qed.
Lemma count_as_range_sum__cfp_step_07 : forall (x : Z) (xs : list Z),
  Count x xs = sum (fun i => 0 <= i < Zlength xs)
                   (fun i => if Z.eqb (Znth i xs 0) x then 1 else 0).
Proof.
  intros x xs.
  rewrite sum_range_unfold.
  unfold Count, set_card, sum.
  unfold finite_Z_range'. cbn [enum].
  apply (fold_filter_ind__cfp_step_07 (Zrange 0 (Zlength xs))
           (fun i => if prop_dec (Znth i xs 0 = x) then true else false)
           (fun i => if Z.eqb (Znth i xs 0) x then 1 else 0)).
  - intros i Hi. destruct (prop_dec (Znth i xs 0 = x)) as [He | He]; [| discriminate].
    rewrite (proj2 (Z.eqb_eq _ _) He). reflexivity.
  - intros i Hi. destruct (prop_dec (Znth i xs 0 = x)) as [He | He]; [discriminate | ].
    rewrite (proj2 (Z.eqb_neq _ _) He). reflexivity.
Qed.
Lemma count_app_single__cfp_step_07 : forall (x : Z) (l : list Z) (d : Z),
  Count x (l ++ d :: nil) = Count x l + (if Z.eqb d x then 1 else 0).
Proof.
  intros x l d.
  rewrite !count_as_range_sum__cfp_step_07.
  apply (sum_Z_range_Znth_app_single 0 d l (fun y => if Z.eqb y x then 1 else 0)).
Qed.
Lemma p_not_div_both__cfp_step_07 : forall p x,
  2 <= p -> Z.divide p x -> Z.divide p (x - 1) -> False.
Proof.
  intros p x Hp H1 H2.
  assert (Hd : Z.divide p 1).
  { replace 1 with (x - (x - 1)) by lia. apply Z.divide_sub_r; auto. }
  pose proof (Z.divide_pos_le p 1 ltac:(lia) Hd). lia.
Qed.
Lemma elemcost_shift_cost__cfp_step_07 : forall change p x d,
  2 <= p -> (d = -1 \/ d = 0 \/ d = 1) -> Z.divide p (x + d) ->
  (if Z.eqb d (-1) then 1 else 0) * change
  + (if Z.eqb d 1 then 1 else 0) * change = ElemCost change p x.
Proof.
  intros change p x d Hp Hd Hdiv. unfold ElemCost.
  destruct Hd as [-> | [-> | ->]].
  - replace (x + -1) with (x - 1) in Hdiv by lia.
    assert (E1 : (x mod p =? 0) = false).
    { destruct (x mod p =? 0) eqn:E; [ | reflexivity].
      exfalso. apply Z.eqb_eq in E. apply (Z.mod_divide x p ltac:(lia)) in E.
      exact (p_not_div_both__cfp_step_07 p x Hp E Hdiv). }
    assert (E2 : ((x - 1) mod p =? 0) = true).
    { apply Z.eqb_eq. apply (Z.mod_divide (x - 1) p ltac:(lia)). exact Hdiv. }
    rewrite E1, E2. cbv beta iota delta [orb Z.eqb Pos.eqb]. lia.
  - replace (x + 0) with x in Hdiv by lia.
    assert (E1 : (x mod p =? 0) = true).
    { apply Z.eqb_eq. apply (Z.mod_divide x p ltac:(lia)). exact Hdiv. }
    rewrite E1. cbv beta iota delta [orb Z.eqb Pos.eqb]. lia.
  - assert (E1 : (x mod p =? 0) = false).
    { destruct (x mod p =? 0) eqn:E; [ | reflexivity].
      exfalso. apply Z.eqb_eq in E. apply (Z.mod_divide x p ltac:(lia)) in E.
      assert (Hd2 : Z.divide p ((x + 1) - 1)) by (replace ((x+1)-1) with x by lia; auto).
      exact (p_not_div_both__cfp_step_07 p (x + 1) Hp Hdiv Hd2). }
    assert (E2 : ((x + 1) mod p =? 0) = true).
    { apply Z.eqb_eq. apply (Z.mod_divide (x + 1) p ltac:(lia)). exact Hdiv. }
    rewrite E1, E2, orb_true_r. cbv beta iota delta [orb Z.eqb Pos.eqb]. lia.
Qed.
Lemma elemcost_attain__cfp_step_07 : forall change p x,
  2 <= p -> ElemCost change p x <> 4611686018427387904 ->
  exists d, (d = -1 \/ d = 0 \/ d = 1) /\ Z.divide p (x + d) /\
    (if Z.eqb d (-1) then 1 else 0) * change
    + (if Z.eqb d 1 then 1 else 0) * change = ElemCost change p x.
Proof.
  intros change p x Hp Hne.
  destruct (Z.eqb (x mod p) 0) eqn:E1.
  - assert (Hdv : Z.divide p (x + 0)).
    { replace (x + 0) with x by lia.
      apply (Z.mod_divide x p ltac:(lia)). apply Z.eqb_eq. exact E1. }
    exists 0. split; [tauto | ]. split; [exact Hdv | ].
    apply elemcost_shift_cost__cfp_step_07; [lia | tauto | exact Hdv].
  - destruct (orb (Z.eqb ((x - 1) mod p) 0) (Z.eqb ((x + 1) mod p) 0)) eqn:E2.
    + apply orb_true_iff in E2. destruct E2 as [E2 | E2].
      * assert (Hdv : Z.divide p (x + -1)).
        { replace (x + -1) with (x - 1) by lia.
          apply (Z.mod_divide (x - 1) p ltac:(lia)). apply Z.eqb_eq. exact E2. }
        exists (-1). split; [tauto | ]. split; [exact Hdv | ].
        apply elemcost_shift_cost__cfp_step_07; [lia | tauto | exact Hdv].
      * assert (Hdv : Z.divide p (x + 1)).
        { apply (Z.mod_divide (x + 1) p ltac:(lia)). apply Z.eqb_eq. exact E2. }
        exists 1. split; [tauto | ]. split; [exact Hdv | ].
        apply elemcost_shift_cost__cfp_step_07; [lia | tauto | exact Hdv].
    + exfalso. apply Hne. unfold ElemCost. rewrite E1, E2. reflexivity.
Qed.
Lemma keptplan_extend__cfp_step_07 : forall (kept : list Z) (change p x base c : Z),
  2 <= p ->
  ElemCost change p x <> 4611686018427387904 ->
  ( (exists delta result,
        Adjusted (kept ++ x :: nil) delta result /\
        Forall (fun y => Z.divide p y) result /\
        c = base + Count (-1) delta * change + Count 1 delta * change)
    <->
    (exists c' : Z,
        (exists delta result,
           Adjusted kept delta result /\
           Forall (fun y => Z.divide p y) result /\
           c' = base + Count (-1) delta * change + Count 1 delta * change)
        /\ c = c' + ElemCost change p x) ).
Proof.
  intros kept change p x base c Hp Hne.
  assert (Hkl : Zlength (kept ++ x :: nil) = Zlength kept + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  split.
  - intros [delta [result [[Hlen [Hall Hres]] [Hdiv Hc]]]].
    rewrite Hkl in Hlen.
    assert (Hne2 : delta <> nil).
    { intros ->. rewrite Zlength_nil in Hlen.
      pose proof (Zlength_nonneg kept). lia. }
    destruct (exists_last Hne2) as [delta' [d Hsp]]. subst delta.
    rewrite Zlength_app, Zlength_cons, Zlength_nil in Hlen.
    assert (Hlen' : Zlength delta' = Zlength kept) by lia.
    apply Forall_app in Hall. destruct Hall as [Hall' Halld].
    inversion Halld as [| dd ll Hd Hrest]; subst.
    assert (Hcomb : combine (kept ++ x :: nil) (delta' ++ d :: nil)
                    = combine kept delta' ++ (x, d) :: nil).
    { rewrite (combine_app__cfp_step_07 kept (x :: nil) delta' (d :: nil)).
      - reflexivity.
      - apply Nat2Z.inj. rewrite <- !Zlength_correct. lia. }
    rewrite Hcomb, map_app in Hdiv.
    apply Forall_app in Hdiv. destruct Hdiv as [Hdiv' Hdivd].
    cbn in Hdivd.
    assert (Hdvd : Z.divide p (x + d)).
    { inversion Hdivd as [| aa ll2 Hy Hrest2]; subst. exact Hy. }
    pose proof (elemcost_shift_cost__cfp_step_07 change p x d Hp Hd Hdvd) as Hec.
    exists (base + Count (-1) delta' * change + Count 1 delta' * change).
    split.
    + exists delta', (map (fun q : Z * Z => fst q + snd q) (combine kept delta')).
      split; [| split].
      * unfold Adjusted. split; [exact Hlen' | ]. split; [exact Hall' | reflexivity].
      * exact Hdiv'.
      * reflexivity.
    + rewrite !count_app_single__cfp_step_07. rewrite <- Hec. ring.
  - intros [c' [[delta' [result' [[Hlen [Hall Hres]] [Hdiv Hc']]]] Hc]].
    destruct (elemcost_attain__cfp_step_07 change p x Hp Hne) as [d [Hd [Hdvd Hec]]].
    assert (Hcomb : combine (kept ++ x :: nil) (delta' ++ d :: nil)
                    = combine kept delta' ++ (x, d) :: nil).
    { rewrite (combine_app__cfp_step_07 kept (x :: nil) delta' (d :: nil)).
      - reflexivity.
      - apply Nat2Z.inj. rewrite <- !Zlength_correct. lia. }
    exists (delta' ++ d :: nil), (result' ++ (x + d) :: nil).
    split; [| split].
    + unfold Adjusted. split.
      * rewrite Hkl, Zlength_app, Zlength_cons, Zlength_nil. lia.
      * split.
        -- apply Forall_app. split; [exact Hall | ].
           constructor; [exact Hd | constructor].
        -- rewrite Hcomb, map_app. rewrite <- Hres. reflexivity.
    + apply Forall_app. split; [exact Hdiv | ].
      constructor; [exact Hdvd | constructor].
    + rewrite Hc, Hc'. rewrite !count_app_single__cfp_step_07.
      rewrite <- Hec. ring.
Qed.
Lemma sublist_app_x__cfp_step_07 : forall (a : list Z) (l r i : Z),
  0 <= l -> l <= r -> r <= i -> i < Zlength a ->
  sublist 0 l a ++ sublist r (i + 1) a
  = (sublist 0 l a ++ sublist r i a) ++ Znth i a 0 :: nil.
Proof.
  intros a l r i Hl Hlr Hri Hi.
  rewrite (sublist_split r (i + 1) i a) by lia.
  rewrite (sublist_single 0 i a) by lia.
  rewrite app_assoc. reflexivity.
Qed.
Lemma sublist_keep_x__cfp_step_07 : forall (a : list Z) (i : Z),
  0 <= i -> i < Zlength a ->
  sublist 0 (i + 1) a ++ sublist (i + 1) (i + 1) a
  = (sublist 0 i a ++ sublist i i a) ++ Znth i a 0 :: nil.
Proof.
  intros a i H0 Hi.
  rewrite (sublist_empty__cfp_step_07 a (i + 1) (i + 1)) by lia.
  rewrite (sublist_empty__cfp_step_07 a i i) by lia.
  rewrite !app_nil_r.
  rewrite (sublist_split 0 (i + 1) i a) by lia.
  rewrite (sublist_single 0 i a) by lia.
  reflexivity.
Qed.
Lemma plan_extend_iff__cfp_step_07 : forall (a : list Z) (del change p i l r c : Z),
  2 <= p -> 0 <= i -> i < Zlength a -> 0 <= l -> l <= r -> r <= i ->
  ElemCost change p (Znth i a 0) <> 4611686018427387904 ->
  ( PartialPlanCost a del change p (i + 1) l r c <->
    exists c', PartialPlanCost a del change p i l r c' /\
               c = c' + ElemCost change p (Znth i a 0) ).
Proof.
  intros a del change p i l r c Hp Hi0 Hi Hl Hlr Hri Hne.
  unfold PartialPlanCost, ChangeCost.
  rewrite (sublist_app_x__cfp_step_07 a l r i Hl Hlr Hri Hi).
  split.
  - intros [_ [_ [_ [_ Hex]]]].
    apply (proj1 (keptplan_extend__cfp_step_07
                    (sublist 0 l a ++ sublist r i a) change p (Znth i a 0)
                    ((r - l) * del) c Hp Hne)) in Hex.
    destruct Hex as [c' [Hex' Hc]].
    exists c'. split; [| exact Hc].
    split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |]. exact Hex'.
  - intros [c' [[_ [_ [_ [_ Hex']]]] Hc]].
    split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
    apply (proj2 (keptplan_extend__cfp_step_07
                    (sublist 0 l a ++ sublist r i a) change p (Znth i a 0)
                    ((r - l) * del) c Hp Hne)).
    exists c'. split; [exact Hex' | exact Hc].
Qed.
Lemma dpkeep_extend_iff__cfp_step_07 : forall (a : list Z) (del change p i c : Z),
  2 <= p -> 0 <= i -> i < Zlength a ->
  ElemCost change p (Znth i a 0) <> 4611686018427387904 ->
  ( DPKeep a del change p (i + 1) c <->
    exists c', DPKeep a del change p i c' /\
               c = c' + ElemCost change p (Znth i a 0) ).
Proof.
  intros a del change p i c Hp Hi0 Hi Hne.
  unfold DPKeep, PartialPlanCost, ChangeCost.
  rewrite (sublist_keep_x__cfp_step_07 a i Hi0 Hi).
  replace (i + 1 - (i + 1)) with (i - i) by lia.
  split.
  - intros [_ [_ [_ [_ Hex]]]].
    apply (proj1 (keptplan_extend__cfp_step_07
                    (sublist 0 i a ++ sublist i i a) change p (Znth i a 0)
                    ((i - i) * del) c Hp Hne)) in Hex.
    destruct Hex as [c' [Hex' Hc]].
    exists c'. split; [| exact Hc].
    split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |]. exact Hex'.
  - intros [c' [[_ [_ [_ [_ Hex']]]] Hc]].
    split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
    apply (proj2 (keptplan_extend__cfp_step_07
                    (sublist 0 i a ++ sublist i i a) change p (Znth i a 0)
                    ((i - i) * del) c Hp Hne)).
    exists c'. split; [exact Hex' | exact Hc].
Qed.
Lemma plan_cut_extend_iff__cfp_step_07 : forall (a : list Z) (del change p i l c : Z),
  0 <= l -> l <= i -> i < Zlength a ->
  ( PartialPlanCost a del change p (i + 1) l (i + 1) c <->
    exists c', PartialPlanCost a del change p i l i c' /\ c = c' + del ).
Proof.
  intros a del change p i l c Hl Hli Hi.
  unfold PartialPlanCost, ChangeCost.
  rewrite (sublist_empty__cfp_step_07 a (i + 1) (i + 1)) by lia.
  rewrite (sublist_empty__cfp_step_07 a i i) by lia.
  split.
  - intros [_ [_ [_ [_ [delta [result [HA [HD HC]]]]]]]].
    exists ((i - l) * del + Count (-1) delta * change + Count 1 delta * change).
    split.
    + split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
      exists delta, result. split; [exact HA |]. split; [exact HD | reflexivity].
    + rewrite HC. ring.
  - intros [c' [[_ [_ [_ [_ [delta [result [HA [HD HC]]]]]]]] Hc]].
    split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
    exists delta, result. split; [exact HA |]. split; [exact HD |].
    rewrite Hc, HC. ring.
Qed.
Lemma dpkeep_sub_dpafter__cfp_step_07 : forall (a : list Z) (del change p i c : Z),
  1 <= i -> DPKeep a del change p i c -> DPAfter a del change p i c.
Proof.
  intros a del change p i c Hi HK.
  unfold DPKeep, DPAfter, PartialPlanCost, ChangeCost in *.
  destruct HK as [_ [_ [_ [Hia [delta [result [HA [HD HC]]]]]]]].
  rewrite (sublist_empty__cfp_step_07 a i i) in HA by lia.
  rewrite app_nil_r in HA.
  exists (i - 1), (i - 1). split; [lia |].
  split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
  exists delta, result.
  rewrite <- (sublist_split 0 i (i - 1) a) by lia.
  split; [exact HA |]. split; [exact HD |].
  rewrite HC. ring.
Qed.
Lemma plan_classify__cfp_step_07 : forall (a : list Z) (del change p i l r c : Z),
  0 <= l -> l <= r -> r <= i ->
  PartialPlanCost a del change p i l r c ->
  DPAfter a del change p i c \/ DPKeep a del change p i c \/
  DPCutFresh a del change p i c \/ DPCutAfterKeep a del change p i c.
Proof.
  intros a del change p i l r c Hl Hlr Hri HP.
  destruct (Z.lt_ge_cases r i) as [Hlt | Hge].
  - left. unfold DPAfter. exists l, r. split; [lia | exact HP].
  - assert (Hr : r = i) by lia. subst r.
    destruct (Z.eq_dec l 0) as [-> | Hl0].
    + right. right. left. exact HP.
    + destruct (Z.eq_dec l i) as [-> | Hli].
      * right. left. exact HP.
      * right. right. right. unfold DPCutAfterKeep.
        exists l. split; [lia |]. split; [lia | exact HP].
Qed.
Lemma dpcutfresh_val__cfp_step_07 : forall (a : list Z) (del change p i c : Z),
  DPCutFresh a del change p i c -> c = i * del.
Proof.
  intros a del change p i c HP.
  unfold DPCutFresh, PartialPlanCost, ChangeCost in HP.
  destruct HP as [_ [_ [_ [Hia [delta [result [[Hlen [_ _]] [_ HC]]]]]]]].
  rewrite (sublist_empty__cfp_step_07 a 0 0) in Hlen by lia.
  rewrite (sublist_empty__cfp_step_07 a i i) in Hlen by lia.
  rewrite app_nil_r, Zlength_nil in Hlen.
  pose proof (count_nonneg__cfp_step_07 (-1) delta).
  pose proof (count_nonneg__cfp_step_07 1 delta).
  pose proof (count_le_len__cfp_step_07 (-1) delta).
  pose proof (count_le_len__cfp_step_07 1 delta).
  assert (Hc1 : Count (-1) delta = 0) by lia.
  assert (Hc2 : Count 1 delta = 0) by lia.
  rewrite HC, Hc1, Hc2. ring.
Qed.
Lemma cfp_state_step__cfp_step_07 :
  forall (a : list Z) (del change p i keep cutFresh cutAfterKeep after cost : Z),
    CostForPrimeState a del change p i keep cutFresh cutAfterKeep after ->
    0 <= del <= 1000000000 ->
    0 <= change <= 1000000000 ->
    Zlength a <= 1000000 ->
    2 <= p ->
    1 <= i ->
    i < Zlength a ->
    cost = ElemCost change p (Znth i a 0) ->
    keep <> 4611686018427387904 ->
    cutFresh <> 4611686018427387904 ->
    after <> 4611686018427387904 ->
    cost <> 4611686018427387904 ->
    keep <= cutAfterKeep ->
    after <= cutFresh ->
    after <= cutAfterKeep ->
    CostForPrimeState a del change p (i + 1)
      (keep + cost) (cutFresh + del) (keep + del) (after + cost).
Proof.
  intros a del change p i keep cutFresh cutAfterKeep after cost
         HS Hdel Hchange Ha Hp Hi1 Hi Hcost Hkne Hfne Htne Hcne Hkca Htf Htca.
  pose proof (cfp_state_finite_bound__cfp_step_07 a del change p i keep cutFresh
                cutAfterKeep after HS Hdel Hchange Ha) as Hb.
  destruct Hb as [Hbk [Hbf [Hba Hbt]]].
  pose proof (Hbk Hkne) as Bk. pose proof (Hbf Hfne) as Bf.
  pose proof (Hbt Htne) as Bt.
  subst cost.
  pose proof (elemcost_bound__cfp_step_07 change p (Znth i a 0)
                ltac:(lia) Hcne) as Bc.
  destruct HS as [HK [HF [HA HT]]].
  pose proof (dpvalue_fin_mem__cfp_step_07 _ _ HK Hkne) as Hkm.
  pose proof (dpvalue_fin_mem__cfp_step_07 _ _ HT Htne) as Htm.
  pose proof (dpvalue_fin_mem__cfp_step_07 _ _ HF Hfne) as Hfm.
  pose proof (dpcutfresh_val__cfp_step_07 _ _ _ _ _ _ Hfm) as Hfv.
  split; [| split; [| split]].
  - (* DPKeep *)
    apply dpvalue_intro__cfp_step_07.
    + apply (proj2 (dpkeep_extend_iff__cfp_step_07 a del change p i
                      (keep + ElemCost change p (Znth i a 0)) Hp ltac:(lia) Hi Hcne)).
      exists keep. split; [exact Hkm | reflexivity].
    + intros c Hc.
      apply (proj1 (dpkeep_extend_iff__cfp_step_07 a del change p i c Hp
                      ltac:(lia) Hi Hcne)) in Hc.
      destruct Hc as [c' [Hc' Heq]].
      pose proof (dpvalue_le_mem__cfp_step_07 _ _ _ HK Hc'). lia.
    + unfold INF. lia.
  - (* DPCutFresh *)
    apply dpvalue_intro__cfp_step_07.
    + replace (cutFresh + del) with ((i + 1) * del) by (rewrite Hfv; ring).
      apply dpcutfresh_mem__cfp_step_07. lia.
    + intros c Hc.
      pose proof (dpcutfresh_val__cfp_step_07 _ _ _ _ _ _ Hc). nia.
    + unfold INF. nia.
  - (* DPCutAfterKeep *)
    apply dpvalue_intro__cfp_step_07.
    + unfold DPCutAfterKeep. exists i. split; [lia |]. split; [lia |].
      apply (proj2 (plan_cut_extend_iff__cfp_step_07 a del change p i i
                      (keep + del) ltac:(lia) ltac:(lia) Hi)).
      exists keep. split; [exact Hkm | reflexivity].
    + intros c Hc. destruct Hc as [l [Hl1 [Hl2 HP]]].
      apply (proj1 (plan_cut_extend_iff__cfp_step_07 a del change p i l c
                      ltac:(lia) ltac:(lia) Hi)) in HP.
      destruct HP as [c' [HP' Heq]].
      destruct (Z.eq_dec l i) as [Hli | Hli].
      * subst l. pose proof (dpvalue_le_mem__cfp_step_07 _ _ _ HK HP'). lia.
      * assert (Hin : DPCutAfterKeep a del change p i c').
        { unfold DPCutAfterKeep. exists l. split; [lia |]. split; [lia | exact HP']. }
        pose proof (dpvalue_le_mem__cfp_step_07 _ _ _ HA Hin). lia.
    + unfold INF. lia.
  - (* DPAfter *)
    apply dpvalue_intro__cfp_step_07.
    + destruct Htm as [l [r [Hr HP]]].
      assert (Hb2 : 0 <= l /\ l <= r) by (destruct HP as [? [? ?]]; lia).
      destruct Hb2 as [Hl0 Hlr].
      unfold DPAfter. exists l, r. split; [lia |].
      apply (proj2 (plan_extend_iff__cfp_step_07 a del change p i l r
                      (after + ElemCost change p (Znth i a 0)) Hp ltac:(lia) Hi
                      Hl0 Hlr ltac:(lia) Hcne)).
      exists after. split; [exact HP | reflexivity].
    + intros c Hc. destruct Hc as [l [r [Hr HP]]].
      assert (Hb2 : 0 <= l /\ l <= r) by (destruct HP as [? [? ?]]; lia).
      destruct Hb2 as [Hl0 Hlr].
      apply (proj1 (plan_extend_iff__cfp_step_07 a del change p i l r c Hp
                      ltac:(lia) Hi Hl0 Hlr ltac:(lia) Hcne)) in HP.
      destruct HP as [c' [HP' Heq]].
      pose proof (plan_classify__cfp_step_07 a del change p i l r c'
                    Hl0 Hlr ltac:(lia) HP') as Hcl.
      destruct Hcl as [Hcl | [Hcl | [Hcl | Hcl]]].
      * pose proof (dpvalue_le_mem__cfp_step_07 _ _ _ HT Hcl). lia.
      * pose proof (dpkeep_sub_dpafter__cfp_step_07 a del change p i c'
                      ltac:(lia) Hcl) as Hcl2.
        pose proof (dpvalue_le_mem__cfp_step_07 _ _ _ HT Hcl2). lia.
      * pose proof (dpvalue_le_mem__cfp_step_07 _ _ _ HF Hcl). lia.
      * pose proof (dpvalue_le_mem__cfp_step_07 _ _ _ HA Hcl). lia.
    + unfold INF. lia.
Qed.
Lemma set_card_empty__cfp_step_08 :
  forall {A : Type} (P : A -> Prop) (FP : Finite P),
    (forall x, ~ P x) -> @set_card A P FP = 0.
Proof.
  intros A P FP Hempty.
  unfold set_card, SumLib.Sum.sum.
  destruct (@enum A P FP) as [|x xs] eqn:Hen; [reflexivity |].
  exfalso.
  apply (Hempty x).
  apply (proj2 (@enum_ok A P FP x)).
  rewrite Hen. simpl. auto.
Qed.
Lemma count_nil__cfp_step_08 : forall x : Z, Count x [] = 0.
Proof.
  intros x. unfold Count.
  apply set_card_empty__cfp_step_08.
  intros j [Hr _]. change (Zlength (@nil Z)) with 0 in Hr. lia.
Qed.
Lemma dpcutfresh_member__cfp_step_08 :
  forall (a : list Z) (del change p i : Z),
    0 <= i -> i <= Zlength a ->
    DPCutFresh a del change p i (i * del).
Proof.
  intros a del change p i Hi Hia.
  pose proof (Zlength_nonneg a) as Hnn.
  unfold DPCutFresh, PartialPlanCost.
  split; [lia |]. split; [lia |]. split; [lia |]. split; [lia |].
  exists nil, nil.
  split.
  - unfold Adjusted.
    split.
    + rewrite Zlength_app.
      rewrite (Zlength_sublist 0 0 a) by lia.
      rewrite (Zlength_sublist i i a) by lia.
      change (Zlength (@nil Z)) with 0. lia.
    + split; [constructor |].
      destruct (sublist 0 0 a ++ sublist i i a); reflexivity.
  - split; [constructor |].
    unfold ChangeCost.
    rewrite !count_nil__cfp_step_08.
    replace (i - 0) with i by lia. lia.
Qed.
Lemma cfp_cutfresh_le__cfp_step_08 :
  forall (a : list Z) (del change p i cf : Z),
    0 <= i -> i <= Zlength a ->
    DPValue (DPCutFresh a del change p i) cf ->
    cf <= i * del.
Proof.
  intros a del change p i cf Hi Hia HD.
  pose proof (dpcutfresh_member__cfp_step_08 a del change p i Hi Hia) as Hmem.
  unfold DPValue, min_value_of_subset_with_default in HD.
  destruct HD as [[Hmin Hle] | [Hall Heq]].
  - destruct Hmin as [c [[HcS Hmn] Hfc]].
    simpl in Hfc. subst cf.
    apply (Hmn (i * del)). exact Hmem.
  - subst cf. apply Hall. exact Hmem.
Qed.
Lemma cfp_state_cutfresh_bound__cfp_step_08 :
  forall (a : list Z) (del change p i keep cf cak af : Z),
    0 <= i -> i <= Zlength a -> Zlength a <= 1000000 ->
    0 <= del -> del <= 1000000000 ->
    CostForPrimeState a del change p i keep cf cak af ->
    cf <= 1000000000000000.
Proof.
  intros a del change p i keep cf cak af Hi Hia Hn Hd0 Hd1 HS.
  destruct HS as [_ [HD _]].
  pose proof (cfp_cutfresh_le__cfp_step_08 a del change p i cf Hi Hia HD).
  nia.
Qed.
Lemma set_card_Z_as_sum__cfp_step_09 :
  forall (low high : Z) (P : Z -> Prop),
    #(fun z : Z => low <= z < high /\ P z) =
    SumLib.Sum.sum (fun z : Z => low <= z < high)
      (fun z => if prop_dec (P z) then 1 else 0).
Proof.
  intros low high P.
  unfold set_card, SumLib.Sum.sum.
  cbn [finite_Z_range' finite_Z_range].
  assert (Hfilter : forall zs : list Z,
    fold_right (fun _ acc : Z => 1 + acc) 0
      (filter (fun z => if prop_dec (P z) then true else false) zs) =
    fold_right (fun z acc : Z =>
      (if prop_dec (P z) then 1 else 0) + acc) 0 zs).
  {
    induction zs as [|z zs IH]; simpl; [reflexivity |].
    destruct (prop_dec (P z)); simpl.
    - exact (f_equal (fun n : Z => 1 + n) IH).
    - exact IH.
  }
  apply Hfilter.
Qed.
Lemma set_card_Z_ext__cfp_step_09 :
  forall (low high : Z) (P Q : Z -> Prop),
    (forall z, low <= z < high -> (P z <-> Q z)) ->
    #(fun z : Z => low <= z < high /\ P z) =
    #(fun z : Z => low <= z < high /\ Q z).
Proof.
  intros low high P Q Hiff.
  rewrite !set_card_Z_as_sum__cfp_step_09.
  apply SumLib.Sum.sum_ext.
  intros z Hz.
  specialize (Hiff z Hz).
  destruct (prop_dec (P z)); destruct (prop_dec (Q z));
    try reflexivity; exfalso; tauto.
Qed.
Lemma set_card_Z_extend__cfp_step_09 :
  forall (low high : Z) (P : Z -> Prop),
    low <= high ->
    #(fun z : Z => low <= z < high + 1 /\ P z) =
    #(fun z : Z => low <= z < high /\ P z) +
    (if prop_dec (P high) then 1 else 0).
Proof.
  intros low high P Hrange.
  rewrite !set_card_Z_as_sum__cfp_step_09.
  rewrite SumLib.ZRange.sum_Z_range_extend_right by lia.
  reflexivity.
Qed.
Lemma count_bound__cfp_step_09 :
  forall (x : Z) (xs : list Z), 0 <= Count x xs <= Zlength xs.
Proof.
  intros x xs.
  unfold Count.
  rewrite set_card_Z_as_sum__cfp_step_09.
  pose proof (Zlength_nonneg xs) as Hn.
  assert (Hlo : (Zlength xs - 0) * 0 <=
    SumLib.Sum.sum (fun z : Z => 0 <= z < Zlength xs)
      (fun z => if prop_dec (Znth z xs 0 = x) then 1 else 0)).
  { apply SumLib.ZRange.sum_Z_range_lower_bound; [lia |].
    intros z Hz. destruct (prop_dec (Znth z xs 0 = x)); lia. }
  assert (Hhi :
    SumLib.Sum.sum (fun z : Z => 0 <= z < Zlength xs)
      (fun z => if prop_dec (Znth z xs 0 = x) then 1 else 0)
    <= (Zlength xs - 0) * 1).
  { apply SumLib.ZRange.sum_Z_range_upper_bound; [lia |].
    intros z Hz. destruct (prop_dec (Znth z xs 0 = x)); lia. }
  lia.
Qed.
Lemma count_nil__cfp_step_09 : forall x : Z, Count x nil = 0.
Proof.
  intros x.
  pose proof (count_bound__cfp_step_09 x nil) as H.
  rewrite Zlength_nil in H.
  lia.
Qed.
Lemma count_snoc__cfp_step_09 :
  forall (x : Z) (ys : list Z) (d : Z),
    Count x (ys ++ d :: nil) = Count x ys + (if Z.eq_dec d x then 1 else 0).
Proof.
  intros x ys d.
  pose proof (Zlength_nonneg ys) as Hn.
  assert (Hlen : Zlength (ys ++ d :: nil) = Zlength ys + 1).
  { rewrite Zlength_app, Zlength_cons, Zlength_nil. lia. }
  unfold Count.
  rewrite Hlen.
  rewrite set_card_Z_extend__cfp_step_09 by lia.
  f_equal.
  - apply set_card_Z_ext__cfp_step_09.
    intros z Hz.
    rewrite app_Znth1 by lia.
    tauto.
  - rewrite app_Znth2 by lia.
    replace (Zlength ys - Zlength ys) with 0 by lia.
    unfold Znth. simpl.
    destruct (prop_dec (d = x)); destruct (Z.eq_dec d x);
      try reflexivity; exfalso; tauto.
Qed.
Lemma sublist_empty__cfp_step_09 :
  forall (l : list Z) (i j : Z), j <= i -> sublist i j l = nil.
Proof.
  intros l i j Hij.
  unfold sublist.
  apply skipn_all2.
  rewrite length_firstn.
  lia.
Qed.
Lemma combine_snoc__cfp_step_09 :
  forall (K D : list Z) (v d : Z),
    Zlength K = Zlength D ->
    combine (K ++ v :: nil) (D ++ d :: nil) = combine K D ++ (v, d) :: nil.
Proof.
  induction K as [|k K IH]; intros D v d HL.
  - destruct D as [|e D].
    + reflexivity.
    + rewrite Zlength_nil, Zlength_cons in HL.
      pose proof (Zlength_nonneg D). lia.
  - destruct D as [|e D].
    + rewrite Zlength_nil, Zlength_cons in HL.
      pose proof (Zlength_nonneg K). lia.
    + simpl. rewrite IH; [reflexivity |].
      rewrite !Zlength_cons in HL. lia.
Qed.
Lemma adjusted_snoc__cfp_step_09 :
  forall (K : list Z) (v : Z) (delta result : list Z),
    Adjusted (K ++ v :: nil) delta result <->
    (exists (delta' result' : list Z) (d : Z),
       delta = delta' ++ d :: nil /\
       (d = -1 \/ d = 0 \/ d = 1) /\
       Adjusted K delta' result' /\
       result = result' ++ (v + d) :: nil).
Proof.
  intros K v delta result.
  split.
  - intros [HLen [HForall HRes]].
    rewrite Zlength_app, Zlength_cons, Zlength_nil in HLen.
    pose proof (Zlength_nonneg K) as HK.
    assert (Hne : delta <> nil).
    { intros Hc. subst delta. rewrite Zlength_nil in HLen. lia. }
    destruct (exists_last Hne) as [delta' [d Hd]].
    assert (HLen' : Zlength delta' = Zlength K).
    { subst delta. rewrite Zlength_app, Zlength_cons, Zlength_nil in HLen. lia. }
    subst delta.
    apply Forall_app in HForall.
    destruct HForall as [HF1 HF2].
    apply Forall_inv in HF2.
    exists delta', (map (fun q : Z * Z => fst q + snd q) (combine K delta')), d.
    split; [reflexivity |].
    split; [exact HF2 |].
    split.
    + unfold Adjusted. split; [lia |]. split; [exact HF1 | reflexivity].
    + rewrite HRes.
      rewrite combine_snoc__cfp_step_09 by lia.
      rewrite map_app.
      reflexivity.
  - intros [delta' [result' [d [Hdelta [Hd [HA Hres]]]]]].
    destruct HA as [HLen [HForall HRes]].
    subst delta result result'.
    unfold Adjusted.
    split.
    { rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. lia. }
    split.
    { apply Forall_app. split; [exact HForall |].
      constructor; [exact Hd | constructor]. }
    rewrite combine_snoc__cfp_step_09 by lia.
    rewrite map_app.
    reflexivity.
Qed.
Lemma changecost_snoc__cfp_step_09 :
  forall (del ch l r : Z) (delta' : list Z) (d : Z),
    (d = -1 \/ d = 0 \/ d = 1) ->
    ChangeCost del ch l r (delta' ++ d :: nil) =
    ChangeCost del ch l r delta' + (if Z.eq_dec d 0 then 0 else ch).
Proof.
  intros del ch l r delta' d Hd.
  unfold ChangeCost.
  rewrite !count_snoc__cfp_step_09.
  destruct Hd as [H|[H|H]]; subst d.
  - destruct (Z.eq_dec (-1) (-1)); [| lia].
    destruct (Z.eq_dec (-1) 1); [lia |].
    destruct (Z.eq_dec (-1) 0); [lia |]. ring.
  - destruct (Z.eq_dec 0 (-1)); [lia |].
    destruct (Z.eq_dec 0 1); [lia |].
    destruct (Z.eq_dec 0 0); [| lia]. ring.
  - destruct (Z.eq_dec 1 (-1)); [lia |].
    destruct (Z.eq_dec 1 1); [| lia].
    destruct (Z.eq_dec 1 0); [lia |]. ring.
Qed.
Lemma changecost_extend__cfp_step_09 :
  forall (del ch l i : Z) (delta : list Z),
    ChangeCost del ch l (i + 1) delta = ChangeCost del ch l i delta + del.
Proof. intros. unfold ChangeCost. ring. Qed.
Lemma changecost_same__cfp_step_09 :
  forall (del ch i : Z) (delta : list Z),
    ChangeCost del ch (i + 1) (i + 1) delta = ChangeCost del ch i i delta.
Proof. intros. unfold ChangeCost. ring. Qed.
Lemma ppc_cut_extend__cfp_step_09 :
  forall (a : list Z) (del ch p i l c : Z),
    0 <= l -> l <= i -> i < Zlength a ->
    (PartialPlanCost a del ch p (i + 1) l (i + 1) c <->
     exists c', PartialPlanCost a del ch p i l i c' /\ c = c' + del).
Proof.
  intros a del ch p i l c Hl Hli Hi.
  assert (Hk : sublist 0 l a ++ sublist (i + 1) (i + 1) a
             = sublist 0 l a ++ sublist i i a).
  { rewrite (sublist_empty__cfp_step_09 a (i + 1) (i + 1)) by lia.
    rewrite (sublist_empty__cfp_step_09 a i i) by lia.
    reflexivity. }
  unfold PartialPlanCost.
  split.
  - intros [H1 [H2 [H3 [H4 [delta [result [HA [HD HC]]]]]]]].
    rewrite Hk in HA.
    exists (ChangeCost del ch l i delta).
    split.
    + repeat split; try lia.
      exists delta, result.
      split; [exact HA | split; [exact HD | reflexivity]].
    + rewrite HC. apply changecost_extend__cfp_step_09.
  - intros [c' [[H1 [H2 [H3 [H4 [delta [result [HA [HD HC]]]]]]]] HC']].
    repeat split; try lia.
    exists delta, result.
    rewrite Hk.
    split; [exact HA | split; [exact HD |]].
    rewrite HC', HC. symmetry. apply changecost_extend__cfp_step_09.
Qed.
Lemma ppc_snoc__cfp_step_09 :
  forall (a : list Z) (del ch p i l r c : Z),
    0 <= l -> l <= r -> r <= i -> i < Zlength a ->
    (PartialPlanCost a del ch p (i + 1) l r c <->
     exists c' d, PartialPlanCost a del ch p i l r c' /\
       (d = -1 \/ d = 0 \/ d = 1) /\ Z.divide p (Znth i a 0 + d) /\
       c = c' + (if Z.eq_dec d 0 then 0 else ch)).
Proof.
  intros a del ch p i l r c Hl Hlr Hri Hi.
  assert (Hk : sublist 0 l a ++ sublist r (i + 1) a
             = (sublist 0 l a ++ sublist r i a) ++ Znth i a 0 :: nil).
  { rewrite (sublist_split r (i + 1) i a) by lia.
    rewrite (@sublist_single Z 0 i a) by lia.
    rewrite app_assoc. reflexivity. }
  unfold PartialPlanCost.
  split.
  - intros [H1 [H2 [H3 [H4 [delta [result [HA [HD HC]]]]]]]].
    rewrite Hk in HA.
    apply adjusted_snoc__cfp_step_09 in HA.
    destruct HA as [delta' [result' [d [Hdelta [Hd [HA' Hres]]]]]].
    subst result.
    apply Forall_app in HD.
    destruct HD as [HD1 HD2].
    apply Forall_inv in HD2.
    exists (ChangeCost del ch l r delta'), d.
    split; [| split; [exact Hd | split; [exact HD2 |]]].
    + repeat split; try lia.
      exists delta', result'.
      split; [exact HA' | split; [exact HD1 | reflexivity]].
    + subst delta.
      rewrite HC. apply changecost_snoc__cfp_step_09. exact Hd.
  - intros [c' [d [[H1 [H2 [H3 [H4 [delta' [result' [HA' [HD' HC']]]]]]]]
             [Hd [Hdiv HC]]]]].
    repeat split; try lia.
    exists (delta' ++ d :: nil), (result' ++ (Znth i a 0 + d) :: nil).
    split.
    { rewrite Hk.
      apply adjusted_snoc__cfp_step_09.
      exists delta', result', d.
      split; [reflexivity | split; [exact Hd | split; [exact HA' | reflexivity]]]. }
    split.
    { apply Forall_app.
      split; [exact HD' | constructor; [exact Hdiv | constructor]]. }
    rewrite HC, HC'. symmetry.
    apply changecost_snoc__cfp_step_09. exact Hd.
Qed.
Lemma ppc_bounds__cfp_step_09 :
  forall (a : list Z) (del ch p i l r c : Z),
    PartialPlanCost a del ch p i l r c ->
    0 <= l /\ l <= r /\ r <= i /\ i <= Zlength a.
Proof. intros. unfold PartialPlanCost in H. tauto. Qed.
Lemma dpkeep_alt__cfp_step_09 :
  forall (a : list Z) (del ch p i c : Z),
    0 <= i -> i < Zlength a ->
    (DPKeep a del ch p (i + 1) c <-> PartialPlanCost a del ch p (i + 1) i i c).
Proof.
  intros a del ch p i c H0 H1.
  assert (Hk : sublist 0 (i + 1) a ++ sublist (i + 1) (i + 1) a
             = sublist 0 i a ++ sublist i (i + 1) a).
  { rewrite (sublist_empty__cfp_step_09 a (i + 1) (i + 1)) by lia.
    rewrite app_nil_r.
    rewrite (sublist_split 0 (i + 1) i a) by lia.
    reflexivity. }
  unfold DPKeep, PartialPlanCost.
  split.
  - intros [A1 [A2 [A3 [A4 [delta [result [HA [HD HC]]]]]]]].
    rewrite Hk in HA.
    repeat split; try lia.
    exists delta, result.
    split; [exact HA | split; [exact HD |]].
    rewrite HC. apply changecost_same__cfp_step_09.
  - intros [A1 [A2 [A3 [A4 [delta [result [HA [HD HC]]]]]]]].
    rewrite <- Hk in HA.
    repeat split; try lia.
    exists delta, result.
    split; [exact HA | split; [exact HD |]].
    rewrite HC. symmetry. apply changecost_same__cfp_step_09.
Qed.
Lemma dpkeep_step_set__cfp_step_09 :
  forall (a : list Z) (del ch p i c : Z),
    0 <= i -> i < Zlength a ->
    (DPKeep a del ch p (i + 1) c <->
     exists c' d, DPKeep a del ch p i c' /\ (d = -1 \/ d = 0 \/ d = 1) /\
        Z.divide p (Znth i a 0 + d) /\
        c = c' + (if Z.eq_dec d 0 then 0 else ch)).
Proof.
  intros a del ch p i c H0 H1.
  assert (H2 : DPKeep a del ch p (i + 1) c
             <-> PartialPlanCost a del ch p (i + 1) i i c)
    by (apply dpkeep_alt__cfp_step_09; lia).
  assert (H3 : PartialPlanCost a del ch p (i + 1) i i c <->
     exists c' d, PartialPlanCost a del ch p i i i c' /\
       (d = -1 \/ d = 0 \/ d = 1) /\ Z.divide p (Znth i a 0 + d) /\
       c = c' + (if Z.eq_dec d 0 then 0 else ch))
    by (apply ppc_snoc__cfp_step_09; lia).
  unfold DPKeep in *.
  split.
  - intros H. apply H3. apply H2. exact H.
  - intros H. apply H2. apply H3. exact H.
Qed.
Lemma dpcutfresh_step_set__cfp_step_09 :
  forall (a : list Z) (del ch p i c : Z),
    0 <= i -> i < Zlength a ->
    (DPCutFresh a del ch p (i + 1) c <->
     exists c', DPCutFresh a del ch p i c' /\ c = c' + del).
Proof.
  intros a del ch p i c H0 H1.
  unfold DPCutFresh.
  apply ppc_cut_extend__cfp_step_09; lia.
Qed.
Lemma dpcutafterkeep_step_set__cfp_step_09 :
  forall (a : list Z) (del ch p i c : Z),
    0 < i -> i < Zlength a ->
    (DPCutAfterKeep a del ch p (i + 1) c <->
     exists c', (DPCutAfterKeep a del ch p i c' \/ DPKeep a del ch p i c') /\
        c = c' + del).
Proof.
  intros a del ch p i c Hi Hn.
  unfold DPCutAfterKeep, DPKeep.
  split.
  - intros [l [Hl1 [Hl2 Hppc]]].
    assert (Hiff : PartialPlanCost a del ch p (i + 1) l (i + 1) c <->
             exists c', PartialPlanCost a del ch p i l i c' /\ c = c' + del)
      by (apply ppc_cut_extend__cfp_step_09; lia).
    apply Hiff in Hppc.
    destruct Hppc as [c' [Hppc Hc]].
    exists c'. split; [| exact Hc].
    destruct (Z.eq_dec l i) as [He | He].
    + right. subst l. exact Hppc.
    + left. exists l. split; [lia | split; [lia | exact Hppc]].
  - intros [c' [Hsrc Hc]].
    assert (Hone : forall l, 0 <= l -> l <= i ->
              PartialPlanCost a del ch p i l i c' ->
              PartialPlanCost a del ch p (i + 1) l (i + 1) c).
    { intros l Hl0 Hl1 Hppc.
      assert (Hiff : PartialPlanCost a del ch p (i + 1) l (i + 1) c <->
               exists c'', PartialPlanCost a del ch p i l i c'' /\ c = c'' + del)
        by (apply ppc_cut_extend__cfp_step_09; lia).
      apply Hiff. exists c'. split; [exact Hppc | exact Hc]. }
    destruct Hsrc as [[l [Hl1 [Hl2 Hppc]]] | Hppc].
    + exists l. split; [lia | split; [lia |]].
      apply Hone; [lia | lia | exact Hppc].
    + exists i. split; [lia | split; [lia |]].
      apply Hone; [lia | lia | exact Hppc].
Qed.
Lemma dpkeep_sub_dpafter__cfp_step_09 :
  forall (a : list Z) (del ch p i c : Z),
    0 < i -> i <= Zlength a ->
    DPKeep a del ch p i c -> DPAfter a del ch p i c.
Proof.
  intros a del ch p i c Hi Hn HK.
  unfold DPKeep, DPAfter in *.
  unfold PartialPlanCost in HK.
  destruct HK as [A1 [A2 [A3 [A4 [delta [result [HA [HD HC]]]]]]]].
  exists (i - 1), (i - 1).
  split; [lia |].
  unfold PartialPlanCost.
  repeat split; try lia.
  exists delta, result.
  assert (Hk : sublist 0 (i - 1) a ++ sublist (i - 1) i a
             = sublist 0 i a ++ sublist i i a).
  { rewrite <- (sublist_split 0 i (i - 1) a) by lia.
    rewrite (sublist_empty__cfp_step_09 a i i) by lia.
    rewrite app_nil_r. reflexivity. }
  rewrite Hk.
  split; [exact HA | split; [exact HD |]].
  rewrite HC. unfold ChangeCost. ring.
Qed.
Lemma dpafter_step_set__cfp_step_09 :
  forall (a : list Z) (del ch p i c : Z),
    0 < i -> i < Zlength a ->
    (DPAfter a del ch p (i + 1) c <->
     exists c' d,
       (DPAfter a del ch p i c' \/ DPCutFresh a del ch p i c' \/
        DPCutAfterKeep a del ch p i c') /\
       (d = -1 \/ d = 0 \/ d = 1) /\ Z.divide p (Znth i a 0 + d) /\
       c = c' + (if Z.eq_dec d 0 then 0 else ch)).
Proof.
  intros a del ch p i c Hi Hn.
  split.
  - intros [l [r [Hr Hppc]]].
    pose proof (ppc_bounds__cfp_step_09 _ _ _ _ _ _ _ _ Hppc)
      as [Hl [Hlr [Hri Hia]]].
    assert (Hiff : PartialPlanCost a del ch p (i + 1) l r c <->
             exists c' d, PartialPlanCost a del ch p i l r c' /\
               (d = -1 \/ d = 0 \/ d = 1) /\ Z.divide p (Znth i a 0 + d) /\
               c = c' + (if Z.eq_dec d 0 then 0 else ch))
      by (apply ppc_snoc__cfp_step_09; lia).
    apply Hiff in Hppc.
    destruct Hppc as [c' [d [Hppc' [Hd [Hdiv Hc]]]]].
    exists c', d.
    split; [| split; [exact Hd | split; [exact Hdiv | exact Hc]]].
    destruct (Z.eq_dec r i) as [Hre | Hrne].
    + subst r.
      destruct (Z.eq_dec l 0) as [Hl0 | Hl0].
      * subst l. right. left. exact Hppc'.
      * destruct (Z.eq_dec l i) as [Hli | Hli].
        { subst l. left.
          apply dpkeep_sub_dpafter__cfp_step_09; [lia | lia | exact Hppc']. }
        { right. right. exists l. split; [lia | split; [lia | exact Hppc']]. }
    + left. exists l, r. split; [lia | exact Hppc'].
  - intros [c' [d [Hsrc [Hd [Hdiv Hc]]]]].
    assert (Hone : forall l r, 0 <= l -> l <= r -> r <= i ->
              PartialPlanCost a del ch p i l r c' ->
              PartialPlanCost a del ch p (i + 1) l r c).
    { intros l r Hl0 Hlr Hri Hppc.
      assert (Hiff : PartialPlanCost a del ch p (i + 1) l r c <->
               exists c'' d', PartialPlanCost a del ch p i l r c'' /\
                 (d' = -1 \/ d' = 0 \/ d' = 1) /\ Z.divide p (Znth i a 0 + d') /\
                 c = c'' + (if Z.eq_dec d' 0 then 0 else ch))
        by (apply ppc_snoc__cfp_step_09; lia).
      apply Hiff. exists c', d.
      split; [exact Hppc | split; [exact Hd | split; [exact Hdiv | exact Hc]]]. }
    destruct Hsrc as [HA | [HF | HK]].
    + destruct HA as [l [r [Hr Hppc]]].
      pose proof (ppc_bounds__cfp_step_09 _ _ _ _ _ _ _ _ Hppc)
        as [Hl [Hlr [Hri Hia]]].
      exists l, r. split; [lia |].
      apply Hone; [lia | lia | lia | exact Hppc].
    + exists 0, i. split; [lia |].
      apply Hone; [lia | lia | lia | exact HF].
    + destruct HK as [l [Hl1 [Hl2 Hppc]]].
      exists l, i. split; [lia |].
      apply Hone; [lia | lia | lia | exact Hppc].
Qed.
Lemma dpvalue_le__cfp_step_09 :
  forall (X : Z -> Prop) (v c : Z), DPValue X v -> X c -> v <= c.
Proof.
  intros X v c HD HX.
  unfold DPValue, min_value_of_subset_with_default, min_value_of_subset,
         min_object_of_subset in HD.
  destruct HD as [[[w [[Hin Hmin] Heq]] Hle] | [Hall Heq]].
  - specialize (Hmin c HX). simpl in Hmin, Heq. lia.
  - specialize (Hall c HX). simpl in Hall. lia.
Qed.
Lemma dpvalue_le_inf__cfp_step_09 :
  forall (X : Z -> Prop) (v : Z), DPValue X v -> v <= INF.
Proof.
  intros X v H.
  unfold DPValue, min_value_of_subset_with_default in H.
  destruct H as [[_ Hle] | [_ Heq]]; [exact Hle | lia].
Qed.
Lemma dpvalue_mem__cfp_step_09 :
  forall (X : Z -> Prop) (v : Z), DPValue X v -> v <> INF -> X v.
Proof.
  intros X v H Hne.
  unfold DPValue, min_value_of_subset_with_default, min_value_of_subset,
         min_object_of_subset in H.
  destruct H as [[[w [[Hin Hmin] Heq]] Hle] | [Hall Heq]].
  - simpl in Heq. subst w. exact Hin.
  - contradiction.
Qed.
Lemma dpvalue_intro__cfp_step_09 :
  forall (X : Z -> Prop) (m : Z),
    X m -> (forall c, X c -> m <= c) -> m <= INF -> DPValue X m.
Proof.
  intros X m HX Hmin Hle.
  unfold DPValue, min_value_of_subset_with_default.
  left. split; [| exact Hle].
  unfold min_value_of_subset, min_object_of_subset.
  exists m. split; [split |].
  - exact HX.
  - intros b Hb. simpl. apply Hmin. exact Hb.
  - reflexivity.
Qed.
Lemma dpvalue_inf__cfp_step_09 :
  forall (X : Z -> Prop), (forall c, X c -> INF <= c) -> DPValue X INF.
Proof.
  intros X H.
  unfold DPValue, min_value_of_subset_with_default.
  right. split; [| reflexivity].
  intros a Ha. simpl. apply H. exact Ha.
Qed.
Lemma dpvalue_unique__cfp_step_09 :
  forall (X : Z -> Prop) (v w : Z), DPValue X v -> DPValue X w -> v = w.
Proof.
  intros X v w Hv Hw.
  pose proof (dpvalue_le_inf__cfp_step_09 X v Hv) as Hvi.
  pose proof (dpvalue_le_inf__cfp_step_09 X w Hw) as Hwi.
  destruct (Z.eq_dec v INF) as [Hv0 | Hv0].
  - destruct (Z.eq_dec w INF) as [Hw0 | Hw0]; [lia |].
    pose proof (dpvalue_mem__cfp_step_09 X w Hw Hw0) as HXw.
    pose proof (dpvalue_le__cfp_step_09 X v w Hv HXw). lia.
  - pose proof (dpvalue_mem__cfp_step_09 X v Hv Hv0) as HXv.
    pose proof (dpvalue_le__cfp_step_09 X w v Hw HXv).
    destruct (Z.eq_dec w INF) as [Hw0 | Hw0]; [lia |].
    pose proof (dpvalue_mem__cfp_step_09 X w Hw Hw0) as HXw.
    pose proof (dpvalue_le__cfp_step_09 X v w Hv HXw). lia.
Qed.
Lemma elemcost_bound__cfp_step_09 :
  forall (ch p v : Z),
    0 <= ch -> ElemCost ch p v <> INF -> 0 <= ElemCost ch p v <= ch.
Proof.
  intros ch p v Hch H.
  unfold ElemCost in *.
  destruct (Z.eqb (v mod p) 0); [lia |].
  destruct (orb (Z.eqb ((v - 1) mod p) 0) (Z.eqb ((v + 1) mod p) 0));
    [lia | exfalso; apply H; reflexivity].
Qed.
Lemma elemcost_le__cfp_step_09 :
  forall (ch p v d : Z), 0 <= ch -> 2 <= p ->
    (d = -1 \/ d = 0 \/ d = 1) -> Z.divide p (v + d) ->
    ElemCost ch p v <= (if Z.eq_dec d 0 then 0 else ch).
Proof.
  intros ch p v d Hch Hp Hd Hdiv.
  unfold ElemCost.
  destruct (Z.eqb (v mod p) 0) eqn:E0.
  - destruct (Z.eq_dec d 0); lia.
  - destruct Hd as [H|[H|H]]; subst d.
    + assert (Hv : Z.divide p (v - 1))
        by (replace (v - 1) with (v + -1) by lia; exact Hdiv).
      assert (Hm : (v - 1) mod p = 0) by (apply Z.mod_divide; [lia | exact Hv]).
      rewrite Hm, Z.eqb_refl. simpl.
      destruct (Z.eq_dec (-1) 0); lia.
    + exfalso.
      assert (Hv : Z.divide p v)
        by (rewrite <- (Z.add_0_r v); exact Hdiv).
      assert (Hm : v mod p = 0) by (apply Z.mod_divide; [lia | exact Hv]).
      rewrite Hm, Z.eqb_refl in E0. discriminate.
    + assert (Hm : (v + 1) mod p = 0)
        by (apply Z.mod_divide; [lia | exact Hdiv]).
      rewrite Hm, Z.eqb_refl, orb_true_r.
      destruct (Z.eq_dec 1 0); lia.
Qed.
Lemma elemcost_attained__cfp_step_09 :
  forall (ch p v : Z), 2 <= p -> ElemCost ch p v <> INF ->
    exists d, (d = -1 \/ d = 0 \/ d = 1) /\ Z.divide p (v + d) /\
      (if Z.eq_dec d 0 then 0 else ch) = ElemCost ch p v.
Proof.
  intros ch p v Hp H.
  unfold ElemCost in *.
  destruct (Z.eqb (v mod p) 0) eqn:E0.
  - exists 0. split; [tauto | split].
    + rewrite Z.add_0_r. apply Z.mod_divide; [lia |].
      apply Z.eqb_eq. exact E0.
    + destruct (Z.eq_dec 0 0); [reflexivity | lia].
  - destruct (Z.eqb ((v - 1) mod p) 0) eqn:E1.
    + exists (-1). split; [tauto | split].
      * replace (v + -1) with (v - 1) by lia.
        apply Z.mod_divide; [lia |]. apply Z.eqb_eq. exact E1.
      * simpl. destruct (Z.eq_dec (-1) 0); [lia | reflexivity].
    + destruct (Z.eqb ((v + 1) mod p) 0) eqn:E2.
      * exists 1. split; [tauto | split].
        { apply Z.mod_divide; [lia |]. apply Z.eqb_eq. exact E2. }
        { simpl. destruct (Z.eq_dec 1 0); [lia | reflexivity]. }
      * exfalso. simpl in H. apply H. reflexivity.
Qed.
Lemma dpvalue_union2__cfp_step_09 :
  forall (X1 X2 Y : Z -> Prop) (m1 m2 : Z),
    DPValue X1 m1 -> DPValue X2 m2 -> m1 <= m2 ->
    (forall c, Y c <-> X1 c \/ X2 c) -> DPValue Y m1.
Proof.
  intros X1 X2 Y m1 m2 H1 H2 Hle HY.
  pose proof (dpvalue_le_inf__cfp_step_09 X1 m1 H1) as Hi1.
  pose proof (dpvalue_le_inf__cfp_step_09 X2 m2 H2) as Hi2.
  destruct (Z.eq_dec m1 INF) as [He | He].
  - subst m1.
    apply dpvalue_inf__cfp_step_09.
    intros c Hc. apply HY in Hc. destruct Hc as [Hc | Hc].
    + apply (dpvalue_le__cfp_step_09 X1); assumption.
    + pose proof (dpvalue_le__cfp_step_09 X2 m2 c H2 Hc). lia.
  - apply dpvalue_intro__cfp_step_09; [| | lia].
    + apply HY. left. apply dpvalue_mem__cfp_step_09; assumption.
    + intros c Hc. apply HY in Hc. destruct Hc as [Hc | Hc].
      * apply (dpvalue_le__cfp_step_09 X1); assumption.
      * pose proof (dpvalue_le__cfp_step_09 X2 m2 c H2 Hc). lia.
Qed.
Lemma dpvalue_union3__cfp_step_09 :
  forall (X1 X2 X3 Y : Z -> Prop) (m1 m2 m3 : Z),
    DPValue X1 m1 -> DPValue X2 m2 -> DPValue X3 m3 ->
    m3 <= m1 -> m3 <= m2 ->
    (forall c, Y c <-> X1 c \/ X2 c \/ X3 c) -> DPValue Y m3.
Proof.
  intros X1 X2 X3 Y m1 m2 m3 H1 H2 H3 Hle1 Hle2 HY.
  pose proof (dpvalue_le_inf__cfp_step_09 X1 m1 H1) as Hi1.
  pose proof (dpvalue_le_inf__cfp_step_09 X2 m2 H2) as Hi2.
  pose proof (dpvalue_le_inf__cfp_step_09 X3 m3 H3) as Hi3.
  destruct (Z.eq_dec m3 INF) as [He | He].
  - subst m3.
    apply dpvalue_inf__cfp_step_09.
    intros c Hc. apply HY in Hc. destruct Hc as [Hc | [Hc | Hc]].
    + pose proof (dpvalue_le__cfp_step_09 X1 m1 c H1 Hc). lia.
    + pose proof (dpvalue_le__cfp_step_09 X2 m2 c H2 Hc). lia.
    + apply (dpvalue_le__cfp_step_09 X3); assumption.
  - apply dpvalue_intro__cfp_step_09; [| | lia].
    + apply HY. right. right. apply dpvalue_mem__cfp_step_09; assumption.
    + intros c Hc. apply HY in Hc. destruct Hc as [Hc | [Hc | Hc]].
      * pose proof (dpvalue_le__cfp_step_09 X1 m1 c H1 Hc). lia.
      * pose proof (dpvalue_le__cfp_step_09 X2 m2 c H2 Hc). lia.
      * apply (dpvalue_le__cfp_step_09 X3); assumption.
Qed.
Lemma dpvalue_shift_fin__cfp_step_09 :
  forall (X Y : Z -> Prop) (m k : Z),
    0 <= k -> DPValue X m -> m <> INF -> m + k <= INF ->
    (forall c, Y c <-> exists c', X c' /\ c = c' + k) ->
    DPValue Y (m + k).
Proof.
  intros X Y m k Hk HX Hne Hb HY.
  apply dpvalue_intro__cfp_step_09; [| | lia].
  - apply HY. exists m.
    split; [apply dpvalue_mem__cfp_step_09; assumption | reflexivity].
  - intros c Hc. apply HY in Hc. destruct Hc as [c' [Hc' Heq]].
    pose proof (dpvalue_le__cfp_step_09 X m c' HX Hc'). lia.
Qed.
Lemma dpvalue_shift_inf__cfp_step_09 :
  forall (X Y : Z -> Prop) (k : Z),
    0 <= k -> DPValue X INF ->
    (forall c, Y c <-> exists c', X c' /\ c = c' + k) ->
    DPValue Y INF.
Proof.
  intros X Y k Hk HX HY.
  apply dpvalue_inf__cfp_step_09.
  intros c Hc. apply HY in Hc. destruct Hc as [c' [Hc' Heq]].
  pose proof (dpvalue_le__cfp_step_09 X INF c' HX Hc'). lia.
Qed.
Lemma dpvalue_snoc_fin__cfp_step_09 :
  forall (X Y : Z -> Prop) (ch p v m : Z),
    0 <= ch -> 2 <= p ->
    ElemCost ch p v <> INF ->
    DPValue X m -> m <> INF -> m + ElemCost ch p v <= INF ->
    (forall c, Y c <-> exists c' d, X c' /\ (d = -1 \/ d = 0 \/ d = 1) /\
        Z.divide p (v + d) /\ c = c' + (if Z.eq_dec d 0 then 0 else ch)) ->
    DPValue Y (m + ElemCost ch p v).
Proof.
  intros X Y ch p v m Hch Hp He HX Hne Hb HY.
  destruct (elemcost_attained__cfp_step_09 ch p v Hp He) as [d [Hd [Hdiv Hcost]]].
  apply dpvalue_intro__cfp_step_09; [| | lia].
  - apply HY. exists m, d.
    split; [apply dpvalue_mem__cfp_step_09; assumption |].
    split; [exact Hd | split; [exact Hdiv | lia]].
  - intros c Hc. apply HY in Hc.
    destruct Hc as [c' [d' [Hc' [Hd' [Hdiv' Heq]]]]].
    pose proof (dpvalue_le__cfp_step_09 X m c' HX Hc').
    pose proof (elemcost_le__cfp_step_09 ch p v d' Hch Hp Hd' Hdiv').
    lia.
Qed.
Lemma dpvalue_snoc_inf__cfp_step_09 :
  forall (X Y : Z -> Prop) (ch p v : Z),
    0 <= ch ->
    DPValue X INF ->
    (forall c, Y c <-> exists c' d, X c' /\ (d = -1 \/ d = 0 \/ d = 1) /\
        Z.divide p (v + d) /\ c = c' + (if Z.eq_dec d 0 then 0 else ch)) ->
    DPValue Y INF.
Proof.
  intros X Y ch p v Hch HX HY.
  apply dpvalue_inf__cfp_step_09.
  intros c Hc. apply HY in Hc.
  destruct Hc as [c' [d' [Hc' [Hd' [Hdiv' Heq]]]]].
  pose proof (dpvalue_le__cfp_step_09 X INF c' HX Hc').
  destruct (Z.eq_dec d' 0); lia.
Qed.
Lemma ppc_bound__cfp_step_09 :
  forall (a : list Z) (del ch p i l r c : Z),
    0 <= del -> del <= 1000000000 -> 0 <= ch -> ch <= 1000000000 ->
    Zlength a <= 1000000 ->
    PartialPlanCost a del ch p i l r c ->
    0 <= c <= 3000000000000000.
Proof.
  intros a del ch p i l r c Hd0 Hd1 Hc0 Hc1 Ha H.
  unfold PartialPlanCost in H.
  destruct H as [H1 [H2 [H3 [H4 [delta [result [HA [HD HC]]]]]]]].
  destruct HA as [HLen [HFa HRe]].
  assert (Hdl : Zlength delta = l + (i - r)).
  { rewrite HLen, Zlength_app.
    rewrite (Zlength_sublist 0 l a) by lia.
    rewrite (Zlength_sublist r i a) by lia.
    lia. }
  pose proof (count_bound__cfp_step_09 (-1) delta) as Hb1.
  pose proof (count_bound__cfp_step_09 1 delta) as Hb2.
  unfold ChangeCost in HC.
  assert (T1 : 0 <= (r - l) * del <= 1000000 * 1000000000) by nia.
  assert (T2 : 0 <= Count (-1) delta * ch <= 1000000 * 1000000000) by nia.
  assert (T3 : 0 <= Count 1 delta * ch <= 1000000 * 1000000000) by nia.
  lia.
Qed.
Lemma cfp_state_finite_bound__cfp_step_09 :
  forall (a : list Z) (del ch p i keep cutFresh cutAfterKeep after : Z),
    0 <= del -> del <= 1000000000 -> 0 <= ch -> ch <= 1000000000 ->
    Zlength a <= 1000000 ->
    CostForPrimeState a del ch p i keep cutFresh cutAfterKeep after ->
    (keep <> INF -> 0 <= keep <= 3000000000000000) /\
    (cutFresh <> INF -> 0 <= cutFresh <= 3000000000000000) /\
    (cutAfterKeep <> INF -> 0 <= cutAfterKeep <= 3000000000000000) /\
    (after <> INF -> 0 <= after <= 3000000000000000).
Proof.
  intros a del ch p i keep cutFresh cutAfterKeep after Hd0 Hd1 Hc0 Hc1 Ha HS.
  destruct HS as [HK [HF [HC HA]]].
  split; [| split; [| split]].
  - intros Hne.
    pose proof (dpvalue_mem__cfp_step_09 _ _ HK Hne) as Hm.
    unfold DPKeep in Hm.
    apply (ppc_bound__cfp_step_09 a del ch p i i i keep); assumption.
  - intros Hne.
    pose proof (dpvalue_mem__cfp_step_09 _ _ HF Hne) as Hm.
    unfold DPCutFresh in Hm.
    apply (ppc_bound__cfp_step_09 a del ch p i 0 i cutFresh); assumption.
  - intros Hne.
    pose proof (dpvalue_mem__cfp_step_09 _ _ HC Hne) as Hm.
    unfold DPCutAfterKeep in Hm.
    destruct Hm as [l [Hl1 [Hl2 Hm]]].
    apply (ppc_bound__cfp_step_09 a del ch p i l i cutAfterKeep); assumption.
  - intros Hne.
    pose proof (dpvalue_mem__cfp_step_09 _ _ HA Hne) as Hm.
    unfold DPAfter in Hm.
    destruct Hm as [l [r [Hr Hm]]].
    apply (ppc_bound__cfp_step_09 a del ch p i l r after); assumption.
Qed.
Lemma dpcutafterkeep_zero__cfp_step_09 :
  forall (a : list Z) (del ch p v : Z),
    DPValue (DPCutAfterKeep a del ch p 0) v -> v = INF.
Proof.
  intros a del ch p v H.
  apply (dpvalue_unique__cfp_step_09 (DPCutAfterKeep a del ch p 0));
    [exact H |].
  apply dpvalue_inf__cfp_step_09.
  intros c Hc. unfold DPCutAfterKeep in Hc.
  destruct Hc as [l [H1 [H2 H3]]]. lia.
Qed.
Lemma dpcutfresh_mem__cfp_step_09 :
  forall (a : list Z) (del ch p i : Z),
    0 <= i -> i <= Zlength a -> DPCutFresh a del ch p i (i * del).
Proof.
  intros a del ch p i H0 H1.
  unfold DPCutFresh, PartialPlanCost.
  repeat split; try lia.
  exists nil, nil.
  assert (Hk : sublist 0 0 a ++ sublist i i a = nil).
  { rewrite (sublist_empty__cfp_step_09 a 0 0) by lia.
    rewrite (sublist_empty__cfp_step_09 a i i) by lia.
    reflexivity. }
  rewrite Hk.
  split.
  - unfold Adjusted.
    split; [reflexivity | split; [constructor | reflexivity]].
  - split; [constructor |].
    unfold ChangeCost.
    rewrite !count_nil__cfp_step_09.
    replace (i - 0) with i by lia.
    lia.
Qed.
Lemma dpcutfresh_finite__cfp_step_09 :
  forall (a : list Z) (del ch p i cf : Z),
    0 <= i -> i <= Zlength a ->
    DPValue (DPCutFresh a del ch p i) cf -> cf <= i * del.
Proof.
  intros a del ch p i cf H0 H1 H2.
  apply (dpvalue_le__cfp_step_09 _ _ _ H2).
  apply dpcutfresh_mem__cfp_step_09; assumption.
Qed.
Lemma cfp_state_step__cfp_step_09 :
  forall (a : list Z)
         (del ch p i keep cutFresh cutAfterKeep after cost newKeep : Z),
    0 <= del -> 0 <= ch -> 2 <= p ->
    0 < i -> i < Zlength a ->
    cost = ElemCost ch p (Znth i a 0) ->
    cost <> INF ->
    CostForPrimeState a del ch p i keep cutFresh cutAfterKeep after ->
    cutAfterKeep <> INF ->
    cutFresh <> INF ->
    cutAfterKeep <= keep ->
    cutAfterKeep <= cutFresh ->
    cutAfterKeep <= after ->
    cutFresh + del <= INF ->
    cutAfterKeep + del <= INF ->
    cutAfterKeep + cost <= INF ->
    ((keep = INF /\ newKeep = INF) \/
     (keep <> INF /\ newKeep = keep + cost /\ keep + cost <= INF)) ->
    CostForPrimeState a del ch p (i + 1) newKeep
      (cutFresh + del) (cutAfterKeep + del) (cutAfterKeep + cost).
Proof.
  intros a del ch p i keep cutFresh cutAfterKeep after cost newKeep
         Hdel Hch Hp Hi Hn Hcost Hcne HS Hcak Hcf Hk1 Hk2 Hk3 Hb1 Hb2 Hb3 Hkeep.
  destruct HS as [HK [HF [HC HA]]].
  subst cost.
  unfold CostForPrimeState.
  split; [| split; [| split]].
  - destruct Hkeep as [[He1 He2] | [He1 [He2 He3]]].
    + subst newKeep. rewrite He1 in HK.
      apply (dpvalue_snoc_inf__cfp_step_09 (DPKeep a del ch p i)
               (DPKeep a del ch p (i + 1)) ch p (Znth i a 0) Hch HK).
      intros c. apply dpkeep_step_set__cfp_step_09; lia.
    + subst newKeep.
      apply (dpvalue_snoc_fin__cfp_step_09 (DPKeep a del ch p i)
               (DPKeep a del ch p (i + 1)) ch p (Znth i a 0) keep
               Hch Hp Hcne HK He1 He3).
      intros c. apply dpkeep_step_set__cfp_step_09; lia.
  - apply (dpvalue_shift_fin__cfp_step_09 (DPCutFresh a del ch p i)
             (DPCutFresh a del ch p (i + 1)) cutFresh del Hdel HF Hcf Hb1).
    intros c. apply dpcutfresh_step_set__cfp_step_09; lia.
  - assert (HU : DPValue
      (fun c => DPCutAfterKeep a del ch p i c \/ DPKeep a del ch p i c)
      cutAfterKeep).
    { apply (dpvalue_union2__cfp_step_09 (DPCutAfterKeep a del ch p i)
               (DPKeep a del ch p i) _ cutAfterKeep keep HC HK Hk1).
      intros c. tauto. }
    apply (dpvalue_shift_fin__cfp_step_09
             (fun c => DPCutAfterKeep a del ch p i c \/ DPKeep a del ch p i c)
             (DPCutAfterKeep a del ch p (i + 1)) cutAfterKeep del
             Hdel HU Hcak Hb2).
    intros c. apply dpcutafterkeep_step_set__cfp_step_09; lia.
  - assert (HU : DPValue
      (fun c => DPAfter a del ch p i c \/ DPCutFresh a del ch p i c \/
                DPCutAfterKeep a del ch p i c) cutAfterKeep).
    { apply (dpvalue_union3__cfp_step_09 (DPAfter a del ch p i)
               (DPCutFresh a del ch p i) (DPCutAfterKeep a del ch p i) _
               after cutFresh cutAfterKeep HA HF HC Hk3 Hk2).
      intros c. tauto. }
    apply (dpvalue_snoc_fin__cfp_step_09
             (fun c => DPAfter a del ch p i c \/ DPCutFresh a del ch p i c \/
                       DPCutAfterKeep a del ch p i c)
             (DPAfter a del ch p (i + 1)) ch p (Znth i a 0) cutAfterKeep
             Hch Hp Hcne HU Hcak Hb3).
    intros c. apply dpafter_step_set__cfp_step_09; lia.
Qed.
Lemma cfp_state_i0_absurd__cfp_step_09 :
  forall (a : list Z) (del ch p i keep cutFresh cutAfterKeep after : Z),
    CostForPrimeState a del ch p i keep cutFresh cutAfterKeep after ->
    i <= 0 -> 0 <= i ->
    cutAfterKeep = 4611686018427387904.
Proof.
  intros a del ch p i keep cutFresh cutAfterKeep after HS Hi1 Hi2.
  destruct HS as [HK [HF [HC HA]]].
  assert (Hz : i = 0) by lia.
  rewrite Hz in HC.
  pose proof (dpcutafterkeep_zero__cfp_step_09 a del ch p cutAfterKeep HC) as He.
  unfold INF in He. lia.
Qed.
Lemma cfp_state_cutfresh_lt_inf__cfp_step_09 :
  forall (a : list Z) (del ch p i keep cutFresh cutAfterKeep after : Z),
    CostForPrimeState a del ch p i keep cutFresh cutAfterKeep after ->
    0 <= i -> i <= Zlength a -> Zlength a <= 1000000 ->
    0 <= del -> del <= 1000000000 ->
    cutFresh < 4611686018427387904.
Proof.
  intros a del ch p i keep cutFresh cutAfterKeep after HS Hi1 Hi2 Ha Hd0 Hd1.
  destruct HS as [HK [HF [HC HA]]].
  pose proof (dpcutfresh_finite__cfp_step_09 a del ch p i cutFresh Hi1 Hi2 HF) as He.
  assert (Hb : i * del <= 1000000 * 1000000000) by nia.
  lia.
Qed.
Lemma dpvalue_le__cfp_step_10 : forall (S : Z -> Prop) v c,
  DPValue S v -> S c -> v <= c.
Proof.
  intros S v c H Hc.
  unfold DPValue, min_value_of_subset_with_default, min_value_of_subset,
         min_object_of_subset in H.
  sets_unfold in H.
  destruct H as [[[u [[Hu Hmin] Hfu]] Hle] | [Hall Heq]].
  - simpl in *. subst. apply Hmin. exact Hc.
  - subst. apply Hall. exact Hc.
Qed.
Lemma dpvalue_mem__cfp_step_10 : forall (S : Z -> Prop) v,
  DPValue S v -> v <> INF -> S v.
Proof.
  intros S v H Hne.
  unfold DPValue, min_value_of_subset_with_default, min_value_of_subset,
         min_object_of_subset in H.
  sets_unfold in H.
  destruct H as [[[u [[Hu Hmin] Hfu]] Hle] | [Hall Heq]].
  - simpl in *. subst. exact Hu.
  - contradiction.
Qed.
Lemma dpvalue_ub__cfp_step_10 : forall (S : Z -> Prop) v,
  DPValue S v -> v <= INF.
Proof.
  intros S v H.
  unfold DPValue, min_value_of_subset_with_default in H.
  destruct H as [[_ Hle] | [_ Heq]]; [exact Hle | subst; lia].
Qed.
Lemma dpvalue_intro__cfp_step_10 : forall (S : Z -> Prop) v,
  S v -> (forall c, S c -> v <= c) -> v <= INF -> DPValue S v.
Proof.
  intros S v Hmem Hmin Hle.
  unfold DPValue, min_value_of_subset_with_default, min_value_of_subset,
         min_object_of_subset.
  sets_unfold. left. split; [| exact Hle].
  exists v. split; [| reflexivity]. split; [exact Hmem |]. simpl. exact Hmin.
Qed.
Lemma dpvalue_inf_intro__cfp_step_10 : forall (S : Z -> Prop),
  (forall c, S c -> INF <= c) -> DPValue S INF.
Proof.
  intros S H.
  unfold DPValue, min_value_of_subset_with_default.
  sets_unfold. right. split; [| reflexivity]. simpl. exact H.
Qed.
Lemma dpvalue_unique__cfp_step_10 : forall (S : Z -> Prop) u v,
  DPValue S u -> DPValue S v -> u = v.
Proof.
  intros S u v Hu Hv.
  destruct (Z.eq_dec u INF) as [Hu0 | Hu0].
  - destruct (Z.eq_dec v INF) as [Hv0 | Hv0]; [congruence |].
    pose proof (dpvalue_le__cfp_step_10 _ _ _ Hu (dpvalue_mem__cfp_step_10 _ _ Hv Hv0)).
    pose proof (dpvalue_ub__cfp_step_10 _ _ Hv). lia.
  - destruct (Z.eq_dec v INF) as [Hv0 | Hv0].
    + pose proof (dpvalue_le__cfp_step_10 _ _ _ Hv (dpvalue_mem__cfp_step_10 _ _ Hu Hu0)).
      pose proof (dpvalue_ub__cfp_step_10 _ _ Hu). lia.
    + pose proof (dpvalue_le__cfp_step_10 _ _ _ Hv (dpvalue_mem__cfp_step_10 _ _ Hu Hu0)).
      pose proof (dpvalue_le__cfp_step_10 _ _ _ Hu (dpvalue_mem__cfp_step_10 _ _ Hv Hv0)).
      lia.
Qed.
Lemma dpvalue_empty__cfp_step_10 : forall (S : Z -> Prop) v,
  (forall c, ~ S c) -> DPValue S v -> v = INF.
Proof.
  intros S v Hemp H.
  destruct (Z.eq_dec v INF) as [? | Hne]; [assumption |].
  exfalso. apply (Hemp v). apply dpvalue_mem__cfp_step_10; assumption.
Qed.

(* ================= Count layer ================= *)
Lemma fold_filter_indicator__cfp_step_10 : forall (l : list Z) (P : Z -> Prop),
  fold_right (fun _ acc : Z => 1 + acc) 0
    (filter (fun x => if prop_dec (P x) then true else false) l) =
  fold_right (fun x acc : Z => (if prop_dec (P x) then 1 else 0) + acc) 0 l.
Proof.
  induction l as [| a l IH]; intros P; simpl; [reflexivity |].
  destruct (prop_dec (P a)); simpl; rewrite IH; lia.
Qed.
Lemma count_as_sum__cfp_step_10 : forall x xs,
  Count x xs =
  sum (fun i => 0 <= i < Zlength xs)
      (fun i : Z => if prop_dec (Znth i xs 0 = x) then 1 else 0).
Proof.
  intros x xs. unfold Count, set_card, sum. simpl.
  apply fold_filter_indicator__cfp_step_10.
Qed.
Lemma count_nil__cfp_step_10 : forall x, Count x [] = 0.
Proof. intros. reflexivity. Qed.
Lemma count_app_single__cfp_step_10 : forall x xs e,
  Count x (xs ++ [e]) = Count x xs + (if Z.eq_dec e x then 1 else 0).
Proof.
  intros x xs e.
  rewrite !count_as_sum__cfp_step_10.
  pose proof (Zlength_nonneg xs) as Hnn.
  replace (Zlength (xs ++ [e])) with (Zlength xs + 1)
    by (rewrite Zlength_app; reflexivity).
  rewrite sum_Z_range_extend_right by lia.
  f_equal.
  - apply sum_Z_range_ext. intros i Hi.
    rewrite (@app_Znth1 Z 0) by lia. reflexivity.
  - rewrite (@app_Znth2 Z 0) by lia.
    replace (Zlength xs - Zlength xs) with 0 by lia.
    replace (Znth 0 [e] 0) with e by reflexivity.
    destruct (prop_dec (e = x)); destruct (Z.eq_dec e x); congruence.
Qed.
Lemma count_bounds__cfp_step_10 : forall x xs, 0 <= Count x xs <= Zlength xs.
Proof.
  intros x xs. pose proof (Zlength_nonneg xs) as Hnn.
  rewrite count_as_sum__cfp_step_10.
  pose proof (sum_Z_range_bounds 0 (Zlength xs)
                (fun i : Z => if prop_dec (Znth i xs 0 = x) then 1 else 0) 0 1) as Hb.
  destruct Hb as [Hlo Hhi]; [lia | | lia].
  intros y Hy. destruct (prop_dec (Znth y xs 0 = x)); lia.
Qed.

(* ================= list / Adjusted / ChangeCost layer ================= *)
Lemma combine_app__cfp_step_10 : forall (l1 m1 l2 m2 : list Z),
  length l1 = length m1 ->
  combine (l1 ++ l2) (m1 ++ m2) = combine l1 m1 ++ combine l2 m2.
Proof.
  induction l1 as [| a l1 IH]; intros m1 l2 m2 Hlen.
  - destruct m1; simpl in *; [reflexivity | discriminate].
  - destruct m1 as [| b m1]; simpl in *; [discriminate |].
    rewrite IH by lia. reflexivity.
Qed.
Lemma sublist_empty__cfp_step_10 : forall (a : list Z) (j : Z),
  sublist j j a = [].
Proof.
  intros a j. unfold sublist. apply skipn_all2.
  rewrite length_firstn. apply Nat.le_min_l.
Qed.
Lemma changecost_app_single__cfp_step_10 : forall del ch l r d e,
  (e = -1 \/ e = 0 \/ e = 1) ->
  ChangeCost del ch l r (d ++ [e]) =
  ChangeCost del ch l r d + (if Z.eq_dec e 0 then 0 else ch).
Proof.
  intros del ch l r d e He. unfold ChangeCost.
  rewrite !count_app_single__cfp_step_10.
  destruct He as [-> | [-> | ->]];
  repeat (match goal with |- context [Z.eq_dec ?u ?v] => destruct (Z.eq_dec u v) end);
  try lia.
Qed.
Lemma adjusted_app_single_intro__cfp_step_10 : forall ks k d e r',
  Adjusted ks d r' -> (e = -1 \/ e = 0 \/ e = 1) ->
  Adjusted (ks ++ [k]) (d ++ [e]) (r' ++ [k + e]).
Proof.
  intros ks k d e r' [Hlen [Hall Hres]] He.
  split; [| split].
  - rewrite !Zlength_app_cons. lia.
  - apply Forall_app. split; [exact Hall | constructor; [exact He | constructor]].
  - rewrite combine_app__cfp_step_10.
    + rewrite map_app. simpl. rewrite Hres. reflexivity.
    + apply Nat2Z.inj. rewrite <- !Zlength_correct. lia.
Qed.
Lemma adjusted_app_single_elim__cfp_step_10 : forall ks k delta result,
  Adjusted (ks ++ [k]) delta result ->
  exists d e r', delta = d ++ [e] /\ result = r' ++ [k + e] /\
                 Adjusted ks d r' /\ (e = -1 \/ e = 0 \/ e = 1).
Proof.
  intros ks k delta result [Hlen [Hall Hres]].
  rewrite Zlength_app_cons in Hlen.
  pose proof (Zlength_nonneg ks) as Hks.
  assert (delta <> []) as Hne.
  { intro Hd. subst delta. rewrite Zlength_nil in Hlen. lia. }
  destruct (exists_last Hne) as [d [e Hd]]. subst delta.
  rewrite Zlength_app_cons in Hlen.
  apply Forall_app in Hall. destruct Hall as [Halld Halle].
  assert (He : e = -1 \/ e = 0 \/ e = 1)
    by (inversion Halle; auto).
  assert (Hcl : length ks = length d).
  { apply Nat2Z.inj. rewrite <- !Zlength_correct. lia. }
  exists d, e, (map (fun q : Z * Z => fst q + snd q) (combine ks d)).
  split; [reflexivity |].
  split.
  - rewrite Hres. rewrite combine_app__cfp_step_10 by exact Hcl.
    rewrite map_app. reflexivity.
  - split; [| exact He].
    split; [lia | split; [exact Halld | reflexivity]].
Qed.

(* ================= PartialPlanCost layer ================= *)
Lemma ppc_congr__cfp_step_10 : forall a del ch p i1 l1 r1 i2 l2 r2 c,
  0 <= l2 -> l2 <= r2 -> r2 <= i2 -> i2 <= Zlength a ->
  sublist 0 l2 a ++ sublist r2 i2 a = sublist 0 l1 a ++ sublist r1 i1 a ->
  r2 - l2 = r1 - l1 ->
  PartialPlanCost a del ch p i1 l1 r1 c ->
  PartialPlanCost a del ch p i2 l2 r2 c.
Proof.
  intros a del ch p i1 l1 r1 i2 l2 r2 c H0 H1 H2 H3 Hkept Hlen Hppc.
  destruct Hppc as [_ [_ [_ [_ [delta [result [Hadj [Hdiv Hc]]]]]]]].
  repeat split; try lia.
  exists delta, result. rewrite Hkept.
  split; [exact Hadj | split; [exact Hdiv |]].
  subst c. unfold ChangeCost. rewrite Hlen. reflexivity.
Qed.
Lemma ppc_keep_step_elim__cfp_step_10 : forall a del ch p i l r c,
  0 <= i -> i < Zlength a -> 0 <= l -> l <= r -> r <= i ->
  PartialPlanCost a del ch p (i+1) l r c ->
  exists c' e, PartialPlanCost a del ch p i l r c' /\
               (e = -1 \/ e = 0 \/ e = 1) /\
               Z.divide p (Znth i a 0 + e) /\
               c = c' + (if Z.eq_dec e 0 then 0 else ch).
Proof.
  intros a del ch p i l r c Hi0 Hin Hl0 Hlr Hri Hppc.
  destruct Hppc as [_ [_ [_ [_ [delta [result [Hadj [Hdiv Hc]]]]]]]].
  assert (Hsp : sublist 0 l a ++ sublist r (i+1) a
                = (sublist 0 l a ++ sublist r i a) ++ [Znth i a 0]).
  { rewrite (sublist_split r (i+1) i a) by lia.
    rewrite (@sublist_single Z 0 i a) by lia.
    rewrite app_assoc. reflexivity. }
  rewrite Hsp in Hadj.
  apply adjusted_app_single_elim__cfp_step_10 in Hadj.
  destruct Hadj as [d [e [r' [Hd [Hr [Hadj' He]]]]]].
  subst delta result.
  apply Forall_app in Hdiv. destruct Hdiv as [Hdiv1 Hdiv2].
  exists (ChangeCost del ch l r d), e.
  split; [| split; [exact He | split]].
  - repeat split; try lia.
    exists d, r'. split; [exact Hadj' | split; [exact Hdiv1 | reflexivity]].
  - inversion Hdiv2; auto.
  - subst c. apply changecost_app_single__cfp_step_10. exact He.
Qed.
Lemma ppc_keep_step_intro__cfp_step_10 : forall a del ch p i l r c' e,
  0 <= i -> i < Zlength a -> 0 <= l -> l <= r -> r <= i ->
  PartialPlanCost a del ch p i l r c' ->
  (e = -1 \/ e = 0 \/ e = 1) -> Z.divide p (Znth i a 0 + e) ->
  PartialPlanCost a del ch p (i+1) l r (c' + (if Z.eq_dec e 0 then 0 else ch)).
Proof.
  intros a del ch p i l r c' e Hi0 Hin Hl0 Hlr Hri Hppc He Hdvd.
  destruct Hppc as [_ [_ [_ [_ [delta [result [Hadj [Hdiv Hc]]]]]]]].
  assert (Hsp : sublist 0 l a ++ sublist r (i+1) a
                = (sublist 0 l a ++ sublist r i a) ++ [Znth i a 0]).
  { rewrite (sublist_split r (i+1) i a) by lia.
    rewrite (@sublist_single Z 0 i a) by lia.
    rewrite app_assoc. reflexivity. }
  repeat split; try lia.
  exists (delta ++ [e]), (result ++ [Znth i a 0 + e]).
  rewrite Hsp.
  split; [apply adjusted_app_single_intro__cfp_step_10; assumption |].
  split.
  - apply Forall_app. split; [exact Hdiv | constructor; [exact Hdvd | constructor]].
  - subst c'. symmetry. apply changecost_app_single__cfp_step_10. exact He.
Qed.
Lemma ppc_cut_step_elim__cfp_step_10 : forall a del ch p i l c,
  0 <= i -> i < Zlength a -> 0 <= l -> l <= i ->
  PartialPlanCost a del ch p (i+1) l (i+1) c ->
  PartialPlanCost a del ch p i l i (c - del).
Proof.
  intros a del ch p i l c Hi0 Hin Hl0 Hli Hppc.
  destruct Hppc as [_ [_ [_ [_ [delta [result [Hadj [Hdiv Hc]]]]]]]].
  rewrite sublist_empty__cfp_step_10 in Hadj.
  repeat split; try lia.
  exists delta, result. rewrite sublist_empty__cfp_step_10.
  split; [exact Hadj | split; [exact Hdiv |]].
  subst c. unfold ChangeCost. lia.
Qed.
Lemma ppc_cut_step_intro__cfp_step_10 : forall a del ch p i l c',
  0 <= i -> i < Zlength a -> 0 <= l -> l <= i ->
  PartialPlanCost a del ch p i l i c' ->
  PartialPlanCost a del ch p (i+1) l (i+1) (c' + del).
Proof.
  intros a del ch p i l c' Hi0 Hin Hl0 Hli Hppc.
  destruct Hppc as [_ [_ [_ [_ [delta [result [Hadj [Hdiv Hc]]]]]]]].
  rewrite sublist_empty__cfp_step_10 in Hadj.
  repeat split; try lia.
  exists delta, result. rewrite sublist_empty__cfp_step_10.
  split; [exact Hadj | split; [exact Hdiv |]].
  subst c'. unfold ChangeCost. lia.
Qed.
Lemma dpkeep_shift__cfp_step_10 : forall a del ch p i c,
  0 <= i -> i < Zlength a ->
  (PartialPlanCost a del ch p (i+1) i i c <-> DPKeep a del ch p (i+1) c).
Proof.
  intros a del ch p i c Hi0 Hin.
  assert (Hs : sublist 0 (i+1) a = sublist 0 i a ++ sublist i (i+1) a)
    by (apply sublist_split; lia).
  unfold DPKeep. split; intro H.
  - apply (ppc_congr__cfp_step_10 a del ch p (i+1) i i (i+1) (i+1) (i+1) c);
      try lia; try assumption.
    rewrite sublist_empty__cfp_step_10, app_nil_r. exact Hs.
  - apply (ppc_congr__cfp_step_10 a del ch p (i+1) (i+1) (i+1) (i+1) i i c);
      try lia; try assumption.
    rewrite sublist_empty__cfp_step_10, app_nil_r. symmetry. exact Hs.
Qed.
Lemma dpkeep_subset_after__cfp_step_10 : forall a del ch p i c,
  1 <= i -> i <= Zlength a -> DPKeep a del ch p i c -> DPAfter a del ch p i c.
Proof.
  intros a del ch p i c Hi1 Hin H. unfold DPKeep in H. unfold DPAfter.
  exists (i-1), (i-1). split; [lia |].
  apply (ppc_congr__cfp_step_10 a del ch p i i i i (i-1) (i-1) c);
    try lia; try assumption.
  rewrite !sublist_empty__cfp_step_10, app_nil_r.
  symmetry. apply sublist_split; lia.
Qed.

(* ================= ElemCost layer ================= *)
Lemma elemcost_lb__cfp_step_10 : forall ch p x e,
  0 <= ch -> p <> 0 -> (e = -1 \/ e = 0 \/ e = 1) -> Z.divide p (x + e) ->
  ElemCost ch p x <= (if Z.eq_dec e 0 then 0 else ch).
Proof.
  intros ch p x e Hch Hp He Hdvd. unfold ElemCost.
  destruct He as [-> | [-> | ->]].
  - replace (x + -1) with (x - 1) in Hdvd by lia.
    apply (Z.mod_divide _ _ Hp) in Hdvd.
    destruct (Z.eq_dec (-1) 0); [lia |].
    destruct (x mod p =? 0) eqn:E1; [lia |].
    rewrite Hdvd. simpl. lia.
  - replace (x + 0) with x in Hdvd by lia.
    apply (Z.mod_divide _ _ Hp) in Hdvd.
    destruct (Z.eq_dec 0 0); [| lia].
    rewrite Hdvd. simpl. lia.
  - apply (Z.mod_divide _ _ Hp) in Hdvd.
    destruct (Z.eq_dec 1 0); [lia |].
    destruct (x mod p =? 0) eqn:E1; [lia |].
    rewrite Hdvd. rewrite orb_true_r. lia.
Qed.
Lemma elemcost_attained__cfp_step_10 : forall ch p x,
  p <> 0 -> ElemCost ch p x <> INF ->
  exists e, (e = -1 \/ e = 0 \/ e = 1) /\ Z.divide p (x + e) /\
            ElemCost ch p x = (if Z.eq_dec e 0 then 0 else ch).
Proof.
  intros ch p x Hp Hne. unfold ElemCost in *.
  destruct (x mod p =? 0) eqn:E1.
  - exists 0. split; [auto | split].
    + replace (x + 0) with x by lia. apply Z.mod_divide; [exact Hp |].
      apply Z.eqb_eq. exact E1.
    + destruct (Z.eq_dec 0 0); [reflexivity | lia].
  - destruct ((x - 1) mod p =? 0) eqn:E2.
    + exists (-1). split; [auto | split].
      * replace (x + -1) with (x - 1) by lia. apply Z.mod_divide; [exact Hp |].
        apply Z.eqb_eq. exact E2.
      * simpl. destruct (Z.eq_dec (-1) 0); [lia | reflexivity].
    + destruct ((x + 1) mod p =? 0) eqn:E3.
      * exists 1. split; [auto | split].
        -- apply Z.mod_divide; [exact Hp |]. apply Z.eqb_eq. exact E3.
        -- simpl. destruct (Z.eq_dec 1 0); [lia | reflexivity].
      * simpl in Hne. contradiction.
Qed.
Lemma elemcost_range__cfp_step_10 : forall ch p x,
  0 <= ch -> ElemCost ch p x <> INF -> 0 <= ElemCost ch p x <= ch.
Proof.
  intros ch p x Hch Hne. unfold ElemCost in *.
  destruct (x mod p =? 0); [lia |].
  destruct (((x - 1) mod p =? 0) || ((x + 1) mod p =? 0))%bool; [lia | contradiction].
Qed.

(* ================= base DP facts ================= *)
Lemma dpcutfresh_mem__cfp_step_10 : forall a del ch p i,
  0 <= i -> i <= Zlength a -> DPCutFresh a del ch p i (i * del).
Proof.
  intros a del ch p i Hi0 Hin. unfold DPCutFresh.
  repeat split; try lia.
  exists (@nil Z), (@nil Z).
  rewrite !sublist_empty__cfp_step_10. simpl.
  split; [split; [reflexivity | split; [constructor | reflexivity]] |].
  split; [constructor |].
  unfold ChangeCost. rewrite !count_nil__cfp_step_10. lia.
Qed.
Lemma dpcutfresh_unique__cfp_step_10 : forall a del ch p i c,
  DPCutFresh a del ch p i c -> c = i * del.
Proof.
  intros a del ch p i c H. unfold DPCutFresh in H.
  destruct H as [_ [_ [_ [_ [delta [result [Hadj [_ Hc]]]]]]]].
  destruct Hadj as [Hlen _].
  rewrite !sublist_empty__cfp_step_10 in Hlen. simpl in Hlen.
  rewrite Zlength_nil in Hlen.
  assert (delta = []) as ->.
  { destruct delta as [| z delta]; [reflexivity |].
    rewrite Zlength_cons in Hlen. pose proof (Zlength_nonneg delta). lia. }
  subst c. unfold ChangeCost. rewrite !count_nil__cfp_step_10. lia.
Qed.
Lemma dpcutfresh_value__cfp_step_10 : forall a del ch p i cf,
  0 <= i -> i <= Zlength a -> i * del <= INF ->
  DPValue (DPCutFresh a del ch p i) cf -> cf = i * del.
Proof.
  intros a del ch p i cf Hi0 Hin Hle H.
  pose proof (dpvalue_le__cfp_step_10 _ _ _ H (dpcutfresh_mem__cfp_step_10 a del ch p i Hi0 Hin)) as Hub.
  destruct (Z.eq_dec cf INF) as [He | He]; [lia |].
  apply (dpcutfresh_unique__cfp_step_10 a del ch p i).
  apply dpvalue_mem__cfp_step_10; assumption.
Qed.
Lemma dpcutfresh_step__cfp_step_10 : forall a del ch p i cf,
  0 <= i -> i < Zlength a -> i * del <= INF -> (i + 1) * del <= INF ->
  DPValue (DPCutFresh a del ch p i) cf ->
  DPValue (DPCutFresh a del ch p (i+1)) (cf + del).
Proof.
  intros a del ch p i cf Hi0 Hin Hle1 Hle2 H.
  rewrite (dpcutfresh_value__cfp_step_10 a del ch p i cf Hi0 ltac:(lia) Hle1 H).
  replace (i * del + del) with ((i+1) * del) by lia.
  apply dpvalue_intro__cfp_step_10; [| | lia].
  - apply dpcutfresh_mem__cfp_step_10; lia.
  - intros c Hc. rewrite (dpcutfresh_unique__cfp_step_10 _ _ _ _ _ _ Hc). lia.
Qed.
Lemma dpcutafterkeep_zero__cfp_step_10 : forall a del ch p v,
  DPValue (DPCutAfterKeep a del ch p 0) v -> v = INF.
Proof.
  intros a del ch p v H.
  eapply dpvalue_empty__cfp_step_10; [| exact H].
  intros c [l [H1 [H2 _]]]. lia.
Qed.
Lemma dpafter_zero__cfp_step_10 : forall a del ch p v,
  DPValue (DPAfter a del ch p 0) v -> v = INF.
Proof.
  intros a del ch p v H.
  eapply dpvalue_empty__cfp_step_10; [| exact H].
  intros c [l [r [Hr [Hl [Hlr _]]]]]. lia.
Qed.
Lemma dpkeep_zero_mem__cfp_step_10 : forall a del ch p,
  0 <= Zlength a -> DPKeep a del ch p 0 0.
Proof.
  intros a del ch p Hn. unfold DPKeep.
  repeat split; try lia.
  exists (@nil Z), (@nil Z).
  rewrite !sublist_empty__cfp_step_10. simpl.
  split; [split; [reflexivity | split; [constructor | reflexivity]] |].
  split; [constructor |].
  unfold ChangeCost. rewrite !count_nil__cfp_step_10. lia.
Qed.
Lemma ppc_bound__cfp_step_10 : forall a del ch p i l r c,
  0 <= del -> 0 <= ch -> PartialPlanCost a del ch p i l r c ->
  0 <= c <= Zlength a * del + 2 * (Zlength a * ch).
Proof.
  intros a del ch p i l r c Hdel Hch H.
  destruct H as [Hl0 [Hlr [Hri [Hin [delta [result [Hadj [_ Hc]]]]]]]].
  destruct Hadj as [Hlen _].
  rewrite Zlength_app in Hlen.
  rewrite !Zlength_sublist in Hlen by lia.
  pose proof (count_bounds__cfp_step_10 (-1) delta) as Hc1.
  pose proof (count_bounds__cfp_step_10 1 delta) as Hc2.
  subst c. unfold ChangeCost. nia.
Qed.
Lemma cfp_state_finite_bound__cfp_step_10 :
  forall a del ch p i keep cutFresh cutAfterKeep after,
  0 <= del -> 0 <= ch ->
  CostForPrimeState a del ch p i keep cutFresh cutAfterKeep after ->
  (keep <> INF -> 0 <= keep <= Zlength a * del + 2 * (Zlength a * ch)) /\
  (cutFresh <> INF -> 0 <= cutFresh <= Zlength a * del + 2 * (Zlength a * ch)) /\
  (cutAfterKeep <> INF -> 0 <= cutAfterKeep <= Zlength a * del + 2 * (Zlength a * ch)) /\
  (after <> INF -> 0 <= after <= Zlength a * del + 2 * (Zlength a * ch)).
Proof.
  intros a del ch p i keep cutFresh cutAfterKeep after Hdel Hch [Hk [Hf [Hak Haf]]].
  split; [| split; [| split]]; intros Hne.
  - pose proof (dpvalue_mem__cfp_step_10 _ _ Hk Hne) as Hm.
    unfold DPKeep in Hm. eapply ppc_bound__cfp_step_10; eauto.
  - pose proof (dpvalue_mem__cfp_step_10 _ _ Hf Hne) as Hm.
    unfold DPCutFresh in Hm. eapply ppc_bound__cfp_step_10; eauto.
  - pose proof (dpvalue_mem__cfp_step_10 _ _ Hak Hne) as Hm.
    destruct Hm as [l [_ [_ Hm]]]. eapply ppc_bound__cfp_step_10; eauto.
  - pose proof (dpvalue_mem__cfp_step_10 _ _ Haf Hne) as Hm.
    destruct Hm as [l [r [_ Hm]]]. eapply ppc_bound__cfp_step_10; eauto.
Qed.

(* ================= DP step lemmas ================= *)
Lemma dpkeep_step_fin__cfp_step_10 : forall a del ch p i keep cost,
  0 <= ch -> p <> 0 -> 0 <= i -> i < Zlength a ->
  cost = ElemCost ch p (Znth i a 0) -> cost <> INF ->
  keep <> INF -> keep + cost <= INF ->
  DPValue (DPKeep a del ch p i) keep ->
  DPValue (DPKeep a del ch p (i+1)) (keep + cost).
Proof.
  intros a del ch p i keep cost Hch Hp Hi0 Hin Hcost Hcne Hkne Hle Hk.
  destruct (elemcost_attained__cfp_step_10 ch p (Znth i a 0) Hp ltac:(congruence))
    as [e [He [Hdvd Hval]]].
  apply dpvalue_intro__cfp_step_10; [| | exact Hle].
  - apply (dpkeep_shift__cfp_step_10 a del ch p i); [lia | lia |].
    rewrite Hcost, Hval.
    apply ppc_keep_step_intro__cfp_step_10; try lia; try assumption.
    apply dpvalue_mem__cfp_step_10; assumption.
  - intros c Hc.
    apply (dpkeep_shift__cfp_step_10 a del ch p i) in Hc; [| lia | lia].
    apply (ppc_keep_step_elim__cfp_step_10 a del ch p i i i c) in Hc; try lia.
    destruct Hc as [c' [e' [Hc' [He' [Hdvd' Hceq]]]]].
    pose proof (dpvalue_le__cfp_step_10 _ _ _ Hk Hc') as Hkc.
    pose proof (elemcost_lb__cfp_step_10 ch p (Znth i a 0) e' Hch Hp He' Hdvd') as Hlb.
    lia.
Qed.
Lemma dpkeep_step_inf__cfp_step_10 : forall a del ch p i keep,
  0 <= ch -> 0 <= i -> i < Zlength a ->
  DPValue (DPKeep a del ch p i) keep -> keep = INF ->
  DPValue (DPKeep a del ch p (i+1)) INF.
Proof.
  intros a del ch p i keep Hch Hi0 Hin Hk Hkinf.
  apply dpvalue_inf_intro__cfp_step_10. intros c Hc.
  apply (dpkeep_shift__cfp_step_10 a del ch p i) in Hc; [| lia | lia].
  apply (ppc_keep_step_elim__cfp_step_10 a del ch p i i i c) in Hc; try lia.
  destruct Hc as [c' [e' [Hc' [He' [Hdvd' Hceq]]]]].
  pose proof (dpvalue_le__cfp_step_10 _ _ _ Hk Hc') as Hkc.
  destruct (Z.eq_dec e' 0); lia.
Qed.
Lemma dpcutafterkeep_src__cfp_step_10 : forall a del ch p i c l,
  1 <= l -> l <= i ->
  PartialPlanCost a del ch p i l i c ->
  DPCutAfterKeep a del ch p i c \/ DPKeep a del ch p i c.
Proof.
  intros a del ch p i c l Hl1 Hli H.
  destruct (Z.eq_dec l i) as [-> | Hne].
  - right. exact H.
  - left. exists l. split; [lia | split; [lia | exact H]].
Qed.
Lemma dpcutafterkeep_step_fin__cfp_step_10 : forall a del ch p i keep cak m,
  0 <= del -> 1 <= i -> i < Zlength a ->
  DPValue (DPKeep a del ch p i) keep ->
  DPValue (DPCutAfterKeep a del ch p i) cak ->
  m = Z.min keep cak -> m <> INF -> m + del <= INF ->
  DPValue (DPCutAfterKeep a del ch p (i+1)) (m + del).
Proof.
  intros a del ch p i keep cak m Hdel Hi1 Hin Hk Hak Hm Hmne Hle.
  apply dpvalue_intro__cfp_step_10; [| | exact Hle].
  - destruct (Z.le_gt_cases keep cak) as [Hc | Hc].
    + replace (m + del) with (keep + del) by lia.
      exists i. split; [lia | split; [lia |]].
      apply ppc_cut_step_intro__cfp_step_10; try lia.
      apply (dpvalue_mem__cfp_step_10 _ _ Hk). lia.
    + assert (Hcm : cak <> INF) by lia.
      destruct (dpvalue_mem__cfp_step_10 _ _ Hak Hcm) as [l [Hl1 [Hl2 Hppc]]].
      replace (m + del) with (cak + del) by lia.
      exists l. split; [lia | split; [lia |]].
      apply ppc_cut_step_intro__cfp_step_10; try lia. exact Hppc.
  - intros c [l [Hl1 [Hl2 Hppc]]].
    apply (ppc_cut_step_elim__cfp_step_10 a del ch p i l c) in Hppc; try lia.
    destruct (dpcutafterkeep_src__cfp_step_10 a del ch p i (c - del) l
                ltac:(lia) ltac:(lia) Hppc) as [Hs | Hs].
    + pose proof (dpvalue_le__cfp_step_10 _ _ _ Hak Hs). lia.
    + pose proof (dpvalue_le__cfp_step_10 _ _ _ Hk Hs). lia.
Qed.
Lemma dpcutafterkeep_step_inf__cfp_step_10 : forall a del ch p i keep cak,
  0 <= del -> 1 <= i -> i < Zlength a ->
  DPValue (DPKeep a del ch p i) keep ->
  DPValue (DPCutAfterKeep a del ch p i) cak ->
  keep = INF -> cak = INF ->
  DPValue (DPCutAfterKeep a del ch p (i+1)) INF.
Proof.
  intros a del ch p i keep cak Hdel Hi1 Hin Hk Hak Hkinf Hcinf.
  apply dpvalue_inf_intro__cfp_step_10.
  intros c [l [Hl1 [Hl2 Hppc]]].
  apply (ppc_cut_step_elim__cfp_step_10 a del ch p i l c) in Hppc; try lia.
  destruct (dpcutafterkeep_src__cfp_step_10 a del ch p i (c - del) l
              ltac:(lia) ltac:(lia) Hppc) as [Hs | Hs].
  - pose proof (dpvalue_le__cfp_step_10 _ _ _ Hak Hs). lia.
  - pose proof (dpvalue_le__cfp_step_10 _ _ _ Hk Hs). lia.
Qed.
Lemma dpafter_le_dpkeep__cfp_step_10 : forall a del ch p i keep aft,
  1 <= i -> i <= Zlength a ->
  DPValue (DPKeep a del ch p i) keep ->
  DPValue (DPAfter a del ch p i) aft ->
  aft <= keep.
Proof.
  intros a del ch p i keep aft Hi1 Hin Hk Haf.
  destruct (Z.eq_dec keep INF) as [-> | Hne].
  - apply dpvalue_ub__cfp_step_10 with (S := DPAfter a del ch p i). exact Haf.
  - apply (dpvalue_le__cfp_step_10 _ _ _ Haf).
    apply dpkeep_subset_after__cfp_step_10; [lia | lia |].
    apply dpvalue_mem__cfp_step_10; assumption.
Qed.
Lemma after_source_le__cfp_step_10 : forall a del ch p i keep cf cak aft l r c',
  1 <= i -> i <= Zlength a ->
  DPValue (DPKeep a del ch p i) keep ->
  DPValue (DPCutFresh a del ch p i) cf ->
  DPValue (DPCutAfterKeep a del ch p i) cak ->
  DPValue (DPAfter a del ch p i) aft ->
  0 <= l -> l <= r -> r <= i ->
  PartialPlanCost a del ch p i l r c' ->
  Z.min cf (Z.min cak aft) <= c'.
Proof.
  intros a del ch p i keep cf cak aft l r c' Hi1 Hin Hk Hf Hak Haf Hl0 Hlr Hri Hppc.
  destruct (Z.eq_dec r i) as [-> | Hrne].
  - destruct (Z.eq_dec l 0) as [-> | Hl0ne].
    + pose proof (dpvalue_le__cfp_step_10 _ _ _ Hf Hppc). lia.
    + destruct (dpcutafterkeep_src__cfp_step_10 a del ch p i c' l
                  ltac:(lia) ltac:(lia) Hppc) as [Hs | Hs].
      * pose proof (dpvalue_le__cfp_step_10 _ _ _ Hak Hs). lia.
      * pose proof (dpvalue_le__cfp_step_10 _ _ _ Hk Hs).
        pose proof (dpafter_le_dpkeep__cfp_step_10 a del ch p i keep aft Hi1 Hin Hk Haf).
        lia.
  - assert (Hs : DPAfter a del ch p i c') by (exists l, r; split; [lia | exact Hppc]).
    pose proof (dpvalue_le__cfp_step_10 _ _ _ Haf Hs). lia.
Qed.
Lemma after_source_mem__cfp_step_10 : forall a del ch p i cf cak aft m,
  1 <= i -> i <= Zlength a ->
  DPValue (DPCutFresh a del ch p i) cf ->
  DPValue (DPCutAfterKeep a del ch p i) cak ->
  DPValue (DPAfter a del ch p i) aft ->
  m = Z.min cf (Z.min cak aft) -> m <> INF ->
  exists l r, 0 <= l /\ l <= r /\ r <= i /\ PartialPlanCost a del ch p i l r m.
Proof.
  intros a del ch p i cf cak aft m Hi1 Hin Hf Hak Haf Hm Hmne.
  assert (Hcase : m = cf \/ m = cak \/ m = aft) by lia.
  destruct Hcase as [Hc | [Hc | Hc]].
  - exists 0, i. split; [lia | split; [lia | split; [lia |]]].
    assert (Hne : cf <> INF) by congruence.
    pose proof (dpvalue_mem__cfp_step_10 _ _ Hf Hne) as Hmem.
    rewrite Hc. exact Hmem.
  - assert (Hne : cak <> INF) by congruence.
    destruct (dpvalue_mem__cfp_step_10 _ _ Hak Hne) as [l [Hl1 [Hl2 Hppc]]].
    exists l, i. split; [lia | split; [lia | split; [lia |]]].
    rewrite Hc. exact Hppc.
  - assert (Hne : aft <> INF) by congruence.
    destruct (dpvalue_mem__cfp_step_10 _ _ Haf Hne) as [l [r [Hr Hppc]]].
    pose proof Hppc as Hb. destruct Hb as [Hl0 [Hlr [Hri _]]].
    exists l, r. split; [lia | split; [lia | split; [lia |]]].
    rewrite Hc. exact Hppc.
Qed.
Lemma dpafter_step_fin__cfp_step_10 : forall a del ch p i keep cf cak aft cost m,
  0 <= ch -> p <> 0 -> 1 <= i -> i < Zlength a ->
  DPValue (DPKeep a del ch p i) keep ->
  DPValue (DPCutFresh a del ch p i) cf ->
  DPValue (DPCutAfterKeep a del ch p i) cak ->
  DPValue (DPAfter a del ch p i) aft ->
  cost = ElemCost ch p (Znth i a 0) -> cost <> INF ->
  m = Z.min cf (Z.min cak aft) -> m <> INF -> m + cost <= INF ->
  DPValue (DPAfter a del ch p (i+1)) (m + cost).
Proof.
  intros a del ch p i keep cf cak aft cost m Hch Hp Hi1 Hin Hk Hf Hak Haf
         Hcost Hcne Hm Hmne Hle.
  destruct (elemcost_attained__cfp_step_10 ch p (Znth i a 0) Hp ltac:(congruence))
    as [e [He [Hdvd Hval]]].
  apply dpvalue_intro__cfp_step_10; [| | exact Hle].
  - destruct (after_source_mem__cfp_step_10 a del ch p i cf cak aft m
                Hi1 ltac:(lia) Hf Hak Haf Hm Hmne) as [l [r [Hl0 [Hlr [Hri Hppc]]]]].
    exists l, r. split; [lia |].
    rewrite Hcost, Hval.
    apply ppc_keep_step_intro__cfp_step_10; try lia; try assumption.
  - intros c [l [r [Hr Hppc]]].
    pose proof Hppc as Hb. destruct Hb as [Hl0 [Hlr [Hri _]]].
    apply (ppc_keep_step_elim__cfp_step_10 a del ch p i l r c) in Hppc; try lia.
    destruct Hppc as [c' [e' [Hc' [He' [Hdvd' Hceq]]]]].
    pose proof (after_source_le__cfp_step_10 a del ch p i keep cf cak aft l r c'
                  Hi1 ltac:(lia) Hk Hf Hak Haf ltac:(lia) ltac:(lia) ltac:(lia) Hc') as Hmin.
    pose proof (elemcost_lb__cfp_step_10 ch p (Znth i a 0) e' Hch Hp He' Hdvd') as Hlb.
    lia.
Qed.
Lemma dpafter_step_inf__cfp_step_10 : forall a del ch p i keep cf cak aft,
  0 <= ch -> 0 <= i -> i < Zlength a -> 1 <= i ->
  DPValue (DPKeep a del ch p i) keep ->
  DPValue (DPCutFresh a del ch p i) cf ->
  DPValue (DPCutAfterKeep a del ch p i) cak ->
  DPValue (DPAfter a del ch p i) aft ->
  Z.min cf (Z.min cak aft) = INF ->
  DPValue (DPAfter a del ch p (i+1)) INF.
Proof.
  intros a del ch p i keep cf cak aft Hch Hi0 Hin Hi1 Hk Hf Hak Haf Hm.
  apply dpvalue_inf_intro__cfp_step_10.
  intros c [l [r [Hr Hppc]]].
  pose proof Hppc as Hb. destruct Hb as [Hl0 [Hlr [Hri _]]].
  apply (ppc_keep_step_elim__cfp_step_10 a del ch p i l r c) in Hppc; try lia.
  destruct Hppc as [c' [e' [Hc' [He' [Hdvd' Hceq]]]]].
  pose proof (after_source_le__cfp_step_10 a del ch p i keep cf cak aft l r c'
                Hi1 ltac:(lia) Hk Hf Hak Haf ltac:(lia) ltac:(lia) ltac:(lia) Hc') as Hmin.
  destruct (Z.eq_dec e' 0); lia.
Qed.

(* ================= composite one-step lemma ================= *)
Lemma cfp_state_step__cfp_step_10 :
  forall a del ch p i keep cf cak aft cost keep' cf' cak' aft',
  0 <= del -> 0 <= ch -> p <> 0 -> 1 <= i -> i < Zlength a ->
  cost = ElemCost ch p (Znth i a 0) -> cost <> INF ->
  CostForPrimeState a del ch p i keep cf cak aft ->
  (keep = INF -> keep' = INF) ->
  (keep <> INF -> keep' = keep + cost) ->
  cf' = cf + del ->
  (Z.min keep cak = INF -> cak' = INF) ->
  (Z.min keep cak <> INF -> cak' = Z.min keep cak + del) ->
  (Z.min cf (Z.min cak aft) = INF -> aft' = INF) ->
  (Z.min cf (Z.min cak aft) <> INF -> aft' = Z.min cf (Z.min cak aft) + cost) ->
  keep' <= INF -> cak' <= INF -> aft' <= INF ->
  i * del <= INF -> (i + 1) * del <= INF ->
  CostForPrimeState a del ch p (i+1) keep' cf' cak' aft'.
Proof.
  intros a del ch p i keep cf cak aft cost keep' cf' cak' aft'
         Hdel Hch Hp Hi1 Hin Hcost Hcne Hstate
         Hk1 Hk2 Hf1 Ha1 Ha2 Hb1 Hb2 Hkub Hakub Hafub Hd1 Hd2.
  destruct Hstate as [Hk [Hf [Hak Haf]]].
  split; [| split; [| split]].
  - destruct (Z.eq_dec keep INF) as [He | He].
    + rewrite (Hk1 He). apply (dpkeep_step_inf__cfp_step_10 a del ch p i keep);
        try lia; assumption.
    + assert (Hkc : keep + cost <= INF) by (rewrite <- (Hk2 He); exact Hkub).
      rewrite (Hk2 He).
      apply (dpkeep_step_fin__cfp_step_10 a del ch p i keep cost);
        try lia; try assumption.
  - subst cf'. apply dpcutfresh_step__cfp_step_10; try lia; assumption.
  - destruct (Z.eq_dec (Z.min keep cak) INF) as [He | He].
    + rewrite (Ha1 He).
      apply (dpcutafterkeep_step_inf__cfp_step_10 a del ch p i keep cak);
        try lia; try assumption.
      * pose proof (dpvalue_ub__cfp_step_10 _ _ Hk). lia.
      * pose proof (dpvalue_ub__cfp_step_10 _ _ Hak). lia.
    + assert (Hac : Z.min keep cak + del <= INF)
        by (rewrite <- (Ha2 He); exact Hakub).
      rewrite (Ha2 He).
      apply (dpcutafterkeep_step_fin__cfp_step_10 a del ch p i keep cak);
        try lia; try assumption; try reflexivity.
  - destruct (Z.eq_dec (Z.min cf (Z.min cak aft)) INF) as [He | He].
    + rewrite (Hb1 He).
      apply (dpafter_step_inf__cfp_step_10 a del ch p i keep cf cak aft);
        try lia; assumption.
    + assert (Hbc : Z.min cf (Z.min cak aft) + cost <= INF)
        by (rewrite <- (Hb2 He); exact Hafub).
      rewrite (Hb2 He).
      apply (dpafter_step_fin__cfp_step_10 a del ch p i keep cf cak aft cost);
        try lia; try assumption; try reflexivity.
Qed.
Lemma dp_le_inf__cfp_step_11 : forall (S : Z -> Prop) (v : Z),
  DPValue S v -> v <= INF.
Proof.
  intros S v H.
  unfold DPValue, min_value_of_subset_with_default in H.
  destruct H as [[_ H] | [_ H]]; lia.
Qed.
Lemma dp_lb__cfp_step_11 : forall (S : Z -> Prop) (v z : Z),
  DPValue S v -> S z -> v <= z.
Proof.
  intros S v z H Hz.
  unfold DPValue, min_value_of_subset_with_default,
         min_value_of_subset, min_object_of_subset in H.
  destruct H as [[[b [[Hb Hmin] Hval]] Hle] | [Hall Heq]].
  - cbv beta in Hval. subst v.
    apply Hmin. sets_unfold. exact Hz.
  - subst v. apply Hall. sets_unfold. exact Hz.
Qed.
Lemma dp_mem__cfp_step_11 : forall (S : Z -> Prop) (v : Z),
  DPValue S v -> v <> INF -> S v.
Proof.
  intros S v H Hne.
  unfold DPValue, min_value_of_subset_with_default,
         min_value_of_subset, min_object_of_subset in H.
  destruct H as [[[b [[Hb _] Hval]] _] | [_ Heq]].
  - cbv beta in Hval. subst v. sets_unfold in Hb. exact Hb.
  - contradiction.
Qed.
Lemma dp_intro__cfp_step_11 : forall (S : Z -> Prop) (v : Z),
  v <= INF ->
  (S v \/ v = INF) ->
  (forall z, S z -> v <= z) ->
  DPValue S v.
Proof.
  intros S v Hle Hmem Hlb.
  unfold DPValue, min_value_of_subset_with_default,
         min_value_of_subset, min_object_of_subset.
  destruct Hmem as [Hin | Heq].
  - left. split; [| exact Hle].
    exists v. split; [split |].
    + sets_unfold. exact Hin.
    + intros b Hb. sets_unfold in Hb. cbv beta. apply Hlb. exact Hb.
    + reflexivity.
  - right. split; [| exact Heq].
    intros x Hx. sets_unfold in Hx. cbv beta.
    rewrite <- Heq. apply Hlb. exact Hx.
Qed.
Lemma dp_empty_inf__cfp_step_11 : forall (S : Z -> Prop) (v : Z),
  DPValue S v -> (forall z, ~ S z) -> v = INF.
Proof.
  intros S v H Hemp.
  destruct (Z.eq_dec v INF) as [Heq | Hne]; [exact Heq |].
  exfalso. apply (Hemp v). apply dp_mem__cfp_step_11; assumption.
Qed.
Lemma dp_cutafterkeep_zero_empty__cfp_step_11 :
  forall (a : list Z) (del change p i : Z),
    i <= 1 -> forall c, ~ DPCutAfterKeep a del change p i c.
Proof.
  intros a del change p i Hi c Hc.
  unfold DPCutAfterKeep in Hc.
  destruct Hc as [l [Hl1 [Hl2 _]]]. lia.
Qed.
Lemma cfp_cutafterkeep_zero_contra__cfp_step_11 :
  forall (a : list Z) (del change p i keep cutFresh cutAfterKeep after : Z),
    CostForPrimeState a del change p i keep cutFresh cutAfterKeep after ->
    i <= 0 ->
    cutAfterKeep = INF.
Proof.
  intros a del change p i keep cutFresh cutAfterKeep after HS Hi.
  destruct HS as [_ [_ [HcAK _]]].
  apply (dp_empty_inf__cfp_step_11 _ _ HcAK).
  apply dp_cutafterkeep_zero_empty__cfp_step_11. lia.
Qed.

(* ---------------- generic Z-cardinality helpers ---------------- *)
Lemma fold_one_Zlength__cfp_step_11 : forall (f : Z -> Z) (l : list Z),
  (forall x, f x = 1) ->
  fold_right (fun (x : Z) (acc : Z) => f x + acc) 0 l = Zlength l.
Proof.
  intros f l Hf. induction l as [| x l IH].
  - rewrite Zlength_nil. reflexivity.
  - cbn [fold_right]. rewrite IH, Hf, Zlength_cons. lia.
Qed.
Lemma sum_const_one__cfp_step_11 : forall (P : Z -> Prop) (HF : Finite P),
  @sum Z P HF (fun _ => 1) = Zlength (@enum Z P HF).
Proof.
  intros P HF. unfold sum.
  apply fold_one_Zlength__cfp_step_11. reflexivity.
Qed.
Lemma set_card_via_list__cfp_step_11 :
  forall (P : Z -> Prop) (HF : Finite P) (l : list Z),
    NoDup l -> (forall x, P x <-> In x l) -> @set_card Z P HF = Zlength l.
Proof.
  intros P HF l Hnd Hmem.
  unfold set_card. rewrite sum_const_one__cfp_step_11.
  assert (Hperm : Permutation (@enum Z P HF) l).
  { apply NoDup_Permutation.
    - apply enum_nodup.
    - exact Hnd.
    - intros x. split.
      + intros Hin. apply Hmem. apply enum_ok. exact Hin.
      + intros Hin. apply enum_ok. apply Hmem. exact Hin. }
  rewrite !Zlength_correct.
  f_equal. apply Permutation_length. exact Hperm.
Qed.
Lemma Zlength_Zrange_aux__cfp_step_11 : forall (n : nat) (low : Z),
  Zlength (Zrange_aux low n) = Z.of_nat n.
Proof.
  induction n as [| n IH]; intros low; simpl.
  - rewrite Zlength_nil. reflexivity.
  - rewrite Zlength_cons, IH. lia.
Qed.
Lemma Zlength_Zrange__cfp_step_11 : forall low high,
  low <= high -> Zlength (Zrange low high) = high - low.
Proof.
  intros low high H. unfold Zrange.
  rewrite Zlength_Zrange_aux__cfp_step_11. lia.
Qed.
Lemma Zrange_snoc__cfp_step_11 : forall low high,
  low <= high -> Zrange low (high + 1) = Zrange low high ++ [high].
Proof.
  intros low high H. unfold Zrange.
  replace (Z.to_nat (high + 1 - low)) with (Z.to_nat (high - low) + 1)%nat by lia.
  rewrite Zrange_aux_app.
  f_equal. simpl.
  replace (low + Z.of_nat (Z.to_nat (high - low))) with high by lia.
  reflexivity.
Qed.
Lemma Count_as_idxs__cfp_step_11 : forall (v : Z) (xs : list Z),
  Count v xs =
  Zlength (filter (fun i => if Z.eq_dec (Znth i xs 0) v then true else false)
                  (Zrange 0 (Zlength xs))).
Proof.
  intros v xs. unfold Count.
  apply set_card_via_list__cfp_step_11.
  - apply NoDup_filter_bool. apply NoDup_Zrange.
  - intros x. rewrite filter_In. rewrite <- In_Zrange.
    split.
    + intros [Hr He]. split; [lia |].
      destruct (Z.eq_dec (Znth x xs 0) v); [reflexivity | contradiction].
    + intros [Hr Ht]. split; [lia |].
      destruct (Z.eq_dec (Znth x xs 0) v); [assumption | discriminate].
Qed.
Lemma Count_nonneg__cfp_step_11 : forall (v : Z) (xs : list Z), 0 <= Count v xs.
Proof.
  intros. rewrite Count_as_idxs__cfp_step_11. apply Zlength_nonneg.
Qed.
Lemma Count_nil__cfp_step_11 : forall (v : Z), Count v [] = 0.
Proof.
  intros v. rewrite Count_as_idxs__cfp_step_11.
  rewrite Zlength_nil. unfold Zrange. simpl. reflexivity.
Qed.
Lemma Count_snoc__cfp_step_11 : forall (v : Z) (xs : list Z) (w : Z),
  Count v (xs ++ [w]) = Count v xs + (if Z.eq_dec w v then 1 else 0).
Proof.
  intros v xs w.
  pose proof (Zlength_nonneg xs) as Hnn.
  assert (Hlast : Znth (Zlength xs) (xs ++ [w]) 0 = w).
  { rewrite app_Znth2 by lia.
    replace (Zlength xs - Zlength xs) with 0 by lia.
    apply Znth0_cons. }
  rewrite !Count_as_idxs__cfp_step_11.
  rewrite Zlength_app_cons.
  rewrite Zrange_snoc__cfp_step_11 by lia.
  rewrite filter_app, Zlength_app.
  f_equal.
  - f_equal. apply filter_ext_in. intros j Hj.
    rewrite <- In_Zrange in Hj.
    rewrite app_Znth1 by lia. reflexivity.
  - simpl. rewrite Hlast.
    destruct (Z.eq_dec w v).
    + rewrite Zlength_cons, Zlength_nil. lia.
    + rewrite Zlength_nil. lia.
Qed.
Lemma filter_disjoint_bound__cfp_step_11 :
  forall (f g : Z -> bool) (l : list Z),
    (forall x, f x = true -> g x = false) ->
    Zlength (filter f l) + Zlength (filter g l) <= Zlength l.
Proof.
  intros f g l Hdisj. induction l as [| x l IH]; simpl.
  - rewrite Zlength_nil. lia.
  - rewrite Zlength_cons.
    destruct (f x) eqn:Hf; destruct (g x) eqn:Hg.
    + rewrite (Hdisj x Hf) in Hg. discriminate.
    + rewrite Zlength_cons. lia.
    + rewrite Zlength_cons. lia.
    + lia.
Qed.
Lemma Count_pm_bound__cfp_step_11 : forall (xs : list Z),
  Count (-1) xs + Count 1 xs <= Zlength xs.
Proof.
  intros xs. pose proof (Zlength_nonneg xs) as Hnn.
  rewrite !Count_as_idxs__cfp_step_11.
  apply Z.le_trans with (m := Zlength (Zrange 0 (Zlength xs))).
  - apply filter_disjoint_bound__cfp_step_11.
    intros x Hx.
    destruct (Z.eq_dec (Znth x xs 0) (-1)) as [Hm | Hm]; [| discriminate].
    destruct (Z.eq_dec (Znth x xs 0) 1) as [Hp | Hp]; [| reflexivity].
    lia.
  - rewrite Zlength_Zrange__cfp_step_11 by lia. lia.
Qed.
Lemma Count_single__cfp_step_11 : forall (v w : Z),
  Count v [w] = (if Z.eq_dec w v then 1 else 0).
Proof.
  intros v w.
  rewrite <- (app_nil_l [w]).
  rewrite Count_snoc__cfp_step_11, Count_nil__cfp_step_11.
  destruct (Z.eq_dec w v); lia.
Qed.
Lemma ChangeCost_snoc_ok__cfp_step_11 :
  forall del change l r delta w,
    (w = -1 \/ w = 0 \/ w = 1) ->
    ChangeCost del change l r (delta ++ [w]) =
    ChangeCost del change l r delta + (if Z.eq_dec w 0 then 0 else change).
Proof.
  intros del change l r delta w Hw. unfold ChangeCost.
  rewrite !Count_snoc__cfp_step_11.
  destruct (Z.eq_dec w (-1)); destruct (Z.eq_dec w 1); destruct (Z.eq_dec w 0); lia.
Qed.
Lemma ChangeCost_shift__cfp_step_11 :
  forall del change l r l' r' delta,
    r' - l' = r - l ->
    ChangeCost del change l' r' delta = ChangeCost del change l r delta.
Proof.
  intros. unfold ChangeCost. rewrite H. reflexivity.
Qed.
Lemma ChangeCost_bound__cfp_step_11 :
  forall del change l r delta,
    0 <= del -> 0 <= change -> l <= r ->
    0 <= ChangeCost del change l r delta <= (r - l) * del + Zlength delta * change.
Proof.
  intros del change l r delta Hd Hc Hlr.
  pose proof (Count_pm_bound__cfp_step_11 delta) as Hb.
  pose proof (Count_nonneg__cfp_step_11 (-1) delta) as H1.
  pose proof (Count_nonneg__cfp_step_11 1 delta) as H2.
  unfold ChangeCost. nia.
Qed.

(* ---------------- Adjusted / plan structure ---------------- *)
Lemma Zlength_zero_nil__cfp_step_11 : forall (l : list Z), Zlength l = 0 -> l = [].
Proof.
  intros l H. destruct l as [| x l]; [reflexivity |].
  rewrite Zlength_cons in H. pose proof (Zlength_nonneg l). lia.
Qed.
Lemma combine_app__cfp_step_11 : forall {A B : Type} (l1 l2 : list A) (l1' l2' : list B),
  length l1 = length l1' ->
  combine (l1 ++ l2) (l1' ++ l2') = combine l1 l1' ++ combine l2 l2'.
Proof.
  intros A B l1. induction l1 as [| x l1 IH]; intros l2 l1' l2' H;
    destruct l1' as [| y l1']; simpl in *; try discriminate; try reflexivity.
  f_equal. apply IH. injection H. auto.
Qed.
Lemma Adjusted_nil_intro__cfp_step_11 : Adjusted [] [] [].
Proof.
  unfold Adjusted. split; [reflexivity | split; [constructor | reflexivity]].
Qed.
Lemma Adjusted_nil__cfp_step_11 : forall delta result,
  Adjusted [] delta result -> delta = [] /\ result = [].
Proof.
  intros delta result [Hlen [_ Hres]].
  rewrite Zlength_nil in Hlen.
  apply Zlength_zero_nil__cfp_step_11 in Hlen. subst delta.
  split; [reflexivity |]. simpl in Hres. exact Hres.
Qed.
Lemma Adjusted_snoc__cfp_step_11 : forall kept delta result x w,
  Adjusted kept delta result ->
  (w = -1 \/ w = 0 \/ w = 1) ->
  Adjusted (kept ++ [x]) (delta ++ [w]) (result ++ [x + w]).
Proof.
  intros kept delta result x w [Hlen [Hall Hres]] Hw.
  assert (Hnat : length kept = length delta).
  { rewrite !Zlength_correct in Hlen. lia. }
  unfold Adjusted. split; [| split].
  - rewrite !Zlength_app_cons. lia.
  - apply Forall_app. split; [exact Hall | constructor; [exact Hw | constructor]].
  - rewrite combine_app__cfp_step_11 by exact Hnat.
    rewrite map_app. rewrite <- Hres. simpl. reflexivity.
Qed.
Lemma Adjusted_unsnoc__cfp_step_11 : forall kept delta result x,
  Adjusted (kept ++ [x]) delta result ->
  exists delta' w result',
    delta = delta' ++ [w] /\ (w = -1 \/ w = 0 \/ w = 1) /\
    result = result' ++ [x + w] /\ Adjusted kept delta' result'.
Proof.
  intros kept delta result x [Hlen [Hall Hres]].
  rewrite Zlength_app_cons in Hlen.
  assert (Hne : delta <> []).
  { intros Hc. subst delta. rewrite Zlength_nil in Hlen.
    pose proof (Zlength_nonneg kept). lia. }
  destruct (exists_last Hne) as [delta' [w Hd]].
  subst delta.
  rewrite Zlength_app_cons in Hlen.
  apply Forall_app in Hall. destruct Hall as [Hall' Hlastw].
  assert (Hw : w = -1 \/ w = 0 \/ w = 1) by (inversion Hlastw; assumption).
  assert (Hnat : length kept = length delta').
  { rewrite !Zlength_correct in Hlen. lia. }
  exists delta', w, (map (fun q => fst q + snd q) (combine kept delta')).
  split; [reflexivity | split; [exact Hw | split]].
  - rewrite Hres. rewrite combine_app__cfp_step_11 by exact Hnat.
    rewrite map_app. simpl. reflexivity.
  - unfold Adjusted. split; [lia | split; [exact Hall' | reflexivity]].
Qed.

(* ---------------- ElemCost bridges ---------------- *)
Lemma ElemCost_attain__cfp_step_11 : forall change p x,
  2 <= p -> ElemCost change p x <> INF ->
  exists w, (w = -1 \/ w = 0 \/ w = 1) /\ Z.divide p (x + w) /\
            (if Z.eq_dec w 0 then 0 else change) = ElemCost change p x.
Proof.
  intros change p x Hp Hne. unfold ElemCost in *.
  destruct (Z.eqb_spec (x mod p) 0) as [H0 | H0].
  - exists 0. split; [tauto | split].
    + replace (x + 0) with x by lia. apply Z.mod_divide; [lia | exact H0].
    + destruct (Z.eq_dec 0 0); [reflexivity | contradiction].
  - destruct (Z.eqb_spec ((x - 1) mod p) 0) as [H1 | H1]; simpl in *.
    + exists (-1). split; [tauto | split].
      * replace (x + -1) with (x - 1) by lia. apply Z.mod_divide; [lia | exact H1].
      * destruct (Z.eq_dec (-1) 0); [discriminate | reflexivity].
    + destruct (Z.eqb_spec ((x + 1) mod p) 0) as [H2 | H2]; simpl in *.
      * exists 1. split; [tauto | split].
        -- apply Z.mod_divide; [lia | exact H2].
        -- destruct (Z.eq_dec 1 0); [discriminate | reflexivity].
      * contradiction.
Qed.
Lemma ElemCost_le_charge__cfp_step_11 : forall change p x w,
  2 <= p -> 0 <= change ->
  (w = -1 \/ w = 0 \/ w = 1) -> Z.divide p (x + w) ->
  ElemCost change p x <= (if Z.eq_dec w 0 then 0 else change).
Proof.
  intros change p x w Hp Hc Hw Hdiv. unfold ElemCost.
  destruct Hw as [Hw | [Hw | Hw]]; subst w.
  - assert (H1 : (x - 1) mod p = 0).
    { apply Z.mod_divide; [lia |]. replace (x - 1) with (x + -1) by lia. exact Hdiv. }
    destruct (Z.eq_dec (-1) 0); [discriminate |].
    destruct (Z.eqb_spec (x mod p) 0); [lia |].
    rewrite H1. simpl. lia.
  - assert (H0 : x mod p = 0).
    { apply Z.mod_divide; [lia |]. replace x with (x + 0) by lia. exact Hdiv. }
    destruct (Z.eq_dec 0 0); [| contradiction].
    rewrite H0. simpl. lia.
  - assert (H1 : (x + 1) mod p = 0).
    { apply Z.mod_divide; [lia | exact Hdiv]. }
    destruct (Z.eq_dec 1 0); [discriminate |].
    destruct (Z.eqb_spec (x mod p) 0); [lia |].
    rewrite H1. rewrite Bool.orb_true_r. lia.
Qed.
Lemma ElemCost_bound__cfp_step_11 : forall change p x,
  0 <= change -> ElemCost change p x <> INF ->
  0 <= ElemCost change p x <= change.
Proof.
  intros change p x Hc Hne. unfold ElemCost in *.
  destruct (Z.eqb (x mod p) 0); [lia |].
  destruct (orb (Z.eqb ((x - 1) mod p) 0) (Z.eqb ((x + 1) mod p) 0)); [lia | contradiction].
Qed.

(* ---------------- sublist shape helpers ---------------- *)
Lemma kept_keep_eq__cfp_step_11 : forall (a : list Z) (l i : Z),
  sublist 0 l a ++ sublist i i a = sublist 0 l a.
Proof.
  intros. rewrite (Zsublist_nil a i i) by lia. apply app_nil_r.
Qed.
Lemma sublist_snoc__cfp_step_11 : forall (a : list Z) (r i : Z),
  0 <= r -> r <= i -> i + 1 <= Zlength a ->
  sublist r (i + 1) a = sublist r i a ++ [Znth i a 0].
Proof.
  intros a r i H1 H2 H3.
  rewrite (sublist_split r (i + 1) i a) by lia.
  rewrite (sublist_single 0 i a) by lia.
  reflexivity.
Qed.

(* ---------------- DPValue combinators ---------------- *)
Lemma dp_empty_intro__cfp_step_11 : forall (S : Z -> Prop),
  (forall z, ~ S z) -> DPValue S INF.
Proof.
  intros S Hemp. apply dp_intro__cfp_step_11.
  - lia.
  - right. reflexivity.
  - intros z Hz. exfalso. apply (Hemp z). exact Hz.
Qed.
Lemma dp_step_fin__cfp_step_11 : forall (S T : Z -> Prop) (m c : Z),
  DPValue S m -> 0 <= c -> m + c <= INF ->
  T (m + c) ->
  (forall z, T z -> exists y, S y /\ y + c <= z) ->
  DPValue T (m + c).
Proof.
  intros S T m c HS Hc Hle Hmem Hdom.
  apply dp_intro__cfp_step_11; [exact Hle | left; exact Hmem |].
  intros z Hz. destruct (Hdom z Hz) as [y [Hy Hyz]].
  pose proof (dp_lb__cfp_step_11 _ _ _ HS Hy). lia.
Qed.
Lemma dp_step_inf__cfp_step_11 : forall (S T : Z -> Prop) (m c : Z),
  DPValue S m -> 0 <= c -> INF <= m + c ->
  (forall z, T z -> exists y, S y /\ y + c <= z) ->
  DPValue T INF.
Proof.
  intros S T m c HS Hc Hle Hdom.
  apply dp_intro__cfp_step_11; [lia | right; reflexivity |].
  intros z Hz. destruct (Hdom z Hz) as [y [Hy Hyz]].
  pose proof (dp_lb__cfp_step_11 _ _ _ HS Hy). lia.
Qed.
Lemma dp_union2__cfp_step_11 : forall (S1 S2 : Z -> Prop) (m1 m2 : Z),
  DPValue S1 m1 -> DPValue S2 m2 ->
  DPValue (fun z => S1 z \/ S2 z) (Z.min m1 m2).
Proof.
  intros S1 S2 m1 m2 H1 H2.
  pose proof (dp_le_inf__cfp_step_11 _ _ H1) as Hi1.
  pose proof (dp_le_inf__cfp_step_11 _ _ H2) as Hi2.
  apply dp_intro__cfp_step_11.
  - lia.
  - destruct (Z.eq_dec (Z.min m1 m2) INF) as [Heq | Hne]; [right; exact Heq |].
    left. simpl.
    destruct (Z.min_spec m1 m2) as [[Hlt Hm] | [Hlt Hm]]; rewrite Hm in *.
    + left. apply dp_mem__cfp_step_11; assumption.
    + right. apply dp_mem__cfp_step_11; assumption.
  - intros z [Hz | Hz].
    + pose proof (dp_lb__cfp_step_11 _ _ _ H1 Hz). lia.
    + pose proof (dp_lb__cfp_step_11 _ _ _ H2 Hz). lia.
Qed.

(* ---------------- component transitions ---------------- *)
Lemma dpcutfresh_charac__cfp_step_11 : forall a del change p j c,
  0 <= j -> j <= Zlength a ->
  (DPCutFresh a del change p j c <-> c = j * del).
Proof.
  intros a del change p j c Hj Hja. unfold DPCutFresh, PartialPlanCost. split.
  - intros [_ [_ [_ [_ [delta [result [Hadj [_ Hc]]]]]]]].
    rewrite (Zsublist_nil a 0 0) in Hadj by lia.
    rewrite (Zsublist_nil a j j) in Hadj by lia.
    simpl in Hadj.
    apply Adjusted_nil__cfp_step_11 in Hadj. destruct Hadj as [Hd Hr]. subst delta.
    unfold ChangeCost in Hc. rewrite !Count_nil__cfp_step_11 in Hc. lia.
  - intros Hc. split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    exists (@nil Z), (@nil Z).
    rewrite (Zsublist_nil a 0 0) by lia.
    rewrite (Zsublist_nil a j j) by lia.
    simpl.
    split; [apply Adjusted_nil_intro__cfp_step_11 | split; [constructor |]].
    unfold ChangeCost. rewrite !Count_nil__cfp_step_11. lia.
Qed.
Lemma keep_sub_after__cfp_step_11 : forall a del change p i c,
  1 <= i -> DPKeep a del change p i c -> DPAfter a del change p i c.
Proof.
  intros a del change p i c Hi HK.
  unfold DPKeep, PartialPlanCost in HK.
  destruct HK as [_ [_ [_ [Hia [delta [result [Hadj [Hall Hc]]]]]]]].
  rewrite kept_keep_eq__cfp_step_11 in Hadj.
  exists (i - 1), (i - 1). split; [lia |].
  unfold PartialPlanCost.
  split; [lia | split; [lia | split; [lia | split; [lia |]]]].
  exists delta, result.
  rewrite <- (sublist_split 0 i (i - 1) a) by lia.
  split; [exact Hadj | split; [exact Hall |]].
  rewrite Hc.
  apply (ChangeCost_shift__cfp_step_11 del change (i - 1) (i - 1) i i delta). lia.
Qed.
Lemma dpkeep_sound__cfp_step_11 :
  forall a del change p i c w,
    0 <= i -> i + 1 <= Zlength a ->
    (w = -1 \/ w = 0 \/ w = 1) -> Z.divide p (Znth i a 0 + w) ->
    DPKeep a del change p i c ->
    DPKeep a del change p (i + 1) (c + (if Z.eq_dec w 0 then 0 else change)).
Proof.
  intros a del change p i c w Hi Hi1 Hw Hdiv HK.
  unfold DPKeep, PartialPlanCost in *.
  destruct HK as [_ [_ [_ [Hia [delta [result [Hadj [Hall Hc]]]]]]]].
  rewrite kept_keep_eq__cfp_step_11 in Hadj.
  split; [lia | split; [lia | split; [lia | split; [lia |]]]].
  exists (delta ++ [w]), (result ++ [Znth i a 0 + w]).
  rewrite kept_keep_eq__cfp_step_11.
  rewrite (sublist_snoc__cfp_step_11 a 0 i) by lia.
  split; [apply Adjusted_snoc__cfp_step_11; assumption |].
  split.
  - apply Forall_app. split; [exact Hall | constructor; [exact Hdiv | constructor]].
  - rewrite (ChangeCost_snoc_ok__cfp_step_11 del change (i + 1) (i + 1) delta w Hw).
    rewrite (ChangeCost_shift__cfp_step_11 del change i i (i + 1) (i + 1) delta) by lia.
    lia.
Qed.
Lemma dpkeep_dominate__cfp_step_11 :
  forall a del change p i c',
    0 <= i -> i + 1 <= Zlength a -> 2 <= p -> 0 <= change ->
    DPKeep a del change p (i + 1) c' ->
    exists c, DPKeep a del change p i c /\ c + ElemCost change p (Znth i a 0) <= c'.
Proof.
  intros a del change p i c' Hi Hi1 Hp Hch HK.
  unfold DPKeep, PartialPlanCost in HK.
  destruct HK as [_ [_ [_ [Hia [delta [result [Hadj [Hall Hc]]]]]]]].
  rewrite kept_keep_eq__cfp_step_11 in Hadj.
  rewrite (sublist_snoc__cfp_step_11 a 0 i) in Hadj by lia.
  destruct (Adjusted_unsnoc__cfp_step_11 _ _ _ _ Hadj)
    as [delta' [w [result' [Hd [Hw [Hres Hadj']]]]]].
  subst delta. rewrite Hres in Hall.
  apply Forall_app in Hall. destruct Hall as [Hall' Hlast].
  assert (Hdiv : Z.divide p (Znth i a 0 + w)) by (inversion Hlast; assumption).
  pose proof (ElemCost_le_charge__cfp_step_11 change p (Znth i a 0) w Hp Hch Hw Hdiv) as Hle.
  rewrite (ChangeCost_snoc_ok__cfp_step_11 del change (i + 1) (i + 1) delta' w Hw) in Hc.
  exists (ChangeCost del change i i delta').
  split.
  - unfold DPKeep, PartialPlanCost.
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    exists delta', result'.
    rewrite kept_keep_eq__cfp_step_11.
    split; [exact Hadj' | split; [exact Hall' | reflexivity]].
  - rewrite Hc.
    rewrite (ChangeCost_shift__cfp_step_11 del change i i (i + 1) (i + 1) delta') by lia.
    lia.
Qed.
Lemma dpcak_sound__cfp_step_11 :
  forall a del change p i c,
    0 <= i -> i + 1 <= Zlength a ->
    DPCutAfterKeep a del change p i c ->
    DPCutAfterKeep a del change p (i + 1) (c + del).
Proof.
  intros a del change p i c Hi Hi1 HA.
  unfold DPCutAfterKeep, PartialPlanCost in *.
  destruct HA as [l [Hl1 [Hl2 [Hl0 [Hlr [Hri [Hia [delta [result [Hadj [Hall Hc]]]]]]]]]]].
  rewrite kept_keep_eq__cfp_step_11 in Hadj.
  exists l. split; [lia | split; [lia |]].
  split; [lia | split; [lia | split; [lia | split; [lia |]]]].
  exists delta, result.
  rewrite kept_keep_eq__cfp_step_11.
  split; [exact Hadj | split; [exact Hall |]].
  rewrite Hc. unfold ChangeCost. lia.
Qed.
Lemma dpcak_dominate__cfp_step_11 :
  forall a del change p i c',
    0 <= i -> i + 1 <= Zlength a ->
    DPCutAfterKeep a del change p (i + 1) c' ->
    exists c, (DPKeep a del change p i c \/ DPCutAfterKeep a del change p i c) /\ c + del <= c'.
Proof.
  intros a del change p i c' Hi Hi1 HA.
  unfold DPCutAfterKeep, PartialPlanCost in HA.
  destruct HA as [l [Hl1 [Hl2 [Hl0 [Hlr [Hri [Hia [delta [result [Hadj [Hall Hc]]]]]]]]]]].
  rewrite kept_keep_eq__cfp_step_11 in Hadj.
  exists (ChangeCost del change l i delta).
  assert (Hbase : PartialPlanCost a del change p i l i (ChangeCost del change l i delta)).
  { unfold PartialPlanCost.
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    exists delta, result.
    rewrite kept_keep_eq__cfp_step_11.
    split; [exact Hadj | split; [exact Hall | reflexivity]]. }
  split.
  - destruct (Z.eq_dec l i) as [Hli | Hli].
    + subst l. left. exact Hbase.
    + right. exists l. split; [lia | split; [lia | exact Hbase]].
  - rewrite Hc. unfold ChangeCost. lia.
Qed.
Lemma dpafter_sound_from_fresh__cfp_step_11 :
  forall a del change p i c w,
    0 <= i -> i + 1 <= Zlength a ->
    (w = -1 \/ w = 0 \/ w = 1) -> Z.divide p (Znth i a 0 + w) ->
    DPCutFresh a del change p i c ->
    DPAfter a del change p (i + 1) (c + (if Z.eq_dec w 0 then 0 else change)).
Proof.
  intros a del change p i c w Hi Hi1 Hw Hdiv HF.
  apply (dpcutfresh_charac__cfp_step_11 a del change p i c) in HF; [| lia | lia].
  exists 0, i. split; [lia |].
  unfold PartialPlanCost.
  split; [lia | split; [lia | split; [lia | split; [lia |]]]].
  exists ([] ++ [w]), ([] ++ [Znth i a 0 + w]).
  rewrite (Zsublist_nil a 0 0) by lia.
  rewrite (sublist_snoc__cfp_step_11 a i i) by lia.
  rewrite (Zsublist_nil a i i) by lia.
  simpl.
  split.
  - apply (Adjusted_snoc__cfp_step_11 [] [] [] (Znth i a 0) w);
      [apply Adjusted_nil_intro__cfp_step_11 | exact Hw].
  - split.
    + constructor; [exact Hdiv | constructor].
    + unfold ChangeCost. rewrite !Count_single__cfp_step_11. rewrite HF.
      destruct (Z.eq_dec w (-1)); destruct (Z.eq_dec w 1);
        destruct (Z.eq_dec w 0); lia.
Qed.
Lemma dpafter_dominate__cfp_step_11 :
  forall a del change p i c',
    0 <= i -> i + 1 <= Zlength a -> 2 <= p -> 0 <= change ->
    DPAfter a del change p (i + 1) c' ->
    exists c, (DPCutFresh a del change p i c \/ DPCutAfterKeep a del change p i c \/
               DPAfter a del change p i c) /\ c + ElemCost change p (Znth i a 0) <= c'.
Proof.
  intros a del change p i c' Hi Hi1 Hp Hch HB.
  destruct HB as [l [r [Hri1 HP]]].
  unfold PartialPlanCost in HP.
  destruct HP as [Hl0 [Hlr [Hrle [Hia [delta [result [Hadj [Hall Hc]]]]]]]].
  rewrite (sublist_snoc__cfp_step_11 a r i) in Hadj by lia.
  rewrite app_assoc in Hadj.
  destruct (Adjusted_unsnoc__cfp_step_11 _ _ _ _ Hadj)
    as [delta' [w [result' [Hd [Hw [Hres Hadj']]]]]].
  subst delta. rewrite Hres in Hall.
  apply Forall_app in Hall. destruct Hall as [Hall' Hlast].
  assert (Hdiv : Z.divide p (Znth i a 0 + w)) by (inversion Hlast; assumption).
  pose proof (ElemCost_le_charge__cfp_step_11 change p (Znth i a 0) w Hp Hch Hw Hdiv) as Hle.
  rewrite (ChangeCost_snoc_ok__cfp_step_11 del change l r delta' w Hw) in Hc.
  exists (ChangeCost del change l r delta').
  assert (Hbase : PartialPlanCost a del change p i l r (ChangeCost del change l r delta')).
  { unfold PartialPlanCost.
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    exists delta', result'.
    split; [exact Hadj' | split; [exact Hall' | reflexivity]]. }
  split; [| lia].
  destruct (Z.eq_dec r i) as [Hri | Hri].
  - subst r.
    destruct (Z.eq_dec l 0) as [Hl | Hl].
    + subst l. left. exact Hbase.
    + destruct (Z.eq_dec l i) as [Hli | Hli].
      * subst l. right. right.
        apply keep_sub_after__cfp_step_11; [lia | exact Hbase].
      * right. left. exists l. split; [lia | split; [lia | exact Hbase]].
  - right. right. exists l, r. split; [lia | exact Hbase].
Qed.

(* ---------------- numeric bound on attained DP values ---------------- *)
Lemma ppc_bound__cfp_step_11 : forall a del change p i l r c,
  0 <= del -> 0 <= change -> PartialPlanCost a del change p i l r c ->
  0 <= c /\ c <= Zlength a * del + Zlength a * change.
Proof.
  intros a del change p i l r c Hd Hch HP.
  pose proof (Zlength_nonneg a) as Hnn.
  destruct HP as [Hl0 [Hlr [Hri [Hia [delta [result [Hadj [_ Hc]]]]]]]].
  destruct Hadj as [Hlen _].
  assert (Hdl : Zlength delta = l + (i - r)).
  { rewrite Hlen, Zlength_app.
    rewrite (Zlength_sublist 0 l a) by lia.
    rewrite (Zlength_sublist r i a) by lia. lia. }
  pose proof (ChangeCost_bound__cfp_step_11 del change l r delta Hd Hch Hlr) as Hb.
  rewrite Hdl in Hb.
  assert (H1 : (r - l) * del <= Zlength a * del) by nia.
  assert (H2 : (l + (i - r)) * change <= Zlength a * change) by nia.
  lia.
Qed.
Lemma cfp_state_finite_bound__cfp_step_11 :
  forall a del change p i keep cutFresh cutAfterKeep after,
    0 <= del <= 1000000000 -> 0 <= change <= 1000000000 ->
    Zlength a <= 1000000 ->
    CostForPrimeState a del change p i keep cutFresh cutAfterKeep after ->
    (keep <> INF -> 0 <= keep <= 2000000000000000) /\
    (cutFresh <> INF -> 0 <= cutFresh <= 2000000000000000) /\
    (cutAfterKeep <> INF -> 0 <= cutAfterKeep <= 2000000000000000) /\
    (after <> INF -> 0 <= after <= 2000000000000000).
Proof.
  intros a del change p i keep cutFresh cutAfterKeep after Hd Hch Hn HS.
  pose proof (Zlength_nonneg a) as Hnn.
  assert (Hbnd : forall l r c, PartialPlanCost a del change p i l r c ->
                               0 <= c <= 2000000000000000).
  { intros l r c HP.
    pose proof (ppc_bound__cfp_step_11 a del change p i l r c ltac:(lia) ltac:(lia) HP)
      as [Hlo Hhi].
    assert (Zlength a * del <= 1000000 * 1000000000) by nia.
    assert (Zlength a * change <= 1000000 * 1000000000) by nia.
    lia. }
  destruct HS as [HK [HF [HA HB]]].
  split; [| split; [| split]].
  - intros Hne. apply (Hbnd i i). apply dp_mem__cfp_step_11; assumption.
  - intros Hne. apply (Hbnd 0 i). apply dp_mem__cfp_step_11; assumption.
  - intros Hne.
    pose proof (dp_mem__cfp_step_11 _ _ HA Hne) as [l [_ [_ HP]]].
    apply (Hbnd _ _ _ HP).
  - intros Hne.
    pose proof (dp_mem__cfp_step_11 _ _ HB Hne) as [l [r [_ HP]]].
    apply (Hbnd _ _ _ HP).
Qed.

(* ---------------- the sweep step ---------------- *)
Lemma cfp_state_step__cfp_step_11 :
  forall a del change p i keep cutFresh cutAfterKeep after cost keep' cutAfterKeep',
    (keep' = keep + cost /\ keep + cost <= INF /\ keep <> INF \/
     keep' = INF /\ keep = INF) ->
    (cutAfterKeep' = INF /\
       (i + 1 <= 1 \/ (INF <= cutAfterKeep + del /\ INF <= keep + del)) \/
     cutAfterKeep' = cutAfterKeep + del /\ cutAfterKeep + del <= INF /\
       cutAfterKeep <= keep /\ 1 <= i /\ cutAfterKeep <> INF) ->
    0 <= i -> i + 1 <= Zlength a -> 2 <= p -> 0 <= del -> 0 <= change ->
    cost = ElemCost change p (Znth i a 0) -> cost <> INF ->
    cutFresh <> INF -> cutFresh <= cutAfterKeep -> cutFresh <= after ->
    cutFresh + del <= INF -> cutFresh + cost <= INF ->
    CostForPrimeState a del change p i keep cutFresh cutAfterKeep after ->
    CostForPrimeState a del change p (i + 1) keep' (cutFresh + del) cutAfterKeep'
                      (cutFresh + cost).
Proof.
  intros a del change p i keep cutFresh cutAfterKeep after cost keep' cutAfterKeep'
         Hkeep' Hcak' Hi Hi1 Hp Hdel Hch Hcost Hcostinf Hcfinf Hcfcak Hcfaf Hcfdel Hcfcost HS.
  destruct HS as [HK [HF [HA HB]]].
  assert (Hein : ElemCost change p (Znth i a 0) <> INF)
    by (rewrite <- Hcost; exact Hcostinf).
  pose proof (ElemCost_bound__cfp_step_11 change p (Znth i a 0) Hch Hein) as Hcb.
  rewrite <- Hcost in Hcb.
  destruct (ElemCost_attain__cfp_step_11 change p (Znth i a 0) Hp Hein)
    as [w [Hw [Hdiv Hchg]]].
  rewrite <- Hcost in Hchg.
  pose proof (dp_mem__cfp_step_11 _ _ HF Hcfinf) as HFmem0.
  pose proof HFmem0 as HFeq.
  apply (dpcutfresh_charac__cfp_step_11 a del change p i cutFresh ltac:(lia) ltac:(lia))
    in HFeq.
  assert (Hringi : (i + 1) * del = i * del + del) by ring.
  split; [| split; [| split]].
  - destruct Hkeep' as [[He [Hle Hkne]] | [He Hkinf]]; subst keep'.
    + apply (dp_step_fin__cfp_step_11 (DPKeep a del change p i) _ keep cost HK).
      * lia.
      * exact Hle.
      * rewrite <- Hchg.
        apply (dpkeep_sound__cfp_step_11 a del change p i keep w);
          [lia | lia | exact Hw | exact Hdiv | apply dp_mem__cfp_step_11; assumption].
      * intros z Hz.
        apply (dpkeep_dominate__cfp_step_11 a del change p i z) in Hz; [| lia | lia | lia | lia].
        destruct Hz as [c [Hc Hle2]]. exists c. split; [exact Hc | rewrite Hcost; lia].
    + apply (dp_step_inf__cfp_step_11 (DPKeep a del change p i) _ keep cost HK).
      * lia.
      * lia.
      * intros z Hz.
        apply (dpkeep_dominate__cfp_step_11 a del change p i z) in Hz; [| lia | lia | lia | lia].
        destruct Hz as [c [Hc Hle2]]. exists c. split; [exact Hc | rewrite Hcost; lia].
  - apply (dp_step_fin__cfp_step_11 (DPCutFresh a del change p i) _ cutFresh del HF).
    + lia.
    + exact Hcfdel.
    + apply (dpcutfresh_charac__cfp_step_11 a del change p (i + 1) (cutFresh + del));
        [lia | lia |]. lia.
    + intros z Hz.
      apply (dpcutfresh_charac__cfp_step_11 a del change p (i + 1) z) in Hz; [| lia | lia].
      exists cutFresh. split; [exact HFmem0 | lia].
  - destruct Hcak' as [[He Hcase] | [He [Hle [Hcakkeep [Hipos Hcakne]]]]]; subst cutAfterKeep'.
    + destruct Hcase as [Hsmall | [Hc1 Hc2]].
      * apply dp_empty_intro__cfp_step_11.
        apply dp_cutafterkeep_zero_empty__cfp_step_11. lia.
      * apply (dp_step_inf__cfp_step_11
                 (fun z => DPKeep a del change p i z \/ DPCutAfterKeep a del change p i z)
                 _ (Z.min keep cutAfterKeep) del).
        -- apply dp_union2__cfp_step_11; assumption.
        -- lia.
        -- destruct (Z.min_spec keep cutAfterKeep) as [[? Hm] | [? Hm]]; rewrite Hm; lia.
        -- intros z Hz.
           apply (dpcak_dominate__cfp_step_11 a del change p i z) in Hz; [| lia | lia].
           exact Hz.
    + assert (Hmin : Z.min keep cutAfterKeep = cutAfterKeep) by (apply Z.min_r; lia).
      replace (cutAfterKeep + del) with (Z.min keep cutAfterKeep + del)
        by (rewrite Hmin; reflexivity).
      apply (dp_step_fin__cfp_step_11
               (fun z => DPKeep a del change p i z \/ DPCutAfterKeep a del change p i z)
               _ (Z.min keep cutAfterKeep) del).
      * apply dp_union2__cfp_step_11; assumption.
      * lia.
      * rewrite Hmin. exact Hle.
      * rewrite Hmin. apply dpcak_sound__cfp_step_11; [lia | lia |].
        apply dp_mem__cfp_step_11; assumption.
      * intros z Hz.
        apply (dpcak_dominate__cfp_step_11 a del change p i z) in Hz; [| lia | lia].
        exact Hz.
  - assert (Hminaf : Z.min cutFresh (Z.min cutAfterKeep after) = cutFresh)
      by (apply Z.min_l; apply Z.min_glb; lia).
    replace (cutFresh + cost) with (Z.min cutFresh (Z.min cutAfterKeep after) + cost)
      by (rewrite Hminaf; reflexivity).
    apply (dp_step_fin__cfp_step_11
             (fun z => DPCutFresh a del change p i z \/
                       (DPCutAfterKeep a del change p i z \/ DPAfter a del change p i z))
             _ (Z.min cutFresh (Z.min cutAfterKeep after)) cost).
    + apply dp_union2__cfp_step_11;
        [exact HF | apply dp_union2__cfp_step_11; [exact HA | exact HB]].
    + lia.
    + rewrite Hminaf. exact Hcfcost.
    + rewrite Hminaf. rewrite <- Hchg.
      apply (dpafter_sound_from_fresh__cfp_step_11 a del change p i cutFresh w);
        [lia | lia | exact Hw | exact Hdiv | exact HFmem0].
    + intros z Hz.
      apply (dpafter_dominate__cfp_step_11 a del change p i z) in Hz; [| lia | lia | lia | lia].
      destruct Hz as [c [Hcc Hle2]]. exists c. split; [exact Hcc | rewrite Hcost; lia].
Qed.
Lemma fold_filter_card__cfp_step_12 : forall (l : list Z) (q : Z -> bool) (g : Z -> Z),
  (forall x, g x = if q x then 1 else 0) ->
  fold_right (fun (_ : Z) (acc : Z) => 1 + acc) 0 (filter q l) =
  fold_right (fun (x : Z) (acc : Z) => g x + acc) 0 l.
Proof.
  induction l as [| x l IH]; intros q g Hg; simpl.
  - reflexivity.
  - rewrite (Hg x). rewrite <- (IH q g Hg). destruct (q x); simpl; lia.
Qed.
Lemma count_as_sum__cfp_step_12 : forall (v : Z) (xs : list Z),
  Count v xs =
  sum (fun i => 0 <= i < Zlength xs)
      (fun i => if prop_dec (Znth i xs 0 = v) then 1 else 0).
Proof.
  intros v xs.
  unfold Count, set_card, sum, enum, finite_Z_range', finite_Z_range.
  apply fold_filter_card__cfp_step_12.
  intros x. destruct (prop_dec (Znth x xs 0 = v)); reflexivity.
Qed.
Lemma count_snoc__cfp_step_12 : forall (v : Z) (xs : list Z) (d : Z),
  Count v (xs ++ [d]) = Count v xs + (if prop_dec (d = v) then 1 else 0).
Proof.
  intros v xs d.
  rewrite !count_as_sum__cfp_step_12.
  rewrite (sum_Z_range_Znth_app_single 0 d xs (fun y => if prop_dec (y = v) then 1 else 0)).
  reflexivity.
Qed.
Lemma count_nonneg__cfp_step_12 : forall (v : Z) (xs : list Z), 0 <= Count v xs.
Proof.
  intros v xs.
  rewrite count_as_sum__cfp_step_12.
  pose proof (Zlength_nonneg xs).
  pose proof (sum_Z_range_bounds 0 (Zlength xs)
                (fun i => if prop_dec (Znth i xs 0 = v) then 1 else 0) 0 1) as HB.
  destruct HB as [HB1 HB2]; try lia.
  intros x Hx. destruct (prop_dec (Znth x xs 0 = v)); lia.
Qed.
Lemma count_pair_bound__cfp_step_12 : forall (xs : list Z),
  Count (-1) xs + Count 1 xs <= Zlength xs.
Proof.
  intros xs.
  pose proof (Zlength_nonneg xs) as HL.
  rewrite !count_as_sum__cfp_step_12.
  rewrite <- sum_Z_range_add.
  pose proof (sum_Z_range_le 0 (Zlength xs)
     (fun i => (if prop_dec (Znth i xs 0 = -1) then 1 else 0)
             + (if prop_dec (Znth i xs 0 = 1) then 1 else 0))
     (fun _ => 1)) as HLe.
  rewrite sum_Z_range_const in HLe by lia.
  assert (Hstep : forall x, 0 <= x < Zlength xs ->
     (if prop_dec (Znth x xs 0 = -1) then 1 else 0)
   + (if prop_dec (Znth x xs 0 = 1) then 1 else 0) <= 1).
  { intros x Hx.
    destruct (prop_dec (Znth x xs 0 = -1)); destruct (prop_dec (Znth x xs 0 = 1)); lia. }
  specialize (HLe Hstep). lia.
Qed.
Lemma combine_app_single__cfp_step_12 : forall (K delta : list Z) (x d : Z),
  length K = length delta ->
  combine (K ++ [x]) (delta ++ [d]) = combine K delta ++ [(x, d)].
Proof.
  induction K as [| k K IH]; intros delta x d Hlen.
  - destruct delta; simpl in *; [reflexivity | discriminate].
  - destruct delta as [| e delta]; simpl in Hlen; [discriminate |].
    simpl. rewrite IH by lia. reflexivity.
Qed.
Lemma zlength_length_eq__cfp_step_12 : forall (l1 l2 : list Z),
  Zlength l1 = Zlength l2 -> length l1 = length l2.
Proof.
  intros l1 l2 H. rewrite !Zlength_correct in H. lia.
Qed.
Lemma adjusted_snoc_intro__cfp_step_12 : forall (K : list Z) (x : Z) (delta result : list Z) (d : Z),
  Adjusted K delta result ->
  (d = -1 \/ d = 0 \/ d = 1) ->
  Adjusted (K ++ [x]) (delta ++ [d]) (result ++ [x + d]).
Proof.
  intros K x delta result d [Hlen [Hall Hres]] Hd.
  unfold Adjusted.
  split; [| split].
  - rewrite !Zlength_app, !Zlength_cons, !Zlength_nil. lia.
  - apply Forall_app. split; [exact Hall |]. constructor; [exact Hd | constructor].
  - rewrite combine_app_single__cfp_step_12 by (apply zlength_length_eq__cfp_step_12; lia).
    rewrite map_app. simpl. rewrite <- Hres. reflexivity.
Qed.
Lemma adjusted_snoc_elim__cfp_step_12 : forall (K : list Z) (x : Z) (delta' result' : list Z),
  Adjusted (K ++ [x]) delta' result' ->
  exists (delta result : list Z) (d : Z),
    delta' = delta ++ [d] /\ result' = result ++ [x + d] /\
    Adjusted K delta result /\ (d = -1 \/ d = 0 \/ d = 1).
Proof.
  intros K x delta' result' HA.
  destruct HA as [Hlen [Hall Hres]].
  assert (Hne : delta' <> []).
  { intros Hc. rewrite Hc in Hlen.
    rewrite Zlength_app, !Zlength_cons, !Zlength_nil in Hlen.
    pose proof (Zlength_nonneg K). lia. }
  destruct (exists_last Hne) as [delta [d Hsplit]].
  subst delta'.
  rewrite !Zlength_app, !Zlength_cons, !Zlength_nil in Hlen.
  apply Forall_app in Hall. destruct Hall as [Hall1 Hall2].
  assert (Hd : d = -1 \/ d = 0 \/ d = 1) by (inversion Hall2; auto).
  exists delta, (map (fun q : Z * Z => fst q + snd q) (combine K delta)), d.
  split; [reflexivity |].
  split.
  - rewrite Hres. rewrite combine_app_single__cfp_step_12 by (apply zlength_length_eq__cfp_step_12; lia).
    rewrite map_app. reflexivity.
  - split; [| exact Hd].
    unfold Adjusted. split; [lia | split; [exact Hall1 | reflexivity]].
Qed.
Lemma elemcost_cases__cfp_step_12 : forall (change p x : Z),
  ElemCost change p x = 0 \/ ElemCost change p x = change \/ ElemCost change p x = INF.
Proof.
  intros change p x. unfold ElemCost.
  destruct (Z.eqb (x mod p) 0); [left; reflexivity |].
  destruct (orb (Z.eqb ((x - 1) mod p) 0) (Z.eqb ((x + 1) mod p) 0));
    [right; left; reflexivity | right; right; reflexivity].
Qed.
Lemma elemcost_nonneg__cfp_step_12 : forall (change p x : Z),
  0 <= change -> 0 <= ElemCost change p x.
Proof.
  intros change p x Hc.
  destruct (elemcost_cases__cfp_step_12 change p x) as [H | [H | H]]; rewrite H; unfold INF; lia.
Qed.
Lemma elemcost_le_change__cfp_step_12 : forall (change p x : Z),
  0 <= change -> ElemCost change p x <> INF -> ElemCost change p x <= change.
Proof.
  intros change p x Hc Hne.
  destruct (elemcost_cases__cfp_step_12 change p x) as [H | [H | H]]; rewrite H; lia.
Qed.
Lemma elemcost_lb__cfp_step_12 : forall (change p x d : Z),
  2 <= p -> 0 <= change ->
  (d = -1 \/ d = 0 \/ d = 1) -> Z.divide p (x + d) ->
  ElemCost change p x <= (if prop_dec (d = 0) then 0 else change).
Proof.
  intros change p x d Hp Hc Hd Hdiv.
  assert (Hp0 : p <> 0) by lia.
  unfold ElemCost.
  destruct Hd as [Hd | [Hd | Hd]]; subst d.
  - destruct (prop_dec ((-1) = 0)) as [Habs | _]; [lia |].
    replace (x + -1) with (x - 1) in Hdiv by lia.
    apply (Z.mod_divide (x - 1) p Hp0) in Hdiv.
    rewrite Hdiv. simpl.
    destruct (Z.eqb (x mod p) 0); lia.
  - destruct (prop_dec (0 = 0)) as [_ | Habs]; [| lia].
    replace (x + 0) with x in Hdiv by lia.
    apply (Z.mod_divide x p Hp0) in Hdiv.
    rewrite Hdiv. simpl. lia.
  - destruct (prop_dec (1 = 0)) as [Habs | _]; [lia |].
    apply (Z.mod_divide (x + 1) p Hp0) in Hdiv.
    rewrite Hdiv. rewrite Bool.orb_true_r.
    destruct (Z.eqb (x mod p) 0); lia.
Qed.
Lemma elemcost_attain__cfp_step_12 : forall (change p x : Z),
  2 <= p -> ElemCost change p x <> INF ->
  exists d, (d = -1 \/ d = 0 \/ d = 1) /\ Z.divide p (x + d) /\
            ElemCost change p x = (if prop_dec (d = 0) then 0 else change).
Proof.
  intros change p x Hp Hne.
  assert (Hp0 : p <> 0) by lia.
  unfold ElemCost in *.
  destruct (Z.eqb (x mod p) 0) eqn:E0.
  - exists 0. split; [tauto | ]. split.
    + replace (x + 0) with x by lia.
      apply (Z.mod_divide x p Hp0). apply Z.eqb_eq. exact E0.
    + destruct (prop_dec (0 = 0)); [reflexivity | lia].
  - destruct (Z.eqb ((x - 1) mod p) 0) eqn:E1.
    + exists (-1). split; [tauto | ]. split.
      * replace (x + -1) with (x - 1) by lia.
        apply (Z.mod_divide (x - 1) p Hp0). apply Z.eqb_eq. exact E1.
      * simpl. destruct (prop_dec ((-1) = 0)); [lia | reflexivity].
    + destruct (Z.eqb ((x + 1) mod p) 0) eqn:E2.
      * exists 1. split; [tauto | ]. split.
        -- apply (Z.mod_divide (x + 1) p Hp0). apply Z.eqb_eq. exact E2.
        -- simpl. destruct (prop_dec (1 = 0)); [lia | reflexivity].
      * simpl in Hne. contradiction.
Qed.
Lemma sublist_same_nil__cfp_step_12 : forall (a : list Z) (i : Z),
  0 <= i -> sublist i i a = [].
Proof.
  intros a i Hi. unfold sublist.
  apply skipn_all2. rewrite length_firstn. lia.
Qed.
Lemma sublist_extend_right__cfp_step_12 : forall (a : list Z) (r i : Z),
  0 <= r -> r <= i -> i < Zlength a ->
  sublist r (i + 1) a = sublist r i a ++ [Znth i a 0].
Proof.
  intros a r i Hr Hri Hi.
  rewrite (sublist_split r (i + 1) i a) by lia.
  rewrite (sublist_single 0 i a) by lia.
  reflexivity.
Qed.
Lemma dpvalue_lb__cfp_step_12 : forall (S : Z -> Prop) (v c : Z),
  DPValue S v -> S c -> v <= c.
Proof.
  intros S v c HD HS.
  unfold DPValue, min_value_of_subset_with_default, min_value_of_subset,
         min_object_of_subset in HD.
  sets_unfold in HD.
  destruct HD as [[[w [[Hin Hmin] Heq]] Hle] | [Hall Heq]].
  - subst w. apply Hmin. exact HS.
  - subst v. apply Hall. exact HS.
Qed.
Lemma dpvalue_ub__cfp_step_12 : forall (S : Z -> Prop) (v : Z), DPValue S v -> v <= INF.
Proof.
  intros S v HD.
  unfold DPValue, min_value_of_subset_with_default in HD.
  destruct HD as [[_ Hle] | [_ Heq]]; [exact Hle | subst v; apply Z.le_refl].
Qed.
Lemma dpvalue_mem__cfp_step_12 : forall (S : Z -> Prop) (v : Z),
  DPValue S v -> v <> INF -> S v.
Proof.
  intros S v HD Hne.
  unfold DPValue, min_value_of_subset_with_default, min_value_of_subset,
         min_object_of_subset in HD.
  sets_unfold in HD.
  destruct HD as [[[w [[Hin Hmin] Heq]] Hle] | [Hall Heq]].
  - subst w. exact Hin.
  - contradiction.
Qed.
Lemma dpvalue_intro__cfp_step_12 : forall (S : Z -> Prop) (v : Z),
  (forall c, S c -> v <= c) ->
  (v <> INF -> S v) ->
  v <= INF ->
  DPValue S v.
Proof.
  intros S v Hlb Hmem Hub.
  unfold DPValue, min_value_of_subset_with_default, min_value_of_subset,
         min_object_of_subset.
  sets_unfold.
  destruct (Z.eq_dec v INF) as [He | Hne].
  - right. split; [| exact He].
    intros c Hc. rewrite <- He. apply Hlb. exact Hc.
  - left. split; [| exact Hub].
    exists v. split; [| reflexivity].
    split; [apply Hmem; exact Hne | exact Hlb].
Qed.
Lemma ppc_transfer__cfp_step_12 : forall (a : list Z) (del change p i1 l1 r1 i2 l2 r2 c c' : Z),
  0 <= l2 -> l2 <= r2 -> r2 <= i2 -> i2 <= Zlength a ->
  sublist 0 l1 a ++ sublist r1 i1 a = sublist 0 l2 a ++ sublist r2 i2 a ->
  c' = c + ((r2 - l2) - (r1 - l1)) * del ->
  PartialPlanCost a del change p i1 l1 r1 c ->
  PartialPlanCost a del change p i2 l2 r2 c'.
Proof.
  intros a del change p i1 l1 r1 i2 l2 r2 c c' Hl2 Hlr2 Hri2 Hi2 Hkept Hc' HP.
  destruct HP as [_ [_ [_ [_ [delta [result [HA [HF Hcost]]]]]]]].
  unfold PartialPlanCost.
  split; [lia | split; [lia | split; [lia | split; [lia |]]]].
  exists delta, result.
  rewrite <- Hkept.
  split; [exact HA | split; [exact HF |]].
  unfold ChangeCost in *. lia.
Qed.
Lemma ppc_snoc_intro__cfp_step_12 : forall (a : list Z) (del change p i l r c c' : Z),
  0 <= l -> l <= r -> r <= i -> i < Zlength a -> 2 <= p ->
  ElemCost change p (Znth i a 0) <> INF ->
  c' = c + ElemCost change p (Znth i a 0) ->
  PartialPlanCost a del change p i l r c ->
  PartialPlanCost a del change p (i + 1) l r c'.
Proof.
  intros a del change p i l r c c' Hl Hlr Hri Hi Hp Hne Hc' HP.
  destruct HP as [_ [_ [_ [_ [delta [result [HA [HF Hcost]]]]]]]].
  destruct (elemcost_attain__cfp_step_12 change p (Znth i a 0) Hp Hne) as [d [Hd [Hdiv Hval]]].
  unfold PartialPlanCost.
  split; [lia | split; [lia | split; [lia | split; [lia |]]]].
  exists (delta ++ [d]), (result ++ [Znth i a 0 + d]).
  rewrite (sublist_extend_right__cfp_step_12 a r i) by lia.
  rewrite app_assoc.
  split; [apply adjusted_snoc_intro__cfp_step_12; assumption |].
  split.
  - apply Forall_app. split; [exact HF |]. constructor; [exact Hdiv | constructor].
  - unfold ChangeCost in *. rewrite !count_snoc__cfp_step_12.
    rewrite Hc', Hcost, Hval.
    destruct Hd as [Hd | [Hd | Hd]]; subst d;
      repeat (destruct (prop_dec _); try lia).
Qed.
Lemma ppc_snoc_elim__cfp_step_12 : forall (a : list Z) (del change p i l r c : Z),
  0 <= l -> l <= r -> r <= i -> i < Zlength a -> 2 <= p -> 0 <= change ->
  PartialPlanCost a del change p (i + 1) l r c ->
  exists c0, PartialPlanCost a del change p i l r c0 /\
             c0 + ElemCost change p (Znth i a 0) <= c.
Proof.
  intros a del change p i l r c Hl Hlr Hri Hi Hp Hch HP.
  destruct HP as [_ [_ [_ [_ [delta' [result' [HA [HF Hcost]]]]]]]].
  rewrite (sublist_extend_right__cfp_step_12 a r i) in HA by lia.
  rewrite app_assoc in HA.
  destruct (adjusted_snoc_elim__cfp_step_12 _ _ _ _ HA) as [delta [result [d [Hde [Hre [HA0 Hd]]]]]].
  exists (ChangeCost del change l r delta).
  split.
  - unfold PartialPlanCost.
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    exists delta, result.
    split; [exact HA0 | split; [| reflexivity]].
    rewrite Hre in HF. apply Forall_app in HF. tauto.
  - pose proof (elemcost_lb__cfp_step_12 change p (Znth i a 0) d Hp Hch Hd) as Hlb.
    rewrite Hre in HF. apply Forall_app in HF. destruct HF as [_ HFd].
    assert (Hdiv : Z.divide p (Znth i a 0 + d)) by (inversion HFd; auto).
    specialize (Hlb Hdiv).
    rewrite Hcost, Hde. unfold ChangeCost. rewrite !count_snoc__cfp_step_12.
    destruct Hd as [Hd | [Hd | Hd]]; subst d;
      repeat (destruct (prop_dec _); try lia).
Qed.
Lemma ppc_bounds_of__cfp_step_12 : forall (a : list Z) (del change p i l r c : Z),
  PartialPlanCost a del change p i l r c ->
  0 <= l /\ l <= r /\ r <= i /\ i <= Zlength a.
Proof. intros. destruct H as [? [? [? [? _]]]]. tauto. Qed.
Lemma kept_keep_eq__cfp_step_12 : forall (a : list Z) (i : Z),
  0 <= i -> i < Zlength a ->
  sublist 0 i a ++ sublist i (i + 1) a
  = sublist 0 (i + 1) a ++ sublist (i + 1) (i + 1) a.
Proof.
  intros a i Hi0 Hi.
  rewrite (sublist_extend_right__cfp_step_12 a i i) by lia.
  rewrite (sublist_extend_right__cfp_step_12 a 0 i) by lia.
  rewrite (sublist_same_nil__cfp_step_12 a i) by lia.
  rewrite (sublist_same_nil__cfp_step_12 a (i + 1)) by lia.
  rewrite app_nil_r. reflexivity.
Qed.
Lemma kept_cut_eq__cfp_step_12 : forall (a : list Z) (l i : Z),
  0 <= i ->
  sublist 0 l a ++ sublist i i a = sublist 0 l a ++ sublist (i + 1) (i + 1) a.
Proof.
  intros a l i Hi.
  rewrite (sublist_same_nil__cfp_step_12 a i) by lia.
  rewrite (sublist_same_nil__cfp_step_12 a (i + 1)) by lia.
  reflexivity.
Qed.
Lemma kept_keep_after_eq__cfp_step_12 : forall (a : list Z) (i : Z),
  1 <= i -> i <= Zlength a ->
  sublist 0 i a ++ sublist i i a = sublist 0 (i - 1) a ++ sublist (i - 1) i a.
Proof.
  intros a i Hi1 Hi.
  rewrite (sublist_same_nil__cfp_step_12 a i) by lia.
  rewrite app_nil_r.
  rewrite (sublist_split 0 i (i - 1) a) by lia.
  reflexivity.
Qed.
Lemma dpkeep_fwd__cfp_step_12 : forall (a : list Z) (del change p i c : Z),
  0 <= i -> i < Zlength a -> 2 <= p ->
  ElemCost change p (Znth i a 0) <> INF ->
  DPKeep a del change p i c ->
  DPKeep a del change p (i + 1) (c + ElemCost change p (Znth i a 0)).
Proof.
  intros a del change p i c Hi0 Hi Hp Hne HK.
  unfold DPKeep in *.
  eapply ppc_transfer__cfp_step_12 with (i1 := i + 1) (l1 := i) (r1 := i); try lia.
  - apply kept_keep_eq__cfp_step_12; lia.
  - instantiate (1 := c + ElemCost change p (Znth i a 0)). lia.
  - eapply ppc_snoc_intro__cfp_step_12; try lia; try eassumption. reflexivity.
Qed.
Lemma dpkeep_bwd__cfp_step_12 : forall (a : list Z) (del change p i c : Z),
  0 <= i -> i < Zlength a -> 2 <= p -> 0 <= change ->
  DPKeep a del change p (i + 1) c ->
  exists c0, DPKeep a del change p i c0 /\
             c0 + ElemCost change p (Znth i a 0) <= c.
Proof.
  intros a del change p i c Hi0 Hi Hp Hch HK.
  unfold DPKeep in *.
  assert (HP : PartialPlanCost a del change p (i + 1) i i c).
  { eapply ppc_transfer__cfp_step_12 with (i1 := i + 1) (l1 := i + 1) (r1 := i + 1); try lia.
    - symmetry. apply kept_keep_eq__cfp_step_12; lia.
    - instantiate (1 := c). lia.
    - exact HK. }
  eapply ppc_snoc_elim__cfp_step_12; try lia; try eassumption.
Qed.
Lemma dpcutfresh_char__cfp_step_12 : forall (a : list Z) (del change p i c : Z),
  0 <= i -> i <= Zlength a ->
  (DPCutFresh a del change p i c <-> c = i * del).
Proof.
  intros a del change p i c Hi0 Hi.
  unfold DPCutFresh, PartialPlanCost.
  split.
  - intros [_ [_ [_ [_ [delta [result [HA [_ Hcost]]]]]]]].
    destruct HA as [Hlen [_ _]].
    rewrite (sublist_same_nil__cfp_step_12 a 0) in Hlen by lia.
    rewrite (sublist_same_nil__cfp_step_12 a i) in Hlen by lia.
    simpl in Hlen. rewrite Zlength_nil in Hlen.
    assert (Hd : delta = []).
    { destruct delta as [| x delta]; [reflexivity |].
      rewrite Zlength_cons in Hlen. pose proof (Zlength_nonneg delta). lia. }
    subst delta. unfold ChangeCost in Hcost.
    change (Count (-1) []) with 0 in Hcost.
    change (Count 1 []) with 0 in Hcost.
    lia.
  - intros Hc.
    split; [lia | split; [lia | split; [lia | split; [lia |]]]].
    exists [], [].
    rewrite (sublist_same_nil__cfp_step_12 a 0) by lia.
    rewrite (sublist_same_nil__cfp_step_12 a i) by lia.
    split.
    + unfold Adjusted. simpl. split; [reflexivity | split; [constructor | reflexivity]].
    + split; [constructor |].
      unfold ChangeCost.
      change (Count (-1) []) with 0.
      change (Count 1 []) with 0.
      lia.
Qed.
Lemma dpcak_zero_empty__cfp_step_12 : forall (a : list Z) (del change p c : Z),
  ~ DPCutAfterKeep a del change p 0 c.
Proof. intros a del change p c [l [H1 [H2 _]]]. lia. Qed.
Lemma dpcak_fwd_cak__cfp_step_12 : forall (a : list Z) (del change p i c : Z),
  0 <= i -> i + 1 <= Zlength a ->
  DPCutAfterKeep a del change p i c ->
  DPCutAfterKeep a del change p (i + 1) (c + del).
Proof.
  intros a del change p i c Hi0 Hi [l [Hl1 [Hl2 HP]]].
  exists l. split; [lia | split; [lia |]].
  eapply ppc_transfer__cfp_step_12 with (i1 := i) (l1 := l) (r1 := i); try lia.
  - apply kept_cut_eq__cfp_step_12; lia.
  - instantiate (1 := c). lia.
  - exact HP.
Qed.
Lemma dpcak_fwd_keep__cfp_step_12 : forall (a : list Z) (del change p i c : Z),
  1 <= i -> i + 1 <= Zlength a ->
  DPKeep a del change p i c ->
  DPCutAfterKeep a del change p (i + 1) (c + del).
Proof.
  intros a del change p i c Hi1 Hi HK.
  exists i. split; [lia | split; [lia |]].
  eapply ppc_transfer__cfp_step_12 with (i1 := i) (l1 := i) (r1 := i); try lia.
  - apply kept_cut_eq__cfp_step_12; lia.
  - instantiate (1 := c). lia.
  - exact HK.
Qed.
Lemma dpcak_bwd__cfp_step_12 : forall (a : list Z) (del change p i c : Z),
  0 <= i ->
  DPCutAfterKeep a del change p (i + 1) c ->
  exists c0, (DPCutAfterKeep a del change p i c0 \/
              (1 <= i /\ DPKeep a del change p i c0)) /\ c = c0 + del.
Proof.
  intros a del change p i c Hi0 [l [Hl1 [Hl2 HP]]].
  pose proof (ppc_bounds_of__cfp_step_12 _ _ _ _ _ _ _ _ HP) as [Hb1 [Hb2 [Hb3 Hb4]]].
  destruct (Z.eq_dec l i) as [He | Hne].
  - subst l. exists (c - del). split.
    + right. split; [lia |].
      unfold DPKeep.
      eapply ppc_transfer__cfp_step_12 with (i1 := i + 1) (l1 := i) (r1 := i + 1); try lia.
      * symmetry. apply kept_cut_eq__cfp_step_12; lia.
      * instantiate (1 := c). lia.
      * exact HP.
    + lia.
  - exists (c - del). split.
    + left. exists l. split; [lia | split; [lia |]].
      eapply ppc_transfer__cfp_step_12 with (i1 := i + 1) (l1 := l) (r1 := i + 1); try lia.
      * symmetry. apply kept_cut_eq__cfp_step_12; lia.
      * instantiate (1 := c). lia.
      * exact HP.
    + lia.
Qed.
Lemma dpafter_fwd_gen__cfp_step_12 : forall (a : list Z) (del change p i l r c : Z),
  0 <= i -> i < Zlength a -> 2 <= p ->
  ElemCost change p (Znth i a 0) <> INF ->
  r <= i ->
  PartialPlanCost a del change p i l r c ->
  DPAfter a del change p (i + 1) (c + ElemCost change p (Znth i a 0)).
Proof.
  intros a del change p i l r c Hi0 Hi Hp Hne Hr HP.
  pose proof (ppc_bounds_of__cfp_step_12 _ _ _ _ _ _ _ _ HP) as [Hb1 [Hb2 [Hb3 Hb4]]].
  exists l, r. split; [lia |].
  eapply ppc_snoc_intro__cfp_step_12; try lia; try eassumption. reflexivity.
Qed.
Lemma dpafter_fwd_cutfresh__cfp_step_12 : forall (a : list Z) (del change p i c : Z),
  0 <= i -> i < Zlength a -> 2 <= p ->
  ElemCost change p (Znth i a 0) <> INF ->
  DPCutFresh a del change p i c ->
  DPAfter a del change p (i + 1) (c + ElemCost change p (Znth i a 0)).
Proof.
  intros a del change p i c Hi0 Hi Hp Hne HC.
  eapply dpafter_fwd_gen__cfp_step_12 with (l := 0) (r := i); try lia; try eassumption.
Qed.
Lemma dpafter_fwd_cak__cfp_step_12 : forall (a : list Z) (del change p i c : Z),
  0 <= i -> i < Zlength a -> 2 <= p ->
  ElemCost change p (Znth i a 0) <> INF ->
  DPCutAfterKeep a del change p i c ->
  DPAfter a del change p (i + 1) (c + ElemCost change p (Znth i a 0)).
Proof.
  intros a del change p i c Hi0 Hi Hp Hne [l [Hl1 [Hl2 HP]]].
  eapply dpafter_fwd_gen__cfp_step_12 with (l := l) (r := i); try lia; try eassumption.
Qed.
Lemma dpafter_fwd_keep__cfp_step_12 : forall (a : list Z) (del change p i c : Z),
  0 <= i -> i < Zlength a -> 2 <= p ->
  ElemCost change p (Znth i a 0) <> INF ->
  DPKeep a del change p i c ->
  DPAfter a del change p (i + 1) (c + ElemCost change p (Znth i a 0)).
Proof.
  intros a del change p i c Hi0 Hi Hp Hne HK.
  eapply dpafter_fwd_gen__cfp_step_12 with (l := i) (r := i); try lia; try eassumption.
Qed.
Lemma dpafter_fwd_after__cfp_step_12 : forall (a : list Z) (del change p i c : Z),
  0 <= i -> i < Zlength a -> 2 <= p ->
  ElemCost change p (Znth i a 0) <> INF ->
  DPAfter a del change p i c ->
  DPAfter a del change p (i + 1) (c + ElemCost change p (Znth i a 0)).
Proof.
  intros a del change p i c Hi0 Hi Hp Hne [l [r [Hr HP]]].
  eapply dpafter_fwd_gen__cfp_step_12 with (l := l) (r := r); try lia; try eassumption.
Qed.
Lemma dpkeep_sub_dpafter__cfp_step_12 : forall (a : list Z) (del change p i c : Z),
  1 <= i ->
  DPKeep a del change p i c ->
  DPAfter a del change p i c.
Proof.
  intros a del change p i c Hi1 HK.
  pose proof (ppc_bounds_of__cfp_step_12 _ _ _ _ _ _ _ _ HK) as [Hb1 [Hb2 [Hb3 Hb4]]].
  exists (i - 1), (i - 1). split; [lia |].
  eapply ppc_transfer__cfp_step_12 with (i1 := i) (l1 := i) (r1 := i); try lia.
  - apply kept_keep_after_eq__cfp_step_12; lia.
  - instantiate (1 := c). lia.
  - exact HK.
Qed.
Lemma dpafter_bwd__cfp_step_12 : forall (a : list Z) (del change p i c : Z),
  0 <= i -> i < Zlength a -> 2 <= p -> 0 <= change ->
  DPAfter a del change p (i + 1) c ->
  exists c0,
    (DPCutFresh a del change p i c0 \/ DPCutAfterKeep a del change p i c0 \/
     DPAfter a del change p i c0 \/ DPKeep a del change p i c0) /\
    c0 + ElemCost change p (Znth i a 0) <= c.
Proof.
  intros a del change p i c Hi0 Hi Hp Hch [l [r [Hr HP]]].
  pose proof (ppc_bounds_of__cfp_step_12 _ _ _ _ _ _ _ _ HP) as [Hb1 [Hb2 [Hb3 Hb4]]].
  assert (Hri : r <= i) by lia.
  destruct (ppc_snoc_elim__cfp_step_12 a del change p i l r c Hb1 Hb2 Hri Hi Hp Hch HP)
    as [c0 [HP0 Hle]].
  exists c0. split; [| exact Hle].
  destruct (Z.eq_dec r i) as [Hre | Hrne].
  - subst r.
    destruct (Z.eq_dec l 0) as [Hle0 | Hlne0].
    + subst l. left. exact HP0.
    + destruct (Z.eq_dec l i) as [Hli | Hlni].
      * subst l. right; right; right. exact HP0.
      * right; left. exists l. split; [lia | split; [lia | exact HP0]].
  - right; right; left. exists l, r. split; [lia | exact HP0].
Qed.
Lemma ppc_bound_value__cfp_step_12 : forall (a : list Z) (del change p i l r c : Z),
  0 <= del -> del <= 1000000000 -> 0 <= change -> change <= 1000000000 ->
  Zlength a <= 1000000 ->
  PartialPlanCost a del change p i l r c ->
  0 <= c /\ c <= 2000000000000000.
Proof.
  intros a del change p i l r c Hd0 Hd1 Hc0 Hc1 Ha HP.
  pose proof (ppc_bounds_of__cfp_step_12 _ _ _ _ _ _ _ _ HP) as [Hb1 [Hb2 [Hb3 Hb4]]].
  destruct HP as [_ [_ [_ [_ [delta [result [HA [_ Hcost]]]]]]]].
  destruct HA as [Hlen [_ _]].
  rewrite Zlength_app in Hlen.
  rewrite (Zlength_sublist 0 l a) in Hlen by lia.
  rewrite (Zlength_sublist r i a) in Hlen by lia.
  pose proof (count_nonneg__cfp_step_12 (-1) delta) as Hn1.
  pose proof (count_nonneg__cfp_step_12 1 delta) as Hn2.
  pose proof (count_pair_bound__cfp_step_12 delta) as Hpb.
  unfold ChangeCost in Hcost.
  assert (Hsum : (r - l) + (Count (-1) delta + Count 1 delta) <= 1000000) by lia.
  split; nia.
Qed.
Lemma cfp_state_finite_bound__cfp_step_12 :
  forall (a : list Z) (del change p i keep cutFresh cutAfterKeep after : Z),
  0 <= del -> del <= 1000000000 -> 0 <= change -> change <= 1000000000 ->
  Zlength a <= 1000000 ->
  CostForPrimeState a del change p i keep cutFresh cutAfterKeep after ->
  (keep <> INF -> 0 <= keep <= 2000000000000000) /\
  (cutFresh <> INF -> 0 <= cutFresh <= 2000000000000000) /\
  (cutAfterKeep <> INF -> 0 <= cutAfterKeep <= 2000000000000000) /\
  (after <> INF -> 0 <= after <= 2000000000000000).
Proof.
  intros a del change p i keep cutFresh cutAfterKeep after
         Hd0 Hd1 Hc0 Hc1 Ha [HK [HF [HA HB]]].
  split; [| split; [| split]].
  - intros Hne. pose proof (dpvalue_mem__cfp_step_12 _ _ HK Hne) as HM.
    unfold DPKeep in HM.
    apply (ppc_bound_value__cfp_step_12 a del change p i i i keep); assumption.
  - intros Hne. pose proof (dpvalue_mem__cfp_step_12 _ _ HF Hne) as HM.
    unfold DPCutFresh in HM.
    apply (ppc_bound_value__cfp_step_12 a del change p i 0 i cutFresh); assumption.
  - intros Hne. pose proof (dpvalue_mem__cfp_step_12 _ _ HA Hne) as HM.
    unfold DPCutAfterKeep in HM. destruct HM as [l [_ [_ HP]]].
    apply (ppc_bound_value__cfp_step_12 a del change p i l i cutAfterKeep); assumption.
  - intros Hne. pose proof (dpvalue_mem__cfp_step_12 _ _ HB Hne) as HM.
    unfold DPAfter in HM. destruct HM as [l [r [_ HP]]].
    apply (ppc_bound_value__cfp_step_12 a del change p i l r after); assumption.
Qed.
Lemma dpcutfresh_val__cfp_step_12 : forall (a : list Z) (del change p i v : Z),
  0 <= i -> i <= Zlength a -> i * del < INF ->
  DPValue (DPCutFresh a del change p i) v ->
  v = i * del.
Proof.
  intros a del change p i v Hi0 Hi Hlt HD.
  assert (Hmem : DPCutFresh a del change p i (i * del))
    by (apply dpcutfresh_char__cfp_step_12; [lia | lia | reflexivity]).
  pose proof (dpvalue_lb__cfp_step_12 _ _ _ HD Hmem) as Hle.
  assert (Hne : v <> INF) by lia.
  pose proof (dpvalue_mem__cfp_step_12 _ _ HD Hne) as HM.
  apply (dpcutfresh_char__cfp_step_12 a del change p i v); [lia | lia | exact HM].
Qed.
Lemma cfp_state_step__cfp_step_12 :
  forall (a : list Z) (del change p i keep cutFresh cutAfterKeep after cost : Z),
  1 <= i -> i < Zlength a -> Zlength a <= 1000000 ->
  2 <= p -> 0 <= del -> del <= 1000000000 -> 0 <= change ->
  cost = ElemCost change p (Znth i a 0) ->
  cost <> INF ->
  CostForPrimeState a del change p i keep cutFresh cutAfterKeep after ->
  keep + cost <= INF ->
  cutFresh + del <= INF ->
  Z.min keep cutAfterKeep + del <= INF ->
  Z.min (Z.min cutFresh cutAfterKeep) after + cost <= INF ->
  CostForPrimeState a del change p (i + 1) (keep + cost) (cutFresh + del)
    (Z.min keep cutAfterKeep + del)
    (Z.min (Z.min cutFresh cutAfterKeep) after + cost).
Proof.
  intros a del change p i keep cutFresh cutAfterKeep after cost
         Hi1 Hi Ha Hp Hd0 Hd1 Hch Hcost Hcne HS Hub1 Hub2 Hub3 Hub4.
  destruct HS as [HK [HF [HA HB]]].
  subst cost.
  assert (Hcost0 : 0 <= ElemCost change p (Znth i a 0))
    by (apply elemcost_nonneg__cfp_step_12; lia).
  assert (HmulF : (i + 1) * del = i * del + del) by ring.
  assert (HiINF : i * del < INF) by (unfold INF; nia).
  assert (Hi1INF : (i + 1) * del <= INF) by (unfold INF; nia).
  assert (HcfVal : cutFresh = i * del)
    by (apply (dpcutfresh_val__cfp_step_12 a del change p i); [lia | lia | exact HiINF | exact HF]).
  unfold CostForPrimeState. split; [| split; [| split]].
  - apply dpvalue_intro__cfp_step_12; [ | | exact Hub1].
    + intros c Hc.
      destruct (dpkeep_bwd__cfp_step_12 a del change p i c ltac:(lia) ltac:(lia) Hp Hch Hc)
        as [c0 [Hc0 Hle]].
      pose proof (dpvalue_lb__cfp_step_12 _ _ _ HK Hc0). lia.
    + intros Hne.
      assert (Hkne : keep <> INF) by lia.
      apply dpkeep_fwd__cfp_step_12; try lia; try assumption.
      apply (dpvalue_mem__cfp_step_12 _ _ HK Hkne).
  - rewrite HcfVal. rewrite <- HmulF.
    apply dpvalue_intro__cfp_step_12.
    + intros c Hc.
      pose proof (dpcutfresh_char__cfp_step_12 a del change p (i + 1) c ltac:(lia) ltac:(lia))
        as [Hch1 _].
      specialize (Hch1 Hc). lia.
    + intros _.
      apply (dpcutfresh_char__cfp_step_12 a del change p (i + 1) ((i + 1) * del));
        [lia | lia | reflexivity].
    + exact Hi1INF.
  - assert (Hmem : Z.min keep cutAfterKeep <> INF ->
                   DPCutAfterKeep a del change p (i + 1) (Z.min keep cutAfterKeep + del)).
    { intros Hmne.
      destruct (Z.le_ge_cases keep cutAfterKeep) as [Hle | Hge].
      - rewrite (Z.min_l _ _ Hle) in *.
        apply dpcak_fwd_keep__cfp_step_12; [lia | lia |].
        apply (dpvalue_mem__cfp_step_12 _ _ HK Hmne).
      - rewrite (Z.min_r _ _ Hge) in *.
        apply dpcak_fwd_cak__cfp_step_12; [lia | lia |].
        apply (dpvalue_mem__cfp_step_12 _ _ HA Hmne). }
    apply dpvalue_intro__cfp_step_12; [ | | exact Hub3].
    + intros c Hc.
      destruct (dpcak_bwd__cfp_step_12 a del change p i c ltac:(lia) Hc)
        as [c0 [[Hcak | [_ Hkp]] Heq]].
      * pose proof (dpvalue_lb__cfp_step_12 _ _ _ HA Hcak).
        pose proof (Z.le_min_r keep cutAfterKeep). lia.
      * pose proof (dpvalue_lb__cfp_step_12 _ _ _ HK Hkp).
        pose proof (Z.le_min_l keep cutAfterKeep). lia.
    + intros Hne. apply Hmem. lia.
  - assert (Hmem : Z.min (Z.min cutFresh cutAfterKeep) after <> INF ->
                   DPAfter a del change p (i + 1)
                     (Z.min (Z.min cutFresh cutAfterKeep) after
                      + ElemCost change p (Znth i a 0))).
    { intros Hmne.
      destruct (Z.le_ge_cases (Z.min cutFresh cutAfterKeep) after) as [Hle | Hge].
      - rewrite (Z.min_l _ _ Hle) in *.
        destruct (Z.le_ge_cases cutFresh cutAfterKeep) as [Hle2 | Hge2].
        + rewrite (Z.min_l _ _ Hle2) in *.
          apply dpafter_fwd_cutfresh__cfp_step_12; try lia; try assumption.
          apply (dpvalue_mem__cfp_step_12 _ _ HF Hmne).
        + rewrite (Z.min_r _ _ Hge2) in *.
          apply dpafter_fwd_cak__cfp_step_12; try lia; try assumption.
          apply (dpvalue_mem__cfp_step_12 _ _ HA Hmne).
      - rewrite (Z.min_r _ _ Hge) in *.
        apply dpafter_fwd_after__cfp_step_12; try lia; try assumption.
        apply (dpvalue_mem__cfp_step_12 _ _ HB Hmne). }
    apply dpvalue_intro__cfp_step_12; [ | | exact Hub4].
    + intros c Hc.
      destruct (dpafter_bwd__cfp_step_12 a del change p i c ltac:(lia) ltac:(lia) Hp Hch Hc)
        as [c0 [[H1 | [H2 | [H3 | H4]]] Hle]].
      * pose proof (dpvalue_lb__cfp_step_12 _ _ _ HF H1).
        pose proof (Z.le_min_l cutFresh cutAfterKeep).
        pose proof (Z.le_min_l (Z.min cutFresh cutAfterKeep) after). lia.
      * pose proof (dpvalue_lb__cfp_step_12 _ _ _ HA H2).
        pose proof (Z.le_min_r cutFresh cutAfterKeep).
        pose proof (Z.le_min_l (Z.min cutFresh cutAfterKeep) after). lia.
      * pose proof (dpvalue_lb__cfp_step_12 _ _ _ HB H3).
        pose proof (Z.le_min_r (Z.min cutFresh cutAfterKeep) after). lia.
      * pose proof (dpkeep_sub_dpafter__cfp_step_12 a del change p i c0 ltac:(lia) H4) as H4'.
        pose proof (dpvalue_lb__cfp_step_12 _ _ _ HB H4').
        pose proof (Z.le_min_r (Z.min cutFresh cutAfterKeep) after). lia.
    + intros Hne. apply Hmem. lia.
Qed.
Lemma cfp_cak_zero_inf__cfp_step_12 :
  forall (a : list Z) (del change p v : Z),
  DPValue (DPCutAfterKeep a del change p 0) v -> v = 4611686018427387904.
Proof.
  intros a del change p v HD.
  destruct (Z.eq_dec v INF) as [He | Hne]; [exact He |].
  pose proof (dpvalue_mem__cfp_step_12 _ _ HD Hne) as HM.
  exfalso. exact (dpcak_zero_empty__cfp_step_12 _ _ _ _ _ HM).
Qed.
Lemma candidate_coverage_init__solver_candidate_coverage :
  forall (x y : Z), CandidateCoverage x y (-1) nil.
Proof.
  intros x y. unfold CandidateCoverage. split.
  - apply Forall_nil.
  - intros q e Hq He1 He2 Hd. lia.
Qed.
Lemma candidate_coverage_Znth__solver_candidate_coverage :
  forall (x y d : Z) (ps : list Z) (j : Z),
    CandidateCoverage x y d ps ->
    0 <= j < Zlength ps ->
    2 <= Znth j ps 0.
Proof.
  intros x y d ps j HC Hj. destruct HC as [HF _].
  apply (Forall_Znth_Zlength (fun q => 2 <= q) ps 0 j HF Hj).
Qed.
Lemma candidate_coverage_extend__solver_candidate_coverage :
  forall (x y d : Z) (ps fs fs2 : list Z),
    CandidateCoverage x y d ps ->
    AddFactorsResult (x + d) fs ->
    AddFactorsResult (y + d) fs2 ->
    CandidateCoverage x y (d + 1) ((ps ++ fs) ++ fs2).
Proof.
  intros x y d ps fs fs2 HC HA1 HA2.
  destruct HC as [HF HIn].
  destruct HA1 as [HS1 [HK1 _]].
  destruct HA2 as [HS2 [HK2 _]].
  split.
  - apply Forall_app. split.
    + apply Forall_app. split.
      * exact HF.
      * eapply Forall_impl; [| exact HS1]. intros a Ha. exact (proj1 Ha).
    + eapply Forall_impl; [| exact HS2]. intros a Ha. exact (proj1 Ha).
  - intros q e Hq He1 He2 Hdiv.
    assert (e < d \/ e = d) as [Hlt | Heq] by lia.
    + apply in_or_app. left. apply in_or_app. left.
      apply (HIn q e Hq He1 Hlt Hdiv).
    + subst e. destruct Hdiv as [Hx | Hy].
      * apply in_or_app. left. apply in_or_app. right.
        apply (HK1 q Hq Hx).
      * apply in_or_app. right. apply (HK2 q Hq Hy).
Qed.
Lemma best_prefix_cost_empty__solver_candidate_coverage :
  forall (a : list Z) (del change : Z) (ps : list Z),
    BestPrefixCost a del change ps 0 4611686018427387904.
Proof.
  intros a del change ps.
  unfold BestPrefixCost, DPValue, min_value_of_subset_with_default.
  right. split.
  - intros c Hc. sets_unfold in Hc. destruct Hc as [j [Hj _]]. lia.
  - reflexivity.
Qed.
Lemma dp_value_unique__solver_best_prefix :
  forall (S : Z -> Prop) (v1 v2 : Z),
    DPValue S v1 -> DPValue S v2 -> v1 = v2.
Proof.
  unfold DPValue. intros S v1 v2 H1 H2.
  eapply (min_default_unique Z.le (fun x : Z => x) S INF); eassumption.
Qed.
Lemma dp_value_extend_singleton__solver_best_prefix :
  forall (S T : Z -> Prop) (v w r : Z),
    DPValue S v ->
    (forall c, T c <-> S c \/ c = w) ->
    r = Z.min v w ->
    DPValue T r.
Proof.
  intros S T v w r HS HT Hr.
  unfold DPValue in *.
  assert (Hmin : r = le_min Z.le v w).
  { unfold le_min. destruct (@le_total Z Z.le Zle_TotalOrder v w); lia. }
  rewrite Hmin.
  eapply (min_default_union_1_right Z.le v w w (fun x : Z => x) S T INF).
  - exact HS.
  - reflexivity.
  - intros b. rewrite HT. split; intros [HH | HH]; solve [ left; assumption | right; lia ].
Qed.
Lemma best_prefix_index_set_step__solver_best_prefix :
  forall (a : list Z) (del change : Z) (ps : list Z) (i retval : Z),
    0 <= i ->
    CostForPrime a del change (Znth i ps 0) retval ->
    forall c,
      (exists j, 0 <= j < i + 1 /\ CostForPrime a del change (Znth j ps 0) c)
      <-> (exists j, 0 <= j < i /\ CostForPrime a del change (Znth j ps 0) c) \/ c = retval.
Proof.
  intros a del change ps i retval Hi Hret c. split.
  - intros [j [Hj Hc]].
    destruct (Z.eq_dec j i).
    + subst j. right.
      unfold CostForPrime in *.
      eapply dp_value_unique__solver_best_prefix; eassumption.
    + left. exists j. split; [lia | assumption].
  - intros [[j [Hj Hc]] | Hc].
    + exists j. split; [lia | assumption].
    + subst c. exists i. split; [lia | assumption].
Qed.
Lemma best_prefix_cost_step__solver_best_prefix :
  forall (a : list Z) (del change : Z) (ps : list Z) (i best retval r : Z),
    0 <= i ->
    BestPrefixCost a del change ps i best ->
    CostForPrime a del change (Znth i ps 0) retval ->
    r = Z.min best retval ->
    BestPrefixCost a del change ps (i + 1) r.
Proof.
  intros a del change ps i best retval r Hi Hbest Hret Hr.
  unfold BestPrefixCost in *.
  eapply (dp_value_extend_singleton__solver_best_prefix _ _ best retval r).
  - exact Hbest.
  - intros c. apply best_prefix_index_set_step__solver_best_prefix; assumption.
  - exact Hr.
Qed.
Lemma set_card_empty__solver_spec_final :
  forall (A : Type) (P : A -> Prop) (HF : Finite P),
    (forall x, ~ P x) -> @set_card A P HF = 0.
Proof.
  intros A P HF Hemp.
  unfold set_card, sum.
  destruct (@enum A P HF) as [|x xs] eqn:E; [reflexivity |].
  exfalso. apply (Hemp x).
  apply (proj2 (@enum_ok A P HF x)).
  rewrite E. left. reflexivity.
Qed.
Lemma set_card_nonneg__solver_spec_final :
  forall (A : Type) (P : A -> Prop) (HF : Finite P),
    0 <= @set_card A P HF.
Proof.
  intros A P HF.
  unfold set_card.
  apply sum_nonneg. intros. lia.
Qed.
Lemma Count_nonneg__solver_spec_final :
  forall x xs, 0 <= Count x xs.
Proof.
  intros. unfold Count. apply set_card_nonneg__solver_spec_final.
Qed.
Lemma Count_zero_singleton__solver_spec_final :
  forall x, x <> 0 -> Count x [0] = 0.
Proof.
  intros x Hx. unfold Count.
  apply set_card_empty__solver_spec_final.
  intros i [Hr Hv].
  rewrite Zlength_cons, Zlength_nil in Hr.
  assert (i = 0) by lia. subst i.
  unfold Znth in Hv. simpl in Hv. lia.
Qed.
Lemma ChangeCost_nonneg__solver_spec_final :
  forall del change l r delta,
    0 <= del -> 0 <= change -> l <= r ->
    0 <= ChangeCost del change l r delta.
Proof.
  intros. unfold ChangeCost.
  pose proof (Count_nonneg__solver_spec_final (-1) delta).
  pose proof (Count_nonneg__solver_spec_final 1 delta).
  nia.
Qed.
Lemma ChangeCost_single_zero__solver_spec_final :
  forall del change l r,
    ChangeCost del change l r [0] = (r - l) * del.
Proof.
  intros. unfold ChangeCost.
  rewrite !Count_zero_singleton__solver_spec_final by lia.
  lia.
Qed.
Lemma fold_gcd_divides_elem__solver_spec_final :
  forall (l : list Z) (x : Z), In x l -> Z.divide (fold_right Z.gcd 0 l) x.
Proof.
  induction l as [|a l IH]; intros x Hin; [inversion Hin |].
  simpl in *. destruct Hin as [<- | Hin].
  - apply Z.gcd_divide_l.
  - apply Z.divide_trans with (fold_right Z.gcd 0 l).
    + apply Z.gcd_divide_r.
    + apply IH; auto.
Qed.
Lemma fold_gcd_greatest__solver_spec_final :
  forall (l : list Z) (p : Z),
    (forall x, In x l -> Z.divide p x) -> Z.divide p (fold_right Z.gcd 0 l).
Proof.
  induction l as [|a l IH]; intros p H; simpl.
  - exists 0. lia.
  - apply Z.gcd_greatest.
    + apply H. left. reflexivity.
    + apply IH. intros. apply H. right. auto.
Qed.
Lemma exists_prime_divisor__solver_spec_final :
  forall n, 1 < n -> exists q, prime q /\ Z.divide q n.
Proof.
  assert (Haux : forall n, 0 <= n -> 1 < n -> exists q, prime q /\ Z.divide q n).
  { intros n Hn0. pattern n. apply Z_lt_induction; [| exact Hn0].
    clear n Hn0. intros n IH Hn.
    destruct (prime_dec n) as [Hp | Hnp].
    - exists n. split; auto. exists 1. lia.
    - destruct (not_prime_divide n Hn Hnp) as [m [Hm Hdiv]].
      destruct (IH m ltac:(lia) ltac:(lia)) as [q [Hq Hqm]].
      exists q. split; auto. apply Z.divide_trans with m; auto. }
  intros n Hn. apply Haux; lia.
Qed.
Lemma In_to_Znth__solver_spec_final :
  forall (l : list Z) (x : Z),
    In x l -> exists j, 0 <= j < Zlength l /\ Znth j l 0 = x.
Proof.
  intros l x Hin.
  apply (In_nth l x 0) in Hin.
  destruct Hin as [k [Hk Hnth]].
  exists (Z.of_nat k). split.
  - rewrite Zlength_correct. lia.
  - unfold Znth. rewrite Nat2Z.id. auto.
Qed.
Lemma Znth_In__solver_spec_final :
  forall (l : list Z) (j : Z),
    0 <= j < Zlength l -> In (Znth j l 0) l.
Proof.
  intros l j Hj. unfold Znth.
  apply nth_In. rewrite Zlength_correct in Hj. lia.
Qed.
Lemma Adjusted_Zlength__solver_spec_final :
  forall kept delta result,
    Adjusted kept delta result -> Zlength result = Zlength kept.
Proof.
  intros kept delta result [Hlen [_ Hres]].
  subst result.
  rewrite !Zlength_correct in *.
  rewrite length_map, length_combine. lia.
Qed.
Lemma Adjusted_Znth__solver_spec_final :
  forall kept delta result m,
    Adjusted kept delta result ->
    0 <= m < Zlength kept ->
    Znth m result 0 = Znth m kept 0 + Znth m delta 0.
Proof.
  intros kept delta result m [Hlen [_ Hres]] Hm.
  subst result.
  assert (Hl : length kept = length delta)
    by (rewrite !Zlength_correct in Hlen; lia).
  unfold Znth.
  pose proof (map_nth (fun q : Z * Z => fst q + snd q)
                (combine kept delta) (0, 0) (Z.to_nat m)) as Hmap.
  simpl in Hmap. rewrite Hmap.
  rewrite combine_nth by exact Hl.
  reflexivity.
Qed.
Lemma fold_gcd_nonneg__solver_spec_final :
  forall l : list Z, 0 <= fold_right Z.gcd 0 l.
Proof.
  induction l as [|a l IH]; simpl; [lia | apply Z.gcd_nonneg].
Qed.
Lemma Zlength_kept__solver_spec_final :
  forall (a : list Z) l r,
    0 <= l <= r -> r <= Zlength a ->
    Zlength (sublist 0 l a ++ sublist r (Zlength a) a) = l + (Zlength a - r).
Proof.
  intros a l r Hlr Hr.
  rewrite Zlength_app.
  rewrite (Zlength_sublist 0 l a) by lia.
  rewrite (Zlength_sublist r (Zlength a) a) by lia.
  lia.
Qed.
Lemma Znth_kept__solver_spec_final :
  forall (a : list Z) l r m,
    0 <= l <= r -> r <= Zlength a ->
    0 <= m < l + (Zlength a - r) ->
    exists k, 0 <= k < Zlength a /\
      Znth m (sublist 0 l a ++ sublist r (Zlength a) a) 0 = Znth k a 0.
Proof.
  intros a l r m Hlr Hr Hm.
  assert (Hs1 : Zlength (sublist 0 l a) = l) by (rewrite Zlength_sublist by lia; lia).
  destruct (Z_lt_ge_dec m l) as [Hlt | Hge].
  - exists m. split; [lia |].
    rewrite app_Znth1 by lia.
    rewrite Znth_sublist0 by lia. reflexivity.
  - exists (r + (m - l)). split; [lia |].
    rewrite app_Znth2 by lia.
    rewrite Hs1.
    rewrite Znth_sublist_lt by lia. reflexivity.
Qed.
Lemma delta_entry__solver_spec_final :
  forall delta m,
    Forall (fun d => d = (-1) \/ d = 0 \/ d = 1) delta ->
    0 <= m < Zlength delta ->
    -1 <= Znth m delta 0 <= 1.
Proof.
  intros delta m Hf Hm.
  rewrite Forall_forall in Hf.
  specialize (Hf (Znth m delta 0) (Znth_In__solver_spec_final delta m Hm)).
  lia.
Qed.
Lemma plan_gives_gcd_change__solver_spec_final :
  forall a del change p c,
    2 <= p ->
    (forall j, 0 <= j < Zlength a -> 2 <= Znth j a 0) ->
    PFeasiblePlan a del change p c ->
    GCDChange a del change c.
Proof.
  intros a del change p c Hp Ha
    [l [r [Hrl [Hl [Hlr [Hr [Hi [delta [result [Hadj [Hdvd Hc]]]]]]]]]]].
  remember (sublist 0 l a ++ sublist r (Zlength a) a) as kept eqn:Hkept.
  assert (Hklen : Zlength kept = l + (Zlength a - r))
    by (subst kept; apply Zlength_kept__solver_spec_final; lia).
  assert (Hrlen : Zlength result = Zlength kept)
    by (apply (Adjusted_Zlength__solver_spec_final kept delta result); auto).
  assert (Hdlen : Zlength delta = Zlength kept) by (destruct Hadj as [? _]; auto).
  assert (Hpos : 1 <= Zlength result) by lia.
  assert (Hentry : forall m, 0 <= m < Zlength result -> 1 <= Znth m result 0).
  { intros m Hm.
    rewrite (Adjusted_Znth__solver_spec_final kept delta result m Hadj) by lia.
    destruct (Znth_kept__solver_spec_final a l r m ltac:(lia) ltac:(lia) ltac:(lia))
      as [k [Hk Hkv]].
    rewrite <- Hkept in Hkv. rewrite Hkv.
    pose proof (Ha k Hk).
    pose proof (delta_entry__solver_spec_final delta m (proj1 (proj2 Hadj)) ltac:(lia)).
    lia. }
  remember (fold_right Z.gcd 0 result) as g eqn:Hg.
  assert (Hg0 : 0 <= g) by (subst g; apply fold_gcd_nonneg__solver_spec_final).
  assert (Hgd : Z.divide g (Znth 0 result 0)).
  { subst g. apply fold_gcd_divides_elem__solver_spec_final.
    apply Znth_In__solver_spec_final. lia. }
  assert (Hgt0 : 0 < g).
  { destruct (Z.eq_dec g 0) as [Hz | Hz]; [| lia].
    exfalso. subst g. destruct Hgd as [k Hk].
    pose proof (Hentry 0 ltac:(lia)). lia. }
  assert (Hpg : Z.divide p g).
  { subst g. apply fold_gcd_greatest__solver_spec_final.
    rewrite Forall_forall in Hdvd. auto. }
  assert (Hgp : p <= g) by (apply Z.divide_pos_le; auto).
  exists l, r, kept, delta, result.
  split; [| split; [assumption | split; [| assumption]]].
  - unfold KeptAfterRemoval. repeat split; try lia. auto.
  - exists g. split; [lia |].
    unfold IsPositiveGcd. split; [lia |]. split; [| auto].
    intro Heq. rewrite Heq, Zlength_nil in Hpos. lia.
Qed.
Lemma sublist_last__solver_spec_final :
  forall (a : list Z), 1 <= Zlength a ->
    sublist (Zlength a - 1) (Zlength a) a = [Znth (Zlength a - 1) a 0].
Proof.
  intros a Ha.
  pose proof (sublist_single 0 (Zlength a - 1) a ltac:(lia)) as H.
  replace (Zlength a - 1 + 1) with (Zlength a) in H by lia.
  exact H.
Qed.
Lemma gcd_change_nonempty__solver_spec_final :
  forall a del change,
    1 <= Zlength a ->
    (forall j, 0 <= j < Zlength a -> 2 <= Znth j a 0) ->
    GCDChange a del change ((Zlength a - 1) * del).
Proof.
  intros a del change Hn Ha.
  pose proof (Ha (Zlength a - 1) ltac:(lia)) as Hv.
  exists 0, (Zlength a - 1), [Znth (Zlength a - 1) a 0], [0],
         [Znth (Zlength a - 1) a 0].
  split; [| split; [| split]].
  - unfold KeptAfterRemoval. repeat split; try lia.
    rewrite Zsublist_nil by lia. simpl.
    rewrite sublist_last__solver_spec_final by lia. reflexivity.
  - unfold Adjusted. split; [reflexivity | split].
    + constructor; [right; left; reflexivity | constructor].
    + simpl. f_equal. lia.
  - exists (Znth (Zlength a - 1) a 0). split; [lia |].
    unfold IsPositiveGcd. split; [lia |]. split.
    + intro Hc. discriminate Hc.
    + simpl. rewrite Z.gcd_0_r. rewrite Z.abs_eq by lia. reflexivity.
  - rewrite ChangeCost_single_zero__solver_spec_final. lia.
Qed.
Lemma gcd_change_gives_candidate_plan__solver_spec_final :
  forall a del change c,
    1 <= Zlength a ->
    GCDChange a del change c ->
    exists q e, prime q /\ -1 <= e /\ e < 2 /\
      (Z.divide q (Znth 0 a 0 + e) \/
       Z.divide q (Znth (Zlength a - 1) a 0 + e)) /\
      PFeasiblePlan a del change q c.
Proof.
  intros a del change c Hn
    [l [r [kept [delta [result [Hkeep [Hadj [[g [Hg1 [Hgpos [Hrnil Hgeq]]]] Hc]]]]]]]].
  destruct Hkeep as [Hl [Hr [Hrl Hkept]]].
  destruct (exists_prime_divisor__solver_spec_final g ltac:(lia)) as [q [Hq Hqg]].
  assert (Hqres : forall x, In x result -> Z.divide q x).
  { intros x Hx. apply Z.divide_trans with g; auto.
    rewrite Hgeq. apply fold_gcd_divides_elem__solver_spec_final; auto. }
  assert (Hklen : Zlength kept = l + (Zlength a - r))
    by (rewrite Hkept; apply Zlength_kept__solver_spec_final; lia).
  assert (Hrlen : Zlength result = Zlength kept)
    by (apply (Adjusted_Zlength__solver_spec_final kept delta result); auto).
  assert (Hdlen : Zlength delta = Zlength kept) by (destruct Hadj as [? _]; auto).
  assert (Hs1 : Zlength (sublist 0 l a) = l)
    by (rewrite Zlength_sublist by lia; lia).
  assert (Hfeas : PFeasiblePlan a del change q c).
  { exists l, r. split; [lia |].
    unfold PartialPlanCost. repeat split; try lia.
    exists delta, result. split; [rewrite <- Hkept; auto |].
    split; [rewrite Forall_forall; auto | auto]. }
  destruct (Z_lt_ge_dec 0 l) as [Hl0 | Hl0].
  - exists q, (Znth 0 delta 0).
    assert (Hk0 : Znth 0 kept 0 = Znth 0 a 0).
    { rewrite Hkept. rewrite app_Znth1 by lia.
      rewrite Znth_sublist0 by lia. reflexivity. }
    pose proof (delta_entry__solver_spec_final delta 0
                  (proj1 (proj2 Hadj)) ltac:(lia)) as Hde.
    split; [auto |]. split; [lia |]. split; [lia |]. split; [| auto].
    left.
    rewrite <- Hk0.
    rewrite <- (Adjusted_Znth__solver_spec_final kept delta result 0 Hadj ltac:(lia)).
    apply Hqres. apply Znth_In__solver_spec_final. lia.
  - assert (Hl00 : l = 0) by lia. subst l.
    exists q, (Znth (Zlength kept - 1) delta 0).
    assert (Hk0 : Znth (Zlength kept - 1) kept 0 = Znth (Zlength a - 1) a 0).
    { rewrite Hkept at 2. rewrite app_Znth2 by lia.
      rewrite Hs1.
      rewrite Znth_sublist_lt by lia. f_equal. lia. }
    pose proof (delta_entry__solver_spec_final delta (Zlength kept - 1)
                  (proj1 (proj2 Hadj)) ltac:(lia)) as Hde.
    split; [auto |]. split; [lia |]. split; [lia |]. split; [| auto].
    right.
    rewrite <- Hk0.
    rewrite <- (Adjusted_Znth__solver_spec_final kept delta result
                  (Zlength kept - 1) Hadj ltac:(lia)).
    apply Hqres. apply Znth_In__solver_spec_final. lia.
Qed.
Lemma PFeasiblePlan_nonneg__solver_spec_final :
  forall a del change p c,
    0 <= del -> 0 <= change ->
    PFeasiblePlan a del change p c -> 0 <= c.
Proof.
  intros a del change p c Hd Hch
    [l [r [Hrl [Hl [Hlr [Hr [Hi [delta [result [Hadj [Hdvd Hc]]]]]]]]]]].
  subst c. apply ChangeCost_nonneg__solver_spec_final; lia.
Qed.
Lemma min_over_set__solver_spec_final :
  forall (X : Z -> Prop) v,
    X v -> 0 <= v -> (forall z, X z -> 0 <= z) ->
    exists m, X m /\ 0 <= m <= v /\ (forall z, X z -> m <= z).
Proof.
  intros X v Hv Hv0 Hnn.
  destruct (min_n_in_range X v Hv0 ltac:(exists v; split; [lia | exact Hv])) as [m [Hm [Hmr Hmin]]].
  exists m. split; [auto | split; [auto |]].
  intros z Hz. destruct (Z_le_gt_dec z v) as [Hle | Hgt].
  - apply Hmin; [split; [apply Hnn; auto | auto] | auto].
  - lia.
Qed.
Lemma dp_value_intro__solver_spec_final :
  forall (X : Z -> Prop) m,
    X m -> (forall z, X z -> m <= z) -> m <= INF -> DPValue X m.
Proof.
  intros X m Hm Hmin Hle.
  unfold DPValue, min_value_of_subset_with_default.
  left. split; [| exact Hle].
  unfold min_value_of_subset, min_object_of_subset.
  exists m. split; [| reflexivity].
  sets_unfold. split; [exact Hm | exact Hmin].
Qed.
Lemma dp_value_le__solver_spec_final :
  forall (X : Z -> Prop) m z, DPValue X m -> X z -> m <= z.
Proof.
  intros X m z Hdp Hz.
  unfold DPValue, min_value_of_subset_with_default in Hdp.
  destruct Hdp as [[[b [[Hb Hmin] Heq]] _] | [Hall Heq]].
  - sets_unfold in Hb. sets_unfold in Hmin. subst b. apply Hmin. exact Hz.
  - sets_unfold in Hall. subst m. apply Hall. exact Hz.
Qed.
Lemma dp_value_mem__solver_spec_final :
  forall (X : Z -> Prop) m, DPValue X m -> m < INF -> X m.
Proof.
  intros X m Hdp Hlt.
  unfold DPValue, min_value_of_subset_with_default in Hdp.
  destruct Hdp as [[[b [[Hb Hmin] Heq]] _] | [Hall Heq]].
  - sets_unfold in Hb. subst b. exact Hb.
  - unfold INF in *. lia.
Qed.
Lemma best_prefix_gives_spec__solver_spec_final :
  forall a del change ps best,
    0 <= del <= 1000000000 ->
    0 <= change <= 1000000000 ->
    1 <= Zlength a <= 1000000 ->
    (forall j, 0 <= j < Zlength a -> 2 <= Znth j a 0) ->
    (forall j, 0 <= j < Zlength ps -> 2 <= Znth j ps 0) ->
    CandidateCoverage (Znth 0 a 0) (Znth (Zlength a - 1) a 0) 2 ps ->
    BestPrefixCost a del change ps (Zlength ps) best ->
    Spec del change a best.
Proof.
  intros a del change ps best Hdel Hch Hn Ha Hps Hcov Hbp.
  destruct Hcov as [Hcov2 Hcov].
  unfold BestPrefixCost in Hbp.
  assert (Hkey : forall c, GCDChange a del change c -> c <= INF ->
            exists mu, (exists j, 0 <= j < Zlength ps /\
                          CostForPrime a del change (Znth j ps 0) mu) /\ mu <= c).
  { intros c Hc Hcinf.
    destruct (gcd_change_gives_candidate_plan__solver_spec_final a del change c
                ltac:(lia) Hc) as [q [e [Hq [He1 [He2 [Hdiv Hfeas]]]]]].
    assert (HIn : In q ps) by (apply (Hcov q e); auto).
    destruct (In_to_Znth__solver_spec_final ps q HIn) as [j [Hj Hjq]].
    assert (Hcnn : 0 <= c)
      by (apply (PFeasiblePlan_nonneg__solver_spec_final a del change q c);
          [lia | lia | exact Hfeas]).
    destruct (min_over_set__solver_spec_final (PFeasiblePlan a del change q) c
                Hfeas Hcnn
                ltac:(intros z Hz;
                      apply (PFeasiblePlan_nonneg__solver_spec_final a del change q z);
                      [lia | lia | exact Hz]))
      as [mu [Hmu [Hmur Hmumin]]].
    exists mu. split; [| lia].
    exists j. split; [lia |].
    unfold CostForPrime. rewrite Hjq.
    apply dp_value_intro__solver_spec_final; [exact Hmu | exact Hmumin | lia]. }
  assert (Hc0G : GCDChange a del change ((Zlength a - 1) * del))
    by (apply gcd_change_nonempty__solver_spec_final; [lia | exact Ha]).
  assert (Hc0b : 0 <= (Zlength a - 1) * del <= 1000000000000000) by nia.
  destruct (Hkey ((Zlength a - 1) * del) Hc0G ltac:(unfold INF; lia))
    as [mu [HmuS Hmuc0]].
  assert (Hbest_le : best <= mu)
    by (apply (dp_value_le__solver_spec_final _ best mu Hbp HmuS)).
  assert (Hbest_lt : best < INF) by (unfold INF in *; lia).
  assert (HbestS : exists j, 0 <= j < Zlength ps /\
                     CostForPrime a del change (Znth j ps 0) best)
    by (apply (dp_value_mem__solver_spec_final _ best Hbp Hbest_lt)).
  destruct HbestS as [j1 [Hj1 Hcfp]].
  assert (Hp1 : 2 <= Znth j1 ps 0) by (apply Hps; lia).
  unfold CostForPrime in Hcfp.
  assert (HbestPlan : PFeasiblePlan a del change (Znth j1 ps 0) best)
    by (apply (dp_value_mem__solver_spec_final _ best Hcfp Hbest_lt)).
  assert (HbestG : GCDChange a del change best)
    by (apply (plan_gives_gcd_change__solver_spec_final a del change
                 (Znth j1 ps 0) best Hp1 Ha HbestPlan)).
  assert (Hlb : forall c, GCDChange a del change c -> best <= c).
  { intros c Hc.
    destruct (Z_le_gt_dec c INF) as [Hle | Hgt].
    - destruct (Hkey c Hc Hle) as [mu' [Hmu'S Hmu'c]].
      assert (best <= mu')
        by (apply (dp_value_le__solver_spec_final _ best mu' Hbp Hmu'S)).
      lia.
    - lia. }
  unfold Spec, min_value_of_subset, min_object_of_subset.
  exists best. split; [| reflexivity].
  sets_unfold. split; [exact HbestG | exact Hlb].
Qed.
