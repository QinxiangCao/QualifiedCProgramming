Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import SimpleC.EE.LLM_bench.Codeforces.SpecHelpers.
Require Import Coq.ZArith.Znumtheory.

Import ListNotations.
Local Open Scope Z_scope.

Definition SquareFree (x : Z) : Prop :=
  exists ps, ps <> [] /\ NoDup ps /\ Forall prime ps /\ x = fold_right Z.mul 1 ps.

(* Per-case signature: solve_case(n:Z)->Z. Output maximizes sum(ai*pi) over
   exactly the statement's square-free-base factorizations. *)
Definition ValidFactorization (n value : Z) : Prop :=
  exists ap : list (Z*Z), ap<>[] /\
    Forall (fun q => SquareFree (fst q) /\ snd q>0) ap /\
    n = (fold_right Z.mul 1) (map (fun q => Z.pow (fst q) (snd q)) ap) /\
    value = (fold_right Z.add 0) (map (fun q => fst q*snd q) ap).
Definition Pre (n : Z) : Prop :=
  (* Stated explicitly in the P019 solver Require, which therefore omits the
     Pre(...) call: 2 <= n <= 1000000000. *)
  True.
Definition Spec (n out : Z) : Prop := max_value_of_subset Z.le (ValidFactorization n) (fun x => x) out.

(* A mathematical prime/exponent profile.  The definitions below expose the
   three stable states used by the implementation: a partially extracted
   prime factorisation, the maximum exponent, and the sum of square-free
   exponent layers.  They describe the number-theoretic objects rather than
   replaying the C control flow. *)
Definition FactorPower (ps es : list Z) : Z :=
  fold_right Z.mul 1
    (map (fun i => Z.pow (Znth i ps 1) (Znth i es 0))
         (Zrange 0 (Zlength ps))).

Definition PrimeExponentProfile (ps es : list Z) : Prop :=
  Zlength ps = Zlength es /\
  NoDup ps /\
  Forall prime ps /\
  (forall i, 0 <= i < Zlength es -> 1 <= Znth i es 0 <= 30).

Definition FactorScan
    (orig rem next : Z) (ps es : list Z) : Prop :=
  2 <= orig <= 1000000000 /\
  1 <= rem <= orig /\
  2 <= next <= orig /\
  Zlength ps <= 29 /\
  PrimeExponentProfile ps es /\
  Forall (fun p => 2 <= p < next) ps /\
  orig = rem * FactorPower ps es /\
  (forall p, prime p -> 2 <= p < next -> ~ (p | rem)).

Definition FactorExtract
    (orig rem d : Z) (ps es : list Z) (e : Z) : Prop :=
  2 <= orig <= 1000000000 /\
  1 <= rem <= orig /\
  2 <= d <= orig /\
  Zlength ps <= 29 /\
  PrimeExponentProfile ps es /\
  Forall (fun p => 2 <= p < d) ps /\
  prime d /\
  0 <= e <= 30 /\
  orig = rem * Z.pow d e * FactorPower ps es /\
  (forall p, prime p -> 2 <= p < d -> ~ (p | rem)) /\
  (e = 0 -> (d | rem)).

Definition PrimeFactorization (orig : Z) (ps es : list Z) : Prop :=
  2 <= orig <= 1000000000 /\
  Zlength ps <= 30 /\
  PrimeExponentProfile ps es /\
  orig = FactorPower ps es.

Definition PrefixMaximum (es : list Z) (upto mx : Z) : Prop :=
  0 <= upto <= Zlength es /\
  0 <= mx <= 30 /\
  (forall i, 0 <= i < upto -> Znth i es 0 <= mx) /\
  (upto = 0 -> mx = 0) /\
  (0 < upto -> exists i, 0 <= i < upto /\ Znth i es 0 = mx).

Definition MaximumExponent (es : list Z) (mx : Z) : Prop :=
  PrefixMaximum es (Zlength es) mx.

Definition LayerPrefixValue
    (ps es : list Z) (k upto : Z) : Z :=
  fold_right Z.mul 1
    (map
       (fun i =>
          if Z_le_dec k (Znth i es 0) then Znth i ps 1 else 1)
       (Zrange 0 upto)).

Definition LayerValue (ps es : list Z) (k : Z) : Z :=
  LayerPrefixValue ps es k (Zlength ps).

Definition LayerProductPrefix
    (orig : Z) (ps es : list Z) (k upto prod : Z) : Prop :=
  PrimeFactorization orig ps es /\
  1 <= k <= 30 /\
  0 <= upto <= Zlength ps /\
  prod = LayerPrefixValue ps es k upto /\
  1 <= prod <= orig /\
  (forall i,
      upto <= i < Zlength ps ->
      k <= Znth i es 0 ->
      prod * Znth i ps 1 <= orig).

Definition LayerSumPrefix
    (orig : Z) (ps es : list Z) (mx next total : Z) : Prop :=
  PrimeFactorization orig ps es /\
  MaximumExponent es mx /\
  1 <= next <= mx + 1 /\
  total = sum_range 1 (next - 1) (LayerValue ps es) /\
  0 <= total <= orig /\
  (next <= mx -> total + LayerValue ps es next <= orig).

Definition FactorizationAnswer
    (orig : Z) (ps es : list Z) (total : Z) : Prop :=
  PrimeFactorization orig ps es /\
  exists mx,
    MaximumExponent es mx /\
    total = sum_range 1 mx (LayerValue ps es) /\
    0 <= total <= orig.

Definition ExtractionScale (rem d e : Z) : Prop :=
  d * d <= rem * Z.pow d e.

(* A proof-facing normalization of the mathematical optimization problem.  A
   row is the (duplicate-free) list of primes in one square-free factor.  The
   value of an empty residual row is zero; nonempty rows are valued by their
   prime product. *)
Require Import Coq.Bool.Bool.
Require Import Coq.micromega.Lia.
Require Import Coq.micromega.Psatz.

Definition NFRowProduct (r : list Z) : Z :=
  fold_right Z.mul 1 r.

Definition NFRowValue (r : list Z) : Z :=
  match r with
  | [] => 0
  | _ => NFRowProduct r
  end.

Definition NFRowsValue (rs : list (list Z)) : Z :=
  fold_right Z.add 0 (map NFRowValue rs).

Definition NFIn (x : Z) (l : list Z) : bool :=
  if in_dec Z.eq_dec x l then true else false.

Definition NFNotIn (x : Z) (l : list Z) : bool :=
  negb (NFIn x l).

Definition NFIntersection (a b : list Z) : list Z :=
  filter (fun x => NFIn x b) a.

Definition NFOnly (a b : list Z) : list Z :=
  filter (fun x => NFNotIn x b) a.

Definition NFUnion (a b : list Z) : list Z :=
  a ++ NFOnly b a.

Lemma NFIn_spec : forall x l, NFIn x l = true <-> In x l.
Proof.
  intros x l. unfold NFIn.
  destruct (in_dec Z.eq_dec x l); split; intros H; auto; discriminate.
Qed.

Definition NFRowGood (r : list Z) : Prop :=
  r <> [] /\ NoDup r /\ Forall prime r.

Fixpoint NFUnionAll (rs : list (list Z)) : list Z :=
  match rs with
  | [] => []
  | r :: tail => NFUnion r (NFUnionAll tail)
  end.

Fixpoint NFResidualsRaw (rs : list (list Z)) : list (list Z) :=
  match rs with
  | [] => []
  | r :: tail =>
      NFIntersection r (NFUnionAll tail) :: NFResidualsRaw tail
  end.

Definition NFRowNonempty (r : list Z) : bool :=
  match r with
  | [] => false
  | _ => true
  end.

Definition NFResiduals (rs : list (list Z)) : list (list Z) :=
  filter NFRowNonempty (NFResidualsRaw rs).

(* The normalization lemmas are placed after the primitive row-set lemmas
   below.  This commented development records their dependency-oriented
   draft without introducing any declarations. *)
(*
Lemma NFRowNonempty_spec : forall r,
  NFRowNonempty r = true <-> r <> [].
Proof.
  intros [|x xs]; simpl; split; intros H.
  - discriminate.
  - exfalso. apply H. reflexivity.
  - discriminate.
  - reflexivity.
Qed.

Lemma NFUnionAll_In : forall x rs,
  In x (NFUnionAll rs) <-> In x (concat rs).
Proof.
  intros x rs. induction rs as [|r rs IH]; simpl; [tauto|].
  rewrite NFUnion_In, in_app_iff, IH. tauto.
Qed.

Lemma NFUnionAll_NoDup : forall rs,
  Forall (fun r => NoDup r) rs -> NoDup (NFUnionAll rs).
Proof.
  intros rs H. induction H as [|r rs Hr Hrs IH]; simpl.
  - constructor.
  - apply NFUnion_NoDup; assumption.
Qed.

Lemma NFUnionAll_Forall_prime : forall rs,
  Forall (fun r => Forall prime r) rs ->
  Forall prime (NFUnionAll rs).
Proof.
  intros rs H. induction H as [|r rs Hr Hrs IH]; simpl.
  - constructor.
  - apply NFUnion_Forall_prime; assumption.
Qed.

Lemma NFUnionAll_nonempty : forall rs,
  rs <> [] -> Forall NFRowGood rs -> NFUnionAll rs <> [].
Proof.
  intros rs Hrs Hgood. destruct rs as [|r tail]; [contradiction|].
  inversion Hgood as [|? ? [Hr_ne _] _]; subst. simpl.
  intro Hnil. assert (In (hd 0 r) (NFUnion r (NFUnionAll tail))).
  { apply NFUnion_In. left. destruct r; [contradiction|simpl; auto]. }
  rewrite Hnil in H. contradiction.
Qed.

Lemma NF_concat_filter_nonempty : forall rs,
  concat (filter NFRowNonempty rs) = concat rs.
Proof.
  intros rs. induction rs as [|r rs IH]; simpl; [reflexivity|].
  destruct r as [|x xs]; simpl; rewrite ?IH; reflexivity.
Qed.

Lemma NF_value_filter_nonempty : forall rs,
  NFRowsValue (filter NFRowNonempty rs) = NFRowsValue rs.
Proof.
  intros rs. unfold NFRowsValue. induction rs as [|r rs IH]; simpl.
  - reflexivity.
  - destruct r as [|x xs]; simpl.
    + rewrite IH. destruct (fold_right Z.add 0 (map NFRowValue rs)); reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma NF_merge_flat_perm_raw : forall rs,
  Forall (fun r => NoDup r) rs ->
  Permutation (concat rs)
    (NFUnionAll rs ++ concat (NFResidualsRaw rs)).
Proof.
  intros rs Hgood. induction Hgood as [|r rs Hr Hrs IH]; simpl.
  - constructor.
  - eapply Permutation_trans.
    + apply Permutation_app_head. exact IH.
    + rewrite !app_assoc.
      apply Permutation_app_tail.
      apply NF_union_intersection_perm.
      * exact Hr.
      * apply NFUnionAll_NoDup. exact Hrs.
Qed.

Lemma NF_merge_flat_perm : forall rs,
  Forall (fun r => NoDup r) rs ->
  Permutation (concat rs)
    (NFUnionAll rs ++ concat (NFResiduals rs)).
Proof.
  intros rs H. unfold NFResiduals. rewrite NF_concat_filter_nonempty.
  apply NF_merge_flat_perm_raw. exact H.
Qed.

Lemma NFResiduals_good : forall rs,
  Forall NFRowGood rs -> Forall NFRowGood (NFResiduals rs).
Proof.
  intros rs Hgood. unfold NFResiduals.
  apply Forall_forall. intros r Hr.
  apply filter_In in Hr as [Hr Hne].
  apply NFRowNonempty_spec in Hne.
  split; [exact Hne|].
  induction Hgood as [|a tail [Ha_ne [Ha_nd Ha_pr]] Htail IH]; simpl in Hr.
  - contradiction.
  - destruct Hr as [<- | Hr].
    + split.
      * apply NFIntersection_NoDup. exact Ha_nd.
      * apply NFIntersection_Forall_prime. exact Ha_pr.
    + specialize (IH Hr). tauto.
Qed.

Lemma NF_merge_value_raw : forall rs,
  Forall NFRowGood rs ->
  NFRowsValue rs <=
    NFRowValue (NFUnionAll rs) + NFRowsValue (NFResidualsRaw rs).
Proof.
  intros rs Hgood. induction Hgood as [|r rs [Hr_ne [Hr_nd Hr_pr]] Hrs IH]; simpl.
  - lia.
  - destruct rs as [|s tail].
    + assert (Hu : NFUnion r [] = r).
      { unfold NFUnion, NFOnly. simpl. apply app_nil_r. }
      assert (Hi_all : forall l, NFIntersection l [] = []).
      { intro l. unfold NFIntersection. induction l as [|x xs IHxs]; simpl; [reflexivity|].
        unfold NFIn. destruct (in_dec Z.eq_dec x []); [contradiction|exact IHxs]. }
      pose proof (Hi_all r) as Hi.
      cbn [NFUnionAll NFResidualsRaw]. rewrite Hu, Hi.
      unfold NFRowsValue. simpl. lia.
    + assert (Hu_good : NFRowGood (NFUnionAll (s :: tail))).
      { split.
        - apply NFUnionAll_nonempty; [discriminate|exact Hrs].
        - split.
          + apply NFUnionAll_NoDup.
            apply Forall_forall. intros q Hq.
            apply (proj1 (Forall_forall NFRowGood (s :: tail))) in Hrs.
            specialize (Hrs q Hq). tauto.
          + apply NFUnionAll_Forall_prime.
            apply Forall_forall. intros q Hq.
            apply (proj1 (Forall_forall NFRowGood (s :: tail))) in Hrs.
            specialize (Hrs q Hq). tauto. }
      destruct Hu_good as [Hu_ne [Hu_nd Hu_pr]].
      pose proof (NF_pair_uncross_value r (NFUnionAll (s :: tail))
        Hr_ne Hu_ne Hr_nd Hu_nd Hr_pr Hu_pr) as Hpair.
      change (NFRowValue r + NFRowsValue (s :: tail) <=
        NFRowValue (NFUnion r (NFUnionAll (s :: tail))) +
        (NFRowValue (NFIntersection r (NFUnionAll (s :: tail))) +
         NFRowsValue (NFResidualsRaw (s :: tail)))).
      lia.
Qed.

Lemma NF_merge_value : forall rs,
  Forall NFRowGood rs ->
  NFRowsValue rs <=
    NFRowValue (NFUnionAll rs) + NFRowsValue (NFResiduals rs).
Proof.
  intros rs H. unfold NFResiduals. rewrite NF_value_filter_nonempty.
  apply NF_merge_value_raw. exact H.
Qed.

(* Nested rows are the canonical shape: every prime occurring in a later row
   already occurs in every preceding row. *)
Fixpoint NFNested (rs : list (list Z)) : Prop :=
  match rs with
  | [] => True
  | r :: tail =>
      (forall s, In s tail -> forall p, In p s -> In p r) /\ NFNested tail
  end.

Lemma NFUnionAll_In_iff : forall p rs,
  In p (NFUnionAll rs) <-> exists r, In r rs /\ In p r.
Proof.
  intros p rs. induction rs as [|r rs IH]; simpl.
  - split; [contradiction|intros [q [Hq _]]; contradiction].
  - rewrite NFUnion_In, IH. split.
    + intros [Hp | [q [Hq Hp]]].
      * exists r. auto.
      * exists q. auto.
    + intros [q [[<- | Hq] Hp]].
      * auto.
      * right. exists q. auto.
Qed.

Lemma NFNested_tail_in_head : forall r tail p,
  NFNested (r :: tail) ->
  In p (concat tail) -> In p r.
Proof.
  intros r tail p [Hhead _] Hp.
  apply in_concat in Hp as [s [Hs Hp]]. eauto.
Qed.

Lemma NFNested_union_head_perm : forall r tail,
  r <> [] -> NoDup r -> Forall (fun q => NoDup q) tail ->
  NFNested (r :: tail) -> Permutation (NFUnionAll (r :: tail)) r.
Proof.
  intros r tail Hr_ne Hr_nd Htail Hnest.
  apply NoDup_Permutation.
  - apply NFUnionAll_NoDup. constructor; assumption.
  - exact Hr_nd.
  - destruct Hnest as [Hhead _]. intro p. rewrite NFUnionAll_In_iff. split.
    + intros [q [Hq Hp]]. destruct Hq as [<- | Hq]; [exact Hp|].
      exact (Hhead q Hq p Hp).
    + intro Hp. exists r. split; [left; reflexivity|exact Hp].
Qed.

Lemma NFGood_concat_nil : forall rs,
  Forall NFRowGood rs -> concat rs = [] -> rs = [].
Proof.
  intros rs Hgood. destruct rs as [|r tail]; [reflexivity|].
  inversion Hgood as [|? ? [Hr_ne _] _]; subst.
  simpl. intro Hnil. apply app_eq_nil in Hnil as [Hr _]. contradiction.
Qed.

Lemma NFResiduals_flat_tail_perm : forall rs c cs,
  Forall NFRowGood rs ->
  Forall NFRowGood (c :: cs) ->
  NFNested (c :: cs) ->
  Permutation (concat rs) (concat (c :: cs)) ->
  Permutation (concat (NFResiduals rs)) (concat cs).
Proof.
  intros rs c cs Hrs Hcs Hnest Hflat.
  assert (Hrs_nd : Forall (fun r => NoDup r) rs).
  { apply Forall_forall. intros r Hr.
    destruct ((proj1 (Forall_forall NFRowGood rs)) Hrs r Hr) as [_ [Hnd _]].
    exact Hnd. }
  pose proof (NF_merge_flat_perm rs Hrs_nd) as Hmerge.
  inversion Hcs as [|? ? [Hc_ne [Hc_nd _]] Hcs_good]; subst.
  assert (Hcs_nd : Forall (fun r => NoDup r) cs).
  { apply Forall_forall. intros r Hr.
    destruct ((proj1 (Forall_forall NFRowGood cs)) Hcs_good r Hr) as [_ [Hnd _]].
    exact Hnd. }
  assert (Hu : Permutation (NFUnionAll rs) c).
  { apply NoDup_Permutation.
    - apply NFUnionAll_NoDup. exact Hrs_nd.
    - exact Hc_nd.
    - intro p. rewrite NFUnionAll_In_iff. split.
      + intros [r [Hr Hp]].
        assert (In p (concat rs)).
        { apply in_concat. exists r. auto. }
        apply (Permutation_in p Hflat) in H.
        simpl in H. apply in_app_iff in H as [Hp_c | Hp_tail]; [exact Hp_c|].
        apply NFNested_tail_in_head with (tail := cs); auto.
      + intro Hp.
        assert (In p (concat rs)).
        { apply (Permutation_in p (Permutation_sym Hflat)).
          simpl. apply in_app_iff. left. exact Hp. }
        apply in_concat in H as [r [Hr Hpr]]. exists r. auto. }
  simpl in Hflat.
  apply (Permutation_app_inv_l c).
  eapply Permutation_trans.
  - apply Permutation_app_tail. apply Permutation_sym. exact Hu.
  - eapply Permutation_trans.
    + apply Permutation_sym. exact Hmerge.
    + exact Hflat.
Qed.

Theorem NF_nested_optimal : forall canonical other,
  Forall NFRowGood canonical -> NFNested canonical ->
  Forall NFRowGood other ->
  Permutation (concat other) (concat canonical) ->
  NFRowsValue other <= NFRowsValue canonical.
Proof.
  induction canonical as [|c cs IH]; intros other Hcan Hnest Hother Hflat.
  - simpl in Hflat.
    assert (Hnil : concat other = []).
    { apply Permutation_nil. apply Permutation_sym. exact Hflat. }
    apply NFGood_concat_nil in Hnil; [subst; simpl; lia|exact Hother].
  - inversion Hcan as [|? ? Hc Hcs]; subst.
    destruct Hnest as [Hhead Hnest].
    pose proof (NF_merge_value other Hother) as Hmerge.
    assert (Hother_nd : Forall (fun r => NoDup r) other).
    { apply Forall_forall. intros r Hr.
      destruct ((proj1 (Forall_forall NFRowGood other)) Hother r Hr)
        as [_ [Hnd _]]. exact Hnd. }
    destruct Hc as [Hc_ne [Hc_nd Hc_pr]].
    assert (Hcs_nd : Forall (fun r => NoDup r) cs).
    { apply Forall_forall. intros r Hr.
      destruct ((proj1 (Forall_forall NFRowGood cs)) Hcs r Hr)
        as [_ [Hnd _]]. exact Hnd. }
    assert (Hu_perm : Permutation (NFUnionAll other) c).
    { apply NoDup_Permutation.
      - apply NFUnionAll_NoDup. exact Hother_nd.
      - exact Hc_nd.
      - intro p. rewrite NFUnionAll_In_iff. split.
        + intros [r [Hr Hp]].
          assert (In p (concat other)).
          { apply in_concat. exists r. auto. }
          apply (Permutation_in p Hflat) in H.
          simpl in H. apply in_app_iff in H as [Hp_c | Hp_tail]; [exact Hp_c|].
          apply in_concat in Hp_tail as [s [Hs Hps]].
          exact (Hhead s Hs p Hps).
        + intro Hp.
          assert (In p (concat other)).
          { apply (Permutation_in p (Permutation_sym Hflat)).
            simpl. apply in_app_iff. left. exact Hp. }
          apply in_concat in H as [r [Hr Hpr]]. exists r. auto. }
    assert (Hres_good : Forall NFRowGood (NFResiduals other)).
    { apply NFResiduals_good. exact Hother. }
    assert (Hres_flat :
      Permutation (concat (NFResiduals other)) (concat cs)).
    { apply NFResiduals_flat_tail_perm with (c := c).
      - exact Hother.
      - exact Hcan.
      - split; assumption.
      - exact Hflat. }
    specialize (IH (NFResiduals other) Hcs Hnest Hres_good Hres_flat).
    pose proof (NFRowValue_perm _ _ Hu_perm) as Hu_value.
    change (NFRowsValue other <= NFRowValue c + NFRowsValue cs).
    lia.
Qed.

Lemma NF_prime_divides_product_member : forall p l,
  prime p -> Forall prime l -> (p | NFRowProduct l) -> In p l.
Proof.
  intros p l Hp Hl. induction Hl as [|q l Hq Hl IH]; simpl.
  - intro Hdiv. apply Z.divide_1_r in Hdiv.
    pose proof (prime_ge_2 p Hp). destruct Hdiv; lia.
  - intro Hdiv. destruct (prime_mult p Hp q (NFRowProduct l) Hdiv)
      as [Hpq | Hprest].
    + left. apply prime_divisors in Hpq; auto.
      pose proof (prime_ge_2 p Hp). pose proof (prime_ge_2 q Hq).
      destruct Hpq as [Hpq | [Hpq | [Hpq | Hpq]]]; lia.
    + right. apply IH. exact Hprest.
Qed.

Lemma NF_prime_products_perm : forall a b,
  Forall prime a -> Forall prime b ->
  NFRowProduct a = NFRowProduct b -> Permutation a b.
Proof.
  intros a b Ha. revert b. induction Ha as [|p a Hp Ha IH]; intros b Hb Heq.
  - destruct b as [|q b]; [constructor|].
    inversion Hb as [|? ? Hq _]; subst. simpl in Heq.
    pose proof (prime_ge_2 q Hq). pose proof (NFRowProduct_pos b).
    assert (Forall prime b) by (inversion Hb; assumption).
    specialize (H0 H1). nia.
  - assert (Hpdiv : (p | NFRowProduct b)).
    { exists (NFRowProduct a). simpl in Heq. nia. }
    pose proof (NF_prime_divides_product_member p b Hp Hb Hpdiv) as Hpin.
    apply in_split in Hpin as [before [after Hbshape]]. subst b.
    assert (Hperm_head : Permutation (before ++ p :: after) (p :: before ++ after)).
    { apply Permutation_sym. apply Permutation_middle. }
    assert (Hbrest : Forall prime (before ++ after)).
    { apply Forall_forall. intros q Hq.
      pose proof (proj1 (Forall_forall prime (before ++ p :: after)) Hb)
        as Hbmem. apply Hbmem. apply in_app_iff in Hq. apply in_app_iff.
      destruct Hq as [Hq | Hq]; [auto|right; simpl; auto]. }
    assert (Hprod_b : NFRowProduct (before ++ p :: after) =
      p * NFRowProduct (before ++ after)).
    { apply NFRowProduct_perm in Hperm_head. simpl in Hperm_head. exact Hperm_head. }
    assert (Hcancel : NFRowProduct a = NFRowProduct (before ++ after)).
    { simpl in Heq. pose proof (prime_ge_2 p Hp). nia. }
    eapply Permutation_trans.
    + apply perm_skip. apply IH; [exact Hbrest|exact Hcancel].
    + apply Permutation_sym. exact Hperm_head.
Qed.

Lemma NF_Forall_repeat : forall (A : Type) (P : A -> Prop) x n,
  P x -> Forall P (repeat x n).
Proof. intros A P x n H. induction n; simpl; constructor; auto. Qed.

Lemma NF_product_repeat_rows : forall r n,
  NFRowProduct (concat (repeat r n)) =
  Z.pow (NFRowProduct r) (Z.of_nat n).
Proof.
  intros r n. rewrite <- Zpower_nat_Z. induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite NFRowProduct_app, IH. reflexivity.
Qed.

Lemma NF_value_repeat_rows : forall r n,
  r <> [] ->
  NFRowsValue (repeat r n) = NFRowProduct r * Z.of_nat n.
Proof.
  intros r n Hr. destruct r as [|x xs]; [contradiction|].
  unfold NFRowsValue. induction n as [|n IH]; simpl.
  - ring.
  - rewrite IH.
    change (x * NFRowProduct xs + NFRowProduct (x :: xs) * Z.of_nat n =
      x * NFRowProduct xs * Z.of_nat (S n)).
    rewrite Nat2Z.inj_succ. simpl. ring.
Qed.

Lemma NF_expand_ap : forall ap,
  Forall (fun q => SquareFree (fst q) /\ snd q > 0) ap ->
  exists rows,
    Forall NFRowGood rows /\
    NFRowProduct (concat rows) =
      fold_right Z.mul 1 (map (fun q => Z.pow (fst q) (snd q)) ap) /\
    NFRowsValue rows =
      fold_right Z.add 0 (map (fun q => fst q * snd q) ap).
Proof.
  intros ap Hap. induction Hap as [|[x w] ap [Hsq Hw] Hap IH].
  - exists []. simpl. repeat split; constructor.
  - destruct Hsq as [r [Hr_ne [Hr_nd [Hr_pr Hx]]]].
    change (x = NFRowProduct r) in Hx.
    assert (Hw0 : 0 <= w) by (simpl in Hw; lia).
    destruct IH as [tail [Htail_good [Htail_prod Htail_value]]].
    exists (repeat r (Z.to_nat w) ++ tail). repeat split.
    + apply Forall_app. split; [apply NF_Forall_repeat|exact Htail_good].
      repeat split; assumption.
    + rewrite concat_app, NFRowProduct_app, NF_product_repeat_rows,
        Htail_prod, <- Hx, (Z2Nat.id w Hw0). reflexivity.
    + rewrite NFRowsValue_app, NF_value_repeat_rows by exact Hr_ne.
      rewrite Htail_value, <- Hx, (Z2Nat.id w Hw0). simpl. ring.
Qed.

Lemma NF_factor_value_sum_nonneg : forall ap,
  Forall (fun q => SquareFree (fst q) /\ snd q > 0) ap ->
  0 <= fold_right Z.add 0 (map (fun q => fst q * snd q) ap).
Proof.
  intros ap Hap. induction Hap as [|[x w] ap [Hsq Hw] Hap IH]; simpl; [lia|].
  destruct Hsq as [r [Hr_ne [Hr_nd [Hr_pr Hx]]]].
  change (x = NFRowProduct r) in Hx.
  pose proof (NFRowProduct_nonempty r Hr_ne Hr_pr) as Hx2.
  assert (Hterm : 0 < x * w).
  { apply Z.mul_pos_pos; [rewrite Hx; lia|exact (Z.gt_lt w 0 Hw)]. }
  nia.
Qed.

Lemma NF_factor_value_sum_pos : forall ap,
  ap <> [] ->
  Forall (fun q => SquareFree (fst q) /\ snd q > 0) ap ->
  0 < fold_right Z.add 0 (map (fun q => fst q * snd q) ap).
Proof.
  intros [|[x w] ap] Hne Hap; [contradiction|].
  inversion Hap as [|? ? [Hsq Hw] Htail]; subst. simpl.
  destruct Hsq as [r [Hr_ne [Hr_nd [Hr_pr Hx]]]].
  change (x = NFRowProduct r) in Hx.
  pose proof (NFRowProduct_nonempty r Hr_ne Hr_pr) as Hx2.
  pose proof (NF_factor_value_sum_nonneg ap Htail) as Htail0.
  assert (Hterm : 0 < x * w).
  { apply Z.mul_pos_pos; [rewrite Hx; lia|exact (Z.gt_lt w 0 Hw)]. }
  nia.
Qed.

Theorem NF_valid_to_rows : forall n value,
  ValidFactorization n value ->
  exists rows,
    rows <> [] /\ Forall NFRowGood rows /\
    NFRowProduct (concat rows) = n /\ NFRowsValue rows = value.
Proof.
  intros n value [ap [Hap_ne [Hap_good [Hn Hvalue]]]].
  destruct (NF_expand_ap ap Hap_good) as [rows [Hgood [Hprod Hval]]].
  exists rows. split.
  - intro Hnil. subst rows. unfold NFRowsValue in Hval. simpl in Hprod, Hval.
    pose proof (NF_factor_value_sum_pos ap Hap_ne Hap_good). nia.
  - split; [exact Hgood|]. split; nia.
Qed.

Definition NFLayerTest (es : list Z) (k i : Z) : bool :=
  if Z_le_dec k (Znth i es 0) then true else false.

Definition NFPrimeLayer (ps es : list Z) (k : Z) : list Z :=
  map (fun i => Znth i ps 1)
    (filter (NFLayerTest es k) (Zrange 0 (Zlength ps))).

Definition NFCanonicalRows (ps es : list Z) (mx : Z) : list (list Z) :=
  map (NFPrimeLayer ps es) (Zrange 1 (mx + 1)).

Lemma NFLayerTest_spec : forall es k i,
  NFLayerTest es k i = true <-> k <= Znth i es 0.
Proof.
  intros. unfold NFLayerTest. destruct (Z_le_dec k (Znth i es 0));
    split; intros; auto; discriminate.
Qed.

Lemma NFPrimeLayer_In : forall ps es k p,
  In p (NFPrimeLayer ps es k) <->
  exists i, 0 <= i < Zlength ps /\ k <= Znth i es 0 /\
    p = Znth i ps 1.
Proof.
  intros. unfold NFPrimeLayer. rewrite in_map_iff. split.
  - intros [i [<- Hi]]. apply filter_In in Hi as [Hi Htest].
    rewrite <- In_Zrange in Hi. apply NFLayerTest_spec in Htest. eauto.
  - intros [i [Hi [He Hp]]]. exists i. split; [symmetry; exact Hp|].
    apply filter_In. split; [apply In_Zrange; exact Hi|].
    apply NFLayerTest_spec. exact He.
Qed.

Lemma NF_Znth_indices_NoDup : forall ps il,
  NoDup ps -> NoDup il ->
  Forall (fun i => 0 <= i < Zlength ps) il ->
  NoDup (map (fun i => Znth i ps 1) il).
Proof.
  intros ps il Hps Hil Hbounds. induction Hil as [|i il Hi Hil IH]; simpl.
  - constructor.
  - inversion Hbounds as [|? ? Hib Hrest]; subst. constructor.
    + intro Hin. apply in_map_iff in Hin as [j [Heq Hj]].
      pose proof ((proj1 (Forall_forall _ _)) Hrest j Hj) as Hjb.
      apply (proj1 (NoDup_nth ps 1)) with
        (i := Z.to_nat i) (j := Z.to_nat j) in Hps.
      * apply Hi. replace i with j; [exact Hj|]. symmetry.
        apply (Z2Nat.inj i j); [exact (proj1 Hib)|exact (proj1 Hjb)|exact Hps].
      * rewrite Zlength_correct in Hib.
        rewrite <- (Nat2Z.id (length ps)).
        exact (proj1 (Z2Nat.inj_lt i (Z.of_nat (length ps))
          (proj1 Hib) (Nat2Z.is_nonneg _)) (proj2 Hib)).
      * rewrite Zlength_correct in Hjb.
        rewrite <- (Nat2Z.id (length ps)).
        exact (proj1 (Z2Nat.inj_lt j (Z.of_nat (length ps))
          (proj1 Hjb) (Nat2Z.is_nonneg _)) (proj2 Hjb)).
      * unfold Znth in Heq. symmetry. exact Heq.
    + apply IH. exact Hrest.
Qed.

Lemma NFPrimeLayer_NoDup : forall ps es k,
  NoDup ps -> NoDup (NFPrimeLayer ps es k).
Proof.
  intros ps es k Hps. unfold NFPrimeLayer. apply NF_Znth_indices_NoDup.
  - exact Hps.
  - apply NoDup_filter. apply NoDup_Zrange.
  - apply Forall_forall. intros i Hi. apply filter_In in Hi as [Hi _].
    apply <- In_Zrange. exact Hi.
Qed.

Lemma NFPrimeLayer_Forall_prime : forall ps es k,
  Forall prime ps -> Forall prime (NFPrimeLayer ps es k).
Proof.
  intros ps es k Hps. apply Forall_forall. intros p Hp.
  apply NFPrimeLayer_In in Hp as [i [Hi [_ ->]]].
  apply Forall_Znth_Zlength; assumption.
Qed.

Lemma NFPrimeLayer_monotone : forall ps es k1 k2 p,
  k1 <= k2 -> In p (NFPrimeLayer ps es k2) ->
  In p (NFPrimeLayer ps es k1).
Proof.
  intros ps es k1 k2 p Hle Hp.
  apply NFPrimeLayer_In in Hp as [i [Hi [Hei Heq]]].
  apply NFPrimeLayer_In. exists i. repeat split; auto; lia.
Qed.

Lemma NFPrimeLayers_range_aux_nested : forall ps es low n,
  NFNested (map (NFPrimeLayer ps es) (Zrange_aux low n)).
Proof.
  intros ps es low n. revert low. induction n as [|n IH]; intros low; simpl; auto.
  split.
  - intros row Hrow p Hp. apply in_map_iff in Hrow as [k2 [<- Hk2]].
    apply NFPrimeLayer_monotone with (k2 := k2); [|exact Hp].
    apply In_Zrange_aux in Hk2. lia.
  - apply IH.
Qed.

Lemma NFCanonicalRows_nested : forall ps es mx,
  NFNested (NFCanonicalRows ps es mx).
Proof.
  intros ps es mx. unfold NFCanonicalRows, Zrange.
  apply NFPrimeLayers_range_aux_nested.
Qed.

Lemma NFPrimeFactorization_nonempty : forall orig ps es,
  PrimeFactorization orig ps es -> ps <> [].
Proof.
  intros orig ps es [Horig [_ [_ Hfactor]]]. intro Hnil. subst ps.
  unfold FactorPower in Hfactor. simpl in Hfactor. nia.
Qed.

Lemma NFMaximumExponent_witness : forall es mx,
  es <> [] -> MaximumExponent es mx ->
  0 <= mx <= 30 /\ exists i, 0 <= i < Zlength es /\ Znth i es 0 = mx.
Proof.
  intros es mx Hes [_ [Hmx [_ [_ Hwit]]]].
  assert (0 < Zlength es).
  { rewrite Zlength_correct. destruct es; [contradiction|simpl; lia]. }
  specialize (Hwit H). destruct Hwit as [i [Hi He]].
  split; [exact Hmx|eauto].
Qed.

Lemma NFCanonicalRows_good : forall orig ps es mx,
  PrimeFactorization orig ps es -> MaximumExponent es mx ->
  Forall NFRowGood (NFCanonicalRows ps es mx).
Proof.
  intros orig ps es mx Hpf Hmax.
  destruct Hpf as [Horig [Hcap [Hprofile Hfactor]]].
  destruct Hprofile as [Hlen [Hnd [Hprime Hexp]]].
  assert (Hps_ne : ps <> []).
  { apply (NFPrimeFactorization_nonempty orig ps es).
    exact (conj Horig (conj Hcap
      (conj (conj Hlen (conj Hnd (conj Hprime Hexp))) Hfactor))). }
  assert (Hes_ne : es <> []).
  { intro Hes. subst es. rewrite Zlength_nil in Hlen.
    apply Zlength_nil_inv in Hlen. contradiction. }
  destruct (NFMaximumExponent_witness es mx Hes_ne Hmax)
    as [Hmx [im [Him Hem]]].
  assert (Hmx1 : 1 <= mx).
  { specialize (Hexp im Him). rewrite Hem in Hexp. lia. }
  unfold NFCanonicalRows. apply Forall_forall. intros row Hrow.
  apply in_map_iff in Hrow as [k [<- Hk]].
  apply <- In_Zrange in Hk. repeat split.
  - intro Hnil.
    assert (In (Znth im ps 1) (NFPrimeLayer ps es k)).
    { apply NFPrimeLayer_In. exists im. repeat split; auto; lia. }
    rewrite Hnil in H. contradiction.
  - apply NFPrimeLayer_NoDup. exact Hnd.
  - apply NFPrimeLayer_Forall_prime. exact Hprime.
Qed.

Lemma NF_product_filter_layer : forall ps es k il,
  NFRowProduct
    (map (fun i => Znth i ps 1) (filter (NFLayerTest es k) il)) =
  fold_right Z.mul 1
    (map (fun i => if Z_le_dec k (Znth i es 0)
                   then Znth i ps 1 else 1) il).
Proof.
  intros ps es k il. unfold NFRowProduct.
  induction il as [|i il IH]; cbn [filter map fold_right]; [reflexivity|].
  destruct (Z_le_dec k (Znth i es 0)) as [Hle|Hnle].
  - assert (Ht : NFLayerTest es k i = true).
    { apply NFLayerTest_spec. exact Hle. }
    rewrite Ht. cbn [filter map fold_right]. rewrite IH, Z.mul_1_l. reflexivity.
  - assert (Ht : NFLayerTest es k i = false).
    { unfold NFLayerTest. destruct (Z_le_dec k (Znth i es 0)) as [Hle'|Hnle'];
        [exfalso; apply Hnle; exact Hle'|reflexivity]. }
    rewrite Ht. cbn [filter map fold_right]. rewrite IH, Z.mul_1_l. reflexivity.
Qed.

Lemma NFPrimeLayer_value : forall ps es k,
  NFPrimeLayer ps es k <> [] ->
  NFRowValue (NFPrimeLayer ps es k) = LayerValue ps es k.
Proof.
  intros ps es k Hne. rewrite NFRowValue_nonempty by exact Hne.
  unfold NFPrimeLayer, LayerValue, LayerPrefixValue.
  apply NF_product_filter_layer.
Qed.

Lemma NF_fold_add_map : forall (A : Type) (f : A -> Z) l,
  fold_right Z.add 0 (map f l) =
  fold_right (fun x acc => f x + acc) 0 l.
Proof. intros A f l. induction l; simpl; [reflexivity|]. rewrite IHl. reflexivity. Qed.

Lemma NFCanonicalRows_value : forall orig ps es mx,
  PrimeFactorization orig ps es -> MaximumExponent es mx ->
  NFRowsValue (NFCanonicalRows ps es mx) =
    sum_range 1 mx (LayerValue ps es).
Proof.
  intros orig ps es mx Hpf Hmax.
  pose proof (NFCanonicalRows_good orig ps es mx Hpf Hmax) as Hgood.
  unfold NFCanonicalRows, NFRowsValue.
  rewrite map_map, NF_fold_add_map. unfold sum_range. rewrite sum_range_unfold.
  apply fold_Zsum_ext_in. intros k Hk.
  apply NFPrimeLayer_value.
  apply (proj1 (Forall_forall NFRowGood
    (map (NFPrimeLayer ps es) (Zrange 1 (mx + 1)))))
    with (x := NFPrimeLayer ps es k) in Hgood.
  - unfold NFRowGood in Hgood. exact (proj1 Hgood).
  - apply in_map. exact Hk.
Qed.

Lemma NFRowProduct_concat : forall rows,
  NFRowProduct (concat rows) =
  fold_right Z.mul 1 (map NFRowProduct rows).
Proof.
  intros rows. induction rows as [|r rows IH]; simpl; [reflexivity|].
  rewrite NFRowProduct_app, IH. reflexivity.
Qed.

Lemma NF_fold_mul_pointwise : forall (A : Type) (l : list A)
    (f g : A -> Z),
  fold_right Z.mul 1 (map (fun x => f x * g x) l) =
  fold_right Z.mul 1 (map f l) * fold_right Z.mul 1 (map g l).
Proof.
  intros A l f g. induction l as [|x l IH]; simpl; [ring|].
  rewrite IH. ring.
Qed.

Lemma NF_fold_matrix : forall (A B : Type) (xs : list A) (ys : list B)
    (entry : A -> B -> Z),
  fold_right Z.mul 1
    (map (fun y => fold_right Z.mul 1 (map (fun x => entry x y) xs)) ys) =
  fold_right Z.mul 1
    (map (fun x => fold_right Z.mul 1 (map (entry x) ys)) xs).
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros ys entry; simpl.
  - induction ys; simpl; [reflexivity|]. rewrite IHys. ring.
  - rewrite <- IH.
    rewrite (NF_fold_mul_pointwise B ys
      (entry x)
      (fun y => fold_right Z.mul 1 (map (fun z => entry z y) xs))).
    reflexivity.
Qed.

Lemma NF_fold_mul_app : forall a b,
  fold_right Z.mul 1 (a ++ b) =
  fold_right Z.mul 1 a * fold_right Z.mul 1 b.
Proof.
  intros a b. induction a; simpl.
  - destruct (fold_right Z.mul 1 b); reflexivity.
  - rewrite IHa, Z.mul_assoc. reflexivity.
Qed.

Lemma NF_fold_mul_ext_in : forall (A : Type) (l : list A) (f g : A -> Z),
  (forall x, In x l -> f x = g x) ->
  fold_right Z.mul 1 (map f l) = fold_right Z.mul 1 (map g l).
Proof.
  intros A l. induction l as [|x l IH]; intros f g Hext; simpl; [reflexivity|].
  rewrite (Hext x) by (left; reflexivity).
  rewrite (IH f g); [reflexivity|].
  intros y Hy. apply Hext. right. exact Hy.
Qed.

Lemma NF_threshold_true_aux : forall p low n e,
  low + Z.of_nat n <= e + 1 ->
  fold_right Z.mul 1
    (map (fun k => if Z_le_dec k e then p else 1) (Zrange_aux low n)) =
  Z.pow p (Z.of_nat n).
Proof.
  intros p low n. revert low. induction n as [|n IH]; intros low e Hbound;
    cbn [Zrange_aux map fold_right].
  - reflexivity.
  - destruct (Z_le_dec low e); [|lia].
    rewrite IH by (rewrite Nat2Z.inj_succ in Hbound; lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma NF_threshold_false_aux : forall p low n e,
  e < low ->
  fold_right Z.mul 1
    (map (fun k => if Z_le_dec k e then p else 1) (Zrange_aux low n)) = 1.
Proof.
  intros p low n. revert low. induction n as [|n IH]; intros low e Hlt;
    cbn [Zrange_aux map fold_right]; [reflexivity|].
  destruct (Z_le_dec low e); [lia|]. rewrite IH by lia. reflexivity.
Qed.

Lemma NF_fold_threshold_range : forall p mx e,
  0 <= e <= mx ->
  fold_right Z.mul 1
    (map (fun k => if Z_le_dec k e then p else 1)
      (Zrange 1 (mx + 1))) = Z.pow p e.
Proof.
  intros p mx e He.
  unfold Zrange. replace (mx + 1 - 1) with mx by ring.
  assert (Hnat : Z.to_nat mx =
      (Z.to_nat e + Z.to_nat (mx - e))%nat).
  { rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
  rewrite Hnat, Zrange_aux_app, map_app, NF_fold_mul_app.
  rewrite NF_threshold_true_aux.
  2: rewrite Z2Nat.id by lia; lia.
  rewrite NF_threshold_false_aux.
  2: rewrite Z2Nat.id by lia; lia.
  rewrite Z2Nat.id by lia. ring.
Qed.

Lemma NF_layer_product_as_entries : forall ps es k il,
  NFRowProduct
    (map (fun i => Znth i ps 1) (filter (NFLayerTest es k) il)) =
  fold_right Z.mul 1
    (map (fun i => if Z_le_dec k (Znth i es 0)
                   then Znth i ps 1 else 1) il).
Proof. apply NF_product_filter_layer. Qed.

Lemma NFCanonicalRows_product : forall orig ps es mx,
  PrimeFactorization orig ps es -> MaximumExponent es mx ->
  NFRowProduct (concat (NFCanonicalRows ps es mx)) = orig.
Proof.
  intros orig ps es mx Hpf Hmax.
  destruct Hpf as [Horig [Hcap [Hprofile Hfactor]]].
  destruct Hprofile as [Hlen [Hnd [Hprime Hexp]]].
  assert (Hps_ne : ps <> []).
  { apply (NFPrimeFactorization_nonempty orig ps es).
    exact (conj Horig (conj Hcap
      (conj (conj Hlen (conj Hnd (conj Hprime Hexp))) Hfactor))). }
  assert (Hes_ne : es <> []).
  { intro Hes. subst es. rewrite Zlength_nil in Hlen.
    apply Zlength_nil_inv in Hlen. contradiction. }
  destruct (NFMaximumExponent_witness es mx Hes_ne Hmax)
    as [Hmx [im [Him Hem]]].
  assert (Hmx1 : 1 <= mx).
  { specialize (Hexp im Him). rewrite Hem in Hexp. lia. }
  rewrite NFRowProduct_concat. unfold NFCanonicalRows.
  rewrite map_map.
  change (fold_right Z.mul 1
    (map (fun k => NFRowProduct (NFPrimeLayer ps es k))
      (Zrange 1 (mx + 1))) = orig).
  unfold NFPrimeLayer.
  set (indices := Zrange 0 (Zlength ps)).
  assert (Hentry : forall k,
    NFRowProduct
      (map (fun i => Znth i ps 1) (filter (NFLayerTest es k) indices)) =
    fold_right Z.mul 1
      (map (fun i => if Z_le_dec k (Znth i es 0)
                     then Znth i ps 1 else 1) indices)).
  { intro k. apply NF_layer_product_as_entries. }
  erewrite NF_fold_mul_ext_in.
  2: intros k Hk; apply Hentry.
  rewrite (NF_fold_matrix Z Z indices (Zrange 1 (mx + 1))
    (fun i k => if Z_le_dec k (Znth i es 0)
                then Znth i ps 1 else 1)).
  assert (Hexponents : forall i, In i indices ->
    0 <= Znth i es 0 <= mx).
  { intros i Hi. unfold indices in Hi. apply <- In_Zrange in Hi.
    assert (Hi_es : 0 <= i < Zlength es) by lia.
    specialize (Hexp i Hi_es).
    destruct Hmax as [_ [_ [Hupper _]]]. specialize (Hupper i Hi_es). lia. }
  erewrite NF_fold_mul_ext_in.
  2: { intros i Hi. apply NF_fold_threshold_range. apply Hexponents. exact Hi. }
  unfold indices, FactorPower in Hfactor. symmetry. exact Hfactor.
Qed.

Lemma NF_concat_Forall_prime : forall rows,
  Forall NFRowGood rows -> Forall prime (concat rows).
Proof.
  intros rows H. induction H as [|r rows [_ [_ Hr]] Hrows IH]; simpl.
  - constructor.
  - apply Forall_app. auto.
Qed.

Lemma NF_rows_unit_product : forall rows,
  fold_right Z.mul 1
    (map (fun q => Z.pow (fst q) (snd q))
      (map (fun r => (NFRowProduct r, 1)) rows)) =
  NFRowProduct (concat rows).
Proof.
  intros rows. induction rows as [|r rows IH]; cbn [map fold_right concat].
  - reflexivity.
  - rewrite Z.pow_1_r, NFRowProduct_app, IH. reflexivity.
Qed.

Lemma NF_rows_unit_value : forall rows,
  Forall NFRowGood rows ->
  fold_right Z.add 0
    (map (fun q => fst q * snd q)
      (map (fun r => (NFRowProduct r, 1)) rows)) =
  fold_right Z.add 0 (map NFRowValue rows).
Proof.
  intros rows Hgood. induction Hgood as [|r rows [Hr_ne Hr_rest] Hgood IH];
    cbn [map fold_right].
  - reflexivity.
  - rewrite Z.mul_1_r, NFRowValue_nonempty by exact Hr_ne.
    rewrite IH. reflexivity.
Qed.

Lemma NF_good_rows_valid : forall rows n value,
  rows <> [] -> Forall NFRowGood rows ->
  NFRowProduct (concat rows) = n -> NFRowsValue rows = value ->
  ValidFactorization n value.
Proof.
  intros rows n value Hne Hgood Hprod Hvalue.
  exists (map (fun r => (NFRowProduct r, 1)) rows). repeat split.
  - intro Hnil. apply map_eq_nil in Hnil. contradiction.
  - apply Forall_forall. intros q Hq.
    apply in_map_iff in Hq as [r [<- Hr]]. simpl.
    destruct ((proj1 (Forall_forall NFRowGood rows)) Hgood r Hr)
      as [Hr_ne [Hr_nd Hr_pr]]. split; [|lia].
    exists r. repeat split; auto.
  - rewrite NF_rows_unit_product. symmetry. exact Hprod.
  - rewrite NF_rows_unit_value by exact Hgood.
    unfold NFRowsValue in Hvalue. symmetry. exact Hvalue.
Qed.

Lemma NFCanonicalRows_nonempty : forall orig ps es mx,
  PrimeFactorization orig ps es -> MaximumExponent es mx ->
  NFCanonicalRows ps es mx <> [].
Proof.
  intros orig ps es mx Hpf Hmax.
  pose proof (NFCanonicalRows_good orig ps es mx Hpf Hmax) as Hgood.
  intro Hnil. subst.
  assert (Hps_ne := NFPrimeFactorization_nonempty orig ps es Hpf).
  destruct Hpf as [_ [_ [[Hlen [_ [_ Hexp]]] _]]].
  assert (Hes_ne : es <> []).
  { intro Hes. subst. rewrite Zlength_nil in Hlen.
    apply Zlength_nil_inv in Hlen. contradiction. }
  destruct (NFMaximumExponent_witness es mx Hes_ne Hmax)
    as [_ [i [Hi He]]]. specialize (Hexp i Hi). rewrite He in Hexp.
  unfold NFCanonicalRows in Hnil. apply map_eq_nil in Hnil.
  unfold Zrange in Hnil. simpl in Hnil.
  replace (mx + 1 - 1) with mx in Hnil by ring.
  assert (0 < Z.to_nat mx)%nat.
  { exact (proj1 (Z2Nat.inj_lt 0 mx ltac:(lia) ltac:(lia)) ltac:(lia)). }
  destruct (Z.to_nat mx) as [|m].
  - lia.
  - simpl in Hnil. discriminate.
Qed.

Theorem NF_layer_answer_valid : forall orig ps es mx,
  PrimeFactorization orig ps es -> MaximumExponent es mx ->
  ValidFactorization orig (sum_range 1 mx (LayerValue ps es)).
Proof.
  intros orig ps es mx Hpf Hmax.
  apply NF_good_rows_valid with (rows := NFCanonicalRows ps es mx).
  - apply NFCanonicalRows_nonempty with (orig := orig); assumption.
  - apply NFCanonicalRows_good with (orig := orig); assumption.
  - apply NFCanonicalRows_product with (orig := orig); assumption.
  - apply NFCanonicalRows_value with (orig := orig); assumption.
Qed.

Theorem NF_layer_answer_maximal : forall orig ps es mx other_value,
  PrimeFactorization orig ps es -> MaximumExponent es mx ->
  ValidFactorization orig other_value ->
  other_value <= sum_range 1 mx (LayerValue ps es).
Proof.
  intros orig ps es mx other_value Hpf Hmax Hvalid.
  destruct (NF_valid_to_rows orig other_value Hvalid)
    as [other [_ [Hother_good [Hother_prod Hother_value]]]].
  set (canonical := NFCanonicalRows ps es mx).
  assert (Hcan_good : Forall NFRowGood canonical).
  { unfold canonical. apply NFCanonicalRows_good with (orig := orig); assumption. }
  assert (Hcan_nested : NFNested canonical).
  { unfold canonical. apply NFCanonicalRows_nested. }
  assert (Hcan_prod : NFRowProduct (concat canonical) = orig).
  { unfold canonical. apply NFCanonicalRows_product with (orig := orig); assumption. }
  assert (Hother_pr : Forall prime (concat other)).
  { apply NF_concat_Forall_prime. exact Hother_good. }
  assert (Hcan_pr : Forall prime (concat canonical)).
  { apply NF_concat_Forall_prime. exact Hcan_good. }
  assert (Hperm : Permutation (concat other) (concat canonical)).
  { apply NF_prime_products_perm; auto. nia. }
  pose proof (NF_nested_optimal canonical other Hcan_good Hcan_nested
    Hother_good Hperm) as Hopt.
  pose proof (NFCanonicalRows_value orig ps es mx Hpf Hmax) as Hcan_value.
  change (NFRowsValue canonical =
    sum_range 1 mx (LayerValue ps es)) in Hcan_value.
  rewrite Hother_value, Hcan_value in Hopt. exact Hopt.
Qed.

Definition LayerOptimalityCertificate
    (orig : Z) (ps es : list Z) (mx : Z) : Prop :=
  Spec orig (sum_range 1 mx (LayerValue ps es)).

Theorem LayerOptimalityCertificate_proved : forall orig ps es mx,
  PrimeFactorization orig ps es -> MaximumExponent es mx ->
  LayerOptimalityCertificate orig ps es mx.
Proof.
  intros orig ps es mx Hpf Hmax.
  unfold LayerOptimalityCertificate, Spec, max_value_of_subset.
  exists (sum_range 1 mx (LayerValue ps es)). split; [split|reflexivity].
  - apply NF_layer_answer_valid; assumption.
  - intros b Hb. apply NF_layer_answer_maximal with
      (orig := orig) (ps := ps) (es := es) (mx := mx); assumption.
Qed.

Theorem LayerOptimalityCertificate_spec : forall orig ps es mx total,
  LayerOptimalityCertificate orig ps es mx ->
  total = sum_range 1 mx (LayerValue ps es) -> Spec orig total.
Proof. intros. subst. exact H. Qed.
*)

Lemma NFNotIn_spec : forall x l, NFNotIn x l = true <-> ~ In x l.
Proof.
  intros x l. unfold NFNotIn.
  rewrite Bool.negb_true_iff, <- Bool.not_true_iff_false, NFIn_spec.
  tauto.
Qed.

Lemma NFIntersection_In : forall x a b,
  In x (NFIntersection a b) <-> In x a /\ In x b.
Proof.
  intros x a b. unfold NFIntersection. rewrite filter_In, NFIn_spec. tauto.
Qed.

Lemma NFOnly_In : forall x a b,
  In x (NFOnly a b) <-> In x a /\ ~ In x b.
Proof.
  intros x a b. unfold NFOnly. rewrite filter_In, NFNotIn_spec. tauto.
Qed.

Lemma NFUnion_In : forall x a b,
  In x (NFUnion a b) <-> In x a \/ In x b.
Proof.
  intros x a b. unfold NFUnion. rewrite in_app_iff, NFOnly_In. tauto.
Qed.

Lemma NFIntersection_NoDup : forall a b,
  NoDup a -> NoDup (NFIntersection a b).
Proof.
  intros a b H. unfold NFIntersection. apply NoDup_filter. exact H.
Qed.

Lemma NFOnly_NoDup : forall a b,
  NoDup a -> NoDup (NFOnly a b).
Proof.
  intros a b H. unfold NFOnly. apply NoDup_filter. exact H.
Qed.

Lemma NFUnion_NoDup : forall a b,
  NoDup a -> NoDup b -> NoDup (NFUnion a b).
Proof.
  intros a b Ha Hb. unfold NFUnion. apply NoDup_app. repeat split.
  - exact Ha.
  - apply NFOnly_NoDup. exact Hb.
  - intros x Hxa Hxb. apply NFOnly_In in Hxb. tauto.
Qed.

Lemma NFIntersection_Forall_prime : forall a b,
  Forall prime a -> Forall prime (NFIntersection a b).
Proof.
  intros a b H. apply Forall_forall. intros x Hx.
  apply NFIntersection_In in Hx as [Hx _].
  exact ((proj1 (Forall_forall prime a)) H x Hx).
Qed.

Lemma NFOnly_Forall_prime : forall a b,
  Forall prime a -> Forall prime (NFOnly a b).
Proof.
  intros a b H. apply Forall_forall. intros x Hx.
  apply NFOnly_In in Hx as [Hx _].
  exact ((proj1 (Forall_forall prime a)) H x Hx).
Qed.

Lemma NFUnion_Forall_prime : forall a b,
  Forall prime a -> Forall prime b -> Forall prime (NFUnion a b).
Proof.
  intros a b Ha Hb. apply Forall_forall. intros x Hx.
  apply NFUnion_In in Hx as [Hx | Hx].
  - exact ((proj1 (Forall_forall prime a)) Ha x Hx).
  - exact ((proj1 (Forall_forall prime b)) Hb x Hx).
Qed.

Lemma NFRowProduct_app : forall a b,
  NFRowProduct (a ++ b) = NFRowProduct a * NFRowProduct b.
Proof.
  intros a b. unfold NFRowProduct. induction a as [|x xs IH]; simpl.
  - destruct (fold_right Z.mul 1 b); reflexivity.
  - rewrite IH.
    ring.
Qed.

Lemma NFRowProduct_perm : forall a b,
  Permutation a b -> NFRowProduct a = NFRowProduct b.
Proof.
  intros a b H. induction H; simpl; try nia; congruence.
Qed.

Lemma NFRowValue_perm : forall a b,
  Permutation a b -> NFRowValue a = NFRowValue b.
Proof.
  intros a b Hperm.
  destruct a as [|x xs], b as [|y ys].
  - reflexivity.
  - pose proof (Permutation_length Hperm). simpl in H. discriminate.
  - pose proof (Permutation_length Hperm). simpl in H. discriminate.
  - unfold NFRowValue. apply NFRowProduct_perm. exact Hperm.
Qed.

Lemma NFRowProduct_pos : forall r,
  Forall prime r -> 1 <= NFRowProduct r.
Proof.
  intros r H. induction H as [|p r Hp Hr IH]; simpl; [lia|].
  pose proof (prime_ge_2 p Hp). nia.
Qed.

Lemma NFRowProduct_nonempty : forall r,
  r <> [] -> Forall prime r -> 2 <= NFRowProduct r.
Proof.
  intros r Hne Hprime. destruct r as [|p r]; [contradiction|].
  inversion Hprime as [|? ? Hp Hrest]; subst. simpl.
  pose proof (prime_ge_2 p Hp).
  pose proof (NFRowProduct_pos r Hrest). nia.
Qed.

Lemma NFRowsValue_app : forall a b,
  NFRowsValue (a ++ b) = NFRowsValue a + NFRowsValue b.
Proof.
  intros a b. unfold NFRowsValue. rewrite map_app.
  induction (map NFRowValue a) as [|x xs IH]; simpl; nia.
Qed.

Lemma NFRowValue_nonempty : forall r,
  r <> [] -> NFRowValue r = NFRowProduct r.
Proof.
  intros r H. destruct r; [contradiction|reflexivity].
Qed.

Lemma NF_partition_perm : forall a b,
  Permutation a (NFOnly a b ++ NFIntersection a b).
Proof.
  intros a b. unfold NFOnly, NFIntersection, NFNotIn, NFIn.
  induction a as [|x xs IH]; simpl; [constructor|].
  destruct (in_dec Z.eq_dec x b) as [Hin | Hnot]; simpl.
  - eapply Permutation_trans.
    + apply perm_skip. exact IH.
    + apply Permutation_middle.
  - apply perm_skip. exact IH.
Qed.

Lemma NF_intersection_sym_perm : forall a b,
  NoDup a -> NoDup b ->
  Permutation (NFIntersection a b) (NFIntersection b a).
Proof.
  intros a b Ha Hb. apply NoDup_Permutation.
  - apply NFIntersection_NoDup. exact Ha.
  - apply NFIntersection_NoDup. exact Hb.
  - intro x. rewrite !NFIntersection_In. tauto.
Qed.

Lemma NF_union_intersection_perm : forall a b,
  NoDup a -> NoDup b ->
  Permutation (a ++ b) (NFUnion a b ++ NFIntersection a b).
Proof.
  intros a b Ha Hb. unfold NFUnion.
  eapply Permutation_trans with
      (l' := a ++ (NFOnly b a ++ NFIntersection b a)).
  - apply Permutation_app_head. apply NF_partition_perm.
  - rewrite app_assoc.
    apply Permutation_app_head. apply NF_intersection_sym_perm; assumption.
Qed.

Lemma NFOnly_Forall_prime_left : forall a b,
  Forall prime a -> Forall prime (NFOnly a b).
Proof. intros; apply NFOnly_Forall_prime; assumption. Qed.

Lemma NF_pair_uncross_value : forall a b,
  a <> [] -> b <> [] ->
  NoDup a -> NoDup b ->
  Forall prime a -> Forall prime b ->
  NFRowValue a + NFRowValue b <=
  NFRowValue (NFUnion a b) + NFRowValue (NFIntersection a b).
Proof.
  intros a b Ha_ne Hb_ne Ha_nd Hb_nd Ha_pr Hb_pr.
  assert (Hunion_ne : NFUnion a b <> []).
  { intro Hnil. destruct a as [|x xs]; [contradiction|].
    assert (In x (NFUnion (x :: xs) b)).
    { apply NFUnion_In. left. simpl; auto. }
    rewrite Hnil in H. contradiction. }
  pose proof (NF_partition_perm a b) as Hpa.
  pose proof (NF_partition_perm b a) as Hpb.
  pose proof (NF_intersection_sym_perm a b Ha_nd Hb_nd) as Hinter.
  assert (Ha_prod : NFRowProduct a =
      NFRowProduct (NFOnly a b) * NFRowProduct (NFIntersection a b)).
  { rewrite (NFRowProduct_perm _ _ Hpa), NFRowProduct_app. reflexivity. }
  assert (Hb_prod : NFRowProduct b =
      NFRowProduct (NFOnly b a) * NFRowProduct (NFIntersection a b)).
  { rewrite (NFRowProduct_perm _ _ Hpb), NFRowProduct_app.
    rewrite (NFRowProduct_perm _ _ Hinter). ring. }
  assert (Hu_prod : NFRowProduct (NFUnion a b) =
      NFRowProduct a * NFRowProduct (NFOnly b a)).
  { unfold NFUnion. apply NFRowProduct_app. }
  rewrite (NFRowValue_nonempty a Ha_ne),
          (NFRowValue_nonempty b Hb_ne),
          (NFRowValue_nonempty (NFUnion a b) Hunion_ne).
  destruct (NFIntersection a b) as [|z zs] eqn:Hi.
  - simpl NFRowValue.
    assert (Ha_only_ne : NFOnly a b <> []).
    { intro Hnil. pose proof (Permutation_length Hpa) as Hlen.
      rewrite Hnil in Hlen. simpl in Hlen.
      destruct a; [contradiction|simpl in Hlen; lia]. }
    assert (Hb_only_ne : NFOnly b a <> []).
    { assert (Hinter_nil : NFIntersection b a = []).
      { apply Permutation_nil. exact Hinter. }
      intro Hnil. pose proof (Permutation_length Hpb) as Hlen.
      rewrite Hnil, Hinter_nil in Hlen. simpl in Hlen.
      destruct b; [contradiction|simpl in Hlen; lia]. }
    pose proof (NFRowProduct_nonempty (NFOnly a b) Ha_only_ne
      (NFOnly_Forall_prime _ _ Ha_pr)) as Hx.
    pose proof (NFRowProduct_nonempty (NFOnly b a) Hb_only_ne
      (NFOnly_Forall_prime _ _ Hb_pr)) as Hy.
    simpl in Ha_prod, Hb_prod. rewrite !Z.mul_1_r in Ha_prod, Hb_prod.
    rewrite Hu_prod, Ha_prod, Hb_prod. nia.
  - assert (Hi_pr : Forall prime (z :: zs)).
    { rewrite <- Hi. apply NFIntersection_Forall_prime. exact Ha_pr. }
    pose proof (NFRowProduct_nonempty (z :: zs) ltac:(discriminate) Hi_pr) as Hi_pos.
    pose proof (NFRowProduct_pos (NFOnly a b)
      (NFOnly_Forall_prime _ _ Ha_pr)) as Hx.
    pose proof (NFRowProduct_pos (NFOnly b a)
      (NFOnly_Forall_prime _ _ Hb_pr)) as Hy.
    simpl NFRowValue.
    rewrite Hu_prod, Ha_prod, Hb_prod.
    assert (Hxy : 0 <=
      (NFRowProduct (NFOnly a b) - 1) *
      (NFRowProduct (NFOnly b a) - 1)) by nia.
    assert (Hfactor :
      NFRowProduct (NFOnly a b) * NFRowProduct (z :: zs) +
      NFRowProduct (NFOnly b a) * NFRowProduct (z :: zs) +
      NFRowProduct (z :: zs) *
        ((NFRowProduct (NFOnly a b) - 1) *
         (NFRowProduct (NFOnly b a) - 1)) =
      (NFRowProduct (NFOnly a b) * NFRowProduct (z :: zs)) *
        NFRowProduct (NFOnly b a) + NFRowProduct (z :: zs)) by ring.
    assert (Hdelta : 0 <= NFRowProduct (z :: zs) *
      ((NFRowProduct (NFOnly a b) - 1) *
       (NFRowProduct (NFOnly b a) - 1))) by nia.
    assert (Hstep :
      NFRowProduct (NFOnly a b) * NFRowProduct (z :: zs) +
      NFRowProduct (NFOnly b a) * NFRowProduct (z :: zs) <=
      NFRowProduct (NFOnly a b) * NFRowProduct (z :: zs) +
      NFRowProduct (NFOnly b a) * NFRowProduct (z :: zs) +
      NFRowProduct (z :: zs) *
        ((NFRowProduct (NFOnly a b) - 1) *
         (NFRowProduct (NFOnly b a) - 1))) by lia.
    rewrite Hfactor in Hstep. exact Hstep.
Qed.

Lemma NFRowNonempty_spec : forall r,
  NFRowNonempty r = true <-> r <> [].
Proof.
  intros [|x xs]; simpl; split; intros H.
  - discriminate.
  - exfalso. apply H. reflexivity.
  - discriminate.
  - reflexivity.
Qed.

Lemma NFUnionAll_In : forall x rs,
  In x (NFUnionAll rs) <-> In x (concat rs).
Proof.
  intros x rs. induction rs as [|r rs IH]; simpl; [tauto|].
  rewrite NFUnion_In, in_app_iff, IH. tauto.
Qed.

Lemma NFUnionAll_NoDup : forall rs,
  Forall (fun r => NoDup r) rs -> NoDup (NFUnionAll rs).
Proof.
  intros rs H. induction H as [|r rs Hr Hrs IH]; simpl.
  - constructor.
  - apply NFUnion_NoDup; assumption.
Qed.

Lemma NFUnionAll_Forall_prime : forall rs,
  Forall (fun r => Forall prime r) rs ->
  Forall prime (NFUnionAll rs).
Proof.
  intros rs H. induction H as [|r rs Hr Hrs IH]; simpl.
  - constructor.
  - apply NFUnion_Forall_prime; assumption.
Qed.

Lemma NFUnionAll_nonempty : forall rs,
  rs <> [] -> Forall NFRowGood rs -> NFUnionAll rs <> [].
Proof.
  intros rs Hrs Hgood. destruct rs as [|r tail]; [contradiction|].
  inversion Hgood as [|? ? [Hr_ne _] _]; subst. simpl.
  intro Hnil. assert (In (hd 0 r) (NFUnion r (NFUnionAll tail))).
  { apply NFUnion_In. left. destruct r; [contradiction|simpl; auto]. }
  rewrite Hnil in H. contradiction.
Qed.

Lemma NF_concat_filter_nonempty : forall rs,
  concat (filter NFRowNonempty rs) = concat rs.
Proof.
  intros rs. induction rs as [|r rs IH]; simpl; [reflexivity|].
  destruct r as [|x xs]; simpl; rewrite ?IH; reflexivity.
Qed.

Lemma NF_value_filter_nonempty : forall rs,
  NFRowsValue (filter NFRowNonempty rs) = NFRowsValue rs.
Proof.
  intros rs. unfold NFRowsValue. induction rs as [|r rs IH]; simpl.
  - reflexivity.
  - destruct r as [|x xs]; simpl.
    + rewrite IH. destruct (fold_right Z.add 0 (map NFRowValue rs)); reflexivity.
    + rewrite IH. reflexivity.
Qed.

Lemma NF_merge_flat_perm_raw : forall rs,
  Forall (fun r => NoDup r) rs ->
  Permutation (concat rs)
    (NFUnionAll rs ++ concat (NFResidualsRaw rs)).
Proof.
  intros rs Hgood. induction Hgood as [|r rs Hr Hrs IH]; simpl.
  - constructor.
  - eapply Permutation_trans.
    + apply Permutation_app_head. exact IH.
    + rewrite !app_assoc.
      apply Permutation_app_tail.
      apply NF_union_intersection_perm.
      * exact Hr.
      * apply NFUnionAll_NoDup. exact Hrs.
Qed.

Lemma NF_merge_flat_perm : forall rs,
  Forall (fun r => NoDup r) rs ->
  Permutation (concat rs)
    (NFUnionAll rs ++ concat (NFResiduals rs)).
Proof.
  intros rs H. unfold NFResiduals. rewrite NF_concat_filter_nonempty.
  apply NF_merge_flat_perm_raw. exact H.
Qed.

Lemma NFResiduals_good : forall rs,
  Forall NFRowGood rs -> Forall NFRowGood (NFResiduals rs).
Proof.
  intros rs Hgood. unfold NFResiduals.
  apply Forall_forall. intros r Hr.
  apply filter_In in Hr as [Hr Hne].
  apply NFRowNonempty_spec in Hne.
  split; [exact Hne|].
  induction Hgood as [|a tail [Ha_ne [Ha_nd Ha_pr]] Htail IH]; simpl in Hr.
  - contradiction.
  - destruct Hr as [<- | Hr].
    + split.
      * apply NFIntersection_NoDup. exact Ha_nd.
      * apply NFIntersection_Forall_prime. exact Ha_pr.
    + specialize (IH Hr). tauto.
Qed.

Lemma NF_merge_value_raw : forall rs,
  Forall NFRowGood rs ->
  NFRowsValue rs <=
    NFRowValue (NFUnionAll rs) + NFRowsValue (NFResidualsRaw rs).
Proof.
  intros rs Hgood. induction Hgood as [|r rs [Hr_ne [Hr_nd Hr_pr]] Hrs IH]; simpl.
  - lia.
  - destruct rs as [|s tail].
    + assert (Hu : NFUnion r [] = r).
      { unfold NFUnion, NFOnly. simpl. apply app_nil_r. }
      assert (Hi_all : forall l, NFIntersection l [] = []).
      { intro l. unfold NFIntersection. induction l as [|x xs IHxs]; simpl; [reflexivity|].
        unfold NFIn. destruct (in_dec Z.eq_dec x []); [contradiction|exact IHxs]. }
      pose proof (Hi_all r) as Hi.
      cbn [NFUnionAll NFResidualsRaw]. rewrite Hu, Hi.
      unfold NFRowsValue. simpl. lia.
    + assert (Hu_good : NFRowGood (NFUnionAll (s :: tail))).
      { split.
        - apply NFUnionAll_nonempty; [discriminate|exact Hrs].
        - split.
          + apply NFUnionAll_NoDup.
            apply Forall_forall. intros q Hq.
            destruct ((proj1 (Forall_forall NFRowGood (s :: tail))) Hrs q Hq)
              as [_ [Hq_nd _]]. exact Hq_nd.
          + apply NFUnionAll_Forall_prime.
            apply Forall_forall. intros q Hq.
            destruct ((proj1 (Forall_forall NFRowGood (s :: tail))) Hrs q Hq)
              as [_ [_ Hq_pr]]. exact Hq_pr. }
      destruct Hu_good as [Hu_ne [Hu_nd Hu_pr]].
      pose proof (NF_pair_uncross_value r (NFUnionAll (s :: tail))
        Hr_ne Hu_ne Hr_nd Hu_nd Hr_pr Hu_pr) as Hpair.
      change (NFRowValue r + NFRowsValue (s :: tail) <=
        NFRowValue (NFUnion r (NFUnionAll (s :: tail))) +
        (NFRowValue (NFIntersection r (NFUnionAll (s :: tail))) +
         NFRowsValue (NFResidualsRaw (s :: tail)))).
      lia.
Qed.

Lemma NF_merge_value : forall rs,
  Forall NFRowGood rs ->
  NFRowsValue rs <=
    NFRowValue (NFUnionAll rs) + NFRowsValue (NFResiduals rs).
Proof.
  intros rs H. unfold NFResiduals. rewrite NF_value_filter_nonempty.
  apply NF_merge_value_raw. exact H.
Qed.
(* Nested rows are the canonical shape: every prime occurring in a later row
   already occurs in every preceding row. *)
Fixpoint NFNested (rs : list (list Z)) : Prop :=
  match rs with
  | [] => True
  | r :: tail =>
      (forall s, In s tail -> forall p, In p s -> In p r) /\ NFNested tail
  end.

Lemma NFUnionAll_In_iff : forall p rs,
  In p (NFUnionAll rs) <-> exists r, In r rs /\ In p r.
Proof.
  intros p rs. induction rs as [|r rs IH]; simpl.
  - split; [contradiction|intros [q [Hq _]]; contradiction].
  - rewrite NFUnion_In, IH. split.
    + intros [Hp | [q [Hq Hp]]].
      * exists r. auto.
      * exists q. auto.
    + intros [q [[<- | Hq] Hp]].
      * auto.
      * right. exists q. auto.
Qed.

Lemma NFNested_tail_in_head : forall r tail p,
  NFNested (r :: tail) ->
  In p (concat tail) -> In p r.
Proof.
  intros r tail p [Hhead _] Hp.
  apply in_concat in Hp as [s [Hs Hp]]. eauto.
Qed.

Lemma NFNested_union_head_perm : forall r tail,
  r <> [] -> NoDup r -> Forall (fun q => NoDup q) tail ->
  NFNested (r :: tail) -> Permutation (NFUnionAll (r :: tail)) r.
Proof.
  intros r tail Hr_ne Hr_nd Htail Hnest.
  apply NoDup_Permutation.
  - apply NFUnionAll_NoDup. constructor; assumption.
  - exact Hr_nd.
  - destruct Hnest as [Hhead _]. intro p. rewrite NFUnionAll_In_iff. split.
    + intros [q [Hq Hp]]. destruct Hq as [<- | Hq]; [exact Hp|].
      exact (Hhead q Hq p Hp).
    + intro Hp. exists r. split; [left; reflexivity|exact Hp].
Qed.

Lemma NFGood_concat_nil : forall rs,
  Forall NFRowGood rs -> concat rs = [] -> rs = [].
Proof.
  intros rs Hgood. destruct rs as [|r tail]; [reflexivity|].
  inversion Hgood as [|? ? [Hr_ne _] _]; subst.
  simpl. intro Hnil. apply app_eq_nil in Hnil as [Hr _]. contradiction.
Qed.

Lemma NFResiduals_flat_tail_perm : forall rs c cs,
  Forall NFRowGood rs ->
  Forall NFRowGood (c :: cs) ->
  NFNested (c :: cs) ->
  Permutation (concat rs) (concat (c :: cs)) ->
  Permutation (concat (NFResiduals rs)) (concat cs).
Proof.
  intros rs c cs Hrs Hcs Hnest Hflat.
  assert (Hrs_nd : Forall (fun r => NoDup r) rs).
  { apply Forall_forall. intros r Hr.
    destruct ((proj1 (Forall_forall NFRowGood rs)) Hrs r Hr) as [_ [Hnd _]].
    exact Hnd. }
  pose proof (NF_merge_flat_perm rs Hrs_nd) as Hmerge.
  inversion Hcs as [|? ? [Hc_ne [Hc_nd _]] Hcs_good]; subst.
  assert (Hcs_nd : Forall (fun r => NoDup r) cs).
  { apply Forall_forall. intros r Hr.
    destruct ((proj1 (Forall_forall NFRowGood cs)) Hcs_good r Hr) as [_ [Hnd _]].
    exact Hnd. }
  assert (Hu : Permutation (NFUnionAll rs) c).
  { apply NoDup_Permutation.
    - apply NFUnionAll_NoDup. exact Hrs_nd.
    - exact Hc_nd.
    - intro p. rewrite NFUnionAll_In_iff. split.
      + intros [r [Hr Hp]].
        assert (In p (concat rs)).
        { apply in_concat. exists r. auto. }
        apply (Permutation_in p Hflat) in H.
        simpl in H. apply in_app_iff in H as [Hp_c | Hp_tail]; [exact Hp_c|].
        apply NFNested_tail_in_head with (tail := cs); auto.
      + intro Hp.
        assert (In p (concat rs)).
        { apply (Permutation_in p (Permutation_sym Hflat)).
          simpl. apply in_app_iff. left. exact Hp. }
        apply in_concat in H as [r [Hr Hpr]]. exists r. auto. }
  simpl in Hflat.
  apply (Permutation_app_inv_l c).
  eapply Permutation_trans.
  - apply Permutation_app_tail. apply Permutation_sym. exact Hu.
  - eapply Permutation_trans.
    + apply Permutation_sym. exact Hmerge.
    + exact Hflat.
Qed.

Theorem NF_nested_optimal : forall canonical other,
  Forall NFRowGood canonical -> NFNested canonical ->
  Forall NFRowGood other ->
  Permutation (concat other) (concat canonical) ->
  NFRowsValue other <= NFRowsValue canonical.
Proof.
  induction canonical as [|c cs IH]; intros other Hcan Hnest Hother Hflat.
  - simpl in Hflat.
    assert (Hnil : concat other = []).
    { apply Permutation_nil. apply Permutation_sym. exact Hflat. }
    apply NFGood_concat_nil in Hnil; [subst; simpl; lia|exact Hother].
  - inversion Hcan as [|? ? Hc Hcs]; subst.
    destruct Hnest as [Hhead Hnest].
    pose proof (NF_merge_value other Hother) as Hmerge.
    assert (Hother_nd : Forall (fun r => NoDup r) other).
    { apply Forall_forall. intros r Hr.
      destruct ((proj1 (Forall_forall NFRowGood other)) Hother r Hr)
        as [_ [Hnd _]]. exact Hnd. }
    destruct Hc as [Hc_ne [Hc_nd Hc_pr]].
    assert (Hcs_nd : Forall (fun r => NoDup r) cs).
    { apply Forall_forall. intros r Hr.
      destruct ((proj1 (Forall_forall NFRowGood cs)) Hcs r Hr)
        as [_ [Hnd _]]. exact Hnd. }
    assert (Hu_perm : Permutation (NFUnionAll other) c).
    { apply NoDup_Permutation.
      - apply NFUnionAll_NoDup. exact Hother_nd.
      - exact Hc_nd.
      - intro p. rewrite NFUnionAll_In_iff. split.
        + intros [r [Hr Hp]].
          assert (In p (concat other)).
          { apply in_concat. exists r. auto. }
          apply (Permutation_in p Hflat) in H.
          simpl in H. apply in_app_iff in H as [Hp_c | Hp_tail]; [exact Hp_c|].
          apply in_concat in Hp_tail as [s [Hs Hps]].
          exact (Hhead s Hs p Hps).
        + intro Hp.
          assert (In p (concat other)).
          { apply (Permutation_in p (Permutation_sym Hflat)).
            simpl. apply in_app_iff. left. exact Hp. }
          apply in_concat in H as [r [Hr Hpr]]. exists r. auto. }
    assert (Hres_good : Forall NFRowGood (NFResiduals other)).
    { apply NFResiduals_good. exact Hother. }
    assert (Hres_flat :
      Permutation (concat (NFResiduals other)) (concat cs)).
    { apply NFResiduals_flat_tail_perm with (c := c).
      - exact Hother.
      - exact Hcan.
      - split; assumption.
      - exact Hflat. }
    specialize (IH (NFResiduals other) Hcs Hnest Hres_good Hres_flat).
    pose proof (NFRowValue_perm _ _ Hu_perm) as Hu_value.
    change (NFRowsValue other <= NFRowValue c + NFRowsValue cs).
    lia.
Qed.

Lemma NF_prime_divides_product_member : forall p l,
  prime p -> Forall prime l -> (p | NFRowProduct l) -> In p l.
Proof.
  intros p l Hp Hl. induction Hl as [|q l Hq Hl IH]; simpl.
  - intro Hdiv. apply Z.divide_1_r in Hdiv.
    pose proof (prime_ge_2 p Hp). destruct Hdiv; lia.
  - intro Hdiv. destruct (prime_mult p Hp q (NFRowProduct l) Hdiv)
      as [Hpq | Hprest].
    + left. apply prime_divisors in Hpq; auto.
      pose proof (prime_ge_2 p Hp). pose proof (prime_ge_2 q Hq).
      destruct Hpq as [Hpq | [Hpq | [Hpq | Hpq]]]; lia.
    + right. apply IH. exact Hprest.
Qed.

Lemma NF_prime_products_perm : forall a b,
  Forall prime a -> Forall prime b ->
  NFRowProduct a = NFRowProduct b -> Permutation a b.
Proof.
  intros a b Ha. revert b. induction Ha as [|p a Hp Ha IH]; intros b Hb Heq.
  - destruct b as [|q b]; [constructor|].
    inversion Hb as [|? ? Hq _]; subst. simpl in Heq.
    pose proof (prime_ge_2 q Hq). pose proof (NFRowProduct_pos b).
    assert (Forall prime b) by (inversion Hb; assumption).
    specialize (H0 H1). nia.
  - assert (Hpdiv : (p | NFRowProduct b)).
    { exists (NFRowProduct a). simpl in Heq. nia. }
    pose proof (NF_prime_divides_product_member p b Hp Hb Hpdiv) as Hpin.
    apply in_split in Hpin as [before [after Hbshape]]. subst b.
    assert (Hperm_head : Permutation (before ++ p :: after) (p :: before ++ after)).
    { apply Permutation_sym. apply Permutation_middle. }
    assert (Hbrest : Forall prime (before ++ after)).
    { apply Forall_forall. intros q Hq.
      pose proof (proj1 (Forall_forall prime (before ++ p :: after)) Hb)
        as Hbmem. apply Hbmem. apply in_app_iff in Hq. apply in_app_iff.
      destruct Hq as [Hq | Hq]; [auto|right; simpl; auto]. }
    assert (Hprod_b : NFRowProduct (before ++ p :: after) =
      p * NFRowProduct (before ++ after)).
    { apply NFRowProduct_perm in Hperm_head. simpl in Hperm_head. exact Hperm_head. }
    assert (Hcancel : NFRowProduct a = NFRowProduct (before ++ after)).
    { simpl in Heq. pose proof (prime_ge_2 p Hp). nia. }
    eapply Permutation_trans.
    + apply perm_skip. apply IH; [exact Hbrest|exact Hcancel].
    + apply Permutation_sym. exact Hperm_head.
Qed.

Lemma NF_Forall_repeat : forall (A : Type) (P : A -> Prop) x n,
  P x -> Forall P (repeat x n).
Proof. intros A P x n H. induction n; simpl; constructor; auto. Qed.

Lemma NF_product_repeat_rows : forall r n,
  NFRowProduct (concat (repeat r n)) =
  Z.pow (NFRowProduct r) (Z.of_nat n).
Proof.
  intros r n. rewrite <- Zpower_nat_Z. induction n as [|n IH]; simpl.
  - reflexivity.
  - rewrite NFRowProduct_app, IH. reflexivity.
Qed.

Lemma NF_value_repeat_rows : forall r n,
  r <> [] ->
  NFRowsValue (repeat r n) = NFRowProduct r * Z.of_nat n.
Proof.
  intros r n Hr. destruct r as [|x xs]; [contradiction|].
  unfold NFRowsValue. induction n as [|n IH]; simpl.
  - ring.
  - rewrite IH.
    change (x * NFRowProduct xs + NFRowProduct (x :: xs) * Z.of_nat n =
      x * NFRowProduct xs * Z.of_nat (S n)).
    rewrite Nat2Z.inj_succ. simpl. ring.
Qed.

Lemma NF_expand_ap : forall ap,
  Forall (fun q => SquareFree (fst q) /\ snd q > 0) ap ->
  exists rows,
    Forall NFRowGood rows /\
    NFRowProduct (concat rows) =
      fold_right Z.mul 1 (map (fun q => Z.pow (fst q) (snd q)) ap) /\
    NFRowsValue rows =
      fold_right Z.add 0 (map (fun q => fst q * snd q) ap).
Proof.
  intros ap Hap. induction Hap as [|[x w] ap [Hsq Hw] Hap IH].
  - exists []. simpl. repeat split; constructor.
  - destruct Hsq as [r [Hr_ne [Hr_nd [Hr_pr Hx]]]].
    change (x = NFRowProduct r) in Hx.
    assert (Hw0 : 0 <= w) by (simpl in Hw; lia).
    destruct IH as [tail [Htail_good [Htail_prod Htail_value]]].
    exists (repeat r (Z.to_nat w) ++ tail). repeat split.
    + apply Forall_app. split; [apply NF_Forall_repeat|exact Htail_good].
      repeat split; assumption.
    + rewrite concat_app, NFRowProduct_app, NF_product_repeat_rows,
        Htail_prod, <- Hx, (Z2Nat.id w Hw0). reflexivity.
    + rewrite NFRowsValue_app, NF_value_repeat_rows by exact Hr_ne.
      rewrite Htail_value, <- Hx, (Z2Nat.id w Hw0). simpl. ring.
Qed.

Lemma NF_factor_value_sum_nonneg : forall ap,
  Forall (fun q => SquareFree (fst q) /\ snd q > 0) ap ->
  0 <= fold_right Z.add 0 (map (fun q => fst q * snd q) ap).
Proof.
  intros ap Hap. induction Hap as [|[x w] ap [Hsq Hw] Hap IH]; simpl; [lia|].
  destruct Hsq as [r [Hr_ne [Hr_nd [Hr_pr Hx]]]].
  change (x = NFRowProduct r) in Hx.
  pose proof (NFRowProduct_nonempty r Hr_ne Hr_pr) as Hx2.
  assert (Hterm : 0 < x * w).
  { apply Z.mul_pos_pos; [rewrite Hx; lia|exact (Z.gt_lt w 0 Hw)]. }
  nia.
Qed.

Lemma NF_factor_value_sum_pos : forall ap,
  ap <> [] ->
  Forall (fun q => SquareFree (fst q) /\ snd q > 0) ap ->
  0 < fold_right Z.add 0 (map (fun q => fst q * snd q) ap).
Proof.
  intros [|[x w] ap] Hne Hap; [contradiction|].
  inversion Hap as [|? ? [Hsq Hw] Htail]; subst. simpl.
  destruct Hsq as [r [Hr_ne [Hr_nd [Hr_pr Hx]]]].
  change (x = NFRowProduct r) in Hx.
  pose proof (NFRowProduct_nonempty r Hr_ne Hr_pr) as Hx2.
  pose proof (NF_factor_value_sum_nonneg ap Htail) as Htail0.
  assert (Hterm : 0 < x * w).
  { apply Z.mul_pos_pos; [rewrite Hx; lia|exact (Z.gt_lt w 0 Hw)]. }
  nia.
Qed.

Theorem NF_valid_to_rows : forall n value,
  ValidFactorization n value ->
  exists rows,
    rows <> [] /\ Forall NFRowGood rows /\
    NFRowProduct (concat rows) = n /\ NFRowsValue rows = value.
Proof.
  intros n value [ap [Hap_ne [Hap_good [Hn Hvalue]]]].
  destruct (NF_expand_ap ap Hap_good) as [rows [Hgood [Hprod Hval]]].
  exists rows. split.
  - intro Hnil. subst rows. unfold NFRowsValue in Hval. simpl in Hprod, Hval.
    pose proof (NF_factor_value_sum_pos ap Hap_ne Hap_good). nia.
  - split; [exact Hgood|]. split; nia.
Qed.

Definition NFLayerTest (es : list Z) (k i : Z) : bool :=
  if Z_le_dec k (Znth i es 0) then true else false.

Definition NFPrimeLayer (ps es : list Z) (k : Z) : list Z :=
  map (fun i => Znth i ps 1)
    (filter (NFLayerTest es k) (Zrange 0 (Zlength ps))).

Definition NFCanonicalRows (ps es : list Z) (mx : Z) : list (list Z) :=
  map (NFPrimeLayer ps es) (Zrange 1 (mx + 1)).

Lemma NFLayerTest_spec : forall es k i,
  NFLayerTest es k i = true <-> k <= Znth i es 0.
Proof.
  intros. unfold NFLayerTest. destruct (Z_le_dec k (Znth i es 0));
    split; intros; auto; discriminate.
Qed.

Lemma NFPrimeLayer_In : forall ps es k p,
  In p (NFPrimeLayer ps es k) <->
  exists i, 0 <= i < Zlength ps /\ k <= Znth i es 0 /\
    p = Znth i ps 1.
Proof.
  intros. unfold NFPrimeLayer. rewrite in_map_iff. split.
  - intros [i [<- Hi]]. apply filter_In in Hi as [Hi Htest].
    rewrite <- In_Zrange in Hi. apply NFLayerTest_spec in Htest. eauto.
  - intros [i [Hi [He Hp]]]. exists i. split; [symmetry; exact Hp|].
    apply filter_In. split; [apply In_Zrange; exact Hi|].
    apply NFLayerTest_spec. exact He.
Qed.

Lemma NF_Znth_indices_NoDup : forall ps il,
  NoDup ps -> NoDup il ->
  Forall (fun i => 0 <= i < Zlength ps) il ->
  NoDup (map (fun i => Znth i ps 1) il).
Proof.
  intros ps il Hps Hil Hbounds. induction Hil as [|i il Hi Hil IH]; simpl.
  - constructor.
  - inversion Hbounds as [|? ? Hib Hrest]; subst. constructor.
    + intro Hin. apply in_map_iff in Hin as [j [Heq Hj]].
      pose proof ((proj1 (Forall_forall _ _)) Hrest j Hj) as Hjb.
      apply (proj1 (NoDup_nth ps 1)) with
        (i := Z.to_nat i) (j := Z.to_nat j) in Hps.
      * apply Hi. replace i with j; [exact Hj|]. symmetry.
        apply (Z2Nat.inj i j); [exact (proj1 Hib)|exact (proj1 Hjb)|exact Hps].
      * rewrite Zlength_correct in Hib.
        rewrite <- (Nat2Z.id (length ps)).
        exact (proj1 (Z2Nat.inj_lt i (Z.of_nat (length ps))
          (proj1 Hib) (Nat2Z.is_nonneg _)) (proj2 Hib)).
      * rewrite Zlength_correct in Hjb.
        rewrite <- (Nat2Z.id (length ps)).
        exact (proj1 (Z2Nat.inj_lt j (Z.of_nat (length ps))
          (proj1 Hjb) (Nat2Z.is_nonneg _)) (proj2 Hjb)).
      * unfold Znth in Heq. symmetry. exact Heq.
    + apply IH. exact Hrest.
Qed.

Lemma NFPrimeLayer_NoDup : forall ps es k,
  NoDup ps -> NoDup (NFPrimeLayer ps es k).
Proof.
  intros ps es k Hps. unfold NFPrimeLayer. apply NF_Znth_indices_NoDup.
  - exact Hps.
  - apply NoDup_filter. apply NoDup_Zrange.
  - apply Forall_forall. intros i Hi. apply filter_In in Hi as [Hi _].
    apply <- In_Zrange. exact Hi.
Qed.

Lemma NFPrimeLayer_Forall_prime : forall ps es k,
  Forall prime ps -> Forall prime (NFPrimeLayer ps es k).
Proof.
  intros ps es k Hps. apply Forall_forall. intros p Hp.
  apply NFPrimeLayer_In in Hp as [i [Hi [_ ->]]].
  apply Forall_Znth_Zlength; assumption.
Qed.

Lemma NFPrimeLayer_monotone : forall ps es k1 k2 p,
  k1 <= k2 -> In p (NFPrimeLayer ps es k2) ->
  In p (NFPrimeLayer ps es k1).
Proof.
  intros ps es k1 k2 p Hle Hp.
  apply NFPrimeLayer_In in Hp as [i [Hi [Hei Heq]]].
  apply NFPrimeLayer_In. exists i. repeat split; auto; lia.
Qed.

Lemma NFPrimeLayers_range_aux_nested : forall ps es low n,
  NFNested (map (NFPrimeLayer ps es) (Zrange_aux low n)).
Proof.
  intros ps es low n. revert low. induction n as [|n IH]; intros low; simpl; auto.
  split.
  - intros row Hrow p Hp. apply in_map_iff in Hrow as [k2 [<- Hk2]].
    apply NFPrimeLayer_monotone with (k2 := k2); [|exact Hp].
    apply In_Zrange_aux in Hk2. lia.
  - apply IH.
Qed.

Lemma NFCanonicalRows_nested : forall ps es mx,
  NFNested (NFCanonicalRows ps es mx).
Proof.
  intros ps es mx. unfold NFCanonicalRows, Zrange.
  apply NFPrimeLayers_range_aux_nested.
Qed.

Lemma NFPrimeFactorization_nonempty : forall orig ps es,
  PrimeFactorization orig ps es -> ps <> [].
Proof.
  intros orig ps es [Horig [_ [_ Hfactor]]]. intro Hnil. subst ps.
  unfold FactorPower in Hfactor. simpl in Hfactor. nia.
Qed.

Lemma NFMaximumExponent_witness : forall es mx,
  es <> [] -> MaximumExponent es mx ->
  0 <= mx <= 30 /\ exists i, 0 <= i < Zlength es /\ Znth i es 0 = mx.
Proof.
  intros es mx Hes [_ [Hmx [_ [_ Hwit]]]].
  assert (0 < Zlength es).
  { rewrite Zlength_correct. destruct es; [contradiction|simpl; lia]. }
  specialize (Hwit H). destruct Hwit as [i [Hi He]].
  split; [exact Hmx|eauto].
Qed.

Lemma NFCanonicalRows_good : forall orig ps es mx,
  PrimeFactorization orig ps es -> MaximumExponent es mx ->
  Forall NFRowGood (NFCanonicalRows ps es mx).
Proof.
  intros orig ps es mx Hpf Hmax.
  destruct Hpf as [Horig [Hcap [Hprofile Hfactor]]].
  destruct Hprofile as [Hlen [Hnd [Hprime Hexp]]].
  assert (Hps_ne : ps <> []).
  { apply (NFPrimeFactorization_nonempty orig ps es).
    exact (conj Horig (conj Hcap
      (conj (conj Hlen (conj Hnd (conj Hprime Hexp))) Hfactor))). }
  assert (Hes_ne : es <> []).
  { intro Hes. subst es. rewrite Zlength_nil in Hlen.
    apply Zlength_nil_inv in Hlen. contradiction. }
  destruct (NFMaximumExponent_witness es mx Hes_ne Hmax)
    as [Hmx [im [Him Hem]]].
  assert (Hmx1 : 1 <= mx).
  { specialize (Hexp im Him). rewrite Hem in Hexp. lia. }
  unfold NFCanonicalRows. apply Forall_forall. intros row Hrow.
  apply in_map_iff in Hrow as [k [<- Hk]].
  apply <- In_Zrange in Hk. repeat split.
  - intro Hnil.
    assert (In (Znth im ps 1) (NFPrimeLayer ps es k)).
    { apply NFPrimeLayer_In. exists im. repeat split; auto; lia. }
    rewrite Hnil in H. contradiction.
  - apply NFPrimeLayer_NoDup. exact Hnd.
  - apply NFPrimeLayer_Forall_prime. exact Hprime.
Qed.

Lemma NF_product_filter_layer : forall ps es k il,
  NFRowProduct
    (map (fun i => Znth i ps 1) (filter (NFLayerTest es k) il)) =
  fold_right Z.mul 1
    (map (fun i => if Z_le_dec k (Znth i es 0)
                   then Znth i ps 1 else 1) il).
Proof.
  intros ps es k il. unfold NFRowProduct.
  induction il as [|i il IH]; cbn [filter map fold_right]; [reflexivity|].
  destruct (Z_le_dec k (Znth i es 0)) as [Hle|Hnle].
  - assert (Ht : NFLayerTest es k i = true).
    { apply NFLayerTest_spec. exact Hle. }
    rewrite Ht. cbn [filter map fold_right]. rewrite IH. reflexivity.
  - assert (Ht : NFLayerTest es k i = false).
    { unfold NFLayerTest. destruct (Z_le_dec k (Znth i es 0)) as [Hle'|Hnle'];
        [exfalso; apply Hnle; exact Hle'|reflexivity]. }
    rewrite Ht. cbn [filter map fold_right]. rewrite IH, Z.mul_1_l. reflexivity.
Qed.

Lemma NFPrimeLayer_value : forall ps es k,
  NFPrimeLayer ps es k <> [] ->
  NFRowValue (NFPrimeLayer ps es k) = LayerValue ps es k.
Proof.
  intros ps es k Hne. rewrite NFRowValue_nonempty by exact Hne.
  unfold NFPrimeLayer, LayerValue, LayerPrefixValue.
  apply NF_product_filter_layer.
Qed.

Lemma NF_fold_add_map : forall (A : Type) (f : A -> Z) l,
  fold_right Z.add 0 (map f l) =
  fold_right (fun x acc => f x + acc) 0 l.
Proof. intros A f l. induction l; simpl; [reflexivity|]. rewrite IHl. reflexivity. Qed.

Lemma NFCanonicalRows_value : forall orig ps es mx,
  PrimeFactorization orig ps es -> MaximumExponent es mx ->
  NFRowsValue (NFCanonicalRows ps es mx) =
    sum_range 1 mx (LayerValue ps es).
Proof.
  intros orig ps es mx Hpf Hmax.
  pose proof (NFCanonicalRows_good orig ps es mx Hpf Hmax) as Hgood.
  unfold NFCanonicalRows, NFRowsValue.
  rewrite map_map, NF_fold_add_map. unfold sum_range. rewrite sum_range_unfold.
  apply fold_Zsum_ext_in. intros k Hk.
  apply NFPrimeLayer_value.
  apply (proj1 (Forall_forall NFRowGood
    (map (NFPrimeLayer ps es) (Zrange 1 (mx + 1)))))
    with (x := NFPrimeLayer ps es k) in Hgood.
  - unfold NFRowGood in Hgood. exact (proj1 Hgood).
  - apply in_map. exact Hk.
Qed.

Lemma NFRowProduct_concat : forall rows,
  NFRowProduct (concat rows) =
  fold_right Z.mul 1 (map NFRowProduct rows).
Proof.
  intros rows. induction rows as [|r rows IH]; simpl; [reflexivity|].
  rewrite NFRowProduct_app, IH. reflexivity.
Qed.

Lemma NF_fold_mul_pointwise : forall (A : Type) (l : list A)
    (f g : A -> Z),
  fold_right Z.mul 1 (map (fun x => f x * g x) l) =
  fold_right Z.mul 1 (map f l) * fold_right Z.mul 1 (map g l).
Proof.
  intros A l f g. induction l as [|x l IH]; simpl; [ring|].
  rewrite IH. ring.
Qed.

Lemma NF_fold_matrix : forall (A B : Type) (xs : list A) (ys : list B)
    (entry : A -> B -> Z),
  fold_right Z.mul 1
    (map (fun y => fold_right Z.mul 1 (map (fun x => entry x y) xs)) ys) =
  fold_right Z.mul 1
    (map (fun x => fold_right Z.mul 1 (map (entry x) ys)) xs).
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros ys entry; simpl.
  - induction ys; simpl; [reflexivity|]. rewrite IHys. ring.
  - rewrite <- IH.
    rewrite (NF_fold_mul_pointwise B ys
      (entry x)
      (fun y => fold_right Z.mul 1 (map (fun z => entry z y) xs))).
    reflexivity.
Qed.

Lemma NF_fold_mul_app : forall a b,
  fold_right Z.mul 1 (a ++ b) =
  fold_right Z.mul 1 a * fold_right Z.mul 1 b.
Proof.
  intros a b. induction a; simpl.
  - destruct (fold_right Z.mul 1 b); reflexivity.
  - rewrite IHa, Z.mul_assoc. reflexivity.
Qed.

Lemma NF_fold_mul_ext_in : forall (A : Type) (l : list A) (f g : A -> Z),
  (forall x, In x l -> f x = g x) ->
  fold_right Z.mul 1 (map f l) = fold_right Z.mul 1 (map g l).
Proof.
  intros A l. induction l as [|x l IH]; intros f g Hext; simpl; [reflexivity|].
  rewrite (Hext x) by (left; reflexivity).
  rewrite (IH f g); [reflexivity|].
  intros y Hy. apply Hext. right. exact Hy.
Qed.

Lemma NF_threshold_true_aux : forall p low n e,
  low + Z.of_nat n <= e + 1 ->
  fold_right Z.mul 1
    (map (fun k => if Z_le_dec k e then p else 1) (Zrange_aux low n)) =
  Z.pow p (Z.of_nat n).
Proof.
  intros p low n. revert low. induction n as [|n IH]; intros low e Hbound;
    cbn [Zrange_aux map fold_right].
  - reflexivity.
  - destruct (Z_le_dec low e); [|lia].
    rewrite IH by (rewrite Nat2Z.inj_succ in Hbound; lia).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. ring.
Qed.

Lemma NF_threshold_false_aux : forall p low n e,
  e < low ->
  fold_right Z.mul 1
    (map (fun k => if Z_le_dec k e then p else 1) (Zrange_aux low n)) = 1.
Proof.
  intros p low n. revert low. induction n as [|n IH]; intros low e Hlt;
    cbn [Zrange_aux map fold_right]; [reflexivity|].
  destruct (Z_le_dec low e); [lia|]. rewrite IH by lia. reflexivity.
Qed.

Lemma NF_fold_threshold_range : forall p mx e,
  0 <= e <= mx ->
  fold_right Z.mul 1
    (map (fun k => if Z_le_dec k e then p else 1)
      (Zrange 1 (mx + 1))) = Z.pow p e.
Proof.
  intros p mx e He.
  unfold Zrange. replace (mx + 1 - 1) with mx by ring.
  assert (Hnat : Z.to_nat mx =
      (Z.to_nat e + Z.to_nat (mx - e))%nat).
  { rewrite <- Z2Nat.inj_add by lia. f_equal. lia. }
  rewrite Hnat, Zrange_aux_app, map_app, NF_fold_mul_app.
  rewrite NF_threshold_true_aux.
  2: rewrite Z2Nat.id by lia; lia.
  rewrite NF_threshold_false_aux.
  2: rewrite Z2Nat.id by lia; lia.
  rewrite Z2Nat.id by lia. ring.
Qed.

Lemma NF_layer_product_as_entries : forall ps es k il,
  NFRowProduct
    (map (fun i => Znth i ps 1) (filter (NFLayerTest es k) il)) =
  fold_right Z.mul 1
    (map (fun i => if Z_le_dec k (Znth i es 0)
                   then Znth i ps 1 else 1) il).
Proof. apply NF_product_filter_layer. Qed.

Lemma NFCanonicalRows_product : forall orig ps es mx,
  PrimeFactorization orig ps es -> MaximumExponent es mx ->
  NFRowProduct (concat (NFCanonicalRows ps es mx)) = orig.
Proof.
  intros orig ps es mx Hpf Hmax.
  destruct Hpf as [Horig [Hcap [Hprofile Hfactor]]].
  destruct Hprofile as [Hlen [Hnd [Hprime Hexp]]].
  assert (Hps_ne : ps <> []).
  { apply (NFPrimeFactorization_nonempty orig ps es).
    exact (conj Horig (conj Hcap
      (conj (conj Hlen (conj Hnd (conj Hprime Hexp))) Hfactor))). }
  assert (Hes_ne : es <> []).
  { intro Hes. subst es. rewrite Zlength_nil in Hlen.
    apply Zlength_nil_inv in Hlen. contradiction. }
  destruct (NFMaximumExponent_witness es mx Hes_ne Hmax)
    as [Hmx [im [Him Hem]]].
  assert (Hmx1 : 1 <= mx).
  { specialize (Hexp im Him). rewrite Hem in Hexp. lia. }
  rewrite NFRowProduct_concat. unfold NFCanonicalRows.
  rewrite map_map.
  change (fold_right Z.mul 1
    (map (fun k => NFRowProduct (NFPrimeLayer ps es k))
      (Zrange 1 (mx + 1))) = orig).
  unfold NFPrimeLayer.
  set (indices := Zrange 0 (Zlength ps)).
  assert (Hentry : forall k,
    NFRowProduct
      (map (fun i => Znth i ps 1) (filter (NFLayerTest es k) indices)) =
    fold_right Z.mul 1
      (map (fun i => if Z_le_dec k (Znth i es 0)
                     then Znth i ps 1 else 1) indices)).
  { intro k. apply NF_layer_product_as_entries. }
  erewrite NF_fold_mul_ext_in.
  2: intros k Hk; apply Hentry.
  rewrite (NF_fold_matrix Z Z indices (Zrange 1 (mx + 1))
    (fun i k => if Z_le_dec k (Znth i es 0)
                then Znth i ps 1 else 1)).
  assert (Hexponents : forall i, In i indices ->
    0 <= Znth i es 0 <= mx).
  { intros i Hi. unfold indices in Hi. apply <- In_Zrange in Hi.
    assert (Hi_es : 0 <= i < Zlength es) by lia.
    specialize (Hexp i Hi_es).
    destruct Hmax as [_ [_ [Hupper _]]]. specialize (Hupper i Hi_es). lia. }
  erewrite NF_fold_mul_ext_in.
  2: { intros i Hi. apply NF_fold_threshold_range. apply Hexponents. exact Hi. }
  unfold indices, FactorPower in Hfactor. symmetry. exact Hfactor.
Qed.

Lemma NF_concat_Forall_prime : forall rows,
  Forall NFRowGood rows -> Forall prime (concat rows).
Proof.
  intros rows H. induction H as [|r rows [_ [_ Hr]] Hrows IH]; simpl.
  - constructor.
  - apply Forall_app. auto.
Qed.

Lemma NF_rows_unit_product : forall rows,
  fold_right Z.mul 1
    (map (fun q => Z.pow (fst q) (snd q))
      (map (fun r => (NFRowProduct r, 1)) rows)) =
  NFRowProduct (concat rows).
Proof.
  intros rows. induction rows as [|r rows IH]; cbn [map fold_right concat].
  - reflexivity.
  - rewrite Z.pow_1_r, NFRowProduct_app, IH. reflexivity.
Qed.

Lemma NF_rows_unit_value : forall rows,
  Forall NFRowGood rows ->
  fold_right Z.add 0
    (map (fun q => fst q * snd q)
      (map (fun r => (NFRowProduct r, 1)) rows)) =
  fold_right Z.add 0 (map NFRowValue rows).
Proof.
  intros rows Hgood. induction Hgood as [|r rows [Hr_ne Hr_rest] Hgood IH];
    cbn [map fold_right].
  - reflexivity.
  - rewrite Z.mul_1_r, NFRowValue_nonempty by exact Hr_ne.
    rewrite IH. reflexivity.
Qed.

Lemma NF_good_rows_valid : forall rows n value,
  rows <> [] -> Forall NFRowGood rows ->
  NFRowProduct (concat rows) = n -> NFRowsValue rows = value ->
  ValidFactorization n value.
Proof.
  intros rows n value Hne Hgood Hprod Hvalue.
  exists (map (fun r => (NFRowProduct r, 1)) rows). repeat split.
  - intro Hnil. apply map_eq_nil in Hnil. contradiction.
  - apply Forall_forall. intros q Hq.
    apply in_map_iff in Hq as [r [<- Hr]]. simpl.
    destruct ((proj1 (Forall_forall NFRowGood rows)) Hgood r Hr)
      as [Hr_ne [Hr_nd Hr_pr]]. split; [|lia].
    exists r. repeat split; auto.
  - rewrite NF_rows_unit_product. symmetry. exact Hprod.
  - rewrite NF_rows_unit_value by exact Hgood.
    unfold NFRowsValue in Hvalue. symmetry. exact Hvalue.
Qed.

Lemma NFCanonicalRows_nonempty : forall orig ps es mx,
  PrimeFactorization orig ps es -> MaximumExponent es mx ->
  NFCanonicalRows ps es mx <> [].
Proof.
  intros orig ps es mx Hpf Hmax.
  pose proof (NFCanonicalRows_good orig ps es mx Hpf Hmax) as Hgood.
  intro Hnil. subst.
  assert (Hps_ne := NFPrimeFactorization_nonempty orig ps es Hpf).
  destruct Hpf as [_ [_ [[Hlen [_ [_ Hexp]]] _]]].
  assert (Hes_ne : es <> []).
  { intro Hes. subst. rewrite Zlength_nil in Hlen.
    apply Zlength_nil_inv in Hlen. contradiction. }
  destruct (NFMaximumExponent_witness es mx Hes_ne Hmax)
    as [_ [i [Hi He]]]. specialize (Hexp i Hi). rewrite He in Hexp.
  unfold NFCanonicalRows in Hnil. apply map_eq_nil in Hnil.
  unfold Zrange in Hnil. simpl in Hnil.
  replace (mx + 1 - 1) with mx in Hnil by ring.
  assert (0 < Z.to_nat mx)%nat.
  { exact (proj1 (Z2Nat.inj_lt 0 mx ltac:(lia) ltac:(lia)) ltac:(lia)). }
  destruct (Z.to_nat mx) as [|m].
  - lia.
  - simpl in Hnil. discriminate.
Qed.

Theorem NF_layer_answer_valid : forall orig ps es mx,
  PrimeFactorization orig ps es -> MaximumExponent es mx ->
  ValidFactorization orig (sum_range 1 mx (LayerValue ps es)).
Proof.
  intros orig ps es mx Hpf Hmax.
  apply NF_good_rows_valid with (rows := NFCanonicalRows ps es mx).
  - apply NFCanonicalRows_nonempty with (orig := orig); assumption.
  - apply NFCanonicalRows_good with (orig := orig); assumption.
  - apply NFCanonicalRows_product with (orig := orig); assumption.
  - apply NFCanonicalRows_value with (orig := orig); assumption.
Qed.

Theorem NF_layer_answer_maximal : forall orig ps es mx other_value,
  PrimeFactorization orig ps es -> MaximumExponent es mx ->
  ValidFactorization orig other_value ->
  other_value <= sum_range 1 mx (LayerValue ps es).
Proof.
  intros orig ps es mx other_value Hpf Hmax Hvalid.
  destruct (NF_valid_to_rows orig other_value Hvalid)
    as [other [_ [Hother_good [Hother_prod Hother_value]]]].
  set (canonical := NFCanonicalRows ps es mx).
  assert (Hcan_good : Forall NFRowGood canonical).
  { unfold canonical. apply NFCanonicalRows_good with (orig := orig); assumption. }
  assert (Hcan_nested : NFNested canonical).
  { unfold canonical. apply NFCanonicalRows_nested. }
  assert (Hcan_prod : NFRowProduct (concat canonical) = orig).
  { unfold canonical. apply NFCanonicalRows_product with (orig := orig); assumption. }
  assert (Hother_pr : Forall prime (concat other)).
  { apply NF_concat_Forall_prime. exact Hother_good. }
  assert (Hcan_pr : Forall prime (concat canonical)).
  { apply NF_concat_Forall_prime. exact Hcan_good. }
  assert (Hperm : Permutation (concat other) (concat canonical)).
  { apply NF_prime_products_perm; auto. nia. }
  pose proof (NF_nested_optimal canonical other Hcan_good Hcan_nested
    Hother_good Hperm) as Hopt.
  pose proof (NFCanonicalRows_value orig ps es mx Hpf Hmax) as Hcan_value.
  change (NFRowsValue canonical =
    sum_range 1 mx (LayerValue ps es)) in Hcan_value.
  rewrite Hother_value, Hcan_value in Hopt. exact Hopt.
Qed.

Definition LayerOptimalityCertificate
    (orig : Z) (ps es : list Z) (mx : Z) : Prop :=
  Spec orig (sum_range 1 mx (LayerValue ps es)).

Theorem LayerOptimalityCertificate_proved : forall orig ps es mx,
  PrimeFactorization orig ps es -> MaximumExponent es mx ->
  LayerOptimalityCertificate orig ps es mx.
Proof.
  intros orig ps es mx Hpf Hmax.
  unfold LayerOptimalityCertificate, Spec, max_value_of_subset.
  exists (sum_range 1 mx (LayerValue ps es)). split; [split|reflexivity].
  - apply NF_layer_answer_valid; assumption.
  - intros b Hb. apply NF_layer_answer_maximal with
      (orig := orig) (ps := ps) (es := es) (mx := mx); assumption.
Qed.

Theorem LayerOptimalityCertificate_spec : forall orig ps es mx total,
  LayerOptimalityCertificate orig ps es mx ->
  total = sum_range 1 mx (LayerValue ps es) -> Spec orig total.
Proof. intros. subst. exact H. Qed.

Require Import Coq.ZArith.Zpow_facts.
Require Import Coq.ZArith.Zquot.
Require Import Coq.ZArith.Zwf.
Lemma prime_divisor_exists__extraction_start :
  forall n, 1 < n -> exists p, prime p /\ (p | n).
Proof.
  intros n Hn.
  generalize Hn.
  pattern n; apply Z_lt_induction; try lia.
  clear n Hn; intros n IH Hn.
  destruct (prime_dec n) as [Hp | Hnp].
  - exists n; split; [exact Hp | exists 1; ring].
  - destruct (not_prime_divide n Hn Hnp) as (q & Hq & Hqdiv).
    destruct (IH q ltac:(lia) ltac:(lia)) as (p & Hp & Hpdiv).
    exists p; split; [exact Hp |].
    destruct Hpdiv as (a & Ha); destruct Hqdiv as (b & Hb).
    exists (a * b). subst. ring.
Qed.
Lemma scan_divisor_is_prime__extraction_start :
  forall rem d,
    2 <= d ->
    (forall p, prime p -> 2 <= p < d -> ~ (p | rem)) ->
    (d | rem) ->
    prime d.
Proof.
  intros rem d Hd Hscan Hdrem.
  destruct (prime_dec d) as [Hp | Hnp]; [exact Hp |].
  exfalso.
  destruct (prime_divisor_exists__extraction_start d ltac:(lia))
    as (p & Hp & Hpdiv).
  assert (Hp_le : p <= d).
  { apply Zdivide_le; [pose proof (prime_ge_2 p Hp); lia | lia | exact Hpdiv]. }
  assert (Hp_ne : p <> d).
  { intro Heq. subst p. apply Hnp. exact Hp. }
  specialize (Hscan p Hp ltac:(split; [apply prime_ge_2; exact Hp | lia])).
  apply Hscan.
  destruct Hpdiv as (a & Ha); destruct Hdrem as (b & Hb).
  exists (a * b). subst. ring.
Qed.
Lemma factor_scan_divisible_starts_extract__extraction_start :
  forall orig rem d ps es,
    FactorScan orig rem d ps es ->
    Z.rem rem d = 0 ->
    d * d <= rem ->
    ExtractionScale rem d 0 /\ FactorExtract orig rem d ps es 0.
Proof.
  intros orig rem d ps es Hscan Hmod Hsq.
  unfold FactorScan in Hscan.
  destruct Hscan as
    (Horig & Hrem & Hd & Hcap & Hprof & Hlt & Heq & Hscan).
  assert (Hdrem : (d | rem)).
  { apply (proj1 (Zrem_divides rem d)) in Hmod.
    destruct Hmod as (q & Hq). exists q. rewrite Z.mul_comm. exact Hq. }
  assert (Hprime : prime d).
  { apply (scan_divisor_is_prime__extraction_start rem d); try lia; assumption. }
  split.
  - unfold ExtractionScale. simpl. nia.
  - unfold PrimeExponentProfile in Hprof.
    destruct Hprof as (Hplen & Hpnd & Hpprime & Hpexp).
    unfold FactorExtract.
    repeat apply conj.
    all: try assumption.
    all: simpl; try ring; try lia.
    all: try (apply Hpexp; assumption).
    all: try solve [auto with zarith].
Qed.
Lemma length_Zrange_aux__extraction_start :
  forall low k, length (Zrange_aux low k) = k.
Proof.
  intros low k; revert low; induction k; intros; simpl; congruence.
Qed.
Lemma fold_mul_ge_pow2__extraction_start :
  forall l,
    Forall (fun x => 2 <= x) l ->
    2 ^ Z.of_nat (length l) <= fold_right Z.mul 1 l.
Proof.
  intros l H; induction H.
  - simpl. reflexivity.
  - change
      (2 ^ Z.of_nat (S (length l)) <=
       x * fold_right Z.mul 1 l).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    assert (0 <= 2 ^ Z.of_nat (length l)) by
      (apply Z.pow_nonneg; lia).
    nia.
Qed.
Lemma FactorPower_lower_bound__extraction_start :
  forall ps es,
    PrimeExponentProfile ps es ->
    2 ^ Zlength ps <= FactorPower ps es.
Proof.
  intros ps es Hprof.
  destruct Hprof as (Hlen & Hnodup & Hprimes & Hexps).
  unfold FactorPower.
  apply Z.le_trans with
    (2 ^ Z.of_nat (length (Zrange 0 (Zlength ps)))).
  - unfold Zrange. rewrite length_Zrange_aux__extraction_start.
    replace (Zlength ps - 0) with (Zlength ps) by lia.
    rewrite Z2Nat.id by (apply Zlength_nonneg). reflexivity.
  - rewrite <- (length_map
      (fun i : Z => Z.pow (Znth i ps 1) (Znth i es 0))
      (Zrange 0 (Zlength ps))).
    apply fold_mul_ge_pow2__extraction_start.
    apply Forall_forall. intros x Hxin.
    apply in_map_iff in Hxin.
    destruct Hxin as (i & <- & Hi).
    apply <- In_Zrange in Hi.
    pose proof (proj1 (Forall_Znth prime 1 ps) Hprimes i Hi) as Hpi.
    specialize (Hexps i). rewrite <- Hlen in Hexps.
    specialize (Hexps Hi).
    apply Z.le_trans with (Z.pow 2 1); [reflexivity |].
    apply Z.le_trans with (Z.pow (Znth i ps 1) 1).
    + apply Zpower_le_monotone3; [lia |].
      split; [lia | apply prime_ge_2; exact Hpi].
    + apply Zpower_le_monotone.
      * pose proof (prime_ge_2 _ Hpi). lia.
      * lia.
Qed.
Lemma FactorPower_positive__extraction_start :
  forall ps es,
    PrimeExponentProfile ps es ->
    1 <= FactorPower ps es.
Proof.
  intros ps es Hprof.
  pose proof (FactorPower_lower_bound__extraction_start ps es Hprof).
  pose proof (Z.pow_pos_nonneg 2 (Zlength ps)
    ltac:(lia) ltac:(apply Zlength_nonneg)).
  nia.
Qed.
Lemma factor_extract_divide_step__extraction_start :
  forall orig rem d ps es e,
    FactorExtract orig rem d ps es e ->
    ExtractionScale rem d e ->
    Z.rem rem d = 0 ->
    ExtractionScale (rem ÷ d) d (e + 1) /\
    FactorExtract orig (rem ÷ d) d ps es (e + 1).
Proof.
  intros orig rem d ps es e Hext Hscale Hmod.
  unfold FactorExtract in Hext.
  destruct Hext as
    (Horig & Hremb & Hd & Hcap & Hprof & Hlt & Hprime & He & Heq & Hscan & Hzero).
  assert (Hquot : rem = d * (rem ÷ d)).
  { apply (proj2 (Z_quot_exact_full rem d)). exact Hmod. }
  assert (Hqpos : 1 <= rem ÷ d) by nia.
  assert (Hqbound : rem ÷ d <= orig) by nia.
  assert (Hfpos : 1 <= FactorPower ps es).
  { apply FactorPower_positive__extraction_start. exact Hprof. }
  assert (Henext : e + 1 <= 30).
  { destruct (Z_le_gt_dec (e + 1) 30); [assumption |].
    assert (e = 30) by lia. subst e.
    assert (Hdpow : 1073741824 <= Z.pow d 30).
    { change (Z.pow 2 30 <= Z.pow d 30).
      apply Zpower_le_monotone3; [lia |]. split; lia. }
    nia. }
  split.
  - unfold ExtractionScale in *.
    replace (e + 1) with (Z.succ e) by lia.
    rewrite Z.pow_succ_r by lia. nia.
  - unfold FactorExtract.
    split; [exact Horig |].
    split; [split; lia |].
    split; [exact Hd |].
    split; [exact Hcap |].
    split; [exact Hprof |].
    split; [exact Hlt |].
    split; [exact Hprime |].
    split; [lia |].
    split.
    + replace (e + 1) with (Z.succ e) by lia.
      rewrite Z.pow_succ_r by lia. nia.
    + split.
      * intros p Hp Hprange Hpdiv.
        apply (Hscan p Hp Hprange).
        destruct Hpdiv as (a & Ha). exists (d * a).
        rewrite Hquot, Ha. ring.
      * intros Hz. lia.
Qed.
Lemma replace_Znth_last_increment__extraction_start : forall (es : list Z) e,
  replace_Znth (Zlength es) (Znth (Zlength es) (es ++ [e]) 0 + 1)
    (es ++ [e]) = es ++ [e + 1].
Proof.
  intros es e.
  rewrite app_Znth2 by lia.
  replace (Zlength es - Zlength es) with 0 by lia.
  rewrite Znth0_cons.
  rewrite replace_Znth_app_r by lia.
  rewrite replace_Znth_nothing by lia.
  replace (Zlength es - Zlength es) with 0 by lia.
  reflexivity.
Qed.
Lemma prime_divisor_exists__scan_completion :
  forall n, 1 < n -> exists p, prime p /\ (p | n).
Proof.
  intros n.
  induction n as [n IH] using (well_founded_induction (Zwf_well_founded 1)).
  intros Hn.
  destruct (prime_dec n) as [Hp | Hnp].
  - exists n. split; [exact Hp | exists 1; ring].
  - destruct (not_prime_divide n Hn Hnp) as [a [[Ha1 Han] Hadiv]].
    destruct (IH a ltac:(unfold Zwf; lia) Ha1) as [p [Hp Hpa]].
    exists p. split; [exact Hp |].
    destruct Hpa as [u Hu].
    destruct Hadiv as [v Hv].
    exists (u * v). nia.
Qed.
Lemma scan_divisor_is_prime__scan_completion :
  forall rem d,
    2 <= d ->
    (forall p, prime p -> 2 <= p < d -> ~ (p | rem)) ->
    (d | rem) ->
    prime d.
Proof.
  intros rem d Hd Hscan Hdrem.
  destruct (prime_dec d) as [Hp | Hnp]; [exact Hp |].
  exfalso.
  destruct (prime_divisor_exists__scan_completion d ltac:(lia))
    as (p & Hp & Hpdiv).
  assert (Hp_le : p <= d).
  { apply Zdivide_le; [pose proof (prime_ge_2 p Hp); lia | lia | exact Hpdiv]. }
  assert (Hp_ne : p <> d).
  { intro Heq. subst p. apply Hnp. exact Hp. }
  specialize (Hscan p Hp ltac:(split; [apply prime_ge_2; exact Hp | lia])).
  apply Hscan.
  destruct Hpdiv as (a & Ha); destruct Hdrem as (b & Hb).
  exists (a * b). subst. ring.
Qed.
Lemma fold_mul_app__scan_completion :
  forall l1 l2,
    fold_right Z.mul 1 (l1 ++ l2) =
    fold_right Z.mul 1 l1 * fold_right Z.mul 1 l2.
Proof.
  induction l1 as [|x l1 IH]; intros l2.
  - change (fold_right Z.mul 1 l2 = 1 * fold_right Z.mul 1 l2).
    ring.
  - simpl. rewrite IH. ring.
Qed.
Lemma Zrange_zero_succ__scan_completion :
  forall k, 0 <= k -> Zrange 0 (k + 1) = Zrange 0 k ++ [k].
Proof.
  intros k Hk. unfold Zrange.
  replace (Z.to_nat (k + 1 - 0)) with (Z.to_nat (k - 0) + 1)%nat by lia.
  rewrite Zrange_aux_app. simpl.
  replace (k - 0) with k by lia.
  rewrite Z2Nat.id by lia.
  reflexivity.
Qed.
Lemma FactorPower_app_single__scan_completion :
  forall ps es p e,
    Zlength ps = Zlength es ->
    FactorPower (ps ++ [p]) (es ++ [e]) =
    FactorPower ps es * Z.pow p e.
Proof.
  intros ps es p e Hlen.
  unfold FactorPower.
  rewrite Zlength_app_cons, Zrange_zero_succ__scan_completion
    by (pose proof (Zlength_nonneg ps); lia).
  rewrite map_app, fold_mul_app__scan_completion. simpl.
  f_equal.
  - apply f_equal.
    apply map_ext_in. intros i Hi.
    apply <- In_Zrange in Hi.
    rewrite !app_Znth1 by lia. reflexivity.
  - rewrite !app_Znth2 by lia.
    rewrite Hlen. replace (Zlength es - Zlength es) with 0 by lia.
    replace (Zlength ps - Zlength ps) with 0 by lia.
    rewrite !Znth0_cons. ring.
Qed.
Lemma length_Zrange_aux__scan_completion :
  forall low k, length (Zrange_aux low k) = k.
Proof.
  intros low k; revert low; induction k; intros; simpl; congruence.
Qed.
Lemma fold_mul_ge_pow2__scan_completion :
  forall l,
    Forall (fun x => 2 <= x) l ->
    2 ^ Z.of_nat (length l) <= fold_right Z.mul 1 l.
Proof.
  intros l H; induction H.
  - simpl. reflexivity.
  - change
      (2 ^ Z.of_nat (S (length l)) <=
       x * fold_right Z.mul 1 l).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    assert (0 <= 2 ^ Z.of_nat (length l)) by
      (apply Z.pow_nonneg; lia).
    nia.
Qed.
Lemma FactorPower_lower_bound__scan_completion :
  forall ps es,
    PrimeExponentProfile ps es ->
    2 ^ Zlength ps <= FactorPower ps es.
Proof.
  intros ps es Hprof.
  destruct Hprof as (Hlen & Hnodup & Hprimes & Hexps).
  unfold FactorPower.
  apply Z.le_trans with
    (2 ^ Z.of_nat (length (Zrange 0 (Zlength ps)))).
  - unfold Zrange. rewrite length_Zrange_aux__scan_completion.
    replace (Zlength ps - 0) with (Zlength ps) by lia.
    rewrite Z2Nat.id by (apply Zlength_nonneg). reflexivity.
  - rewrite <- (length_map
      (fun i : Z => Z.pow (Znth i ps 1) (Znth i es 0))
      (Zrange 0 (Zlength ps))).
    apply fold_mul_ge_pow2__scan_completion.
    apply Forall_forall. intros x Hxin.
    apply in_map_iff in Hxin.
    destruct Hxin as (i & <- & Hi).
    apply <- In_Zrange in Hi.
    pose proof (proj1 (Forall_Znth prime 1 ps) Hprimes i Hi) as Hpi.
    specialize (Hexps i). rewrite <- Hlen in Hexps.
    specialize (Hexps Hi).
    apply Z.le_trans with (Z.pow 2 1); [reflexivity |].
    apply Z.le_trans with (Z.pow (Znth i ps 1) 1).
    + apply Zpower_le_monotone3; [lia |].
      split; [lia | apply prime_ge_2; exact Hpi].
    + apply Zpower_le_monotone.
      * pose proof (prime_ge_2 _ Hpi). lia.
      * lia.
Qed.
Lemma FactorPower_positive__scan_completion :
  forall ps es,
    PrimeExponentProfile ps es ->
    1 <= FactorPower ps es.
Proof.
  intros ps es Hprof.
  pose proof (FactorPower_lower_bound__scan_completion ps es Hprof).
  pose proof (Z.pow_pos_nonneg 2 (Zlength ps)
    ltac:(lia) ltac:(apply Zlength_nonneg)).
  nia.
Qed.
Lemma PrimeExponentProfile_app_single__scan_completion :
  forall ps es p e,
    PrimeExponentProfile ps es ->
    Forall (fun q => 2 <= q < p) ps ->
    prime p ->
    1 <= e <= 30 ->
    PrimeExponentProfile (ps ++ [p]) (es ++ [e]).
Proof.
  intros ps es p e Hprof Hlt Hp He.
  destruct Hprof as (Hlen & Hnodup & Hprimes & Hexps).
  unfold PrimeExponentProfile.
  split.
  - rewrite !Zlength_app_cons. lia.
  - split.
    + apply NoDup_app.
      * exact Hnodup.
      * constructor; [simpl; tauto | constructor].
      * intros q Hqps Hqsingle.
        simpl in Hqsingle. destruct Hqsingle as [Heq | Hfalse]; [|contradiction].
        subst q.
        pose proof (proj1 (Forall_forall (fun q : Z => 2 <= q < p) ps)
          Hlt p Hqps) as Hbound.
        exact (Z.lt_irrefl p (proj2 Hbound)).
    + split.
      * apply Forall_app. split; [exact Hprimes | constructor; [exact Hp | constructor]].
      * intros j Hj.
        rewrite Zlength_app_cons in Hj.
        destruct (Z_lt_ge_dec j (Zlength es)).
        -- rewrite app_Znth1 by lia. apply Hexps; lia.
        -- assert (j = Zlength es) by lia. subst j.
           rewrite app_Znth2 by lia.
           replace (Zlength es - Zlength es) with 0 by lia.
           rewrite Znth0_cons. exact He.
Qed.
Lemma factor_extract_nondividing_to_scan__scan_completion :
  forall orig rem d ps es e,
    FactorExtract orig rem d ps es e ->
    ExtractionScale rem d e ->
    Z.rem rem d <> 0 ->
    FactorScan orig rem (d + 1) (ps ++ [d]) (es ++ [e]) /\
    Zlength ps + 1 <= 29 /\
    d + 1 <= orig.
Proof.
  intros orig rem d ps es e Hext Hscale Hrem.
  unfold FactorExtract in Hext.
  destruct Hext as
    (Horig & Hremb & Hd & Hcap & Hprof & Hlt & Hprime & He & Heq & Hscan & Hzero).
  assert (Hediv : e <> 0).
  { intro He0. specialize (Hzero He0). apply Hrem.
    apply (proj2 (Zrem_divides rem d)).
    destruct Hzero as (q & Hq). exists q. rewrite Z.mul_comm. exact Hq. }
  assert (He_pos : 1 <= e) by lia.
  assert (Hfpos : 1 <= FactorPower ps es).
  { apply FactorPower_positive__scan_completion. exact Hprof. }
  assert (Hflow : 2 ^ Zlength ps <= FactorPower ps es).
  { apply FactorPower_lower_bound__scan_completion. exact Hprof. }
  assert (Hdpow : 2 <= Z.pow d e).
  { apply Z.le_trans with (Z.pow 2 1); [reflexivity |].
    apply Z.le_trans with (Z.pow d 1).
    - apply Zpower_le_monotone3; [lia |]. split; lia.
    - apply Zpower_le_monotone; [lia |]. lia. }
  assert (Hcapacity : Zlength ps + 1 <= 29).
  { destruct (Z_le_gt_dec (Zlength ps + 1) 29); [assumption |].
    assert (Zlength ps = 29) by lia.
    rewrite H in Hflow.
    change (536870912 <= FactorPower ps es) in Hflow.
    nia. }
  assert (Hdnext : d + 1 <= orig).
  { unfold ExtractionScale in Hscale. nia. }
  assert (Hprofile_app : PrimeExponentProfile (ps ++ [d]) (es ++ [e])).
  { apply PrimeExponentProfile_app_single__scan_completion;
      [exact Hprof | exact Hlt | exact Hprime | lia]. }
  split.
  - unfold FactorScan.
    split; [exact Horig |].
    split; [exact Hremb |].
    split; [lia |].
    split.
    + rewrite Zlength_app_cons. exact Hcapacity.
    + split; [exact Hprofile_app |].
      split.
      * apply Forall_app. split.
        -- eapply Forall_impl; [|exact Hlt].
           intros q Hq. destruct Hq. split; lia.
        -- constructor; [split; lia | constructor].
      * split.
        -- rewrite FactorPower_app_single__scan_completion.
           ++ nia.
           ++ exact (proj1 Hprof).
        -- intros p Hp Hprange Hpdiv.
           destruct (Z.eq_dec p d) as [Heqpd | Hpne].
           ++ subst p. apply Hrem. apply (proj2 (Zrem_divides rem d)).
              destruct Hpdiv as (q & Hq). exists q. rewrite Z.mul_comm. exact Hq.
           ++ apply (Hscan p Hp); try lia. exact Hpdiv.
  - split; assumption.
Qed.
Lemma factor_scan_skip_candidate__scan_completion :
  forall orig rem d ps es,
    FactorScan orig rem d ps es ->
    d * d <= rem ->
    Z.rem rem d <> 0 ->
    FactorScan orig rem (d + 1) ps es.
Proof.
  intros orig rem d ps es Hscan Hsq Hmod.
  unfold FactorScan in Hscan.
  destruct Hscan as
    (Horig & Hrem & Hd & Hcap & Hprof & Hlt & Heq & Hscan).
  unfold FactorScan.
  split; [exact Horig |].
  split; [exact Hrem |].
  split; [nia |].
  split; [exact Hcap |].
  split; [exact Hprof |].
  split.
  - eapply Forall_impl; [|exact Hlt].
    intros q Hq. destruct Hq as [Hqlo Hqhi]. split; lia.
  - split; [exact Heq |].
    intros p Hp Hprange Hpdiv.
    destruct (Z.eq_dec p d) as [Heqpd | Hne].
    + subst p. apply Hmod. apply (proj2 (Zrem_divides rem d)).
      destruct Hpdiv as (q & Hq). exists q. rewrite Z.mul_comm. exact Hq.
    + apply (Hscan p Hp); try lia. exact Hpdiv.
Qed.
Lemma factor_scan_residual_is_prime__scan_completion :
  forall orig rem next ps es,
    1 < rem -> next * next > rem ->
    FactorScan orig rem next ps es -> prime rem.
Proof.
  intros orig rem next ps es Hrem Hsq Hscan.
  destruct Hscan as
    [Horig [Hremb [Hnext [Hpslen [Hprof [Hsmall [Heq Hexcluded]]]]]]].
  destruct (prime_dec rem) as [Hp | Hnp]; [exact Hp |].
  exfalso.
  destruct (not_prime_divide rem Hrem Hnp) as [a [[Ha1 Har] Ha]].
  destruct Ha as [b Hab].
  assert (Hb1 : 1 < b) by nia.
  assert (Ha_small : a < next \/ b < next) by nia.
  destruct Ha_small as [Ha_small | Hb_small].
  - destruct (prime_divisor_exists__scan_completion a Ha1)
      as [p [Hp Hpa]].
    assert (Hp1 : 1 < p) by (inversion Hp; lia).
    assert (Hple : p <= a) by
      (apply Z.divide_pos_le; [lia | exact Hpa]).
    apply (Hexcluded p Hp ltac:(lia)).
    destruct Hpa as [u Hu]. exists (u * b). nia.
  - destruct (prime_divisor_exists__scan_completion b Hb1)
      as [p [Hp Hpb]].
    assert (Hp1 : 1 < p) by (inversion Hp; lia).
    assert (Hple : p <= b) by
      (apply Z.divide_pos_le; [lia | exact Hpb]).
    apply (Hexcluded p Hp ltac:(lia)).
    destruct Hpb as [u Hu]. exists (a * u). nia.
Qed.
Lemma factor_scan_finish_prime__scan_completion :
  forall orig rem next ps es,
    1 < rem -> next * next > rem ->
    FactorScan orig rem next ps es ->
    PrimeFactorization orig (ps ++ [rem]) (es ++ [1]).
Proof.
  intros orig rem next ps es Hrem Hsq Hscan.
  pose proof Hscan as Hscan'.
  destruct Hscan as
    [Horig [Hremb [Hnext [Hpslen [Hprof [Hsmall [Heq Hexcluded]]]]]]].
  destruct Hprof as [Hlen [Hnodup [Hprimes Hexps]]].
  assert (Hprime : prime rem) by
    (eapply factor_scan_residual_is_prime__scan_completion; eauto).
  unfold PrimeFactorization.
  split; [exact Horig |].
  split.
  - rewrite Zlength_app_cons. lia.
  - split.
    + unfold PrimeExponentProfile.
      split.
      * rewrite !Zlength_app_cons. lia.
      * split.
        -- apply NoDup_app.
           ++ exact Hnodup.
           ++ repeat constructor; simpl; tauto.
           ++ intros q Hqin Hqrem.
              simpl in Hqrem. destruct Hqrem as [Hqr | []]. subst q.
              apply (Hexcluded rem Hprime).
              ** apply Forall_forall with (x := rem) in Hsmall; auto.
              ** exists 1. ring.
        -- split.
           ++ apply Forall_app. split; [exact Hprimes |].
              constructor; [exact Hprime | constructor].
           ++ intros i Hi.
              rewrite Zlength_app_cons in Hi.
              destruct (Z_lt_ge_dec i (Zlength es)) as [Hil | Hige].
              ** rewrite app_Znth1 by lia. apply Hexps. lia.
              ** assert (i = Zlength es) by lia. subst i.
                 rewrite app_Znth2 by lia.
                 replace (Zlength es - Zlength es) with 0 by lia.
                 rewrite Znth0_cons. lia.
    + rewrite FactorPower_app_single__scan_completion by exact Hlen.
      rewrite Z.pow_1_r. nia.
Qed.
Lemma factor_scan_finish_unit__scan_completion :
  forall orig rem next ps es,
    rem <= 1 ->
    FactorScan orig rem next ps es ->
    PrimeFactorization orig ps es /\ 1 <= Zlength ps.
Proof.
  intros orig rem next ps es Hrem Hscan.
  pose proof Hscan as Hscan'.
  destruct Hscan as
    [Horig [Hremb [Hnext [Hpslen [Hprof [Hsmall [Heq Hexcluded]]]]]]].
  assert (Hrem1 : rem = 1) by lia.
  subst rem.
  split.
  - unfold PrimeFactorization.
    split; [exact Horig |].
    split; [lia |].
    split; [exact Hprof |].
    nia.
  - destruct ps as [|p ps].
    + assert (Hempty : FactorPower [] es = 1) by reflexivity.
      rewrite Hempty in Heq. lia.
    + rewrite Zlength_cons. pose proof (Zlength_nonneg ps). lia.
Qed.
Lemma prefix_maximum_zero__maximum_scan :
  forall es, PrefixMaximum es 0 0.
Proof.
  intros es. unfold PrefixMaximum.
  split; [pose proof (Zlength_nonneg es); lia |].
  split; [lia |].
  split.
  - intros i Hi. lia.
  - split.
    + intros _. reflexivity.
    + intros H. lia.
Qed.
Lemma prefix_maximum_step_gt__maximum_scan :
  forall es upto mx,
    PrefixMaximum es upto mx ->
    0 <= upto < Zlength es ->
    1 <= Znth upto es 0 <= 30 ->
    mx < Znth upto es 0 ->
    PrefixMaximum es (upto + 1) (Znth upto es 0).
Proof.
  intros es upto mx Hpref Hupto Hnewbound Hgt.
  unfold PrefixMaximum in *.
  destruct Hpref as (Hrange & Hmx & Hbound & Hz & Hattain).
  repeat split; try lia.
  - intros j Hj.
    destruct (Z_lt_ge_dec j upto).
    + specialize (Hbound j). lia.
    + assert (j = upto) by lia. subst j. lia.
  - intros _. exists upto. lia.
Qed.
Lemma prefix_maximum_step_le__maximum_scan :
  forall es upto mx,
    PrefixMaximum es upto mx ->
    0 <= upto < Zlength es ->
    1 <= Znth upto es 0 <= 30 ->
    Znth upto es 0 <= mx ->
    PrefixMaximum es (upto + 1) mx.
Proof.
  intros es upto mx Hpref Hupto Hnewbound Hle.
  unfold PrefixMaximum in *.
  destruct Hpref as (Hrange & Hmx & Hbound & Hz & Hattain).
  repeat split; try lia.
  - intros j Hj.
    destruct (Z_lt_ge_dec j upto).
    + apply Hbound. lia.
    + assert (j = upto) by lia. subst j. exact Hle.
  - intros _. destruct (Z.eq_dec upto 0).
    + subst upto. pose proof (Hz eq_refl) as Hmxzero.
      subst mx. exists 0. simpl in *. lia.
    + destruct (Hattain ltac:(lia)) as (j & Hj & Heq).
      exists j. lia.
Qed.
Lemma prefix_scan_completion__maximum_scan :
  forall orig ps es m i mx,
    PrimeFactorization orig ps es ->
    1 <= m ->
    i >= m ->
    i <= m ->
    Zlength es = m ->
    PrefixMaximum es i mx ->
    i = m /\ MaximumExponent es mx /\ 1 <= mx <= 30.
Proof.
  intros orig ps es m i mx Hfactor Hm Hge Hle Hlen Hprefix.
  assert (Hi : i = m) by lia.
  subst i.
  assert (Hmaximum : MaximumExponent es mx).
  { unfold MaximumExponent. rewrite Hlen. exact Hprefix. }
  pose proof Hfactor as Hfactor_copy.
  unfold PrimeFactorization, PrimeExponentProfile in Hfactor_copy.
  destruct Hfactor_copy as
    (_ & _ & (_ & _ & _ & Hexponents) & _).
  pose proof Hprefix as Hprefix_copy.
  unfold PrefixMaximum in Hprefix_copy.
  destruct Hprefix_copy as (_ & Hmx & _ & _ & Hattain).
  destruct (Hattain ltac:(lia)) as (j & Hj & Heq).
  pose proof (Hexponents j ltac:(lia)) as Hjbound.
  split; [reflexivity |].
  split; [exact Hmaximum |].
  rewrite <- Heq. exact Hjbound.
Qed.
Lemma fold_right_mul_pointwise__prefix_maximum :
  forall (xs : list Z) (f g : Z -> Z),
    Forall (fun x => 1 <= f x /\ f x <= g x) xs ->
    1 <= fold_right Z.mul 1 (map f xs) /\
    fold_right Z.mul 1 (map f xs) <=
      fold_right Z.mul 1 (map g xs).
Proof.
  intros xs f g Hfg.
  induction Hfg as [|x xs Hx Hxs IH].
  - simpl. lia.
  - simpl in *.
    destruct Hx as [Hfx Hle].
    destruct IH as [Hfold IH].
    split; nia.
Qed.
Lemma layer_value_le_factor_power__prefix_maximum :
  forall ps es,
    PrimeExponentProfile ps es ->
    1 <= LayerValue ps es 1 <= FactorPower ps es.
Proof.
  intros ps es Hprofile.
  destruct Hprofile as (Hlen & Hnodup & Hprimes & Hexponents).
  unfold LayerValue, LayerPrefixValue, FactorPower.
  apply fold_right_mul_pointwise__prefix_maximum.
  apply Forall_forall.
  intros idx Hidxin.
  apply (proj2 (In_Zrange 0 (Zlength ps) idx)) in Hidxin.
  assert (Hidxes : 0 <= idx < Zlength es) by lia.
  pose proof (Hexponents idx Hidxes) as He.
  pose proof (Forall_Znth_Zlength prime ps 1 idx Hprimes Hidxin) as Hp.
  pose proof (prime_ge_2 _ Hp) as Hp2.
  destruct (Z_le_dec 1 (Znth idx es 0)) as [Hyes | Hno].
  - split; [lia |].
    replace (Znth idx ps 1) with (Z.pow (Znth idx ps 1) 1) at 1 by ring.
    apply Z.pow_le_mono_r; lia.
  - lia.
Qed.
Lemma Zrange_zero_snoc__layer_accumulation : forall i,
  0 <= i -> Zrange 0 (i + 1) = Zrange 0 i ++ [i].
Proof.
  intros i Hi.
  unfold Zrange.
  replace (i + 1 - 0) with ((i - 0) + 1) by lia.
  rewrite Z2Nat.inj_add by lia.
  simpl Z.to_nat at 1.
  rewrite Zrange_aux_app.
  rewrite Z2Nat.id by lia.
  simpl.
  replace (i - 0) with i by lia.
  reflexivity.
Qed.
Lemma Zrange_zero_split__layer_accumulation : forall a b,
  0 <= a <= b -> Zrange 0 b = Zrange 0 a ++ Zrange a b.
Proof.
  intros a b Hab.
  unfold Zrange.
  replace (b - 0) with ((a - 0) + (b - a)) by lia.
  rewrite Z2Nat.inj_add by lia.
  rewrite Zrange_aux_app.
  rewrite Z2Nat.id by lia.
  replace (a - 0) with a by lia.
  reflexivity.
Qed.
Lemma fold_right_Zmul_app__layer_accumulation : forall xs ys,
  fold_right Z.mul 1 (xs ++ ys) =
  fold_right Z.mul 1 xs * fold_right Z.mul 1 ys.
Proof.
  induction xs as [|x xs IH]; intros ys; simpl.
  - destruct (fold_right Z.mul 1 ys); reflexivity.
  - rewrite IH. ring.
Qed.
Lemma fold_right_Zmul_bounds__layer_accumulation :
  forall (l : list Z) (f g : Z -> Z),
    (forall x, In x l -> 1 <= f x <= g x) ->
    1 <= fold_right Z.mul 1 (map f l) /\
    fold_right Z.mul 1 (map f l) <= fold_right Z.mul 1 (map g l).
Proof.
  induction l as [|x l IH]; intros f g Hfg; simpl.
  - lia.
  - pose proof (Hfg x (or_introl eq_refl)) as Hhead.
    specialize (IH f g ltac:(intros y Hy; apply Hfg; right; exact Hy)).
    destruct Hhead as [Hf Hfgx].
    destruct IH as [Htail Hle].
    nia.
Qed.
Lemma layer_product_factor_bounds__layer_accumulation : forall ps es k i,
  PrimeExponentProfile ps es ->
  1 <= k ->
  0 <= i < Zlength ps ->
  1 <= (if Z_le_dec k (Znth i es 0) then Znth i ps 1 else 1) <=
       Z.pow (Znth i ps 1) (Znth i es 0).
Proof.
  intros ps es k i Hprof Hk Hi.
  destruct Hprof as [Hlen [_ [Hprimes Hexps]]].
  assert (Hi_es : 0 <= i < Zlength es) by lia.
  pose proof ((proj1 (Forall_Znth prime 1 ps)) Hprimes i Hi) as Hprime.
  pose proof (prime_ge_2 _ Hprime) as Hp.
  pose proof (Hexps i Hi_es) as He.
  assert (Hpow : 1 <= Z.pow (Znth i ps 1) (Znth i es 0)).
  { pose proof (Z.pow_pos_nonneg (Znth i ps 1) (Znth i es 0) ltac:(lia) ltac:(lia)). lia. }
  destruct (Z_le_dec k (Znth i es 0)) as [Htake | Hskip].
  - split; [lia|].
    replace (Znth i es 0) with ((Znth i es 0 - 1) + 1) by lia.
    rewrite Z.pow_add_r by lia.
    simpl Z.pow.
    assert (1 <= Z.pow (Znth i ps 1) (Znth i es 0 - 1)).
    { pose proof (Z.pow_pos_nonneg (Znth i ps 1) (Znth i es 0 - 1) ltac:(lia) ltac:(lia)). lia. }
    nia.
  - lia.
Qed.
Lemma layer_prefix_value_snoc_take__layer_accumulation : forall ps es k i,
  0 <= i -> k <= Znth i es 0 ->
  LayerPrefixValue ps es k (i + 1) =
  LayerPrefixValue ps es k i * Znth i ps 1.
Proof.
  intros ps es k i Hi Htake.
  unfold LayerPrefixValue.
  rewrite Zrange_zero_snoc__layer_accumulation by exact Hi.
  rewrite map_app, fold_right_Zmul_app__layer_accumulation.
  simpl.
  destruct (Z_le_dec k (Znth i es 0)); [ring|lia].
Qed.
Lemma layer_prefix_value_snoc_skip__layer_accumulation : forall ps es k i,
  0 <= i -> Znth i es 0 < k ->
  LayerPrefixValue ps es k (i + 1) = LayerPrefixValue ps es k i.
Proof.
  intros ps es k i Hi Hskip.
  unfold LayerPrefixValue.
  rewrite Zrange_zero_snoc__layer_accumulation by exact Hi.
  rewrite map_app, fold_right_Zmul_app__layer_accumulation.
  simpl.
  destruct (Z_le_dec k (Znth i es 0)); [lia|ring].
Qed.
Lemma layer_prefix_value_bounds__layer_accumulation : forall ps es k upto,
  PrimeExponentProfile ps es ->
  1 <= k ->
  0 <= upto <= Zlength ps ->
  1 <= LayerPrefixValue ps es k upto <= FactorPower ps es.
Proof.
  intros ps es k upto Hprof Hk Hupto.
  unfold LayerPrefixValue, FactorPower.
  pose proof (fold_right_Zmul_bounds__layer_accumulation
    (Zrange 0 upto)
    (fun i => if Z_le_dec k (Znth i es 0) then Znth i ps 1 else 1)
    (fun i => Z.pow (Znth i ps 1) (Znth i es 0))) as Hprefix.
  specialize (Hprefix ltac:(intros x Hx; apply layer_product_factor_bounds__layer_accumulation; try assumption;
    apply (proj2 (In_Zrange 0 upto x)) in Hx; lia)).
  destruct Hprefix as [Hpos Hleprefix].
  rewrite (Zrange_zero_split__layer_accumulation upto (Zlength ps)) by exact Hupto.
  rewrite map_app, fold_right_Zmul_app__layer_accumulation.
  assert (Hsuffix : 1 <=
    fold_right Z.mul 1
      (map (fun i : Z => Z.pow (Znth i ps 1) (Znth i es 0))
           (Zrange upto (Zlength ps)))).
  { pose proof (fold_right_Zmul_bounds__layer_accumulation
      (Zrange upto (Zlength ps))
      (fun i => Z.pow (Znth i ps 1) (Znth i es 0))
      (fun i => Z.pow (Znth i ps 1) (Znth i es 0))) as Hsuffix_bounds.
    specialize (Hsuffix_bounds ltac:(intros x Hx;
      apply (proj2 (In_Zrange upto (Zlength ps) x)) in Hx;
      pose proof (layer_product_factor_bounds__layer_accumulation ps es k x Hprof Hk ltac:(lia));
      split; lia)).
    exact (proj1 Hsuffix_bounds). }
  nia.
Qed.
Lemma layer_prefix_value_mono__layer_accumulation : forall ps es k a b,
  PrimeExponentProfile ps es ->
  1 <= k ->
  0 <= a <= b -> b <= Zlength ps ->
  LayerPrefixValue ps es k a <= LayerPrefixValue ps es k b.
Proof.
  intros ps es k a b Hprof Hk Hab Hb.
  unfold LayerPrefixValue.
  rewrite (Zrange_zero_split__layer_accumulation a b) by exact Hab.
  rewrite map_app, fold_right_Zmul_app__layer_accumulation.
  assert (Hleft : 1 <= fold_right Z.mul 1
    (map (fun i : Z => if Z_le_dec k (Znth i es 0) then Znth i ps 1 else 1)
         (Zrange 0 a))).
  { pose proof (fold_right_Zmul_bounds__layer_accumulation
      (Zrange 0 a)
      (fun i => if Z_le_dec k (Znth i es 0) then Znth i ps 1 else 1)
      (fun i => Z.pow (Znth i ps 1) (Znth i es 0))) as Hleft_bounds.
    specialize (Hleft_bounds ltac:(intros x Hx; apply layer_product_factor_bounds__layer_accumulation; try assumption;
      apply (proj2 (In_Zrange 0 a x)) in Hx; lia)).
    exact (proj1 Hleft_bounds). }
  assert (Hmiddle : 1 <= fold_right Z.mul 1
    (map (fun i : Z => if Z_le_dec k (Znth i es 0) then Znth i ps 1 else 1)
         (Zrange a b))).
  { pose proof (fold_right_Zmul_bounds__layer_accumulation
      (Zrange a b)
      (fun i => if Z_le_dec k (Znth i es 0) then Znth i ps 1 else 1)
      (fun i => Z.pow (Znth i ps 1) (Znth i es 0))) as Hmiddle_bounds.
    specialize (Hmiddle_bounds ltac:(intros x Hx; apply layer_product_factor_bounds__layer_accumulation; try assumption;
      apply (proj2 (In_Zrange a b x)) in Hx; lia)).
    exact (proj1 Hmiddle_bounds). }
  nia.
Qed.
Lemma layer_prefix_future_bound__layer_accumulation : forall orig ps es k upto i,
  PrimeFactorization orig ps es ->
  1 <= k ->
  0 <= upto <= i ->
  i < Zlength ps ->
  k <= Znth i es 0 ->
  LayerPrefixValue ps es k upto * Znth i ps 1 <= orig.
Proof.
  intros orig ps es k upto i Hfact Hk Huptoi Hi Htake.
  destruct Hfact as [Horig [Hcap [Hprof Horig_eq]]].
  pose proof (layer_prefix_value_mono__layer_accumulation ps es k upto i Hprof Hk Huptoi ltac:(lia)) as Hmono.
  pose proof (layer_prefix_value_bounds__layer_accumulation ps es k (i + 1) Hprof Hk ltac:(lia)) as Hbounds.
  rewrite (layer_prefix_value_snoc_take__layer_accumulation ps es k i ltac:(lia) Htake) in Hbounds.
  destruct Hbounds as [_ Hbound].
  destruct Hprof as [Hlen [_ [Hprimes Hexps]]].
  pose proof ((proj1 (Forall_Znth prime 1 ps)) Hprimes i ltac:(lia)) as Hprime.
  pose proof (prime_ge_2 _ Hprime) as Hp.
  rewrite Horig_eq.
  nia.
Qed.
Lemma layer_product_prefix_initial__layer_accumulation : forall orig ps es k,
  PrimeFactorization orig ps es ->
  1 <= k <= 30 ->
  LayerProductPrefix orig ps es k 0 1.
Proof.
  intros orig ps es k Hfact Hk.
  unfold LayerProductPrefix.
  split; [exact Hfact|].
  split; [exact Hk|].
  split.
  - destruct Hfact as [_ [_ [Hprof _]]].
    destruct Hprof as [Hlen _]. pose proof (Zlength_nonneg ps). lia.
  - split.
    + unfold LayerPrefixValue, Zrange. simpl. reflexivity.
    + split.
      * destruct Hfact as [Horig _]. lia.
      * intros i Hi Htake.
        change (LayerPrefixValue ps es k 0 * Znth i ps 1 <= orig).
        apply layer_prefix_future_bound__layer_accumulation; try assumption; lia.
Qed.
Lemma layer_product_prefix_take__layer_accumulation : forall orig ps es k i prod,
  LayerProductPrefix orig ps es k i prod ->
  i < Zlength ps ->
  k <= Znth i es 0 ->
  LayerProductPrefix orig ps es k (i + 1) (prod * Znth i ps 1).
Proof.
  intros orig ps es k i prod Hprefix Hi Htake.
  destruct Hprefix as [Hfact [Hk [Hupto [Hprod [Hprod_bounds Hfuture]]]]].
  destruct Hk as [Hklo Hkhi].
  pose proof Hfact as Hfact_copy.
  destruct Hfact_copy as [_ [_ [Hprof Horig_eq]]].
  pose proof (layer_prefix_value_snoc_take__layer_accumulation ps es k i ltac:(lia) Htake) as Hstep.
  rewrite <- Hprod in Hstep.
  pose proof (layer_prefix_value_bounds__layer_accumulation ps es k (i + 1)
    Hprof Hklo ltac:(lia)) as Hnew_bounds.
  rewrite <- Horig_eq in Hnew_bounds.
  unfold LayerProductPrefix.
  split; [exact Hfact|]. split; [lia|]. split; [lia|].
  split; [symmetry; exact Hstep|]. split.
  - rewrite <- Hstep. exact Hnew_bounds.
  - intros j Hj Hjexp. rewrite <- Hstep.
    apply layer_prefix_future_bound__layer_accumulation; try assumption; lia.
Qed.
Lemma layer_product_prefix_skip__layer_accumulation : forall orig ps es k i prod,
  LayerProductPrefix orig ps es k i prod ->
  i < Zlength ps ->
  Znth i es 0 < k ->
  LayerProductPrefix orig ps es k (i + 1) prod.
Proof.
  intros orig ps es k i prod Hprefix Hi Hskip.
  destruct Hprefix as [Hfact [Hk [Hupto [Hprod [Hprod_bounds Hfuture]]]]].
  destruct Hk as [Hklo Hkhi].
  pose proof Hfact as Hfact_copy.
  destruct Hfact_copy as [_ [_ [Hprof Horig_eq]]].
  pose proof (layer_prefix_value_snoc_skip__layer_accumulation ps es k i ltac:(lia) Hskip) as Hstep.
  rewrite <- Hprod in Hstep.
  pose proof (layer_prefix_value_bounds__layer_accumulation ps es k (i + 1)
    Hprof Hklo ltac:(lia)) as Hnew_bounds.
  rewrite <- Horig_eq in Hnew_bounds.
  unfold LayerProductPrefix.
  split; [exact Hfact|]. split; [lia|]. split; [lia|].
  split; [symmetry; exact Hstep|]. split.
  - rewrite <- Hstep. exact Hnew_bounds.
  - intros j Hj Hjexp. rewrite <- Hstep.
    apply layer_prefix_future_bound__layer_accumulation; try assumption; lia.
Qed.
Lemma fold_mul_nonneg__layer_accumulation : forall (xs : list Z) (f : Z -> Z),
  (forall x, In x xs -> 0 <= f x) ->
  0 <= fold_right Z.mul 1 (map f xs).
Proof.
  induction xs as [|x xs IH]; intros f Hf; simpl; [lia |].
  pose proof (Hf x (or_introl eq_refl)) as Hx.
  assert (Htail : forall y, In y xs -> 0 <= f y).
  { intros y Hy. apply Hf. right. exact Hy. }
  specialize (IH f Htail). nia.
Qed.
Lemma fold_mul_mono__layer_accumulation : forall (xs : list Z) (f g : Z -> Z),
  (forall x, In x xs -> 0 <= f x <= g x) ->
  fold_right Z.mul 1 (map f xs) <= fold_right Z.mul 1 (map g xs).
Proof.
  induction xs as [|x xs IH]; intros f g Hfg; simpl; [lia|].
  pose proof (Hfg x (or_introl eq_refl)) as Hx.
  assert (Htail : forall y, In y xs -> 0 <= f y <= g y).
  { intros y Hy. apply Hfg. right. exact Hy. }
  specialize (IH f g Htail).
  assert (Hf_tail : 0 <= fold_right Z.mul 1 (map f xs)).
  { apply fold_mul_nonneg__layer_accumulation. intros y Hy. specialize (Htail y Hy). lia. }
  assert (Hg_tail : 0 <= fold_right Z.mul 1 (map g xs)).
  { apply fold_mul_nonneg__layer_accumulation. intros y Hy. specialize (Htail y Hy). lia. }
  nia.
Qed.
Lemma fold_mul_scale_once__layer_accumulation : forall (xs : list Z) idx c (f : Z -> Z),
  NoDup xs -> In idx xs ->
  fold_right Z.mul 1
    (map (fun x => if Z.eq_dec x idx then c * f x else f x) xs) =
  c * fold_right Z.mul 1 (map f xs).
Proof.
  induction xs as [|x xs IH]; intros idx c f Hnodup Hin; simpl in *; [contradiction|].
  inversion Hnodup as [|? ? Hnotin Hnodup_tail]; subst.
  destruct Hin as [Heq | Hin].
  - subst x. destruct (Z.eq_dec idx idx) as [_ | Hneq]; [|contradiction].
    assert (Hnone : forall y, In y xs -> y <> idx).
    { intros y Hy Heq. subst y. contradiction. }
    assert (Hmap : map (fun y => if Z.eq_dec y idx then c * f y else f y) xs = map f xs).
    { apply map_ext_in. intros y Hy.
      destruct (Z.eq_dec y idx); [exfalso; eapply Hnone; eauto | reflexivity]. }
    rewrite Hmap. ring.
  - destruct (Z.eq_dec x idx) as [Heq | Hneq]; [subst x; contradiction|].
    rewrite (IH idx c f Hnodup_tail Hin). ring.
Qed.
Lemma linear_times_base_le_pow__layer_accumulation : forall p e,
  2 <= p -> 1 <= e -> e * p <= Z.pow p e.
Proof.
  intros p e Hp He. remember (Z.to_nat e) as n eqn:Hn. generalize dependent e.
  induction n as [|n IH]; intros e He Hn; [lia|].
  assert (He_repr : e = Z.of_nat (S n)).
  { pose proof (Z2Nat.id e ltac:(lia)) as Heid.
    rewrite <- Hn in Heid. symmetry. exact Heid. }
  subst e. destruct n as [|n].
  - replace (Z.of_nat 1) with 1 by reflexivity. rewrite Z.pow_1_r. nia.
  - assert (Hconv : Z.to_nat (Z.of_nat (S n)) = S n) by apply Nat2Z.id.
    specialize (IH (Z.of_nat (S n)) ltac:(lia) (eq_sym Hconv)).
    rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r by lia. nia.
Qed.
Lemma layer_sum_factor_bounds__layer_accumulation : forall ps es i k,
  Zlength ps = Zlength es -> Forall prime ps ->
  (forall q, 0 <= q < Zlength es -> 1 <= Znth q es 0 <= 30) ->
  0 <= i < Zlength ps ->
  1 <= (if Z_le_dec k (Znth i es 0) then Znth i ps 1 else 1) <=
    Z.pow (Znth i ps 1) (Znth i es 0).
Proof.
  intros ps es i k Hlen Hprimes Hexps Hi.
  assert (Hpprime : prime (Znth i ps 1)).
  { rewrite Forall_forall in Hprimes. apply Hprimes. apply Znth_In_Zlength. exact Hi. }
  pose proof (prime_ge_2 _ Hpprime) as Hp.
  assert (He : 1 <= Znth i es 0 <= 30).
  { apply Hexps. rewrite <- Hlen. exact Hi. }
  destruct (Z_le_dec k (Znth i es 0)).
  - split; [lia |].
    pose proof (linear_times_base_le_pow__layer_accumulation
      (Znth i ps 1) (Znth i es 0) Hp (proj1 He)). nia.
  - split; [lia |].
    pose proof (Z.pow_pos_nonneg (Znth i ps 1) (Znth i es 0) ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma layer_value_scaled_bound__layer_accumulation : forall ps es mx idx j k,
  Zlength ps = Zlength es -> Forall prime ps ->
  (forall q, 0 <= q < Zlength es -> 1 <= Znth q es 0 <= 30) ->
  0 <= idx < Zlength es -> Znth idx es 0 = mx ->
  1 <= k <= j -> j <= mx ->
  j * LayerValue ps es k <= FactorPower ps es.
Proof.
  intros ps es mx idx j k Hlen Hprimes Hexps Hidx Hidxexp Hk Hj.
  unfold LayerValue, LayerPrefixValue, FactorPower.
  set (xs := Zrange 0 (Zlength ps)).
  set (lf := fun i => if Z_le_dec k (Znth i es 0) then Znth i ps 1 else 1).
  set (pf := fun i => Z.pow (Znth i ps 1) (Znth i es 0)).
  assert (Hidx_ps : 0 <= idx < Zlength ps) by (rewrite Hlen; exact Hidx).
  assert (Hidx_in : In idx xs).
  { unfold xs. apply (proj1 (In_Zrange 0 (Zlength ps) idx)). exact Hidx_ps. }
  assert (Hnodup : NoDup xs) by (unfold xs; apply NoDup_Zrange).
  rewrite <- (fold_mul_scale_once__layer_accumulation xs idx j lf Hnodup Hidx_in).
  apply fold_mul_mono__layer_accumulation. intros i Hi.
  assert (Hi_range : 0 <= i < Zlength ps).
  { unfold xs in Hi. apply (proj2 (In_Zrange 0 (Zlength ps) i)). exact Hi. }
  assert (Hordinary := layer_sum_factor_bounds__layer_accumulation
      ps es i k Hlen Hprimes Hexps Hi_range).
  unfold lf, pf. destruct (Z.eq_dec i idx) as [Heq | Hneq].
  - subst i.
    assert (Hpprime : prime (Znth idx ps 1)).
    { rewrite Forall_forall in Hprimes. apply Hprimes.
      apply Znth_In_Zlength. exact Hidx_ps. }
    pose proof (prime_ge_2 _ Hpprime) as Hp. rewrite Hidxexp.
    destruct (Z_le_dec k mx) as [Hkmx | Hkmx]; [|lia]. split; [nia |].
    eapply Z.le_trans.
    + apply linear_times_base_le_pow__layer_accumulation; lia.
    + apply Z.pow_le_mono_r; lia.
  - destruct Hordinary as [Hpositive Hupper]. split; lia.
Qed.
Lemma layer_sum_bound__layer_accumulation : forall orig ps es mx j,
  PrimeFactorization orig ps es -> MaximumExponent es mx ->
  1 <= j <= mx -> sum_range 1 j (LayerValue ps es) <= orig.
Proof.
  intros orig ps es mx j Hfactor Hmaximum Hj.
  unfold PrimeFactorization in Hfactor.
  destruct Hfactor as [_ [_ [Hprofile Horig]]].
  unfold PrimeExponentProfile in Hprofile.
  destruct Hprofile as [Hlen [_ [Hprimes Hexps]]].
  unfold MaximumExponent, PrefixMaximum in Hmaximum.
  destruct Hmaximum as [_ [_ [_ [Hzero Hattain]]]].
  assert (Hlenpos : 0 < Zlength es).
  { pose proof (Zlength_nonneg es).
    destruct (Z.eq_dec (Zlength es) 0) as [Heq | Hneq].
    - specialize (Hzero Heq). lia.
    - lia. }
  destruct (Hattain Hlenpos) as [idx [Hidx Hidxexp]].
  assert (Hscaled : forall k, 1 <= k < j + 1 ->
    j * LayerValue ps es k <= FactorPower ps es).
  { intros k Hk. eapply layer_value_scaled_bound__layer_accumulation; eauto; lia. }
  unfold sum_range.
  assert (Hsum := sum_Z_range_le 1 (j + 1)
    (fun k => j * LayerValue ps es k)
    (fun _ => FactorPower ps es) Hscaled).
  rewrite sum_Z_range_factor_l in Hsum.
  rewrite sum_Z_range_const in Hsum by lia. rewrite Horig. nia.
Qed.
Lemma sum_range_step__layer_accumulation : forall k f, 1 <= k ->
  sum_range 1 k f = sum_range 1 (k - 1) f + f k.
Proof.
  intros k f Hk. unfold sum_range.
  rewrite (sum_Z_range_extend_right 1 k f) by lia.
  replace (k - 1 + 1) with k by lia. reflexivity.
Qed.
Lemma layer_sum_prefix_step_base__layer_accumulation : forall orig ps es mx k upto total prod,
  upto = Zlength ps -> k <= mx ->
  LayerSumPrefix orig ps es mx k total ->
  LayerProductPrefix orig ps es k upto prod ->
  LayerSumPrefix orig ps es mx (k + 1) (total + prod).
Proof.
  intros orig ps es mx k upto total prod Hupto Hkmx Hsum Hprod. subst upto.
  unfold LayerProductPrefix in Hprod.
  destruct Hprod as [Hfactor_prod [Hk_prod [Hupto_bounds
    [Hprod_eq [Hprod_bounds Hremaining]]]]].
  unfold LayerSumPrefix in Hsum.
  destruct Hsum as [Hfactor [Hmaximum [Hk_bounds
    [Htotal_eq [Htotal_bounds Hfuture]]]]].
  assert (Hprod_layer : prod = LayerValue ps es k).
  { unfold LayerValue. exact Hprod_eq. }
  unfold LayerSumPrefix. split; [exact Hfactor |]. split; [exact Hmaximum |].
  split; [lia |]. split.
  - rewrite Hprod_layer, Htotal_eq. replace (k + 1 - 1) with k by lia.
    symmetry. apply sum_range_step__layer_accumulation. lia.
  - split.
    + split.
      * pose proof (proj1 Htotal_bounds). pose proof (proj1 Hprod_bounds). lia.
      * rewrite Hprod_layer, Htotal_eq.
        replace (sum_range 1 (k - 1) (LayerValue ps es) + LayerValue ps es k)
          with (sum_range 1 k (LayerValue ps es)) by
          (exact (sum_range_step__layer_accumulation k (LayerValue ps es) ltac:(lia))).
        apply layer_sum_bound__layer_accumulation with (mx := mx); try assumption. lia.
    + intros Hnext. rewrite Hprod_layer, Htotal_eq.
      replace (sum_range 1 (k - 1) (LayerValue ps es) +
        LayerValue ps es k + LayerValue ps es (k + 1))
        with (sum_range 1 (k + 1) (LayerValue ps es)) by
        (rewrite sum_range_step__layer_accumulation by lia;
         replace (k + 1 - 1) with k by lia;
         rewrite sum_range_step__layer_accumulation by lia; ring).
      apply layer_sum_bound__layer_accumulation with (mx := mx); try assumption. lia.
Qed.
Lemma layer_product_prefix_zero__layer_accumulation : forall orig ps es mx k total,
  k <= mx -> LayerSumPrefix orig ps es mx k total ->
  LayerProductPrefix orig ps es k 0 1.
Proof.
  intros orig ps es mx k total Hkmx Hsum. pose proof Hsum as Hsum_copy.
  unfold LayerSumPrefix in Hsum_copy.
  destruct Hsum_copy as [Hfactor [Hmaximum [Hk_bounds _]]].
  apply layer_product_prefix_initial__layer_accumulation; [exact Hfactor |].
  unfold MaximumExponent, PrefixMaximum in Hmaximum.
  destruct Hmaximum as [Hrange [Hmx_bounds Hrest]]. lia.
Qed.
Lemma layer_product_prefix_step_in__layer_accumulation : forall orig ps es k i prod,
  LayerProductPrefix orig ps es k i prod -> i < Zlength ps ->
  k <= Znth i es 0 ->
  LayerProductPrefix orig ps es k (i + 1) (prod * Znth i ps 0).
Proof.
  intros orig ps es k i prod Hprefix Hi Htake.
  assert (Hi0 : 0 <= i) by (unfold LayerProductPrefix in Hprefix; tauto).
  rewrite (Znth_indep ps i 0 1) by lia.
  apply layer_product_prefix_take__layer_accumulation; assumption.
Qed.
Lemma layer_product_prefix_step_out__layer_accumulation : forall orig ps es k i prod,
  LayerProductPrefix orig ps es k i prod -> i < Zlength ps ->
  Znth i es 0 < k -> LayerProductPrefix orig ps es k (i + 1) prod.
Proof. intros. apply layer_product_prefix_skip__layer_accumulation; assumption. Qed.
Lemma layer_sum_prefix_step__layer_accumulation :
  forall orig ps es mx k upto total prod,
  upto = Zlength ps -> k <= mx ->
  LayerSumPrefix orig ps es mx k total ->
  LayerProductPrefix orig ps es k upto prod ->
  LayerSumPrefix orig ps es mx (k + 1) (total + prod).
Proof.
  intros. apply layer_sum_prefix_step_base__layer_accumulation with (upto := upto); assumption.
Qed.
Lemma layer_sum_completion_answer__final_result :
  forall orig ps es mx next total,
    mx < next ->
    next <= mx + 1 ->
    LayerSumPrefix orig ps es mx next total ->
    FactorizationAnswer orig ps es total.
Proof.
  intros orig ps es mx next total Hlt Hle Hprefix.
  assert (Hnext : next = mx + 1) by lia.
  unfold LayerSumPrefix in Hprefix.
  destruct Hprefix as
      [Hfactor [Hmaximum [Hnext_bounds [Htotal [Htotal_bounds Hfuture]]]]].
  unfold FactorizationAnswer.
  split; [exact Hfactor |].
  exists mx.
  split; [exact Hmaximum |].
  split.
  - rewrite Hnext in Htotal.
    replace (mx + 1 - 1) with mx in Htotal by lia.
    exact Htotal.
  - exact Htotal_bounds.
Qed.
