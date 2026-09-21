From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.
Import ListNotations.
Local Open Scope Z_scope.

(** The mathematical modulus of a CRT instance.  This is a property of the
    input sequence and is independent of either loop in the C implementation. *)
Definition CRTProduct (moduli : list Z) : Z :=
  fold_right Z.mul 1 moduli.

(** A well-formed nonempty system of congruences: corresponding lists have
    the same length, each modulus is positive, each remainder is canonical,
    and distinct moduli are coprime. *)
Definition CRTInputValid
    (remainders moduli : list Z) : Prop :=
  Zlength remainders = Zlength moduli /\
  1 <= Zlength moduli /\
  (forall i,
      0 <= i < Zlength moduli ->
      1 <= Znth i moduli 0 /\
      0 <= Znth i remainders 0 < Znth i moduli 0) /\
  (forall i j,
      0 <= i /\ i < j /\ j < Zlength moduli ->
      Z.gcd (Znth i moduli 0) (Znth j moduli 0) = 1).

(** The C example intentionally uses [int].  The product bound makes every
    multiplication of two reduced residues fit.  The final clause accounts
    for the hard-frozen [exgcd] interface, which exposes an arbitrary signed
    [int] Bezout coefficient but no stronger coefficient bound. *)
Definition CRTMachineSafe
    (remainders moduli : list Z) : Prop :=
  let product := CRTProduct moduli in
  1 <= product <= 46340 /\
  (forall i coefficient,
      0 <= i < Zlength moduli ->
      (-2147483648 <= coefficient <= 2147483647) ->
      -2147483648 <=
        coefficient * (product / Znth i moduli 0) <=
        2147483647).

(** The public functional result: [answer] is the canonical representative
    modulo the product and satisfies every input congruence.  Pairwise
    coprimality in [CRTInputValid] makes this representative unique. *)
Definition CanonicalCRTSolution
    (remainders moduli : list Z) (answer : Z) : Prop :=
  0 <= answer < CRTProduct moduli /\
  Forall2 (fun remainder modulus => answer mod modulus = remainder)
    remainders moduli.

(** Internal mathematical state for the accumulation phase.  C-level bounds,
    pointer ownership, and the range of [processed] deliberately remain in
    the loop invariant rather than being hidden in this predicate. *)
Definition CRTProcessedCongruences
    (remainders moduli : list Z) (processed result : Z) : Prop :=
  forall i,
    0 <= i < processed ->
    result mod Znth i moduli 0 = Znth i remainders 0.

From Coq Require Import Lia Ring.
From Coq Require Import Lia.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.ZArith.Zquot.
Require Import Coq.micromega.Lia.
Lemma fold_right_mul_acc__product_progress :
  forall (l : list Z) (acc : Z),
    fold_right Z.mul acc l = fold_right Z.mul 1 l * acc.
Proof.
  intros l acc.
  induction l as [|x xs IH].
  - cbn [fold_right]. rewrite Z.mul_1_l. reflexivity.
  - cbn [fold_right]. rewrite IH, Z.mul_assoc. reflexivity.
Qed.
Lemma crt_prefix_product_step__product_progress :
  forall (moduli : list Z) (i : Z),
    0 <= i < Zlength moduli ->
    CRTProduct (sublist 0 (i + 1) moduli) =
      CRTProduct (sublist 0 i moduli) * Znth i moduli 0.
Proof.
  intros moduli i Hi.
  rewrite (sublist_split 0 (i + 1) i moduli) by lia.
  rewrite (sublist_single 0 i moduli) by lia.
  unfold CRTProduct.
  rewrite fold_right_app.
  simpl.
  rewrite Z.mul_1_r.
  apply fold_right_mul_acc__product_progress.
Qed.
Lemma crt_product_app__product_progress :
  forall (left right : list Z),
    CRTProduct (left ++ right) = CRTProduct left * CRTProduct right.
Proof.
  intros left right.
  unfold CRTProduct.
  rewrite fold_right_app.
  apply fold_right_mul_acc__product_progress.
Qed.
Lemma crt_input_moduli_positive__product_progress :
  forall (remainders moduli : list Z),
    CRTInputValid remainders moduli ->
    Forall (fun modulus => 1 <= modulus) moduli.
Proof.
  intros remainders moduli Hvalid.
  apply Forall_forall.
  intros modulus Hin.
  apply In_nth with (d := 0) in Hin as [n [Hn Hnth]].
  destruct Hvalid as [_ [_ [Hvalues _]]].
  specialize (Hvalues (Z.of_nat n)).
  assert (0 <= Z.of_nat n < Zlength moduli) as Hrange.
  { rewrite Zlength_correct. lia. }
  specialize (Hvalues Hrange).
  destruct Hvalues as [Hmodulus _].
  unfold Znth in Hmodulus.
  rewrite Nat2Z.id in Hmodulus.
  rewrite Hnth in Hmodulus.
  exact Hmodulus.
Qed.
Lemma crt_product_positive__product_progress :
  forall (moduli : list Z),
    Forall (fun modulus => 1 <= modulus) moduli ->
    1 <= CRTProduct moduli.
Proof.
  intros moduli Hpositive.
  induction Hpositive as [|modulus tail Hmodulus Htail IH].
  - unfold CRTProduct. simpl. lia.
  - unfold CRTProduct in *. simpl. nia.
Qed.
Lemma crt_prefix_product_bounds__product_progress :
  forall (remainders moduli : list Z) (i : Z),
    CRTInputValid remainders moduli ->
    0 <= i <= Zlength moduli ->
    (1 <= CRTProduct (sublist 0 i moduli) <= CRTProduct moduli) /\
    (i = Zlength moduli -> sublist 0 i moduli = moduli).
Proof.
  intros remainders moduli i Hvalid Hi.
  assert (moduli =
          sublist 0 i moduli ++ sublist i (Zlength moduli) moduli) as Hsplit.
  {
    rewrite <- (sublist_split 0 (Zlength moduli) i moduli) by lia.
    symmetry.
    apply sublist_self.
    reflexivity.
  }
  pose proof
    (crt_input_moduli_positive__product_progress remainders moduli Hvalid)
    as Hall.
  rewrite Hsplit in Hall.
  apply Forall_app in Hall as [Hprefix Hsuffix].
  pose proof (crt_product_positive__product_progress _ Hprefix) as Hp.
  pose proof (crt_product_positive__product_progress _ Hsuffix) as Hs.
  assert (CRTProduct moduli =
          CRTProduct (sublist 0 i moduli) *
          CRTProduct (sublist i (Zlength moduli) moduli)) as Hproduct.
  {
    transitivity
      (CRTProduct
         (sublist 0 i moduli ++ sublist i (Zlength moduli) moduli)).
    - f_equal. exact Hsplit.
    - apply crt_product_app__product_progress.
  }
  split.
  - split; [exact Hp |].
    nia.
  - intros Heq.
    apply sublist_self.
    exact Heq.
Qed.
Lemma crt_factor_quotient_bounds__product_progress :
  forall (remainders moduli : list Z) (i : Z),
    CRTInputValid remainders moduli ->
    0 <= i < Zlength moduli ->
    (1 <= Znth i moduli 0 <= CRTProduct moduli) /\
    (1 <= CRTProduct moduli / Znth i moduli 0 <= CRTProduct moduli).
Proof.
  intros remainders moduli i Hvalid Hi.
  pose proof Hvalid as Hvalid_parts.
  destruct Hvalid as [_ [_ [Hvalues _]]].
  specialize (Hvalues i Hi).
  destruct Hvalues as [Hmodulus _].
  pose proof
    (crt_prefix_product_bounds__product_progress
       remainders moduli i Hvalid_parts ltac:(lia)) as Hprefix.
  pose proof
    (crt_prefix_product_bounds__product_progress
       remainders moduli (i + 1) Hvalid_parts ltac:(lia)) as Hnext.
  destruct Hprefix as [[Hprefix_pos _] _].
  destruct Hnext as [[_ Hnext_bound] _].
  pose proof (crt_prefix_product_step__product_progress moduli i Hi) as Hstep.
  assert (Znth i moduli 0 <= CRTProduct moduli) as Hmodulus_bound by nia.
  split.
  - lia.
  - split.
    + apply Z.div_le_lower_bound; nia.
    + apply Z.div_le_upper_bound; nia.
Qed.
Lemma CRTProduct_ge_one__machine_safety :
  forall moduli,
    (forall modulus, In modulus moduli -> 1 <= modulus) ->
    1 <= CRTProduct moduli.
Proof.
  intros moduli Hall.
  induction moduli as [|modulus rest IH].
  - reflexivity.
  - simpl.
    assert (Hmodulus : 1 <= modulus).
    { apply Hall. left. reflexivity. }
    assert (Hrest : 1 <= CRTProduct rest).
    { apply IH. intros x Hx. apply Hall. right. exact Hx. }
    nia.
Qed.
Lemma CRTProduct_factor_upper_bound__machine_safety :
  forall moduli modulus,
    (forall x, In x moduli -> 1 <= x) ->
    In modulus moduli ->
    modulus <= CRTProduct moduli.
Proof.
  intros moduli.
  induction moduli as [|head rest IH]; intros modulus Hall Hin.
  - contradiction.
  - simpl.
    assert (Hhead : 1 <= head).
    { apply Hall. left. reflexivity. }
    destruct Hin as [Heq | Hin].
    + subst modulus.
      pose proof
        (CRTProduct_ge_one__machine_safety rest
           (fun x Hx => Hall x (or_intror Hx))) as Hrest.
      nia.
    + pose proof
        (IH modulus (fun x Hx => Hall x (or_intror Hx)) Hin) as Hfactor.
      assert (1 <= modulus) by (apply Hall; right; exact Hin).
      nia.
Qed.
Lemma CRTInputValid_modulus_upper_bound__machine_safety :
  forall remainders moduli i,
    CRTInputValid remainders moduli ->
    0 <= i < Zlength moduli ->
    Znth i moduli 0 <= CRTProduct moduli.
Proof.
  intros remainders moduli i Hvalid Hi.
  unfold CRTInputValid in Hvalid.
  destruct Hvalid as [_ [_ [Hentries _]]].
  apply CRTProduct_factor_upper_bound__machine_safety.
  - intros modulus Hin.
    destruct (In_nth moduli modulus 0 Hin) as [n [Hn Hnth]].
    specialize (Hentries (Z.of_nat n) ltac:(rewrite Zlength_correct; lia)).
    unfold Znth in Hentries.
    rewrite Nat2Z.id in Hentries.
    rewrite Hnth in Hentries.
    lia.
  - unfold Znth.
    apply nth_In.
    apply Nat2Z.inj_lt.
    rewrite Z2Nat.id by lia.
    rewrite <- Zlength_correct.
    lia.
Qed.
Lemma crt_c_rem_mul_int_bounds__machine_safety :
  forall a product remainder,
    1 <= product ->
    product <= 46340 ->
    0 <= remainder ->
    remainder < product ->
    -2147483648 <= Z.rem a product * remainder <= 2147483647.
Proof.
  intros a product remainder Hproduct_pos Hproduct_bound
    Hremainder_nonneg Hremainder_bound.
  pose proof (Z.rem_bound_abs a product ltac:(lia)) as Hrem.
  nia.
Qed.
Lemma crt_fold_product_app__crt_transition :
  forall l1 l2 : list Z,
    fold_right Z.mul 1 (l1 ++ l2) =
    fold_right Z.mul 1 l1 * fold_right Z.mul 1 l2.
Proof.
  induction l1 as [| a l1 IH]; intros l2; simpl.
  - symmetry. apply Z.mul_1_l.
  - rewrite IH. ring.
Qed.
Lemma crt_gcd_of_bezout_one__crt_transition :
  forall a b,
    Z.Bezout a b 1 ->
    Z.gcd a b = 1.
Proof.
  intros a b [x [y Hbezout]].
  apply Zgcd_1_rel_prime.
  apply bezout_rel_prime.
  apply Bezout_intro with x y.
  exact Hbezout.
Qed.
Lemma crt_gcd_mul_one__crt_transition :
  forall a b m,
    Z.gcd a m = 1 ->
    Z.gcd b m = 1 ->
    Z.gcd (a * b) m = 1.
Proof.
  intros a b m Ha Hb.
  apply crt_gcd_of_bezout_one__crt_transition.
  destruct (Z.gcd_bezout a m 1 Ha) as [xa [ya Hbezout_a]].
  destruct (Z.gcd_bezout b m 1 Hb) as [xb [yb Hbezout_b]].
  exists (xa * xb).
  exists (xa * a * yb + ya * xb * b + ya * yb * m).
  transitivity ((xa * a + ya * m) * (xb * b + yb * m)).
  - ring.
  - rewrite Hbezout_a, Hbezout_b. ring.
Qed.
Lemma crt_fold_product_coprime__crt_transition :
  forall (l : list Z) m,
    (forall k,
        0 <= k < Zlength l ->
        Z.gcd (Znth k l 0) m = 1) ->
    Z.gcd (fold_right Z.mul 1 l) m = 1.
Proof.
  induction l as [| a l IH]; intros m Hall; simpl.
  - apply Z.gcd_1_l.
  - apply crt_gcd_mul_one__crt_transition.
    + specialize (Hall 0).
      rewrite Zlength_cons in Hall.
      pose proof (Zlength_nonneg l).
      specialize (Hall ltac:(lia)).
      rewrite Znth0_cons in Hall.
      exact Hall.
    + apply IH.
      intros k Hk.
      specialize (Hall (k + 1)).
      rewrite Zlength_cons in Hall.
      specialize (Hall ltac:(lia)).
      rewrite Znth_cons in Hall by lia.
      replace (k + 1 - 1) with k in Hall by ring.
      exact Hall.
Qed.
Lemma crt_Znth_divides_fold_product__crt_transition :
  forall (l : list Z) k,
    0 <= k < Zlength l ->
    (Znth k l 0 | fold_right Z.mul 1 l).
Proof.
  induction l as [| a l IH]; intros k Hk.
  - rewrite Zlength_nil in Hk. lia.
  - rewrite Zlength_cons in Hk.
    destruct (Z.eq_dec k 0) as [-> | Hne].
    + rewrite Znth0_cons. simpl.
      exists (fold_right Z.mul 1 l). ring.
    + assert (0 < k) by lia.
      rewrite Znth_cons by lia.
      specialize (IH (k - 1) ltac:(lia)).
      destruct IH as [q Hq].
      exists (a * q).
      simpl. rewrite Hq. ring.
Qed.
Lemma crt_product_factor_arithmetic__crt_transition :
  forall remainders moduli i,
    CRTInputValid remainders moduli ->
    0 <= i < Zlength moduli ->
    let m := Znth i moduli 0 in
    let q := CRTProduct moduli / m in
      q * m = CRTProduct moduli /\
      Z.gcd q m = 1 /\
      forall j,
        0 <= j < Zlength moduli ->
        j <> i ->
        (Znth j moduli 0 | q).
Proof.
  intros remainders moduli i Hvalid Hi.
  destruct Hvalid as [_ [_ [Hbounds Hpairwise]]].
  cbn zeta.
  set (m := Znth i moduli 0).
  set (prefix := sublist 0 i moduli).
  set (suffix := sublist (i + 1) (Zlength moduli) moduli).
  pose proof (Hbounds i Hi) as [Hm _].
  fold m in Hm.
  assert (Hprefix_len : Zlength prefix = i).
  {
    subst prefix.
    rewrite Zlength_sublist by lia. ring.
  }
  assert (Hsuffix_len : Zlength suffix = Zlength moduli - (i + 1)).
  {
    subst suffix.
    rewrite Zlength_sublist by lia. reflexivity.
  }
  assert (Hdecomp : moduli = prefix ++ [m] ++ suffix).
  {
    pose proof
      (sublist_split 0 (Zlength moduli) i moduli ltac:(lia) ltac:(lia))
      as Hwhole.
    pose proof
      (sublist_split i (Zlength moduli) (i + 1) moduli
        ltac:(lia) ltac:(lia))
      as Htail.
    rewrite (sublist_self moduli (Zlength moduli) eq_refl) in Hwhole.
    rewrite (sublist_single 0 i moduli Hi) in Htail.
    fold prefix in Hwhole.
    fold suffix in Htail.
    fold m in Htail.
    rewrite Htail in Hwhole.
    exact Hwhole.
  }
  assert (Hproduct :
    CRTProduct moduli =
      fold_right Z.mul 1 prefix * m * fold_right Z.mul 1 suffix).
  {
    unfold CRTProduct.
    rewrite Hdecomp.
    rewrite !crt_fold_product_app__crt_transition.
    simpl. ring.
  }
  assert (Hquotient :
    CRTProduct moduli / m =
      fold_right Z.mul 1 prefix * fold_right Z.mul 1 suffix).
  {
    rewrite Hproduct.
    replace
      (fold_right Z.mul 1 prefix * m * fold_right Z.mul 1 suffix)
      with
      ((fold_right Z.mul 1 prefix * fold_right Z.mul 1 suffix) * m)
      by ring.
    apply Z.div_mul. lia.
  }
  split.
  - rewrite Hquotient, Hproduct. ring.
  - split.
    + rewrite Hquotient.
      apply crt_gcd_mul_one__crt_transition.
      * apply crt_fold_product_coprime__crt_transition.
        intros k Hk.
        assert (Hki : 0 <= k < i) by lia.
        specialize (Hpairwise k i ltac:(lia)).
        subst prefix m.
        rewrite Znth_sublist by lia.
        replace (k + 0) with k by ring.
        exact Hpairwise.
      * apply crt_fold_product_coprime__crt_transition.
        intros k Hk.
        assert (Hkj : 0 <= k + (i + 1) < Zlength moduli) by lia.
        specialize (Hpairwise i (k + (i + 1)) ltac:(lia)).
        subst suffix m.
        rewrite Znth_sublist by lia.
        rewrite Z.gcd_comm.
        exact Hpairwise.
    + intros j Hj Hji.
      rewrite Hquotient.
      destruct (Z_lt_ge_dec j i) as [Hlt | Hge].
      * assert (Hdiv :
          (Znth j prefix 0 | fold_right Z.mul 1 prefix)).
        {
          apply crt_Znth_divides_fold_product__crt_transition.
          lia.
        }
        assert (Heq : Znth j prefix 0 = Znth j moduli 0).
        {
          subst prefix.
          rewrite Znth_sublist by lia.
          replace (j + 0) with j by ring.
          reflexivity.
        }
        rewrite Heq in Hdiv.
        destruct Hdiv as [q Hq].
        exists (q * fold_right Z.mul 1 suffix).
        rewrite Hq. ring.
      * assert (Hgt : i < j) by lia.
        set (k := j - (i + 1)).
        assert (Hdiv :
          (Znth k suffix 0 | fold_right Z.mul 1 suffix)).
        {
          apply crt_Znth_divides_fold_product__crt_transition.
          subst k. lia.
        }
        assert (Heq : Znth k suffix 0 = Znth j moduli 0).
        {
          subst suffix k.
          rewrite Znth_sublist by lia.
          replace (j - (i + 1) + (i + 1)) with j by ring.
          reflexivity.
        }
        rewrite Heq in Hdiv.
        destruct Hdiv as [q Hq].
        exists (fold_right Z.mul 1 prefix * q).
        rewrite Hq. ring.
Qed.
Lemma crt_update_processed__crt_transition :
  forall remainders moduli result i product x y,
    CRTInputValid remainders moduli ->
    0 <= i < Zlength moduli ->
    product = CRTProduct moduli ->
    1 <= product ->
    CRTProcessedCongruences remainders moduli i result ->
    (forall k,
        i <= k < Zlength moduli ->
        result mod Znth k moduli 0 = 0) ->
    (product / Znth i moduli 0) * x + Znth i moduli 0 * y =
      Z.gcd (product / Znth i moduli 0) (Znth i moduli 0) ->
    CRTProcessedCongruences remainders moduli (i + 1)
      ((result +
        ((((x * (product / Znth i moduli 0)) mod product) *
          Znth i remainders 0) mod product)) mod product).
Proof.
  intros remainders moduli result i product x y
    Hvalid Hi Hproduct Hproduct_pos Hprocessed Hzero Hbezout.
  pose proof Hvalid as Hvalid_for_factor.
  pose proof
    (crt_product_factor_arithmetic__crt_transition
      remainders moduli i Hvalid_for_factor Hi)
    as Hfactor_data.
  cbn zeta in Hfactor_data.
  destruct Hfactor_data as [Hfactor [Hgcd Hother_divides]].
  destruct Hvalid as [_ [_ [Hbounds _]]].
  set (m := Znth i moduli 0).
  set (q := product / m).
  set (r := Znth i remainders 0).
  fold m q in Hfactor, Hgcd, Hother_divides.
  fold m q in Hbezout.
  rewrite <- Hproduct in Hfactor, Hgcd, Hother_divides.
  pose proof (Hbounds i Hi) as [Hm Hr].
  fold m in Hm.
  fold m r in Hr.
  assert (Hm_div_product : (m | product)).
  {
    exists q.
    symmetry. exact Hfactor.
  }
  unfold CRTProcessedCongruences.
  intros j Hj.
  destruct (Z_lt_ge_dec j i) as [Hji | Hji].
  - assert (Hjrange : 0 <= j < Zlength moduli) by lia.
    pose proof (Hbounds j Hjrange) as [Hmj Hremj].
    specialize (Hprocessed j ltac:(lia)).
    specialize (Hother_divides j Hjrange ltac:(lia)).
    set (mj := Znth j moduli 0).
    fold mj in Hmj, Hremj, Hprocessed, Hother_divides.
    assert (Hmj_div_product : (mj | product)).
    {
      destruct Hother_divides as [factor_j Hfactor_j].
      exists (factor_j * m).
      rewrite <- Hfactor, Hfactor_j. ring.
    }
    assert (Hcoefficient_mod : (x * q mod product) mod mj = 0).
    {
      rewrite <-
        (Znumtheory.Zmod_div_mod mj product (x * q)
          ltac:(lia) ltac:(lia) Hmj_div_product).
      destruct Hother_divides as [factor_j Hfactor_j].
      change (q = factor_j * mj) in Hfactor_j.
      rewrite Hfactor_j.
      replace (x * (factor_j * mj)) with ((x * factor_j) * mj) by ring.
      apply Z_mod_mult.
    }
    assert (Hterm_mod :
      ((((x * q) mod product) * r) mod product) mod mj = 0).
    {
      rewrite <-
        (Znumtheory.Zmod_div_mod mj product
          (((x * q) mod product) * r)
          ltac:(lia) ltac:(lia) Hmj_div_product).
      rewrite Zmult_mod, Hcoefficient_mod, Z.mul_0_l, Zmod_0_l.
      reflexivity.
    }
    fold q r.
    rewrite <-
      (Znumtheory.Zmod_div_mod mj product
        (result + ((((x * q) mod product) * r) mod product))
        ltac:(lia) ltac:(lia) Hmj_div_product).
    rewrite Zplus_mod, Hprocessed, Hterm_mod, Z.add_0_r.
    apply Z.mod_small. exact Hremj.
  - assert (Hjeq : j = i) by lia.
    subst j.
    specialize (Hzero i ltac:(lia)).
    fold m in Hzero.
    change (q * x + m * y = Z.gcd q m) in Hbezout.
    change (Z.gcd q m = 1) in Hgcd.
    rewrite Hgcd in Hbezout.
    assert (Hcoefficient_mod : (x * q mod product) mod m = 1 mod m).
    {
      rewrite <-
        (Znumtheory.Zmod_div_mod m product (x * q)
          ltac:(lia) ltac:(lia) Hm_div_product).
      rewrite Z.mul_comm.
      replace (q * x) with (1 + (- y) * m) by lia.
      apply Z_mod_plus_full.
    }
    assert (Hterm_mod :
      ((((x * q) mod product) * r) mod product) mod m = r).
    {
      rewrite <-
        (Znumtheory.Zmod_div_mod m product
          (((x * q) mod product) * r)
          ltac:(lia) ltac:(lia) Hm_div_product).
      rewrite Zmult_mod, Hcoefficient_mod.
      destruct (Z.eq_dec m 1) as [Hm_one | Hm_not_one].
      - assert (Hr_zero : r = 0) by lia.
        rewrite Hm_one.
        symmetry. exact Hr_zero.
      - rewrite (Z.mod_small 1) by lia.
        rewrite (Z.mod_small r) by lia.
        rewrite Z.mul_1_l.
        apply Z.mod_small. exact Hr.
    }
    fold q r.
    change
      (((result + ((((x * q) mod product) * r) mod product)) mod product)
        mod m = r).
    rewrite <-
      (Znumtheory.Zmod_div_mod m product
        (result + ((((x * q) mod product) * r) mod product))
        ltac:(lia) ltac:(lia) Hm_div_product).
    rewrite Zplus_mod, Hzero, Hterm_mod, Z.add_0_l.
    apply Z.mod_small. exact Hr.
Qed.
Lemma crt_rem_mod__crt_transition :
  forall a p,
    p <> 0 ->
    (Z.rem a p) mod p = a mod p.
Proof.
  intros a p Hp.
  rewrite <- (Z.mod_add (Z.rem a p) (a ÷ p) p Hp).
  pose proof (Z.quot_rem' a p) as Hquot_rem.
  replace (Z.rem a p + (a ÷ p) * p) with a by lia.
  reflexivity.
Qed.
Lemma crt_rem_mul_mod__crt_transition :
  forall a r p,
    p <> 0 ->
    (Z.rem a p * r) mod p = ((a mod p) * r) mod p.
Proof.
  intros a r p Hp.
  transitivity (((Z.rem a p) mod p * (r mod p)) mod p).
  - apply Zmult_mod.
  - rewrite (crt_rem_mod__crt_transition a p Hp).
    symmetry.
    rewrite Zmult_mod, Zmod_mod.
    reflexivity.
Qed.
Lemma crt_nonnegative_rem_eq_mod__crt_transition :
  forall a p,
    0 < p ->
    0 <= Z.rem a p ->
    Z.rem a p = a mod p.
Proof.
  intros a p Hp Hrem.
  apply Zmod_unique with (a ÷ p).
  - pose proof (Z.rem_bound_abs a p) as Hbound.
    rewrite Z.abs_eq in Hbound by lia.
    lia.
  - apply Z.quot_rem. lia.
Qed.
Lemma crt_quot_div_pos__crt_transition :
  forall a b,
    0 <= a ->
    0 <= b ->
    a ÷ b = a / b.
Proof.
  intros. apply Zquot_Zdiv_pos; assumption.
Qed.
Lemma crt_rem_eq_mod_of_nonnegative_dividend__crt_transition :
  forall a b,
    0 <= a ->
    0 < b ->
    Z.rem a b = a mod b.
Proof.
  intros. apply Zrem_Zmod_pos; assumption.
Qed.


(** The public progress relation compares corresponding initialized equations. *)
Definition CRTConsistentPrefix
    (remainders moduli : list Z) (processed result : Z) : Prop :=
  Forall2 (fun remainder modulus => result mod modulus = remainder)
    (sublist 0 processed remainders) (sublist 0 processed moduli).

Require Import AUXLib.MonotonicList.
Lemma crt_Forall2_Znth (P : Z -> Z -> Prop) (xs ys : list Z) :
  Zlength xs = Zlength ys ->
  (Forall2 P xs ys <->
   forall k, 0 <= k < Zlength ys -> P (Znth k xs 0) (Znth k ys 0)).
Proof.
  revert ys. induction xs as [|x xs IH]; intros [|y ys] Hlen;
    rewrite ?Zlength_nil, ?Zlength_cons in Hlen;
    try solve [pose proof (Zlength_nonneg xs); lia | pose proof (Zlength_nonneg ys); lia].
  - split; intros; [rewrite Zlength_nil in *; lia | constructor].
  - assert (Ht : Zlength xs = Zlength ys) by lia.
    rewrite (Forall2_cons_iff P x y xs ys), (IH ys Ht).
    rewrite Zlength_cons. pose proof (Zlength_nonneg ys) as Hnn.
    split.
    + intros [Hhead Htail] k Hk. destruct (Z.eq_dec k 0) as [->|Hne].
      * rewrite !Znth0_cons. exact Hhead.
      * rewrite !Znth_cons by lia. apply Htail. lia.
    + intros H. split.
      * specialize (H 0 ltac:(lia)). rewrite !Znth0_cons in H. exact H.
      * intros k Hk. specialize (H (k + 1) ltac:(lia)).
        rewrite !Znth_cons in H by lia.
        replace (k + 1 - 1) with k in H by lia. exact H.
Qed.

Lemma crt_input_from_explicit remainders moduli :
  Zlength remainders = Zlength moduli ->
  1 <= Zlength moduli ->
  Forall (Z.le 1) moduli -> Forall (Z.le 0) remainders ->
  Forall2 Z.lt remainders moduli ->
  (forall i j, 0 <= i /\ i < j /\ j < Zlength moduli ->
      Z.gcd (Znth i moduli 0) (Znth j moduli 0) = 1) ->
  CRTInputValid remainders moduli.
Proof.
  intros Hlen Hnonempty Hmod Hrem Hlt Hcoprime.
  unfold CRTInputValid. split; [exact Hlen|]. split; [exact Hnonempty|].
  split; [|exact Hcoprime]. intros i Hi.
  pose proof (proj1 (Forall_Znth (Z.le 1) 0 moduli) Hmod i Hi).
  pose proof (proj1 (Forall_Znth (Z.le 0) 0 remainders) Hrem i ltac:(lia)).
  pose proof (proj1 (crt_Forall2_Znth Z.lt remainders moduli Hlen) Hlt i Hi).
  lia.
Qed.

Lemma crt_prefix_indexed remainders moduli processed result :
  Zlength remainders = Zlength moduli ->
  0 <= processed <= Zlength moduli ->
  (CRTConsistentPrefix remainders moduli processed result <->
   CRTProcessedCongruences remainders moduli processed result).
Proof.
  intros Hlen Hp. unfold CRTConsistentPrefix, CRTProcessedCongruences.
  rewrite crt_Forall2_Znth by (rewrite !Zlength_sublist by lia; lia).
  rewrite Zlength_sublist by lia.
  replace (processed - 0) with processed by lia.
  split; intros H k Hk; specialize (H k Hk);
    rewrite !Znth_sublist in * by lia;
    replace (k + 0) with k in * by lia; exact H.
Qed.


Definition CRTUnprocessedZero (moduli : list Z) (processed result : Z) : Prop :=
  Forall (fun modulus => Z.rem result modulus = 0)
    (sublist processed (Zlength moduli) moduli).

Lemma crt_unprocessed_zero_indexed moduli processed result :
  0 <= processed <= Zlength moduli ->
  (CRTUnprocessedZero moduli processed result <->
   forall k, processed <= k < Zlength moduli ->
     Z.rem result (Znth k moduli 0) = 0).
Proof.
  intros Hp. unfold CRTUnprocessedZero.
  rewrite Forall_Znth with (d:=0), Zlength_sublist by lia.
  split.
  - intros H k Hk. specialize (H (k-processed) ltac:(lia)).
    rewrite Znth_sublist in H by lia.
    replace (k-processed+processed) with k in H by lia. exact H.
  - intros H k Hk. rewrite Znth_sublist by lia. apply H. lia.
Qed.

Lemma crt_machine_from_Forall remainders moduli :
  1 <= CRTProduct moduli <= 46340 ->
  (forall coefficient, -2147483648 <= coefficient <= 2147483647 ->
    Forall (Z.le (-2147483648))
      (map (Z.mul coefficient) (map (Z.div (CRTProduct moduli)) moduli)) /\
    Forall (Z.ge 2147483647)
      (map (Z.mul coefficient) (map (Z.div (CRTProduct moduli)) moduli))) ->
  CRTMachineSafe remainders moduli.
Proof.
  intros Hproduct Hsafe. unfold CRTMachineSafe. split; [exact Hproduct|].
  intros k coefficient Hk Hcoefficient.
  destruct (Hsafe coefficient Hcoefficient) as [Hlo Hhi].
  rewrite !Forall_map in Hlo, Hhi.
  pose proof (proj1 (Forall_Znth _ 0 moduli) Hlo k Hk) as Hlower.
  pose proof (proj1 (Forall_Znth _ 0 moduli) Hhi k Hk) as Hupper.
  cbn in Hlower, Hupper. lia.
Qed.

Lemma crt_rem_multiple m value modulus :
  modulus <> 0 -> (m | value) -> (m | modulus) -> (m | Z.rem value modulus).
Proof.
  intros Hmod [a Ha] [b Hb].
  pose proof (Z.quot_rem value modulus Hmod) as Hqr.
  exists (a - b * Z.quot value modulus). nia.
Qed.

Lemma crt_update_unprocessed_rem remainders moduli result i product x offset :
  CRTInputValid remainders moduli ->
  0 <= i < Zlength moduli ->
  product = CRTProduct moduli -> 0 < product ->
  CRTUnprocessedZero moduli i result ->
  CRTUnprocessedZero moduli (i+1)
    (Z.rem (result +
      Z.rem (Z.rem (x * Z.quot product (Znth i moduli 0)) product *
        Znth i remainders 0) product + offset * product) product).
Proof.
  intros Hvalid Hi Hproduct Hpositive Hz.
  pose proof (crt_product_factor_arithmetic__crt_transition remainders moduli i Hvalid Hi)
    as [Hfactor [Hgcd Hothers]].
  destruct Hvalid as [_ [_ [Hbounds Hcoprime]]].
  pose proof (Hbounds i Hi) as [Hmi _].
  rewrite Z.quot_div_nonneg by lia.
  apply (proj2 (crt_unprocessed_zero_indexed moduli (i+1) _ ltac:(lia))).
  pose proof (proj1 (crt_unprocessed_zero_indexed moduli i result ltac:(lia)) Hz) as Hz_indexed.
  clear Hz. rename Hz_indexed into Hz.
  intros k Hk. pose proof (Hbounds k ltac:(lia)) as [Hmk _].
  specialize (Hothers k ltac:(lia) ltac:(lia)).
  rewrite <- Hproduct in Hfactor, Hothers.
  assert (HP : (Znth k moduli 0 | product)).
  { rewrite <- Hfactor. apply Z.divide_mul_l. exact Hothers. }
  apply (proj2 (Z.rem_divide _ (Znth k moduli 0) ltac:(lia))).
  apply crt_rem_multiple; [lia| |exact HP].
  apply Z.divide_add_r.
  - apply Z.divide_add_r.
    + apply (proj1 (Z.rem_divide result (Znth k moduli 0) ltac:(lia))).
      apply Hz. lia.
    + apply crt_rem_multiple; [lia| |exact HP].
      apply Z.divide_mul_l.
      apply crt_rem_multiple; [lia| |exact HP].
      apply Z.divide_mul_r. exact Hothers.
  - apply Z.divide_mul_r. exact HP.
Qed.

Require Import SimpleC.SL.IntLib.

Lemma crt_reduced_int_cast a product :
  1 <= product <= 46340 ->
  signed_last_nbits (Z.rem a product) 32 = Z.rem a product.
Proof.
  intros Hp. apply signed_last_nbits_eq; [lia |].
  pose proof (Z.rem_bound_abs a product ltac:(lia)) as Hb.
  rewrite (Z.abs_eq product) in Hb by lia.
  change (-2147483648 <= Z.rem a product < 2147483648).
  destruct (Z_le_gt_dec 0 (Z.rem a product)).
  - rewrite Z.abs_eq in Hb by lia. lia.
  - rewrite Z.abs_neq in Hb by lia. lia.
Qed.
