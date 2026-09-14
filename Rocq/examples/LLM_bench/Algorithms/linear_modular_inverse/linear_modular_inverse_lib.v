From Coq Require Import ZArith List.
From AUXLib Require Import ListLib.

Import ListNotations.
Local Open Scope Z_scope.

Definition PrimeForLinearInverse (p : Z) : Prop :=
  2 <= p /\
  forall divisor,
    2 <= divisor < p ->
    p mod divisor <> 0.

Definition CanonicalModularInverse
    (p index value : Z) : Prop :=
  1 <= index < p /\
  0 < value < p /\
  exists coefficient,
    index * value + p * coefficient = 1.

Definition ModularInversePrefix
    (p next : Z) (values : list Z) : Prop :=
  Zlength values = next - 1 /\
  forall index,
    1 <= index < next ->
    CanonicalModularInverse p index
      (Znth (index - 1) values 0).

From Coq Require Import Lia Psatz.
Lemma linear_inverse_division_facts__recurrence_core :
  forall p i,
    PrimeForLinearInverse p ->
    2 <= i < p ->
    p = (p / i) * i + p mod i /\
    1 <= p / i /\
    1 <= p mod i < i /\
    0 < p - p / i < p.
Proof.
  intros p i [Hp Hprime] Hi.
  assert (Hi_pos : 0 < i) by lia.
  assert (Hi_nonzero : i <> 0) by lia.
  assert (Hdiv : p = (p / i) * i + p mod i).
  { pose proof (Z.div_mod p i Hi_nonzero) as H.
    nia. }
  assert (Hmod_bounds : 0 <= p mod i < i).
  { apply Z.mod_pos_bound. lia. }
  assert (Hmod_nonzero : p mod i <> 0).
  { apply Hprime. lia. }
  assert (Hquot : 1 <= p / i).
  { assert (Hquot_nonneg : 0 <= p / i) by (apply Z.div_pos; lia).
    nia. }
  repeat split; try nia.
Qed.
Lemma linear_inverse_product_bound__recurrence_core :
  forall p a b,
    2 <= p <= 46340 ->
    0 < a < p ->
    0 < b < p ->
    a * b <= 2147483647.
Proof.
  intros p a b Hp Ha Hb.
  nia.
Qed.
Lemma linear_inverse_prefix_extend__recurrence_core :
  forall p i q r values,
    PrimeForLinearInverse p ->
    2 <= i < p ->
    q = p / i ->
    r = p mod i ->
    ModularInversePrefix p i values ->
    ModularInversePrefix p (i + 1)
      (values ++ [((p - q) * Znth (r - 1) values 0) mod p]).
Proof.
  intros p i q r values Hprime Hi Hq Hr [Hlen Hprefix].
  subst q r.
  destruct (linear_inverse_division_facts__recurrence_core p i Hprime Hi)
    as [Hdiv [Hquot [[Hrem_pos Hrem_lt] Hdiff]]].
  assert (Hcanonical :
      CanonicalModularInverse p (p mod i)
        (Znth (p mod i - 1) values 0)).
  { apply Hprefix. lia. }
  destruct Hcanonical as
    [[Hindex_lo Hindex_hi] [[Hvalue_pos Hvalue_hi] [coefficient Hbezout]]].
  split.
  - rewrite Zlength_app, Zlength_cons, Zlength_nil, Hlen.
    lia.
  - intros index Hindex.
    destruct (Z_lt_ge_dec index i) as [Hindex_old | Hindex_new].
    + specialize (Hprefix index ltac:(lia)).
      rewrite app_Znth1 by lia.
      exact Hprefix.
    + assert (Hindex_eq : index = i) by lia.
      subst index.
      rewrite app_Znth2 by lia.
      rewrite Hlen.
      replace (i - 1 - (i - 1)) with 0 by lia.
      rewrite Znth0_cons.
      set (value := Znth (p mod i - 1) values 0) in *.
      set (raw := (p - p / i) * value).
      assert (Hp_pos : 0 < p).
      { destruct Hprime as [Hp _]. lia. }
      assert (Hraw_div : raw = p * (raw / p) + raw mod p).
      { pose proof (Z.div_mod raw p ltac:(lia)) as H.
        nia. }
      assert (Hmod_bounds : 0 <= raw mod p < p).
      { apply Z.mod_pos_bound. lia. }
      assert (Hqi : i * (p / i) = p - p mod i).
      { nia. }
      assert (Hraw_inverse :
          i * raw + p * (coefficient - i * value + value) = 1).
      { unfold raw.
        nia. }
      assert (Hinverse :
          i * (raw mod p) +
          p * (coefficient - i * value + value + i * (raw / p)) = 1).
      { rewrite Hraw_div in Hraw_inverse.
        nia. }
      split; [lia |].
      split.
      * split; [|lia].
        destruct (Z.eq_dec (raw mod p) 0) as [Hzero | Hnonzero].
        -- assert (Hmultiple :
               p * (coefficient - i * value + value + i * (raw / p)) = 1)
               by nia.
           assert (Hone_mod : 1 mod p = 0).
           { rewrite <- Hmultiple, Z.mul_comm.
             apply Z.mod_mul. lia. }
           assert (Hone_small : 1 mod p = 1).
           { apply Z.mod_small. lia. }
           lia.
        -- lia.
      * exists (coefficient - i * value + value + i * (raw / p)).
        exact Hinverse.
Qed.
