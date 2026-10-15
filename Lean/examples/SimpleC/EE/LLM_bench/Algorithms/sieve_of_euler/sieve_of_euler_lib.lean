import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.Prime
import MaxMinLib.Interface
import AUXLib.ListLib.LengthCompat

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_lib.Legacy
open AUXLib AUXLib.Prime
export AUXLib.Prime (prime prime_alt prime_ge_2)

def StrictPrime (p : Int) : Prop :=
  1 < p ∧
  ∀ d : Int,
    0 < d →
    Z.divide d p →
    d = 1 ∨ d = p

def LeastPrimeFactor (p k : Int) : Prop :=
  StrictPrime p ∧
  Z.divide p k ∧
  ∀ q : Int,
    StrictPrime q →
    Z.divide q k →
    p <= q

def FlagEntryFor (k value : Int) : Prop :=
  (StrictPrime k ∧ value = k) ∨
  (¬ StrictPrime k ∧ LeastPrimeFactor value k)

def LeastPrimeFlagList (n : Int) (flags : List Int) : Prop :=
  Zlength flags = n - 1 ∧
  ∀ k : Int,
    2 <= k ∧ k <= n →
    FlagEntryFor k (Znth (k - 2) flags 0)

def PrimePrefixList (bound tot : Int) (primes : List Int) : Prop :=
  0 <= tot ∧
  (∀ pos : Int,
    1 <= pos ∧ pos <= tot →
    StrictPrime (Znth (pos - 1) primes 0) ∧
    Znth (pos - 1) primes 0 <= bound) ∧
  (∀ p : Int,
    2 <= p ∧ p <= bound →
    (StrictPrime p ↔
     ∃ pos : Int,
       1 <= pos ∧ pos <= tot ∧
       Znth (pos - 1) primes 0 = p)) ∧
  (∀ p q : Int,
    1 <= p ∧ p < q ∧ q <= tot →
    Znth (p - 1) primes 0 < Znth (q - 1) primes 0)

def PrimeBounds (n tot : Int) (primes : List Int) : Prop :=
  ∀ pos : Int,
    1 <= pos ∧ pos <= tot →
    2 <= Znth (pos - 1) primes 0 ∧
    Znth (pos - 1) primes 0 <= n

def PriorNonDivisibility
    (current j : Int) (primes : List Int) : Prop :=
  ∀ pos : Int,
    1 <= pos ∧ pos < j →
    ¬ Z.divide (Znth (pos - 1) primes 0) current

def ProductIndex
    (current j : Int) (primes : List Int) : Int :=
  current * Znth (j - 1) primes 0

def FlagValue (flags : List Int) (k : Int) : Int :=
  Znth (k - 2) flags 0

def CurrentProductMarked
    (n current pos : Int) (flags primes : List Int) : Prop :=
  2 <= ProductIndex current pos primes ∧
  ProductIndex current pos primes <= n →
  FlagValue flags (ProductIndex current pos primes) =
    Znth (pos - 1) primes 0 ∧
  FlagValue flags (ProductIndex current pos primes) ≠
    ProductIndex current pos primes ∧
  FlagEntryFor (ProductIndex current pos primes)
    (FlagValue flags (ProductIndex current pos primes))

def CurrentBaseProgress
    (n current j : Int) (flags primes : List Int) : Prop :=
  ∀ pos : Int,
    1 <= pos ∧ pos < j →
    CurrentProductMarked n current pos flags primes

def EarlierLinearProduct
    (frontier k tot : Int) (primes : List Int) : Prop :=
  ∃ base pos : Int,
    2 <= base ∧ base < frontier ∧
    1 <= pos ∧ pos <= tot ∧
    Znth (pos - 1) primes 0 <= base ∧
    PriorNonDivisibility base pos primes ∧
    k = base * Znth (pos - 1) primes 0

def FutureSelfCompleteness
    (frontier k tot : Int) (primes : List Int) : Prop :=
  ¬ EarlierLinearProduct frontier k tot primes

def FutureFlagState
    (frontier k tot : Int) (flags primes : List Int) : Prop :=
  (FlagValue flags k ≠ k → FlagEntryFor k (FlagValue flags k)) ∧
  (FlagValue flags k = k → FutureSelfCompleteness frontier k tot primes)

def EulerFlagState
    (n frontier tot : Int) (flags primes : List Int) : Prop :=
  Zlength flags = n - 1 ∧
  ∀ k : Int,
    2 <= k ∧ k <= n →
    (k <= frontier → FlagEntryFor k (FlagValue flags k)) ∧
    (frontier < k → FutureFlagState frontier k tot flags primes)

def EulerSieveResult
    (n tot : Int) (flags primes : List Int) : Prop :=
  Zlength flags = n - 1 ∧
  Zlength primes = n ∧
  0 <= tot ∧ tot <= n ∧
  LeastPrimeFlagList n flags ∧
  PrimePrefixList n tot primes

def EulerInitPrefix (n next : Int) (flags : List Int) : Prop :=
  Zlength flags = n - 1 ∧
  ∀ k : Int,
    2 <= k ∧ k < next →
    Znth (k - 2) flags 0 = k

def EulerOuterState
    (n next tot : Int) (flags primes : List Int) : Prop :=
  EulerFlagState n next tot flags primes ∧
  Zlength primes = n ∧
  2 <= next ∧ next <= n + 1 ∧
  0 <= tot ∧ tot < next ∧
  PrimePrefixList (next - 1) tot primes ∧
  PrimeBounds n tot primes

def EulerInnerState
    (n current j tot : Int) (flags primes : List Int) : Prop :=
  EulerFlagState n current tot flags primes ∧
  Zlength primes = n ∧
  2 <= current ∧ current <= n ∧
  1 <= j ∧ j <= tot ∧
  0 < tot ∧ tot <= n ∧
  tot < current + 1 ∧
  PrimePrefixList current tot primes ∧
  PrimeBounds current tot primes ∧
  CurrentBaseProgress n current j flags primes ∧
  PriorNonDivisibility current j primes ∧
  (ProductIndex current j primes > n →
   EulerOuterState n (current + 1) tot flags primes)

def EulerInnerMarkedState
    (n current j tot : Int) (flags primes : List Int) : Prop :=
  EulerInnerState n current j tot flags primes ∧
  ProductIndex current j primes <= n ∧
  FlagEntryFor (ProductIndex current j primes)
    (Znth (j - 1) primes 0) ∧
  FlagValue flags (ProductIndex current j primes) =
    Znth (j - 1) primes 0 ∧
  CurrentBaseProgress n current (j + 1) flags primes ∧
  (Z.divide (Znth (j - 1) primes 0) current →
   EulerOuterState n (current + 1) tot flags primes) ∧
  (¬ Z.divide (Znth (j - 1) primes 0) current →
   EulerInnerState n current (j + 1) tot flags primes)

theorem StrictPrime_two__core_invariants :
  StrictPrime 2 := by
  refine ⟨by omega, ?_⟩
  intro d hd hv
  have := Int.le_of_dvd (by omega : (0:Int)<2) ((Z.divide_iff_dvd _ _).1 hv)
  omega

theorem EulerInitPrefix_start__core_invariants :
  ∀ (n : Int) (flags : List Int),
    Zlength flags = n - 1 →
    EulerInitPrefix n 2 flags := by
  intro n flags hlen
  exact ⟨hlen, by intro k hk; omega⟩

theorem EulerInitPrefix_step__core_invariants :
  ∀ (n i : Int) (flags : List Int),
    i <= n →
    2 <= i →
    EulerInitPrefix n i flags →
    EulerInitPrefix n (i + 1) (replace_Znth (i - 2) i flags) := by
  rintro n i flags hi h2 ⟨hlen, hpre⟩
  refine ⟨by rw [Zlength_replace_Znth]; exact hlen, ?_⟩
  intro k hk
  by_cases he : k=i
  · subst k
    exact Znth_replace_Znth_Same 0 flags (i-2) i (by omega)
  · rw [Znth_replace_Znth_Diff 0 flags (i-2) (k-2) i (by omega) (by omega) (by omega)]
    exact hpre k (by omega)

theorem EulerInitPrefix_finish_outer__core_invariants :
  ∀ (n i : Int) (flags primes : List Int),
    i > n →
    2 <= n →
    Zlength primes = n →
    EulerInitPrefix n i flags →
    EulerOuterState n 2 0 flags primes := by
  rintro n i flags primes hi hn hp ⟨hlen,hpre⟩
  refine ⟨⟨hlen, ?_⟩, hp, by omega, by omega, by omega, by omega, ?_, ?_⟩
  · intro k hk
    constructor
    · intro hkle
      have he : k=2 := by omega
      subst k
      exact .inl ⟨StrictPrime_two__core_invariants, hpre 2 (by omega)⟩
    · intro hkg
      refine ⟨?_, ?_⟩
      · intro hnon
        exact False.elim (hnon (hpre k (by omega)))
      · rintro _ ⟨base,pos,hb,hbf,_⟩
        omega
  · exact ⟨by omega, by intro pos hp; omega, by intro p hp; omega, by intro p q hpq; omega⟩
  · intro pos hp
    omega

theorem prime_to_StrictPrime__core_invariants :
  ∀ p : Int,
    prime p →
    StrictPrime p := by
  intro p hp
  have hgt := prime_ge_2 p hp
  refine ⟨by omega, ?_⟩
  intro d hd hdiv
  rcases prime_divisors p hp d hdiv with h | h | h | h <;> omega

theorem StrictPrime_to_prime__core_invariants :
  ∀ p : Int,
    StrictPrime p →
    prime p := by
  rintro p ⟨hp,hdiv⟩
  apply (prime_alt p).1
  refine ⟨hp, ?_⟩
  intro d hd hv
  rcases hdiv d (by omega) hv with h | h <;> omega

theorem StrictPrime_divisor_self_or_all__core_invariants :
  ∀ p q : Int,
    StrictPrime p →
    StrictPrime q →
    Z.divide q p →
    q <= p := by
  rintro p q ⟨hp,hpdiv⟩ ⟨hq,_⟩ hdiv
  rcases hpdiv q (by omega) hdiv with h | h <;> omega

theorem EulerOuterState_nonself_first_prime_facts__core_invariants :
  ∀ (n i tot : Int) (flags primes : List Int),
    Znth (i - 2) flags 0 ≠ i →
    i <= n →
    2 <= i →
    EulerOuterState n i tot flags primes →
    1 <= tot ∧
    2 <= Znth 0 primes 0 ∧
    Znth 0 primes 0 <= i := by
  rintro n i tot flags primes hn hi h2 ⟨⟨hlen,hflag⟩,hp,hi2,hil,ht0,hti,hpre,hbounds⟩
  change FlagValue flags i ≠ i at hn
  have hc := (hflag i ⟨h2,hi⟩).1 (Int.le_refl i)
  rcases hc with ⟨_,hs⟩ | ⟨_,hl⟩
  · exact False.elim (hn hs)
  · have hq2 := hl.1.1
    have hqle := Int.le_of_dvd (by omega : 0<i) ((Z.divide_iff_dvd _ _).1 hl.2.1)
    rcases (hpre.2.2.1 (FlagValue flags i) (by omega)).1 hl.1 with ⟨pos,hpos,hpost,hval⟩
    have ht : 1≤tot := by omega
    have hb := hbounds 1 ⟨by omega,ht⟩
    have hf := hpre.2.1 1 ⟨by omega,ht⟩
    simpa using (show 1≤tot ∧ 2≤Znth (1-1) primes 0 ∧ Znth (1-1) primes 0≤i from ⟨ht,hb.1,by have := hf.2; omega⟩)

theorem PrimeBounds_from_prefix__core_invariants :
  ∀ (bound tot : Int) (primes : List Int),
    PrimePrefixList bound tot primes →
    PrimeBounds bound tot primes := by
  rintro bound tot primes ⟨_,hat,_⟩ pos hp
  have h := hat pos hp
  exact ⟨by have := h.1.1; omega,h.2⟩

theorem PrimePrefixList_extend_nonprime_current__core_invariants :
  ∀ (current tot : Int) (primes : List Int),
    PrimePrefixList (current - 1) tot primes →
    ¬ StrictPrime current →
    PrimePrefixList current tot primes := by
  rintro current tot primes ⟨h0,hat,hcomplete,hsort⟩ hn
  refine ⟨h0, ?_, ?_, hsort⟩
  · intro pos hp
    have h := hat pos hp
    exact ⟨h.1,by have := h.2; omega⟩
  · intro p hp
    by_cases he : p=current
    · subst p
      constructor
      · exact fun h => False.elim (hn h)
      · rintro ⟨pos,hlo,hhi,hval⟩
        have h := (hat pos ⟨hlo,hhi⟩).2
        omega
    · exact hcomplete p (by omega)

theorem EulerOuterState_nonself_current_not_prime__core_invariants :
  ∀ (n i tot : Int) (flags primes : List Int),
    Znth (i - 2) flags 0 ≠ i →
    i <= n →
    2 <= i →
    EulerOuterState n i tot flags primes →
    ¬ StrictPrime i := by
  intro n i tot flags primes hn hi h2 hout
  have hc := (hout.1.2 i ⟨h2,hi⟩).1 (Int.le_refl i)
  rcases hc with ⟨_,he⟩ | ⟨hnot,_⟩
  · exact False.elim (hn he)
  · exact hnot

private theorem least_nat (P : Nat → Prop) (h : ∃ n, P n) :
    ∃ n, P n ∧ ∀ m, P m → n ≤ m := by
  classical
  rcases h with ⟨n,hn⟩
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hm : ∃ m, m<n ∧ P m
    · rcases hm with ⟨m,hm,hp⟩
      exact ih m hm hp
    · refine ⟨n,hn,?_⟩
      intro m hp
      by_cases hmn : n≤m
      · exact hmn
      · exact False.elim (hm ⟨m,by omega,hp⟩)

theorem least_prime_factor_exists__core_invariants :
  ∀ k : Int,
    1 < k →
    ∃ q : Int, LeastPrimeFactor q k := by
  intro k hk
  have hself : Z.divide (k.toNat : Int) k := by
    refine ⟨1, ?_⟩
    simp only [Int.one_mul]
    omega
  rcases least_nat (fun n => 1<(n:Int) ∧ Z.divide (n:Int) k)
      ⟨k.toNat,by omega,hself⟩ with ⟨q,hq,hmin⟩
  refine ⟨(q:Int), ⟨hq.1,?_⟩,hq.2,?_⟩
  · intro d hd hdq
    by_cases hd1 : d=1
    · exact .inl hd1
    · have hd2 : 1<d := by omega
      have hdk : Z.divide d k := (Z.divide_iff_dvd _ _).2
        (Int.dvd_trans ((Z.divide_iff_dvd _ _).1 hdq) ((Z.divide_iff_dvd _ _).1 hq.2))
      have hqd := hmin d.toNat ⟨by omega,by simpa [Int.toNat_of_nonneg (by omega : 0≤d)] using hdk⟩
      have hdle := Int.le_of_dvd (by omega : 0<(q:Int)) ((Z.divide_iff_dvd _ _).1 hdq)
      exact .inr (by omega)
  · intro r hr hd
    have hr2 := hr.1
    have := hmin r.toNat ⟨by omega,by simpa [Int.toNat_of_nonneg (by omega : 0≤r)] using hd⟩
    omega

theorem LeastPrimeFactor_lt_of_not_prime__core_invariants :
  ∀ q k : Int,
    1 < k →
    LeastPrimeFactor q k →
    ¬ StrictPrime k →
    q < k := by
  rintro q k hk ⟨hp,hd,_⟩ hn
  have hle := Int.le_of_dvd (by omega : 0<k) ((Z.divide_iff_dvd _ _).1 hd)
  by_cases he : q=k
  · subst q; exact False.elim (hn hp)
  · omega

theorem LeastPrimeFactor_le_complement__core_invariants :
  ∀ q k b : Int,
    1 < k →
    LeastPrimeFactor q k →
    ¬ StrictPrime k →
    k = b * q →
    q <= b := by
  intro q k b hk hl hn he
  have hqlt := LeastPrimeFactor_lt_of_not_prime__core_invariants q k hk hl hn
  have hq2 := hl.1.1
  have hb : 1<b := by
    by_cases h : 1<b
    · exact h
    · have := Int.mul_le_mul_of_nonneg_right (by omega : b≤1) (by omega : 0≤q)
      simp only [Int.one_mul] at this
      omega
  rcases least_prime_factor_exists__core_invariants b hb with ⟨r,hr⟩
  have hrdk : Z.divide r k := by
    rcases hr.2.1 with ⟨a,ha⟩
    exact ⟨q*a,by grind⟩
  have hqr := hl.2.2 r hr.1 hrdk
  have hrb := Int.le_of_dvd (by omega : 0<b) ((Z.divide_iff_dvd _ _).1 hr.2.1)
  omega

theorem PrimePrefixList_lookup__core_invariants :
  ∀ (bound tot p : Int) (primes : List Int),
    PrimePrefixList bound tot primes →
    2 <= p →
    p <= bound →
    StrictPrime p →
    ∃ pos : Int,
      1 <= pos ∧ pos <= tot ∧
      Znth (pos - 1) primes 0 = p := by
  intro bound tot p primes hp h2 hle hprime
  exact (hp.2.2.1 p ⟨h2,hle⟩).1 hprime

theorem FutureSelfCompleteness_successor_prime__core_invariants :
  ∀ (frontier tot : Int) (primes : List Int),
    2 <= frontier →
    PrimePrefixList frontier tot primes →
    FutureSelfCompleteness frontier (frontier + 1) tot primes →
    StrictPrime (frontier + 1) := by
  intro frontier tot primes hf hp hfuture
  apply Classical.byContradiction
  intro hn
  rcases least_prime_factor_exists__core_invariants (frontier+1) (by omega) with ⟨q,hq⟩
  have hqlt := LeastPrimeFactor_lt_of_not_prime__core_invariants q (frontier+1) (by omega) hq hn
  have hq2 := hq.1.1
  rcases PrimePrefixList_lookup__core_invariants frontier tot q primes hp (by omega) (by omega) hq.1 with ⟨pos,hpos,hpost,hval⟩
  rcases hq.2.1 with ⟨base,hbase⟩
  have hqb := LeastPrimeFactor_le_complement__core_invariants q (frontier+1) base (by omega) hq hn hbase
  have hb2 : 2≤base := by omega
  have hblt : base<frontier := by
    have := Int.mul_le_mul_of_nonneg_left (by omega : 2≤q) (by omega : 0≤base)
    omega
  apply hfuture
  refine ⟨base,pos,hb2,hblt,hpos,hpost,by omega,?_,by rw [hval]; exact hbase⟩
  intro prev hprev hd
  have hpr := (hp.2.1 prev ⟨hprev.1,by omega⟩).1
  have hs := hp.2.2.2 prev pos ⟨hprev.1,hprev.2,hpost⟩
  have hdk : Z.divide (Znth (prev-1) primes 0) (frontier+1) := by
    rcases hd with ⟨c,hc⟩
    exact ⟨q*c,by grind⟩
  have := hq.2.2 _ hpr hdk
  omega

theorem PrimePrefixList_first_le__core_invariants :
  ∀ (bound tot pos : Int) (primes : List Int),
    PrimePrefixList bound tot primes →
    1 <= pos →
    pos <= tot →
    Znth 0 primes 0 <= Znth (pos - 1) primes 0 := by
  intro bound tot pos primes hp h1 ht
  by_cases he : pos=1
  · subst pos; simp
  · have := hp.2.2.2 1 pos ⟨by omega,by omega,ht⟩
    simpa using (Int.le_of_lt this)

theorem FutureSelfCompleteness_advance_after_product_exit__core_invariants :
  ∀ (n frontier k tot : Int) (primes : List Int),
    2 <= frontier →
    k <= n →
    frontier + 1 < k →
    PrimePrefixList frontier tot primes →
    ProductIndex frontier 1 primes > n →
    FutureSelfCompleteness frontier k tot primes →
    FutureSelfCompleteness (frontier + 1) k tot primes := by
  intro n frontier k tot primes hf hkn hkg hp hexit hold
  rintro ⟨base,pos,hb2,hbf,hpos,hpost,hprime,hprior,hprod⟩
  by_cases he : base=frontier
  · subst base
    have hle := PrimePrefixList_first_le__core_invariants frontier tot pos primes hp hpos hpost
    have hm := Int.mul_le_mul_of_nonneg_left hle (by omega : 0≤frontier)
    simp only [ProductIndex,Int.sub_self] at hexit
    omega
  · exact hold ⟨base,pos,hb2,by omega,hpos,hpost,hprime,hprior,hprod⟩

private theorem classified_successor (n current tot : Int) (flags primes : List Int)
    (hc : 2≤current) (hp : PrimePrefixList current tot primes)
    (hflag : EulerFlagState n current tot flags primes) (k : Int)
    (hk : 2≤k ∧ k≤n) (hle : k≤current+1) : FlagEntryFor k (FlagValue flags k) := by
  by_cases hkc : k≤current
  · exact (hflag.2 k hk).1 hkc
  · have he : k=current+1 := by omega
    subst k
    have hf := (hflag.2 (current+1) hk).2 (by omega)
    by_cases hs : FlagValue flags (current+1)=current+1
    · exact .inl ⟨FutureSelfCompleteness_successor_prime__core_invariants current tot primes hc hp (hf.2 hs),hs⟩
    · exact hf.1 hs

theorem EulerFlagState_advance_after_product_exit__core_invariants :
  ∀ (n frontier tot : Int) (flags primes : List Int),
    2 <= frontier →
    frontier <= n →
    PrimePrefixList frontier tot primes →
    ProductIndex frontier 1 primes > n →
    EulerFlagState n frontier tot flags primes →
    EulerFlagState n (frontier + 1) tot flags primes := by
  intro n frontier tot flags primes hf hfn hp hexit hflag
  refine ⟨hflag.1,?_⟩
  intro k hk
  refine ⟨classified_successor n frontier tot flags primes hf hp hflag k hk,?_⟩
  intro hkg
  have hfuture := (hflag.2 k hk).2 (by omega)
  exact ⟨hfuture.1,fun hs => FutureSelfCompleteness_advance_after_product_exit__core_invariants n frontier k tot primes hf hk.2 hkg hp hexit (hfuture.2 hs)⟩

theorem EulerOuterState_advance_after_product_exit__core_invariants :
  ∀ (n current tot : Int) (flags primes : List Int),
    2 <= current →
    current <= n →
    EulerOuterState n current tot flags primes →
    PrimePrefixList current tot primes →
    ProductIndex current 1 primes > n →
    EulerOuterState n (current + 1) tot flags primes := by
  intro n current tot flags primes hc hcn hout hp hexit
  rcases hout with ⟨hf,hlen,hc2,hcle,ht0,htlt,_,hb⟩
  exact ⟨EulerFlagState_advance_after_product_exit__core_invariants n current tot flags primes hc hcn hp hexit hf,
    hlen,by omega,by omega,ht0,by omega,by simpa using hp,hb⟩

theorem EulerOuterState_nonself_inner_start__core_invariants :
  ∀ (n current tot : Int) (flags primes : List Int),
    Znth (current - 2) flags 0 ≠ current →
    current <= n →
    2 <= current →
    EulerOuterState n current tot flags primes →
    EulerInnerState n current 1 tot flags primes := by
  intro n current tot flags primes hn hcn hc hout
  have ht := (EulerOuterState_nonself_first_prime_facts__core_invariants n current tot flags primes hn hcn hc hout).1
  have hnot := EulerOuterState_nonself_current_not_prime__core_invariants n current tot flags primes hn hcn hc hout
  have hp := PrimePrefixList_extend_nonprime_current__core_invariants current tot primes hout.2.2.2.2.2.2.1 hnot
  rcases hout with ⟨hf,hlen,hc2,hcle,ht0,htlt,hpo,hb⟩
  refine ⟨hf,hlen,hc,hcn,by omega,ht,by omega,by omega,by omega,hp,
    PrimeBounds_from_prefix__core_invariants current tot primes hp,?_,?_,?_⟩
  · intro pos hpos; omega
  · intro pos hpos; omega
  · intro hexit
    exact EulerOuterState_advance_after_product_exit__core_invariants n current tot flags primes hc hcn
      ⟨hf,hlen,hc2,hcle,ht0,htlt,hpo,hb⟩ hp hexit

theorem EulerOuterState_self_current_prime__core_invariants :
  ∀ (n current tot : Int) (flags primes : List Int),
    Znth (current - 2) flags 0 = current →
    current <= n →
    2 <= current →
    EulerOuterState n current tot flags primes →
    StrictPrime current := by
  intro n current tot flags primes hs hcn hc hout
  have h := (hout.1.2 current ⟨hc,hcn⟩).1 (Int.le_refl current)
  change FlagValue flags current = current at hs
  rw [hs] at h
  rcases h with ⟨hp,_⟩ | ⟨hn,hp⟩
  · exact hp
  · exact False.elim (hn hp.1)

theorem PrimePrefixList_append_current__core_invariants :
  ∀ (n current tot : Int) (primes : List Int),
    Zlength primes = n →
    tot < n →
    PrimePrefixList (current - 1) tot primes →
    StrictPrime current →
    2 <= current →
    PrimePrefixList current (tot + 1)
      (replace_Znth ((tot + 1) - 1) current primes) := by
  rintro n current tot primes hlen ht ⟨ht0,hat,hcomplete,hsort⟩ hc hc2
  have hwrite : 0≤tot+1-1 ∧ tot+1-1<Zlength primes := by omega
  have same := Znth_replace_Znth_Same 0 primes (tot+1-1) current hwrite
  have diff : ∀ pos,1≤pos → pos≤tot →
      Znth (pos-1) (replace_Znth (tot+1-1) current primes) 0 = Znth (pos-1) primes 0 := by
    intro pos hp hpt
    exact Znth_replace_Znth_Diff 0 primes (tot+1-1) (pos-1) current hwrite (by omega) (by omega)
  have hnew : ∀ pos, 1≤pos ∧ pos≤tot+1 →
      StrictPrime (Znth (pos-1) (replace_Znth (tot+1-1) current primes) 0) ∧
      Znth (pos-1) (replace_Znth (tot+1-1) current primes) 0≤current := by
    intro pos hp
    by_cases he : pos=tot+1
    · subst pos; rw [same]; exact ⟨hc,by omega⟩
    · rw [diff pos hp.1 (by omega)]
      have h := hat pos ⟨hp.1,by omega⟩
      exact ⟨h.1,by have := h.2; omega⟩
  refine ⟨by omega,hnew,?_,?_⟩
  · intro p hp
    constructor
    · intro hprime
      by_cases he : p=current
      · subst p; exact ⟨tot+1,by omega,by omega,same⟩
      · rcases (hcomplete p (by omega)).1 hprime with ⟨pos,hlo,hhi,hval⟩
        exact ⟨pos,hlo,by omega,by rw [diff pos hlo hhi]; exact hval⟩
    · rintro ⟨pos,hlo,hhi,hval⟩
      rw [←hval]
      exact (hnew pos ⟨hlo,hhi⟩).1
  · intro p q hpq
    rw [diff p hpq.1 (by omega)]
    by_cases he : q=tot+1
    · subst q; rw [same]
      have := (hat p ⟨hpq.1,by omega⟩).2
      omega
    · rw [diff q (by omega) (by omega)]
      exact hsort p q ⟨hpq.1,hpq.2.1,by omega⟩

theorem EulerFlagState_prime_append_current__core_invariants :
  ∀ (n current tot : Int) (flags primes : List Int),
    2 <= current →
    current <= n →
    Zlength primes = n →
    tot < n →
    EulerFlagState n current tot flags primes →
    EulerFlagState n current (tot + 1) flags
      (replace_Znth ((tot + 1) - 1) current primes) := by
  intro n current tot flags primes hc hcn hlen ht hflag
  refine ⟨hflag.1,?_⟩
  intro k hk
  refine ⟨(hflag.2 k hk).1,?_⟩
  intro hkg
  have hf := (hflag.2 k hk).2 hkg
  refine ⟨hf.1,?_⟩
  rintro hs ⟨base,pos,hb2,hbf,hpos,hpost,hpb,hprior,hprod⟩
  have ht0 : 0≤tot := by omega
  have hw : 0≤tot+1-1 ∧ tot+1-1<Zlength primes := by omega
  by_cases he : pos=tot+1
  · subst pos
    rw [Znth_replace_Znth_Same 0 primes (tot+1-1) current hw] at hpb
    omega
  · have hpt : pos≤tot := by omega
    have diff : ∀ prev,1≤prev → prev≤tot →
        Znth (prev-1) (replace_Znth (tot+1-1) current primes) 0 = Znth (prev-1) primes 0 := by
      intro prev hp hpv
      exact Znth_replace_Znth_Diff 0 primes (tot+1-1) (prev-1) current hw (by omega) (by omega)
    rw [diff pos hpos hpt] at hpb hprod
    apply hf.2 hs
    refine ⟨base,pos,hb2,hbf,hpos,hpt,hpb,?_,hprod⟩
    intro prev hprev hdiv
    apply hprior prev hprev
    rw [diff prev hprev.1 (by omega)]
    exact hdiv

theorem EulerOuterState_self_inner_start__core_invariants :
  ∀ (n current tot : Int) (flags primes : List Int),
    Znth (current - 2) flags 0 = current →
    current <= n →
    2 <= current →
    EulerOuterState n current tot flags primes →
    EulerInnerState n current 1 (tot + 1) flags
      (replace_Znth ((tot + 1) - 1) current primes) := by
  intro n current tot flags primes hs hcn hc hout
  have hprime := EulerOuterState_self_current_prime__core_invariants n current tot flags primes hs hcn hc hout
  rcases hout with ⟨hf,hlen,hc2,hcle,ht0,htlt,hpo,hb⟩
  have hp := PrimePrefixList_append_current__core_invariants n current tot primes hlen (by omega) hpo hprime hc
  have hflag := EulerFlagState_prime_append_current__core_invariants n current tot flags primes hc hcn hlen (by omega) hf
  have hlen' : Zlength (replace_Znth (tot+1-1) current primes)=n := by rw [Zlength_replace_Znth]; exact hlen
  have hbounds := PrimeBounds_from_prefix__core_invariants current (tot+1) _ hp
  refine ⟨hflag,hlen',hc,hcn,by omega,by omega,by omega,by omega,by omega,hp,hbounds,?_,?_,?_⟩
  · intro pos hpos; omega
  · intro pos hpos; omega
  · intro hexit
    refine ⟨EulerFlagState_advance_after_product_exit__core_invariants n current (tot+1) flags _ hc hcn hp hexit hflag,
      hlen',by omega,by omega,by omega,by omega,by simpa using hp,?_⟩
    intro pos hpos
    have h := hbounds pos hpos
    exact ⟨h.1,by have := h.2; omega⟩

theorem EulerOuterState_self_first_prime_facts__core_invariants :
  ∀ (n current tot : Int) (flags primes : List Int),
    Znth (current - 2) flags 0 = current →
    current <= n →
    2 <= current →
    EulerOuterState n current tot flags primes →
    2 <= Znth 0 (replace_Znth ((tot + 1) - 1) current primes) 0 ∧
    Znth 0 (replace_Znth ((tot + 1) - 1) current primes) 0 <= current := by
  intro n current tot flags primes hs hcn hc hout
  have hi := EulerOuterState_self_inner_start__core_invariants n current tot flags primes hs hcn hc hout
  have ht := hi.2.2.2.2.2.1
  have hb := hi.2.2.2.2.2.2.2.2.2.2.1 1 ⟨by omega,ht⟩
  simpa using hb

theorem StrictPrime_product_not_prime__core_invariants :
  ∀ a p : Int,
    2 <= a →
    StrictPrime p →
    ¬ StrictPrime (a * p) := by
  intro a p ha hp hprod
  have hp2 := hp.1
  have hmul := Int.mul_le_mul_of_nonneg_right ha (by omega : 0≤p)
  rcases hprod.2 p (by omega) ⟨a,rfl⟩ with h | h <;> omega

theorem LeastPrimeFactor_current_product__core_invariants :
  ∀ (current j tot : Int) (primes : List Int),
    2 <= current →
    1 <= j →
    j <= tot →
    PrimePrefixList current tot primes →
    PriorNonDivisibility current j primes →
    LeastPrimeFactor (Znth (j - 1) primes 0)
      (current * Znth (j - 1) primes 0) := by
  intro current j tot primes hc hj hjt hp hprior
  have hselected := (hp.2.1 j ⟨hj,hjt⟩).1
  refine ⟨hselected,⟨current,rfl⟩,?_⟩
  intro q hq hd
  rcases prime_mult q (StrictPrime_to_prime__core_invariants q hq) current (Znth (j-1) primes 0) hd with hd | hd
  · have hq2 := hq.1
    have hqle := Int.le_of_dvd (by omega : 0<current) ((Z.divide_iff_dvd _ _).1 hd)
    rcases PrimePrefixList_lookup__core_invariants current tot q primes hp (by omega) hqle hq with ⟨pos,hpos,hpost,hval⟩
    by_cases hlt : pos<j
    · exact False.elim (hprior pos ⟨hpos,hlt⟩ (by rw [hval]; exact hd))
    · by_cases he : pos=j
      · subst pos; omega
      · have hs := hp.2.2.2 j pos ⟨hj,by omega,hpost⟩
        omega
  · have hq2 := hq.1
    rcases hselected.2 q (by omega) hd with h | h <;> omega

theorem FlagEntryFor_current_product__core_invariants :
  ∀ (current j tot : Int) (primes : List Int),
    2 <= current →
    1 <= j →
    j <= tot →
    PrimePrefixList current tot primes →
    PriorNonDivisibility current j primes →
    FlagEntryFor (current * Znth (j - 1) primes 0)
      (Znth (j - 1) primes 0) := by
  intro current j tot primes hc hj hjt hp hprior
  exact .inr ⟨StrictPrime_product_not_prime__core_invariants current _ hc (hp.2.1 j ⟨hj,hjt⟩).1,
    LeastPrimeFactor_current_product__core_invariants current j tot primes hc hj hjt hp hprior⟩

theorem EulerFlagState_advance_after_inner_product_exit__core_invariants :
  ∀ (n current j tot : Int) (flags primes : List Int),
    2 <= current →
    current <= n →
    1 <= j →
    j <= tot →
    PrimePrefixList current tot primes →
    EulerFlagState n current tot flags primes →
    CurrentBaseProgress n current j flags primes →
    ProductIndex current j primes > n →
    EulerFlagState n (current + 1) tot flags primes := by
  intro n current j tot flags primes hc hcn hj hjt hp hf hprogress hexit
  refine ⟨hf.1,?_⟩
  intro k hk
  refine ⟨classified_successor n current tot flags primes hc hp hf k hk,?_⟩
  intro hkg
  have hfuture := (hf.2 k hk).2 (by omega)
  refine ⟨hfuture.1,?_⟩
  rintro hs ⟨base,pos,hb2,hbc,hpos,hpost,hpb,hprior,hprod⟩
  by_cases he : base=current
  · subst base
    by_cases hlt : pos<j
    · have hr : 2≤ProductIndex current pos primes ∧ ProductIndex current pos primes≤n := by
        change 2≤current*Znth (pos-1) primes 0 ∧ current*Znth (pos-1) primes 0≤n
        omega
      have hn := (hprogress pos ⟨hpos,hlt⟩ hr).2.1
      change FlagValue flags (current*Znth (pos-1) primes 0) ≠ current*Znth (pos-1) primes 0 at hn
      rw [←hprod] at hn
      exact hn hs
    · have hle : Znth (j-1) primes 0≤Znth (pos-1) primes 0 := by
        by_cases heq : pos=j
        · subst pos; omega
        · have := hp.2.2.2 j pos ⟨hj,by omega,hpost⟩
          omega
      have hm := Int.mul_le_mul_of_nonneg_left hle (by omega : 0≤current)
      unfold ProductIndex at hexit
      omega
  · exact hfuture.2 hs ⟨base,pos,hb2,by omega,hpos,hpost,hpb,hprior,hprod⟩

theorem EulerFlagState_advance_after_inner_divide__core_invariants :
  ∀ (n current j tot : Int) (flags primes : List Int),
    2 <= current →
    current <= n →
    1 <= j →
    j <= tot →
    PrimePrefixList current tot primes →
    EulerFlagState n current tot flags primes →
    CurrentBaseProgress n current (j + 1) flags primes →
    PriorNonDivisibility current j primes →
    Z.divide (Znth (j - 1) primes 0) current →
    EulerFlagState n (current + 1) tot flags primes := by
  intro n current j tot flags primes hc hcn hj hjt hp hf hprogress hprior hdivide
  refine ⟨hf.1,?_⟩
  intro k hk
  refine ⟨classified_successor n current tot flags primes hc hp hf k hk,?_⟩
  intro hkg
  have hfuture := (hf.2 k hk).2 (by omega)
  refine ⟨hfuture.1,?_⟩
  rintro hs ⟨base,pos,hb2,hbc,hpos,hpost,hpb,hpriorprod,hprod⟩
  by_cases he : base=current
  · subst base
    by_cases hlt : pos<j+1
    · have hr : 2≤ProductIndex current pos primes ∧ ProductIndex current pos primes≤n := by
        change 2≤current*Znth (pos-1) primes 0 ∧ current*Znth (pos-1) primes 0≤n
        omega
      have hn := (hprogress pos ⟨hpos,hlt⟩ hr).2.1
      change FlagValue flags (current*Znth (pos-1) primes 0) ≠ current*Znth (pos-1) primes 0 at hn
      rw [←hprod] at hn
      exact hn hs
    · exact hpriorprod j ⟨hj,by omega⟩ hdivide
  · exact hfuture.2 hs ⟨base,pos,hb2,by omega,hpos,hpost,hpb,hpriorprod,hprod⟩

theorem PriorNonDivisibility_nondivide_next_index__core_invariants :
  ∀ (current j tot : Int) (primes : List Int),
    2 <= current →
    1 <= j →
    j <= tot →
    PrimePrefixList current tot primes →
    PriorNonDivisibility current j primes →
    ¬ Z.divide (Znth (j - 1) primes 0) current →
    j + 1 <= tot := by
  intro current j tot primes hc hj hjt hp hprior hn
  rcases least_prime_factor_exists__core_invariants current (by omega) with ⟨q,hq⟩
  have hq2 := hq.1.1
  have hql := Int.le_of_dvd (by omega : 0<current) ((Z.divide_iff_dvd _ _).1 hq.2.1)
  rcases PrimePrefixList_lookup__core_invariants current tot q primes hp (by omega) hql hq.1 with ⟨pos,hpos,hpost,hval⟩
  by_cases hlt : pos<j
  · exact False.elim (hprior pos ⟨hpos,hlt⟩ (by rw [hval]; exact hq.2.1))
  · by_cases he : pos=j
    · subst pos
      exact False.elim (hn (by rw [hval]; exact hq.2.1))
    · omega

theorem EulerInnerState_mark_product__core_invariants :
  ∀ (n current j tot : Int) (flags primes : List Int),
    2 <= current →
    current <= n →
    1 <= j →
    j <= tot →
    ProductIndex current j primes <= n →
    EulerInnerState n current j tot flags primes →
    EulerInnerMarkedState n current j tot
      (replace_Znth (ProductIndex current j primes - 2)
         (Znth (j - 1) primes 0) flags)
      primes := by
  intro n current j tot flags primes hc hcn hj hjt hprodle hinner
  rcases hinner with ⟨hflag,hlen,hc2,hcle,hj2,hjle,ht0,htn,htc,hpre,hbounds,hprogress,hprior,hexitold⟩
  have hflen := hflag.1
  have hsel := hbounds j ⟨hj,hjt⟩
  let selected := Znth (j-1) primes 0
  let product := ProductIndex current j primes
  let marked := replace_Znth (product-2) selected flags
  have hs2 : 2≤selected := hsel.1
  have hpeq : product=current*selected := rfl
  have hpgt : current<product := by
    have := Int.mul_le_mul_of_nonneg_left hs2 (by omega : 0≤current)
    omega
  have hsne : selected≠product := by
    have := Int.mul_le_mul_of_nonneg_right hc (by omega : 0≤selected)
    omega
  have hprange : 2≤product ∧ product≤n := ⟨by omega,hprodle⟩
  have hwrite : 0≤product-2 ∧ product-2<Zlength flags := by omega
  have hsame : FlagValue marked product=selected := Znth_replace_Znth_Same 0 flags (product-2) selected hwrite
  have hdiff : ∀ k, 2≤k ∧ k≤n → k≠product → FlagValue marked k=FlagValue flags k := by
    intro k hk hn
    exact Znth_replace_Znth_Diff 0 flags (product-2) (k-2) selected hwrite (by omega) (by omega)
  have hentry : FlagEntryFor product selected :=
    FlagEntryFor_current_product__core_invariants current j tot primes hc hj hjt hpre hprior
  have hmarked : EulerFlagState n current tot marked primes := by
    refine ⟨?_,?_⟩
    · change Zlength (replace_Znth (product-2) selected flags)=n-1
      rw [Zlength_replace_Znth]
      exact hflen
    · intro k hk
      constructor
      · intro hkle
        rw [hdiff k hk (by omega)]
        exact (hflag.2 k hk).1 hkle
      · intro hkg
        by_cases he : k=product
        · subst k
          refine ⟨?_,?_⟩
          · intro _; rw [hsame]; exact hentry
          · intro hs
            rw [hsame] at hs
            exact False.elim (hsne hs)
        · have hfuture := (hflag.2 k hk).2 hkg
          unfold FutureFlagState
          rw [hdiff k hk he]
          exact hfuture
  have hprogressj : CurrentBaseProgress n current j marked primes := by
    intro pos hpos hr
    have hne : ProductIndex current pos primes≠product := by
      have hs := hpre.2.2.2 pos j ⟨hpos.1,hpos.2,hjt⟩
      have hm := Int.mul_lt_mul_of_pos_left hs (by omega : 0<current)
      change current*Znth (pos-1) primes 0 ≠ current*Znth (j-1) primes 0
      omega
    have h := hprogress pos hpos hr
    rw [hdiff (ProductIndex current pos primes) hr hne]
    exact h
  have hprogressnext : CurrentBaseProgress n current (j+1) marked primes := by
    intro pos hpos
    by_cases he : pos=j
    · subst pos
      intro _
      change FlagValue marked product=selected ∧ FlagValue marked product≠product ∧ FlagEntryFor product (FlagValue marked product)
      rw [hsame]
      exact ⟨rfl,hsne,hentry⟩
    · exact hprogressj pos ⟨hpos.1,by omega⟩
  have hb_n : PrimeBounds n tot primes := by
    intro pos hpos
    have h := hbounds pos hpos
    exact ⟨h.1,by have := h.2; omega⟩
  have hi : EulerInnerState n current j tot marked primes :=
    ⟨hmarked,hlen,hc,hcn,hj,hjt,ht0,htn,htc,hpre,hbounds,hprogressj,hprior,by intro h; omega⟩
  have hdivide : Z.divide selected current → EulerOuterState n (current+1) tot marked primes := by
    intro hd
    refine ⟨EulerFlagState_advance_after_inner_divide__core_invariants n current j tot marked primes hc hcn hj hjt hpre hmarked hprogressnext hprior hd,
      hlen,by omega,by omega,by omega,htc,by simpa using hpre,hb_n⟩
  have hnondivide : ¬Z.divide selected current → EulerInnerState n current (j+1) tot marked primes := by
    intro hn
    have hjnext := PriorNonDivisibility_nondivide_next_index__core_invariants current j tot primes hc hj hjt hpre hprior hn
    have hpriornext : PriorNonDivisibility current (j+1) primes := by
      intro pos hpos
      by_cases he : pos=j
      · subst pos; exact hn
      · exact hprior pos ⟨hpos.1,by omega⟩
    refine ⟨hmarked,hlen,hc,hcn,by omega,hjnext,ht0,htn,htc,hpre,hbounds,hprogressnext,hpriornext,?_⟩
    intro he
    exact ⟨EulerFlagState_advance_after_inner_product_exit__core_invariants n current (j+1) tot marked primes hc hcn (by omega) hjnext hpre hmarked hprogressnext he,
      hlen,by omega,by omega,by omega,htc,by simpa using hpre,hb_n⟩
  exact ⟨hi,hprodle,hentry,hsame,hprogressnext,hdivide,hnondivide⟩

end SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_lib.Legacy

namespace SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_lib
open AUXLib

abbrev StrictPrime := Legacy.StrictPrime
abbrev ProductIndex := Legacy.ProductIndex
abbrev FlagValue := Legacy.FlagValue
abbrev PrimeBounds := Legacy.PrimeBounds

def LeastPrimeFactor (p k : Int) : Prop :=
  MaxMinLib.min_value_of_subset (LE.le (α := Int))
    (fun q => StrictPrime q ∧ Z.divide q k) id p
def FlagEntryFor (k value : Int) : Prop :=
  (StrictPrime k ∧ value = k) ∨ (¬ StrictPrime k ∧ LeastPrimeFactor value k)
def LeastPrimeFlagList (n : Int) (flags : List Int) : Prop :=
  ∀ k, 2 ≤ k ∧ k ≤ n → FlagEntryFor k (Znth (k-2) flags 0)
def PrimePrefixList (bound tot : Int) (primes : List Int) : Prop :=
  Forall StrictPrime (sublist 0 tot primes) ∧
  Forall (GE.ge bound) (sublist 0 tot primes) ∧
  (∀ p, 2 ≤ p ∧ p ≤ bound →
    (StrictPrime p ↔ ∃ pos, 1 ≤ pos ∧ pos ≤ tot ∧ Znth (pos-1) primes 0 = p)) ∧
  (∀ p q, 1 ≤ p ∧ p < q ∧ q ≤ tot → Znth (p-1) primes 0 < Znth (q-1) primes 0)
def PriorNonDivisibility (current j : Int) (primes : List Int) : Prop :=
  Forall (fun p => ¬ Z.divide p current) (sublist 0 (j-1) primes)
def CurrentProductMarked (n current pos : Int) (flags primes : List Int) : Prop :=
  2 ≤ ProductIndex current pos primes ∧ ProductIndex current pos primes ≤ n →
  FlagValue flags (ProductIndex current pos primes) = Znth (pos-1) primes 0 ∧
  FlagValue flags (ProductIndex current pos primes) ≠ ProductIndex current pos primes ∧
  FlagEntryFor (ProductIndex current pos primes) (FlagValue flags (ProductIndex current pos primes))
def CurrentBaseProgress (n current j : Int) (flags primes : List Int) : Prop :=
  ∀ pos, 1 ≤ pos ∧ pos < j → CurrentProductMarked n current pos flags primes
def EarlierLinearProduct (frontier k tot : Int) (primes : List Int) : Prop :=
  ∃ base pos, 2 ≤ base ∧ base < frontier ∧ 1 ≤ pos ∧ pos ≤ tot ∧
    Znth (pos-1) primes 0 ≤ base ∧ PriorNonDivisibility base pos primes ∧
    k = base * Znth (pos-1) primes 0
def FutureSelfCompleteness (frontier k tot : Int) (primes : List Int) : Prop :=
  ¬ EarlierLinearProduct frontier k tot primes
def FutureFlagState (frontier k tot : Int) (flags primes : List Int) : Prop :=
  (FlagValue flags k ≠ k → FlagEntryFor k (FlagValue flags k)) ∧
  (FlagValue flags k = k → FutureSelfCompleteness frontier k tot primes)
def EulerFlagState (n frontier tot : Int) (flags primes : List Int) : Prop :=
  ∀ k, 2 ≤ k ∧ k ≤ n → (k ≤ frontier → FlagEntryFor k (FlagValue flags k)) ∧
    (frontier < k → FutureFlagState frontier k tot flags primes)
def EulerSieveResult (n tot : Int) (flags primes : List Int) : Prop :=
  LeastPrimeFlagList n flags ∧ PrimePrefixList n tot primes
def EulerInitPrefix (n next : Int) (flags : List Int) : Prop :=
  ∀ k, 2 ≤ k ∧ k < next → Znth (k-2) flags 0 = k
def EulerOuterState (n next tot : Int) (flags primes : List Int) : Prop :=
  EulerFlagState n next tot flags primes ∧ PrimePrefixList (next-1) tot primes
def EulerInnerState (n current j tot : Int) (flags primes : List Int) : Prop :=
  EulerFlagState n current tot flags primes ∧ PrimePrefixList current tot primes ∧
  CurrentBaseProgress n current j flags primes ∧ PriorNonDivisibility current j primes ∧
  (ProductIndex current j primes > n → EulerOuterState n (current+1) tot flags primes)
def EulerInnerMarkedState (n current j tot : Int) (flags primes : List Int) : Prop :=
  EulerInnerState n current j tot flags primes ∧
  FlagEntryFor (ProductIndex current j primes) (Znth (j-1) primes 0) ∧
  FlagValue flags (ProductIndex current j primes) = Znth (j-1) primes 0 ∧
  CurrentBaseProgress n current (j+1) flags primes ∧
  (Z.divide (Znth (j-1) primes 0) current → EulerOuterState n (current+1) tot flags primes) ∧
  (¬ Z.divide (Znth (j-1) primes 0) current → EulerInnerState n current (j+1) tot flags primes)

theorem least_factor_legacy (p k : Int) : LeastPrimeFactor p k ↔ Legacy.LeastPrimeFactor p k := by
  constructor
  · rintro ⟨q, ⟨⟨hp, hd⟩, hm⟩, he⟩
    change q = p at he; subst q
    exact ⟨hp, hd, by intro r hr hd; exact hm r ⟨hr, hd⟩⟩
  · rintro ⟨hp, hd, hm⟩
    exact ⟨p, ⟨⟨hp, hd⟩, by intro q hq; exact hm q hq.1 hq.2⟩, rfl⟩

theorem flag_entry_legacy (k value : Int) : FlagEntryFor k value ↔ Legacy.FlagEntryFor k value := by
  unfold FlagEntryFor Legacy.FlagEntryFor
  rw [least_factor_legacy]
theorem flag_list_facts (n : Int) (flags : List Int) :
    Legacy.LeastPrimeFlagList n flags ↔ Zlength flags = n-1 ∧ LeastPrimeFlagList n flags := by
  simp only [Legacy.LeastPrimeFlagList, LeastPrimeFlagList, flag_entry_legacy]

private theorem forall_indexed {A : Type} (P : A → Prop) (l : List A) (d : A) :
    Forall P l ↔ ∀ i, 0 ≤ i ∧ i < Zlength l → P (Znth i l d) := by
  rw [Forall.iff_forall_mem]
  constructor
  · intro h i hi
    have hn : i.toNat < l.length := by change 0 ≤ i ∧ i < (l.length : Int) at hi; omega
    have hm := h l[i.toNat] (List.mem_iff_getElem.mpr ⟨i.toNat, hn, rfl⟩)
    simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using hm
  · intro h v hv
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp hv
    have hi : 0 ≤ (n : Int) ∧ (n : Int) < Zlength l := by change 0 ≤ (n : Int) ∧ (n : Int) < (l.length : Int); omega
    have hh := h n hi
    simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn, Option.getD_some] using hh

theorem prefix_Forall (P : Int → Prop) (primes : List Int) (tot : Int)
    (ht : 0 ≤ tot ∧ tot ≤ Zlength primes) :
    Forall P (sublist 0 tot primes) ↔ ∀ pos, 1 ≤ pos ∧ pos ≤ tot → P (Znth (pos-1) primes 0) := by
  rw [forall_indexed P _ 0]
  have hlen : Zlength (sublist 0 tot primes) = tot := by
    unfold Zlength
    rw [sublist_length 0 tot primes ⟨by omega, ht.1⟩ ht.2]
    simpa only [Int.sub_zero] using Int.toNat_of_nonneg ht.1
  constructor
  · intro h pos hp
    have hh := h (pos-1) (by rw [hlen]; omega)
    rw [Znth_sublist 0 0 (pos-1) tot primes (by omega) (by omega), Int.add_zero] at hh
    exact hh
  · intro h pos hp
    rw [hlen] at hp
    rw [Znth_sublist 0 0 pos tot primes (by omega) (by omega), Int.add_zero]
    simpa only [Int.add_sub_cancel] using h (pos+1) (by omega)

theorem prime_prefix_legacy (bound tot : Int) (primes : List Int)
    (ht : 0 ≤ tot ∧ tot ≤ Zlength primes) :
    PrimePrefixList bound tot primes ↔ Legacy.PrimePrefixList bound tot primes := by
  unfold PrimePrefixList Legacy.PrimePrefixList
  rw [prefix_Forall _ primes tot ht, prefix_Forall _ primes tot ht]
  constructor
  · rintro ⟨hp, hb, hr⟩
    exact ⟨ht.1, (by intro pos hs; exact ⟨hp pos hs, hb pos hs⟩), hr⟩
  · rintro ⟨_, hv, hr⟩
    exact ⟨(by intro pos hs; exact (hv pos hs).1), (by intro pos hs; exact (hv pos hs).2), hr⟩

theorem prior_nondiv_legacy (current j : Int) (primes : List Int)
    (hj : 1 ≤ j ∧ j ≤ Zlength primes+1) :
    PriorNonDivisibility current j primes ↔ Legacy.PriorNonDivisibility current j primes := by
  unfold PriorNonDivisibility Legacy.PriorNonDivisibility
  rw [prefix_Forall _ primes (j-1) (by omega)]
  constructor <;> intro h pos hp <;> exact h pos (by omega)

theorem current_marked_legacy (n current pos : Int) (flags primes : List Int) :
    CurrentProductMarked n current pos flags primes ↔ Legacy.CurrentProductMarked n current pos flags primes := by
  simp only [CurrentProductMarked, Legacy.CurrentProductMarked, flag_entry_legacy]
theorem current_progress_legacy (n current j : Int) (flags primes : List Int) :
    CurrentBaseProgress n current j flags primes ↔ Legacy.CurrentBaseProgress n current j flags primes := by
  simp only [CurrentBaseProgress, Legacy.CurrentBaseProgress, current_marked_legacy]

theorem earlier_product_legacy (frontier k tot : Int) (primes : List Int)
    (ht : 0 ≤ tot ∧ tot ≤ Zlength primes) :
    EarlierLinearProduct frontier k tot primes ↔ Legacy.EarlierLinearProduct frontier k tot primes := by
  constructor
  · rintro ⟨base, pos, hb, hf, hp, hpt, hv, hn, he⟩
    exact ⟨base, pos, hb, hf, hp, hpt, hv, (prior_nondiv_legacy base pos primes (by omega)).mp hn, he⟩
  · rintro ⟨base, pos, hb, hf, hp, hpt, hv, hn, he⟩
    exact ⟨base, pos, hb, hf, hp, hpt, hv, (prior_nondiv_legacy base pos primes (by omega)).mpr hn, he⟩

theorem future_self_legacy (frontier k tot : Int) (primes : List Int)
    (ht : 0 ≤ tot ∧ tot ≤ Zlength primes) :
    FutureSelfCompleteness frontier k tot primes ↔ Legacy.FutureSelfCompleteness frontier k tot primes := by
  unfold FutureSelfCompleteness Legacy.FutureSelfCompleteness
  rw [earlier_product_legacy frontier k tot primes ht]
theorem future_flag_legacy (frontier k tot : Int) (flags primes : List Int)
    (ht : 0 ≤ tot ∧ tot ≤ Zlength primes) :
    FutureFlagState frontier k tot flags primes ↔ Legacy.FutureFlagState frontier k tot flags primes := by
  simp only [FutureFlagState, Legacy.FutureFlagState, flag_entry_legacy,
    future_self_legacy frontier k tot primes ht]
theorem flag_state_facts (n frontier tot : Int) (flags primes : List Int)
    (ht : 0 ≤ tot ∧ tot ≤ Zlength primes) :
    Legacy.EulerFlagState n frontier tot flags primes ↔
      Zlength flags = n-1 ∧ EulerFlagState n frontier tot flags primes := by
  simp only [Legacy.EulerFlagState, EulerFlagState, flag_entry_legacy,
    future_flag_legacy frontier _ tot flags primes ht]

theorem init_prefix_facts (n next : Int) (flags : List Int) :
    Legacy.EulerInitPrefix n next flags ↔ Zlength flags = n-1 ∧ EulerInitPrefix n next flags := Iff.rfl

theorem outer_state_facts (n next tot : Int) (flags primes : List Int) :
    Legacy.EulerOuterState n next tot flags primes ↔
    Zlength flags = n-1 ∧ Zlength primes = n ∧ (2 ≤ next ∧ next ≤ n+1) ∧
    (0 ≤ tot ∧ tot < next) ∧ EulerOuterState n next tot flags primes := by
  constructor
  · rintro ⟨hf, hl, hn, hnn, ht, htn, hp, _⟩
    have htl : tot ≤ Zlength primes := by omega
    exact ⟨hf.1, hl, ⟨hn, hnn⟩, ⟨ht, htn⟩,
      (flag_state_facts n next tot flags primes ⟨ht, htl⟩).mp hf |>.2,
      (prime_prefix_legacy (next-1) tot primes ⟨ht, htl⟩).mpr hp⟩
  · rintro ⟨hfl, hl, hn, ht, hf, hp⟩
    have htl : tot ≤ Zlength primes := by omega
    have hprefix := (prime_prefix_legacy (next-1) tot primes ⟨ht.1, htl⟩).mp hp
    have hb := Legacy.PrimeBounds_from_prefix__core_invariants _ _ _ hprefix
    exact ⟨(flag_state_facts n next tot flags primes ⟨ht.1, htl⟩).mpr ⟨hfl, hf⟩,
      hl, hn.1, hn.2, ht.1, ht.2, hprefix, by
        intro pos hpos; have hh := hb pos hpos; exact ⟨hh.1, by omega⟩⟩

theorem inner_state_facts (n current j tot : Int) (flags primes : List Int) :
    Legacy.EulerInnerState n current j tot flags primes ↔
    Zlength flags = n-1 ∧ Zlength primes = n ∧ (2 ≤ current ∧ current ≤ n) ∧
    (1 ≤ j ∧ j ≤ tot) ∧ (0 < tot ∧ tot ≤ n) ∧ tot < current+1 ∧
    EulerInnerState n current j tot flags primes := by
  constructor
  · rintro ⟨hf, hl, hc, hcn, hj, hjt, ht, htn, htc, hp, _, hg, hn, he⟩
    have htl : 0 ≤ tot ∧ tot ≤ Zlength primes := by omega
    refine ⟨hf.1, hl, ⟨hc, hcn⟩, ⟨hj, hjt⟩, ⟨ht, htn⟩, htc,
      ((flag_state_facts n current tot flags primes htl).mp hf).2,
      (prime_prefix_legacy current tot primes htl).mpr hp,
      (current_progress_legacy n current j flags primes).mpr hg,
      (prior_nondiv_legacy current j primes (by omega)).mpr hn, ?_⟩
    intro hguard
    exact ((outer_state_facts n (current+1) tot flags primes).mp (he hguard)).2.2.2.2
  · rintro ⟨hfl, hl, hc, hj, ht, htc, hf, hp, hg, hn, he⟩
    have htl : 0 ≤ tot ∧ tot ≤ Zlength primes := by omega
    have hprefix := (prime_prefix_legacy current tot primes htl).mp hp
    refine ⟨(flag_state_facts n current tot flags primes htl).mpr ⟨hfl, hf⟩,
      hl, hc.1, hc.2, hj.1, hj.2, ht.1, ht.2, htc, hprefix,
      Legacy.PrimeBounds_from_prefix__core_invariants _ _ _ hprefix,
      (current_progress_legacy n current j flags primes).mp hg,
      (prior_nondiv_legacy current j primes (by omega)).mp hn, ?_⟩
    intro hguard
    exact (outer_state_facts n (current+1) tot flags primes).mpr
      ⟨hfl, hl, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, he hguard⟩

theorem marked_state_facts (n current j tot : Int) (flags primes : List Int) :
    Legacy.EulerInnerMarkedState n current j tot flags primes ↔
    Zlength flags = n-1 ∧ Zlength primes = n ∧ (2 ≤ current ∧ current ≤ n) ∧
    (1 ≤ j ∧ j ≤ tot) ∧ (0 < tot ∧ tot ≤ n) ∧ tot < current+1 ∧
    ProductIndex current j primes ≤ n ∧
    (¬ Z.divide (Znth (j-1) primes 0) current → j+1 ≤ tot) ∧
    EulerInnerMarkedState n current j tot flags primes := by
  constructor
  · rintro ⟨hi, hprod, he, hv, hg, hd, hn⟩
    rcases (inner_state_facts n current j tot flags primes).mp hi with ⟨hfl, hpl, hc, hj, ht, htc, hi'⟩
    refine ⟨hfl, hpl, hc, hj, ht, htc, hprod, ?_, hi',
      (flag_entry_legacy _ _).mpr he, hv,
      (current_progress_legacy _ _ _ _ _).mpr hg, ?_, ?_⟩
    · intro h; exact ((inner_state_facts _ _ _ _ _ _).mp (hn h)).2.2.2.1.2
    · intro h; exact ((outer_state_facts _ _ _ _ _).mp (hd h)).2.2.2.2
    · intro h; exact ((inner_state_facts _ _ _ _ _ _).mp (hn h)).2.2.2.2.2.2
  · rintro ⟨hfl, hpl, hc, hj, ht, htc, hprod, hnext, hi, he, hv, hg, hd, hn⟩
    refine ⟨(inner_state_facts _ _ _ _ _ _).mpr ⟨hfl, hpl, hc, hj, ht, htc, hi⟩,
      hprod, (flag_entry_legacy _ _).mp he, hv,
      (current_progress_legacy _ _ _ _ _).mp hg, ?_, ?_⟩
    · intro h; exact (outer_state_facts _ _ _ _ _).mpr
        ⟨hfl, hpl, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩, hd h⟩
    · intro h; exact (inner_state_facts _ _ _ _ _ _).mpr
        ⟨hfl, hpl, hc, ⟨by omega, hnext h⟩, ht, htc, hn h⟩

theorem sieve_result_facts (n tot : Int) (flags primes : List Int) :
    Legacy.EulerSieveResult n tot flags primes ↔ Zlength flags = n-1 ∧
    Zlength primes = n ∧ (0 ≤ tot ∧ tot ≤ n) ∧ EulerSieveResult n tot flags primes := by
  constructor
  · rintro ⟨hf, hp, ht, htn, hflags, hprimes⟩
    exact ⟨hf, hp, ⟨ht, htn⟩, ((flag_list_facts _ _).mp hflags).2,
      (prime_prefix_legacy _ _ _ (by omega)).mpr hprimes⟩
  · rintro ⟨hf, hp, ht, hflags, hprimes⟩
    exact ⟨hf, hp, ht.1, ht.2, (flag_list_facts _ _).mpr ⟨hf, hflags⟩,
      (prime_prefix_legacy _ _ _ (by omega)).mp hprimes⟩

theorem init_prefix_math (n next : Int) (flags : List Int)
    (h : Legacy.EulerInitPrefix n next flags) : EulerInitPrefix n next flags := h.2
theorem outer_state_math (n next tot : Int) (flags primes : List Int)
    (h : Legacy.EulerOuterState n next tot flags primes) : EulerOuterState n next tot flags primes :=
  ((outer_state_facts _ _ _ _ _).mp h).2.2.2.2
theorem inner_state_math (n current j tot : Int) (flags primes : List Int)
    (h : Legacy.EulerInnerState n current j tot flags primes) : EulerInnerState n current j tot flags primes :=
  ((inner_state_facts _ _ _ _ _ _).mp h).2.2.2.2.2.2
theorem marked_state_math (n current j tot : Int) (flags primes : List Int)
    (h : Legacy.EulerInnerMarkedState n current j tot flags primes) : EulerInnerMarkedState n current j tot flags primes :=
  ((marked_state_facts _ _ _ _ _ _).mp h).2.2.2.2.2.2.2.2
theorem sieve_result_math (n tot : Int) (flags primes : List Int)
    (h : Legacy.EulerSieveResult n tot flags primes) : EulerSieveResult n tot flags primes :=
  ((sieve_result_facts _ _ _ _).mp h).2.2.2

export Legacy (StrictPrime_two__core_invariants EulerInitPrefix_start__core_invariants EulerInitPrefix_step__core_invariants EulerInitPrefix_finish_outer__core_invariants prime_to_StrictPrime__core_invariants StrictPrime_to_prime__core_invariants StrictPrime_divisor_self_or_all__core_invariants EulerOuterState_nonself_first_prime_facts__core_invariants PrimeBounds_from_prefix__core_invariants PrimePrefixList_extend_nonprime_current__core_invariants EulerOuterState_nonself_current_not_prime__core_invariants least_prime_factor_exists__core_invariants LeastPrimeFactor_lt_of_not_prime__core_invariants LeastPrimeFactor_le_complement__core_invariants PrimePrefixList_lookup__core_invariants FutureSelfCompleteness_successor_prime__core_invariants PrimePrefixList_first_le__core_invariants FutureSelfCompleteness_advance_after_product_exit__core_invariants EulerFlagState_advance_after_product_exit__core_invariants EulerOuterState_advance_after_product_exit__core_invariants EulerOuterState_nonself_inner_start__core_invariants EulerOuterState_self_current_prime__core_invariants PrimePrefixList_append_current__core_invariants EulerFlagState_prime_append_current__core_invariants EulerOuterState_self_inner_start__core_invariants EulerOuterState_self_first_prime_facts__core_invariants StrictPrime_product_not_prime__core_invariants LeastPrimeFactor_current_product__core_invariants FlagEntryFor_current_product__core_invariants EulerFlagState_advance_after_inner_product_exit__core_invariants EulerFlagState_advance_after_inner_divide__core_invariants PriorNonDivisibility_nondivide_next_index__core_invariants EulerInnerState_mark_product__core_invariants)
end SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_lib

namespace SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler
export sieve_of_euler_lib (StrictPrime LeastPrimeFactor FlagEntryFor LeastPrimeFlagList PrimePrefixList PrimeBounds PriorNonDivisibility ProductIndex FlagValue CurrentProductMarked CurrentBaseProgress EarlierLinearProduct FutureSelfCompleteness FutureFlagState EulerFlagState EulerSieveResult EulerInitPrefix EulerOuterState EulerInnerState EulerInnerMarkedState)
end SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler

namespace SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.Modern
export SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.sieve_of_euler_lib (PrimePrefixList)
end SimpleC.EE.LLM_bench.Algorithms.sieve_of_euler.Modern
