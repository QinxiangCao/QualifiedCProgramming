import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
namespace SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes.sieve_of_eratosthenes_lib
open AUXLib

def StrictPrime (p : Int) : Prop :=
  1 < p ∧ ∀ d : Int, 0 < d → Z.divide d p → d = 1 ∨ d = p

def HasProperDivisorBelow (bound k : Int) : Prop :=
  ∃ d : Int, 2 ≤ d ∧ d < bound ∧ d < k ∧ Z.divide d k

def ExactZeroOne (is_zero : Prop) (value : Int) : Prop :=
  (is_zero ∧ value = 0) ∨ (¬ is_zero ∧ value = 1)

def PrimeIndicatorList (n : Int) (values : List Int) : Prop :=
  Zlength values = n ∧ ∀ k : Int, (1 ≤ k ∧ k ≤ n) →
    (StrictPrime k ∧ Znth (k-1) values 0 = 1) ∨ (¬ StrictPrime k ∧ Znth (k-1) values 0 = 0)

def SieveInitPrefix (n next : Int) (values : List Int) : Prop :=
  Zlength values = n ∧ ∀ k : Int, (1 ≤ k ∧ k < next) → Znth (k-1) values 0 = 1

def SieveStage (n bound : Int) (values : List Int) : Prop :=
  Zlength values = n ∧ ∀ k : Int, (1 ≤ k ∧ k ≤ n) →
    (k = 1 ∧ Znth (k-1) values 0 = 0) ∨
    (2 ≤ k ∧ ExactZeroOne (HasProperDivisorBelow bound k) (Znth (k-1) values 0))

def ProcessedMultiple (factor next k : Int) : Prop :=
  2*factor ≤ k ∧ k < next ∧ Z.divide factor k

def SieveMarkState (n factor next : Int) (values : List Int) : Prop :=
  2 ≤ factor ∧ 2*factor ≤ next ∧ Z.divide factor next ∧ Zlength values = n ∧
  ∀ k : Int, (1 ≤ k ∧ k ≤ n) → (k = 1 ∧ Znth (k-1) values 0 = 0) ∨
    (2 ≤ k ∧ ExactZeroOne (HasProperDivisorBelow factor k ∨ ProcessedMultiple factor next k)
      (Znth (k-1) values 0))

theorem StrictPrime_iff_no_proper_divisor (p : Int) (hp : 1 < p) :
    StrictPrime p ↔ ¬ HasProperDivisorBelow p p := by
  constructor
  · rintro ⟨_, hprime⟩ ⟨d, hd, _, hdp, hdiv⟩
    have := hprime d (by omega) hdiv
    omega
  · intro hn
    refine ⟨hp, ?_⟩
    intro d hd hdiv
    by_cases hd1 : d = 1
    · exact Or.inl hd1
    · apply Or.inr
      have hdp : d ≤ p := Int.le_of_dvd (by omega) (by
        rcases hdiv with ⟨q, hq⟩
        exact ⟨q, by rw [hq, Int.mul_comm]⟩)
      apply Classical.byContradiction
      intro hne
      exact hn ⟨d, by omega, by omega, by omega, hdiv⟩

theorem StrictPrime_iff_no_divisor_below (bound k : Int) (hk : 1 < k) (hb : k < bound) :
    StrictPrime k ↔ ¬ HasProperDivisorBelow bound k := by
  constructor
  · rintro ⟨_, hp⟩ ⟨d, hd, _, hdk, hdiv⟩
    have := hp d (by omega) hdiv
    omega
  · intro hn
    apply (StrictPrime_iff_no_proper_divisor k hk).mpr
    rintro ⟨d, hd, hdb, hdk, hdiv⟩
    exact hn ⟨d, hd, by omega, hdk, hdiv⟩

theorem SieveStage_implies_PrimeIndicatorList (n bound : Int) (values : List Int)
    (hb : n < bound) (hs : SieveStage n bound values) : PrimeIndicatorList n values := by
  refine ⟨hs.1, ?_⟩
  intro k hk
  rcases hs.2 k hk with ⟨heq, hv⟩ | ⟨hk2, hv⟩
  · subst k
    exact Or.inr ⟨by rintro ⟨h, _⟩; omega, hv⟩
  · have hp := StrictPrime_iff_no_divisor_below bound k (by omega) (by omega)
    rcases hv with ⟨hbad, hz⟩ | ⟨hgood, hone⟩
    · exact Or.inr ⟨fun h => hp.mp h hbad, hz⟩
    · exact Or.inl ⟨hp.mpr hgood, hone⟩

theorem SieveInitPrefix_start__sieve_invariants (n : Int) (values : List Int)
    (hlen : Zlength values = n) : SieveInitPrefix n 1 values := by
  exact ⟨hlen, by intro k hk; omega⟩

theorem SieveInitPrefix_step__sieve_invariants (n next : Int) (values : List Int)
    (hn : 1 ≤ next) (hnn : next ≤ n) (hs : SieveInitPrefix n next values) :
    SieveInitPrefix n (next+1) (replace_Znth (next-1) 1 values) := by
  rcases hs with ⟨hlen, hp⟩
  refine ⟨by rw [Zlength_replace_Znth]; exact hlen, ?_⟩
  intro k hk
  by_cases heq : k = next
  · subst k; exact Znth_replace_Znth_Same 0 values (next-1) 1 (by omega)
  · rw [Znth_replace_Znth_Diff 0 values (next-1) (k-1) 1 (by omega) (by omega) (by omega)]
    exact hp k (by omega)

theorem SieveInitPrefix_finish__sieve_invariants (n next : Int) (values : List Int)
    (hn : 2 ≤ n) (hnl : n < next) (hnu : next ≤ n+1) (hs : SieveInitPrefix n next values) :
    SieveStage n 2 (replace_Znth (2-1) 1 (replace_Znth (1-1) 0 values)) := by
  rcases hs with ⟨hlen, hp⟩
  have hz : Zlength (replace_Znth (1-1) 0 values) = n := by rw [Zlength_replace_Znth]; exact hlen
  refine ⟨by rw [Zlength_replace_Znth]; exact hz, ?_⟩
  intro k hk
  by_cases heq : k = 1
  · subst k
    refine Or.inl ⟨rfl, ?_⟩
    rw [Znth_replace_Znth_Diff 0 _ (2-1) (1-1) 1 (by omega) (by omega) (by omega)]
    exact Znth_replace_Znth_Same 0 values (1-1) 0 (by omega)
  · refine Or.inr ⟨by omega, Or.inr ⟨?_, ?_⟩⟩
    · rintro ⟨d, hd, hdb, _⟩; omega
    · by_cases hk2 : k = 2
      · subst k
        exact Znth_replace_Znth_Same 0 _ (2-1) 1 (by omega)
      · rw [Znth_replace_Znth_Diff 0 _ (2-1) (k-1) 1 (by omega) (by omega) (by omega),
          Znth_replace_Znth_Diff 0 values (1-1) (k-1) 0 (by omega) (by omega) (by omega)]
        exact hp k (by omega)

theorem SieveStage_mark_start__sieve_invariants (n factor : Int) (values : List Int)
    (hf : 2 ≤ factor) (hfn : factor ≤ n) (hs : SieveStage n factor values) :
    SieveMarkState n factor (factor*2) values := by
  refine ⟨hf, by omega, ⟨2, by omega⟩, hs.1, ?_⟩
  intro k hk
  rcases hs.2 k hk with h1 | ⟨hk2, hv⟩
  · exact Or.inl h1
  · refine Or.inr ⟨hk2, ?_⟩
    rcases hv with ⟨hb, hz⟩ | ⟨hg, ho⟩
    · exact Or.inl ⟨Or.inl hb, hz⟩
    · refine Or.inr ⟨?_, ho⟩
      rintro (hb | ⟨hl, hu, _⟩)
      · exact hg hb
      · omega

theorem ProcessedMultiple_step_except_current__sieve_invariants (factor next k : Int)
    (hf : 0 < factor) (hd : Z.divide factor next) (hne : k ≠ next) :
    ProcessedMultiple factor (next+factor) k ↔ ProcessedMultiple factor next k := by
  constructor
  · rintro ⟨hl, hu, hkdiv⟩
    refine ⟨hl, ?_, hkdiv⟩
    rcases hd with ⟨a, ha⟩
    rcases hkdiv with ⟨b, hb⟩
    apply Classical.byContradiction
    intro hnot
    have hab : a < b := (Int.mul_lt_mul_right hf).mp (by omega)
    have hm := Int.mul_le_mul_of_nonneg_right (show a+1 ≤ b by omega) (Int.le_of_lt hf)
    rw [Int.add_mul] at hm
    omega
  · rintro ⟨hl, hu, hd⟩
    exact ⟨hl, by omega, hd⟩

theorem SieveMarkState_step__sieve_invariants (n factor next : Int) (values : List Int)
    (hn : next ≤ n) (hs : SieveMarkState n factor next values) :
    SieveMarkState n factor (next+factor) (replace_Znth (next-1) 0 values) := by
  rcases hs with ⟨hf, hstart, hd, hlen, hm⟩
  refine ⟨hf, by omega, ?_, by rw [Zlength_replace_Znth]; exact hlen, ?_⟩
  · rcases hd with ⟨q, hq⟩
    refine ⟨q+1, ?_⟩
    rw [Int.add_mul]; omega
  · intro k hk
    rcases hm k hk with ⟨hk1, hv⟩ | ⟨hk2, hv⟩
    · apply Or.inl
      refine ⟨hk1, ?_⟩
      rw [Znth_replace_Znth_Diff 0 values (next-1) (k-1) 0 (by omega) (by omega) (by omega)]
      exact hv
    · refine Or.inr ⟨hk2, ?_⟩
      by_cases heq : k = next
      · subst k
        exact Or.inl ⟨Or.inr ⟨hstart, by omega, hd⟩, Znth_replace_Znth_Same 0 values (next-1) 0 (by omega)⟩
      · rw [Znth_replace_Znth_Diff 0 values (next-1) (k-1) 0 (by omega) (by omega) (by omega)]
        have ht := ProcessedMultiple_step_except_current__sieve_invariants factor next k (by omega) hd heq
        rcases hv with ⟨ho, hz⟩ | ⟨hno, hone⟩
        · exact Or.inl ⟨ho.imp id ht.mpr, hz⟩
        · exact Or.inr ⟨fun h => hno (h.imp id ht.mp), hone⟩

theorem HasProperDivisorBelow_succ_at_mark_exit__sieve_invariants (factor next k : Int)
    (hf : 2 ≤ factor) (hkn : k < next) :
    HasProperDivisorBelow (factor+1) k ↔ HasProperDivisorBelow factor k ∨ ProcessedMultiple factor next k := by
  constructor
  · rintro ⟨d, hd, hdb, hdk, hdiv⟩
    by_cases hlt : d < factor
    · exact Or.inl ⟨d, hd, hlt, hdk, hdiv⟩
    · have heq : d = factor := by omega
      subst d
      refine Or.inr ⟨?_, hkn, hdiv⟩
      rcases hdiv with ⟨q, hq⟩
      have hq2 : 1 < q := (Int.mul_lt_mul_right (show 0 < factor by omega)).mp (by omega)
      have hm := Int.mul_le_mul_of_nonneg_right (show 2 ≤ q by omega) (show 0 ≤ factor by omega)
      omega
  · rintro (⟨d, hd, hdb, hdk, hdiv⟩ | ⟨hl, hu, hdiv⟩)
    · exact ⟨d, hd, by omega, hdk, hdiv⟩
    · exact ⟨factor, hf, by omega, by omega, hdiv⟩

theorem SieveMarkState_finish__sieve_invariants (n factor next : Int) (values : List Int)
    (hn : n < next) (hs : SieveMarkState n factor next values) : SieveStage n (factor+1) values := by
  rcases hs with ⟨hf, hstart, hd, hlen, hm⟩
  refine ⟨hlen, ?_⟩
  intro k hk
  rcases hm k hk with h1 | ⟨hk2, hv⟩
  · exact Or.inl h1
  · refine Or.inr ⟨hk2, ?_⟩
    have ht := HasProperDivisorBelow_succ_at_mark_exit__sieve_invariants factor next k hf (by omega)
    rcases hv with ⟨ho, hz⟩ | ⟨hno, hone⟩
    · exact Or.inl ⟨ht.mpr ho, hz⟩
    · exact Or.inr ⟨fun h => hno (ht.mp h), hone⟩

theorem HasProperDivisorBelow_succ_absorbed__sieve_invariants (factor k : Int)
    (hf : HasProperDivisorBelow factor factor) :
    HasProperDivisorBelow (factor+1) k ↔ HasProperDivisorBelow factor k := by
  rcases hf with ⟨small, hs2, hsf, _, hsdiv⟩
  constructor
  · rintro ⟨d, hd, hdb, hdk, hdiv⟩
    by_cases hlt : d < factor
    · exact ⟨d, hd, hlt, hdk, hdiv⟩
    · have heq : d = factor := by omega
      subst d
      refine ⟨small, hs2, hsf, by omega, ?_⟩
      rcases hsdiv with ⟨q, hq⟩
      rcases hdiv with ⟨r, hr⟩
      exact ⟨q*r, by rw [hr, hq]; simp [Int.mul_comm, Int.mul_left_comm, Int.mul_assoc]⟩
  · rintro ⟨d, hd, hdb, hdk, hdiv⟩
    exact ⟨d, hd, by omega, hdk, hdiv⟩

theorem SieveStage_skip_composite__sieve_invariants (n factor : Int) (values : List Int)
    (hf : 2 ≤ factor) (hfn : factor ≤ n) (hv : Znth (factor-1) values 0 ≠ 1)
    (hs : SieveStage n factor values) : SieveStage n (factor+1) values := by
  have hbad : HasProperDivisorBelow factor factor := by
    rcases hs.2 factor (by omega) with ⟨h1, _⟩ | ⟨_, ⟨hb, _⟩ | ⟨_, h1⟩⟩
    · omega
    · exact hb
    · exact False.elim (hv h1)
  refine ⟨hs.1, ?_⟩
  intro k hk
  rcases hs.2 k hk with h1 | ⟨hk2, hv⟩
  · exact Or.inl h1
  · refine Or.inr ⟨hk2, ?_⟩
    have ht := HasProperDivisorBelow_succ_absorbed__sieve_invariants factor k hbad
    rcases hv with ⟨ho, hz⟩ | ⟨hno, hone⟩
    · exact Or.inl ⟨ht.mpr ho, hz⟩
    · exact Or.inr ⟨fun h => hno (ht.mp h), hone⟩

end SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes.sieve_of_eratosthenes_lib
namespace SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes
export sieve_of_eratosthenes_lib (StrictPrime HasProperDivisorBelow ExactZeroOne PrimeIndicatorList
  SieveInitPrefix SieveStage ProcessedMultiple SieveMarkState)
end SimpleC.EE.LLM_bench.Algorithms.sieve_of_eratosthenes
