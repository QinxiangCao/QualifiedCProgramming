import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_sieve_count
import AUXLib.Arithmetic
import SimpleC.SL.SeparationLogic
import AUXLib.ListLib.LengthCompat
import AUXLib.ListLib.Arithmetic
import MaxMinLib.Interface
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum.Prime
import AUXLib.Prime
import AUXLib.ListLib.Interval

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_lib
open AUXLib


open AUXLib.Prime

def Pre (a : List Int) : Prop :=
  (2 ≤ Zlength a ∧ Zlength a ≤ 100000) ∧ Forall (fun x => 1 ≤ x ∧ x ≤ 1000000000) a

def Spec (a : List Int) (out : Int) : Prop :=
  (out = 0 ∨ out = 1) ∧ (out = 1 ↔ ∃ i j x, (0 ≤ i ∧ i < Zlength a) ∧ (0 ≤ j ∧ j < Zlength a) ∧
    i ≠ j ∧ x ≥ 2 ∧ x ∣ Znth i a 0 ∧ x ∣ Znth j a 0)

def MarkedBefore (bound value : Int) : Prop := ∃ d, (2 ≤ d ∧ d < bound) ∧ d ∣ value

def PrimePrefixTable (bound : Int) (primes flags : List Int) : Prop :=
  (2 ≤ bound ∧ bound ≤ 31624) ∧ Zlength flags = 31624 ∧ primes.Nodup ∧ Forall prime primes ∧ increasing primes ∧
  (∀ p, p ∈ primes ↔ (2 ≤ p ∧ p < bound) ∧ prime p) ∧
  (∀ k, (2 ≤ k ∧ k ≤ 31623) → (Znth k flags 0 = 0 ↔ ¬ MarkedBefore bound k))

def PrimeMarkTable (factor next : Int) (primes flags : List Int) : Prop :=
  (2 ≤ factor ∧ factor ≤ 31623) ∧ factor * factor ≤ next ∧ Zlength flags = 31624 ∧
  primes.Nodup ∧ Forall prime primes ∧ increasing primes ∧
  (∀ p, p ∈ primes ↔ (2 ≤ p ∧ p < factor + 1) ∧ prime p) ∧
  (∀ k, (2 ≤ k ∧ k ≤ 31623) → (Znth k flags 0 = 0 ↔ ¬ (MarkedBefore factor k ∨ factor ∣ k ∧ (factor * factor ≤ k ∧ k < next))))

def CompletePrimeTable (primes : List Int) : Prop :=
  primes.Nodup ∧ Forall prime primes ∧ increasing primes ∧ (∀ p, p ∈ primes ↔ (2 ≤ p ∧ p ≤ 31623) ∧ prime p)

def zdividesb (p x : Int) : Bool := decide (p ∣ x)

def PrimeFactorBagPrefix (a : List Int) (upto : Int) (factors : List Int) : Prop :=
  (0 ≤ upto ∧ upto ≤ Zlength a) ∧ Forall prime factors ∧ ∀ p, prime p →
    (factors.count p : Int) = (((a.take upto.toNat).filter (zdividesb p)).length : Int)

def FactorScanState (a primes : List Int) (index tested rem : Int) (factors : List Int) : Prop :=
  ∃ done picked, factors = done ++ picked ∧ PrimeFactorBagPrefix a index done ∧
    (0 ≤ index ∧ index < Zlength a) ∧ (0 ≤ tested ∧ tested ≤ Zlength primes) ∧
    (1 ≤ rem ∧ rem ≤ Znth index a 1) ∧ rem ∣ Znth index a 1 ∧ picked.Nodup ∧ Forall prime picked ∧
    (∀ p, prime p → (p ∈ picked ↔ p ∈ primes.take tested.toNat ∧ p ∣ Znth index a 1)) ∧
    (∀ p, p ∈ primes.take tested.toNat → ¬ p ∣ rem)

def FactorDivideState (a primes : List Int) (index tested rem : Int) (factors : List Int) : Prop :=
  ∃ done picked p, factors = done ++ picked ++ [p] ∧ PrimeFactorBagPrefix a index done ∧
    (0 ≤ index ∧ index < Zlength a) ∧ (0 ≤ tested ∧ tested < Zlength primes) ∧
    p = Znth tested primes 0 ∧ prime p ∧ p ∣ Znth index a 1 ∧
    (1 ≤ rem ∧ rem ≤ Znth index a 1) ∧ rem ∣ Znth index a 1 ∧ picked.Nodup ∧ Forall prime picked ∧
    (∀ q, prime q → (q ∈ picked ↔ q ∈ primes.take tested.toNat ∧ q ∣ Znth index a 1)) ∧
    (∀ q, q ∈ primes.take tested.toNat → ¬ q ∣ rem)

def DuplicatePrefixState (factors : List Int) (upto found : Int) : Prop :=
  (0 ≤ upto ∧ upto ≤ Zlength factors) ∧ (found = 0 ∨ found = 1) ∧
    (found = 1 ↔ ∃ i j, (0 ≤ i ∧ i < j) ∧ j < upto ∧ Znth i factors 0 = Znth j factors 0)

def ProperMarkedBefore (bound value : Int) : Prop := ∃ d, (2 ≤ d ∧ d < bound) ∧ d < value ∧ d ∣ value

def PrimePrefixTable2 (bound : Int) (primes flags : List Int) : Prop :=
  (2 ≤ bound ∧ bound ≤ 31624) ∧ Zlength flags = 31624 ∧ primes.Nodup ∧ Forall prime primes ∧ increasing primes ∧
  (∀ p, p ∈ primes ↔ (2 ≤ p ∧ p < bound) ∧ prime p) ∧
  (∀ k, (2 ≤ k ∧ k ≤ 31623) → (Znth k flags 0 = 0 ↔ ¬ ProperMarkedBefore bound k))

def PrimeMarkTable2 (factor next : Int) (primes flags : List Int) : Prop :=
  (2 ≤ factor ∧ factor ≤ 31623) ∧ factor * factor ≤ next ∧ factor ∣ next ∧ Zlength flags = 31624 ∧
  primes.Nodup ∧ Forall prime primes ∧ increasing primes ∧
  (∀ p, p ∈ primes ↔ (2 ≤ p ∧ p < factor + 1) ∧ prime p) ∧
  (∀ k, (2 ≤ k ∧ k ≤ 31623) → (Znth k flags 0 = 0 ↔ ¬ (ProperMarkedBefore factor k ∨ factor ∣ k ∧ (factor * factor ≤ k ∧ k < next))))

def FactorAppendCapacity (primes : List Int) (index tested rem count : Int) : Prop :=
  ((0 ≤ tested ∧ tested < Zlength primes) ∧ Znth tested primes 0 ∣ rem) → count + 1 ≤ index * 10 + 9

def DuplicateScanLoopState (factors : List Int) (count cursor found : Int) : Prop :=
  (count = 0 ∧ cursor = 1 ∧ DuplicatePrefixState factors 0 found) ∨
  (1 ≤ count ∧ (1 ≤ cursor ∧ cursor ≤ count) ∧ DuplicatePrefixState factors cursor found)

def ResidualPrimeCoverage (original rem : Int) (picked : List Int) : Prop :=
  ∀ p, prime p → (p ∣ original ↔ p ∈ picked ∨ p ∣ rem)

def FactorScanState2 (a primes : List Int) (index tested rem : Int) (factors : List Int) : Prop :=
  ∃ done picked, factors = done ++ picked ∧ PrimeFactorBagPrefix a index done ∧
    (0 ≤ index ∧ index < Zlength a) ∧ (0 ≤ tested ∧ tested ≤ Zlength primes) ∧
    (1 ≤ rem ∧ rem ≤ Znth index a 1) ∧ rem ∣ Znth index a 1 ∧ picked.Nodup ∧ Forall prime picked ∧
    (∀ p, prime p → (p ∈ picked ↔ p ∈ primes.take tested.toNat ∧ p ∣ Znth index a 1)) ∧
    (∀ p, p ∈ primes.take tested.toNat → ¬ p ∣ rem) ∧
    ResidualPrimeCoverage (Znth index a 1) rem picked

def FactorDivideState2 (a primes : List Int) (index tested rem : Int) (factors : List Int) : Prop :=
  ∃ done picked p, factors = done ++ picked ++ [p] ∧ PrimeFactorBagPrefix a index done ∧
    (0 ≤ index ∧ index < Zlength a) ∧ (0 ≤ tested ∧ tested < Zlength primes) ∧
    p = Znth tested primes 0 ∧ prime p ∧ p ∣ Znth index a 1 ∧
    (1 ≤ rem ∧ rem ≤ Znth index a 1) ∧ rem ∣ Znth index a 1 ∧ picked.Nodup ∧ Forall prime picked ∧
    (∀ q, prime q → (q ∈ picked ↔ q ∈ primes.take tested.toNat ∧ q ∣ Znth index a 1)) ∧
    (∀ q, q ∈ primes.take tested.toNat → ¬ q ∣ rem) ∧
    ResidualPrimeCoverage (Znth index a 1) rem (picked ++ [p])

theorem FactorScanState2_implies_FactorScanState (a primes : List Int) (index tested rem : Int) (factors : List Int)
    (h : FactorScanState2 a primes index tested rem factors) : FactorScanState a primes index tested rem factors := by
  rcases h with ⟨done,picked,hf,hbag,hi,ht,hr,hd,hn,hp,hpicked,he,_⟩
  exact ⟨done,picked,hf,hbag,hi,ht,hr,hd,hn,hp,hpicked,he⟩

theorem FactorDivideState2_implies_FactorDivideState (a primes : List Int) (index tested rem : Int) (factors : List Int)
    (h : FactorDivideState2 a primes index tested rem factors) : FactorDivideState a primes index tested rem factors := by
  rcases h with ⟨done,picked,p,hf,hbag,hi,ht,heq,hprime,hpd,hr,hd,hn,hp,hpicked,he,_⟩
  exact ⟨done,picked,p,hf,hbag,hi,ht,heq,hprime,hpd,hr,hd,hn,hp,hpicked,he⟩

theorem complete_prime_table_index_bounds__safety_prime_bounds (primes : List Int) (j : Int)
    (ht : CompletePrimeTable primes) (hj : 0≤j ∧ j<Zlength primes) :
    prime (Znth j primes 0) ∧ 2≤Znth j primes 0 ∧ Znth j primes 0≤31623 := by
  have h := ht.2.2.2 (Znth j primes 0) |>.mp (by
    have hjn : j.toNat<primes.length := by simp only [Zlength,Int.ofNat_eq_coe] at hj; omega
    simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hjn,Option.getD_some]
    exact List.getElem_mem hjn)
  exact ⟨h.2,h.1⟩

theorem factor_divide_state_current_prime__safety_prime_bounds (a primes : List Int) (index tested rem : Int) (factors : List Int)
    (h : FactorDivideState2 a primes index tested rem factors) : prime (Znth tested primes 0) ∧ Znth tested primes 0≠0 := by
  rcases h with ⟨done,picked,p,hf,hbag,hi,ht,heq,hprime,_⟩
  rw [heq] at hprime
  exact ⟨hprime,by have := prime_ge_2 _ hprime; omega⟩

theorem bounded_prime_square_int64__safety_prime_bounds (p : Int) (hp : 2≤p ∧ p≤31623) :
    0≤p*p ∧ p*p≤2000000000 := by constructor <;> nlinarith

theorem increasing_aux_snoc__sieve_construction (l : List Int) (x y : Int)
    (hi : increasing_aux l x) (hall : ∀z, z∈l → z≤y) (hxy : x≤y) : increasing_aux (l++[y]) x := by
  induction l generalizing x with
  | nil => exact ⟨hxy,True.intro⟩
  | cons a l ih => exact ⟨hi.1,ih a hi.2 (fun z hz=>hall z (List.mem_cons_of_mem a hz)) (hall a (by simp))⟩

theorem increasing_snoc__sieve_construction (l : List Int) (y : Int)
    (hi : increasing l) (hall : ∀x, x∈l → x≤y) : increasing (l++[y]) := by
  cases l with
  | nil => trivial
  | cons a l => exact increasing_aux_snoc__sieve_construction l a y hi (fun z hz=>hall z (List.mem_cons_of_mem a hz)) (hall a (by simp))

theorem proper_marked_before_advance_large__sieve_construction (i k : Int)
    (hi : 2≤i) (hsq : i*i>31623) (hk : 2≤k ∧ k≤31623) :
    ProperMarkedBefore (i+1) k ↔ ProperMarkedBefore i k := by
  constructor
  · rintro ⟨d,hd,hdk,hdiv⟩
    by_cases hdi : d<i
    · exact ⟨d,⟨hd.1,hdi⟩,hdk,hdiv⟩
    · have he : d=i := by omega
      subst d
      rcases hdiv with ⟨q,hq⟩
      have hq2 : 2≤q := by nlinarith
      have hqi : q<i := by nlinarith
      have hqk : q<k := by nlinarith
      exact ⟨q,⟨hq2,hqi⟩,hqk,⟨i,by nlinarith⟩⟩
  · rintro ⟨d,hd,hdk,hdiv⟩; exact ⟨d,by omega,hdk,hdiv⟩

theorem proper_marked_before_advance_marked__sieve_construction (i k : Int)
    (hm : ProperMarkedBefore i i) : ProperMarkedBefore (i+1) k ↔ ProperMarkedBefore i k := by
  constructor
  · rintro ⟨d,hd,hdk,hdiv⟩
    by_cases hdi : d<i
    · exact ⟨d,⟨hd.1,hdi⟩,hdk,hdiv⟩
    · have he : d=i := by omega
      subst d
      rcases hm with ⟨e,he,hei,hed⟩
      exact ⟨e,he,by omega,dvd_trans hed hdiv⟩
  · rintro ⟨d,hd,hdk,hdiv⟩; exact ⟨d,by omega,hdk,hdiv⟩

theorem prime_prefix_table2_unmarked_prime__sieve_construction (bound : Int) (primes flags : List Int)
    (ht : PrimePrefixTable2 bound primes flags) (hb : 2≤bound ∧ bound≤31623) (hz : Znth bound flags 0=0) : prime bound := by
  apply (prime_alt bound).mp
  refine ⟨by omega,?_⟩
  intro d hd hdiv
  exact (ht.2.2.2.2.2.2 bound hb).mp hz ⟨d,by omega,hd.2,(Z.divide_iff_dvd _ _).mp hdiv⟩

private theorem prime_snoc_table (bound : Int) (primes : List Int)
    (hn : primes.Nodup) (hf : Forall prime primes) (hinc : increasing primes)
    (hc : ∀p, p∈primes ↔ (2≤p ∧ p<bound) ∧ prime p) (hp : prime bound) :
    (primes++[bound]).Nodup ∧ Forall prime (primes++[bound]) ∧ increasing (primes++[bound]) ∧
    ∀p, p∈primes++[bound] ↔ (2≤p ∧ p<bound+1) ∧ prime p := by
  have hb := prime_ge_2 bound hp
  refine ⟨?_,?_,?_,?_⟩
  · apply List.nodup_append.mpr
    refine ⟨hn,by simp,?_⟩
    intro x hx y hy heq
    have hyb : y=bound := by simpa using hy
    have he : x=bound := heq.trans hyb
    have := (hc x).mp hx
    omega
  · apply Forall.iff_forall_mem.mpr
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hf.mem hx
    · have he : x=bound := by simpa using hx
      exact he.symm ▸ hp
  · exact increasing_snoc__sieve_construction primes bound hinc (fun x hx=>by have := (hc x).mp hx; omega)
  · intro p
    simp only [List.mem_append,List.mem_singleton,hc]
    constructor
    · rintro (⟨hr,hp⟩ | he)
      · exact ⟨by omega,hp⟩
      · subst p; exact ⟨by omega,hp⟩
    · rintro ⟨hr,hp⟩
      by_cases hl : p<bound
      · exact Or.inl ⟨⟨hr.1,hl⟩,hp⟩
      · exact Or.inr (by omega)

theorem prime_prefix_table2_begin_mark__sieve_construction (factor : Int) (primes flags : List Int)
    (ht : PrimePrefixTable2 factor primes flags) (hb : 2≤factor ∧ factor≤31623)
    (hz : Znth factor flags 0=0) (hsq : factor*factor≤31623) :
    PrimeMarkTable2 factor (factor*factor) (primes++[factor]) flags := by
  have hp := prime_prefix_table2_unmarked_prime__sieve_construction factor primes flags ht hb hz
  rcases ht with ⟨hbound,hlen,hn,hf,hi,hc,hflags⟩
  rcases prime_snoc_table factor primes hn hf hi hc hp with ⟨hn',hf',hi',hc'⟩
  refine ⟨hb,le_refl _,dvd_mul_right factor factor,hlen,hn',hf',hi',hc',?_⟩
  intro k hk
  rw [hflags k hk]
  constructor
  · rintro hm (hproper | ⟨_,hr⟩)
    · exact hm hproper
    · omega
  · intro hm hproper; exact hm (Or.inl hproper)

theorem prime_prefix_table2_advance_unmarked__sieve_construction (factor : Int) (primes flags : List Int)
    (ht : PrimePrefixTable2 factor primes flags) (hb : 2≤factor ∧ factor≤31623)
    (hz : Znth factor flags 0=0) (hsq : factor*factor>31623) :
    PrimePrefixTable2 (factor+1) (primes++[factor]) flags := by
  have hp := prime_prefix_table2_unmarked_prime__sieve_construction factor primes flags ht hb hz
  rcases ht with ⟨hbound,hlen,hn,hf,hi,hc,hflags⟩
  rcases prime_snoc_table factor primes hn hf hi hc hp with ⟨hn',hf',hi',hc'⟩
  refine ⟨by omega,hlen,hn',hf',hi',hc',?_⟩
  intro k hk
  rw [hflags k hk,proper_marked_before_advance_large__sieve_construction factor k hb.1 hsq hk]

theorem prime_prefix_table2_advance_marked__sieve_construction (factor : Int) (primes flags : List Int)
    (ht : PrimePrefixTable2 factor primes flags) (hb : 2≤factor ∧ factor≤31623)
    (hz : Znth factor flags 0≠0) : PrimePrefixTable2 (factor+1) primes flags := by
  classical
  rcases ht with ⟨hbound,hlen,hn,hf,hi,hc,hflags⟩
  have hm : ProperMarkedBefore factor factor := by
    by_contra hnm
    exact hz ((hflags factor hb).mpr hnm)
  refine ⟨by omega,hlen,hn,hf,hi,?_,?_⟩
  · intro p
    rw [hc p]
    constructor
    · rintro ⟨hr,hp⟩; exact ⟨by omega,hp⟩
    · rintro ⟨hr,hp⟩
      have hne : p≠factor := by
        intro he
        subst p
        rcases hm with ⟨d,hd,hdf,hdiv⟩
        have hd' := prime_divisors factor hp d ((Z.divide_iff_dvd _ _).mpr hdiv)
        omega
      exact ⟨by omega,hp⟩
  · intro k hk
    rw [hflags k hk,proper_marked_before_advance_marked__sieve_construction factor k hm]

theorem prime_prefix_table2_complete__sieve_marking_exits (primes flags : List Int)
    (ht : PrimePrefixTable2 31624 primes flags) : CompletePrimeTable primes := by
  rcases ht with ⟨hb,hl,hn,hf,hi,hc,hflags⟩
  refine ⟨hn,hf,hi,?_⟩
  intro p
  rw [hc p]
  constructor <;> rintro ⟨hr,hp⟩ <;> exact ⟨by omega,hp⟩

theorem prime_factor_bag_prefix_zero__sieve_marking_exits (a : List Int) : PrimeFactorBagPrefix a 0 [] := by
  exact ⟨⟨by omega,Zlength_nonneg a⟩,Forall.nil,by intro p hp; rfl⟩

private theorem prime_nat_iff (p : Int) (hp0 : 0≤p) : prime p ↔ p.toNat.Prime := by
  have he : (p.toNat:Int)=p := by omega
  rw [←prime_alt,Nat.prime_def_lt']
  constructor
  · rintro ⟨hp,hd⟩
    refine ⟨by omega,?_⟩
    intro m hm hml hdiv
    have hdi : (m:Int)∣p := by
      rw [←he]
      exact Int.natCast_dvd_natCast.mpr hdiv
    exact hd (m:Int) (by omega) ((Z.divide_iff_dvd _ _).mpr hdi)
  · rintro ⟨hp,hd⟩
    refine ⟨by omega,?_⟩
    intro m hm hdiv
    have hme : (m.toNat:Int)=m := by omega
    have hdi := (Z.divide_iff_dvd _ _).mp hdiv
    rw [←he,←hme] at hdi
    exact hd m.toNat (by omega) (by omega) (Int.natCast_dvd_natCast.mp hdi)

theorem NoDup_firstn__factor_scan_advance (A : Type) (n : Nat) (l : List A) (hn : l.Nodup) :
    (l.take n).Nodup := hn.take

theorem firstn_Z_succ__factor_scan_advance (A : Type) (l : List A) (j : Int) (d : A)
    (hj : 0≤j ∧ j<Zlength l) : l.take (j+1).toNat=l.take j.toNat++[Znth j l d] := by
  have hn : j.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hj; omega
  have hs : (j+1).toNat=j.toNat+1 := by omega
  rw [hs,List.take_succ_eq_append_getElem hn]
  congr 2
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]

theorem NoDup_snoc_notin__factor_scan_advance (A : Type) (l : List A) (x : A)
    (hn : (l++[x]).Nodup) : x∉l := by
  intro hx
  exact (List.nodup_append.mp hn).2.2 x hx x (by simp) rfl

theorem prime_floor_29__factor_scan_advance (p : Int) (hp : prime p) (hb : 24≤p) : 29≤p := by
  have hn := (prime_nat_iff p (by omega)).mp hp
  by_contra h
  interval_cases p <;> (revert hn; decide)

theorem prime_floor_5__factor_scan_advance (p : Int) (hp : prime p) (hb : 4≤p) : 5≤p := by
  have hn := (prime_nat_iff p (by omega)).mp hp
  by_contra h
  interval_cases p <;> (revert hn; decide)

theorem prime_floor_7__factor_scan_advance (p : Int) (hp : prime p) (hb : 6≤p) : 7≤p := by
  have hn := (prime_nat_iff p (by omega)).mp hp
  by_contra h
  interval_cases p <;> (revert hn; decide)

theorem prime_floor_11__factor_scan_advance (p : Int) (hp : prime p) (hb : 8≤p) : 11≤p := by
  have hn := (prime_nat_iff p (by omega)).mp hp
  by_contra h
  interval_cases p <;> (revert hn; decide)

theorem prime_floor_13__factor_scan_advance (p : Int) (hp : prime p) (hb : 12≤p) : 13≤p := by
  have hn := (prime_nat_iff p (by omega)).mp hp
  by_contra h
  interval_cases p <;> (revert hn; decide)

theorem prime_floor_17__factor_scan_advance (p : Int) (hp : prime p) (hb : 14≤p) : 17≤p := by
  have hn := (prime_nat_iff p (by omega)).mp hp
  by_contra h
  interval_cases p <;> (revert hn; decide)

theorem prime_floor_19__factor_scan_advance (p : Int) (hp : prime p) (hb : 18≤p) : 19≤p := by
  have hn := (prime_nat_iff p (by omega)).mp hp
  by_contra h
  interval_cases p <;> (revert hn; decide)

theorem prime_floor_23__factor_scan_advance (p : Int) (hp : prime p) (hb : 20≤p) : 23≤p := by
  have hn := (prime_nat_iff p (by omega)).mp hp
  by_contra h
  interval_cases p <;> (revert hn; decide)

theorem prime_not_divide_distinct_prime__factor_scan_advance (p q : Int) (hp : prime p) (hq : prime q)
    (hne : p≠q) : ¬p∣q := by
  intro hd
  have hd' := prime_divisors q hq p ((Z.divide_iff_dvd _ _).mpr hd)
  have := prime_ge_2 p hp
  have := prime_ge_2 q hq
  omega

theorem zdividesb_true_iff__factor_scan_advance (p x : Int) : zdividesb p x=true ↔ p∣x := by simp [zdividesb]

theorem zdividesb_true__duplicate_init_result (p x : Int) : zdividesb p x=true ↔ p∣x := zdividesb_true_iff__factor_scan_advance p x

theorem complete_prime_table_Znth_ge_2__factor_scan_divide (primes : List Int) (tested : Int)
    (ht : CompletePrimeTable primes) (hr : 0≤tested ∧ tested<Zlength primes) : 2≤Znth tested primes 0 :=
  (complete_prime_table_index_bounds__safety_prime_bounds primes tested ht hr).2.1

theorem complete_prime_table_mod_zero_divides__factor_scan_divide (primes : List Int) (tested rem : Int)
    (ht : CompletePrimeTable primes) (hr : 0≤tested ∧ tested<Zlength primes)
    (hm : Z.rem rem (Znth tested primes 0)=0) : Znth tested primes 0∣rem := by
  exact Int.dvd_of_tmod_eq_zero hm

theorem factor_scan_state2_initial__factor_scan_divide (a primes : List Int) (index : Int) (factors : List Int)
    (hbag : PrimeFactorBagPrefix a index factors) (hi : 0≤index ∧ index<Zlength a) (hpos : 1≤Znth index a 0) :
    FactorScanState2 a primes index 0 (Znth index a 0) factors := by
  have he := Znth_indep a index 0 1 hi
  refine ⟨factors,[],by simp,hbag,hi,⟨by omega,Zlength_nonneg primes⟩,by omega,?_,by simp,Forall.nil,?_,?_,?_⟩
  · rw [he]
  · intro p hp; simp
  · intro p hp; simp at hp
  · intro p hp; simp only [List.not_mem_nil,false_or,he]

theorem factor_scan_state2_append_divisor__factor_scan_divide (a primes : List Int) (index tested rem : Int) (factors : List Int)
    (ht : CompletePrimeTable primes) (hs : FactorScanState2 a primes index tested rem factors)
    (hr : 0≤tested ∧ tested<Zlength primes) (hd : Znth tested primes 0∣rem) :
    FactorDivideState2 a primes index tested rem (factors++[Znth tested primes 0]) := by
  have hp := (complete_prime_table_index_bounds__safety_prime_bounds primes tested ht hr).1
  rcases hs with ⟨done,picked,hf,hbag,hi,ht',hb,hd',hn,hp',hpk,hprior,hcover⟩
  refine ⟨done,picked,Znth tested primes 0,by rw [hf],hbag,hi,hr,rfl,hp,dvd_trans hd hd',hb,hd',hn,hp',hpk,hprior,?_⟩
  intro q hq
  rw [hcover q hq]
  simp only [List.mem_append,List.mem_singleton]
  constructor
  · rintro (hm | hqd)
    · exact Or.inl (Or.inl hm)
    · exact Or.inr hqd
  · rintro ((hm | he) | hqd)
    · exact Or.inl hm
    · exact Or.inr (he.symm ▸ hd)
    · exact Or.inr hqd

open SieveCount

theorem prime_prefix_table2_capacity__sieve_construction (bound : Int) (primes flags : List Int)
    (ht : PrimePrefixTable2 bound primes flags) : Zlength primes+1<4000 := by
  rcases ht with ⟨hb,hl,hn,hf,hi,hc,hflags⟩
  have hsub : primes⊆bounded_primes := by
    intro p hp
    rcases (hc p).mp hp with ⟨hr,hprime⟩
    exact bounded_primes_complete__sieve_construction p (by omega) hprime
  have hlen := List.Subperm.length_le (hn.subperm hsub)
  have hbound := bounded_primes_length__sieve_construction
  simp only [Zlength,Int.ofNat_eq_coe]
  omega

theorem prime_mark_table2_replace_step__sieve_marking_exits (factor next : Int) (primes flags : List Int)
    (hnext : next≤31623) (ht : PrimeMarkTable2 factor next primes flags) :
    PrimeMarkTable2 factor (next+factor) primes (replace_Znth next 1 flags) := by
  rcases ht with ⟨hb,hsq,hd,hl,hn,hf,hi,hc,hflags⟩
  refine ⟨hb,by nlinarith,dvd_add hd (dvd_refl _),by rw [Zlength_replace_Znth,hl],hn,hf,hi,hc,?_⟩
  intro k hk
  have hnr : 0≤next ∧ next<Zlength flags := by constructor <;> nlinarith
  by_cases he : k=next
  · subst k
    rw [Znth_replace_Znth_Same 0 flags next 1 hnr]
    constructor
    · intro h; contradiction
    · intro h
      exact False.elim (h (Or.inr ⟨hd,hsq,by omega⟩))
  · rw [Znth_replace_Znth_Diff 0 flags next k 1 hnr (by omega) (by omega),hflags k hk]
    have hequiv : (ProperMarkedBefore factor k ∨ factor∣k ∧ (factor*factor≤k ∧ k<next+factor)) ↔
        (ProperMarkedBefore factor k ∨ factor∣k ∧ (factor*factor≤k ∧ k<next)) := by
      constructor
      · rintro (hm | ⟨hdk,hkr⟩)
        · exact Or.inl hm
        · by_cases hkn : k<next
          · exact Or.inr ⟨hdk,hkr.1,hkn⟩
          · rcases dvd_sub hdk hd with ⟨q,hq⟩
            have hq0 : q=0 := by nlinarith
            subst q
            omega
      · rintro (hm | ⟨hdk,hkr⟩)
        · exact Or.inl hm
        · exact Or.inr ⟨hdk,hkr.1,by omega⟩
    exact not_congr hequiv.symm

theorem prime_mark_table2_finish__sieve_marking_exits (factor next : Int) (primes flags : List Int)
    (hnext : 31623<next) (ht : PrimeMarkTable2 factor next primes flags) :
    PrimePrefixTable2 (factor+1) primes flags := by
  rcases ht with ⟨hb,hsq,hd,hl,hn,hf,hi,hc,hflags⟩
  refine ⟨by omega,hl,hn,hf,hi,hc,?_⟩
  intro k hk
  rw [hflags k hk]
  apply not_congr
  constructor
  · rintro (⟨d,hr,hdk,hdiv⟩ | ⟨hdiv,hr⟩)
    · exact ⟨d,by omega,hdk,hdiv⟩
    · exact ⟨factor,by omega,by nlinarith,hdiv⟩
  · rintro ⟨d,hr,hdk,hdiv⟩
    by_cases hdf : d<factor
    · exact Or.inl ⟨d,⟨hr.1,hdf⟩,hdk,hdiv⟩
    · have he : d=factor := by omega
      subst d
      by_cases hksq : factor*factor≤k
      · exact Or.inr ⟨hdiv,hksq,by omega⟩
      · rcases hdiv with ⟨q,hq⟩
        have hq2 : 2≤q := by nlinarith
        have hqf : q<factor := by nlinarith
        have hqk : q<k := by nlinarith
        exact Or.inl ⟨q,⟨hq2,hqf⟩,hqk,⟨factor,by nlinarith⟩⟩

private theorem prime_dvd_prime_eq {p q : Int} (hp : prime p) (hq : prime q) (hd : p∣q) : p=q := by
  have h := prime_divisors q hq p ((Z.divide_iff_dvd _ _).mpr hd)
  have := prime_ge_2 p hp
  have := prime_ge_2 q hq
  omega

private theorem prime_dvd_mul {p a b : Int} (hp : prime p) (hd : p∣a*b) : p∣a ∨ p∣b := by
  have h := prime_mult p hp a b ((Z.divide_iff_dvd _ _).mpr hd)
  simpa only [Z.divide_iff_dvd] using h

private theorem nodup_snoc {A : Type} (l : List A) (x : A) (hn : l.Nodup) (hx : x∉l) : (l++[x]).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨hn,by simp,?_⟩
  intro a ha b hb he
  have hb' : b=x := by simpa using hb
  exact hx ((he.trans hb') ▸ ha)

private theorem forall_snoc {A : Type} (P : A → Prop) (l : List A) (x : A)
    (hl : Forall P l) (hx : P x) : Forall P (l++[x]) := by
  apply Forall.iff_forall_mem.mpr
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact hl.mem ha
  · have he : a=x := by simpa using ha
    exact he.symm ▸ hx

theorem factor_divide_state2_reduce__factor_scan_divide (a primes : List Int) (index tested rem : Int) (factors : List Int)
    (hs : FactorDivideState2 a primes index tested rem factors) (hd : Znth tested primes 0∣rem) :
    FactorDivideState2 a primes index tested (Z.quot rem (Znth tested primes 0)) factors := by
  rcases hs with ⟨done,picked,p,hf,hbag,hi,ht,heq,hp,hpd,hb,hrd,hn,hpf,hpk,hprior,hcover⟩
  subst p
  have hp2 := prime_ge_2 _ hp
  have he : rem=Znth tested primes 0*Z.quot rem (Znth tested primes 0) := by
    have h := Int.tmod_add_mul_tdiv rem (Znth tested primes 0)
    rw [Int.tmod_eq_zero_of_dvd hd] at h
    simpa only [Z.quot,zero_add] using h.symm
  have hq1 : 1≤Z.quot rem (Znth tested primes 0) := by nlinarith
  have hqle : Z.quot rem (Znth tested primes 0)≤rem := by nlinarith
  have hqd : Z.quot rem (Znth tested primes 0)∣rem := ⟨Znth tested primes 0,he.trans (mul_comm _ _)⟩
  refine ⟨done,picked,Znth tested primes 0,hf,hbag,hi,ht,rfl,hp,hpd,by omega,dvd_trans hqd hrd,hn,hpf,hpk,?_,?_⟩
  · intro q hq hdq
    exact hprior q hq (dvd_trans hdq hqd)
  · intro q hq
    rw [hcover q hq]
    constructor
    · rintro (hm | hdq)
      · exact Or.inl hm
      · rw [he] at hdq
        rcases prime_dvd_mul hq hdq with hdq | hdq
        · have heq := prime_dvd_prime_eq hq hp hdq
          exact Or.inl (List.mem_append.mpr (Or.inr (by simp [heq])))
        · exact Or.inr hdq
    · rintro (hm | hdq)
      · exact Or.inl hm
      · exact Or.inr (dvd_trans hdq hqd)

theorem factor_divide2_to_scan2_next__factor_scan_advance (a primes : List Int) (index tested rem : Int) (factors : List Int)
    (htab : CompletePrimeTable primes) (hs : FactorDivideState2 a primes index tested rem factors)
    (hmod : Z.rem rem (Znth tested primes 0)≠0) : FactorScanState2 a primes index (tested+1) rem factors := by
  rcases hs with ⟨done,picked,p,hf,hbag,hi,ht,heq,hp,hpd,hb,hrd,hn,hpf,hpk,hprior,hcover⟩
  subst p
  have htake := firstn_Z_succ__factor_scan_advance Int primes tested 0 ht
  have hnt : (primes.take tested.toNat++[Znth tested primes 0]).Nodup := by
    rw [←htake]; exact htab.1.take
  have hnot := NoDup_snoc_notin__factor_scan_advance Int _ _ hnt
  have hnotpicked : Znth tested primes 0∉picked := fun h=>hnot ((hpk _ hp).mp h).1
  have hnotrem : ¬Znth tested primes 0∣rem := fun hd=>hmod (Int.tmod_eq_zero_of_dvd hd)
  refine ⟨done,picked++[Znth tested primes 0],by simpa only [List.append_assoc] using hf,hbag,hi,by omega,hb,hrd,
    nodup_snoc picked _ hn hnotpicked,forall_snoc prime picked _ hpf hp,?_,?_,hcover⟩
  · intro q hq
    rw [htake]
    simp only [List.mem_append,List.mem_singleton]
    rw [hpk q hq]
    constructor
    · rintro (⟨hm,hdq⟩ | heq)
      · exact ⟨Or.inl hm,hdq⟩
      · exact ⟨Or.inr heq,heq.symm ▸ hpd⟩
    · rintro ⟨hm | heq,hdq⟩
      · exact Or.inl ⟨hm,hdq⟩
      · exact Or.inr heq
  · intro q hq
    rw [htake] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hprior q hq
    · have he : q=Znth tested primes 0 := by simpa using hq
      exact he.symm ▸ hnotrem

theorem factor_scan2_to_scan2_next__factor_scan_advance (a primes : List Int) (index tested rem : Int) (factors : List Int)
    (htab : CompletePrimeTable primes) (hs : FactorScanState2 a primes index tested rem factors)
    (ht : 0≤tested ∧ tested<Zlength primes) (hmod : Z.rem rem (Znth tested primes 0)≠0) :
    FactorScanState2 a primes index (tested+1) rem factors := by
  have hp := (complete_prime_table_index_bounds__safety_prime_bounds primes tested htab ht).1
  rcases hs with ⟨done,picked,hf,hbag,hi,ht',hb,hrd,hn,hpf,hpk,hprior,hcover⟩
  have htake := firstn_Z_succ__factor_scan_advance Int primes tested 0 ht
  have hnt : (primes.take tested.toNat++[Znth tested primes 0]).Nodup := by rw [←htake]; exact htab.1.take
  have hnot := NoDup_snoc_notin__factor_scan_advance Int _ _ hnt
  have hnotpicked : Znth tested primes 0∉picked := fun h=>hnot ((hpk _ hp).mp h).1
  have hnotrem : ¬Znth tested primes 0∣rem := fun hd=>hmod (Int.tmod_eq_zero_of_dvd hd)
  have hnotoriginal : ¬Znth tested primes 0∣Znth index a 1 := by
    intro hd
    rcases (hcover _ hp).mp hd with hpick | hr
    · exact hnotpicked hpick
    · exact hnotrem hr
  refine ⟨done,picked,hf,hbag,hi,by omega,hb,hrd,hn,hpf,?_,?_,hcover⟩
  · intro q hq
    rw [htake]
    simp only [List.mem_append,List.mem_singleton]
    rw [hpk q hq]
    constructor
    · rintro ⟨hm,hdq⟩; exact ⟨Or.inl hm,hdq⟩
    · rintro ⟨hm | he,hdq⟩
      · exact ⟨hm,hdq⟩
      · exact False.elim (hnotoriginal (he ▸ hdq))
  · intro q hq
    rw [htake] at hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hprior q hq
    · have he : q=Znth tested primes 0 := by simpa using hq
      exact he.symm ▸ hnotrem

private theorem prime_not_dvd_product {p : Int} (l : List Int) (hp : prime p)
    (hf : Forall prime l) (hnot : p∉l) : ¬p∣l.foldr (·*·) 1 := by
  induction l with
  | nil => intro hd; have hp2 := prime_ge_2 p hp; have := Int.le_of_dvd (by decide : (0:Int)<1) hd; omega
  | cons q l ih =>
    intro hd
    rcases prime_dvd_mul hp hd with hpq | hpl
    · have he := prime_dvd_prime_eq hp (hf.mem (by simp)) hpq
      exact hnot (by simp [he])
    · exact ih (by cases hf; assumption) (fun h=>hnot (List.mem_cons_of_mem q h)) hpl

theorem prime_rel_prime_product__factor_scan_advance (p : Int) (l : List Int)
    (hp : prime p) (hf : Forall prime l) (hnot : p∉l) : rel_prime p (l.foldr (·*·) 1) := by
  apply (Zgcd_1_rel_prime p _).mp
  have hp2 := prime_ge_2 p hp
  have hg := Int.gcd_pos_of_ne_zero_left (l.foldr (·*·) 1) (by omega : p≠0)
  have hgp := Int.gcd_dvd_left p (l.foldr (·*·) 1)
  have hgl := Int.gcd_dvd_right p (l.foldr (·*·) 1)
  have hc := prime_divisors p hp _ ((Z.divide_iff_dvd _ _).mpr hgp)
  have hnotdiv := prime_not_dvd_product l hp hf hnot
  change (Int.gcd p (l.foldr (·*·) 1):Int)=1
  rcases hc with h | h | h | h
  · omega
  · exact h
  · rw [h] at hgl; contradiction
  · omega

theorem product_distinct_primes_divides__factor_scan_advance (l : List Int) (x : Int)
    (hn : l.Nodup) (hf : Forall prime l) (hd : ∀p, p∈l → p∣x) : l.foldr (·*·) 1∣x := by
  induction l with
  | nil => exact one_dvd _
  | cons p l ih =>
    rcases List.nodup_cons.mp hn with ⟨hnot,hn'⟩
    have hp : prime p := hf.mem (by simp)
    have hf' : Forall prime l := by cases hf; assumption
    have hrest := ih hn' hf' (fun q hq=>hd q (List.mem_cons_of_mem p hq))
    rcases hrest with ⟨k,hk⟩
    have hpd := hd p (by simp)
    rw [hk] at hpd
    rcases prime_dvd_mul hp hpd with hprod | hpk
    · exact False.elim (prime_not_dvd_product l hp hf' hnot hprod)
    · rcases hpk with ⟨q,hq⟩
      refine ⟨q,?_⟩
      change x=(p*l.foldr (·*·) 1)*q
      rw [hk,hq]
      ring

theorem prime_divisor_exists__duplicate_init_result (x : Int) (hx : 1<x) : ∃p, prime p ∧ p∣x := by
  rcases Nat.exists_prime_and_dvd (by omega : x.toNat≠1) with ⟨p,hp,hd⟩
  have hx0 : (x.toNat:Int)=x := by omega
  refine ⟨(p:Int),?_,?_⟩
  · apply (prime_nat_iff (p:Int) (by omega)).mpr
    simpa only [Int.toNat_natCast] using hp
  · rw [←hx0]
    exact Int.natCast_dvd_natCast.mpr hd

private theorem znth_mem {A : Type} (a : List A) (d : A) (i : Int) (hi : 0≤i ∧ i<Zlength a) : Znth i a d∈a := by
  have hn : i.toNat<a.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,Option.getD_some]
  exact List.getElem_mem hn

theorem increasing_Znth_le__duplicate_loop (l : List Int) (i j : Int)
    (hinc : increasing l) (hij : 0≤i ∧ i≤j) (hj : j<Zlength l) : Znth i l 0≤Znth j l 0 := by
  induction l generalizing i j with
  | nil => simp only [Zlength_nil] at hj; omega
  | cons a l ih =>
    simp only [Zlength_cons] at hj
    by_cases hi0 : i=0
    · subst i
      by_cases hj0 : j=0
      · subst j; exact le_refl _
      · rw [Znth_cons 0 j a l (by omega)]
        exact increasing_aux_head_le_all_In l a _ hinc (znth_mem l 0 (j-1) (by omega))
    · rw [Znth_cons 0 i a l (by omega),Znth_cons 0 j a l (by omega)]
      exact ih (i-1) (j-1) (increasing_aux_tail_increasing l a hinc) (by omega) (by omega)

theorem composite_small_prime_divisor__factor_item_finish (n : Int) (hn : 1<n ∧ n≤1000000000) (hnot : ¬prime n) :
    ∃p, prime p ∧ p∣n ∧ p*p≤n := by
  have hn0 : (n.toNat:Int)=n := by omega
  have hnp : ¬n.toNat.Prime := fun h=>hnot ((prime_nat_iff n (by omega)).mpr h)
  have hp := Nat.minFac_prime (by omega : n.toNat≠1)
  have hd := Nat.minFac_dvd n.toNat
  have hsq := Nat.minFac_sq_le_self (by omega : 0<n.toNat) hnp
  refine ⟨(n.toNat.minFac:Int),?_,?_,?_⟩
  · apply (prime_nat_iff _ (by omega)).mpr
    simpa only [Int.toNat_natCast] using hp
  · rw [←hn0]
    exact Int.natCast_dvd_natCast.mpr hd
  · have hsq' : ((n.toNat.minFac^2:Nat):Int)≤(n.toNat:Int) := by exact_mod_cast hsq
    simpa only [Nat.cast_pow,hn0,pow_two] using hsq'

theorem residual_prime_exhausted__factor_item_finish (primes : List Int) (tested rem : Int)
    (ht : CompletePrimeTable primes) (hr : 0≤tested ∧ tested≤Zlength primes)
    (hex : ∀p, p∈primes.take tested.toNat → ¬p∣rem) (hrem : 1<rem ∧ rem≤1000000000)
    (hend : tested≥Zlength primes) : prime rem := by
  by_contra hnot
  rcases composite_small_prime_divisor__factor_item_finish rem hrem hnot with ⟨p,hp,hd,hsq⟩
  have hp2 := prime_ge_2 p hp
  have hpbound : 2≤p ∧ p≤31623 := ⟨hp2,by nlinarith⟩
  have hmem := (ht.2.2.2 p).mpr ⟨hpbound,hp⟩
  apply hex p _ hd
  have hn : primes.length≤tested.toNat := by simp only [Zlength,Int.ofNat_eq_coe] at hend; omega
  rwa [List.take_of_length_le hn]

theorem complete_prime_before_index__factor_item_finish (primes : List Int) (j q : Int)
    (ht : CompletePrimeTable primes) (hj : 0≤j ∧ j<Zlength primes) (hq : prime q)
    (hqb : 2≤q ∧ q≤31623) (hlt : q<Znth j primes 0) : q∈primes.take j.toNat := by
  have hmem := (ht.2.2.2 q).mpr ⟨hqb,hq⟩
  rcases List.mem_iff_getElem.mp hmem with ⟨k,hk,hke⟩
  have hkr : 0≤(k:Int) ∧ (k:Int)<Zlength primes := by simp only [Zlength,Int.ofNat_eq_coe]; omega
  have hkread : Znth (k:Int) primes 0=q := by
    simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some] using hke
  have hkj : (k:Int)<j := by
    by_contra hn
    have hle := increasing_Znth_le__duplicate_loop primes j (k:Int) ht.2.2.1 (by omega) hkr.2
    rw [hkread] at hle
    omega
  apply List.mem_iff_getElem.mpr
  have hkt : k<(primes.take j.toNat).length := by simp only [List.length_take]; omega
  refine ⟨k,hkt,?_⟩
  simpa only [List.getElem_take] using hke

theorem residual_prime_square_cutoff__factor_item_finish (primes : List Int) (tested rem : Int)
    (ht : CompletePrimeTable primes) (hr : 0≤tested ∧ tested<Zlength primes)
    (hex : ∀p, p∈primes.take tested.toNat → ¬p∣rem) (hrem : 1<rem ∧ rem≤1000000000)
    (hcut : Znth tested primes 0*Znth tested primes 0>rem) : prime rem := by
  by_contra hnot
  rcases composite_small_prime_divisor__factor_item_finish rem hrem hnot with ⟨p,hp,hd,hsq⟩
  have hp2 := prime_ge_2 p hp
  have hq2 := complete_prime_table_Znth_ge_2__factor_scan_divide primes tested ht hr
  have hpbound : 2≤p ∧ p≤31623 := ⟨hp2,by nlinarith⟩
  have hlt : p<Znth tested primes 0 := by nlinarith
  exact hex p (complete_prime_before_index__factor_item_finish primes tested p ht hr hp hpbound hlt) hd

theorem firstn_succ_Znth__factor_item_finish (l : List Int) (i d : Int) (hi : 0≤i ∧ i<Zlength l) :
    l.take (i+1).toNat=l.take i.toNat++[Znth i l d] := firstn_Z_succ__factor_scan_advance Int l i d hi

set_option maxHeartbeats 2000000 in
theorem increasing_nodup_prime_ten_product__factor_scan_advance (l : List Int)
    (hinc : increasing l) (hn : l.Nodup) (hf : Forall prime l) (hlen : 10≤l.length) :
    1000000000<(l.take 10).foldr (·*·) 1 := by
  rcases l with _ | ⟨p0, _ | ⟨p1, _ | ⟨p2, _ | ⟨p3, _ | ⟨p4, _ | ⟨p5, _ | ⟨p6, _ | ⟨p7, _ | ⟨p8, _ | ⟨p9, rest⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;> simp only [List.length_cons,List.length_nil] at hlen <;> try omega
  simp only [List.nodup_cons] at hn
  rcases hn with ⟨hn0, ⟨hn1, ⟨hn2, ⟨hn3, ⟨hn4, ⟨hn5, ⟨hn6, ⟨hn7, ⟨hn8, ⟨hn9, hnd⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩
  change p0≤p1 ∧ p1≤p2 ∧ p2≤p3 ∧ p3≤p4 ∧ p4≤p5 ∧ p5≤p6 ∧ p6≤p7 ∧ p7≤p8 ∧ p8≤p9 ∧ increasing_aux rest p9 at hinc
  rcases hinc with ⟨hi0, ⟨hi1, ⟨hi2, ⟨hi3, ⟨hi4, ⟨hi5, ⟨hi6, ⟨hi7, ⟨hi8, hic⟩⟩⟩⟩⟩⟩⟩⟩⟩
  have hp0 : prime p0 := hf.mem (List.mem_cons_self)
  have hp1 : prime p1 := hf.mem (List.mem_cons_of_mem p0 (List.mem_cons_self))
  have hp2 : prime p2 := hf.mem (List.mem_cons_of_mem p0 (List.mem_cons_of_mem p1 (List.mem_cons_self)))
  have hp3 : prime p3 := hf.mem (List.mem_cons_of_mem p0 (List.mem_cons_of_mem p1 (List.mem_cons_of_mem p2 (List.mem_cons_self))))
  have hp4 : prime p4 := hf.mem (List.mem_cons_of_mem p0 (List.mem_cons_of_mem p1 (List.mem_cons_of_mem p2 (List.mem_cons_of_mem p3 (List.mem_cons_self)))))
  have hp5 : prime p5 := hf.mem (List.mem_cons_of_mem p0 (List.mem_cons_of_mem p1 (List.mem_cons_of_mem p2 (List.mem_cons_of_mem p3 (List.mem_cons_of_mem p4 (List.mem_cons_self))))))
  have hp6 : prime p6 := hf.mem (List.mem_cons_of_mem p0 (List.mem_cons_of_mem p1 (List.mem_cons_of_mem p2 (List.mem_cons_of_mem p3 (List.mem_cons_of_mem p4 (List.mem_cons_of_mem p5 (List.mem_cons_self)))))))
  have hp7 : prime p7 := hf.mem (List.mem_cons_of_mem p0 (List.mem_cons_of_mem p1 (List.mem_cons_of_mem p2 (List.mem_cons_of_mem p3 (List.mem_cons_of_mem p4 (List.mem_cons_of_mem p5 (List.mem_cons_of_mem p6 (List.mem_cons_self))))))))
  have hp8 : prime p8 := hf.mem (List.mem_cons_of_mem p0 (List.mem_cons_of_mem p1 (List.mem_cons_of_mem p2 (List.mem_cons_of_mem p3 (List.mem_cons_of_mem p4 (List.mem_cons_of_mem p5 (List.mem_cons_of_mem p6 (List.mem_cons_of_mem p7 (List.mem_cons_self)))))))))
  have hp9 : prime p9 := hf.mem (List.mem_cons_of_mem p0 (List.mem_cons_of_mem p1 (List.mem_cons_of_mem p2 (List.mem_cons_of_mem p3 (List.mem_cons_of_mem p4 (List.mem_cons_of_mem p5 (List.mem_cons_of_mem p6 (List.mem_cons_of_mem p7 (List.mem_cons_of_mem p8 (List.mem_cons_self))))))))))
  have hs0 : p0<p1 := by
    have hne : p0≠p1 := fun he=>hn0 (by rw [he]; exact List.mem_cons_self)
    omega
  have hs1 : p1<p2 := by
    have hne : p1≠p2 := fun he=>hn1 (by rw [he]; exact List.mem_cons_self)
    omega
  have hs2 : p2<p3 := by
    have hne : p2≠p3 := fun he=>hn2 (by rw [he]; exact List.mem_cons_self)
    omega
  have hs3 : p3<p4 := by
    have hne : p3≠p4 := fun he=>hn3 (by rw [he]; exact List.mem_cons_self)
    omega
  have hs4 : p4<p5 := by
    have hne : p4≠p5 := fun he=>hn4 (by rw [he]; exact List.mem_cons_self)
    omega
  have hs5 : p5<p6 := by
    have hne : p5≠p6 := fun he=>hn5 (by rw [he]; exact List.mem_cons_self)
    omega
  have hs6 : p6<p7 := by
    have hne : p6≠p7 := fun he=>hn6 (by rw [he]; exact List.mem_cons_self)
    omega
  have hs7 : p7<p8 := by
    have hne : p7≠p8 := fun he=>hn7 (by rw [he]; exact List.mem_cons_self)
    omega
  have hs8 : p8<p9 := by
    have hne : p8≠p9 := fun he=>hn8 (by rw [he]; exact List.mem_cons_self)
    omega
  have hb0 : 2≤p0 := prime_ge_2 p0 hp0
  have hb1 : 3≤p1 := by omega
  have hb2 : 5≤p2 := prime_floor_5__factor_scan_advance p2 hp2 (by omega)
  have hb3 : 7≤p3 := prime_floor_7__factor_scan_advance p3 hp3 (by omega)
  have hb4 : 11≤p4 := prime_floor_11__factor_scan_advance p4 hp4 (by omega)
  have hb5 : 13≤p5 := prime_floor_13__factor_scan_advance p5 hp5 (by omega)
  have hb6 : 17≤p6 := prime_floor_17__factor_scan_advance p6 hp6 (by omega)
  have hb7 : 19≤p7 := prime_floor_19__factor_scan_advance p7 hp7 (by omega)
  have hb8 : 23≤p8 := prime_floor_23__factor_scan_advance p8 hp8 (by omega)
  have hb9 : 29≤p9 := prime_floor_29__factor_scan_advance p9 hp9 (by omega)
  change 1000000000<p0*(p1*(p2*(p3*(p4*(p5*(p6*(p7*(p8*(p9*1)))))))))
  have hlower : 2*(3*(5*(7*(11*(13*(17*(19*(23*(29*1))))))))) ≤ p0*(p1*(p2*(p3*(p4*(p5*(p6*(p7*(p8*(p9*1))))))))) := by
    gcongr <;> omega
  change 6469693230≤p0*(p1*(p2*(p3*(p4*(p5*(p6*(p7*(p8*(p9*1))))))))) at hlower
  omega

theorem increasing_prime_divisors_length__factor_scan_advance (l : List Int) (x : Int)
    (hi : increasing l) (hn : l.Nodup) (hf : Forall prime l) (hd : ∀p, p∈l → p∣x)
    (hx : 1≤x ∧ x≤1000000000) : l.length≤9 := by
  by_contra hlen
  have hlarge := increasing_nodup_prime_ten_product__factor_scan_advance l hi hn hf (by omega)
  have hft : Forall prime (l.take 10) := Forall.iff_forall_mem.mpr (fun p hp=>hf.mem (List.mem_of_mem_take hp))
  have hdt : (l.take 10).foldr (·*·) 1∣x := product_distinct_primes_divides__factor_scan_advance _ x hn.take hft
    (fun p hp=>hd p (List.mem_of_mem_take hp))
  have hle := Int.le_of_dvd (by omega : 0<x) hdt
  omega

theorem distinct_prime_divisors_length__factor_scan_advance (l : List Int) (x : Int)
    (hn : l.Nodup) (hf : Forall prime l) (hd : ∀p, p∈l → p∣x)
    (hx : 1≤x ∧ x≤1000000000) : l.length≤9 := by
  have hp := sort_list_perm l
  have hfs : Forall prime (sort l) := Forall.iff_forall_mem.mpr (fun p h=>hf.mem (hp.mem_iff.mpr h))
  have hlen := increasing_prime_divisors_length__factor_scan_advance (sort l) x (sort_list_increasing l)
    (hp.nodup_iff.mp hn) hfs (fun p h=>hd p (hp.mem_iff.mpr h)) hx
  rwa [hp.length_eq] 

theorem sum_count_occ_notin__factor_scan_advance (a : Int) (u l : List Int) (hnot : a∉u) :
    (u.map (fun x=>(a::l).count x)).foldr Nat.add 0=(u.map (fun x=>l.count x)).foldr Nat.add 0 := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    have hne : b≠a := by intro he; exact hnot (by rw [he]; exact List.mem_cons_self)
    have hn : a∉u := fun h=>hnot (List.mem_cons_of_mem b h)
    change (a::l).count b+_ = l.count b+_
    rw [show (a::l).count b=l.count b by simp [List.count_cons,hne,Ne.symm hne],ih hn]

theorem sum_count_occ_cons__factor_scan_advance (a : Int) (u l : List Int) (hn : u.Nodup) (hm : a∈u) :
    (u.map (fun x=>(a::l).count x)).foldr Nat.add 0=((u.map (fun x=>l.count x)).foldr Nat.add 0).succ := by
  induction u with
  | nil => contradiction
  | cons b u ih =>
    rcases List.nodup_cons.mp hn with ⟨hb,hn'⟩
    rcases List.mem_cons.mp hm with he | hm
    · subst b
      change (a::l).count a+_ = (l.count a+_).succ
      rw [sum_count_occ_notin__factor_scan_advance a u l hb]
      simp only [List.count_cons_self]
      omega
    · have hne : b≠a := by intro he; exact hb (he.symm ▸ hm)
      change (a::l).count b+_ = (l.count b+_).succ
      rw [show (a::l).count b=l.count b by simp [List.count_cons,hne,Ne.symm hne],ih hn' hm]
      omega

theorem sum_count_occ_nil__factor_scan_advance (u : List Int) :
    (u.map (fun x=>([]:List Int).count x)).foldr Nat.add 0=0 := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    change Nat.add 0 ((u.map (fun x=>([]:List Int).count x)).foldr Nat.add 0)=0
    rw [ih]

theorem length_as_sum_count_occ__factor_scan_advance (l u : List Int) (hn : u.Nodup) (hc : ∀a, a∈l → a∈u) :
    l.length=(u.map (fun x=>l.count x)).foldr Nat.add 0 := by
  induction l with
  | nil => exact (sum_count_occ_nil__factor_scan_advance u).symm
  | cons a l ih =>
    rw [sum_count_occ_cons__factor_scan_advance a u l hn (hc a List.mem_cons_self)]
    exact congrArg Nat.succ (ih (fun x hx=>hc x (List.mem_cons_of_mem a hx)))

theorem sum_filter_cons__factor_scan_advance (u vals : List Int) (x : Int) (f : Int → Int → Bool) :
    (u.map (fun p=>((x::vals).filter (fun y=>f p y)).length)).foldr Nat.add 0=
      (u.filter (fun p=>f p x)).length+(u.map (fun p=>(vals.filter (fun y=>f p y)).length)).foldr Nat.add 0 := by
  induction u with
  | nil => rfl
  | cons p u ih =>
    simp only [List.map_cons,List.foldr_cons]
    rw [ih]
    let A : Nat := (vals.filter (fun y=>f p y)).length
    let B : Nat := (u.filter (fun p=>f p x)).length
    let C : Nat := (u.map (fun p=>(vals.filter (fun y=>f p y)).length)).foldr Nat.add 0
    cases he : f p x <;> simp only [List.filter_cons,he,Bool.false_eq_true,if_false,if_true,List.length_cons]
    · change A+(B+C)=B+(A+C)
      omega
    · change (A+1)+(B+C)=(B+1)+(A+C)
      omega

theorem transpose_filter_counts__factor_scan_advance (u vals : List Int) (f : Int → Int → Bool) :
    (u.map (fun p=>(vals.filter (fun x=>f p x)).length)).foldr Nat.add 0=
      (vals.map (fun x=>(u.filter (fun p=>f p x)).length)).foldr Nat.add 0 := by
  induction vals with
  | nil =>
    induction u with
    | nil => rfl
    | cons a u ih =>
      simp only [List.map_cons,List.filter_nil,List.length_nil,List.foldr_cons,List.map_nil,List.foldr_nil] at ih ⊢
      rw [ih]
  | cons x vals ih =>
    rw [sum_filter_cons__factor_scan_advance u vals x f,ih]
    rfl

theorem prime_filter_length__factor_scan_advance (u : List Int) (x : Int) (hn : u.Nodup) (hf : Forall prime u)
    (hx : 1≤x ∧ x≤1000000000) : (u.filter (fun p=>zdividesb p x)).length≤9 := by
  apply distinct_prime_divisors_length__factor_scan_advance _ x (hn.filter _)
  · exact Forall.iff_forall_mem.mpr (fun p hp=>hf.mem (List.mem_filter.mp hp).1)
  · intro p hp
    exact (zdividesb_true_iff__factor_scan_advance p x).mp (List.mem_filter.mp hp).2
  · exact hx

theorem sum_prime_filter_bound__factor_scan_advance (vals u : List Int)
    (hb : Forall (fun x=>1≤x ∧ x≤1000000000) vals) (hn : u.Nodup) (hf : Forall prime u) :
    (vals.map (fun x=>(u.filter (fun p=>zdividesb p x)).length)).foldr Nat.add 0≤vals.length*9 := by
  induction vals with
  | nil => exact le_refl _
  | cons x vals ih =>
    have hx := hb.mem List.mem_cons_self
    have ht : Forall (fun x=>1≤x ∧ x≤1000000000) vals := by cases hb; assumption
    have h1 := prime_filter_length__factor_scan_advance u x hn hf hx
    have h2 := ih ht
    change (u.filter (fun p=>zdividesb p x)).length+_≤(vals.length+1)*9
    omega

theorem sum_counts_to_filters__factor_scan_advance (u factors vals : List Int) (hf : Forall prime u)
    (hc : ∀p, prime p → (factors.count p:Int)=((vals.filter (zdividesb p)).length:Int)) :
    (u.map (fun p=>factors.count p)).foldr Nat.add 0=
      (u.map (fun p=>(vals.filter (zdividesb p)).length)).foldr Nat.add 0 := by
  congr 1
  apply List.map_congr_left
  intro p hp
  have h := hc p (hf.mem hp)
  omega

theorem prime_factor_bag_length_bound__factor_scan_advance (a : List Int) (index : Int) (factors : List Int)
    (hbag : PrimeFactorBagPrefix a index factors) (hb : Forall (fun x=>1≤x ∧ x≤1000000000) a) : Zlength factors≤index*9 := by
  rcases hbag with ⟨hi,hf,hc⟩
  let u := factors.dedup
  let vals := a.take index.toNat
  have hn : u.Nodup := List.nodup_dedup factors
  have hu : Forall prime u := Forall.iff_forall_mem.mpr (fun p hp=>hf.mem (List.mem_dedup.mp hp))
  have hv : Forall (fun x=>1≤x ∧ x≤1000000000) vals := Forall.iff_forall_mem.mpr (fun x hx=>hb.mem (List.mem_of_mem_take hx))
  have hlen := length_as_sum_count_occ__factor_scan_advance factors u hn (fun p hp=>List.mem_dedup.mpr hp)
  have hcounts := sum_counts_to_filters__factor_scan_advance u factors vals hu hc
  have hnat : factors.length≤vals.length*9 := by
    rw [hlen,hcounts,transpose_filter_counts__factor_scan_advance]
    exact sum_prime_filter_bound__factor_scan_advance vals u hv hn hu
  have hvlen : vals.length=index.toNat := by
    have hin : index.toNat≤a.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
    exact List.length_take_of_le hin
  rw [hvlen] at hnat
  simp only [Zlength,Int.ofNat_eq_coe]
  omega

theorem factor_scan2_capacity_next__factor_scan_advance (a primes : List Int) (index tested rem : Int) (factors : List Int) (count : Int)
    (ht : CompletePrimeTable primes) (hs : FactorScanState2 a primes index tested rem factors)
    (hb : Forall (fun x=>1≤x ∧ x≤1000000000) a) (hcount : count=Zlength factors) :
    FactorAppendCapacity primes index tested rem count := by
  rcases hs with ⟨done,picked,hf,hbag,hi,ht',hr,hd,hn,hpf,hpk,hprior,hcover⟩
  rintro ⟨htr,hdiv⟩
  have hp := (complete_prime_table_index_bounds__safety_prime_bounds primes tested ht htr).1
  have hnot : Znth tested primes 0∉picked := fun h=>hprior _ ((hpk _ hp).mp h).1 hdiv
  have hds : ∀p, p∈picked++[Znth tested primes 0] → p∣Znth index a 1 := by
    intro p hmem
    rcases List.mem_append.mp hmem with hm | hm
    · exact ((hpk p (hpf.mem hm)).mp hm).2
    · have he : p=Znth tested primes 0 := by simpa using hm
      exact he.symm ▸ dvd_trans hdiv hd
  have horig := hb.mem (znth_mem a 1 index hi)
  have hselected := distinct_prime_divisors_length__factor_scan_advance _ (Znth index a 1)
    (nodup_snoc picked _ hn hnot) (forall_snoc prime picked _ hpf hp) hds horig
  have hdone := prime_factor_bag_length_bound__factor_scan_advance a index done hbag hb
  simp only [List.length_append,List.length_cons,List.length_nil] at hselected
  rw [hcount,hf,Zlength_app]
  simp only [Zlength,Int.ofNat_eq_coe] at hdone ⊢
  omega

theorem pointwise_bounds_Forall__factor_scan_advance (a : List Int)
    (hb : ∀k, (0≤k ∧ k<Zlength a) → 1≤Znth k a 0 ∧ Znth k a 0≤1000000000) :
    Forall (fun x=>1≤x ∧ x≤1000000000) a := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  rcases List.mem_iff_getElem.mp hx with ⟨k,hk,hke⟩
  have h := hb (k:Int) (by simp only [Zlength,Int.ofNat_eq_coe]; omega)
  simpa only [Znth,Int.toNat_natCast,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hk,Option.getD_some,hke] using h

theorem prime_factor_bag_prefix_next__factor_item_finish (a : List Int) (index : Int) (done picked : List Int)
    (hbag : PrimeFactorBagPrefix a index done) (hi : 0≤index ∧ index<Zlength a)
    (hn : picked.Nodup) (hf : Forall prime picked) (hpk : ∀p, prime p → (p∈picked ↔ p∣Znth index a 1)) :
    PrimeFactorBagPrefix a (index+1) (done++picked) := by
  rcases hbag with ⟨hb,hdf,hcounts⟩
  refine ⟨by omega,?_,?_⟩
  · apply Forall.iff_forall_mem.mpr
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hdf.mem hp
    · exact hf.mem hp
  · intro p hp
    have hc := hcounts p hp
    rw [List.count_append,firstn_succ_Znth__factor_item_finish a index 1 hi,List.filter_append,List.length_append]
    by_cases hd : p∣Znth index a 1
    · have hmem := (hpk p hp).mpr hd
      have hcount := List.count_eq_one_of_mem hn hmem
      have hfilter : ([Znth index a 1].filter (zdividesb p)).length=1 := by simp [zdividesb,hd]
      rw [hcount,hfilter]
      omega
    · have hnot : p∉picked := fun h=>hd ((hpk p hp).mp h)
      have hcount := List.count_eq_zero_of_not_mem hnot
      have hfilter : ([Znth index a 1].filter (zdividesb p)).length=0 := by simp [zdividesb,hd]
      rw [hcount,hfilter]
      omega

theorem factor_scan2_residual_complete__factor_item_finish (a primes : List Int) (index tested rem : Int) (factors : List Int)
    (hs : FactorScanState2 a primes index tested rem factors) (hp : prime rem) :
    PrimeFactorBagPrefix a (index+1) (factors++[rem]) := by
  rcases hs with ⟨done,picked,hf,hbag,hi,ht,hb,hd,hn,hpf,hpk,hprior,hcover⟩
  have hnot : rem∉picked := fun hm=>hprior rem ((hpk rem hp).mp hm).1 (dvd_refl _)
  rw [hf,List.append_assoc]
  apply prime_factor_bag_prefix_next__factor_item_finish a index done (picked++[rem]) hbag hi
    (nodup_snoc picked rem hn hnot) (forall_snoc prime picked rem hpf hp)
  intro p hprime
  simp only [List.mem_append,List.mem_singleton]
  rw [hcover p hprime]
  constructor
  · rintro (hm | he)
    · exact Or.inl hm
    · exact Or.inr (he.symm ▸ dvd_refl rem)
  · rintro (hm | hpd)
    · exact Or.inl hm
    · exact Or.inr (prime_dvd_prime_eq hprime hp hpd)

theorem factor_scan2_unit_complete__factor_item_finish (a primes : List Int) (index tested rem : Int) (factors : List Int)
    (hs : FactorScanState2 a primes index tested rem factors) (he : rem=1) : PrimeFactorBagPrefix a (index+1) factors := by
  rcases hs with ⟨done,picked,hf,hbag,hi,ht,hb,hd,hn,hpf,hpk,hprior,hcover⟩
  rw [hf]
  apply prime_factor_bag_prefix_next__factor_item_finish a index done picked hbag hi hn hpf
  intro p hp
  rw [hcover p hp,he]
  constructor
  · exact Or.inl
  · rintro (hm | hd)
    · exact hm
    · have hp2 := prime_ge_2 p hp
      have := Int.le_of_dvd (by decide : (0:Int)<1) hd
      omega

theorem prime_factor_bag_prefix_permutation__duplicate_init_result (a : List Int) (upto : Int) (factors sorted : List Int)
    (hp : factors.Perm sorted) (hb : PrimeFactorBagPrefix a upto factors) : PrimeFactorBagPrefix a upto sorted := by
  rcases hb with ⟨hr,hf,hc⟩
  refine ⟨hr,Forall.iff_forall_mem.mpr (fun p hm=>hf.mem (hp.mem_iff.mpr hm)),?_⟩
  intro p hprime
  rw [←hp.count_eq p]
  exact hc p hprime

theorem duplicate_scan_loop_initial__duplicate_init_result (factors : List Int) (count : Int)
    (hlen : Zlength factors=count) (hcount : 0≤count) : DuplicateScanLoopState factors count 1 0 := by
  by_cases hz : count=0
  · left
    refine ⟨hz,rfl,by omega,Or.inl rfl,?_⟩
    constructor
    · intro h; contradiction
    · rintro ⟨i,j,hr,hj,he⟩; omega
  · right
    refine ⟨by omega,by omega,by omega,Or.inl rfl,?_⟩
    constructor
    · intro h; contradiction
    · rintro ⟨i,j,hr,hj,he⟩; omega

theorem duplicate_scan_loop_exit__duplicate_init_result (factors : List Int) (count cursor found : Int)
    (he : count≤cursor) (hs : DuplicateScanLoopState factors count cursor found) : DuplicatePrefixState factors count found := by
  rcases hs with ⟨hc,hi,hp⟩ | ⟨hc,hi,hp⟩
  · rwa [hc]
  · have hi' : cursor=count := by omega
    rwa [hi'] at hp

theorem duplicate_scan_equal_step__duplicate_loop (factors : List Int) (count i found : Int)
    (hlen : Zlength factors=count) (hs : DuplicateScanLoopState factors count i found)
    (hi : 1≤i) (hic : i<count) (he : Znth i factors 0=Znth (i-1) factors 0) :
    DuplicateScanLoopState factors count (i+1) 1 := by
  right
  refine ⟨by omega,by omega,by omega,Or.inr rfl,?_⟩
  constructor
  · intro h
    exact ⟨i-1,i,by omega,by omega,he.symm⟩
  · intro h; rfl

theorem duplicate_scan_unequal_step__duplicate_loop (factors : List Int) (count i found : Int)
    (hlen : Zlength factors=count) (hinc : increasing factors) (hs : DuplicateScanLoopState factors count i found)
    (hi : 1≤i) (hic : i<count) (hne : Znth i factors 0≠Znth (i-1) factors 0) :
    DuplicateScanLoopState factors count (i+1) found := by
  rcases hs with ⟨hc,hi',hp⟩ | ⟨hc,hi',hp⟩
  · omega
  · rcases hp with ⟨hb,hbool,hdup⟩
    right
    refine ⟨hc,by omega,by omega,hbool,?_⟩
    constructor
    · intro h
      rcases hdup.mp h with ⟨x,y,hr,hy,he⟩
      exact ⟨x,y,hr,by omega,he⟩
    · rintro ⟨x,y,hr,hy,he⟩
      apply hdup.mpr
      by_cases hyi : y<i
      · exact ⟨x,y,hr,hyi,he⟩
      · have hy' : y=i := by omega
        subst y
        have hprev := increasing_Znth_le__duplicate_loop factors (i-1) i hinc (by omega) (by omega)
        have hx := increasing_Znth_le__duplicate_loop factors x (i-1) hinc (by omega) (by omega)
        exact False.elim (hne (by omega))

theorem two_occurrences_nat_count_occ__duplicate_init_result (A : Type) (dec : DecidableEq A)
    (l : List A) (x d : A) (i j : Nat) (hij : i<j) (hj : j<l.length)
    (hiX : l.getD i d=x) (hjX : l.getD j d=x) :
    (letI : DecidableEq A := dec; 2≤l.count x) := by
  letI : DecidableEq A := dec
  change 2≤l.count x
  induction l generalizing i j with
  | nil => simp only [List.length_nil] at hj; omega
  | cons a l ih =>
    cases j with
    | zero => omega
    | succ j =>
      have hj' : j<l.length := by simpa only [List.length_cons,Nat.succ_lt_succ_iff] using hj
      have hjX' : l.getD j d=x := hjX
      cases i with
      | zero =>
        have he : a=x := hiX
        have hmem : x∈l := by
          rw [←hjX']
          simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj',Option.getD_some]
          exact List.getElem_mem hj'
        have hc := List.count_pos_iff.mpr hmem
        rw [he,List.count_cons_self]
        omega
      | succ i =>
        have hc := ih i j (by omega) hj' hiX hjX'
        rw [List.count_cons]
        split <;> omega

theorem count_occ_two_occurrences_nat__duplicate_init_result (A : Type) (dec : DecidableEq A)
    (l : List A) (x d : A) (hc : letI : DecidableEq A := dec; 2≤l.count x) :
    ∃i j : Nat, i<j ∧ j<l.length ∧ l.getD i d=x ∧ l.getD j d=x := by
  letI : DecidableEq A := dec
  change 2≤l.count x at hc
  induction l with
  | nil => simp only [List.count_nil] at hc; omega
  | cons a l ih =>
    by_cases he : a=x
    · rw [he,List.count_cons_self] at hc
      have hmem : x∈l := List.count_pos_iff.mp (by omega)
      rcases List.mem_iff_getElem.mp hmem with ⟨j,hj,hjx⟩
      refine ⟨0,j+1,by omega,by simp only [List.length_cons]; omega,he,?_⟩
      change l.getD j d=x
      simpa only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hj,Option.getD_some] using hjx
    · rw [List.count_cons_of_ne he] at hc
      rcases ih hc with ⟨i,j,hij,hj,hix,hjx⟩
      exact ⟨i+1,j+1,by omega,by simp only [List.length_cons]; omega,hix,hjx⟩

theorem two_occurrences_count_occ__duplicate_init_result (A : Type) (dec : DecidableEq A) (l : List A) (x d : A) :
    (∃i j : Int, (0≤i ∧ i<j) ∧ j<Zlength l ∧ Znth i l d=x ∧ Znth j l d=x) ↔
      (letI : DecidableEq A := dec; 2≤l.count x) := by
  constructor
  · rintro ⟨i,j,hr,hj,hix,hjx⟩
    have hjn : j.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hj; omega
    exact two_occurrences_nat_count_occ__duplicate_init_result A dec l x d i.toNat j.toNat (by omega) hjn hix hjx
  · intro hc
    rcases count_occ_two_occurrences_nat__duplicate_init_result A dec l x d hc with ⟨i,j,hij,hj,hix,hjx⟩
    refine ⟨(i:Int),(j:Int),by omega,by simp only [Zlength,Int.ofNat_eq_coe]; omega,?_,?_⟩
    · simpa only [Znth,Int.toNat_natCast] using hix
    · simpa only [Znth,Int.toNat_natCast] using hjx

theorem Znth_map_in_range__duplicate_init_result (A B : Type) (f : A → B) (l : List A) (i : Int) (da : A) (db : B)
    (hi : 0≤i ∧ i<Zlength l) : Znth i (l.map f) db=f (Znth i l da) := by
  have hn : i.toNat<l.length := by simp only [Zlength,Int.ofNat_eq_coe] at hi; omega
  have hm : i.toNat<(l.map f).length := by simpa only [List.length_map] using hn
  simp only [Znth,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hn,List.getElem?_eq_getElem hm,Option.getD_some,List.getElem_map]

theorem filter_length_count_true__duplicate_init_result (f : Int → Bool) (l : List Int) :
    (l.filter f).length=(l.map f).count true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases he : f a <;> simp only [List.filter_cons,he,Bool.false_eq_true,if_false,if_true,List.length_cons,List.map_cons,List.count_cons,he,show (false==true)=false from rfl,show (true==true)=true from rfl] <;> omega

theorem filter_two_indices__duplicate_init_result (f : Int → Bool) (l : List Int) :
    2≤(l.filter f).length ↔ ∃i j : Int, (0≤i ∧ i<j) ∧ j<Zlength l ∧ f (Znth i l 0)=true ∧ f (Znth j l 0)=true := by
  have hl : Zlength (l.map f)=Zlength l := by simp only [Zlength,List.length_map]
  rw [filter_length_count_true__duplicate_init_result]
  constructor
  · intro hc
    rcases (two_occurrences_count_occ__duplicate_init_result Bool inferInstance (l.map f) true false).mpr hc with ⟨i,j,hr,hj,hiX,hjX⟩
    rw [hl] at hj
    rw [Znth_map_in_range__duplicate_init_result Int Bool f l i 0 false (by omega)] at hiX
    rw [Znth_map_in_range__duplicate_init_result Int Bool f l j 0 false (by omega)] at hjX
    exact ⟨i,j,hr,hj,hiX,hjX⟩
  · rintro ⟨i,j,hr,hj,hiX,hjX⟩
    apply (two_occurrences_count_occ__duplicate_init_result Bool inferInstance (l.map f) true false).mp
    refine ⟨i,j,hr,by omega,?_,?_⟩
    · rw [Znth_map_in_range__duplicate_init_result Int Bool f l i 0 false (by omega)]; exact hiX
    · rw [Znth_map_in_range__duplicate_init_result Int Bool f l j 0 false (by omega)]; exact hjX

theorem prime_factor_duplicate_spec__duplicate_init_result (a factors : List Int) (count found : Int)
    (hlen : Zlength factors=count) (hbag : PrimeFactorBagPrefix a (Zlength a) factors)
    (hs : DuplicatePrefixState factors count found) : Spec a found := by
  rcases hbag with ⟨hb,hf,hcounts⟩
  rcases hs with ⟨hr,hbool,hdup⟩
  have hcounts' : ∀p, prime p → (factors.count p:Int)=((a.filter (zdividesb p)).length:Int) := by
    intro p hp
    have h := hcounts p hp
    simpa only [Zlength,Int.ofNat_eq_coe,Int.toNat_natCast,List.take_length] using h
  refine ⟨hbool,⟨?_,?_⟩⟩
  · intro hone
    rcases hdup.mp hone with ⟨fi,fj,hij,hj,he⟩
    let p := Znth fi factors 0
    have hp : prime p := hf.mem (znth_mem factors 0 fi (by omega))
    have hfactor : 2≤factors.count p := (two_occurrences_count_occ__duplicate_init_result Int inferInstance factors p 0).mp
      ⟨fi,fj,hij,by omega,rfl,he.symm⟩
    have hc := hcounts' p hp
    have hfilter : 2≤(a.filter (zdividesb p)).length := by omega
    rcases (filter_two_indices__duplicate_init_result (zdividesb p) a).mp hfilter with ⟨i,j,hr,hj,hiP,hjP⟩
    exact ⟨i,j,p,by omega,by omega,by omega,prime_ge_2 p hp,
      (zdividesb_true__duplicate_init_result _ _).mp hiP,(zdividesb_true__duplicate_init_result _ _).mp hjP⟩
  · rintro ⟨i,j,x,hi,hj,hne,hx,hxi,hxj⟩
    rcases prime_divisor_exists__duplicate_init_result x (by omega) with ⟨p,hp,hpx⟩
    have hpi := dvd_trans hpx hxi
    have hpj := dvd_trans hpx hxj
    have hfilter : 2≤(a.filter (zdividesb p)).length := by
      apply (filter_two_indices__duplicate_init_result (zdividesb p) a).mpr
      by_cases hij : i<j
      · exact ⟨i,j,by omega,hj.2,(zdividesb_true__duplicate_init_result _ _).mpr hpi,(zdividesb_true__duplicate_init_result _ _).mpr hpj⟩
      · exact ⟨j,i,by omega,hi.2,(zdividesb_true__duplicate_init_result _ _).mpr hpj,(zdividesb_true__duplicate_init_result _ _).mpr hpi⟩
    have hc := hcounts' p hp
    have hfactor : 2≤factors.count p := by omega
    rcases (two_occurrences_count_occ__duplicate_init_result Int inferInstance factors p 0).mpr hfactor with ⟨fi,fj,hij,hj,hfi,hfj⟩
    exact hdup.mpr ⟨fi,fj,hij,by omega,hfi.trans hfj.symm⟩

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P048_1771C_hossam_and_trainees_lib
