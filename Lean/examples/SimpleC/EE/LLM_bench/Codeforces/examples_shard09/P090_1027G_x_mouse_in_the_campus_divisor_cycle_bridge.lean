import Mathlib.Data.List.Perm.Basic
import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_gcd_stratum_transport
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide
namespace P090_DivisorCycleBridge

theorem positive_divisor_list_spec (m d : Int) :
    0 < m → (d ∈ positive_divisor_list m ↔ 0 < d ∧ d ≤ m ∧ d ∣ᶻ m) := by
  intro hm
  unfold positive_divisor_list
  rw [List.mem_filter]
  constructor
  · rintro ⟨hmem,hmod⟩
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hmem
    obtain ⟨j,hj,hjn⟩ := List.mem_range'.mp hn
    have hnpos : 0 < n := by omega
    have hnle : (n:Int) ≤ m := by omega
    exact ⟨by simp only [Int.ofNat_eq_coe]; omega,hnle,
      (Z.divide_iff_dvd _ _).mpr (Int.dvd_iff_fmod_eq_zero.mpr (by simpa using hmod))⟩
  · rintro ⟨hd,hdm,hdiv⟩
    refine ⟨List.mem_map.mpr ⟨d.toNat,?_,?_⟩,?_⟩
    · exact List.mem_range'.mpr ⟨d.toNat-1,by omega,by omega⟩
    · simpa using Int.toNat_of_nonneg (by omega : 0 ≤ d)
    · simpa using Int.fmod_eq_zero_of_dvd ((Z.divide_iff_dvd _ _).mp hdiv)

theorem positive_divisor_list_nodup (m : Int) : NoDup (positive_divisor_list m) := by
  apply List.Nodup.filter
  apply List.Nodup.map_on
  · intro a ha b hb hab
    exact Int.ofNat_inj.mp hab
  · exact List.nodup_range' _ (by omega)

theorem valid_factor_table_m_positive (m : Int) (pr pe : List Int) : ValidFactorTable m pr pe → 0 < m := by
  intro hv
  rw [hv.2.2.1]
  exact canonical_factor_product_positive pr pe (valid_factor_table_canonical m pr pe hv)

theorem valid_factor_table_divisor_permutation (m : Int) (pr pe : List Int) :
    ValidFactorTable m pr pe → List.Perm (enumerated_products pr pe) (positive_divisor_list m) := by
  intro hv
  have hm := valid_factor_table_m_positive m pr pe hv
  apply (List.perm_ext_iff_of_nodup (valid_factor_table_enumerated_products_nodup m pr pe hv) (positive_divisor_list_nodup m)).mpr
  intro d
  rw [valid_factor_table_exact_positive_divisor_bijection m pr pe d hv,positive_divisor_list_spec m d hm]
  exact ⟨fun ⟨hd,hdiv⟩ => ⟨hd,Int.le_of_dvd hm ((Z.divide_iff_dvd _ _).mp hdiv),hdiv⟩,fun ⟨hd,_,hdiv⟩ => ⟨hd,hdiv⟩⟩

theorem permutation_fold_right_add (xs ys : List Int) :
    List.Perm xs ys → xs.foldr Int.add 0 = ys.foldr Int.add 0 := by
  intro hp
  exact hp.foldr_eq' (fun a _ b _ c => by change b+(a+c)=a+(b+c); omega) 0

theorem permutation_filter_bool {A : Type} (keep : A→Bool) (xs ys : List A) :
    List.Perm xs ys → List.Perm (xs.filter keep) (ys.filter keep) := fun h => h.filter keep

theorem divisor_permutation_nonunit_cycle_sum (m x : Int) (pr pe : List Int) :
    ValidFactorTable m pr pe → NonUnitDivisorCycleSum pr pe x = ConcreteNonUnitDivisorCycleSum m x := by
  intro hv
  exact permutation_fold_right_add _ _ (((valid_factor_table_divisor_permutation m pr pe hv).filter (fun d => !(d==1))).map (CycleTerm x))

theorem walk_suffix_is_concrete_nonunit_divisor_cycle_sum (m x : Int) (pr pe : List Int) :
    ValidFactorTable m pr pe → WalkSuffix pr pe x 0 1 = ConcreteNonUnitDivisorCycleSum m x := by
  intro hv
  rw [walk_suffix_zero_is_nonunit_cycle_sum]
  exact divisor_permutation_nonunit_cycle_sum m x pr pe hv

theorem concrete_nonunit_divisor_cycle_budget (m x : Int) (pr pe : List Int) :
    ValidFactorTable m pr pe → WalkBudget m 0 (ConcreteNonUnitDivisorCycleSum m x) := by
  intro hv
  rw [← walk_suffix_is_concrete_nonunit_divisor_cycle_sum m x pr pe hv]
  exact valid_factor_table_initial_walk_budget m x pr pe hv

theorem room_zero_final_decomposition (m x : Int) (pr pe : List Int) :
    ValidFactorTable m pr pe → 1+WalkSuffix pr pe x 0 1 = RoomZeroCycleTotal m x := by
  intro hv
  unfold RoomZeroCycleTotal
  rw [walk_suffix_is_concrete_nonunit_divisor_cycle_sum m x pr pe hv]

theorem walk_suffix_is_concrete_full_divisor_cycle_sum (m x : Int) (pr pe : List Int) :
    ValidFactorTable m pr pe → WalkSuffix pr pe x 0 1 = ((positive_divisor_list m).map (CycleTerm x)).foldr Int.add 0 := by
  intro hv
  rw [walk_suffix_is_concrete_nonunit_divisor_cycle_sum m x pr pe hv]
  exact (fold_filter_cycle_term_one x (positive_divisor_list m)).symm

theorem room_zero_full_divisor_decomposition (m x : Int) (pr pe : List Int) :
    ValidFactorTable m pr pe → 1+WalkSuffix pr pe x 0 1 = 1+((positive_divisor_list m).map (CycleTerm x)).foldr Int.add 0 := by
  intro hv
  rw [walk_suffix_is_concrete_full_divisor_cycle_sum m x pr pe hv]
end P090_DivisorCycleBridge
export P090_DivisorCycleBridge (positive_divisor_list_spec positive_divisor_list_nodup valid_factor_table_m_positive
  valid_factor_table_divisor_permutation permutation_fold_right_add permutation_filter_bool divisor_permutation_nonunit_cycle_sum
  walk_suffix_is_concrete_nonunit_divisor_cycle_sum concrete_nonunit_divisor_cycle_budget room_zero_final_decomposition
  walk_suffix_is_concrete_full_divisor_cycle_sum room_zero_full_divisor_decomposition)
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
