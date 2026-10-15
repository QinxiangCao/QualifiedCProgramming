import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_global_orbit_bridge
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
open AUXLib AUXLib.Prime MaxMinLib
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo
local infix:50 " ∣ᶻ " => Z.divide
namespace P090_DivisorStrataKeys

theorem concrete_nonunit_divisor_spec (m divisor : Int) :
    0 < m → (divisor ∈ concrete_nonunit_divisors m ↔ 1 < divisor ∧ divisor ≤ m ∧ divisor ∣ᶻ m) := by
  intro hm
  unfold concrete_nonunit_divisors
  rw [List.mem_filter,positive_divisor_list_spec m divisor hm]
  constructor
  · rintro ⟨⟨hp,hle,hdiv⟩,hn⟩
    have hne : divisor ≠ 1 := by simpa using hn
    exact ⟨by omega,hle,hdiv⟩
  · rintro ⟨hp,hle,hdiv⟩
    have hne : divisor ≠ 1 := by omega
    exact ⟨⟨by omega,hle,hdiv⟩,by simp [hne]⟩

theorem concrete_nonunit_divisors_nodup (m : Int) : NoDup (concrete_nonunit_divisors m) :=
  List.Nodup.filter _ (positive_divisor_list_nodup m)

theorem positive_divisor_exact_product (m divisor : Int) :
    0 < divisor → divisor ∣ᶻ m → m = divisor*(m /ᶻ divisor) := by
  intro hd hdiv
  exact coq_div_factor m divisor (Int.fmod_eq_zero_of_dvd ((Z.divide_iff_dvd _ _).mp hdiv))

theorem positive_divisor_quotient_positive (m divisor : Int) :
    0 < m → 0 < divisor → divisor ∣ᶻ m → 0 < m /ᶻ divisor :=
  P090_GcdStratumTransport.positive_divisor_quotient_positive m divisor

theorem positive_divisor_quotient_injective (m left right : Int) :
    0 < m → 0 < left → 0 < right → left ∣ᶻ m → right ∣ᶻ m → m /ᶻ left = m /ᶻ right → left = right := by
  intro hm hl hr hld hrd hq
  have hlf := positive_divisor_exact_product m left hl hld
  have hrf := positive_divisor_exact_product m right hr hrd
  have hqp := positive_divisor_quotient_positive m left hm hl hld
  rw [← hq] at hrf
  nlinarith

theorem concrete_nonunit_key_positive (m divisor : Int) :
    0 < m → divisor ∈ concrete_nonunit_divisors m → 0 < m /ᶻ divisor := by
  intro hm hd
  obtain ⟨hp,hle,hdiv⟩ := (concrete_nonunit_divisor_spec m divisor hm).mp hd
  exact positive_divisor_quotient_positive m divisor hm (by omega) hdiv

theorem concrete_nonunit_key_nonzero (m divisor : Int) :
    0 < m → divisor ∈ concrete_nonunit_divisors m → m /ᶻ divisor ≠ 0 := by
  intro hm hd
  have hp := concrete_nonunit_key_positive m divisor hm hd
  omega

theorem concrete_nonunit_keys_pairwise_distinct (m left right : Int) :
    0 < m → left ∈ concrete_nonunit_divisors m → right ∈ concrete_nonunit_divisors m →
    m /ᶻ left = m /ᶻ right → left = right := by
  intro hm hl hr hq
  obtain ⟨hlp,_,hld⟩ := (concrete_nonunit_divisor_spec m left hm).mp hl
  obtain ⟨hrp,_,hrd⟩ := (concrete_nonunit_divisor_spec m right hm).mp hr
  exact positive_divisor_quotient_injective m left right hm (by omega) (by omega) hld hrd hq

theorem concrete_nonunit_key_distinct_from_zero_key (m divisor : Int) :
    0 < m → divisor ∈ concrete_nonunit_divisors m → m /ᶻ divisor ≠ m := by
  intro hm hd he
  obtain ⟨hp,_,hdiv⟩ := (concrete_nonunit_divisor_spec m divisor hm).mp hd
  have hf := positive_divisor_exact_product m divisor (by omega) hdiv
  rw [he] at hf
  nlinarith

theorem concrete_distinct_global_stratum_keys (m : Int) :
    0 < m → DistinctGlobalStratumKeys m (concrete_nonunit_divisors m) := by
  intro hm
  apply List.nodup_cons.mpr
  constructor
  · intro hmem
    obtain ⟨d,hd,he⟩ := List.mem_map.mp hmem
    exact concrete_nonunit_key_distinct_from_zero_key m d hm hd he
  · exact P090_OrbitQuotient.nodup_map_on _ _ (concrete_nonunit_divisors_nodup m)
      (fun l r hl hr => concrete_nonunit_keys_pairwise_distinct m l r hm hl hr)

theorem gcd_positive_with_positive_modulus (room m : Int) : 0 < m → 0 < Z.gcd room m := by
  intro hm
  have h := Int.gcd_pos_of_ne_zero_right room (by omega : m ≠ 0)
  simpa [Z.gcd] using (Int.ofNat_pos.mpr h)

theorem gcd_quotient_is_positive_divisor (room m : Int) :
    0 < m → let gcd_value := Z.gcd room m; let divisor := m /ᶻ gcd_value
    0 < divisor ∧ divisor ≤ m ∧ divisor ∣ᶻ m ∧ m /ᶻ divisor = gcd_value := by
  intro hm
  dsimp only
  have hgp := gcd_positive_with_positive_modulus room m hm
  have hgd : Z.gcd room m ∣ᶻ m := (Z.divide_iff_dvd _ _).mpr (Int.gcd_dvd_right room m)
  have hdp := positive_divisor_quotient_positive m (Z.gcd room m) hm hgp hgd
  have hf := positive_divisor_exact_product m (Z.gcd room m) hgp hgd
  have hdd : (m /ᶻ Z.gcd room m) ∣ᶻ m := ⟨Z.gcd room m,hf⟩
  refine ⟨hdp,Int.le_of_dvd hm ((Z.divide_iff_dvd _ _).mp hdd),hdd,?_⟩
  conv_lhs => arg 1; rw [hf]
  exact Int.mul_fdiv_cancel _ (by omega)

theorem gcd_equal_modulus_room_zero (room m : Int) :
    0 < m → (0 ≤ room ∧ room < m) → Z.gcd room m = m → room = 0 := by
  intro hm hr hg
  have hd : m ∣ room := by rw [← hg]; exact Int.gcd_dvd_left room m
  have hmod := Int.fmod_eq_zero_of_dvd hd
  rwa [Int.fmod_eq_of_lt hr.1 hr.2] at hmod

theorem gcd_quotient_nonunit_when_not_zero_stratum (room m : Int) :
    0 < m → Z.gcd room m ≠ m → 1 < m /ᶻ Z.gcd room m := by
  intro hm hn
  have h := gcd_quotient_is_positive_divisor room m hm
  have hnot : m /ᶻ Z.gcd room m ≠ 1 := by
    intro h1
    have hh := h.2.2.2
    rw [h1] at hh
    have he : m = Z.gcd room m := by simpa [Z.div] using hh
    exact hn he.symm
  omega

theorem concrete_divisor_strata_classify (m : Int) :
    0 < m → DivisorStrataClassify m (concrete_nonunit_divisors m) := by
  intro hm room hr
  by_cases hz : Z.gcd room m = m
  · exact Or.inl hz
  · obtain ⟨hdp,hdle,hdiv,hq⟩ := gcd_quotient_is_positive_divisor room m hm
    exact Or.inr ⟨m /ᶻ Z.gcd room m,(concrete_nonunit_divisor_spec m _ hm).mpr
      ⟨gcd_quotient_nonunit_when_not_zero_stratum room m hm hz,hdle,hdiv⟩,hq.symm⟩

theorem concrete_nonunit_stratum_divisor_unique (m room left right : Int) :
    0 < m → left ∈ concrete_nonunit_divisors m → right ∈ concrete_nonunit_divisors m →
    Z.gcd room m = m /ᶻ left → Z.gcd room m = m /ᶻ right → left = right := by
  intro hm hl hr hgl hgr
  exact concrete_nonunit_keys_pairwise_distinct m left right hm hl hr (hgl.symm.trans hgr)

theorem concrete_divisor_strata_key_premises (m : Int) :
    0 < m → let divisors := (positive_divisor_list m).filter (fun d => !(d==1))
    DistinctGlobalStratumKeys m divisors ∧ DivisorStrataClassify m divisors := by
  intro hm
  exact ⟨concrete_distinct_global_stratum_keys m hm,concrete_divisor_strata_classify m hm⟩
end P090_DivisorStrataKeys
-- Both source modules publish the same quotient-positivity theorem. Preserve both qualified APIs;
-- the outer namespace already forwards the statement from P090_GcdStratumTransport.
export P090_DivisorStrataKeys (concrete_nonunit_divisor_spec concrete_nonunit_divisors_nodup positive_divisor_exact_product
  positive_divisor_quotient_injective concrete_nonunit_key_positive concrete_nonunit_key_nonzero
  concrete_nonunit_keys_pairwise_distinct concrete_nonunit_key_distinct_from_zero_key concrete_distinct_global_stratum_keys
  gcd_positive_with_positive_modulus gcd_quotient_is_positive_divisor gcd_equal_modulus_room_zero
  gcd_quotient_nonunit_when_not_zero_stratum concrete_divisor_strata_classify concrete_nonunit_stratum_divisor_unique
  concrete_divisor_strata_key_premises)
end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P090_1027G_x_mouse_in_the_campus_lib
