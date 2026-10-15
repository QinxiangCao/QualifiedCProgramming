import AUXLib.NumberTheory
import SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_lib

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_lib
open AUXLib

def CRTLCMPrefix (moduli : List Int) (count : Int) : Int :=
  (moduli.take count.toNat).foldl Z.lcm 1

def CRTCongruent (value residue modulus : Int) : Prop :=
  ∃ quotient, value = residue + modulus * quotient

def CRTAllCongruences (residues moduli : List Int) (count value : Int) : Prop :=
  ∀ index, (0 ≤ index ∧ index < count) →
    CRTCongruent value (Znth index residues 0) (Znth index moduli 0)

def ExtendedCRTInputs (residues moduli : List Int) (n : Int) : Prop :=
  1 ≤ n ∧ Zlength residues = n ∧ Zlength moduli = n ∧
  ∀ index, (0 ≤ index ∧ index < n) →
    (0 < Znth index moduli 0 ∧ Znth index moduli 0 ≤ 2147483647) ∧
    (0 ≤ Znth index residues 0 ∧ Znth index residues 0 < Znth index moduli 0)

def ExtendedCRTSystemCompatible (residues moduli : List Int) (n : Int) : Prop :=
  ∃ solution, CRTAllCongruences residues moduli n solution

def ExtendedCRTIntSafe (moduli : List Int) (n : Int) : Prop :=
  (∀ count, (1 ≤ count ∧ count ≤ n) → 0 < CRTLCMPrefix moduli count ∧ CRTLCMPrefix moduli count ≤ 2147483647) ∧
  (∀ index, (1 ≤ index ∧ index < n) →
    2 * Z.quot (Znth index moduli 0) (Z.gcd (CRTLCMPrefix moduli index) (Znth index moduli 0)) ≤ 2147483647)

def ExtendedCRTSystemResult (residues moduli : List Int) (n result combined_modulus : Int) : Prop :=
  combined_modulus = CRTLCMPrefix moduli n ∧ (0 ≤ result ∧ result < combined_modulus) ∧
  CRTAllCongruences residues moduli n result

def CRTPrefixMeaning (residues moduli : List Int) (count answer combined_modulus : Int) : Prop :=
  combined_modulus = CRTLCMPrefix moduli count ∧ CRTAllCongruences residues moduli count answer

def CRTReducedMergeEquation (current_answer current_modulus next_residue next_modulus multiplier : Int) : Prop :=
  let gcd := Z.gcd current_modulus next_modulus
  ∃ adjustment, Z.div current_modulus gcd * multiplier + Z.div next_modulus gcd * adjustment =
    Z.div (next_residue-current_answer) gcd

theorem extended_crt_index_bounds__machine_bounds (residues moduli : List Int) (n index : Int)
    (hi : ExtendedCRTInputs residues moduli n) (hx : 0 ≤ index ∧ index < n) :
    (0 < Znth index moduli 0 ∧ Znth index moduli 0 ≤ 2147483647) ∧
    (0 ≤ Znth index residues 0 ∧ Znth index residues 0 < Znth index moduli 0) := hi.2.2.2 index hx

theorem positive_gcd_quotient_bounds__machine_bounds (current_modulus modulus gcd : Int)
    (hm : 0 < modulus ∧ modulus ≤ 2147483647) (hg : gcd = Z.gcd current_modulus modulus)
    (hgp : 0 < gcd) : 0 < Z.quot modulus gcd ∧ Z.quot modulus gcd ≤ 2147483647 := by
  obtain ⟨q, hq⟩ : Z.divide gcd modulus := by rw [hg]; exact Z.gcd_divide_r current_modulus modulus
  have hqp : 0 < q := by
    exact Int.pos_of_mul_pos_left (show 0 < q*gcd by omega) hgp
  have hle := Int.mul_le_mul_of_nonneg_left (show 1 ≤ gcd by omega) (Int.le_of_lt hqp)
  rw [hq, Z.quot_mul q gcd (by omega)]
  simp only [Int.mul_one] at hle
  omega

theorem signed_difference_division_bounds__machine_bounds (residue answer divisor : Int)
    (hr : 0 ≤ residue ∧ residue ≤ 2147483647) (ha : 0 ≤ answer ∧ answer ≤ 2147483647)
    (hd : 0 < divisor) : -2147483648 < Z.quot (residue-answer) divisor ∧
    Z.quot (residue-answer) divisor ≤ 2147483647 := by
  have hl := Int.mul_le_mul_of_nonpos_right (show 1 ≤ divisor by omega) (show (-2147483647 : Int) ≤ 0 by decide)
  have hu := Int.mul_le_mul_of_nonneg_right (show 1 ≤ divisor by omega) (show (0 : Int) ≤ 2147483647 by decide)
  have hlow := Z.quot_le_lower_bound (residue-answer) divisor (-2147483647) hd (by omega)
  have hupp := Z.quot_le_upper_bound (residue-answer) divisor 2147483647 hd (by omega)
  omega

theorem bounded_merge_arithmetic__machine_bounds (answer lcm multiplier reduced_modulus : Int)
    (ha : 0 ≤ answer ∧ answer < lcm) (hm : 0 ≤ multiplier ∧ multiplier < reduced_modulus)
    (hl : 0 < lcm) (hp : lcm*reduced_modulus ≤ 2147483647) :
    multiplier*lcm ≤ 2147483647 ∧ -2147483648 ≤ multiplier*lcm ∧
    answer+multiplier*lcm ≤ 2147483647 ∧ -2147483648 ≤ answer+multiplier*lcm := by
  have hn := Int.mul_nonneg hm.1 (Int.le_of_lt hl)
  have hu := Int.mul_le_mul_of_nonneg_right (show multiplier+1 ≤ reduced_modulus by omega) (Int.le_of_lt hl)
  simp only [Int.add_mul, Int.one_mul] at hu
  rw [Int.mul_comm reduced_modulus lcm] at hu
  omega

theorem crt_prefix_meaning_one__prefix_boundaries (residues moduli : List Int) (n : Int)
    (hi : ExtendedCRTInputs residues moduli n) (hn : 1 ≤ n) :
    CRTPrefixMeaning residues moduli 1 (Znth 0 residues 0) (Znth 0 moduli 0) := by
  have hrlen := hi.2.1
  have hmlen := hi.2.2.1
  have hz := hi.2.2.2 0 (by omega)
  cases residues with
  | nil => simp [Zlength] at hrlen; omega
  | cons r rs =>
    cases moduli with
    | nil => simp [Zlength] at hmlen; omega
    | cons m ms =>
      simp only [Znth, Int.toNat_zero, List.getD_cons_zero] at hz ⊢
      refine ⟨?_, ?_⟩
      · change m = Z.lcm 1 m
        exact (Z.lcm_1_l_nonneg m (by omega)).symm
      · intro index hx
        have hidx : index = 0 := by omega
        subst index
        exact ⟨0, by simp [Znth]⟩

theorem crt_prefix_meaning_to_result__prefix_boundaries (residues moduli : List Int)
    (n i answer combined_modulus : Int) (he : i = n) (ha : 0 ≤ answer ∧ answer < combined_modulus)
    (hp : CRTPrefixMeaning residues moduli i answer combined_modulus) :
    ExtendedCRTSystemResult residues moduli n answer combined_modulus := by
  subst i
  exact ⟨hp.1, ha, hp.2⟩

theorem quot_div_of_divide_pos__merge_transition (numerator denominator : Int)
    (hd : 0 < denominator) (hdiv : Z.divide denominator numerator) :
    Z.quot numerator denominator = Z.div numerator denominator := by
  obtain ⟨q, hq⟩ := hdiv
  rw [hq, Z.quot_mul q denominator (by omega)]
  exact (Int.mul_fdiv_cancel q (by omega)).symm

theorem firstn_succ_nth__merge_transition {A : Type} (l : List A) (n : Nat) (default : A)
    (hn : n < l.length) : l.take (n+1) = l.take n ++ [l.getD n default] := by
  rw [List.take_succ_eq_append_getElem hn]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hn]

theorem fold_left_lcm_all_divide__merge_transition (values : List Int) (accumulator difference : Int)
    (ha : Z.divide accumulator difference)
    (hall : ∀ value, value ∈ values → Z.divide value difference) :
    Z.divide (values.foldl Z.lcm accumulator) difference := by
  induction values generalizing accumulator with
  | nil => exact ha
  | cons v vs ih =>
    apply ih (Z.lcm accumulator v) (Z.lcm_least accumulator v difference ha (hall v (by simp)))
    intro other ho
    exact hall other (List.mem_cons_of_mem _ ho)

theorem fold_left_lcm_preserves_divide__merge_transition (values : List Int) (accumulator divisor : Int)
    (hd : Z.divide divisor accumulator) : Z.divide divisor (values.foldl Z.lcm accumulator) := by
  induction values generalizing accumulator with
  | nil => exact hd
  | cons v vs ih =>
    apply ih
    apply (Z.divide_iff_dvd _ _).mpr
    exact Int.dvd_trans ((Z.divide_iff_dvd _ _).mp hd) ((Z.divide_iff_dvd _ _).mp (Z.divide_lcm_l accumulator v))

theorem fold_left_lcm_in_divides__merge_transition (values : List Int) (accumulator value : Int)
    (hm : value ∈ values) : Z.divide value (values.foldl Z.lcm accumulator) := by
  induction values generalizing accumulator with
  | nil => simp at hm
  | cons v vs ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact fold_left_lcm_preserves_divide__merge_transition vs (Z.lcm accumulator value) value (Z.divide_lcm_r accumulator value)
    · exact ih (Z.lcm accumulator v) hm

theorem crt_lcm_prefix_multiple__merge_transition (moduli : List Int) (count index : Int)
    (hi : 0 ≤ index ∧ index < count) (hc : count ≤ Zlength moduli) :
    Z.divide (Znth index moduli 0) (CRTLCMPrefix moduli count) := by
  apply fold_left_lcm_in_divides__merge_transition
  apply List.mem_take_iff_getElem.mpr
  have hlen : index.toNat < moduli.length := by simp only [Zlength, Int.ofNat_eq_coe] at hc; omega
  refine ⟨index.toNat, by simp only [Zlength, Int.ofNat_eq_coe] at hc; omega, ?_⟩
  simp [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]

theorem crt_prefix_solution_congruent_lcm__merge_transition (residues moduli : List Int)
    (count answer combined solution : Int) (hc : 0 ≤ count)
    (hp : CRTPrefixMeaning residues moduli count answer combined)
    (hs : CRTAllCongruences residues moduli count solution) : Z.divide combined (solution-answer) := by
  rw [hp.1]
  apply fold_left_lcm_all_divide__merge_transition
  · exact ⟨solution-answer, by omega⟩
  · intro modulus hm
    obtain ⟨k, hk, he⟩ := List.mem_take_iff_getElem.mp hm
    have hkr : 0 ≤ (k : Int) ∧ (k : Int) < count := by omega
    have hmod : Znth (k : Int) moduli 0 = modulus := by
      simpa [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show k < moduli.length by omega)] using he
    obtain ⟨qa, ha⟩ := hp.2 (k : Int) hkr
    obtain ⟨qs, hsol⟩ := hs (k : Int) hkr
    rw [hmod] at ha hsol
    exact ⟨qs-qa, by grind⟩

theorem crt_merge_difference_divisible__merge_transition (residues moduli : List Int)
    (n index answer combined : Int) (hc : ExtendedCRTSystemCompatible residues moduli n)
    (hp : CRTPrefixMeaning residues moduli index answer combined) (hi : 0 ≤ index ∧ index < n) :
    Z.divide (Z.gcd combined (Znth index moduli 0)) (Znth index residues 0-answer) := by
  obtain ⟨solution, hs⟩ := hc
  have hsp : CRTAllCongruences residues moduli index solution := by
    intro old ho
    exact hs old (by omega)
  obtain ⟨qp, hqp⟩ := crt_prefix_solution_congruent_lcm__merge_transition residues moduli index answer combined solution hi.1 hp hsp
  obtain ⟨qn, hqn⟩ := hs index hi
  obtain ⟨qc, hqc⟩ := Z.gcd_divide_l combined (Znth index moduli 0)
  obtain ⟨qm, hqm⟩ := Z.gcd_divide_r combined (Znth index moduli 0)
  exact ⟨qc*qp-qm*qn, by grind⟩

theorem reduced_merge_equation_from_bezout__merge_transition
    (current_answer current_modulus next_residue next_modulus gcd x_coefficient y_coefficient normalized quotient : Int)
    (hg : gcd = Z.gcd current_modulus next_modulus) (hgp : 0 < gcd)
    (hd : Z.divide gcd (next_residue-current_answer))
    (hb : current_modulus*x_coefficient+next_modulus*y_coefficient = gcd)
    (hn : x_coefficient*Z.div (next_residue-current_answer) gcd = normalized+Z.div next_modulus gcd*quotient) :
    CRTReducedMergeEquation current_answer current_modulus next_residue next_modulus normalized := by
  obtain ⟨cq, hc⟩ : Z.divide gcd current_modulus := by rw [hg]; exact Z.gcd_divide_l current_modulus next_modulus
  obtain ⟨nq, hnext⟩ : Z.divide gcd next_modulus := by rw [hg]; exact Z.gcd_divide_r current_modulus next_modulus
  obtain ⟨dq, hdiff⟩ := hd
  have hcd : Z.div current_modulus gcd = cq := by rw [hc]; exact Int.mul_fdiv_cancel cq (by omega)
  have hnd : Z.div next_modulus gcd = nq := by rw [hnext]; exact Int.mul_fdiv_cancel nq (by omega)
  have hdd : Z.div (next_residue-current_answer) gcd = dq := by rw [hdiff]; exact Int.mul_fdiv_cancel dq (by omega)
  have hunit : cq*x_coefficient+nq*y_coefficient = 1 := by
    apply Int.eq_of_mul_eq_mul_right (a := gcd) (by omega)
    grind
  unfold CRTReducedMergeEquation
  rw [← hg]
  refine ⟨y_coefficient*dq+cq*quotient, ?_⟩
  rw [hcd, hnd, hdd]
  rw [hnd, hdd] at hn
  grind

theorem crt_lcm_prefix_step__merge_transition (residues moduli : List Int)
    (n index answer combined gcd reduced : Int) (hi : ExtendedCRTInputs residues moduli n)
    (hx : 0 ≤ index ∧ index < n) (hp : 0 < combined)
    (hprefix : CRTPrefixMeaning residues moduli index answer combined)
    (hg : gcd = Z.gcd combined (Znth index moduli 0)) (hgp : 0 < gcd)
    (hr : reduced = Z.div (Znth index moduli 0) gcd) :
    CRTLCMPrefix moduli (index+1) = combined*reduced := by
  have hlen := hi.2.2.1
  have hm := (hi.2.2.2 index hx).1.1
  have hnat : index.toNat < moduli.length := by simp only [Zlength, Int.ofNat_eq_coe] at hlen; omega
  unfold CRTLCMPrefix
  rw [show (index+1).toNat = index.toNat+1 by omega,
    firstn_succ_nth__merge_transition moduli index.toNat 0 hnat, List.foldl_append]
  change Z.lcm (CRTLCMPrefix moduli index) (Znth index moduli 0) = combined*reduced
  rw [← hprefix.1]
  unfold Z.lcm
  rw [← hg, ← hr]
  apply (Z.abs_eq_iff _).mpr
  apply Int.mul_nonneg (Int.le_of_lt hp)
  rw [hr]
  exact Int.fdiv_nonneg (Int.le_of_lt hm) (Int.le_of_lt hgp)

theorem crt_prefix_meaning_merge__merge_transition (residues moduli : List Int)
    (n index answer combined gcd reduced multiplier : Int)
    (hi : ExtendedCRTInputs residues moduli n) (hc : ExtendedCRTSystemCompatible residues moduli n)
    (hx : 0 ≤ index ∧ index < n) (hp : 0 < combined)
    (hprefix : CRTPrefixMeaning residues moduli index answer combined)
    (hg : gcd = Z.gcd combined (Znth index moduli 0)) (hgp : 0 < gcd)
    (hr : reduced = Z.div (Znth index moduli 0) gcd) (hm : 0 ≤ multiplier ∧ multiplier < reduced)
    (hmerge : CRTReducedMergeEquation answer combined (Znth index residues 0) (Znth index moduli 0) multiplier) :
    CRTPrefixMeaning residues moduli (index+1) (answer+multiplier*combined) (combined*reduced) := by
  refine ⟨(crt_lcm_prefix_step__merge_transition residues moduli n index answer combined gcd reduced hi hx hp hprefix hg hgp hr).symm, ?_⟩
  intro old ho
  by_cases hold : old < index
  · obtain ⟨qo, hqo⟩ := hprefix.2 old (by omega)
    obtain ⟨qcomb, hcomb⟩ := crt_lcm_prefix_multiple__merge_transition moduli index old (by omega) (by have := hi.2.2.1; omega)
    have hpre := hprefix.1
    exact ⟨qo+multiplier*qcomb, by grind⟩
  · have heq : old = index := by omega
    subst old
    obtain ⟨cq, hcq⟩ : Z.divide gcd combined := by rw [hg]; exact Z.gcd_divide_l combined (Znth index moduli 0)
    obtain ⟨mq, hmq⟩ : Z.divide gcd (Znth index moduli 0) := by rw [hg]; exact Z.gcd_divide_r combined (Znth index moduli 0)
    obtain ⟨dq, hdq⟩ : Z.divide gcd (Znth index residues 0-answer) := by
      rw [hg]; exact crt_merge_difference_divisible__merge_transition residues moduli n index answer combined hc hprefix hx
    have hcd : Z.div combined gcd = cq := by rw [hcq]; exact Int.mul_fdiv_cancel cq (by omega)
    have hmd : Z.div (Znth index moduli 0) gcd = mq := by rw [hmq]; exact Int.mul_fdiv_cancel mq (by omega)
    have hdd : Z.div (Znth index residues 0-answer) gcd = dq := by rw [hdq]; exact Int.mul_fdiv_cancel dq (by omega)
    unfold CRTReducedMergeEquation at hmerge
    rw [← hg] at hmerge
    obtain ⟨adjustment, ha⟩ := hmerge
    rw [hcd, hmd, hdd] at ha
    exact ⟨-adjustment, by grind⟩

theorem bezout_coefficient_strict__gcd_branch_setup (lcm modulus gcd x y : Int)
    (hm : 0 < modulus) (hg : gcd = Z.gcd lcm modulus) (hgp : 0 < gcd)
    (hn : Z.rem lcm modulus ≠ 0) (hb : lcm*x+modulus*y = gcd)
    (ha : Z.abs x ≤ Z.quot modulus gcd) : -Z.quot modulus gcd < x ∧ x < Z.quot modulus gcd := by
  obtain ⟨lq, hlq⟩ : Z.divide gcd lcm := by rw [hg]; exact Z.gcd_divide_l lcm modulus
  obtain ⟨mq, hmq⟩ : Z.divide gcd modulus := by rw [hg]; exact Z.gcd_divide_r lcm modulus
  have hquot : Z.quot modulus gcd = mq := by rw [hmq, Z.quot_mul mq gcd (by omega)]
  have hmqpos : 0 < mq := Int.pos_of_mul_pos_left (show 0 < mq*gcd by omega) hgp
  have hu : lq*x+mq*y = 1 := by
    apply Int.eq_of_mul_eq_mul_right (a := gcd) (by omega)
    grind
  have hmne : mq ≠ 1 := by
    intro he
    apply hn
    have hmg : modulus = gcd := by simpa only [he, Int.one_mul] using hmq
    rw [hmg]
    exact (Z.rem_divide lcm gcd (by omega)).mpr ⟨lq, hlq⟩
  rw [hquot] at ha ⊢
  have hab := (Z.abs_le_iff x mq).mp ha
  have hneg : x ≠ -mq := by
    intro he
    have hd : mq ∣ 1 := ⟨y-lq, by grind⟩
    have := Int.le_of_dvd (show (0 : Int) < 1 by decide) hd
    omega
  have hpos : x ≠ mq := by
    intro he
    have hd : mq ∣ 1 := ⟨lq+y, by grind⟩
    have := Int.le_of_dvd (show (0 : Int) < 1 by decide) hd
    omega
  omega

end SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_lib
namespace SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem
export SimpleC.EE.LLM_bench.Algorithms.modular_mul.modular_mul_lib (ModularMul)
export extended_chinese_remainder_theorem_lib (CRTLCMPrefix CRTCongruent CRTAllCongruences ExtendedCRTInputs
  ExtendedCRTSystemCompatible ExtendedCRTIntSafe ExtendedCRTSystemResult CRTPrefixMeaning CRTReducedMergeEquation)
end SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem
