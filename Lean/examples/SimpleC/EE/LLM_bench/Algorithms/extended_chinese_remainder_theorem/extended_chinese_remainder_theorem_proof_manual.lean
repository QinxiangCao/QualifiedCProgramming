import SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_goal
import SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open extended_chinese_remainder_theorem_goal extended_chinese_remainder_theorem_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

-- Use the original generated residual branch and SL preprocessing. Goal_apply
-- requires explicit arguments in Lean; pure split results also need the
-- dump_spatial_left bridge from entailments to propositions.

private theorem nth_property (P : Int → Prop) (xs : List Int) (h : Forall P xs)
    (i : Int) (hi : 0 ≤ i ∧ i < Zlength xs) : P (Znth i xs 0) := by
  have hin : i.toNat < xs.length := by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega
  have hp := h.mem (List.getElem_mem (l := xs) hin)
  simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hin, Option.getD_some] using hp

private theorem inputs_from_annotation (rs ms : List Int) (n : Int)
    (hn : 1 ≤ n) (hr : Zlength rs = n) (hm : Zlength ms = n)
    (hpos : Forall (fun z => 0 < z) ms) (hmax : Forall (fun z => z ≤ INT_MAX) ms)
    (hrpos : Forall (fun z => 0 ≤ z) rs) (hlt : Forall2 (fun r m => r < m) rs ms) :
    ExtendedCRTInputs rs ms n := by
  refine ⟨hn, hr, hm, ?_⟩
  intro i hi
  have hri : 0 ≤ i ∧ i < Zlength rs := by omega
  have hmi : 0 ≤ i ∧ i < Zlength ms := by omega
  refine ⟨⟨nth_property _ ms hpos i hmi, nth_property _ ms hmax i hmi⟩,
    nth_property _ rs hrpos i hri, ?_⟩
  have hnat : i.toNat < rs.length := by simp only [Zlength, Int.ofNat_eq_coe] at hri; omega
  exact ((AUXLib.Forall2_nth_iff Int Int (fun r m => r < m) rs ms 0 0).mp hlt).2 i.toNat hnat

private theorem positive_lcm (a b : Int) (ha : 0 < a) (hb : 0 < b) : 0 < Z.lcm a b := by
  have hg : 0 < Z.gcd a b := by
    have hp := Int.gcd_pos_of_ne_zero_left b (by omega : a ≠ 0)
    simpa only [Z.gcd, Int.ofNat_eq_coe, Int.natCast_pos] using hp
  have hd := Z.gcd_divide_r a b
  obtain ⟨q, hq⟩ := hd
  have hqpos : 0 < q := Int.pos_of_mul_pos_left (show 0 < q * Z.gcd a b by omega) hg
  have hdiv := quot_div_of_divide_pos__merge_transition b (Z.gcd a b) hg ⟨q,hq⟩
  unfold Z.lcm
  rw [← hdiv]
  have hquot : Z.quot b (Z.gcd a b) = q := by
    conv_lhs => arg 1; rw [hq]
    exact Z.quot_mul q _ (by omega)
  rw [hquot]
  have hp := Int.mul_pos ha hqpos
  rw [(Z.abs_eq_iff _).mpr (by omega)]
  exact hp

private theorem fold_lcm_positive (xs : List Int) (h : Forall (fun z => 0 < z) xs)
    (a : Int) (ha : 0 < a) : 0 < xs.foldl Z.lcm a := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    change 0 < xs.foldl Z.lcm (Z.lcm a x)
    cases h with
    | cons hx hxs => exact ih hxs _ (positive_lcm a x ha hx)

private theorem int_safe_from_annotation (ms : List Int) (n : Int)
    (hpos : Forall (fun z => 0 < z) ms)
    (hb : ∀ count, 1 ≤ count ∧ count ≤ n → CRTLCMPrefix ms count ≤ INT_MAX)
    (hq : ∀ index, 1 ≤ index ∧ index < n →
      2 * Z.quot (Znth index ms 0) (Z.gcd (CRTLCMPrefix ms index) (Znth index ms 0)) ≤ INT_MAX) :
    ExtendedCRTIntSafe ms n := by
  refine ⟨?_, hq⟩
  intro count hc
  refine ⟨?_, hb count hc⟩
  apply fold_lcm_positive _ _ 1 (by decide)
  apply Forall.iff_forall_mem.mpr
  intro z hz
  exact hpos.mem (List.mem_of_mem_take hz)



theorem proof_of_extended_chinese_remainder_theorem_entail_wit_1 : extended_chinese_remainder_theorem_entail_wit_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_1
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 0 ⟨by omega, by omega⟩
  have hp := crt_prefix_meaning_one__prefix_boundaries residue_values modulus_values n_pre hInputs (by omega)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | (solve | simp only [INT_MAX, INT_MIN] at *; omega) | (solve | nlinarith) | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_2_1 : extended_chinese_remainder_theorem_entail_wit_2_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_2_1
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval := by assumption
  have hp : CRTPrefixMeaning residue_values modulus_values i answer lcm := by assumption
  have hc : ExtendedCRTSystemCompatible residue_values modulus_values n_pre := by assumption
  have hm : Z.divide retval (Znth i modulus_values 0) := by rw [hg]; exact Z.gcd_divide_r _ _
  have hmod := quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) retval hgp hm
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 hg hgp
  have hstep := crt_lcm_prefix_step__merge_transition residue_values modulus_values n_pre i answer lcm retval (Z.quot (Znth i modulus_values 0) retval) hInputs ⟨by omega, by omega⟩ (by omega) hp hg hgp hmod
  have hprod := (hSafe.1 (i+1) ⟨by omega, by omega⟩).2
  rw [hstep] at hprod
  have hd : Z.divide retval (Znth i residue_values 0-answer) := by
    rw [hg]
    exact crt_merge_difference_divisible__merge_transition residue_values modulus_values n_pre i answer lcm hc hp ⟨by omega, by omega⟩
  have hdiff := quot_div_of_divide_pos__merge_transition (Znth i residue_values 0-answer) retval hgp hd
  have hmul_preserved := PreH2
  obtain ⟨hbound, q, hq⟩ := PreH2
  rw [hdiff] at hq
  have heq : CRTReducedMergeEquation answer lcm (Znth i residue_values 0) (Znth i modulus_values 0) (retval_2 + Z.quot (Znth i modulus_values 0) retval) := by
    apply reduced_merge_equation_from_bezout__merge_transition answer lcm (Znth i residue_values 0) (Znth i modulus_values 0) retval x_v y_v (retval_2 + Z.quot (Znth i modulus_values 0) retval) (q-1) hg hgp hd (by assumption)
    rw [← hmod]
    nlinarith [hq]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | (solve | simp only [INT_MAX, INT_MIN] at *; omega) | (solve | nlinarith) | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_2_2 : extended_chinese_remainder_theorem_entail_wit_2_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_2_2
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v_2 retval retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval := by assumption
  have hp : CRTPrefixMeaning residue_values modulus_values i answer lcm := by assumption
  have hc : ExtendedCRTSystemCompatible residue_values modulus_values n_pre := by assumption
  have hm : Z.divide retval (Znth i modulus_values 0) := by rw [hg]; exact Z.gcd_divide_r _ _
  have hmod := quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) retval hgp hm
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 hg hgp
  have hstep := crt_lcm_prefix_step__merge_transition residue_values modulus_values n_pre i answer lcm retval (Z.quot (Znth i modulus_values 0) retval) hInputs ⟨by omega, by omega⟩ (by omega) hp hg hgp hmod
  have hprod := (hSafe.1 (i+1) ⟨by omega, by omega⟩).2
  rw [hstep] at hprod
  have hd : Z.divide retval (Znth i residue_values 0-answer) := by
    rw [hg]
    exact crt_merge_difference_divisible__merge_transition residue_values modulus_values n_pre i answer lcm hc hp ⟨by omega, by omega⟩
  have hdiff := quot_div_of_divide_pos__merge_transition (Znth i residue_values 0-answer) retval hgp hd
  have hmul_preserved := PreH2
  obtain ⟨hbound, q, hq⟩ := PreH2
  rw [hdiff] at hq
  have heq : CRTReducedMergeEquation answer lcm (Znth i residue_values 0) (Znth i modulus_values 0) (retval_3 + Z.quot (Znth i modulus_values 0) retval) := by
    apply reduced_merge_equation_from_bezout__merge_transition answer lcm (Znth i residue_values 0) (Znth i modulus_values 0) retval x_v_2 y_v (retval_3 + Z.quot (Znth i modulus_values 0) retval) (q-1) hg hgp hd (by assumption)
    rw [← hmod]
    nlinarith [hq]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | (solve | simp only [INT_MAX, INT_MIN] at *; omega) | (solve | nlinarith) | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_2_3 : extended_chinese_remainder_theorem_entail_wit_2_3 := by
  unfold extended_chinese_remainder_theorem_entail_wit_2_3
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval := by assumption
  have hp : CRTPrefixMeaning residue_values modulus_values i answer lcm := by assumption
  have hc : ExtendedCRTSystemCompatible residue_values modulus_values n_pre := by assumption
  have hm : Z.divide retval (Znth i modulus_values 0) := by rw [hg]; exact Z.gcd_divide_r _ _
  have hmod := quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) retval hgp hm
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 hg hgp
  have hstep := crt_lcm_prefix_step__merge_transition residue_values modulus_values n_pre i answer lcm retval (Z.quot (Znth i modulus_values 0) retval) hInputs ⟨by omega, by omega⟩ (by omega) hp hg hgp hmod
  have hprod := (hSafe.1 (i+1) ⟨by omega, by omega⟩).2
  rw [hstep] at hprod
  have hd : Z.divide retval (Znth i residue_values 0-answer) := by
    rw [hg]
    exact crt_merge_difference_divisible__merge_transition residue_values modulus_values n_pre i answer lcm hc hp ⟨by omega, by omega⟩
  have hdiff := quot_div_of_divide_pos__merge_transition (Znth i residue_values 0-answer) retval hgp hd
  have hmul_preserved := PreH2
  obtain ⟨hbound, q, hq⟩ := PreH2
  rw [hdiff] at hq
  have heq : CRTReducedMergeEquation answer lcm (Znth i residue_values 0) (Znth i modulus_values 0) retval_2 := by
    apply reduced_merge_equation_from_bezout__merge_transition answer lcm (Znth i residue_values 0) (Znth i modulus_values 0) retval x_v y_v retval_2 q hg hgp hd (by assumption)
    rw [← hmod]
    nlinarith [hq]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | (solve | simp only [INT_MAX, INT_MIN] at *; omega) | (solve | nlinarith) | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_2_4 : extended_chinese_remainder_theorem_entail_wit_2_4 := by
  unfold extended_chinese_remainder_theorem_entail_wit_2_4
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v_2 retval retval_3 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval := by assumption
  have hp : CRTPrefixMeaning residue_values modulus_values i answer lcm := by assumption
  have hc : ExtendedCRTSystemCompatible residue_values modulus_values n_pre := by assumption
  have hm : Z.divide retval (Znth i modulus_values 0) := by rw [hg]; exact Z.gcd_divide_r _ _
  have hmod := quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) retval hgp hm
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 hg hgp
  have hstep := crt_lcm_prefix_step__merge_transition residue_values modulus_values n_pre i answer lcm retval (Z.quot (Znth i modulus_values 0) retval) hInputs ⟨by omega, by omega⟩ (by omega) hp hg hgp hmod
  have hprod := (hSafe.1 (i+1) ⟨by omega, by omega⟩).2
  rw [hstep] at hprod
  have hd : Z.divide retval (Znth i residue_values 0-answer) := by
    rw [hg]
    exact crt_merge_difference_divisible__merge_transition residue_values modulus_values n_pre i answer lcm hc hp ⟨by omega, by omega⟩
  have hdiff := quot_div_of_divide_pos__merge_transition (Znth i residue_values 0-answer) retval hgp hd
  have hmul_preserved := PreH2
  obtain ⟨hbound, q, hq⟩ := PreH2
  rw [hdiff] at hq
  have heq : CRTReducedMergeEquation answer lcm (Znth i residue_values 0) (Znth i modulus_values 0) retval_3 := by
    apply reduced_merge_equation_from_bezout__merge_transition answer lcm (Znth i residue_values 0) (Znth i modulus_values 0) retval x_v_2 y_v retval_3 q hg hgp hd (by assumption)
    rw [← hmod]
    nlinarith [hq]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | (solve | simp only [INT_MAX, INT_MIN] at *; omega) | (solve | nlinarith) | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_1 : extended_chinese_remainder_theorem_entail_wit_3_1 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_1
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval := by assumption
  have hp : CRTPrefixMeaning residue_values modulus_values i answer lcm := by assumption
  have hc : ExtendedCRTSystemCompatible residue_values modulus_values n_pre := by assumption
  have hm : Z.divide retval (Znth i modulus_values 0) := by rw [hg]; exact Z.gcd_divide_r _ _
  have hmod := quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) retval hgp hm
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 hg hgp
  have hstep := crt_lcm_prefix_step__merge_transition residue_values modulus_values n_pre i answer lcm retval (Z.quot (Znth i modulus_values 0) retval) hInputs ⟨by omega, by omega⟩ (by omega) hp hg hgp hmod
  have hprod := (hSafe.1 (i+1) ⟨by omega, by omega⟩).2
  rw [hstep] at hprod
  have hn : 0 ≤ (retval_2 + Z.quot (Znth i modulus_values 0) retval) ∧ (retval_2 + Z.quot (Znth i modulus_values 0) retval) < Z.quot (Znth i modulus_values 0) retval := ⟨by assumption, by assumption⟩
  have har := bounded_merge_arithmetic__machine_bounds answer lcm (retval_2 + Z.quot (Znth i modulus_values 0) retval) (Z.quot (Znth i modulus_values 0) retval) ⟨by omega, by omega⟩ hn (by omega) hprod
  have hpositive : 0 < lcm * Z.quot (Znth i modulus_values 0) retval := Int.mul_pos (by omega) hred.1
  have hnext := crt_prefix_meaning_merge__merge_transition residue_values modulus_values n_pre i answer lcm retval (Z.quot (Znth i modulus_values 0) retval) (retval_2 + Z.quot (Znth i modulus_values 0) retval) hInputs hc ⟨by omega, by omega⟩ (by omega) hp hg hgp hmod hn PreH4
  have hmul_nonneg : 0 ≤ (retval_2 + Z.quot (Znth i modulus_values 0) retval) * lcm := Int.mul_nonneg hn.1 (by omega)
  have hmul_upper := Int.mul_le_mul_of_nonneg_right (show (retval_2 + Z.quot (Znth i modulus_values 0) retval) + 1 ≤ Z.quot (Znth i modulus_values 0) retval by omega) (show 0 ≤ lcm by omega)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | (solve | simp only [INT_MAX, INT_MIN] at *; omega) | (solve | nlinarith) | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_2 : extended_chinese_remainder_theorem_entail_wit_3_2 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_2
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval := by assumption
  have hp : CRTPrefixMeaning residue_values modulus_values i answer lcm := by assumption
  have hc : ExtendedCRTSystemCompatible residue_values modulus_values n_pre := by assumption
  have hm : Z.divide retval (Znth i modulus_values 0) := by rw [hg]; exact Z.gcd_divide_r _ _
  have hmod := quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) retval hgp hm
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 hg hgp
  have hstep := crt_lcm_prefix_step__merge_transition residue_values modulus_values n_pre i answer lcm retval (Z.quot (Znth i modulus_values 0) retval) hInputs ⟨by omega, by omega⟩ (by omega) hp hg hgp hmod
  have hprod := (hSafe.1 (i+1) ⟨by omega, by omega⟩).2
  rw [hstep] at hprod
  have hn : 0 ≤ (retval_2 + Z.quot (Znth i modulus_values 0) retval) ∧ (retval_2 + Z.quot (Znth i modulus_values 0) retval) < Z.quot (Znth i modulus_values 0) retval := ⟨by assumption, by assumption⟩
  have har := bounded_merge_arithmetic__machine_bounds answer lcm (retval_2 + Z.quot (Znth i modulus_values 0) retval) (Z.quot (Znth i modulus_values 0) retval) ⟨by omega, by omega⟩ hn (by omega) hprod
  have hpositive : 0 < lcm * Z.quot (Znth i modulus_values 0) retval := Int.mul_pos (by omega) hred.1
  have hnext := crt_prefix_meaning_merge__merge_transition residue_values modulus_values n_pre i answer lcm retval (Z.quot (Znth i modulus_values 0) retval) (retval_2 + Z.quot (Znth i modulus_values 0) retval) hInputs hc ⟨by omega, by omega⟩ (by omega) hp hg hgp hmod hn PreH4
  have hmul_nonneg : 0 ≤ (retval_2 + Z.quot (Znth i modulus_values 0) retval) * lcm := Int.mul_nonneg hn.1 (by omega)
  have hmul_upper := Int.mul_le_mul_of_nonneg_right (show (retval_2 + Z.quot (Znth i modulus_values 0) retval) + 1 ≤ Z.quot (Znth i modulus_values 0) retval by omega) (show 0 ≤ lcm by omega)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | (solve | simp only [INT_MAX, INT_MIN] at *; omega) | (solve | nlinarith) | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_3 : extended_chinese_remainder_theorem_entail_wit_3_3 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_3
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval := by assumption
  have hp : CRTPrefixMeaning residue_values modulus_values i answer lcm := by assumption
  have hc : ExtendedCRTSystemCompatible residue_values modulus_values n_pre := by assumption
  have hm : Z.divide retval (Znth i modulus_values 0) := by rw [hg]; exact Z.gcd_divide_r _ _
  have hmod := quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) retval hgp hm
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 hg hgp
  have hstep := crt_lcm_prefix_step__merge_transition residue_values modulus_values n_pre i answer lcm retval (Z.quot (Znth i modulus_values 0) retval) hInputs ⟨by omega, by omega⟩ (by omega) hp hg hgp hmod
  have hprod := (hSafe.1 (i+1) ⟨by omega, by omega⟩).2
  rw [hstep] at hprod
  have hn : 0 ≤ retval_2 ∧ retval_2 < Z.quot (Znth i modulus_values 0) retval := ⟨by assumption, by assumption⟩
  have har := bounded_merge_arithmetic__machine_bounds answer lcm retval_2 (Z.quot (Znth i modulus_values 0) retval) ⟨by omega, by omega⟩ hn (by omega) hprod
  have hpositive : 0 < lcm * Z.quot (Znth i modulus_values 0) retval := Int.mul_pos (by omega) hred.1
  have hnext := crt_prefix_meaning_merge__merge_transition residue_values modulus_values n_pre i answer lcm retval (Z.quot (Znth i modulus_values 0) retval) retval_2 hInputs hc ⟨by omega, by omega⟩ (by omega) hp hg hgp hmod hn PreH4
  have hmul_nonneg : 0 ≤ retval_2 * lcm := Int.mul_nonneg hn.1 (by omega)
  have hmul_upper := Int.mul_le_mul_of_nonneg_right (show retval_2 + 1 ≤ Z.quot (Znth i modulus_values 0) retval by omega) (show 0 ≤ lcm by omega)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | (solve | simp only [INT_MAX, INT_MIN] at *; omega) | (solve | nlinarith) | trivial

theorem proof_of_extended_chinese_remainder_theorem_entail_wit_3_4 : extended_chinese_remainder_theorem_entail_wit_3_4 := by
  unfold extended_chinese_remainder_theorem_entail_wit_3_4
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval := by assumption
  have hp : CRTPrefixMeaning residue_values modulus_values i answer lcm := by assumption
  have hc : ExtendedCRTSystemCompatible residue_values modulus_values n_pre := by assumption
  have hm : Z.divide retval (Znth i modulus_values 0) := by rw [hg]; exact Z.gcd_divide_r _ _
  have hmod := quot_div_of_divide_pos__merge_transition (Znth i modulus_values 0) retval hgp hm
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 hg hgp
  have hstep := crt_lcm_prefix_step__merge_transition residue_values modulus_values n_pre i answer lcm retval (Z.quot (Znth i modulus_values 0) retval) hInputs ⟨by omega, by omega⟩ (by omega) hp hg hgp hmod
  have hprod := (hSafe.1 (i+1) ⟨by omega, by omega⟩).2
  rw [hstep] at hprod
  have hn : 0 ≤ retval_2 ∧ retval_2 < Z.quot (Znth i modulus_values 0) retval := ⟨by assumption, by assumption⟩
  have har := bounded_merge_arithmetic__machine_bounds answer lcm retval_2 (Z.quot (Znth i modulus_values 0) retval) ⟨by omega, by omega⟩ hn (by omega) hprod
  have hpositive : 0 < lcm * Z.quot (Znth i modulus_values 0) retval := Int.mul_pos (by omega) hred.1
  have hnext := crt_prefix_meaning_merge__merge_transition residue_values modulus_values n_pre i answer lcm retval (Z.quot (Znth i modulus_values 0) retval) retval_2 hInputs hc ⟨by omega, by omega⟩ (by omega) hp hg hgp hmod hn PreH4
  have hmul_nonneg : 0 ≤ retval_2 * lcm := Int.mul_nonneg hn.1 (by omega)
  have hmul_upper := Int.mul_le_mul_of_nonneg_right (show retval_2 + 1 ≤ Z.quot (Znth i modulus_values 0) retval by omega) (show 0 ≤ lcm by omega)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | (solve | simp only [INT_MAX, INT_MIN] at *; omega) | (solve | nlinarith) | trivial

theorem proof_of_extended_chinese_remainder_theorem_return_wit_1 : extended_chinese_remainder_theorem_return_wit_1 := by
  unfold extended_chinese_remainder_theorem_return_wit_1
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have he : i = n_pre := by omega
  have hr := crt_prefix_meaning_to_result__prefix_boundaries residue_values modulus_values n_pre i answer lcm he ⟨by omega, by omega⟩ PreH15
  asrt_simpl
  Intros
  Exists lcm
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | (solve | simp only [INT_MAX, INT_MIN] at *; omega) | (solve | nlinarith) | (solve | repeat constructor <;> first | assumption | omega) | trivial

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_7 : extended_chinese_remainder_theorem_safety_wit_7 := by
  unfold extended_chinese_remainder_theorem_safety_wit_7
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN] at *
  all_goals omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_9 : extended_chinese_remainder_theorem_safety_wit_9 := by
  unfold extended_chinese_remainder_theorem_safety_wit_9
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN] at *
  all_goals omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_12 : extended_chinese_remainder_theorem_safety_wit_12 := by
  unfold extended_chinese_remainder_theorem_safety_wit_12
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval := by assumption
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 hg hgp
  have hbound := PreH2.1
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN] at *
  all_goals omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_13 : extended_chinese_remainder_theorem_safety_wit_13 := by
  unfold extended_chinese_remainder_theorem_safety_wit_13
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval := by assumption
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 hg hgp
  have hbound := PreH2.1
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN] at *
  all_goals omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_14 : extended_chinese_remainder_theorem_safety_wit_14 := by
  unfold extended_chinese_remainder_theorem_safety_wit_14
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval := by assumption
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 hg hgp
  have hn : 0 ≤ (retval_2 + (Z.quot (Znth i modulus_values 0) retval)) ∧ (retval_2 + (Z.quot (Znth i modulus_values 0) retval)) < (Z.quot (Znth i modulus_values 0) retval) := ⟨by assumption, by assumption⟩
  have har := bounded_merge_arithmetic__machine_bounds answer lcm (retval_2 + (Z.quot (Znth i modulus_values 0) retval)) (Z.quot (Znth i modulus_values 0) retval) ⟨by omega, by omega⟩ hn (by omega) (by assumption)
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN] at *
  all_goals omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_15 : extended_chinese_remainder_theorem_safety_wit_15 := by
  unfold extended_chinese_remainder_theorem_safety_wit_15
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval := by assumption
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 hg hgp
  have hn : 0 ≤ (retval_2 + (Z.quot (Znth i modulus_values 0) retval)) ∧ (retval_2 + (Z.quot (Znth i modulus_values 0) retval)) < (Z.quot (Znth i modulus_values 0) retval) := ⟨by assumption, by assumption⟩
  have har := bounded_merge_arithmetic__machine_bounds answer lcm (retval_2 + (Z.quot (Znth i modulus_values 0) retval)) (Z.quot (Znth i modulus_values 0) retval) ⟨by omega, by omega⟩ hn (by omega) (by assumption)
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN] at *
  all_goals omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_16 : extended_chinese_remainder_theorem_safety_wit_16 := by
  unfold extended_chinese_remainder_theorem_safety_wit_16
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval := by assumption
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 hg hgp
  have hn : 0 ≤ (retval_2 + (Z.quot (Znth i modulus_values 0) retval)) ∧ (retval_2 + (Z.quot (Znth i modulus_values 0) retval)) < (Z.quot (Znth i modulus_values 0) retval) := ⟨by assumption, by assumption⟩
  have har := bounded_merge_arithmetic__machine_bounds answer lcm (retval_2 + (Z.quot (Znth i modulus_values 0) retval)) (Z.quot (Znth i modulus_values 0) retval) ⟨by omega, by omega⟩ hn (by omega) (by assumption)
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN] at *
  all_goals omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_17 : extended_chinese_remainder_theorem_safety_wit_17 := by
  unfold extended_chinese_remainder_theorem_safety_wit_17
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval := by assumption
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 hg hgp
  have hn : 0 ≤ (retval_2 + (Z.quot (Znth i modulus_values 0) retval)) ∧ (retval_2 + (Z.quot (Znth i modulus_values 0) retval)) < (Z.quot (Znth i modulus_values 0) retval) := ⟨by assumption, by assumption⟩
  have har := bounded_merge_arithmetic__machine_bounds answer lcm (retval_2 + (Z.quot (Znth i modulus_values 0) retval)) (Z.quot (Znth i modulus_values 0) retval) ⟨by omega, by omega⟩ hn (by omega) (by assumption)
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN] at *
  all_goals omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_18 : extended_chinese_remainder_theorem_safety_wit_18 := by
  unfold extended_chinese_remainder_theorem_safety_wit_18
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval_2 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval_2 = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval_2 := by assumption
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval_2 hb.1 hg hgp
  have hn : 0 ≤ retval ∧ retval < (Z.quot (Znth i modulus_values 0) retval_2) := ⟨by assumption, by assumption⟩
  have har := bounded_merge_arithmetic__machine_bounds answer lcm retval (Z.quot (Znth i modulus_values 0) retval_2) ⟨by omega, by omega⟩ hn (by omega) (by assumption)
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN] at *
  all_goals omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_19 : extended_chinese_remainder_theorem_safety_wit_19 := by
  unfold extended_chinese_remainder_theorem_safety_wit_19
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval_2 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval_2 = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval_2 := by assumption
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval_2 hb.1 hg hgp
  have hn : 0 ≤ retval ∧ retval < (Z.quot (Znth i modulus_values 0) retval_2) := ⟨by assumption, by assumption⟩
  have har := bounded_merge_arithmetic__machine_bounds answer lcm retval (Z.quot (Znth i modulus_values 0) retval_2) ⟨by omega, by omega⟩ hn (by omega) (by assumption)
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN] at *
  all_goals omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_20 : extended_chinese_remainder_theorem_safety_wit_20 := by
  unfold extended_chinese_remainder_theorem_safety_wit_20
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval_2 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval_2 = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval_2 := by assumption
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval_2 hb.1 hg hgp
  have hn : 0 ≤ retval ∧ retval < (Z.quot (Znth i modulus_values 0) retval_2) := ⟨by assumption, by assumption⟩
  have har := bounded_merge_arithmetic__machine_bounds answer lcm retval (Z.quot (Znth i modulus_values 0) retval_2) ⟨by omega, by omega⟩ hn (by omega) (by assumption)
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN] at *
  all_goals omega

theorem proof_of_extended_chinese_remainder_theorem_safety_wit_21 : extended_chinese_remainder_theorem_safety_wit_21 := by
  unfold extended_chinese_remainder_theorem_safety_wit_21
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval_2 retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval_2 = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval_2 := by assumption
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval_2 hb.1 hg hgp
  have hn : 0 ≤ retval ∧ retval < (Z.quot (Znth i modulus_values 0) retval_2) := ⟨by assumption, by assumption⟩
  have har := bounded_merge_arithmetic__machine_bounds answer lcm retval (Z.quot (Znth i modulus_values 0) retval_2) ⟨by omega, by omega⟩ hn (by omega) (by assumption)
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN] at *
  all_goals omega

theorem proof_of_extended_chinese_remainder_theorem_partial_solve_wit_4_pure : extended_chinese_remainder_theorem_partial_solve_wit_4_pure := by
  unfold extended_chinese_remainder_theorem_partial_solve_wit_4_pure
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN] at *
  all_goals omega

theorem proof_of_extended_chinese_remainder_theorem_partial_solve_wit_8_pure : extended_chinese_remainder_theorem_partial_solve_wit_8_pure := by
  unfold extended_chinese_remainder_theorem_partial_solve_wit_8_pure
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval := by assumption
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 hg hgp
  have hp : CRTPrefixMeaning residue_values modulus_values i answer lcm := by assumption
  have hdouble := hSafe.2 i ⟨by omega, by omega⟩
  rw [← hp.1, ← hg] at hdouble
  simp only [INT_MAX] at *
  have hdiff := signed_difference_division_bounds__machine_bounds (Znth i residue_values 0) answer retval ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hgp
  have hstrict := bezout_coefficient_strict__gcd_branch_setup lcm (Znth i modulus_values 0) retval x_v y_v hb.1.1 hg hgp (by assumption) (by assumption) (by assumption)
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN] at *
  all_goals omega

theorem proof_of_extended_chinese_remainder_theorem_partial_solve_wit_10_pure : extended_chinese_remainder_theorem_partial_solve_wit_10_pure := by
  unfold extended_chinese_remainder_theorem_partial_solve_wit_10_pure
  left
  intro modulus_values residue_values n_pre residues_pre moduli_pre combined_modulus_pre lcm answer i y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  prop_apply (intArray.full_Zlength residues_pre n_pre residue_values)
  Intros_p hreslength
  prop_apply (intArray.full_Zlength moduli_pre n_pre modulus_values)
  Intros_p hmodlength
  have hInputs := inputs_from_annotation residue_values modulus_values n_pre (by omega) hreslength hmodlength (by assumption) (by assumption) (by assumption) (by assumption)
  have hSafe := int_safe_from_annotation modulus_values n_pre (by assumption) (by assumption) (by assumption)
  have hb := hInputs.2.2.2 i ⟨by omega, by omega⟩
  have hg : retval = Z.gcd lcm (Znth i modulus_values 0) := by assumption
  have hgp : 0 < retval := by assumption
  have hred := positive_gcd_quotient_bounds__machine_bounds lcm (Znth i modulus_values 0) retval hb.1 hg hgp
  have hp : CRTPrefixMeaning residue_values modulus_values i answer lcm := by assumption
  have hdouble := hSafe.2 i ⟨by omega, by omega⟩
  rw [← hp.1, ← hg] at hdouble
  simp only [INT_MAX] at *
  have hdiff := signed_difference_division_bounds__machine_bounds (Znth i residue_values 0) answer retval ⟨by omega, by omega⟩ ⟨by omega, by omega⟩ hgp
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN] at *
  all_goals omega

end SimpleC.EE.LLM_bench.Algorithms.extended_chinese_remainder_theorem.extended_chinese_remainder_theorem_proof_manual
