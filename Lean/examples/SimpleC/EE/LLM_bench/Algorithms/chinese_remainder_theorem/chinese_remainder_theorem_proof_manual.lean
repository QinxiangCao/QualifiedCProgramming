import SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_goal
import SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_proof_auto

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open chinese_remainder_theorem_goal chinese_remainder_theorem_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

private theorem normalize_negative_term (a r p result : Int) (hp : 0 < p) (hr : 0 ≤ result) :
    Z.rem (result+(Z.rem (Z.rem a p*r) p+p)) p =
    Z.modulo (result+Z.modulo (Z.modulo a p*r) p) p := by
  have hb := AUXLib.rem_bounds (Z.rem a p*r) p hp
  rw [crt_rem_eq_mod_of_nonnegative_dividend__crt_transition _ p (by omega) hp]
  change Int.fmod (result+(Z.rem (Z.rem a p*r) p+p)) p = _
  rw [← Int.add_assoc, Int.add_fmod_right]
  apply Int.add_fmod_eq_add_fmod_left
  have ht := (crt_rem_mod__crt_transition (Z.rem a p*r) p (by omega)).trans
    (crt_rem_mul_mod__crt_transition a r p (by omega))
  simpa only [Z.modulo, Int.fmod_fmod] using ht

private theorem normalize_nonnegative_term (a r p result : Int) (hp : 0 < p) (hr : 0 ≤ result)
    (ht : 0 ≤ Z.rem (Z.rem a p*r) p) :
    Z.rem (result+Z.rem (Z.rem a p*r) p) p =
    Z.modulo (result+Z.modulo (Z.modulo a p*r) p) p := by
  rw [crt_rem_eq_mod_of_nonnegative_dividend__crt_transition _ p (by omega) hp]
  rw [crt_nonnegative_rem_eq_mod__crt_transition (Z.rem a p*r) p hp ht,
    crt_rem_mul_mod__crt_transition a r p (by omega)]

-- Preserve the source residual VCs and run the SL strategy. Goal_apply needs
-- explicit arguments; pure split conclusions use dump_spatial_left, whereas
-- the store_int_range proof retains the actual coefficient cell.

private theorem small_rem_cast32 (value modulus : Int)
    (hpos : 1 ≤ modulus) (hbound : modulus ≤ 46340) :
    signed_last_nbits (Z.rem value modulus) 32 = Z.rem value modulus := by
  apply signed_last_nbits_eq _ 32 (by decide)
  have hb := AUXLib.rem_bounds value modulus (by omega)
  change (-2147483648 : Int) ≤ Z.rem value modulus ∧
    Z.rem value modulus < 2147483648
  omega

private theorem crt_unprocessed_zero_init (moduli : List Int) :
    CRTUnprocessedZero moduli 0 0 := by
  unfold CRTUnprocessedZero
  apply Forall.iff_forall_mem.mpr
  intro modulus hmem
  simp [Z.rem]

private theorem crt_consistent_prefix_init (remainders moduli : List Int) :
    CRTConsistentPrefix remainders moduli 0 0 := by
  unfold CRTConsistentPrefix
  change Forall2 (fun r m : Int => Z.modulo 0 m = r) [] []
  exact Forall2.nil

private theorem forall_indexed (P : Int → Prop) (l : List Int) :
    Forall P l ↔ ∀ i, 0 ≤ i ∧ i < Zlength l → P (Znth i l 0) := by
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

private theorem sublist_zlen (lo hi : Int) (l : List Int)
    (hb : 0 ≤ lo ∧ lo ≤ hi) (he : hi ≤ Zlength l) :
    Zlength (sublist lo hi l) = hi - lo := by
  unfold Zlength
  rw [sublist_length lo hi l hb he]
  simp only [Int.ofNat_eq_coe]
  exact Int.toNat_of_nonneg (by omega)

private theorem prefix_indexed (r m : List Int) (i result : Int)
    (hlen : Zlength r = Zlength m) (hi : 0 ≤ i ∧ i ≤ Zlength m) :
    CRTConsistentPrefix r m i result ↔ CRTProcessedCongruences r m i result := by
  have hr := sublist_zlen 0 i r (by omega) (by omega)
  have hm := sublist_zlen 0 i m (by omega) hi.2
  unfold CRTConsistentPrefix
  rw [Forall2_nth_iff Int Int _ _ _ 0 0]
  have hnat : (sublist 0 i r).length = (sublist 0 i m).length := by
    change ((sublist 0 i r).length : Int) = i - 0 at hr
    change ((sublist 0 i m).length : Int) = i - 0 at hm
    omega
  constructor
  · intro h k hk
    have hn : k.toNat < (sublist 0 i r).length := by
      change ((sublist 0 i r).length : Int) = i - 0 at hr
      omega
    have hh := h.2 k.toNat hn
    change Z.modulo result (Znth k (sublist 0 i m) 0) = Znth k (sublist 0 i r) 0 at hh
    simpa only [Znth_sublist 0 0 k i m (by omega) (by omega),
      Znth_sublist 0 0 k i r (by omega) (by omega), Int.add_zero] using hh
  · intro h
    refine ⟨hnat, ?_⟩
    intro n hn
    have hk : 0 ≤ (n : Int) ∧ (n : Int) < i := by
      change ((sublist 0 i r).length : Int) = i - 0 at hr
      omega
    change Z.modulo result (Znth (n : Int) (sublist 0 i m) 0) = Znth (n : Int) (sublist 0 i r) 0
    simpa only [Znth_sublist 0 0 (n : Int) i m (by omega) (by omega),
      Znth_sublist 0 0 (n : Int) i r (by omega) (by omega), Int.add_zero] using h n hk

private theorem zero_indexed (m : List Int) (i result : Int)
    (hi : 0 ≤ i ∧ i ≤ Zlength m) :
    CRTUnprocessedZero m i result ↔
      ∀ k, i ≤ k ∧ k < Zlength m → Z.rem result (Znth k m 0) = 0 := by
  unfold CRTUnprocessedZero
  rw [forall_indexed]
  have hl := sublist_zlen i (Zlength m) m hi (by rfl)
  constructor
  · intro h k hk
    have hh := h (k-i) (by omega)
    rw [Znth_sublist 0 i (k-i) (Zlength m) m hi.1 (by omega), Int.sub_add_cancel] at hh
    exact hh
  · intro h k hk
    rw [Znth_sublist 0 i k (Zlength m) m hi.1 (by omega)]
    exact h (k+i) (by omega)

private theorem rem_multiple (m value p : Int) (hv : m ∣ value) (hp : m ∣ p) :
    m ∣ Z.rem value p := by
  have hd := Int.dvd_trans hp (Int.dvd_tmod_sub_self (x := value) (m := p))
  have hs := Int.dvd_add hd hv
  simpa only [Int.sub_add_cancel] using hs

private theorem update_unprocessed (r m : List Int) (result i product x offset : Int)
    (hv : CRTInputValid r m) (hi : 0 ≤ i ∧ i < Zlength m)
    (hp : product = CRTProduct m) (hpp : 0 < product)
    (hz : CRTUnprocessedZero m i result) :
    CRTUnprocessedZero m (i+1)
      (Z.rem (result + Z.rem (Z.rem (x * Z.quot product (Znth i m 0)) product *
        Znth i r 0) product + offset * product) product) := by
  have hf := crt_product_factor_arithmetic__crt_transition r m i hv hi
  dsimp only at hf
  rw [← hp] at hf
  have hmi := (hv.2.2.1 i hi).1
  rw [crt_quot_div_pos__crt_transition product (Znth i m 0) (by omega) (by omega)]
  apply (zero_indexed m (i+1) _ (by omega)).mpr
  have hz' := (zero_indexed m i result (by omega)).mp hz
  intro k hk
  have hq := (Z.divide_iff_dvd _ _).mp (hf.2.2 k (by omega) (by omega))
  have hd : Znth k m 0 ∣ product := by
    rw [← hf.1]
    exact Int.dvd_trans hq (Int.dvd_mul_right _ _)
  apply Int.tmod_eq_zero_of_dvd
  apply rem_multiple _ _ product
  · apply Int.dvd_add
    · apply Int.dvd_add
      · exact Int.dvd_of_tmod_eq_zero (hz' k (by omega))
      · apply rem_multiple _ _ product _ hd
        apply Int.dvd_trans (rem_multiple _ _ product
          (Int.dvd_trans hq (Int.dvd_mul_left _ _)) hd)
        exact Int.dvd_mul_right _ _
    · exact Int.dvd_trans hd (Int.dvd_mul_left _ _)
  · exact hd

private theorem crt_input_from_annotation (remainders moduli : List Int)
    (hlen : Zlength remainders = Zlength moduli) (hn : 1 ≤ Zlength moduli)
    (hm : Forall (fun m => 1 ≤ m) moduli)
    (hr : Forall (fun r => 0 ≤ r) remainders)
    (hrel : Forall2 (fun r m => r < m) remainders moduli)
    (hc : ∀ i j, ((0 ≤ i ∧ i < j) ∧ j < Zlength moduli) →
      Z.gcd (Znth i moduli 0) (Znth j moduli 0) = 1) :
    CRTInputValid remainders moduli := by
  refine ⟨hlen, hn, ?_, ?_⟩
  · intro i hi
    have him : i.toNat < moduli.length := by
      change 0 ≤ i ∧ i < (moduli.length : Int) at hi
      omega
    have hir : i.toNat < remainders.length := by
      change 0 ≤ i ∧ i < (moduli.length : Int) at hi
      change (remainders.length : Int) = moduli.length at hlen
      omega
    have hmi := (Forall.iff_forall_mem.mp hm) moduli[i.toNat]
      (List.mem_iff_getElem.mpr ⟨i.toNat, him, rfl⟩)
    have hri := (Forall.iff_forall_mem.mp hr) remainders[i.toNat]
      (List.mem_iff_getElem.mpr ⟨i.toNat, hir, rfl⟩)
    have hre := ((AUXLib.Forall2_nth_iff Int Int (· < ·) remainders moduli 0 0).mp hrel).2 i.toNat hir
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem him, Option.getD_some] using hmi
    · simpa only [Znth, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hir, Option.getD_some] using hri
    · exact hre
  · intro i j hi
    exact hc i j ⟨⟨hi.1, hi.2.1⟩, hi.2.2⟩

theorem proof_of_chinese_remainder_theorem_safety_wit_3_split_goal_1 : chinese_remainder_theorem_safety_wit_3_split_goal_1 := by
  unfold chinese_remainder_theorem_safety_wit_3_split_goal_1
  intro moduli_l remainders_l n_pre remainders_pre moduli_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have input_valid_PreH3 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      simp only [INT_MAX] at *
      dump_pre_spatial
      have hi : 0 ≤ i ∧ i < Zlength moduli_l := by omega
      have hb := (crt_prefix_product_bounds__product_progress remainders_l moduli_l (i+1) input_valid_PreH3 (by omega)).1
      rw [crt_prefix_product_step__product_progress moduli_l i hi, ← PreH13] at hb
      omega

theorem proof_of_chinese_remainder_theorem_safety_wit_3_split_goal_2 : chinese_remainder_theorem_safety_wit_3_split_goal_2 := by
  unfold chinese_remainder_theorem_safety_wit_3_split_goal_2
  intro moduli_l remainders_l n_pre remainders_pre moduli_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have input_valid_PreH3 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      simp only [INT_MIN] at *
      dump_pre_spatial
      have hi : 0 ≤ i ∧ i < Zlength moduli_l := by omega
      have hb := (crt_prefix_product_bounds__product_progress remainders_l moduli_l (i+1) input_valid_PreH3 (by omega)).1
      rw [crt_prefix_product_step__product_progress moduli_l i hi, ← PreH13] at hb
      omega

theorem proof_of_chinese_remainder_theorem_safety_wit_3 : chinese_remainder_theorem_safety_wit_3 := by
  unfold chinese_remainder_theorem_safety_wit_3
  right
  intro moduli_l remainders_l n_pre remainders_pre moduli_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have input_valid_PreH3 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_3_split_goal_1 moduli_l remainders_l n_pre remainders_pre moduli_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_3_split_goal_2 moduli_l remainders_l n_pre remainders_pre moduli_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
    | trivial

theorem proof_of_chinese_remainder_theorem_safety_wit_7_split_goal_1 : chinese_remainder_theorem_safety_wit_7_split_goal_1 := by
  unfold chinese_remainder_theorem_safety_wit_7_split_goal_1
  intro moduli_l remainders_l n_pre remainders_pre moduli_pre result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have input_valid_PreH3 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      simp only [INT_MIN] at *
      dump_pre_spatial
      left
      omega

theorem proof_of_chinese_remainder_theorem_safety_wit_7_split_goal_2 : chinese_remainder_theorem_safety_wit_7_split_goal_2 := by
  unfold chinese_remainder_theorem_safety_wit_7_split_goal_2
  intro moduli_l remainders_l n_pre remainders_pre moduli_pre result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have input_valid_PreH3 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      dump_pre_spatial
      have hb := input_valid_PreH3.2.2.1 i (by omega)
      omega

theorem proof_of_chinese_remainder_theorem_safety_wit_7 : chinese_remainder_theorem_safety_wit_7 := by
  unfold chinese_remainder_theorem_safety_wit_7
  right
  intro moduli_l remainders_l n_pre remainders_pre moduli_pre result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have input_valid_PreH3 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_7_split_goal_1 moduli_l remainders_l n_pre remainders_pre moduli_pre result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_7_split_goal_2 moduli_l remainders_l n_pre remainders_pre moduli_pre result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | trivial

theorem proof_of_chinese_remainder_theorem_safety_wit_11_split_goal_1 : chinese_remainder_theorem_safety_wit_11_split_goal_1 := by
  unfold chinese_remainder_theorem_safety_wit_11_split_goal_1
  intro moduli_l remainders_l n_pre remainders_pre moduli_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have input_valid_PreH5 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      simp only [INT_MAX] at *
      have hb := input_valid_PreH5.2.2.1 i (by omega)
      have hm := CRTInputValid_modulus_upper_bound__machine_safety remainders_l moduli_l i input_valid_PreH5 (by omega)
      have hr := crt_c_rem_mul_int_bounds__machine_safety (x_v * Z.quot product (Znth i moduli_l 0)) product (Znth i remainders_l 0) PreH14 PreH15 hb.2.1 (by omega)
      dump_pre_spatial
      rw [small_rem_cast32 _ product PreH14 PreH15]
      omega

theorem proof_of_chinese_remainder_theorem_safety_wit_11_split_goal_2 : chinese_remainder_theorem_safety_wit_11_split_goal_2 := by
  unfold chinese_remainder_theorem_safety_wit_11_split_goal_2
  intro moduli_l remainders_l n_pre remainders_pre moduli_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have input_valid_PreH5 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      simp only [INT_MIN] at *
      have hb := input_valid_PreH5.2.2.1 i (by omega)
      have hm := CRTInputValid_modulus_upper_bound__machine_safety remainders_l moduli_l i input_valid_PreH5 (by omega)
      have hr := crt_c_rem_mul_int_bounds__machine_safety (x_v * Z.quot product (Znth i moduli_l 0)) product (Znth i remainders_l 0) PreH14 PreH15 hb.2.1 (by omega)
      dump_pre_spatial
      rw [small_rem_cast32 _ product PreH14 PreH15]
      omega

theorem proof_of_chinese_remainder_theorem_safety_wit_11 : chinese_remainder_theorem_safety_wit_11 := by
  unfold chinese_remainder_theorem_safety_wit_11
  right
  intro moduli_l remainders_l n_pre remainders_pre moduli_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have input_valid_PreH5 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_11_split_goal_1 moduli_l remainders_l n_pre remainders_pre moduli_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_11_split_goal_2 moduli_l remainders_l n_pre remainders_pre moduli_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21))
    | trivial

theorem proof_of_chinese_remainder_theorem_safety_wit_17_split_goal_1 : chinese_remainder_theorem_safety_wit_17_split_goal_1 := by
  unfold chinese_remainder_theorem_safety_wit_17_split_goal_1
  intro moduli_l remainders_l n_pre remainders_pre moduli_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have input_valid_PreH6 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      simp only [INT_MAX] at *
      have hb := AUXLib.rem_bounds (Z.rem (x_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product (by omega)
      dump_pre_spatial
      rw [small_rem_cast32 _ product (by omega) (by omega)]
      omega

theorem proof_of_chinese_remainder_theorem_safety_wit_17_split_goal_2 : chinese_remainder_theorem_safety_wit_17_split_goal_2 := by
  unfold chinese_remainder_theorem_safety_wit_17_split_goal_2
  intro moduli_l remainders_l n_pre remainders_pre moduli_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have input_valid_PreH6 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      simp only [INT_MIN] at *
      have hb := AUXLib.rem_bounds (Z.rem (x_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product (by omega)
      dump_pre_spatial
      rw [small_rem_cast32 _ product (by omega) (by omega)]
      omega

theorem proof_of_chinese_remainder_theorem_safety_wit_17 : chinese_remainder_theorem_safety_wit_17 := by
  unfold chinese_remainder_theorem_safety_wit_17
  right
  intro moduli_l remainders_l n_pre remainders_pre moduli_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have input_valid_PreH6 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_17_split_goal_1 moduli_l remainders_l n_pre remainders_pre moduli_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_safety_wit_17_split_goal_2 moduli_l remainders_l n_pre remainders_pre moduli_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22))
    | trivial

theorem proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_1 : chinese_remainder_theorem_entail_wit_1_split_goal_1 := by
  unfold chinese_remainder_theorem_entail_wit_1_split_goal_1
  intro moduli_l remainders_l n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have input_valid_PreH2 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      exact PreH3.1.2

theorem proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_2 : chinese_remainder_theorem_entail_wit_1_split_goal_2 := by
  unfold chinese_remainder_theorem_entail_wit_1_split_goal_2
  intro moduli_l remainders_l n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have input_valid_PreH2 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      exact PreH3.1.1

theorem proof_of_chinese_remainder_theorem_entail_wit_1 : chinese_remainder_theorem_entail_wit_1 := by
  unfold chinese_remainder_theorem_entail_wit_1
  right
  intro moduli_l remainders_l n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  have input_valid_PreH2 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_1 moduli_l remainders_l n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_1 moduli_l remainders_l n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_2 moduli_l remainders_l n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_1_split_goal_2 moduli_l remainders_l n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9)
    | trivial

theorem proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_1 : chinese_remainder_theorem_entail_wit_2_split_goal_1 := by
  unfold chinese_remainder_theorem_entail_wit_2_split_goal_1
  intro moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have input_valid_PreH3 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      have hi : 0 ≤ i ∧ i < Zlength moduli_l := by omega
      have hb := (crt_prefix_product_bounds__product_progress remainders_l moduli_l (i+1) input_valid_PreH3 (by omega)).1
      rw [crt_prefix_product_step__product_progress moduli_l i hi, ← PreH13] at hb
      omega

theorem proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_2 : chinese_remainder_theorem_entail_wit_2_split_goal_2 := by
  unfold chinese_remainder_theorem_entail_wit_2_split_goal_2
  intro moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have input_valid_PreH3 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      have hi : 0 ≤ i ∧ i < Zlength moduli_l := by omega
      have hb := (crt_prefix_product_bounds__product_progress remainders_l moduli_l (i+1) input_valid_PreH3 (by omega)).1
      rw [crt_prefix_product_step__product_progress moduli_l i hi, ← PreH13] at hb
      omega

theorem proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_3 : chinese_remainder_theorem_entail_wit_2_split_goal_3 := by
  unfold chinese_remainder_theorem_entail_wit_2_split_goal_3
  intro moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have input_valid_PreH3 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      rw [PreH13]
      exact (crt_prefix_product_step__product_progress moduli_l i (by omega)).symm

theorem proof_of_chinese_remainder_theorem_entail_wit_2 : chinese_remainder_theorem_entail_wit_2 := by
  unfold chinese_remainder_theorem_entail_wit_2
  right
  intro moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have input_valid_PreH3 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_1 moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_1 moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_2 moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_2 moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_3 moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_2_split_goal_3 moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
    | trivial

theorem proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_1 : chinese_remainder_theorem_entail_wit_3_split_goal_1 := by
  unfold chinese_remainder_theorem_entail_wit_3_split_goal_1
  intro moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have input_valid_PreH3 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      intro k hk
      simp [Z.rem]

theorem proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_2 : chinese_remainder_theorem_entail_wit_3_split_goal_2 := by
  unfold chinese_remainder_theorem_entail_wit_3_split_goal_2
  intro moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have input_valid_PreH3 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      intro k hk
      omega

theorem proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_3 : chinese_remainder_theorem_entail_wit_3_split_goal_3 := by
  unfold chinese_remainder_theorem_entail_wit_3_split_goal_3
  intro moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have input_valid_PreH3 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      have hi : i = Zlength moduli_l := by omega
      rw [sublist_self moduli_l i hi] at PreH13
      exact PreH13

theorem proof_of_chinese_remainder_theorem_entail_wit_3 : chinese_remainder_theorem_entail_wit_3 := by
  unfold chinese_remainder_theorem_entail_wit_3
  right
  intro moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15
  have input_valid_PreH3 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_1 moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_1 moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_2 moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_2 moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_3 moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15))
    | exact (proof_of_chinese_remainder_theorem_entail_wit_3_split_goal_3 moduli_l remainders_l n_pre product i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15)
    | trivial

theorem proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 : chinese_remainder_theorem_entail_wit_4_1_split_goal_1 := by
  unfold chinese_remainder_theorem_entail_wit_4_1_split_goal_1
  intro moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [small_rem_cast32 _ product PreH15 PreH16] at PreH1 ⊢
  have hv := crt_input_from_annotation remainders_l moduli_l PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have h := update_unprocessed remainders_l moduli_l result i product x_v 1
    hv (by omega) PreH14 (by omega) PreH22
  simpa only [Int.one_mul, Int.zero_mul, Int.add_zero, Int.add_assoc] using h

theorem proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 : chinese_remainder_theorem_entail_wit_4_1_split_goal_2 := by
  unfold chinese_remainder_theorem_entail_wit_4_1_split_goal_2
  intro moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [small_rem_cast32 _ product PreH15 PreH16] at PreH1 ⊢
  have hv := crt_input_from_annotation remainders_l moduli_l PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hm := (hv.2.2.1 i (by omega)).1
  have hq := crt_quot_div_pos__crt_transition product (Znth i moduli_l 0) (by omega) (by omega)
  rw [hq] at PreH3 PreH1 ⊢
  have hc := (prefix_indexed remainders_l moduli_l i result PreH6 (by omega)).mp PreH21
  have hz' := (zero_indexed moduli_l i result (by omega)).mp PreH22
  have hz : ∀ k, (i ≤ k ∧ k < Zlength moduli_l) → Z.modulo result (Znth k moduli_l 0) = 0 := by
    intro k hk
    have hmk := (hv.2.2.1 k (by omega)).1
    rw [← crt_rem_eq_mod_of_nonnegative_dividend__crt_transition result (Znth k moduli_l 0) PreH19 (by omega)]
    exact hz' k hk
  have hu := crt_update_processed__crt_transition remainders_l moduli_l result i product x_v y_v
    hv (by omega) PreH14 PreH15 hc hz PreH3
  rw [normalize_negative_term _ _ product result (by omega) PreH19]
  exact (prefix_indexed remainders_l moduli_l (i+1) _ PreH6 (by omega)).mpr hu

theorem proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 : chinese_remainder_theorem_entail_wit_4_1_split_goal_3 := by
  unfold chinese_remainder_theorem_entail_wit_4_1_split_goal_3
  intro moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [small_rem_cast32 _ product PreH15 PreH16] at PreH1 ⊢
  have ht := AUXLib.rem_bounds (Z.rem (x_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product (by omega)
  have hb := AUXLib.rem_nonneg_bounds (result + (Z.rem (Z.rem (x_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product + product)) product (by omega) (by omega)
  omega

theorem proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_4 : chinese_remainder_theorem_entail_wit_4_1_split_goal_4 := by
  unfold chinese_remainder_theorem_entail_wit_4_1_split_goal_4
  intro moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [small_rem_cast32 _ product PreH15 PreH16] at PreH1 ⊢
  have ht := AUXLib.rem_bounds (Z.rem (x_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product (by omega)
  have hb := AUXLib.rem_nonneg_bounds (result + (Z.rem (Z.rem (x_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product + product)) product (by omega) (by omega)
  omega

theorem proof_of_chinese_remainder_theorem_entail_wit_4_1 : chinese_remainder_theorem_entail_wit_4_1 := by
  unfold chinese_remainder_theorem_entail_wit_4_1
  right
  intro moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_1 moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_2 moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_3 moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_chinese_remainder_theorem_entail_wit_4_1_split_goal_4 moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | assumption
      | omega

theorem proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 : chinese_remainder_theorem_entail_wit_4_2_split_goal_1 := by
  unfold chinese_remainder_theorem_entail_wit_4_2_split_goal_1
  intro moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [small_rem_cast32 _ product PreH15 PreH16] at PreH1 ⊢
  have hv := crt_input_from_annotation remainders_l moduli_l PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have h := update_unprocessed remainders_l moduli_l result i product x_v 0
    hv (by omega) PreH14 (by omega) PreH22
  simpa only [Int.one_mul, Int.zero_mul, Int.add_zero, Int.add_assoc] using h

theorem proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 : chinese_remainder_theorem_entail_wit_4_2_split_goal_2 := by
  unfold chinese_remainder_theorem_entail_wit_4_2_split_goal_2
  intro moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [small_rem_cast32 _ product PreH15 PreH16] at PreH1 ⊢
  have hv := crt_input_from_annotation remainders_l moduli_l PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have hm := (hv.2.2.1 i (by omega)).1
  have hq := crt_quot_div_pos__crt_transition product (Znth i moduli_l 0) (by omega) (by omega)
  rw [hq] at PreH3 PreH1 ⊢
  have hc := (prefix_indexed remainders_l moduli_l i result PreH6 (by omega)).mp PreH21
  have hz' := (zero_indexed moduli_l i result (by omega)).mp PreH22
  have hz : ∀ k, (i ≤ k ∧ k < Zlength moduli_l) → Z.modulo result (Znth k moduli_l 0) = 0 := by
    intro k hk
    have hmk := (hv.2.2.1 k (by omega)).1
    rw [← crt_rem_eq_mod_of_nonnegative_dividend__crt_transition result (Znth k moduli_l 0) PreH19 (by omega)]
    exact hz' k hk
  have hu := crt_update_processed__crt_transition remainders_l moduli_l result i product x_v y_v
    hv (by omega) PreH14 PreH15 hc hz PreH3
  rw [normalize_nonnegative_term _ _ product result (by omega) PreH19 PreH1]
  exact (prefix_indexed remainders_l moduli_l (i+1) _ PreH6 (by omega)).mpr hu

theorem proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 : chinese_remainder_theorem_entail_wit_4_2_split_goal_3 := by
  unfold chinese_remainder_theorem_entail_wit_4_2_split_goal_3
  intro moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [small_rem_cast32 _ product PreH15 PreH16] at PreH1 ⊢
  have hb := AUXLib.rem_nonneg_bounds (result + Z.rem (Z.rem (x_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product) product (by omega) (by omega)
  omega

theorem proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_4 : chinese_remainder_theorem_entail_wit_4_2_split_goal_4 := by
  unfold chinese_remainder_theorem_entail_wit_4_2_split_goal_4
  intro moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  rw [small_rem_cast32 _ product PreH15 PreH16] at PreH1 ⊢
  have hb := AUXLib.rem_nonneg_bounds (result + Z.rem (Z.rem (x_v * Z.quot product (Znth i moduli_l 0)) product * Znth i remainders_l 0) product) product (by omega) (by omega)
  omega

theorem proof_of_chinese_remainder_theorem_entail_wit_4_2 : chinese_remainder_theorem_entail_wit_4_2 := by
  unfold chinese_remainder_theorem_entail_wit_4_2
  right
  intro moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_1 moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_2 moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_3 moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | exact proof_of_chinese_remainder_theorem_entail_wit_4_2_split_goal_4 moduli_l remainders_l n_pre result i product y_v x_v retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
      | assumption
      | omega

theorem proof_of_chinese_remainder_theorem_return_wit_1_split_goal_1 : chinese_remainder_theorem_return_wit_1_split_goal_1 := by
  unfold chinese_remainder_theorem_return_wit_1_split_goal_1
  intro moduli_l remainders_l n_pre result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  refine ⟨⟨PreH16, by omega⟩, ?_⟩
  have hc := (prefix_indexed remainders_l moduli_l i result PreH3 (by omega)).mp PreH18
  intro k hk
  exact hc k (by omega)

theorem proof_of_chinese_remainder_theorem_return_wit_1 : chinese_remainder_theorem_return_wit_1 := by
  unfold chinese_remainder_theorem_return_wit_1
  right
  intro moduli_l remainders_l n_pre result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have input_valid_PreH3 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  aggressive_pre_process
  all_goals try (apply dump_spatial_left)
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_return_wit_1_split_goal_1 moduli_l remainders_l n_pre result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19))
    | exact (proof_of_chinese_remainder_theorem_return_wit_1_split_goal_1 moduli_l remainders_l n_pre result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19)
    | trivial

theorem proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 : chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 := by
  unfold chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1
  intro moduli_l remainders_l n_pre remainders_pre moduli_pre result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have input_valid_PreH13 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      simp only [INT_MAX, INT_MIN] at *
      have hb := crt_factor_quotient_bounds__product_progress remainders_l moduli_l i input_valid_PreH13 (by omega)
      dump_pre_spatial
      rw [crt_quot_div_pos__crt_transition product (Znth i moduli_l 0) (by omega) (by omega), PreH21]
      omega

theorem proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 : chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 := by
  unfold chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2
  intro moduli_l remainders_l n_pre remainders_pre moduli_pre result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have input_valid_PreH13 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      simp only [INT_MAX, INT_MIN] at *
      have hb := input_valid_PreH13.2.2.1 i (by omega)
      dump_pre_spatial
      omega

theorem proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_3 : chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_3 := by
  unfold chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_3
  intro moduli_l remainders_l n_pre remainders_pre moduli_pre result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have input_valid_PreH13 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  first
    | solve | assumption
    | solve | omega
    | solve | exact crt_unprocessed_zero_init moduli_l
    | solve | exact crt_consistent_prefix_init remainders_l moduli_l
    | solve | simp [CRTProduct, sublist, CRTConsistentPrefix, CRTProcessedCongruences, CRTUnprocessedZero, Z.modulo]
    |
      simp only [INT_MAX, INT_MIN] at *
      have hb := crt_factor_quotient_bounds__product_progress remainders_l moduli_l i input_valid_PreH13 (by omega)
      dump_pre_spatial
      omega

theorem proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure : chinese_remainder_theorem_partial_solve_wit_4_pure := by
  unfold chinese_remainder_theorem_partial_solve_wit_4_pure
  right
  intro moduli_l remainders_l n_pre remainders_pre moduli_pre result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have input_valid_PreH13 : (CRTInputValid remainders_l moduli_l) := crt_input_from_annotation _ _ (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
  aggressive_pre_process
  all_goals first
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_1 moduli_l remainders_l n_pre remainders_pre moduli_pre result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29))
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_2 moduli_l remainders_l n_pre remainders_pre moduli_pre result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29))
    | (solve | Goal_apply (proof_of_chinese_remainder_theorem_partial_solve_wit_4_pure_split_goal_3 moduli_l remainders_l n_pre remainders_pre moduli_pre result i product PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29))
    | trivial

end SimpleC.EE.LLM_bench.Algorithms.chinese_remainder_theorem.chinese_remainder_theorem_proof_manual
