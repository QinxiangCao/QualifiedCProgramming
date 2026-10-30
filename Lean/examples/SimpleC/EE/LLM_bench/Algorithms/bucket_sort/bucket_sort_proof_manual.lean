import SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_goal
import SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open bucket_sort_goal bucket_sort_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray


private theorem nth_property (P : Int → Prop) (l : List Int) (i : Int)
    (h : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l 0) :=
  (forall_znth__pass_transition P 0 l).mp h i hi

private theorem forall_replace (P : Int → Prop) (l : List Int) (i v : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) (hl : Forall P l) (hv : P v) : Forall P (replace_Znth i v l) := by
  apply (forall_znth__pass_transition P 0 _).mpr
  intro k hk
  rw [Zlength_replace_Znth] at hk
  by_cases he : k = i
  · subst k; rw [Znth_replace_Znth_Same 0 l i v hi]; exact hv
  · rw [Znth_replace_Znth_Diff 0 l i k v hi hk (Ne.symm he)]
    exact nth_property P l k hl hk

private theorem forall_weaken (l : List Int) (lo hi : Int) (hle : lo ≤ hi)
    (h : Forall (fun x => x ≤ lo) l) : Forall (fun x => x ≤ hi) l := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  have := h.mem hx
  omega

attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixed_seg
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg

theorem proof_of_sort_safety_wit_17 : sort_safety_wit_17 := by
  left
  intro input a_pre n_pre current counts max_value exponent i digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  prop_apply (intArray.full_Zlength (&("count")) 10 counts)
  Intros_p hlen
  have hlow0 := nth_property _ counts digit PreH12 (by omega)
  have hhigh0 := nth_property _ counts digit PreH13 (by omega)
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_sort_safety_wit_21 : sort_safety_wit_21 := by
  left
  intro input a_pre n_pre totals current digit exponent max_value histogram PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  prop_apply (intArray.full_Zlength (&("count")) 10 totals)
  Intros_p hlen
  have hlow0 := nth_property _ totals digit PreH16 (by omega)
  have hhigh0 := nth_property _ totals digit PreH17 (by omega)
  have hlow1 := nth_property _ totals (digit-1) PreH16 (by omega)
  have hhigh1 := nth_property _ totals (digit-1) PreH17 (by omega)
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_sort_entail_wit_1 : sort_entail_wit_1 := by
  left
  intro input a_pre n_pre PreH1 PreH2 PreH3 PreH4 PreH5
  prop_apply (intArray.full_Zlength a_pre n_pre input)
  Intros_p hlen
  have hlo := nth_property _ input 0 PreH4 (by omega)
  have hhi := nth_property _ input 0 PreH5 (by omega)
  have hp : PrefixMaximum input 1 (Znth 0 input 0) := by
    refine ⟨⟨0,by omega,rfl⟩,?_⟩
    intro k hk
    have he : k=0 := by omega
    subst k; omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_2_1 : sort_entail_wit_2_1 := by
  left
  intro input a_pre n_pre max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  prop_apply (intArray.full_Zlength a_pre n_pre input)
  Intros_p hlen
  have hlo := nth_property _ input i PreH9 (by omega)
  have hhi := nth_property _ input i PreH10 (by omega)
  have hp := prefix_maximum_extend_greater__maximum_pass_entry input i max_value (by omega) PreH11 PreH1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_2_2 : sort_entail_wit_2_2 := by
  left
  intro input a_pre n_pre max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  prop_apply (intArray.full_Zlength a_pre n_pre input)
  Intros_p hlen
  have hlo := nth_property _ input i PreH9 (by omega)
  have hhi := nth_property _ input i PreH10 (by omega)
  have hp := prefix_maximum_extend_bounded__maximum_pass_entry input i max_value PreH11 PreH1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_3 : sort_entail_wit_3 := by
  left
  intro input a_pre n_pre max_value i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have he : i = n_pre := by omega
  subst i
  have hd : DecimalExponent 1 := ⟨0,by decide,rfl⟩
  have hp : RadixPassState input input 1 := by
    refine ⟨List.Perm.refl _,?_⟩
    intro x y hxy
    simp only [Z.modulo,Int.fmod_one]
    omega
  Exists input
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_4 : sort_entail_wit_4 := by
  right
  intro input n_pre current_2 exponent max_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have hb : exponent ≤ 100000000 := by
    apply decimal_exponent_active_bound__maximum_pass_entry exponent max_value <;> assumption
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact Forall.nil

theorem proof_of_sort_entail_wit_5 : sort_entail_wit_5 := by
  right
  intro input n_pre zero_prefix_2 current_2 digit exponent max_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hz : Forall (Eq (0 : Int)) (zero_prefix_2 ++ [0]) := by
    apply Forall.iff_forall_mem.mpr
    intro x hx
    rcases List.mem_append.mp hx with h | h
    · exact PreH13.mem h
    · have he : x = 0 := by simpa using h
      exact he.symm
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> assumption

theorem proof_of_sort_entail_wit_6 : sort_entail_wit_6 := by
  left
  intro input a_pre n_pre zero_prefix current_2 digit exponent max_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16
  have hz : digit = 10 := by omega
  subst digit
  have hlo : Forall (fun x : Int => 0 ≤ x) zero_prefix := by
    apply Forall.iff_forall_mem.mpr
    intro x hx; have := PreH13.mem hx; omega
  have hhi : Forall (fun x : Int => x ≤ 0) zero_prefix := by
    apply Forall.iff_forall_mem.mpr
    intro x hx; have := PreH13.mem hx; omega
  prop_apply (intArray.seg_Zlength (&("count")) 0 10 zero_prefix)
  Intros_p hlen
  have hh := digit_histogram_prefix_zero__count_zero_init current_2 exponent zero_prefix (by
    intro d hd; have := nth_property _ zero_prefix d PreH13 (by omega); omega)
  Exists zero_prefix current_2
  split_pure_spatial
  · sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp (intArray.undef_seg_empty (&("count")) 10)).1)
    sep_apply (intArray.seg_to_full (&("count")) 0 10 zero_prefix)
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_7 : sort_entail_wit_7 := by
  left
  intro input a_pre n_pre counts_2 current i exponent max_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  prop_apply (intArray.full_Zlength a_pre n_pre current)
  Intros_p hlen
  have hv := nth_property _ current i PreH11 (by omega)
  have hd := c_radix_digit_range__stable_placement _ exponent hv (by omega)
  Exists counts_2 current
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_sort_entail_wit_8 : sort_entail_wit_8 := by
  left
  intro input a_pre n_pre current_2 counts_2 max_value exponent i digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  prop_apply (intArray.full_Zlength a_pre n_pre current_2)
  Intros_p hlen
  prop_apply (intArray.full_Zlength (&("count")) 10 (replace_Znth digit (Znth digit counts_2 0+1) counts_2))
  Intros_p hc
  simp only [Zlength_replace_Znth] at hc
  have hv := nth_property _ current_2 i PreH10 (by omega)
  have hd := radix_digit_c_bridge__stable_placement _ exponent hv (by omega)
  have he : RadixDigit (Znth i current_2 0) exponent = digit := by omega
  have hh := digit_histogram_prefix_step__histogram_update current_2 exponent i counts_2 (by omega) hc (by omega) PreH17
  rw [he] at hh
  have hlow := nth_property _ counts_2 digit PreH12 (by omega)
  have hhigh := nth_property _ counts_2 digit PreH13 (by omega)
  have hlo := forall_replace (fun x : Int => 0 ≤ x) counts_2 digit (Znth digit counts_2 0+1) (by omega) PreH12 (by omega)
  have hhi := forall_replace (fun x : Int => x ≤ i+1) counts_2 digit (Znth digit counts_2 0+1) (by omega) (forall_weaken _ i (i+1) (by omega) PreH13) (by omega)
  Exists (replace_Znth digit (Znth digit counts_2 0+1) counts_2) current_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_9 : sort_entail_wit_9 := by
  left
  intro input a_pre n_pre counts current_2 i exponent max_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  prop_apply (intArray.full_Zlength (&("count")) 10 counts)
  Intros_p hc
  have he : i = n_pre := by omega
  subst i
  have hp := digit_prefix_totals_init__prefix_totals counts hc
  Exists counts current_2 counts
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_10 : sort_entail_wit_10 := by
  left
  intro input a_pre n_pre totals_2 current_2 digit exponent max_value histogram_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  prop_apply (intArray.full_Zlength a_pre n_pre current_2)
  Intros_p hlen
  prop_apply (intArray.full_Zlength (&("count")) 10 (replace_Znth digit (Znth digit totals_2 0+Znth (digit-1) totals_2 0) totals_2))
  Intros_p ht
  simp only [Zlength_replace_Znth] at ht
  have hstep := digit_prefix_totals_step__prefix_totals histogram_2 totals_2 digit PreH4 ht (by omega) PreH22
  have hm := digit_histogram_prefix_mass_bound__prefix_totals current_2 exponent n_pre histogram_2 digit (by omega) PreH4 PreH21 (by omega)
  have hv : 0 ≤ Znth digit totals_2 0 + Znth (digit-1) totals_2 0 ∧ Znth digit totals_2 0 + Znth (digit-1) totals_2 0 ≤ n_pre := by
    have he := (hstep digit (by omega)).1 (by omega)
    rw [Znth_replace_Znth_Same 0 totals_2 digit _ (by omega)] at he
    omega
  have hlo := forall_replace (fun x : Int => 0 ≤ x) totals_2 digit _ (by omega) PreH16 hv.1
  have hhi := forall_replace (fun x : Int => x ≤ n_pre) totals_2 digit _ (by omega) PreH17 hv.2
  Exists (replace_Znth digit (Znth digit totals_2 0+Znth (digit-1) totals_2 0) totals_2) current_2 histogram_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_sort_entail_wit_11 : sort_entail_wit_11 := by
  left
  intro input a_pre n_pre totals current_2 digit exponent max_value histogram_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  prop_apply (intArray.full_Zlength a_pre n_pre current_2)
  Intros_p hlen
  prop_apply (intArray.full_Zlength (&("count")) 10 totals)
  Intros_p ht
  have he : digit = 10 := by omega
  subst digit
  have hhist : DigitHistogramPrefix current_2 exponent (Zlength current_2) histogram_2 := by simpa only [hlen] using PreH21
  have hp := bucket_placement_initial__stable_placement current_2 exponent histogram_2 totals PreH4 ht hhist PreH22
  have hp' : BucketPlacementProgress current_2 exponent (n_pre-1+1) histogram_2 totals (List.replicate 1000 none) := by simpa only [hlen,Int.sub_add_cancel] using hp
  Exists (List.replicate 1000 (none : Option Int)) totals current_2 histogram_2
  split_pure_spatial
  · refine naive_C_Rules.toContext.derivable1_trans _
      ((intArray.full a_pre n_pre current_2 ** intArray.full (&("count")) 10 totals) ** intArray.undef_full (&("output")) 1000) _ ?_ ?_
    · cancel
    · exact naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _
        (naive_C_Rules.toContext.derivable1_refl _)
        (intArray.undef_full_to_mixed_full (&("output")) 1000)
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_12 : sort_entail_wit_12 := by
  left
  intro input a_pre n_pre mixed_output_2 counters_2 current i exponent max_value histogram_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  prop_apply (intArray.full_Zlength a_pre n_pre current)
  Intros_p hlen
  prop_apply (intArray.full_Zlength (&("count")) 10 counters_2)
  Intros_p hc
  have hv := nth_property _ current i PreH12 (by omega)
  have hd := c_radix_digit_range__stable_placement _ exponent hv (by omega)
  have bridge := radix_digit_c_bridge__stable_placement _ exponent hv (by omega)
  have hhist : DigitHistogramPrefix current exponent (Zlength current) histogram_2 := by simpa only [hlen] using PreH21
  have hl := bucket_progress_counter_for_index__stable_placement current exponent (i+1) histogram_2 counters_2 mixed_output_2 i PreH4 hhist PreH22 (by omega) (by omega) (by rw [bridge]; exact hd)
  rw [bridge] at hl
  have hu := nth_property _ counters_2 (Z.rem (Z.quot (Znth i current 0) exponent) 10) PreH17 (by omega)
  sep_apply (intArray.full_split_to_missing_i (&("count")) (Z.rem (Z.quot (Znth i current 0) exponent) 10) 10 counters_2 0 (by omega))
  asrt_simpl
  Intros
  Exists mixed_output_2 counters_2 current histogram_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl | trivial

theorem proof_of_sort_entail_wit_13 : sort_entail_wit_13 := by
  left
  intro input a_pre n_pre current_2 histogram_2 counters_2 mixed_output_2 max_value exponent i digit PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  prop_apply (intArray.full_Zlength a_pre n_pre current_2)
  Intros_p hlen
  prop_apply (intArray.full_Zlength (&("count")) 10 (replace_Znth digit (Znth digit counters_2 0-1) counters_2))
  Intros_p hc
  simp only [Zlength_replace_Znth] at hc
  have hv := nth_property _ current_2 i PreH11 (by omega)
  have hd := radix_digit_c_bridge__stable_placement _ exponent hv (by omega)
  have he : RadixDigit (Znth i current_2 0) exponent = digit := by omega
  have hhist : DigitHistogramPrefix current_2 exponent (Zlength current_2) histogram_2 := by simpa only [hlen] using PreH20
  have hwrite : Znth digit (replace_Znth digit (Znth digit counters_2 0-1) counters_2) 0 = Znth digit counters_2 0-1 := Znth_replace_Znth_Same 0 counters_2 digit _ (by omega)
  have hp := bucket_placement_step__stable_placement current_2 exponent histogram_2 counters_2 mixed_output_2 i PreH3 hc (by omega) (by omega) hhist PreH21
  simp only [he,hwrite] at hp
  have hnext := hp (by omega)
  have hnext' : BucketPlacementProgress current_2 exponent (i-1+1) histogram_2 (replace_Znth digit (Znth digit counters_2 0-1) counters_2) (replace_Znth (Znth digit counters_2 0-1) (some (Znth i current_2 0)) mixed_output_2) := by simpa only [Int.sub_add_cancel] using hnext
  have hlo := forall_replace (fun x : Int => 0 ≤ x) counters_2 digit (Znth digit counters_2 0-1) (by omega) PreH15 (by omega)
  have hhi := forall_replace (fun x : Int => x ≤ n_pre) counters_2 digit (Znth digit counters_2 0-1) (by omega) PreH16 (by omega)
  Exists (replace_Znth (Znth digit counters_2 0-1) (some (Znth i current_2 0)) mixed_output_2) (replace_Znth digit (Znth digit counters_2 0-1) counters_2) current_2 histogram_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_sort_entail_wit_14 : sort_entail_wit_14 := by
  left
  intro input a_pre n_pre mixed_output counters current_2 i exponent max_value histogram PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  prop_apply (intArray.full_Zlength a_pre n_pre current_2)
  Intros_p hlen
  have he : i = -1 := by omega
  subst i
  have hhist : DigitHistogramPrefix current_2 exponent (Zlength current_2) histogram := by simpa only [hlen] using PreH21
  have hd : ∀ k, (0 ≤ k ∧ k < Zlength current_2) → 0 ≤ RadixDigit (Znth k current_2 0) exponent ∧ RadixDigit (Znth k current_2 0) exponent < 10 := by
    intro k hk
    have hv := nth_property _ current_2 k PreH12 hk
    rw [radix_digit_c_bridge__stable_placement _ exponent hv (by omega)]
    exact c_radix_digit_range__stable_placement _ exponent hv (by omega)
  have hcomplete := bucket_placement_complete__stable_placement current_2 exponent histogram counters mixed_output PreH4 (by omega) hhist hd PreH22
  have hperm := radix_stable_output_permutation__stable_placement current_2 exponent hd
  have hlo := PreH12.perm hperm
  have hhi := PreH13.perm hperm
  have hpass : StableDigitPass current_2 (RadixStableOutput current_2 exponent) exponent := rfl
  have hcopy := radix_copy_prefix_zero__copy_back current_2 (RadixStableOutput current_2 exponent)
  Exists counters current_2 (RadixStableOutput current_2 exponent) current_2
  split_pure_spatial
  · sep_apply (intArray.mixed_full_split_to_mixed_seg (&("output")) n_pre 1000 mixed_output (by omega))
    have hp : sublist 0 n_pre mixed_output = List.map some (RadixStableOutput current_2 exponent) := by simpa only [hlen] using hcomplete.2
    rw [hp]
    sep_apply (intArray.mixed_seg_to_seg (&("output")) 0 n_pre (RadixStableOutput current_2 exponent))
    sep_apply (intArray.mixed_seg_to_undef_seg (&("output")) n_pre 1000 (sublist n_pre 1000 mixed_output))
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_entail_wit_15 : sort_entail_wit_15 := by
  left
  intro input a_pre n_pre bucket_starts_2 working_2 pass_output_2 i exponent max_value current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  simp only [Int.sub_zero]
  prop_apply (intArray.full_Zlength a_pre n_pre (replace_Znth i (Znth i pass_output_2 0) working_2))
  Intros_p hlen
  simp only [Zlength_replace_Znth] at hlen
  have hp := radix_copy_prefix_step__copy_back current_2 pass_output_2 working_2 i (by omega) (by omega) PreH17
  Exists bucket_starts_2 (replace_Znth i (Znth i pass_output_2 0) working_2) pass_output_2 current_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | rfl

theorem proof_of_sort_entail_wit_16 : sort_entail_wit_16 := by
  left
  intro input a_pre n_pre bucket_starts working pass_output i exponent max_value current_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  prop_apply (intArray.full_Zlength a_pre n_pre working)
  Intros_p hw
  prop_apply (intArray.seg_Zlength (&("output")) 0 n_pre pass_output)
  Intros_p ho
  have he : working = pass_output := by
    apply (ListLib.list_eq_ext working pass_output 0).mpr
    constructor
    · change Zlength working = Zlength pass_output
      omega
    · change ∀ k, 0 ≤ k ∧ k < Zlength working → Znth k working 0 = Znth k pass_output 0
      intro k hk
      exact PreH17.1 k (by omega)
  subst working
  have hp : RadixPassState input pass_output (exponent*10) :=
    ⟨PreH15.1.trans (stable_digit_pass_permutation__pass_transition current_2 pass_output exponent PreH16),
      stable_digit_pass_next_order__pass_transition current_2 pass_output exponent (by omega) PreH15.2 PreH16⟩
  have hd := decimal_exponent_next__pass_transition exponent PreH14 PreH8
  have hout : intArray.seg (&("output")) 0 n_pre pass_output ** intArray.undef_seg (&("output")) n_pre 1000 |-- intArray.undef_full (&("output")) 1000 := by
    refine naive_C_Rules.toContext.derivable1_trans _ (intArray.undef_seg (&("output")) 0 n_pre ** intArray.undef_seg (&("output")) n_pre 1000) _ ?_ ?_
    · exact naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _ (intArray.seg_to_undef_seg (&("output")) 0 n_pre pass_output) (naive_C_Rules.toContext.derivable1_refl _)
    · simpa only [Int.zero_mul,Int.add_zero,Int.sub_zero] using intArray.undef_seg_merge_to_undef_full (&("output")) 0 n_pre 1000 (by omega)
  Exists pass_output
  split_pure_spatial
  · sep_apply hout
    sep_apply (intArray.full_to_undef_full (&("count")) 10 bucket_starts)
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_sort_return_wit_1 : sort_return_wit_1 := by
  left
  intro input a_pre n_pre PreH1 PreH2 PreH3 PreH4 PreH5
  prop_apply (intArray.full_Zlength a_pre n_pre input)
  Intros_p hlen
  have hs := increasing_short_list__final_result input (by omega)
  Exists input
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | exact List.Perm.refl _

theorem proof_of_sort_return_wit_2 : sort_return_wit_2 := by
  left
  intro input a_pre n_pre current exponent max_value PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  prop_apply (intArray.full_Zlength a_pre n_pre current)
  Intros_p hlen
  have hi : Zlength input = n_pre := by
    have hp : Zlength input = Zlength current := congrArg Int.ofNat PreH12.1.length_eq
    omega
  have hs := radix_pass_state_final_increasing__final_result input current n_pre exponent max_value hi hlen (by omega) PreH4 PreH1
    (fun k hk => nth_property _ current k PreH8 (by omega)) PreH10 PreH12
  have hp := PreH12.1
  Exists current
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> assumption

end SimpleC.EE.LLM_bench.Algorithms.bucket_sort.bucket_sort_proof_manual
