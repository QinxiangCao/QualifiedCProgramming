import SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_goal
import SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_proof_auto

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open huffman_encoding_goal huffman_encoding_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem forall_nth (P : Int → Prop) (l : List Int) (h : Forall P l)
    (i : Int) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l 0) := by
  induction h generalizing i with
  | nil => simp [Zlength] at hi; omega
  | @cons x xs hx hs ih =>
    by_cases hz : i=0
    · subst i; simpa only [Znth0_cons] using hx
    · rw [Znth_cons 0 i x xs (by omega)]
      apply ih (i-1)
      rw [Zlength_cons] at hi; omega

private theorem input_bounds (l : List Int) (hl : Forall (fun x => 1 ≤ x) l)
    (hu : Forall (fun x => x ≤ 1000) l) : HuffmanInputBounded l := by
  intro i hi
  exact ⟨forall_nth _ l hl i hi, forall_nth _ l hu i hi⟩

private theorem prefix_len (l : List Int) (n : Int) (hn : 0 ≤ n ∧ n ≤ Zlength l) :
    Zlength (sublist 0 n l) = n := by
  unfold Zlength
  rw [sublist_length 0 n l (by omega) (by omega)]
  simp only [Int.sub_zero, Int.ofNat_eq_coe, Int.toNat_of_nonneg hn.1]

private theorem live_bounds (l : List Int) (n : Int) (hn : 0 ≤ n ∧ n ≤ Zlength l)
    (hl : Forall (fun x => 1 ≤ x) (sublist 0 n l))
    (hu : Forall (fun x => x ≤ 8000) (sublist 0 n l)) :
    ∀ i, (0 ≤ i ∧ i < n) → 1 ≤ Znth i l 0 ∧ Znth i l 0 ≤ 8000 := by
  intro i hi
  have hlen := prefix_len l n hn
  have hl' := forall_nth _ (sublist 0 n l) hl i (by omega)
  have hu' := forall_nth _ (sublist 0 n l) hu i (by omega)
  rw [Znth_sublist 0 0 i n l (by omega) (by omega)] at hl' hu'
  simpa only [Int.add_zero] using And.intro hl' hu'

private theorem prefix_bounds (l : List Int) (n : Int) (hn : 0 ≤ n ∧ n ≤ Zlength l)
    (h : ∀ i, (0 ≤ i ∧ i < n) → 1 ≤ Znth i l 0 ∧ Znth i l 0 ≤ 8000) :
    Forall (fun x => 1 ≤ x) (sublist 0 n l) ∧ Forall (fun x => x ≤ 8000) (sublist 0 n l) := by
  constructor
  all_goals apply Forall.iff_forall_mem.mpr
  all_goals intro x hx
  all_goals obtain ⟨i,hi,he⟩ := in_sublist0_has_index__removals_bounds Int l 0 x n hn hx
  · simpa only [he] using (h i hi).1
  · simpa only [he] using (h i hi).2

theorem proof_of_huffman_cost_entail_wit_1 : huffman_cost_entail_wit_1 := by
  unfold huffman_cost_entail_wit_1
  right
  intro n_pre weights_l PreH1 PreH2 PreH3 low high
  refine Automation.exp_right_rule (CRules := naive_C_Rules) weights_l ?_
  split_pure_spatial
  · sep_apply (intArray.undef_full_split_to_undef_seg &("work") n_pre 8 ⟨by omega,by omega⟩)
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega

theorem proof_of_huffman_cost_entail_wit_2 : huffman_cost_entail_wit_2 := by
  unfold huffman_cost_entail_wit_2
  right
  intro n_pre weights_l i copied_2 remaining_2 PreH1 PreH2 PreH3 PreH4 low high PreH6 PreH7 PreH8 PreH9
  cases remaining_2 with
  | nil =>
    simp only [List.append_nil] at PreH6
    rw [PreH6] at PreH4
    omega
  | cons next tail =>
    have he : Znth (Zlength copied_2) (copied_2++next::tail) 0 = next := by
      rw [app_Znth2 0 copied_2 (next::tail) _ (le_refl _)]
      simp only [Int.sub_self, Znth0_cons]
    refine Automation.exp_right_rule (CRules := naive_C_Rules) tail ?_
    rw [he]
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial
      all_goals first
        | assumption
        | simp only [List.append_assoc, List.cons_append, List.nil_append]
        | rw [Zlength_app, Zlength_cons, Zlength_nil]; omega
        | rw [← PreH6]; omega
        | omega

theorem proof_of_huffman_cost_entail_wit_3 : huffman_cost_entail_wit_3 := by
  unfold huffman_cost_entail_wit_3
  right
  intro n_pre weights_l i copied remaining PreH1 PreH2 PreH3 PreH4 low high PreH6 PreH7 PreH8 PreH9
  let work_pre : Int := &("work")
  have PreH5 := input_bounds weights_l low high
  have hei : i = n_pre := by omega
  have hr : remaining = [] := by
    have hh := congrArg Zlength PreH6
    rw [Zlength_app] at hh
    have hz : Zlength remaining = 0 := by omega
    cases remaining with
    | nil => rfl
    | cons a l => rw [Zlength_cons] at hz; have := Zlength_nonneg l; omega
  rw [hr, List.append_nil] at PreH6
  rw [← PreH6, hei]
  have hb := huffman_input_live_bounds__copy_initialization weights_l n_pre PreH4 PreH5
  have hp : HuffmanProgress weights_l weights_l n_pre 0 := by
    rw [← PreH4]; exact huffman_initial_progress__copy_initialization weights_l (by omega) PreH5
  refine Automation.exp_right_rule (CRules := naive_C_Rules) weights_l ?_
  split_pure_spatial
  · sep_apply (intArray.seg_to_full work_pre 0 n_pre weights_l)
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (rw [sublist_self weights_l n_pre (by omega)]; apply Forall.iff_forall_mem.mpr; intro x hx; first | (have h := low.mem hx; omega) | (have h := high.mem hx; omega))

theorem proof_of_huffman_cost_entail_wit_4 : huffman_cost_entail_wit_4 := by
  unfold huffman_cost_entail_wit_4
  right
  pre_process
  have hp := huffman_min_scan_init__min_scan_updates work_l_2
  entailer!

theorem proof_of_huffman_cost_entail_wit_6_1 : huffman_cost_entail_wit_6_1 := by
  unfold huffman_cost_entail_wit_6_1
  right
  pre_process
  have hp := huffman_min_scan_take_new__min_scan_updates work_l_2 i first PreH24 PreH1
  entailer!

theorem proof_of_huffman_cost_entail_wit_6_2 : huffman_cost_entail_wit_6_2 := by
  unfold huffman_cost_entail_wit_6_2
  right
  pre_process
  have hp := huffman_min_scan_keep_old__min_scan_updates work_l_2 i first PreH24 PreH1
  entailer!

theorem proof_of_huffman_cost_entail_wit_8_1 : huffman_cost_entail_wit_8_1 := by
  unfold huffman_cost_entail_wit_8_1
  right
  pre_process
  have hp := huffman_min_scan_take_new__min_scan_updates work_l_2 i second PreH26 PreH1
  entailer!

theorem proof_of_huffman_cost_entail_wit_8_2 : huffman_cost_entail_wit_8_2 := by
  unfold huffman_cost_entail_wit_8_2
  right
  pre_process
  have hp := huffman_min_scan_keep_old__min_scan_updates work_l_2 i second PreH26 PreH1
  entailer!

theorem proof_of_huffman_cost_entail_wit_7 : huffman_cost_entail_wit_7 := by
  unfold huffman_cost_entail_wit_7
  right
  pre_process
  have hi : i=active := by omega
  have hlive := live_bounds work_l active (by omega) PreH18 PreH19
  have hb := prefix_bounds (replace_Znth first (Znth (active-1) work_l 0) work_l) (active-1)
    (by rw [Zlength_replace_Znth]; omega)
    (replace_last_live_bounds__removals_bounds work_l first active 1 8000 (by omega) (by omega) hlive)
  have hh := huffman_first_held_after_removal__removals_bounds weights_l work_l first active total
    (by omega) (by omega) (by simpa only [hi] using PreH21) PreH20
  have hs := huffman_min_scan_init__min_scan_updates (replace_Znth first (Znth (active-1) work_l 0) work_l)
  have hx := hlive first (by omega)
  entailer!
  all_goals first | assumption | (simp only [Zlength_replace_Znth]; omega) | omega

theorem proof_of_huffman_cost_entail_wit_9 : huffman_cost_entail_wit_9 := by
  unfold huffman_cost_entail_wit_9
  right
  pre_process
  have hlive := live_bounds work_l_2 active (by omega) PreH22 PreH23
  have hinput := input_bounds weights_l PreH6 PreH7
  have hc := huffman_residual_charge_bounds__removals_bounds weights_l work_l_2 active x second total n_pre
    PreH4 PreH5 (by omega) hinput (by omega) (by omega) PreH18 PreH24
  have hy := hlive second (by omega)
  let rem := replace_Znth second (Znth (active-1) work_l_2 0) work_l_2
  have hlrem : Zlength rem = n_pre := (Zlength_replace_Znth work_l_2 second _).trans PreH5
  have hlraw : (rem.length : Int) = n_pre := hlrem
  have hrbound := replace_last_live_bounds__removals_bounds work_l_2 second active 1 8000 (by omega) (by omega) hlive
  have hpair := huffman_pair_ready_after_removal__removals_bounds weights_l work_l_2 active x second total i n_pre PreH5 (by omega) (by omega) (by omega) PreH24 PreH25
  have hp := huffman_progress_after_merge__merge_transition weights_l rem (active-1) x (Znth second work_l_2 0) total
    (by omega) hpair
  have hnew : ∀ k, (0 ≤ k ∧ k < active) →
      1 ≤ Znth k (replace_Znth (active-1) (x+Znth second work_l_2 0) rem) 0 ∧
      Znth k (replace_Znth (active-1) (x+Znth second work_l_2 0) rem) 0 ≤ 8000 := by
    intro k hk
    by_cases he : k=active-1
    · subst k
      rw [Znth_replace_Znth_Same 0 rem (active-1) _ (by omega)]
      omega
    · rw [Znth_replace_Znth_Diff 0 rem (active-1) k _ (by omega) (by omega) (Ne.symm he)]
      exact hrbound k (by omega)
  obtain ⟨hb0, hb1⟩ := prefix_bounds _ active (by rw [Zlength_replace_Znth]; omega) hnew
  entailer!
  all_goals first | (simpa only [Int.sub_add_cancel, Int.add_assoc] using hp) | (simpa only [Int.sub_add_cancel] using hb0) | (simpa only [Int.sub_add_cancel] using hb1) | assumption | omega | (simp only [Zlength_replace_Znth]; omega)

theorem proof_of_huffman_cost_entail_wit_10 : huffman_cost_entail_wit_10 := by
  unfold huffman_cost_entail_wit_10
  right
  pre_process
  have he : active=1 := by omega
  have ho : HuffmanOptimalCost weights_l total := by
    obtain ⟨hs,remaining,hr,hi⟩ := PreH14
    rw [he, sublist_zero_one__final_result work_l (by omega)] at hr
    have hz := huffman_singleton_optimal_zero__final_result _ remaining hr
    simpa only [hz, Int.add_zero] using hi
  sep_apply (intArray.full_to_undef_full &("work") n_pre work_l)
  sep_apply (intArray.undef_full_to_undef_seg &("work") n_pre)
  sep_apply (intArray.undef_seg_merge_to_undef_full &("work") 0 n_pre 8 ⟨by omega,by omega⟩)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  entailer!

theorem proof_of_huffman_cost_safety_wit_15 : huffman_cost_safety_wit_15 := by
  pre_process
  have hlive := live_bounds work_l active (by omega) PreH22 PreH23
  have hy := hlive second (by omega)
  have hinput := input_bounds weights_l PreH6 PreH7
  have hc := huffman_residual_charge_bounds__removals_bounds weights_l work_l active x second total n_pre
    PreH4 PreH5 (by omega) hinput (by omega) (by omega) PreH18 PreH24
  entailer!
  all_goals simp only [INT_MIN,INT_MAX] at *
  all_goals omega

theorem proof_of_huffman_cost_safety_wit_16 : huffman_cost_safety_wit_16 := by
  pre_process
  have hlive := live_bounds work_l active (by omega) PreH22 PreH23
  have hy := hlive second (by omega)
  have hinput := input_bounds weights_l PreH6 PreH7
  have hc := huffman_residual_charge_bounds__removals_bounds weights_l work_l active x second total n_pre
    PreH4 PreH5 (by omega) hinput (by omega) (by omega) PreH18 PreH24
  entailer!
  all_goals simp only [INT_MIN,INT_MAX] at *
  all_goals omega

end SimpleC.EE.LLM_bench.Algorithms.huffman_encoding.huffman_encoding_proof_manual
