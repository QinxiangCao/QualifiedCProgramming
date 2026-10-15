import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P004_1890A_doremys_paint_3_goal
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P004_1890A_doremys_paint_3_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P004_1890A_doremys_paint_3_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P004_1890A_doremys_paint_3_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩

theorem proof_of_solver_safety_wit_7_split_goal_1 : solver_safety_wit_7_split_goal_1 := by
  intro n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  unfold PaintScanState at *
  change ((cx + 1) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_7_split_goal_2 : solver_safety_wit_7_split_goal_2 := by
  intro n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  unfold PaintScanState at *
  change (((-2147483648)) <= (cx + 1))
  omega

theorem proof_of_solver_safety_wit_7 : solver_safety_wit_7 := by
  right
  intro n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_7_split_goal_1 n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_solver_safety_wit_7_split_goal_2 n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_safety_wit_10_split_goal_1 : solver_safety_wit_10_split_goal_1 := by
  intro n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dump_pre_spatial
  unfold PaintScanState at *
  change ((cy + 1) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_10_split_goal_2 : solver_safety_wit_10_split_goal_2 := by
  intro n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dump_pre_spatial
  unfold PaintScanState at *
  change (((-2147483648)) <= (cy + 1))
  omega

theorem proof_of_solver_safety_wit_10 : solver_safety_wit_10 := by
  right
  intro n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_10_split_goal_1 n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    | exact proof_of_solver_safety_wit_10_split_goal_2 n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_solver_safety_wit_11_split_goal_1 : solver_safety_wit_11_split_goal_1 := by
  intro n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  dump_pre_spatial
  unfold PaintScanState at *
  change ((cy + 1) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_11_split_goal_2 : solver_safety_wit_11_split_goal_2 := by
  intro n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  dump_pre_spatial
  unfold PaintScanState at *
  change (((-2147483648)) <= (cy + 1))
  omega

theorem proof_of_solver_safety_wit_11 : solver_safety_wit_11 := by
  right
  intro n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_11_split_goal_1 n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    | exact proof_of_solver_safety_wit_11_split_goal_2 n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_safety_wit_17_split_goal_1 : solver_safety_wit_17_split_goal_1 := by
  intro n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  unfold PaintScanState at *
  change ((cx - cy) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_17_split_goal_2 : solver_safety_wit_17_split_goal_2 := by
  intro n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  dump_pre_spatial
  unfold PaintScanState at *
  change (((-2147483648)) <= (cx - cy))
  omega

theorem proof_of_solver_safety_wit_17 : solver_safety_wit_17 := by
  right
  intro n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_17_split_goal_1 n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_solver_safety_wit_17_split_goal_2 n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_safety_wit_19_split_goal_1 : solver_safety_wit_19_split_goal_1 := by
  intro n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dump_pre_spatial
  unfold PaintScanState at *
  change ((cy - cx) <= 2147483647)
  omega

theorem proof_of_solver_safety_wit_19_split_goal_2 : solver_safety_wit_19_split_goal_2 := by
  intro n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  dump_pre_spatial
  unfold PaintScanState at *
  change (((-2147483648)) <= (cy - cx))
  omega

theorem proof_of_solver_safety_wit_19 : solver_safety_wit_19 := by
  right
  intro n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pures
  all_goals first
    | exact proof_of_solver_safety_wit_19_split_goal_1 n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    | exact proof_of_solver_safety_wit_19_split_goal_2 n_pre a_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_solver_entail_wit_1_split_goal_1 : solver_entail_wit_1_split_goal_1 := by
  intro n_pre input PreH1 PreH2 PreH3 PreH4
  exact paint_scan_state_init__scan_transitions input

theorem proof_of_solver_entail_wit_1_split_goal_2 : solver_entail_wit_1_split_goal_2 := by
  intro n_pre input PreH1 PreH2 PreH3 PreH4
  intro k hk
  exact PreH4 k (by omega)

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  right
  intro n_pre input PreH1 PreH2 PreH3 PreH4
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_1_split_goal_1 n_pre input PreH1 PreH2 PreH3 PreH4
      | exact proof_of_solver_entail_wit_1_split_goal_2 n_pre input PreH1 PreH2 PreH3 PreH4

theorem proof_of_solver_entail_wit_2_1_split_goal_1 : solver_entail_wit_2_1_split_goal_1 := by
  intro n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  exact paint_scan_state_step_x__scan_transitions input i x y cx cy (by omega) PreH1 PreH9

theorem proof_of_solver_entail_wit_2_1 : solver_entail_wit_2_1 := by
  right
  intro n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_1_split_goal_1 n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_entail_wit_2_2_split_goal_1 : solver_entail_wit_2_2_split_goal_1 := by
  intro n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have hh:=PreH9 i (by omega)
  exact paint_scan_state_step_first_y__scan_transitions input i x y cx cy (by omega) hh.1 PreH1 PreH2 PreH10

theorem proof_of_solver_entail_wit_2_2 : solver_entail_wit_2_2 := by
  right
  intro n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_2_split_goal_1 n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_solver_entail_wit_2_3_split_goal_1 : solver_entail_wit_2_3_split_goal_1 := by
  intro n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  apply paint_scan_state_step_y__scan_transitions
  all_goals solve | assumption | omega

theorem proof_of_solver_entail_wit_2_3 : solver_entail_wit_2_3 := by
  right
  intro n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_entail_wit_2_3_split_goal_1 n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_return_wit_1_split_goal_1 : solver_return_wit_1_split_goal_1 := by
  intro n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  obtain ⟨hb,hx,hcx,hcy,htot,hsent,hyx,hcxocc,hcyocc,hcover⟩:=PreH9
  have hy:=hsent.mpr PreH1
  have hall : ∀ j, (0≤j ∧ j<Zlength input) → Znth j input 0=x := by
    intro j hj
    obtain hh | ⟨hyn,_⟩ := hcover j (by omega)
    · exact hh
    · exact False.elim (hyn hy)
  refine ⟨Or.inr rfl,⟨?_,fun _ => rfl⟩⟩
  intro hh
  exact ⟨input,List.Perm.refl _,good_adjacent_sums_uniform__accepted_results input x hall⟩

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  right
  intro n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_return_wit_1_split_goal_1 n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_return_wit_2_split_goal_1 : solver_return_wit_2_split_goal_1 := by
  intro n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  refine ⟨Or.inl rfl,⟨by omega,?_⟩⟩
  rintro ⟨b,hp,hg⟩
  have hb:=paint_scan_state_full_count_balance__rejected_results input b n_pre i x y cx cy PreH6 PreH5 PreH4 PreH9 PreH3 PreH11 hp hg
  have hh:=(Z.abs_le_iff _ _).mp hb
  omega

theorem proof_of_solver_return_wit_2 : solver_return_wit_2 := by
  right
  intro n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_return_wit_2_split_goal_1 n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_return_wit_3_split_goal_1 : solver_return_wit_3_split_goal_1 := by
  intro n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  have he : i=n_pre := by omega
  rw [he] at PreH11
  obtain ⟨hb,hx,hcx,hcy,htot,hsent,hyx,hcxocc,hcyocc,hcover⟩:=PreH11
  have hyn : y≠ -1 := by intro hy;exact PreH3 (hsent.mp hy)
  have hxy : x≠y := Ne.symm (hyx hyn)
  have hcyo:=hcyocc hyn
  rw [sublist_self input n_pre PreH5] at hcxocc hcyo
  have hc : ∀ j, (0≤j ∧ j<Zlength input) → Znth j input 0=x ∨ Znth j input 0=y := by
    intro j hj
    obtain hh | ⟨_,hh⟩ := hcover j (by omega)
    · exact Or.inl hh
    · exact Or.inr hh
  refine ⟨Or.inr rfl,⟨?_,fun _ => rfl⟩⟩
  intro hh
  apply balanced_two_value_permutation__accepted_results input x y hxy hc
  all_goals unfold Occurrences at hcxocc hcyo;omega

theorem proof_of_solver_return_wit_3 : solver_return_wit_3 := by
  right
  intro n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_return_wit_3_split_goal_1 n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_return_wit_4_split_goal_1 : solver_return_wit_4_split_goal_1 := by
  intro n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  refine ⟨Or.inl rfl,⟨by omega,?_⟩⟩
  rintro ⟨b,hp,hg⟩
  have hb:=paint_scan_state_full_count_balance__rejected_results input b n_pre i x y cx cy PreH5 PreH4 PreH3 PreH8 PreH2 PreH10 hp hg
  have hh:=(Z.abs_le_iff _ _).mp hb
  omega

theorem proof_of_solver_return_wit_4 : solver_return_wit_4 := by
  right
  intro n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_return_wit_4_split_goal_1 n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_solver_return_wit_5_split_goal_1 : solver_return_wit_5_split_goal_1 := by
  intro n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  refine ⟨Or.inl rfl,⟨by omega,?_⟩⟩
  rintro ⟨b,hp,hg⟩
  obtain ⟨hb,hx,hcx,hcy,htot,hsent,hyx,hcxocc,hcyocc,hcover⟩:=PreH11
  have hxy : x≠y := Ne.symm (hyx PreH2)
  have hix : x∈input := by rw [hx];exact Znth_in_range__rejected_results input 0 0 (by omega)
  have hcy0 : cy≠0 := by intro hh;exact PreH2 (hsent.mpr hh)
  have hcyo:=hcyocc PreH2
  have hiyp : y∈sublist 0 i input := by
    by_contra hh
    have hc : (sublist 0 i input).count y=0 := List.count_eq_zero.mpr hh
    simp only [Occurrences,hc,Nat.cast_zero] at hcyo
    exact hcy0 hcyo
  have hiy:=In_sublist_from_zero__rejected_results input i y hiyp
  have hiz:=Znth_in_range__rejected_results input i 0 (by omega)
  exact False.elim (good_adjacent_sums_no_three_distinct__rejected_results input b x y (Znth i input 0) hxy (Ne.symm PreH3) (Ne.symm PreH1) hix hiy hiz hp hg)

theorem proof_of_solver_return_wit_5 : solver_return_wit_5 := by
  right
  intro n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first
      | exact proof_of_solver_return_wit_5_split_goal_1 n_pre input x y cx cy i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P004_1890A_doremys_paint_3_proof_manual
