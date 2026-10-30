import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_goal
import SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 600
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open P047_1523C_compression_and_expansion_goal P047_1523C_compression_and_expansion_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem split_cell (ptr i n : Int) (cells : List (Option Int)) (default : Option Int) (v : Int)
    (hi : 0≤i ∧ i<n) (hv : Znth i cells default=some v) :
    intArray.mixed_full ptr n cells |-- ((ptr+i*sizeof(INT)) # Int |-> v) ** intArray.mixed_missing_i ptr i 0 n cells := by
  have h := intArray.mixed_full_split_to_mixed_missing_i ptr i n cells default hi
  rw [hv] at h
  exact h

private theorem merge_cell (ptr i n : Int) (cells : List (Option Int)) (v : Int) (hi : 0≤i ∧ i<n) :
    (((ptr+i*sizeof(INT)) # Int |-> v) ** intArray.mixed_missing_i ptr i 0 n cells) |--
      intArray.mixed_full ptr n (replace_Znth i (some v) cells) := by
  exact intArray.mixed_missing_i_merge_to_mixed_full ptr i n (some v) cells hi

theorem proof_of_solver_safety_wit_7_split_goal_1 : solver_safety_wit_7_split_goal_1 := by
  unfold solver_safety_wit_7_split_goal_1
  intro last_numbers values_pre n_pre flat_pre lengths_pre cells lengths_data flat_data total active depth target x line items __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  dump_pre_spatial
  have h := BoundedItem_Znth n_pre active (depth-1) PreH18 (by omega)
  simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_solver_safety_wit_7_split_goal_2 : solver_safety_wit_7_split_goal_2 := by
  unfold solver_safety_wit_7_split_goal_2
  intro last_numbers values_pre n_pre flat_pre lengths_pre cells lengths_data flat_data total active depth target x line items __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  dump_pre_spatial
  have h := BoundedItem_Znth n_pre active (depth-1) PreH18 (by omega)
  simp only [INT_MAX,INT_MIN]
  omega

theorem proof_of_solver_safety_wit_7 : solver_safety_wit_7 := by
  unfold solver_safety_wit_7
  right
  intro last_numbers values_pre n_pre flat_pre lengths_pre cells lengths_data flat_data total active depth target x line items __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  split_pures
  · exact proof_of_solver_safety_wit_7_split_goal_1 last_numbers values_pre n_pre flat_pre lengths_pre cells lengths_data flat_data total active depth target x line items __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  · exact proof_of_solver_safety_wit_7_split_goal_2 last_numbers values_pre n_pre flat_pre lengths_pre cells lengths_data flat_data total active depth target x line items __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro last_numbers n_pre __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5
  obtain ⟨items,hitems⟩ := PreH4.2.2
  have hs : Spec last_numbers items := hitems
  have hlen : Zlength (List.replicate 1005 (none : Option Int))=1005 := by simp only [Zlength,List.length_replicate]; rfl
  have hilen := hitems.1
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (List.replicate 1005 (none : Option Int)) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) ([] : List Int) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) items ?_
  split_pure_spatial
  · exact intArray.undef_full_to_mixed_full _ _
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | (exact BoundedItem_nil _) | (exact Or.inl ⟨rfl,rfl⟩) |
      (intro k hk; have h:=PreH3 k (by omega); omega) |
      (unfold FlatPrefix; rw [Zsublist_nil _ 0 0 (le_refl _)]; rfl) |
      (exact ⟨rfl,fun k hk=>by omega⟩)
    all_goals have hl := hitems.1; omega

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro last_numbers n_pre cells_2 lengths_data_2 flat_data_2 total active_2 depth line items_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  rcases Spec_nonone_pop__semantic_transitions last_numbers items_2 active_2 line PreH8 PreH15 (by omega) PreH1 with ⟨hline,hpop⟩
  have hd : 1≤depth := by
    rcases hpop with ⟨pre,last,suf,he,rest⟩
    rw [he,Zlength_app,Zlength_cons] at PreH14
    have h1:=Zlength_nonneg pre
    have h2:=Zlength_nonneg suf
    omega
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cells_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) active_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) items_2 ?_
  have hc := PreH23 (depth-1) (by omega)
  sep_apply (split_cell (&("stack")) (depth-1) 1005 cells_2 __default__App_option_Z _ (by omega) hc)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first | assumption | rfl | omega | tauto

theorem proof_of_solver_entail_wit_4 : solver_entail_wit_4 := by
  unfold solver_entail_wit_4
  right
  intro last_numbers n_pre cells_2 lengths_data_2 flat_data_2 total active_2 depth target_2 x line items_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  rcases PopTarget_remove_last__semantic_transitions n_pre active_2 target_2 x PreH21 PreH20 (by rw [←PreH19]; exact PreH3) with ⟨hlen,hrlen,hpop,hbound,hprefix⟩
  have hpop' : PopTarget active_2.dropLast (Znth line items_2 []) x := by rw [←PreH16]; exact hpop
  have hc : ∀k,(0≤k ∧ k<depth-1) → Znth k cells_2 __default__App_option_Z=some (Znth k active_2.dropLast 0) := by
    intro k hk
    rw [hprefix k (by omega)]
    exact PreH28 k (by omega)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) cells_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) active_2.dropLast ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) items_2 ?_
  sep_apply (merge_cell (&("stack")) (depth-1) 1005 cells_2 (Znth (depth-1) active_2 0) (by omega))
  change Znth (depth-1) cells_2 __default__App_option_Z=some (Znth (depth-1) active_2 0) at PreH29
  rw [←PreH29,replace_Znth_Znth]
  sep_apply (split_cell (&("stack")) (depth-1-1) 1005 cells_2 __default__App_option_Z _ (by omega) (hc _ (by omega)))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | omega | tauto | (exact hc _ (by omega))

theorem proof_of_solver_entail_wit_5_1 : solver_entail_wit_5_1 := by
  unfold solver_entail_wit_5_1
  right
  intro last_numbers n_pre cells_2 lengths_data_2 flat_data_2 total active_2 depth line items_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  have ha := Spec_one_append__semantic_transitions n_pre last_numbers items_2 active_2 line PreH8 PreH15 (by omega) PreH16 PreH3 PreH1
  rcases stack_append_one_invariant__semantic_transitions cells_2 active_2 depth __default__App_option_Z PreH14 (by omega) PreH23 with ⟨hlen,hcells⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) items_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega |
      (rw [ha,Zlength_app,Zlength_cons,Zlength_nil]; omega) |
      (rw [ha,←PreH5]; exact BoundedItem_append_one n_pre active_2 PreH3 PreH16) |
      (rw [←PreH14]; omega) |
      (rw [ha,←PreH14]; exact hcells)

theorem proof_of_solver_entail_wit_5_2 : solver_entail_wit_5_2 := by
  unfold solver_entail_wit_5_2
  right
  intro last_numbers n_pre cells_2 lengths_data_2 flat_data_2 total active_2 depth target x line items_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hx := PreH8 line (by omega)
  rw [←PreH14] at hx
  rcases PopTarget_last_match__semantic_transitions n_pre active_2 target x PreH21 hx PreH20 (by rw [←PreH19]; exact PreH3) with ⟨ht,hbound⟩
  have hc : ∀k,(0≤k ∧ k<depth) → Znth k (replace_Znth (depth-1) (some x) cells_2) __default__App_option_Z=some (Znth k (Znth line items_2 []) 0) := by
    intro k hk
    rw [←PreH16,ht,←PreH19]
    by_cases he:k=depth-1
    · subst k
      rw [Znth_replace_Znth_Same _ _ _ _ (by omega),Znth_replace_Znth_Same _ _ _ _ (by omega)]
    · rw [Znth_replace_Znth_Diff _ _ _ _ _ (by omega) (by omega) (Ne.symm he),Znth_replace_Znth_Diff _ _ _ _ _ (by omega) (by omega) (Ne.symm he)]
      exact PreH28 k hk
  refine Automation.exp_right_rule (CRules := naive_C_Rules) (replace_Znth (depth-1) (some x) cells_2) ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) items_2 ?_
  sep_apply (merge_cell (&("stack")) (depth-1) 1005 cells_2 x (by omega))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (rw [Zlength_replace_Znth]; exact PreH27) |
      (rw [←PreH16,ht,Zlength_replace_Znth]; exact PreH19) | (rw [←PreH16]; exact hbound)

theorem proof_of_solver_entail_wit_6 : solver_entail_wit_6 := by
  unfold solver_entail_wit_6
  right
  intro last_numbers n_pre items_2 cells_2 active_2 flat_data_2 lengths_data_2 line depth total __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hl := LengthsPrefix_snoc__flattening_and_completion items_2 line lengths_data_2 PreH19 (by omega)
  rw [←PreH10] at hl
  have hm : (line+1)*n_pre≤n_pre*n_pre := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
  have hsum : total+depth≤(line+1)*n_pre := by nlinarith
  refine Automation.exp_right_rule (CRules := naive_C_Rules) flat_data_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) items_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [←PreH3,←PreH10]
    all_goals solve | assumption | omega |
      (rw [Zsublist_nil _ 0 0 (le_refl _),List.append_nil]) |
      (rw [←PreH13]; exact PreH21) | rfl

theorem proof_of_solver_entail_wit_7 : solver_entail_wit_7 := by
  unfold solver_entail_wit_7
  right
  intro last_numbers n_pre cells_2 lengths_data_2 total flat_data_2 flat_before_2 i depth active_2 line items_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hc := PreH27 i (by omega)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) flat_before_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) items_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [←PreH11,←PreH4]
    all_goals solve | assumption | omega | rfl | (rw [←PreH15]; exact PreH27) | (rw [←PreH20])

theorem proof_of_solver_entail_wit_8 : solver_entail_wit_8 := by
  unfold solver_entail_wit_8
  right
  intro last_numbers n_pre items_2 cells_2 active_2 flat_before_2 flat_data_2 lengths_data_2 line depth i total __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hs := sublist_snoc_Znth__flattening_and_completion Int 0 i active_2 (by omega)
  have hf : flat_before_2++sublist 0 (i+1) active_2=flat_data_2++[Znth i active_2 0] := by rw [hs,PreH19,List.append_assoc]
  have hflen : Zlength (flat_before_2++sublist 0 (i+1) active_2)=Zlength flat_data_2+1 := by rw [hf,Zlength_app]; rfl
  refine Automation.exp_right_rule (CRules := naive_C_Rules) flat_before_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) items_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [←PreH10,←PreH3]
    all_goals solve | assumption | omega | rfl | (rw [hf,PreH19]) | (rw [hflen]) | (rw [←PreH14]; exact PreH26)

theorem proof_of_solver_entail_wit_9 : solver_entail_wit_9 := by
  unfold solver_entail_wit_9
  right
  intro last_numbers n_pre cells_2 lengths_data_2 total flat_data_2 flat_before i depth active_2 line items_2 __default__App_option_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hi:i=depth := by omega
  have hs : sublist 0 i active_2=active_2 := by rw [hi,PreH15]; exact sublist_self _ _ rfl
  have hf : FlatPrefix items_2 (line+1) (flat_before++sublist 0 i active_2) := by
    rw [hs,PreH11]
    exact FlatPrefix_snoc__flattening_and_completion items_2 line flat_before PreH19 (by omega)
  have hc : CurrentItem items_2 (line+1) active_2 := Or.inr ⟨by omega,by rw [Int.add_sub_cancel]; exact PreH11⟩
  refine Automation.exp_right_rule (CRules := naive_C_Rules) active_2 ?_
  refine Automation.exp_right_rule (CRules := naive_C_Rules) items_2 ?_
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals try simp only [←PreH4]
    all_goals solve | assumption | rfl | omega | (rw [←PreH15]; exact PreH27)

theorem proof_of_solver_entail_wit_10 : solver_entail_wit_10 := by
  unfold solver_entail_wit_10
  right
  intro last_numbers n_pre cells lengths_data_2 flat_data_2 total active depth line items_2 __default__App_option_Z __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22
  have he:line=n_pre := by omega
  have hf := FlatPrefix_full__flattening_and_completion items_2 line flat_data_2 PreH19 (by omega)
  rcases LengthsPrefix_full__flattening_and_completion items_2 line lengths_data_2 (by omega) PreH20 with ⟨hl,hn⟩
  have hnd : ∀k,(0≤k ∧ k<n_pre) → Znth k lengths_data_2 0=Zlength (Znth k items_2 __default__List_Z) := by
    intro k hk
    rw [Znth_indep items_2 k __default__List_Z [] (by omega)]
    exact hn k (by omega)
  refine Automation.exp_right_rule (CRules := naive_C_Rules) items_2 ?_
  split_pure_spatial
  · exact intArray.mixed_full_to_undef_full (&("stack")) 1005 cells
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | exact PreH16.trans (congrArg Zlength hf)

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro last_numbers n_pre flat_pre items flat_data lengths_data_2 total __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  refine Automation.exp_right_rule (CRules := naive_C_Rules) items ?_
  rw [PreH6] at PreH7
  split_pure_spatial
  · rw [PreH6,PreH7]; cancel
  · split_pures <;> dump_pre_spatial <;> assumption

end SimpleC.EE.LLM_bench.Codeforces.examples_shard00.P047_1523C_compression_and_expansion_proof_manual
