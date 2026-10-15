import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_goal

set_option linter.unusedVariables false
set_option linter.style.nameCheck false
set_option maxHeartbeats 4000000
set_option maxRecDepth 2000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_manual_spatial
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
private noncomputable abbrev intArray2 := naive_C_Rules.IntArray2

private theorem shape_rec (storeA : Int → Int → Int → SacContext.rules.expr)
    (k : Nat) (x lo hi : Int) :
    store_undef_array_rec SacContext.rules (fun x lo => EX a : Int, storeA x lo a) x lo hi k |--
      EX l : List Int, store_array_rec SacContext.rules storeA x lo hi l := by
  induction k generalizing lo with
  | zero =>
    simp only [store_undef_array_rec]
    Intros_p he
    Exists ([] : List Int)
    simp only [store_array_rec]
    split_pure_spatial
    · cancel
    · split_pures <;> dump_pre_spatial
      all_goals solve | assumption | rfl | trivial
  | succ k ih =>
    simp only [store_undef_array_rec]
    Intros a
    sep_apply (ih (lo+1))
    Intros l
    Exists (a::l)
    simp only [store_array_rec]
    cancel

private theorem shape_full (x n : Int) :
    intArray.full_shape x n |-- EX l : List Int, intArray.full x n l := by
  apply shape_rec

private theorem undef_singleton (p : Int) :
    intArray.undef_full p 1 |-- (p # Int |->_) := by
  change intArray.undef_full p (0+1) |-- (p # Int |->_)
  rel_rw [intArray.undef_full_unfold p 0 ([] : List Int) (by omega)]
  simp only [Int.zero_add]
  rel_rw [intArray.undef_seg_empty p 1]
  entailer!
  all_goals try simp only [Int.zero_mul,Int.add_zero] at *
  all_goals first | assumption | exact naive_C_Rules.toContext.derivable1_refl _

theorem cell_to_singleton (p v : Int) :
    (p # Int |-> v) |-- intArray.full p 1 [v] := by
  rel_rw [intArray.full_unfold p 1 [] v,intArray.seg_empty p 1]
  entailer!
  all_goals try simp only [Int.zero_mul,Int.add_zero] at *
  all_goals first | assumption | exact naive_C_Rules.toContext.derivable1_refl _

private theorem singleton_to_cell (p : Int) (values : List Int) (h : Zlength values = 1) :
    intArray.full p 1 values |-- (p # Int |-> Znth 0 values 0) := by
  cases values with
  | nil => simp only [Zlength_nil] at h; omega
  | cons v tail =>
    have ht : tail = [] := by
      have hh : tail.length + 1 = 1 := Int.ofNat.inj h
      have hl : tail.length = 0 := by omega
      exact List.length_eq_zero_iff.mp hl
    subst tail
    rel_rw [intArray.full_unfold p 1 [] v,intArray.seg_empty p 1]
    simp only [Znth0_cons]
    entailer!
    all_goals try simp only [Int.zero_mul,Int.add_zero] at *
    all_goals first | assumption | exact naive_C_Rules.toContext.derivable1_refl _

theorem proof_of_feasible_entail_wit_1 : feasible_entail_wit_1 := by
  unfold feasible_entail_wit_1
  right
  intro rep_pre x_pre m_pre n_pre old_bj old_bi rows __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  sep_apply (shape_full rep_pre 256)
  Intros reps
  prop_apply (intArray.full_Zlength rep_pre 256 reps)
  Intros_p hlen
  Exists reps
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | skip
    all_goals
      have hm : m_pre=1 ∨ m_pre=2 ∨ m_pre=3 ∨ m_pre=4 ∨ m_pre=5 ∨ m_pre=6 ∨ m_pre=7 ∨ m_pre=8 := by omega
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem proof_of_feasible_which_implies_wit_1 : feasible_which_implies_wit_1 := by
  unfold feasible_which_implies_wit_1
  left
  intro bj_pre bi_pre old_bj old_bi
  sep_apply (intArray.mixed_full_to_undef_full bi_pre 1 old_bi)
  sep_apply (intArray.mixed_full_to_undef_full bj_pre 1 old_bj)
  sep_apply (undef_singleton bi_pre)
  sep_apply (undef_singleton bj_pre)
  cancel

theorem proof_of_solver_which_implies_wit_1 : solver_which_implies_wit_1 := by
  unfold solver_which_implies_wit_1
  left
  intro bj_pre bi_pre
  exact naive_C_Rules.toContext.derivable1_sepcon_mono _ _ _ _
    (undef_singleton bi_pre) (undef_singleton bj_pre)

theorem proof_of_solver_which_implies_wit_2 : solver_which_implies_wit_2 := by
  unfold solver_which_implies_wit_2
  right
  Exists ([none] : List (Option Int)) ([none] : List (Option Int))
  split_pure_spatial
  · rel_rw [intArray.mixed_full_unfold (&("ci")) 1 [] none,
      intArray.mixed_full_unfold (&("cj")) 1 [] none,
      intArray.mixed_seg_empty (&("ci")) 1,intArray.mixed_seg_empty (&("cj")) 1]
    simp only [SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.mixedstoreA]
    entailer!
    all_goals try simp only [Int.zero_mul,Int.add_zero] at *
    all_goals first | assumption | exact naive_C_Rules.toContext.derivable1_refl _
  · split_pures <;> dump_pre_spatial <;> rfl

theorem proof_of_solver_which_implies_wit_3_split_goal_spatial : solver_which_implies_wit_3_split_goal_spatial := by
  intro bj_pre bi_pre old_js old_is cj_values ci_values PreH1 PreH2 PreH3 PreH4
  sep_apply (singleton_to_cell (&("ci")) ci_values PreH1)
  sep_apply (singleton_to_cell (&("cj")) cj_values PreH2)
  sep_apply (singleton_to_cell bi_pre old_is PreH3)
  sep_apply (singleton_to_cell bj_pre old_js PreH4)
  cancel

theorem proof_of_solver_which_implies_wit_3 : solver_which_implies_wit_3 := by
  unfold solver_which_implies_wit_3
  right
  intro bj_pre bi_pre old_js old_is cj_values ci_values PreH1 PreH2 PreH3 PreH4
  exact proof_of_solver_which_implies_wit_3_split_goal_spatial bj_pre bi_pre old_js old_is cj_values ci_values PreH1 PreH2 PreH3 PreH4

theorem proof_of_solver_which_implies_wit_4 : solver_which_implies_wit_4 := by
  unfold solver_which_implies_wit_4
  left
  intro cj_values ci_values
  sep_apply (intArray.mixed_full_to_undef_full (&("ci")) 1 ci_values)
  sep_apply (intArray.mixed_full_to_undef_full (&("cj")) 1 cj_values)
  sep_apply (undef_singleton (&("ci")))
  sep_apply (undef_singleton (&("cj")))
  cancel

theorem proof_of_solver_which_implies_wit_5 : solver_which_implies_wit_5 := by
  unfold solver_which_implies_wit_5
  right
  intro bj_pre bi_pre bj_values bi_values
  prop_apply (intArray.full_Zlength bi_pre 1 bi_values)
  Intros_p hbi
  prop_apply (intArray.full_Zlength bj_pre 1 bj_values)
  Intros_p hbj
  Exists (bj_values.map some) (bi_values.map some)
  split_pure_spatial
  · sep_apply (intArray.full_to_mixed_full bi_pre 1 bi_values)
    sep_apply (intArray.full_to_mixed_full bj_pre 1 bj_values)
    cancel
  · split_pures <;> dump_pre_spatial
    · simpa only [Zlength,List.length_map] using hbi
    · simpa only [Zlength,List.length_map] using hbj

private theorem matrix_cell_restore (a n m i j : Int) (rows : List (List Int)) (defaultRow : List Int)
    (hn : n = Zlength rows) (hi : 0 ≤ i ∧ i < n) (hj : 0 ≤ j ∧ j < m) :
    ((a + (i*m+j)*sizeof(INT)) # Int |-> Znth j (Znth i rows defaultRow) 0)
    ** intArray.missing_i (a+i*m*sizeof(INT)) j 0 m (Znth i rows defaultRow)
    ** intArray2.missing_i a i 0 n m rows |-- intArray2.full a n m rows := by
  rw [Znth_indep rows i defaultRow [] (by omega)]
  have ha : a+(i*m+j)*sizeof(INT) = (a+i*m*sizeof(INT))+j*sizeof(INT) := by ring
  rw [ha]
  sep_apply (intArray.missing_i_merge_to_full (a+i*m*sizeof(INT)) j m
    (Znth j (Znth i rows []) (0 : Int)) (Znth i rows []) hj)
  simp only [replace_Znth_Znth]
  change (intArray.full (intArray2.row_addr a m i) m (Znth i rows []) **
    intArray2.missing_i a i 0 n m rows) |-- intArray2.full a n m rows
  simpa only [replace_Znth_Znth] using
    (intArray2.missing_i_merge_to_full a i n m rows (Znth i rows []) hi)

theorem proof_of_feasible_entail_wit_5_1_split_goal_spatial : feasible_entail_wit_5_1_split_goal_spatial := by
  intro x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  exact matrix_cell_restore a_pre n_pre m_pre i j rows __default__List_Z PreH12 ⟨PreH19,PreH20⟩ ⟨PreH21,PreH4⟩

theorem proof_of_feasible_entail_wit_5_2_split_goal_spatial : feasible_entail_wit_5_2_split_goal_spatial := by
  intro x_pre m_pre n_pre a_pre old_bj old_bi rows reps_2 mask j i full __default__List_Z PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  exact matrix_cell_restore a_pre n_pre m_pre i j rows __default__List_Z PreH12 ⟨PreH19,PreH20⟩ ⟨PreH21,PreH4⟩

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_manual_spatial

/- Recursively audit all ten source Qed and the public singleton helper. -/
run_cmd do
  let proved := #[
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_manual_spatial.proof_of_feasible_entail_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_manual_spatial.proof_of_feasible_which_implies_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_manual_spatial.proof_of_solver_which_implies_wit_1,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_manual_spatial.proof_of_solver_which_implies_wit_2,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_manual_spatial.proof_of_solver_which_implies_wit_3_split_goal_spatial,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_manual_spatial.proof_of_solver_which_implies_wit_3,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_manual_spatial.proof_of_solver_which_implies_wit_4,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_manual_spatial.proof_of_solver_which_implies_wit_5,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_manual_spatial.proof_of_feasible_entail_wit_5_1_split_goal_spatial,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_manual_spatial.proof_of_feasible_entail_wit_5_2_split_goal_spatial,
    ``SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P066_1288D_minimax_problem_manual_spatial.cell_to_singleton
  ]
  /- The five CNotation constants are existing address/type-size interpretation parameters. -/
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound,
    ``SimpleC.SL.CNotation.eval_addr_expr, ``SimpleC.SL.CNotation.sizeof_struct_type,
    ``SimpleC.SL.CNotation.sizeof_union_type, ``SimpleC.SL.CNotation.sizeof_enum_type,
    ``SimpleC.SL.CNotation.sizeof_alias_type]
  let mut allAxioms : Array Lean.Name := #[]
  for decl in proved do
    let axioms ← Lean.collectAxioms decl
    if axioms.contains ``sorryAx then
      throwError "unproved dependency in {decl}"
    for axiomName in axioms do
      unless allowed.contains axiomName do
        throwError "unexpected additional axiom {axiomName} in {decl}"
      unless allAxioms.contains axiomName do
        allAxioms := allAxioms.push axiomName
  Lean.logInfo m!"Audited {proved.size} space declarations (10 source Qed and cell_to_singleton): no sorryAx. Existing axioms: {allAxioms}"
