import SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_manual_placement
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option maxRecDepth 1000
namespace SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_goal SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
local infixl:70 " /ᶻ " => Z.div
local infixl:70 " mod " => Z.modulo


private noncomputable abbrev charArray := naive_C_Rules.CharArray

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
    charArray.full_shape x n |-- EX l : List Int, charArray.full x n l := by
  apply shape_rec

theorem proof_of_solver_safety_wit_18_split_goal_1 : solver_safety_wit_18_split_goal_1 := by
  intro g_pre m_pre n_pre available grid c t j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  dump_pre_spatial
  exact False.elim (PreH17 available (by omega) PreH20)

theorem proof_of_solver_safety_wit_18 : solver_safety_wit_18 := by
  unfold solver_safety_wit_18
  right
  intro g_pre m_pre n_pre available grid c t j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  exact proof_of_solver_safety_wit_18_split_goal_1 g_pre m_pre n_pre available grid c t j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20

theorem proof_of_solver_entail_wit_1 : solver_entail_wit_1 := by
  unfold solver_entail_wit_1
  right
  intro g_pre m_pre n_pre PreH1 PreH2 PreH3 PreH4
  sep_apply (shape_full g_pre (n_pre*m_pre))
  Intros flat
  prop_apply (charArray.full_Zlength g_pre (n_pre*m_pre) flat)
  Intros_p hlen
  Exists flat
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (intro k hk; omega)

theorem proof_of_solver_entail_wit_2_split_goal_1 : solver_entail_wit_2_split_goal_1 := by
  intro m_pre n_pre flat_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  simpa only [add_zero] using PreH9

theorem proof_of_solver_entail_wit_2_split_goal_2 : solver_entail_wit_2_split_goal_2 := by
  intro m_pre n_pre flat_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  intro h
  constructor <;> nlinarith

theorem proof_of_solver_entail_wit_2 : solver_entail_wit_2 := by
  unfold solver_entail_wit_2
  right
  intro m_pre n_pre flat_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_2_split_goal_1 m_pre n_pre flat_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_solver_entail_wit_2_split_goal_2 m_pre n_pre flat_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_entail_wit_3_split_goal_1 : solver_entail_wit_3_split_goal_1 := by
  intro m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  have he : (i+1)*m_pre=i*m_pre+j := by nlinarith
  rw [he]
  exact PreH12

theorem proof_of_solver_entail_wit_3 : solver_entail_wit_3 := by
  unfold solver_entail_wit_3
  right
  intro m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_3_split_goal_1 m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_entail_wit_4_split_goal_1 : solver_entail_wit_4_split_goal_1 := by
  intro m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  intro k hk
  by_cases he : k=i*m_pre+j
  · subst k
    exact Znth_replace_Znth_Same 0 flat_2 (i*m_pre+j) 0 (by constructor <;> nlinarith)
  · rw [Znth_replace_Znth_Diff 0 flat_2 (i*m_pre+j) k 0 (by constructor <;> nlinarith) (by omega) (Ne.symm he)]
    exact PreH12 k (by omega)

theorem proof_of_solver_entail_wit_4_split_goal_2 : solver_entail_wit_4_split_goal_2 := by
  intro m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  rw [Zlength_replace_Znth]
  exact PreH11

theorem proof_of_solver_entail_wit_4_split_goal_3 : solver_entail_wit_4_split_goal_3 := by
  intro m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  intro h
  constructor <;> nlinarith

theorem proof_of_solver_entail_wit_4 : solver_entail_wit_4 := by
  unfold solver_entail_wit_4
  right
  intro m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_4_split_goal_1 m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    | exact proof_of_solver_entail_wit_4_split_goal_2 m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12
    | exact proof_of_solver_entail_wit_4_split_goal_3 m_pre n_pre flat_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12

theorem proof_of_solver_entail_wit_5_split_goal_1 : solver_entail_wit_5_split_goal_1 := by
  intro m_pre n_pre flat i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  rw [zero_mul]
  apply GreedyTrace_zero flat PreH8
  have he : n_pre*m_pre=i*m_pre := by nlinarith
  rw [he]
  exact PreH9

theorem proof_of_solver_entail_wit_5_split_goal_2 : solver_entail_wit_5_split_goal_2 := by
  intro m_pre n_pre flat i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  intro k hk
  left
  apply PreH9 k
  have he : i*m_pre=n_pre*m_pre := by nlinarith
  rw [he,← PreH8]
  exact hk

theorem proof_of_solver_entail_wit_5 : solver_entail_wit_5 := by
  unfold solver_entail_wit_5
  right
  intro m_pre n_pre flat i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_5_split_goal_1 m_pre n_pre flat i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9
    | exact proof_of_solver_entail_wit_5_split_goal_2 m_pre n_pre flat i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9

theorem proof_of_solver_entail_wit_6_split_goal_1 : solver_entail_wit_6_split_goal_1 := by
  intro m_pre n_pre grid_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  simpa only [add_zero] using PreH10

theorem proof_of_solver_entail_wit_6_split_goal_2 : solver_entail_wit_6_split_goal_2 := by
  intro m_pre n_pre grid_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  intro h
  constructor <;> nlinarith

theorem proof_of_solver_entail_wit_6 : solver_entail_wit_6 := by
  unfold solver_entail_wit_6
  right
  intro m_pre n_pre grid_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_6_split_goal_1 m_pre n_pre grid_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
    | exact proof_of_solver_entail_wit_6_split_goal_2 m_pre n_pre grid_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10

theorem proof_of_solver_entail_wit_7_split_goal_1 : solver_entail_wit_7_split_goal_1 := by
  intro m_pre n_pre grid_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  apply GreedyTrace_skip (i*m_pre+j) grid_2 PreH13 (PreH10 PreH1)
  rcases PreH12 (i*m_pre+j) (by have h:=PreH10 PreH1; omega) with hz | hc
  · contradiction
  · exact hc

theorem proof_of_solver_entail_wit_7 : solver_entail_wit_7 := by
  unfold solver_entail_wit_7
  right
  intro m_pre n_pre grid_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_7_split_goal_1 m_pre n_pre grid_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14

theorem proof_of_solver_entail_wit_8 : solver_entail_wit_8 := by
  unfold solver_entail_wit_8
  right
  intro m_pre n_pre grid_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14
  obtain ⟨available,hr,hplace⟩ := five_colour_neighbour_available__solver_colour_search grid_2 n_pre m_pre i j PreH2 PreH4 (by omega) (by omega) PreH14
  Exists available
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hplace | assumption | omega | (intro color hc; omega)

theorem proof_of_solver_entail_wit_11_split_goal_1 : solver_entail_wit_11_split_goal_1 := by
  intro m_pre n_pre available grid_2 c t j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have he := can_place_one_iff_legal_color__solver_colour_search grid_2 n_pre m_pre i j t PreH5 PreH7 (by omega) (by omega) PreH18 (by omega)
  refine ⟨he.mp PreH2,?_⟩
  intro d hd hlegal
  exact PreH20 d hd ((can_place_one_iff_legal_color__solver_colour_search grid_2 n_pre m_pre i j d PreH5 PreH7 (by omega) (by omega) PreH18 (by omega)).mpr hlegal)

theorem proof_of_solver_entail_wit_11 : solver_entail_wit_11 := by
  unfold solver_entail_wit_11
  right
  intro m_pre n_pre available grid_2 c t j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_11_split_goal_1 m_pre n_pre available grid_2 c t j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_solver_entail_wit_12_1 : solver_entail_wit_12_1 := by
  unfold solver_entail_wit_12_1
  right
  intro m_pre n_pre available grid_2 c t_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20
  exact False.elim (PreH17 available (by omega) PreH20)

theorem proof_of_solver_entail_wit_13 : solver_entail_wit_13 := by
  unfold solver_entail_wit_13
  right
  intro m_pre n_pre available_2 grid_2 c t j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hnone : NoPlaceableColorBelow grid_2 n_pre m_pre i j (t+1) := by
    intro d hd
    by_cases hlt : d<t
    · exact PreH20 d (by omega)
    · have he : d=t := by omega
      simpa only [he] using PreH2
  Exists available_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hnone | assumption | omega

theorem proof_of_solver_entail_wit_14_colour_found_split_goal_1 : solver_entail_wit_14_colour_found_split_goal_1 := by
  intro m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact ⟨PreH17,PreH16,by intro prev hp; omega⟩

theorem proof_of_solver_entail_wit_14_colour_found_split_goal_2 : solver_entail_wit_14_colour_found_split_goal_2 := by
  intro m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact ⟨PreH16,by intro prev hp; omega⟩

theorem proof_of_solver_entail_wit_14_colour_found_split_goal_3 : solver_entail_wit_14_colour_found_split_goal_3 := by
  intro m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact PreH17.1.1.2

theorem proof_of_solver_entail_wit_14_colour_found_split_goal_4 : solver_entail_wit_14_colour_found_split_goal_4 := by
  intro m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  exact PreH17.1.1.1

theorem proof_of_solver_entail_wit_14_colour_found : solver_entail_wit_14_colour_found := by
  unfold solver_entail_wit_14_colour_found
  right
  intro m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_14_colour_found_split_goal_1 m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_solver_entail_wit_14_colour_found_split_goal_2 m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_solver_entail_wit_14_colour_found_split_goal_3 m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
    | exact proof_of_solver_entail_wit_14_colour_found_split_goal_4 m_pre n_pre grid_2 i j t c PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17

theorem proof_of_solver_entail_wit_17_colour_found_split_goal_1 : solver_entail_wit_17_colour_found_split_goal_1 := by
  intro m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  exact ⟨PreH26,greedy_side_extend__solver_greedy_side grid_2 n_pre m_pre i j c size retval_2 PreH27 PreH6 PreH2 PreH1⟩

theorem proof_of_solver_entail_wit_17_colour_found_split_goal_2 : solver_entail_wit_17_colour_found_split_goal_2 := by
  intro m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  exact greedy_side_extend__solver_greedy_side grid_2 n_pre m_pre i j c size retval_2 PreH27 PreH6 PreH2 PreH1

theorem proof_of_solver_entail_wit_17_colour_found_split_goal_3 : solver_entail_wit_17_colour_found_split_goal_3 := by
  intro m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have h := PreH6.2.1
  omega

theorem proof_of_solver_entail_wit_17_colour_found : solver_entail_wit_17_colour_found := by
  unfold solver_entail_wit_17_colour_found
  right
  intro m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_17_colour_found_split_goal_1 m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    | exact proof_of_solver_entail_wit_17_colour_found_split_goal_2 m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
    | exact proof_of_solver_entail_wit_17_colour_found_split_goal_3 m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_solver_entail_wit_18_1_colour_found_split_goal_1 : solver_entail_wit_18_1_colour_found_split_goal_1 := by
  intro m_pre n_pre grid_2 size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  exact ⟨PreH21,Or.inl (by omega)⟩

theorem proof_of_solver_entail_wit_18_1_colour_found : solver_entail_wit_18_1_colour_found := by
  unfold solver_entail_wit_18_1_colour_found
  right
  intro m_pre n_pre grid_2 size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_18_1_colour_found_split_goal_1 m_pre n_pre grid_2 size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21

theorem proof_of_solver_entail_wit_18_2_colour_found_split_goal_1 : solver_entail_wit_18_2_colour_found_split_goal_1 := by
  intro m_pre n_pre grid_2 size c j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  exact ⟨PreH25,Or.inr (Or.inl PreH3)⟩

theorem proof_of_solver_entail_wit_18_2_colour_found : solver_entail_wit_18_2_colour_found := by
  unfold solver_entail_wit_18_2_colour_found
  right
  intro m_pre n_pre grid_2 size c j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_18_2_colour_found_split_goal_1 m_pre n_pre grid_2 size c j i retval PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25

theorem proof_of_solver_entail_wit_18_3_colour_found_split_goal_1 : solver_entail_wit_18_3_colour_found_split_goal_1 := by
  intro m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  exact ⟨PreH28,Or.inr (Or.inr ⟨retval_2,PreH2,PreH1⟩)⟩

theorem proof_of_solver_entail_wit_18_3_colour_found : solver_entail_wit_18_3_colour_found := by
  unfold solver_entail_wit_18_3_colour_found
  right
  intro m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_18_3_colour_found_split_goal_1 m_pre n_pre grid_2 size c j i retval retval_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28

theorem proof_of_solver_entail_wit_19_colour_found : solver_entail_wit_19_colour_found := by
  unfold solver_entail_wit_19_colour_found
  right
  intro m_pre n_pre grid i j c size PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18
  have hpaint : PaintRectanglePrefix grid grid m_pre i j size c ((i-i)*size) := by
    refine ⟨rfl,?_⟩
    intro k hk
    exact Or.inr ⟨by intro off hoff; nlinarith,rfl⟩
  Exists grid
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hpaint | assumption | omega

theorem proof_of_solver_entail_wit_20_colour_found : solver_entail_wit_20_colour_found := by
  unfold solver_entail_wit_20_colour_found
  right
  intro m_pre n_pre current_2 before_2 r size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hpaint : PaintRectanglePrefix before_2 current_2 m_pre i j size c ((r-i)*size+(j-j)) := by simpa only [sub_self,add_zero] using PreH24
  have hbound : j<j+size → 0≤r*m_pre+j ∧ r*m_pre+j<n_pre*m_pre := by intro h; constructor <;> nlinarith
  Exists before_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hpaint | exact hbound | assumption | omega

theorem proof_of_solver_entail_wit_21_colour_found : solver_entail_wit_21_colour_found := by
  unfold solver_entail_wit_21_colour_found
  right
  intro m_pre n_pre current_2 before_2 q r size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hpaint : PaintRectanglePrefix before_2 current_2 m_pre i j size c (((r+1)-i)*size) := by
    have he : ((r+1)-i)*size=(r-i)*size+(q-j) := by nlinarith
    rw [he]
    exact PreH27
  Exists before_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hpaint | assumption | omega

theorem proof_of_solver_entail_wit_22_colour_found : solver_entail_wit_22_colour_found := by
  unfold solver_entail_wit_22_colour_found
  right
  intro m_pre n_pre current_2 before_2 q r size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27
  have hidx : 0≤r*m_pre+q ∧ r*m_pre+q<Zlength current_2 := by have h:=PreH19 PreH1; omega
  have hpaint := paint_prefix_replace__solver_paint before_2 current_2 m_pre i j size c r q PreH12 (by omega) (by omega) hidx PreH27
  have hcanon := canonical_grid_replace__solver_paint current_2 (r*m_pre+q) c hidx (by omega) PreH23
  have hlen : Zlength (replace_Znth (r*m_pre+q) c current_2)=n_pre*m_pre := by rw [Zlength_replace_Znth,PreH21]
  have hbound : q+1<j+size → 0≤r*m_pre+(q+1) ∧ r*m_pre+(q+1)<n_pre*m_pre := by intro h; constructor <;> nlinarith
  Exists before_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hpaint | exact hcanon | exact hlen | exact hbound | assumption | omega

theorem proof_of_solver_entail_wit_23_split_goal_1 : solver_entail_wit_23_split_goal_1 := by
  intro m_pre n_pre grid_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  have he : (i+1)*m_pre=i*m_pre+j := by nlinarith
  rw [he]
  exact PreH13

theorem proof_of_solver_entail_wit_23 : solver_entail_wit_23 := by
  unfold solver_entail_wit_23
  right
  intro m_pre n_pre grid_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_23_split_goal_1 m_pre n_pre grid_2 j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13

theorem proof_of_solver_entail_wit_24_colour_found_split_goal_1 : solver_entail_wit_24_colour_found_split_goal_1 := by
  intro m_pre n_pre current before r size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  rw [← add_assoc]
  apply GreedyTrace_place (i*m_pre+j) before current i j c size PreH22 rfl (by omega) (by omega) PreH21 PreH23
  have he : size*size=(r-i)*size := by nlinarith
  rw [he]
  exact PreH24

theorem proof_of_solver_entail_wit_24_colour_found_split_goal_2 : solver_entail_wit_24_colour_found_split_goal_2 := by
  intro m_pre n_pre current before r size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  intro h
  constructor <;> nlinarith

theorem proof_of_solver_entail_wit_24_colour_found : solver_entail_wit_24_colour_found := by
  unfold solver_entail_wit_24_colour_found
  right
  intro m_pre n_pre current before r size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_24_colour_found_split_goal_1 m_pre n_pre current before r size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
    | exact proof_of_solver_entail_wit_24_colour_found_split_goal_2 m_pre n_pre current before r size c j i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24

theorem proof_of_solver_entail_wit_25_split_goal_1 : solver_entail_wit_25_split_goal_1 := by
  intro m_pre n_pre grid_2 i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  simpa only [add_assoc] using PreH11

theorem proof_of_solver_entail_wit_25_split_goal_2 : solver_entail_wit_25_split_goal_2 := by
  intro m_pre n_pre grid_2 i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  intro h
  constructor <;> nlinarith

theorem proof_of_solver_entail_wit_25 : solver_entail_wit_25 := by
  unfold solver_entail_wit_25
  right
  intro m_pre n_pre grid_2 i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial <;> first
    | exact proof_of_solver_entail_wit_25_split_goal_1 m_pre n_pre grid_2 i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11
    | exact proof_of_solver_entail_wit_25_split_goal_2 m_pre n_pre grid_2 i j PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11

theorem proof_of_solver_return_wit_1 : solver_return_wit_1 := by
  unfold solver_return_wit_1
  right
  intro m_pre n_pre grid i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  have htrace : GreedyPlacementTrace n_pre m_pre (n_pre*m_pre) grid := by
    have he : i=n_pre := by omega
    simpa only [he] using PreH10
  have hpartial := greedy_trace_implies_partial_tiling__solver_final n_pre m_pre (n_pre*m_pre) grid PreH2 PreH4 htrace
  obtain ⟨out,hflat,hspec⟩ := complete_partial_tiling_implies_spec__solver_final n_pre m_pre grid PreH2 PreH4 PreH8 hpartial
  Exists out
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    · exact hflat.symm
    · exact hspec

end SimpleC.EE.LLM_bench.Codeforces.examples_shard09.P081_432E_square_tiling_proof_manual
