import SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_goal
import SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_lib

set_option maxHeartbeats 800000
set_option maxRecDepth 8000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open edit_strings_goal edit_strings_lib EditStringsProofInternal
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray
local macro "finish_entail" : tactic => `(tactic| (
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | trivial | omega | int_auto))


attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg

private theorem edit_scratch_split (x k cap : Int) (hk : 0≤k ∧ k≤cap) :
    intArray.undef_full x cap |-- intArray.undef_full x k ** intArray.undef_seg x k cap := by
  sep_apply (intArray.undef_full_split_to_undef_seg x k cap hk)
  sep_apply (intArray.undef_seg_to_undef_full x 0 k)
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  cancel

private theorem edit_Forall_snoc {A : Type} (P : A → Prop) (xs : List A) (x : A)
    (hxs : Forall P xs) (hx : P x) : Forall P (xs++[x]) := by
  induction hxs with
  | nil => exact .cons hx .nil
  | cons ha ht ih => exact .cons ha ih

theorem proof_of_max_edit_string_matches_entail_wit_1 : max_edit_string_matches_entail_wit_1 := by
  unfold max_edit_string_matches_entail_wit_1
  right
  intro t2_l t1_l s2_l s1_l n_pre PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10
  sep_apply (intArray.undef_full_split_to_undef_seg ( &( "cnt21" ) ) n_pre 100000 (by omega))
  sep_apply (intArray.undef_full_split_to_undef_seg ( &( "cnt20" ) ) n_pre 100000 (by omega))
  sep_apply (intArray.undef_full_split_to_undef_seg ( &( "cnt11" ) ) n_pre 100000 (by omega))
  sep_apply (intArray.undef_full_split_to_undef_seg ( &( "cnt10" ) ) n_pre 100000 (by omega))
  sep_apply (edit_scratch_split ( &( "seg2" ) ) n_pre 100000 (by omega))
  sep_apply (edit_scratch_split ( &( "seg1" ) ) n_pre 100000 (by omega))
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals exact Forall.nil

theorem proof_of_max_edit_string_matches_entail_wit_2 : max_edit_string_matches_entail_wit_2 := by
  unfold max_edit_string_matches_entail_wit_2
  right
  intro t2_l t1_l s2_l s1_l n_pre c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17
  have h_c21_2 := edit_Forall_snoc (Eq (0 : Int)) c21_2 0 PreH17 rfl
  have h_c20_2 := edit_Forall_snoc (Eq (0 : Int)) c20_2 0 PreH16 rfl
  have h_c11_2 := edit_Forall_snoc (Eq (0 : Int)) c11_2 0 PreH15 rfl
  have h_c10_2 := edit_Forall_snoc (Eq (0 : Int)) c10_2 0 PreH14 rfl
  finish_entail

theorem proof_of_max_edit_string_matches_safety_wit_14 : max_edit_string_matches_safety_wit_14 := by
  unfold max_edit_string_matches_safety_wit_14
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre c21 c20 c11 c10 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hz_c10 := edit_zero_read c10 (((0 : Int) - (0 : Int))) PreH16
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_16 : max_edit_string_matches_safety_wit_16 := by
  unfold max_edit_string_matches_safety_wit_16
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre c21 c20 c11 c10 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  have hz_c11 := edit_zero_read c11 (((0 : Int) - (0 : Int))) PreH17
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_26 : max_edit_string_matches_safety_wit_26 := by
  unfold max_edit_string_matches_safety_wit_26
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 c10 c11 c20 c21 i block1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hb_c10 := edit_bounded_read c10 (block1) 0 n_pre PreH14 PreH15 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_27 : max_edit_string_matches_safety_wit_27 := by
  unfold max_edit_string_matches_safety_wit_27
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 c10 c11 c20 c21 i block1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  have hb_c11 := edit_bounded_read c11 (block1) 0 n_pre PreH16 PreH17 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_35 : max_edit_string_matches_safety_wit_35 := by
  unfold max_edit_string_matches_safety_wit_35
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 c21 c20 c11 c10 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hz_c20 := edit_zero_read c20 ((0 : Int)) PreH23
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_37 : max_edit_string_matches_safety_wit_37 := by
  unfold max_edit_string_matches_safety_wit_37
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 c21 c20 c11 c10 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  have hz_c21 := edit_zero_read c21 ((0 : Int)) PreH24
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_47 : max_edit_string_matches_safety_wit_47 := by
  unfold max_edit_string_matches_safety_wit_47
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 sg2 c10 c11 c20 c21 i block2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have hb_c20 := edit_bounded_read c20 (block2) 0 n_pre PreH18 PreH19 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_48 : max_edit_string_matches_safety_wit_48 := by
  unfold max_edit_string_matches_safety_wit_48
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 sg2 c10 c11 c20 c21 i block2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  have hb_c21 := edit_bounded_read c21 (block2) 0 n_pre PreH20 PreH21 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_56 : max_edit_string_matches_safety_wit_56 := by
  unfold max_edit_string_matches_safety_wit_56
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 sg2 c10 c11 c20 c21 rest prefix1 prefix2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have hb_c10 := edit_bounded_read c10 (a) 0 n_pre PreH17 PreH18 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_57 : max_edit_string_matches_safety_wit_57 := by
  unfold max_edit_string_matches_safety_wit_57
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 sg2 c10 c11 c20 c21 rest prefix1 prefix2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have hb_c20 := edit_bounded_read c20 (b) 0 n_pre PreH21 PreH22 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_64 : max_edit_string_matches_safety_wit_64 := by
  unfold max_edit_string_matches_safety_wit_64
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 sg2 c10 c11 c20 c21 rest prefix1 prefix2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  have hb_c11 := edit_bounded_read c11 (a) 0 n_pre PreH20 PreH21 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_65 : max_edit_string_matches_safety_wit_65 := by
  unfold max_edit_string_matches_safety_wit_65
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 sg2 c10 c11 c20 c21 rest prefix1 prefix2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hb_c11 := edit_bounded_read c11 (a) 0 n_pre PreH21 PreH22 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_66 : max_edit_string_matches_safety_wit_66 := by
  unfold max_edit_string_matches_safety_wit_66
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 sg2 c10 c11 c20 c21 rest prefix1 prefix2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  have hb_c21 := edit_bounded_read c21 (b) 0 n_pre PreH24 PreH25 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_67 : max_edit_string_matches_safety_wit_67 := by
  unfold max_edit_string_matches_safety_wit_67
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 sg2 c10 c11 c20 c21 rest prefix1 prefix2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hb_c21 := edit_bounded_read c21 (b) 0 n_pre PreH25 PreH26 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_76 : max_edit_string_matches_safety_wit_76 := by
  unfold max_edit_string_matches_safety_wit_76
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 sg2 c10 c11 c20 c21 rest prefix1 prefix2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hb_c10 := edit_bounded_read c10 (a) 0 n_pre PreH19 PreH20 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_77 : max_edit_string_matches_safety_wit_77 := by
  unfold max_edit_string_matches_safety_wit_77
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 sg2 c10 c11 c20 c21 rest prefix1 prefix2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  have hb_c10 := edit_bounded_read c10 (a) 0 n_pre PreH20 PreH21 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_78 : max_edit_string_matches_safety_wit_78 := by
  unfold max_edit_string_matches_safety_wit_78
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 sg2 c10 c11 c20 c21 rest prefix1 prefix2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hb_c21 := edit_bounded_read c21 (b) 0 n_pre PreH25 PreH26 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_79 : max_edit_string_matches_safety_wit_79 := by
  unfold max_edit_string_matches_safety_wit_79
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 sg2 c10 c11 c20 c21 rest prefix1 prefix2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  have hb_c21 := edit_bounded_read c21 (b) 0 n_pre PreH26 PreH27 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_80 : max_edit_string_matches_safety_wit_80 := by
  unfold max_edit_string_matches_safety_wit_80
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 sg2 c10 c11 c20 c21 rest prefix1 prefix2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  have hb_c11 := edit_bounded_read c11 (a) 0 n_pre PreH20 PreH21 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_81 : max_edit_string_matches_safety_wit_81 := by
  unfold max_edit_string_matches_safety_wit_81
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 sg2 c10 c11 c20 c21 rest prefix1 prefix2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hb_c11 := edit_bounded_read c11 (a) 0 n_pre PreH21 PreH22 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_82 : max_edit_string_matches_safety_wit_82 := by
  unfold max_edit_string_matches_safety_wit_82
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 sg2 c10 c11 c20 c21 rest prefix1 prefix2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  have hb_c20 := edit_bounded_read c20 (b) 0 n_pre PreH22 PreH23 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_safety_wit_83 : max_edit_string_matches_safety_wit_83 := by
  unfold max_edit_string_matches_safety_wit_83
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 sg2 c10 c11 c20 c21 rest prefix1 prefix2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  have hb_c20 := edit_bounded_read c20 (b) 0 n_pre PreH23 PreH24 (by omega)
  split_pures
  all_goals dump_pre_spatial
  all_goals first
    | (change _ ≤ (2147483647 : Int); omega)
    | (change (-2147483648 : Int) ≤ _; omega)

theorem proof_of_max_edit_string_matches_entail_wit_3_1 : max_edit_string_matches_entail_wit_3_1 := by
  unfold max_edit_string_matches_entail_wit_3_1
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  prop_apply (intArray.full_Zlength (( &( "cnt10" ) )) (i) ((replace_Znth ((0 : Int)) (((Znth ((0 : Int) - (0 : Int)) c10_2 (0 : Int)) + 1)) (c10_2))))
  Intros_p hlength_0
  simp only [Zlength_replace_Znth] at hlength_0
  prop_apply (intArray.full_Zlength (s1_pre) (n_pre) (s1_l))
  Intros_p hlength_1
  prop_apply (intArray.seg_Zlength (( &( "cnt11" ) )) ((0 : Int)) (i) (c11_2))
  Intros_p hlength_5
  simp only [Int.sub_zero] at hlength_5
  have hn := edit_build_first_zero s1_l t1_l n_pre c10_2 c11_2 (by omega) (by omega) (by omega) (by omega) PreH16 PreH17 PreH1
  have hnew : EditBuildMeaning s1_l t1_l n_pre 1 [0] ((replace_Znth ((0 : Int)) (((Znth ((0 : Int) - (0 : Int)) c10_2 (0 : Int)) + 1)) (c10_2))) (c11_2) := by simpa only [Int.sub_zero] using hn
  have hc := edit_counts_bounds s1_l t1_l n_pre 1 ((replace_Znth ((0 : Int)) (((Znth ((0 : Int) - (0 : Int)) c10_2 (0 : Int)) + 1)) (c10_2))) (c11_2) (by omega) (by omega) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) hnew.2
  rcases hc with ⟨⟨hc0lo,hc0hi⟩,⟨hc1lo,hc1hi⟩⟩
  obtain ⟨hc20_2lo,hc20_2hi⟩ := edit_zero_bounds c20_2 n_pre (by omega) PreH18
  obtain ⟨hc21_2lo,hc21_2hi⟩ := edit_zero_bounds c21_2 n_pre (by omega) PreH19
  sep_apply (intArray.seg_to_full (( &( "cnt11" ) )) ((0 : Int)) (i) (c11_2))
  sep_apply (intArray.seg_to_full (( &( "cnt20" ) )) ((0 : Int)) (i) (c20_2))
  sep_apply (intArray.seg_to_full (( &( "cnt21" ) )) ((0 : Int)) (i) (c21_2))
  have hiEq : i=n_pre := by omega
  rw [hiEq]
  sep_apply (intArray.seg_single ( &( "seg1" ) ) 0 0)
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  Exists (([0] : List Int)) (c21_2) (c20_2) (c11_2) ((replace_Znth ((0 : Int)) (((Znth ((0 : Int) - (0 : Int)) c10_2 (0 : Int)) + 1)) (c10_2)))
  split_pure_spatial
  · simp only [Int.zero_add,Int.sub_zero]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_max_edit_string_matches_entail_wit_3_2 : max_edit_string_matches_entail_wit_3_2 := by
  unfold max_edit_string_matches_entail_wit_3_2
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19
  prop_apply (intArray.full_Zlength (( &( "cnt11" ) )) (i) ((replace_Znth ((0 : Int)) (((Znth ((0 : Int) - (0 : Int)) c11_2 (0 : Int)) + 1)) (c11_2))))
  Intros_p hlength_0
  simp only [Zlength_replace_Znth] at hlength_0
  prop_apply (intArray.full_Zlength (s1_pre) (n_pre) (s1_l))
  Intros_p hlength_1
  prop_apply (intArray.seg_Zlength (( &( "cnt10" ) )) ((0 : Int)) (i) (c10_2))
  Intros_p hlength_5
  simp only [Int.sub_zero] at hlength_5
  have hn := edit_build_first_one s1_l t1_l n_pre c10_2 c11_2 (by omega) (by omega) (by omega) (by omega) PreH16 PreH17 PreH8 PreH9 PreH1
  have hnew : EditBuildMeaning s1_l t1_l n_pre 1 [0] (c10_2) ((replace_Znth ((0 : Int)) (((Znth ((0 : Int) - (0 : Int)) c11_2 (0 : Int)) + 1)) (c11_2))) := by simpa only [Int.sub_zero] using hn
  have hc := edit_counts_bounds s1_l t1_l n_pre 1 (c10_2) ((replace_Znth ((0 : Int)) (((Znth ((0 : Int) - (0 : Int)) c11_2 (0 : Int)) + 1)) (c11_2))) (by omega) (by omega) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) hnew.2
  rcases hc with ⟨⟨hc0lo,hc0hi⟩,⟨hc1lo,hc1hi⟩⟩
  obtain ⟨hc20_2lo,hc20_2hi⟩ := edit_zero_bounds c20_2 n_pre (by omega) PreH18
  obtain ⟨hc21_2lo,hc21_2hi⟩ := edit_zero_bounds c21_2 n_pre (by omega) PreH19
  sep_apply (intArray.seg_to_full (( &( "cnt10" ) )) ((0 : Int)) (i) (c10_2))
  sep_apply (intArray.seg_to_full (( &( "cnt20" ) )) ((0 : Int)) (i) (c20_2))
  sep_apply (intArray.seg_to_full (( &( "cnt21" ) )) ((0 : Int)) (i) (c21_2))
  have hiEq : i=n_pre := by omega
  rw [hiEq]
  sep_apply (intArray.seg_single ( &( "seg1" ) ) 0 0)
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  Exists (([0] : List Int)) (c21_2) (c20_2) ((replace_Znth ((0 : Int)) (((Znth ((0 : Int) - (0 : Int)) c11_2 (0 : Int)) + 1)) (c11_2))) (c10_2)
  split_pure_spatial
  · simp only [Int.zero_add,Int.sub_zero]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_max_edit_string_matches_entail_wit_4_1 : max_edit_string_matches_entail_wit_4_1 := by
  unfold max_edit_string_matches_entail_wit_4_1
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  prop_apply (intArray.seg_Zlength (( &( "seg1" ) )) ((0 : Int)) ((i + 1)) ((sg1 ++ ((Znth ((i - 1) - (0 : Int)) sg1 (0 : Int)) :: (@List.nil Int)))))
  Intros_p hlength_0
  simp only [Zlength_app,Zlength_cons,Zlength_nil,Int.sub_zero] at hlength_0
  have hm := edit_segment_extend_same t1_l sg1 i (by omega) (by omega) PreH26.1 (by exact ⟨PreH2,PreH1⟩)
  have hnew : EditSegmentMeaning t1_l (i+1) ((sg1 ++ ((Znth ((i - 1) - (0 : Int)) sg1 (0 : Int)) :: (@List.nil Int)))) := by simpa only [Int.sub_zero] using hm
  have hbound := edit_segment_bound t1_l ((sg1 ++ ((Znth ((i - 1) - (0 : Int)) sg1 (0 : Int)) :: (@List.nil Int)))) (i+1) i hnew (by omega)
  have hcounts := PreH26.2
  Exists ((sg1 ++ ((Znth ((i - 1) - (0 : Int)) sg1 (0 : Int)) :: (@List.nil Int)))) (c21_2) (c20_2) (c11_2) (c10_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega | (simpa only [Int.sub_zero] using hbound.1) | (simpa only [Int.sub_zero] using hbound.2)

theorem proof_of_max_edit_string_matches_entail_wit_4_2 : max_edit_string_matches_entail_wit_4_2 := by
  unfold max_edit_string_matches_entail_wit_4_2
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  prop_apply (intArray.seg_Zlength (( &( "seg1" ) )) ((0 : Int)) ((i + 1)) ((sg1 ++ (i :: (@List.nil Int)))))
  Intros_p hlength_0
  simp only [Zlength_app,Zlength_cons,Zlength_nil,Int.sub_zero] at hlength_0
  have hm := edit_segment_extend_new t1_l sg1 i (by omega) (by omega) PreH25.1 (by intro he; have hl := he.1; have hr := he.2; omega)
  have hnew : EditSegmentMeaning t1_l (i+1) ((sg1 ++ (i :: (@List.nil Int)))) := by simpa only [Int.sub_zero] using hm
  have hbound := edit_segment_bound t1_l ((sg1 ++ (i :: (@List.nil Int)))) (i+1) i hnew (by omega)
  have hcounts := PreH25.2
  Exists ((sg1 ++ (i :: (@List.nil Int)))) (c21_2) (c20_2) (c11_2) (c10_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega | (simpa only [Int.sub_zero] using hbound.1) | (simpa only [Int.sub_zero] using hbound.2)

theorem proof_of_max_edit_string_matches_entail_wit_4_3 : max_edit_string_matches_entail_wit_4_3 := by
  unfold max_edit_string_matches_entail_wit_4_3
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1 c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26
  prop_apply (intArray.seg_Zlength (( &( "seg1" ) )) ((0 : Int)) ((i + 1)) ((sg1 ++ (i :: (@List.nil Int)))))
  Intros_p hlength_0
  simp only [Zlength_app,Zlength_cons,Zlength_nil,Int.sub_zero] at hlength_0
  have hm := edit_segment_extend_new t1_l sg1 i (by omega) (by omega) PreH26.1 (by intro he; have hl := he.1; have hr := he.2; omega)
  have hnew : EditSegmentMeaning t1_l (i+1) ((sg1 ++ (i :: (@List.nil Int)))) := by simpa only [Int.sub_zero] using hm
  have hbound := edit_segment_bound t1_l ((sg1 ++ (i :: (@List.nil Int)))) (i+1) i hnew (by omega)
  have hcounts := PreH26.2
  Exists ((sg1 ++ (i :: (@List.nil Int)))) (c21_2) (c20_2) (c11_2) (c10_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega | (simpa only [Int.sub_zero] using hbound.1) | (simpa only [Int.sub_zero] using hbound.2)

theorem proof_of_max_edit_string_matches_entail_wit_5_1 : max_edit_string_matches_entail_wit_5_1 := by
  unfold max_edit_string_matches_entail_wit_5_1
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1_2 c10_2 c11_2 c20_2 c21_2 i block1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  prop_apply (intArray.full_Zlength (( &( "cnt10" ) )) (n_pre) ((replace_Znth (block1) (((Znth block1 c10_2 (0 : Int)) + 1)) (c10_2))))
  Intros_p hlength_0
  simp only [Zlength_replace_Znth] at hlength_0
  prop_apply (intArray.full_Zlength (s1_pre) (n_pre) (s1_l))
  Intros_p hlength_1
  prop_apply (intArray.seg_Zlength (( &( "seg1" ) )) ((0 : Int)) ((i + 1)) (sg1_2))
  Intros_p hlength_5
  simp only [Int.sub_zero] at hlength_5
  prop_apply (intArray.full_Zlength (( &( "cnt11" ) )) (n_pre) (c11_2))
  Intros_p hlength_6
  have hread := edit_bounded_read s1_l i 0 1 PreH6 PreH7 (by omega)
  have hn := edit_counts_inc_zero s1_l t1_l n_pre i sg1_2 c10_2 c11_2 block1 (by omega) (by omega) (by omega) (by omega) (by omega) PreH28 PreH29 PreH27 (by omega)
  have hnew : EditBuildMeaning s1_l t1_l n_pre (i+1) sg1_2 ((replace_Znth (block1) (((Znth block1 c10_2 (0 : Int)) + 1)) (c10_2))) (c11_2) := ⟨PreH28,by simpa only [Int.sub_zero] using hn⟩
  have hbounds := edit_counts_bounds s1_l t1_l n_pre (i+1) ((replace_Znth (block1) (((Znth block1 c10_2 (0 : Int)) + 1)) (c10_2))) (c11_2) (by omega) (by omega) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) hnew.2
  rcases hbounds with ⟨⟨hc0lo,hc0hi⟩,⟨hc1lo,hc1hi⟩⟩
  Exists (sg1_2) (c21_2) (c20_2) (c11_2) ((replace_Znth (block1) (((Znth block1 c10_2 (0 : Int)) + 1)) (c10_2)))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_max_edit_string_matches_entail_wit_5_2 : max_edit_string_matches_entail_wit_5_2 := by
  unfold max_edit_string_matches_entail_wit_5_2
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1_2 c10_2 c11_2 c20_2 c21_2 i block1 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29
  prop_apply (intArray.full_Zlength (( &( "cnt11" ) )) (n_pre) ((replace_Znth (block1) (((Znth block1 c11_2 (0 : Int)) + 1)) (c11_2))))
  Intros_p hlength_0
  simp only [Zlength_replace_Znth] at hlength_0
  prop_apply (intArray.full_Zlength (s1_pre) (n_pre) (s1_l))
  Intros_p hlength_1
  prop_apply (intArray.seg_Zlength (( &( "seg1" ) )) ((0 : Int)) ((i + 1)) (sg1_2))
  Intros_p hlength_5
  simp only [Int.sub_zero] at hlength_5
  prop_apply (intArray.full_Zlength (( &( "cnt10" ) )) (n_pre) (c10_2))
  Intros_p hlength_6
  have hread := edit_bounded_read s1_l i 0 1 PreH6 PreH7 (by omega)
  have hn := edit_counts_inc_one s1_l t1_l n_pre i sg1_2 c10_2 c11_2 block1 (by omega) (by omega) (by omega) (by omega) (by omega) PreH28 PreH29 PreH27 (by omega)
  have hnew : EditBuildMeaning s1_l t1_l n_pre (i+1) sg1_2 (c10_2) ((replace_Znth (block1) (((Znth block1 c11_2 (0 : Int)) + 1)) (c11_2))) := ⟨PreH28,by simpa only [Int.sub_zero] using hn⟩
  have hbounds := edit_counts_bounds s1_l t1_l n_pre (i+1) (c10_2) ((replace_Znth (block1) (((Znth block1 c11_2 (0 : Int)) + 1)) (c11_2))) (by omega) (by omega) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) hnew.2
  rcases hbounds with ⟨⟨hc0lo,hc0hi⟩,⟨hc1lo,hc1hi⟩⟩
  Exists (sg1_2) (c21_2) (c20_2) ((replace_Znth (block1) (((Znth block1 c11_2 (0 : Int)) + 1)) (c11_2))) (c10_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_max_edit_string_matches_entail_wit_6_1 : max_edit_string_matches_entail_wit_6_1 := by
  unfold max_edit_string_matches_entail_wit_6_1
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1_2 c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  prop_apply (intArray.full_Zlength (( &( "cnt20" ) )) (n_pre) ((replace_Znth ((0 : Int)) (((Znth (0 : Int) c20_2 (0 : Int)) + 1)) (c20_2))))
  Intros_p hlength_0
  simp only [Zlength_replace_Znth] at hlength_0
  prop_apply (intArray.full_Zlength (s2_pre) (n_pre) (s2_l))
  Intros_p hlength_1
  prop_apply (intArray.full_Zlength (( &( "cnt21" ) )) (n_pre) (c21_2))
  Intros_p hlength_8
  have hn := edit_build_first_zero s2_l t2_l n_pre c20_2 c21_2 (by omega) (by omega) (by omega) (by omega) PreH23 PreH24 PreH1
  have hnew : EditBuildMeaning s2_l t2_l n_pre 1 [0] ((replace_Znth ((0 : Int)) (((Znth (0 : Int) c20_2 (0 : Int)) + 1)) (c20_2))) (c21_2) := by simpa only [Int.sub_zero] using hn
  have hc := edit_counts_bounds s2_l t2_l n_pre 1 ((replace_Znth ((0 : Int)) (((Znth (0 : Int) c20_2 (0 : Int)) + 1)) (c20_2))) (c21_2) (by omega) (by omega) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) hnew.2
  rcases hc with ⟨⟨hc0lo,hc0hi⟩,⟨hc1lo,hc1hi⟩⟩
  have hbuild1 : EditBuildMeaning s1_l t1_l n_pre n_pre sg1_2 c10_2 c11_2 := by simpa only [show i=n_pre by omega] using PreH25
  sep_apply (intArray.seg_to_full (( &( "seg1" ) )) ((0 : Int)) (i) (sg1_2))
  have hiEq : i=n_pre := by omega
  rw [hiEq]
  sep_apply (intArray.seg_single ( &( "seg2" ) ) 0 0)
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  Exists (([0] : List Int)) (sg1_2) (c21_2) ((replace_Znth ((0 : Int)) (((Znth (0 : Int) c20_2 (0 : Int)) + 1)) (c20_2))) (c11_2) (c10_2)
  split_pure_spatial
  · simp only [Int.zero_add,Int.sub_zero]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_max_edit_string_matches_entail_wit_6_2 : max_edit_string_matches_entail_wit_6_2 := by
  unfold max_edit_string_matches_entail_wit_6_2
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1_2 c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  prop_apply (intArray.full_Zlength (( &( "cnt21" ) )) (n_pre) ((replace_Znth ((0 : Int)) (((Znth (0 : Int) c21_2 (0 : Int)) + 1)) (c21_2))))
  Intros_p hlength_0
  simp only [Zlength_replace_Znth] at hlength_0
  prop_apply (intArray.full_Zlength (s2_pre) (n_pre) (s2_l))
  Intros_p hlength_1
  prop_apply (intArray.full_Zlength (( &( "cnt20" ) )) (n_pre) (c20_2))
  Intros_p hlength_8
  have hn := edit_build_first_one s2_l t2_l n_pre c20_2 c21_2 (by omega) (by omega) (by omega) (by omega) PreH23 PreH24 PreH9 PreH10 PreH1
  have hnew : EditBuildMeaning s2_l t2_l n_pre 1 [0] (c20_2) ((replace_Znth ((0 : Int)) (((Znth (0 : Int) c21_2 (0 : Int)) + 1)) (c21_2))) := by simpa only [Int.sub_zero] using hn
  have hc := edit_counts_bounds s2_l t2_l n_pre 1 (c20_2) ((replace_Znth ((0 : Int)) (((Znth (0 : Int) c21_2 (0 : Int)) + 1)) (c21_2))) (by omega) (by omega) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) hnew.2
  rcases hc with ⟨⟨hc0lo,hc0hi⟩,⟨hc1lo,hc1hi⟩⟩
  have hbuild1 : EditBuildMeaning s1_l t1_l n_pre n_pre sg1_2 c10_2 c11_2 := by simpa only [show i=n_pre by omega] using PreH25
  sep_apply (intArray.seg_to_full (( &( "seg1" ) )) ((0 : Int)) (i) (sg1_2))
  have hiEq : i=n_pre := by omega
  rw [hiEq]
  sep_apply (intArray.seg_single ( &( "seg2" ) ) 0 0)
  simp only [Int.zero_mul,Int.add_zero,Int.sub_zero]
  Exists (([0] : List Int)) (sg1_2) ((replace_Znth ((0 : Int)) (((Znth (0 : Int) c21_2 (0 : Int)) + 1)) (c21_2))) (c20_2) (c11_2) (c10_2)
  split_pure_spatial
  · simp only [Int.zero_add,Int.sub_zero]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_max_edit_string_matches_entail_wit_7_1 : max_edit_string_matches_entail_wit_7_1 := by
  unfold max_edit_string_matches_entail_wit_7_1
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg2 sg1_2 c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  prop_apply (intArray.seg_Zlength (( &( "seg2" ) )) ((0 : Int)) ((i + 1)) ((sg2 ++ ((Znth ((i - 1) - (0 : Int)) sg2 (0 : Int)) :: (@List.nil Int)))))
  Intros_p hlength_0
  simp only [Zlength_app,Zlength_cons,Zlength_nil,Int.sub_zero] at hlength_0
  have hm := edit_segment_extend_same t2_l sg2 i (by omega) (by omega) PreH25.1 (by exact ⟨PreH2,PreH1⟩)
  have hnew : EditSegmentMeaning t2_l (i+1) ((sg2 ++ ((Znth ((i - 1) - (0 : Int)) sg2 (0 : Int)) :: (@List.nil Int)))) := by simpa only [Int.sub_zero] using hm
  have hbound := edit_segment_bound t2_l ((sg2 ++ ((Znth ((i - 1) - (0 : Int)) sg2 (0 : Int)) :: (@List.nil Int)))) (i+1) i hnew (by omega)
  have hcounts := PreH25.2
  Exists ((sg2 ++ ((Znth ((i - 1) - (0 : Int)) sg2 (0 : Int)) :: (@List.nil Int)))) (sg1_2) (c21_2) (c20_2) (c11_2) (c10_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega | (simpa only [Int.sub_zero] using hbound.1) | (simpa only [Int.sub_zero] using hbound.2)

theorem proof_of_max_edit_string_matches_entail_wit_7_2 : max_edit_string_matches_entail_wit_7_2 := by
  unfold max_edit_string_matches_entail_wit_7_2
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg2 sg1_2 c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  prop_apply (intArray.seg_Zlength (( &( "seg2" ) )) ((0 : Int)) ((i + 1)) ((sg2 ++ (i :: (@List.nil Int)))))
  Intros_p hlength_0
  simp only [Zlength_app,Zlength_cons,Zlength_nil,Int.sub_zero] at hlength_0
  have hm := edit_segment_extend_new t2_l sg2 i (by omega) (by omega) PreH24.1 (by intro he; have hl := he.1; have hr := he.2; omega)
  have hnew : EditSegmentMeaning t2_l (i+1) ((sg2 ++ (i :: (@List.nil Int)))) := by simpa only [Int.sub_zero] using hm
  have hbound := edit_segment_bound t2_l ((sg2 ++ (i :: (@List.nil Int)))) (i+1) i hnew (by omega)
  have hcounts := PreH24.2
  Exists ((sg2 ++ (i :: (@List.nil Int)))) (sg1_2) (c21_2) (c20_2) (c11_2) (c10_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega | (simpa only [Int.sub_zero] using hbound.1) | (simpa only [Int.sub_zero] using hbound.2)

theorem proof_of_max_edit_string_matches_entail_wit_7_3 : max_edit_string_matches_entail_wit_7_3 := by
  unfold max_edit_string_matches_entail_wit_7_3
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg2 sg1_2 c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25
  prop_apply (intArray.seg_Zlength (( &( "seg2" ) )) ((0 : Int)) ((i + 1)) ((sg2 ++ (i :: (@List.nil Int)))))
  Intros_p hlength_0
  simp only [Zlength_app,Zlength_cons,Zlength_nil,Int.sub_zero] at hlength_0
  have hm := edit_segment_extend_new t2_l sg2 i (by omega) (by omega) PreH25.1 (by intro he; have hl := he.1; have hr := he.2; omega)
  have hnew : EditSegmentMeaning t2_l (i+1) ((sg2 ++ (i :: (@List.nil Int)))) := by simpa only [Int.sub_zero] using hm
  have hbound := edit_segment_bound t2_l ((sg2 ++ (i :: (@List.nil Int)))) (i+1) i hnew (by omega)
  have hcounts := PreH25.2
  Exists ((sg2 ++ (i :: (@List.nil Int)))) (sg1_2) (c21_2) (c20_2) (c11_2) (c10_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega | (simpa only [Int.sub_zero] using hbound.1) | (simpa only [Int.sub_zero] using hbound.2)

theorem proof_of_max_edit_string_matches_entail_wit_8_1 : max_edit_string_matches_entail_wit_8_1 := by
  unfold max_edit_string_matches_entail_wit_8_1
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 i block2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  prop_apply (intArray.full_Zlength (( &( "cnt20" ) )) (n_pre) ((replace_Znth (block2) (((Znth block2 c20_2 (0 : Int)) + 1)) (c20_2))))
  Intros_p hlength_0
  simp only [Zlength_replace_Znth] at hlength_0
  prop_apply (intArray.full_Zlength (s2_pre) (n_pre) (s2_l))
  Intros_p hlength_1
  prop_apply (intArray.seg_Zlength (( &( "seg2" ) )) ((0 : Int)) ((i + 1)) (sg2_2))
  Intros_p hlength_6
  simp only [Int.sub_zero] at hlength_6
  prop_apply (intArray.full_Zlength (( &( "cnt21" ) )) (n_pre) (c21_2))
  Intros_p hlength_9
  have hread := edit_bounded_read s2_l i 0 1 PreH8 PreH9 (by omega)
  have hn := edit_counts_inc_zero s2_l t2_l n_pre i sg2_2 c20_2 c21_2 block2 (by omega) (by omega) (by omega) (by omega) (by omega) PreH27 PreH28 PreH26 (by omega)
  have hnew : EditBuildMeaning s2_l t2_l n_pre (i+1) sg2_2 ((replace_Znth (block2) (((Znth block2 c20_2 (0 : Int)) + 1)) (c20_2))) (c21_2) := ⟨PreH27,by simpa only [Int.sub_zero] using hn⟩
  have hbounds := edit_counts_bounds s2_l t2_l n_pre (i+1) ((replace_Znth (block2) (((Znth block2 c20_2 (0 : Int)) + 1)) (c20_2))) (c21_2) (by omega) (by omega) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) hnew.2
  rcases hbounds with ⟨⟨hc0lo,hc0hi⟩,⟨hc1lo,hc1hi⟩⟩
  Exists (sg2_2) (sg1_2) (c21_2) ((replace_Znth (block2) (((Znth block2 c20_2 (0 : Int)) + 1)) (c20_2))) (c11_2) (c10_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_max_edit_string_matches_entail_wit_8_2 : max_edit_string_matches_entail_wit_8_2 := by
  unfold max_edit_string_matches_entail_wit_8_2
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 i block2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28
  prop_apply (intArray.full_Zlength (( &( "cnt21" ) )) (n_pre) ((replace_Znth (block2) (((Znth block2 c21_2 (0 : Int)) + 1)) (c21_2))))
  Intros_p hlength_0
  simp only [Zlength_replace_Znth] at hlength_0
  prop_apply (intArray.full_Zlength (s2_pre) (n_pre) (s2_l))
  Intros_p hlength_1
  prop_apply (intArray.seg_Zlength (( &( "seg2" ) )) ((0 : Int)) ((i + 1)) (sg2_2))
  Intros_p hlength_6
  simp only [Int.sub_zero] at hlength_6
  prop_apply (intArray.full_Zlength (( &( "cnt20" ) )) (n_pre) (c20_2))
  Intros_p hlength_9
  have hread := edit_bounded_read s2_l i 0 1 PreH8 PreH9 (by omega)
  have hn := edit_counts_inc_one s2_l t2_l n_pre i sg2_2 c20_2 c21_2 block2 (by omega) (by omega) (by omega) (by omega) (by omega) PreH27 PreH28 PreH26 (by omega)
  have hnew : EditBuildMeaning s2_l t2_l n_pre (i+1) sg2_2 (c20_2) ((replace_Znth (block2) (((Znth block2 c21_2 (0 : Int)) + 1)) (c21_2))) := ⟨PreH27,by simpa only [Int.sub_zero] using hn⟩
  have hbounds := edit_counts_bounds s2_l t2_l n_pre (i+1) (c20_2) ((replace_Znth (block2) (((Znth block2 c21_2 (0 : Int)) + 1)) (c21_2))) (by omega) (by omega) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) hnew.2
  rcases hbounds with ⟨⟨hc0lo,hc0hi⟩,⟨hc1lo,hc1hi⟩⟩
  Exists (sg2_2) (sg1_2) ((replace_Znth (block2) (((Znth block2 c21_2 (0 : Int)) + 1)) (c21_2))) (c20_2) (c11_2) (c10_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_max_edit_string_matches_entail_wit_9 : max_edit_string_matches_entail_wit_9 := by
  unfold max_edit_string_matches_entail_wit_9
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg2_2 sg1_2 c21_2 c20_2 c11_2 c10_2 i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23
  prop_apply (intArray.full_Zlength (s1_pre) (n_pre) (s1_l))
  Intros_p hlength_0
  prop_apply (intArray.full_Zlength (s2_pre) (n_pre) (s2_l))
  Intros_p hlength_1
  prop_apply (intArray.full_Zlength (t1_pre) (n_pre) (t1_l))
  Intros_p hlength_2
  prop_apply (intArray.full_Zlength (t2_pre) (n_pre) (t2_l))
  Intros_p hlength_3
  prop_apply (intArray.full_Zlength (( &( "seg1" ) )) (n_pre) (sg1_2))
  Intros_p hlength_4
  prop_apply (intArray.seg_Zlength (( &( "seg2" ) )) ((0 : Int)) (i) (sg2_2))
  Intros_p hlength_5
  simp only [Int.sub_zero] at hlength_5
  have hbinary1 : Forall (fun bit : Int => bit=0 ∨ bit=1) s1_l := by
    apply edit_Forall_of_read
    intro idx hi
    have hb := edit_bounded_read s1_l idx 0 1 PreH6 PreH7 (by omega)
    omega
  have hbinary2 : Forall (fun bit : Int => bit=0 ∨ bit=1) s2_l := by
    apply edit_Forall_of_read
    intro idx hi
    have hb := edit_bounded_read s2_l idx 0 1 PreH8 PreH9 (by omega)
    omega
  have hbuild2 : EditBuildMeaning s2_l t2_l n_pre n_pre sg2_2 c20_2 c21_2 := by
    simpa only [show i=n_pre by omega] using PreH23
  obtain ⟨answer,hremaining,hanswer⟩ := edit_initial_remaining s1_l s2_l t1_l t2_l sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 n_pre
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hbinary1 hbinary2 PreH22 hbuild2
  have hseg1 := PreH22.1
  have hseg2 := hbuild2.1
  have hans : EditStringsAnswer (s1_l.map (48+·)) (s2_l.map (48+·)) (t1_l.map (48+·)) (t2_l.map (48+·)) (0+answer) := by
    simpa only [Int.zero_add] using hanswer
  rw [show i=n_pre by omega]
  sep_apply (intArray.undef_seg_empty (&("seg2")) n_pre).left
  sep_apply (intArray.seg_to_full (&("seg2")) 0 n_pre sg2_2)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  Exists answer ([] : List Int) ([] : List Int) sg2_2 sg1_2 c21_2 c20_2 c11_2 c10_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_max_edit_string_matches_entail_wit_10 : max_edit_string_matches_entail_wit_10 := by
  unfold max_edit_string_matches_entail_wit_10
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre rest_2 prefix2_2 prefix1_2 sg2 sg1 c21_2 c20_2 c11_2 c10_2 ans i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  have hb1 := edit_segment_bound t1_l sg1 n_pre i PreH24 (by omega)
  have hb2 := edit_segment_bound t2_l sg2 n_pre i PreH25 (by omega)
  Exists rest_2 prefix2_2 prefix1_2 sg2 sg1 c21_2 c20_2 c11_2 c10_2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega

theorem proof_of_max_edit_string_matches_entail_wit_11_1 : max_edit_string_matches_entail_wit_11_1 := by
  unfold max_edit_string_matches_entail_wit_11_1
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 rest_2 prefix1_2 prefix2_2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  prop_apply (intArray.full_Zlength (( &( "cnt20" ) )) (n_pre) ((replace_Znth (b) (((Znth b c20_2 (0 : Int)) - 1)) (c20_2))))
  Intros_p hlength_0
  simp only [Zlength_replace_Znth] at hlength_0
  prop_apply (intArray.full_Zlength (( &( "cnt10" ) )) (n_pre) ((replace_Znth (a) (((Znth a c10_2 (0 : Int)) - 1)) (c10_2))))
  Intros_p hlength_1
  simp only [Zlength_replace_Znth] at hlength_1
  prop_apply (intArray.full_Zlength (t1_pre) (n_pre) (t1_l))
  Intros_p hlength_4
  prop_apply (intArray.full_Zlength (t2_pre) (n_pre) (t2_l))
  Intros_p hlength_5
  prop_apply (intArray.full_Zlength (( &( "seg1" ) )) (n_pre) (sg1_2))
  Intros_p hlength_6
  prop_apply (intArray.full_Zlength (( &( "seg2" ) )) (n_pre) (sg2_2))
  Intros_p hlength_7
  prop_apply (intArray.full_Zlength (( &( "cnt11" ) )) (n_pre) (c11_2))
  Intros_p hlength_8
  prop_apply (intArray.full_Zlength (( &( "cnt21" ) )) (n_pre) (c21_2))
  Intros_p hlength_9
  have hn := edit_remaining_common_step s1_l s2_l t1_l t2_l sg1_2 sg2_2 prefix1_2 prefix2_2 i c10_2 c11_2 c20_2 c21_2 n_pre a b 0 rest_2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) PreH25 PreH26 (by omega) (by omega) (by omega) (by assumption) (by assumption) (by omega) (by omega) (by omega) (by simpa only [Int.reduceEq,ite_true,ite_false] using PreH2) (by simpa only [Int.reduceEq,ite_true,ite_false] using PreH1) PreH30
  simp only [Int.reduceEq,ite_true,ite_false] at hn
  have hnext : EditRemainingMatches s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2++[0]) (prefix2_2++[0]) (i+1) ((replace_Znth (a) (((Znth a c10_2 (0 : Int)) - 1)) (c10_2))) (c11_2) ((replace_Znth (b) (((Znth b c20_2 (0 : Int)) - 1)) (c20_2))) (c21_2) (rest_2-1) := by
    simpa only [Int.sub_zero] using hn
  have hc := edit_remaining_count_bounds s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2++[0]) (prefix2_2++[0]) (i+1) ((replace_Znth (a) (((Znth a c10_2 (0 : Int)) - 1)) (c10_2))) (c11_2) ((replace_Znth (b) (((Znth b c20_2 (0 : Int)) - 1)) (c20_2))) (c21_2) n_pre (rest_2-1)
    (by omega) (by omega) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by omega) hnext
  rcases hc with ⟨⟨hc10lo,hc10hi⟩,⟨hc11lo,hc11hi⟩,⟨hc20lo,hc20hi⟩,⟨hc21lo,hc21hi⟩⟩
  have hmatch : (ans+1)=EditPairMatches (prefix1_2++[0]) (prefix2_2++[0]) := by
    rw [edit_pair_app prefix1_2 prefix2_2 [0] [0] (by omega)]
    have hlast : EditPairMatches [0] [0]=1 := rfl
    rw [hlast]
    omega
  have hans : EditStringsAnswer (s1_l.map (48+·)) (s2_l.map (48+·)) (t1_l.map (48+·)) (t2_l.map (48+·)) ((ans+1)+(rest_2-1)) := by
    convert PreH31 using 1 <;> omega
  Exists (rest_2-1) (prefix2_2++[0]) (prefix1_2++[0]) sg2_2 sg1_2 (c21_2) ((replace_Znth (b) (((Znth b c20_2 (0 : Int)) - 1)) (c20_2))) (c11_2) ((replace_Znth (a) (((Znth a c10_2 (0 : Int)) - 1)) (c10_2)))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega | (simp only [Zlength_app,Zlength_cons,Zlength_nil] <;> omega)

theorem proof_of_max_edit_string_matches_entail_wit_11_2 : max_edit_string_matches_entail_wit_11_2 := by
  unfold max_edit_string_matches_entail_wit_11_2
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 rest_2 prefix1_2 prefix2_2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  prop_apply (intArray.full_Zlength (( &( "cnt21" ) )) (n_pre) ((replace_Znth (b) (((Znth b c21_2 (0 : Int)) - 1)) (c21_2))))
  Intros_p hlength_0
  simp only [Zlength_replace_Znth] at hlength_0
  prop_apply (intArray.full_Zlength (( &( "cnt11" ) )) (n_pre) ((replace_Znth (a) (((Znth a c11_2 (0 : Int)) - 1)) (c11_2))))
  Intros_p hlength_1
  simp only [Zlength_replace_Znth] at hlength_1
  prop_apply (intArray.full_Zlength (( &( "cnt10" ) )) (n_pre) (c10_2))
  Intros_p hlength_2
  prop_apply (intArray.full_Zlength (t1_pre) (n_pre) (t1_l))
  Intros_p hlength_5
  prop_apply (intArray.full_Zlength (t2_pre) (n_pre) (t2_l))
  Intros_p hlength_6
  prop_apply (intArray.full_Zlength (( &( "seg1" ) )) (n_pre) (sg1_2))
  Intros_p hlength_7
  prop_apply (intArray.full_Zlength (( &( "seg2" ) )) (n_pre) (sg2_2))
  Intros_p hlength_8
  prop_apply (intArray.full_Zlength (( &( "cnt20" ) )) (n_pre) (c20_2))
  Intros_p hlength_9
  have hn := edit_remaining_common_step s1_l s2_l t1_l t2_l sg1_2 sg2_2 prefix1_2 prefix2_2 i c10_2 c11_2 c20_2 c21_2 n_pre a b 1 rest_2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) PreH26 PreH27 (by omega) (by omega) (by omega) (by assumption) (by assumption) (by omega) (by omega) (by omega) (by simpa only [Int.reduceEq,ite_true,ite_false] using PreH2) (by simpa only [Int.reduceEq,ite_true,ite_false] using PreH1) PreH31
  simp only [Int.reduceEq,ite_true,ite_false] at hn
  have hnext : EditRemainingMatches s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2++[1]) (prefix2_2++[1]) (i+1) (c10_2) ((replace_Znth (a) (((Znth a c11_2 (0 : Int)) - 1)) (c11_2))) (c20_2) ((replace_Znth (b) (((Znth b c21_2 (0 : Int)) - 1)) (c21_2))) (rest_2-1) := by
    simpa only [Int.sub_zero] using hn
  have hc := edit_remaining_count_bounds s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2++[1]) (prefix2_2++[1]) (i+1) (c10_2) ((replace_Znth (a) (((Znth a c11_2 (0 : Int)) - 1)) (c11_2))) (c20_2) ((replace_Znth (b) (((Znth b c21_2 (0 : Int)) - 1)) (c21_2))) n_pre (rest_2-1)
    (by omega) (by omega) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by omega) hnext
  rcases hc with ⟨⟨hc10lo,hc10hi⟩,⟨hc11lo,hc11hi⟩,⟨hc20lo,hc20hi⟩,⟨hc21lo,hc21hi⟩⟩
  have hmatch : (ans+1)=EditPairMatches (prefix1_2++[1]) (prefix2_2++[1]) := by
    rw [edit_pair_app prefix1_2 prefix2_2 [1] [1] (by omega)]
    have hlast : EditPairMatches [1] [1]=1 := rfl
    rw [hlast]
    omega
  have hans : EditStringsAnswer (s1_l.map (48+·)) (s2_l.map (48+·)) (t1_l.map (48+·)) (t2_l.map (48+·)) ((ans+1)+(rest_2-1)) := by
    convert PreH32 using 1 <;> omega
  Exists (rest_2-1) (prefix2_2++[1]) (prefix1_2++[1]) sg2_2 sg1_2 ((replace_Znth (b) (((Znth b c21_2 (0 : Int)) - 1)) (c21_2))) (c20_2) ((replace_Znth (a) (((Znth a c11_2 (0 : Int)) - 1)) (c11_2))) (c10_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega | (simp only [Zlength_app,Zlength_cons,Zlength_nil] <;> omega)

theorem proof_of_max_edit_string_matches_entail_wit_11_3 : max_edit_string_matches_entail_wit_11_3 := by
  unfold max_edit_string_matches_entail_wit_11_3
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 rest_2 prefix1_2 prefix2_2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  prop_apply (intArray.full_Zlength (( &( "cnt21" ) )) (n_pre) ((replace_Znth (b) (((Znth b c21_2 (0 : Int)) - 1)) (c21_2))))
  Intros_p hlength_0
  simp only [Zlength_replace_Znth] at hlength_0
  prop_apply (intArray.full_Zlength (( &( "cnt11" ) )) (n_pre) ((replace_Znth (a) (((Znth a c11_2 (0 : Int)) - 1)) (c11_2))))
  Intros_p hlength_1
  simp only [Zlength_replace_Znth] at hlength_1
  prop_apply (intArray.full_Zlength (( &( "cnt20" ) )) (n_pre) (c20_2))
  Intros_p hlength_2
  prop_apply (intArray.full_Zlength (( &( "cnt10" ) )) (n_pre) (c10_2))
  Intros_p hlength_3
  prop_apply (intArray.full_Zlength (t1_pre) (n_pre) (t1_l))
  Intros_p hlength_6
  prop_apply (intArray.full_Zlength (t2_pre) (n_pre) (t2_l))
  Intros_p hlength_7
  prop_apply (intArray.full_Zlength (( &( "seg1" ) )) (n_pre) (sg1_2))
  Intros_p hlength_8
  prop_apply (intArray.full_Zlength (( &( "seg2" ) )) (n_pre) (sg2_2))
  Intros_p hlength_9
  have hn := edit_remaining_common_step s1_l s2_l t1_l t2_l sg1_2 sg2_2 prefix1_2 prefix2_2 i c10_2 c11_2 c20_2 c21_2 n_pre a b 1 rest_2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) PreH27 PreH28 (by omega) (by omega) (by omega) (by assumption) (by assumption) (by omega) (by omega) (by omega) (by simpa only [Int.reduceEq,ite_true,ite_false] using PreH2) (by simpa only [Int.reduceEq,ite_true,ite_false] using PreH1) PreH32
  simp only [Int.reduceEq,ite_true,ite_false] at hn
  have hnext : EditRemainingMatches s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2++[1]) (prefix2_2++[1]) (i+1) (c10_2) ((replace_Znth (a) (((Znth a c11_2 (0 : Int)) - 1)) (c11_2))) (c20_2) ((replace_Znth (b) (((Znth b c21_2 (0 : Int)) - 1)) (c21_2))) (rest_2-1) := by
    simpa only [Int.sub_zero] using hn
  have hc := edit_remaining_count_bounds s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2++[1]) (prefix2_2++[1]) (i+1) (c10_2) ((replace_Znth (a) (((Znth a c11_2 (0 : Int)) - 1)) (c11_2))) (c20_2) ((replace_Znth (b) (((Znth b c21_2 (0 : Int)) - 1)) (c21_2))) n_pre (rest_2-1)
    (by omega) (by omega) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by omega) hnext
  rcases hc with ⟨⟨hc10lo,hc10hi⟩,⟨hc11lo,hc11hi⟩,⟨hc20lo,hc20hi⟩,⟨hc21lo,hc21hi⟩⟩
  have hmatch : (ans+1)=EditPairMatches (prefix1_2++[1]) (prefix2_2++[1]) := by
    rw [edit_pair_app prefix1_2 prefix2_2 [1] [1] (by omega)]
    have hlast : EditPairMatches [1] [1]=1 := rfl
    rw [hlast]
    omega
  have hans : EditStringsAnswer (s1_l.map (48+·)) (s2_l.map (48+·)) (t1_l.map (48+·)) (t2_l.map (48+·)) ((ans+1)+(rest_2-1)) := by
    convert PreH33 using 1 <;> omega
  Exists (rest_2-1) (prefix2_2++[1]) (prefix1_2++[1]) sg2_2 sg1_2 ((replace_Znth (b) (((Znth b c21_2 (0 : Int)) - 1)) (c21_2))) (c20_2) ((replace_Znth (a) (((Znth a c11_2 (0 : Int)) - 1)) (c11_2))) (c10_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega | (simp only [Zlength_app,Zlength_cons,Zlength_nil] <;> omega)

theorem proof_of_max_edit_string_matches_entail_wit_11_4 : max_edit_string_matches_entail_wit_11_4 := by
  unfold max_edit_string_matches_entail_wit_11_4
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 rest_2 prefix1_2 prefix2_2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  prop_apply (intArray.full_Zlength (( &( "cnt21" ) )) (n_pre) ((replace_Znth (b) (((Znth b c21_2 (0 : Int)) - 1)) (c21_2))))
  Intros_p hlength_0
  simp only [Zlength_replace_Znth] at hlength_0
  prop_apply (intArray.full_Zlength (( &( "cnt10" ) )) (n_pre) ((replace_Znth (a) (((Znth a c10_2 (0 : Int)) - 1)) (c10_2))))
  Intros_p hlength_1
  simp only [Zlength_replace_Znth] at hlength_1
  prop_apply (intArray.full_Zlength (( &( "cnt11" ) )) (n_pre) (c11_2))
  Intros_p hlength_2
  prop_apply (intArray.full_Zlength (( &( "cnt20" ) )) (n_pre) (c20_2))
  Intros_p hlength_3
  prop_apply (intArray.full_Zlength (t1_pre) (n_pre) (t1_l))
  Intros_p hlength_6
  prop_apply (intArray.full_Zlength (t2_pre) (n_pre) (t2_l))
  Intros_p hlength_7
  prop_apply (intArray.full_Zlength (( &( "seg1" ) )) (n_pre) (sg1_2))
  Intros_p hlength_8
  prop_apply (intArray.full_Zlength (( &( "seg2" ) )) (n_pre) (sg2_2))
  Intros_p hlength_9
  have hn := edit_remaining_zero_one_step s1_l s2_l t1_l t2_l sg1_2 sg2_2 prefix1_2 prefix2_2 i c10_2 c11_2 c20_2 c21_2 n_pre a b rest_2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by assumption) (by assumption) (by omega) (by omega) (by omega) (by omega) (by omega) PreH32
  simp only [Int.reduceEq,ite_true,ite_false] at hn
  have hnext : EditRemainingMatches s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2++[0]) (prefix2_2++[1]) (i+1) ((replace_Znth (a) (((Znth a c10_2 (0 : Int)) - 1)) (c10_2))) (c11_2) (c20_2) ((replace_Znth (b) (((Znth b c21_2 (0 : Int)) - 1)) (c21_2))) rest_2 := by
    simpa only [Int.sub_zero] using hn
  have hc := edit_remaining_count_bounds s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2++[0]) (prefix2_2++[1]) (i+1) ((replace_Znth (a) (((Znth a c10_2 (0 : Int)) - 1)) (c10_2))) (c11_2) (c20_2) ((replace_Znth (b) (((Znth b c21_2 (0 : Int)) - 1)) (c21_2))) n_pre rest_2
    (by omega) (by omega) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by omega) hnext
  rcases hc with ⟨⟨hc10lo,hc10hi⟩,⟨hc11lo,hc11hi⟩,⟨hc20lo,hc20hi⟩,⟨hc21lo,hc21hi⟩⟩
  have hmatch : ans=EditPairMatches (prefix1_2++[0]) (prefix2_2++[1]) := by
    rw [edit_pair_app prefix1_2 prefix2_2 [0] [1] (by omega)]
    have hlast : EditPairMatches [0] [1]=0 := rfl
    rw [hlast]
    omega
  have hans : EditStringsAnswer (s1_l.map (48+·)) (s2_l.map (48+·)) (t1_l.map (48+·)) (t2_l.map (48+·)) (ans+rest_2) := by
    convert PreH33 using 1 <;> omega
  Exists rest_2 (prefix2_2++[1]) (prefix1_2++[0]) sg2_2 sg1_2 ((replace_Znth (b) (((Znth b c21_2 (0 : Int)) - 1)) (c21_2))) (c20_2) (c11_2) ((replace_Znth (a) (((Znth a c10_2 (0 : Int)) - 1)) (c10_2)))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega | (simp only [Zlength_app,Zlength_cons,Zlength_nil] <;> omega)

theorem proof_of_max_edit_string_matches_entail_wit_11_5 : max_edit_string_matches_entail_wit_11_5 := by
  unfold max_edit_string_matches_entail_wit_11_5
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 rest_2 prefix1_2 prefix2_2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41
  prop_apply (intArray.full_Zlength (( &( "cnt21" ) )) (n_pre) ((replace_Znth (b) (((Znth b c21_2 (0 : Int)) - 1)) (c21_2))))
  Intros_p hlength_0
  simp only [Zlength_replace_Znth] at hlength_0
  prop_apply (intArray.full_Zlength (( &( "cnt10" ) )) (n_pre) ((replace_Znth (a) (((Znth a c10_2 (0 : Int)) - 1)) (c10_2))))
  Intros_p hlength_1
  simp only [Zlength_replace_Znth] at hlength_1
  prop_apply (intArray.full_Zlength (( &( "cnt11" ) )) (n_pre) (c11_2))
  Intros_p hlength_2
  prop_apply (intArray.full_Zlength (( &( "cnt20" ) )) (n_pre) (c20_2))
  Intros_p hlength_3
  prop_apply (intArray.full_Zlength (t1_pre) (n_pre) (t1_l))
  Intros_p hlength_6
  prop_apply (intArray.full_Zlength (t2_pre) (n_pre) (t2_l))
  Intros_p hlength_7
  prop_apply (intArray.full_Zlength (( &( "seg1" ) )) (n_pre) (sg1_2))
  Intros_p hlength_8
  prop_apply (intArray.full_Zlength (( &( "seg2" ) )) (n_pre) (sg2_2))
  Intros_p hlength_9
  have hn := edit_remaining_zero_one_step s1_l s2_l t1_l t2_l sg1_2 sg2_2 prefix1_2 prefix2_2 i c10_2 c11_2 c20_2 c21_2 n_pre a b rest_2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by assumption) (by assumption) (by omega) (by omega) (by omega) (by omega) (by omega) PreH33
  simp only [Int.reduceEq,ite_true,ite_false] at hn
  have hnext : EditRemainingMatches s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2++[0]) (prefix2_2++[1]) (i+1) ((replace_Znth (a) (((Znth a c10_2 (0 : Int)) - 1)) (c10_2))) (c11_2) (c20_2) ((replace_Znth (b) (((Znth b c21_2 (0 : Int)) - 1)) (c21_2))) rest_2 := by
    simpa only [Int.sub_zero] using hn
  have hc := edit_remaining_count_bounds s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2++[0]) (prefix2_2++[1]) (i+1) ((replace_Znth (a) (((Znth a c10_2 (0 : Int)) - 1)) (c10_2))) (c11_2) (c20_2) ((replace_Znth (b) (((Znth b c21_2 (0 : Int)) - 1)) (c21_2))) n_pre rest_2
    (by omega) (by omega) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by omega) hnext
  rcases hc with ⟨⟨hc10lo,hc10hi⟩,⟨hc11lo,hc11hi⟩,⟨hc20lo,hc20hi⟩,⟨hc21lo,hc21hi⟩⟩
  have hmatch : ans=EditPairMatches (prefix1_2++[0]) (prefix2_2++[1]) := by
    rw [edit_pair_app prefix1_2 prefix2_2 [0] [1] (by omega)]
    have hlast : EditPairMatches [0] [1]=0 := rfl
    rw [hlast]
    omega
  have hans : EditStringsAnswer (s1_l.map (48+·)) (s2_l.map (48+·)) (t1_l.map (48+·)) (t2_l.map (48+·)) (ans+rest_2) := by
    convert PreH34 using 1 <;> omega
  Exists rest_2 (prefix2_2++[1]) (prefix1_2++[0]) sg2_2 sg1_2 ((replace_Znth (b) (((Znth b c21_2 (0 : Int)) - 1)) (c21_2))) (c20_2) (c11_2) ((replace_Znth (a) (((Znth a c10_2 (0 : Int)) - 1)) (c10_2)))
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega | (simp only [Zlength_app,Zlength_cons,Zlength_nil] <;> omega)

theorem proof_of_max_edit_string_matches_entail_wit_11_6 : max_edit_string_matches_entail_wit_11_6 := by
  unfold max_edit_string_matches_entail_wit_11_6
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 rest_2 prefix1_2 prefix2_2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39
  prop_apply (intArray.full_Zlength (( &( "cnt20" ) )) (n_pre) ((replace_Znth (b) (((Znth b c20_2 (0 : Int)) - 1)) (c20_2))))
  Intros_p hlength_0
  simp only [Zlength_replace_Znth] at hlength_0
  prop_apply (intArray.full_Zlength (( &( "cnt11" ) )) (n_pre) ((replace_Znth (a) (((Znth a c11_2 (0 : Int)) - 1)) (c11_2))))
  Intros_p hlength_1
  simp only [Zlength_replace_Znth] at hlength_1
  prop_apply (intArray.full_Zlength (( &( "cnt10" ) )) (n_pre) (c10_2))
  Intros_p hlength_2
  prop_apply (intArray.full_Zlength (t1_pre) (n_pre) (t1_l))
  Intros_p hlength_5
  prop_apply (intArray.full_Zlength (t2_pre) (n_pre) (t2_l))
  Intros_p hlength_6
  prop_apply (intArray.full_Zlength (( &( "seg1" ) )) (n_pre) (sg1_2))
  Intros_p hlength_7
  prop_apply (intArray.full_Zlength (( &( "seg2" ) )) (n_pre) (sg2_2))
  Intros_p hlength_8
  prop_apply (intArray.full_Zlength (( &( "cnt21" ) )) (n_pre) (c21_2))
  Intros_p hlength_9
  have hn := edit_remaining_one_zero_step s1_l s2_l t1_l t2_l sg1_2 sg2_2 prefix1_2 prefix2_2 i c10_2 c11_2 c20_2 c21_2 n_pre a b rest_2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by assumption) (by assumption) (by omega) (by omega) (by omega) (by omega) PreH31
  simp only [Int.reduceEq,ite_true,ite_false] at hn
  have hnext : EditRemainingMatches s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2++[1]) (prefix2_2++[0]) (i+1) (c10_2) ((replace_Znth (a) (((Znth a c11_2 (0 : Int)) - 1)) (c11_2))) ((replace_Znth (b) (((Znth b c20_2 (0 : Int)) - 1)) (c20_2))) (c21_2) rest_2 := by
    simpa only [Int.sub_zero] using hn
  have hc := edit_remaining_count_bounds s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2++[1]) (prefix2_2++[0]) (i+1) (c10_2) ((replace_Znth (a) (((Znth a c11_2 (0 : Int)) - 1)) (c11_2))) ((replace_Znth (b) (((Znth b c20_2 (0 : Int)) - 1)) (c20_2))) (c21_2) n_pre rest_2
    (by omega) (by omega) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by omega) hnext
  rcases hc with ⟨⟨hc10lo,hc10hi⟩,⟨hc11lo,hc11hi⟩,⟨hc20lo,hc20hi⟩,⟨hc21lo,hc21hi⟩⟩
  have hmatch : ans=EditPairMatches (prefix1_2++[1]) (prefix2_2++[0]) := by
    rw [edit_pair_app prefix1_2 prefix2_2 [1] [0] (by omega)]
    have hlast : EditPairMatches [1] [0]=0 := rfl
    rw [hlast]
    omega
  have hans : EditStringsAnswer (s1_l.map (48+·)) (s2_l.map (48+·)) (t1_l.map (48+·)) (t2_l.map (48+·)) (ans+rest_2) := by
    convert PreH32 using 1 <;> omega
  Exists rest_2 (prefix2_2++[0]) (prefix1_2++[1]) sg2_2 sg1_2 (c21_2) ((replace_Znth (b) (((Znth b c20_2 (0 : Int)) - 1)) (c20_2))) ((replace_Znth (a) (((Znth a c11_2 (0 : Int)) - 1)) (c11_2))) (c10_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega | (simp only [Zlength_app,Zlength_cons,Zlength_nil] <;> omega)

theorem proof_of_max_edit_string_matches_entail_wit_11_7 : max_edit_string_matches_entail_wit_11_7 := by
  unfold max_edit_string_matches_entail_wit_11_7
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre sg1_2 sg2_2 c10_2 c11_2 c20_2 c21_2 rest_2 prefix1_2 prefix2_2 i ans a b PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40
  prop_apply (intArray.full_Zlength (( &( "cnt20" ) )) (n_pre) ((replace_Znth (b) (((Znth b c20_2 (0 : Int)) - 1)) (c20_2))))
  Intros_p hlength_0
  simp only [Zlength_replace_Znth] at hlength_0
  prop_apply (intArray.full_Zlength (( &( "cnt11" ) )) (n_pre) ((replace_Znth (a) (((Znth a c11_2 (0 : Int)) - 1)) (c11_2))))
  Intros_p hlength_1
  simp only [Zlength_replace_Znth] at hlength_1
  prop_apply (intArray.full_Zlength (( &( "cnt10" ) )) (n_pre) (c10_2))
  Intros_p hlength_2
  prop_apply (intArray.full_Zlength (( &( "cnt21" ) )) (n_pre) (c21_2))
  Intros_p hlength_3
  prop_apply (intArray.full_Zlength (t1_pre) (n_pre) (t1_l))
  Intros_p hlength_6
  prop_apply (intArray.full_Zlength (t2_pre) (n_pre) (t2_l))
  Intros_p hlength_7
  prop_apply (intArray.full_Zlength (( &( "seg1" ) )) (n_pre) (sg1_2))
  Intros_p hlength_8
  prop_apply (intArray.full_Zlength (( &( "seg2" ) )) (n_pre) (sg2_2))
  Intros_p hlength_9
  have hn := edit_remaining_one_zero_step s1_l s2_l t1_l t2_l sg1_2 sg2_2 prefix1_2 prefix2_2 i c10_2 c11_2 c20_2 c21_2 n_pre a b rest_2
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by assumption) (by assumption) (by omega) (by omega) (by omega) (by omega) PreH32
  simp only [Int.reduceEq,ite_true,ite_false] at hn
  have hnext : EditRemainingMatches s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2++[1]) (prefix2_2++[0]) (i+1) (c10_2) ((replace_Znth (a) (((Znth a c11_2 (0 : Int)) - 1)) (c11_2))) ((replace_Znth (b) (((Znth b c20_2 (0 : Int)) - 1)) (c20_2))) (c21_2) rest_2 := by
    simpa only [Int.sub_zero] using hn
  have hc := edit_remaining_count_bounds s1_l s2_l t1_l t2_l sg1_2 sg2_2 (prefix1_2++[1]) (prefix2_2++[0]) (i+1) (c10_2) ((replace_Znth (a) (((Znth a c11_2 (0 : Int)) - 1)) (c11_2))) ((replace_Znth (b) (((Znth b c20_2 (0 : Int)) - 1)) (c20_2))) (c21_2) n_pre rest_2
    (by omega) (by omega) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by first | omega | (simp only [Zlength_replace_Znth] <;> omega)) (by omega) hnext
  rcases hc with ⟨⟨hc10lo,hc10hi⟩,⟨hc11lo,hc11hi⟩,⟨hc20lo,hc20hi⟩,⟨hc21lo,hc21hi⟩⟩
  have hmatch : ans=EditPairMatches (prefix1_2++[1]) (prefix2_2++[0]) := by
    rw [edit_pair_app prefix1_2 prefix2_2 [1] [0] (by omega)]
    have hlast : EditPairMatches [1] [0]=0 := rfl
    rw [hlast]
    omega
  have hans : EditStringsAnswer (s1_l.map (48+·)) (s2_l.map (48+·)) (t1_l.map (48+·)) (t2_l.map (48+·)) (ans+rest_2) := by
    convert PreH33 using 1 <;> omega
  Exists rest_2 (prefix2_2++[0]) (prefix1_2++[1]) sg2_2 sg1_2 (c21_2) ((replace_Znth (b) (((Znth b c20_2 (0 : Int)) - 1)) (c20_2))) ((replace_Znth (a) (((Znth a c11_2 (0 : Int)) - 1)) (c11_2))) (c10_2)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | rfl | trivial | omega | (simp only [Zlength_app,Zlength_cons,Zlength_nil] <;> omega)

theorem proof_of_max_edit_string_matches_entail_wit_12 : max_edit_string_matches_entail_wit_12 := by
  unfold max_edit_string_matches_entail_wit_12
  left
  intro t2_l t1_l s2_l s1_l s1_pre s2_pre t1_pre t2_pre n_pre rest prefix2 prefix1 sg2 sg1 c21 c20 c11 c10 ans i PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30
  prop_apply (intArray.full_Zlength (( &( "seg1" ) )) (n_pre) (sg1))
  Intros_p hlength_4
  prop_apply (intArray.full_Zlength (( &( "seg2" ) )) (n_pre) (sg2))
  Intros_p hlength_5
  have hempty : EditRemainingMatches s1_l s2_l t1_l t2_l sg1 sg2 prefix1 prefix2 n_pre c10 c11 c20 c21 rest := by
    simpa only [show i=n_pre by omega] using PreH29
  have hr := edit_remaining_empty s1_l s2_l t1_l t2_l sg1 sg2 prefix1 prefix2 c10 c11 c20 c21 n_pre rest (by omega) (by omega) hempty
  have hans : EditStringsAnswer (s1_l.map (48+·)) (s2_l.map (48+·)) (t1_l.map (48+·)) (t2_l.map (48+·)) ans := by
    simpa only [hr,Int.add_zero] using PreH30
  sep_apply (intArray.full_to_seg ( &( "seg1" ) ) n_pre sg1)
  sep_apply (intArray.seg_to_undef_seg ( &( "seg1" ) ) 0 n_pre sg1)
  sep_apply (intArray.undef_seg_merge_to_undef_full ( &( "seg1" ) ) 0 n_pre 100000 (by omega))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  sep_apply (intArray.full_to_seg ( &( "seg2" ) ) n_pre sg2)
  sep_apply (intArray.seg_to_undef_seg ( &( "seg2" ) ) 0 n_pre sg2)
  sep_apply (intArray.undef_seg_merge_to_undef_full ( &( "seg2" ) ) 0 n_pre 100000 (by omega))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  sep_apply (intArray.full_to_seg ( &( "cnt10" ) ) n_pre c10)
  sep_apply (intArray.seg_to_undef_seg ( &( "cnt10" ) ) 0 n_pre c10)
  sep_apply (intArray.undef_seg_merge_to_undef_full ( &( "cnt10" ) ) 0 n_pre 100000 (by omega))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  sep_apply (intArray.full_to_seg ( &( "cnt11" ) ) n_pre c11)
  sep_apply (intArray.seg_to_undef_seg ( &( "cnt11" ) ) 0 n_pre c11)
  sep_apply (intArray.undef_seg_merge_to_undef_full ( &( "cnt11" ) ) 0 n_pre 100000 (by omega))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  sep_apply (intArray.full_to_seg ( &( "cnt20" ) ) n_pre c20)
  sep_apply (intArray.seg_to_undef_seg ( &( "cnt20" ) ) 0 n_pre c20)
  sep_apply (intArray.undef_seg_merge_to_undef_full ( &( "cnt20" ) ) 0 n_pre 100000 (by omega))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  sep_apply (intArray.full_to_seg ( &( "cnt21" ) ) n_pre c21)
  sep_apply (intArray.seg_to_undef_seg ( &( "cnt21" ) ) 0 n_pre c21)
  sep_apply (intArray.undef_seg_merge_to_undef_full ( &( "cnt21" ) ) 0 n_pre 100000 (by omega))
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    exact hans

end SimpleC.EE.LLM_bench.Algorithms.edit_strings.edit_strings_proof_manual
