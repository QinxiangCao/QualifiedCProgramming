import SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_goal

set_option maxHeartbeats 2000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false

namespace SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open coin_change_goal coin_change_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.undef_seg

private theorem scratch_cleanup (x k cap : Int) (l : List Int) (hk : 0 ≤ k) :
    intArray.full x k l ** intArray.undef_seg x k cap |-- intArray.undef_full x cap := by
  prop_apply (intArray.undef_seg_valid x k cap)
  Intros_p hcap
  sep_apply (intArray.full_to_undef_full x k l)
  sep_apply (intArray.undef_full_to_undef_seg x k)
  sep_apply (intArray.undef_seg_merge_to_undef_full x 0 k cap ⟨hk, hcap⟩)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  cancel

-- Previously proved auxiliary statements retained for proof audits.
private theorem annotation_Forall_nth_in (P : Int → Prop) (l : List Int) (i d : Int)
    (h : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l d) := by
  have hin : i.toNat < l.length := by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega
  have hp := h.mem (List.getElem_mem (l := l) hin)
  simpa only [Znth, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hin, Option.getD_some] using hp

theorem proof_of_coinChange_entail_wit_1 : coinChange_entail_wit_1 := by
  unfold coinChange_entail_wit_1
  right
  intro amount_pre coinsSize_pre coins_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8
  have hp : DpPrefixZeroed [1] 1 := by
    refine ⟨by omega, by simp [Zlength], rfl, ?_⟩
    intro k hk; omega
  Exists ([1] : List Int)
  split_pure_spatial
  · exact intArray.seg_single ( &( "dp" ) ) 0 (1 : Int)
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_coinChange_entail_wit_2 : coinChange_entail_wit_2 := by
  unfold coinChange_entail_wit_2
  left
  intro amount_pre coinsSize_pre coins_pre coins_l dp_l_2 j NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8
  prop_apply (intArray.full_Zlength coins_pre coinsSize_pre coins_l)
  Intros_p coins_length
  have PreH9 : (DpPrefixZeroed dp_l_2 j) := NewPreH8
  prop_apply (intArray.seg_Zlength ( &( "dp" ) ) 0 (j + 1) (dp_l_2 ++ [0]))
  Intros_p hlen
  have hp := DpPrefixZeroed_snoc_zero dp_l_2 j (by omega) PreH9 (by simpa using hlen)
  Exists (dp_l_2 ++ [0])
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_3 : coinChange_entail_wit_3 := by
  unfold coinChange_entail_wit_3
  left
  intro amount_pre coinsSize_pre coins_pre coins_l dp_l_2 j NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8
  prop_apply (intArray.full_Zlength coins_pre coinsSize_pre coins_l)
  Intros_p coins_length
  have PreH9 : (DpPrefixZeroed dp_l_2 j) := NewPreH8
  have hj : j = amount_pre + 1 := by omega
  subst j
  have hp := DpPrefixZeroed_to_DpReachableTable_nil dp_l_2 (amount_pre + 1) PreH9
  Exists dp_l_2
  sep_apply (((naive_C_Rules.toContext.logic_equiv_derivable1 _ _).mp
    (intArray.undef_seg_empty ( &( "dp" ) ) (amount_pre + 1))).1)
  sep_apply (intArray.seg_to_full ( &( "dp" ) ) 0 (amount_pre + 1) dp_l_2)
  simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_4 : coinChange_entail_wit_4 := by
  unfold coinChange_entail_wit_4
  left
  intro amount_pre coinsSize_pre coins_pre coins_l dp_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9
  prop_apply (intArray.full_Zlength coins_pre coinsSize_pre coins_l)
  Intros_p coins_length
  have current_coin_positive : 1 ≤ Znth i coins_l 0 := by
    exact annotation_Forall_nth_in _ coins_l i 0 NewPreH8 (by omega)
  have PreH12 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1)) := NewPreH9
  have hp : DpCoinInnerProgress (sublist 0 i coins_l) (Znth i coins_l 0) dp_l_2 (Znth i coins_l 0) amount_pre := by
    rcases PreH12 with ⟨hh, hlen, ht⟩
    refine ⟨by omega, by omega, by omega, hlen, ?_, ?_⟩
    · intro k hk
      exact (ht k (by omega)).trans (ReachableAmount_app_single_below _ (Znth i coins_l 0) k (by omega) hk).symm
    · intro k hk
      exact ht k (by omega)
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_5_1 : coinChange_entail_wit_5_1 := by
  unfold coinChange_entail_wit_5_1
  left
  intro amount_pre coinsSize_pre coins_pre coins_l dp_l_2 j coin i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13
  prop_apply (intArray.full_Zlength coins_pre coinsSize_pre coins_l)
  Intros_p coins_length
  have current_coin_positive : 1 ≤ Znth i coins_l 0 := by
    exact annotation_Forall_nth_in _ coins_l i 0 NewPreH7 (by omega)
  have PreH1 : ((Znth (j - coin) dp_l_2 (0 : Int)) ≠ (0 : Int)) := NewPreH1
  have PreH2 : (j <= amount_pre) := NewPreH2
  have PreH15 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre) := NewPreH13
  have hp := DpCoinInnerProgress_replace_current _ coin dp_l_2 j amount_pre PreH1 PreH2 PreH15
  Exists (replace_Znth j 1 dp_l_2)
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_5_2 : coinChange_entail_wit_5_2 := by
  unfold coinChange_entail_wit_5_2
  left
  intro amount_pre coinsSize_pre coins_pre coins_l dp_l_2 j coin i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12 NewPreH13
  prop_apply (intArray.full_Zlength coins_pre coinsSize_pre coins_l)
  Intros_p coins_length
  have current_coin_positive : 1 ≤ Znth i coins_l 0 := by
    exact annotation_Forall_nth_in _ coins_l i 0 NewPreH7 (by omega)
  have PreH1 : ((Znth (j - coin) dp_l_2 (0 : Int)) = (0 : Int)) := NewPreH1
  have PreH15 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre) := NewPreH13
  have hp : DpCoinInnerProgress (sublist 0 i coins_l) coin dp_l_2 (j + 1) amount_pre := by
    rcases PreH15 with ⟨hc, hcj, hja, hlen, hb, ha⟩
    refine ⟨hc, by omega, by omega, hlen, ?_, ?_⟩
    · intro k hk
      by_cases he : k = j
      · subst k
        constructor
        · intro hz
          exact ReachableAmount_app_l _ [coin] j ((ha j (by omega)).mp hz)
        · intro hr
          rcases ReachableAmount_app_single_inv _ coin j hc hr with hr | ⟨_, hm⟩
          · exact (ha j (by omega)).mpr hr
          · exact False.elim (((hb (j - coin) (by omega)).mpr hm) PreH1)
      · exact hb k (by omega)
    · intro k hk
      exact ha k (by omega)
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_6_1 : coinChange_entail_wit_6_1 := by
  unfold coinChange_entail_wit_6_1
  left
  intro amount_pre coinsSize_pre coins_pre coins_l dp_l_2 j coin i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9 NewPreH10 NewPreH11 NewPreH12
  prop_apply (intArray.full_Zlength coins_pre coinsSize_pre coins_l)
  Intros_p coins_length
  have current_coin_positive : 1 ≤ Znth i coins_l 0 := by
    exact annotation_Forall_nth_in _ coins_l i 0 NewPreH6 (by omega)
  have PreH9 : (coin = (Znth i coins_l (0 : Int))) := NewPreH7
  have PreH14 : (DpCoinInnerProgress (sublist ((0 : Int)) (i) (coins_l)) coin dp_l_2 j amount_pre) := NewPreH12
  have hj : j = amount_pre + 1 := by omega
  have ht : DpReachableTable (sublist 0 (i + 1) coins_l) dp_l_2 (amount_pre + 1) := by
    rw [sublist_0_succ_app 0 coins_l i (by omega), ← PreH9]
    rcases PreH14 with ⟨hc, hcj, hja, hlen, hb, ha⟩
    exact ⟨by omega, hlen, fun k hk => hb k (by omega)⟩
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_6_2 : coinChange_entail_wit_6_2 := by
  unfold coinChange_entail_wit_6_2
  left
  intro amount_pre coinsSize_pre coins_pre coins_l dp_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8 NewPreH9
  prop_apply (intArray.full_Zlength coins_pre coinsSize_pre coins_l)
  Intros_p coins_length
  have current_coin_positive : 1 ≤ Znth i coins_l 0 := by
    exact annotation_Forall_nth_in _ coins_l i 0 NewPreH8 (by omega)
  have PreH9 : ((Znth i coins_l 0) = (Znth i coins_l (0 : Int))) := by first | assumption | omega
  have PreH12 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1)) := NewPreH9
  have ht : DpReachableTable (sublist 0 (i + 1) coins_l) dp_l_2 (amount_pre + 1) := by
    rw [sublist_0_succ_app 0 coins_l i (by omega), ← PreH9]
    rcases PreH12 with ⟨hh, hlen, ht⟩
    refine ⟨hh, hlen, ?_⟩
    intro k hk
    exact (ht k hk).trans (ReachableAmount_app_single_below _ (Znth i coins_l 0) k (by omega) (by omega)).symm
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_7 : coinChange_entail_wit_7 := by
  unfold coinChange_entail_wit_7
  left
  intro amount_pre coinsSize_pre coins_pre coins_l dp_l_2 i NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6 NewPreH7 NewPreH8
  prop_apply (intArray.full_Zlength coins_pre coinsSize_pre coins_l)
  Intros_p coins_length
  have PreH9 : (DpReachableTable (sublist ((0 : Int)) (i) (coins_l)) dp_l_2 (amount_pre + 1)) := NewPreH8
  have hi : i = coinsSize_pre := by omega
  have hs : sublist 0 i coins_l = coins_l := by
    apply sublist_self
    omega
  have ht : DpReachableTable coins_l dp_l_2 (amount_pre + 1) := by simpa only [hs] using PreH9
  have hn : NoReachableAbove coins_l amount_pre amount_pre := by
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro k hk hr; omega
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_8 : coinChange_entail_wit_8 := by
  unfold coinChange_entail_wit_8
  left
  intro amount_pre coinsSize_pre coins_pre coins_l dp_l_2 res NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6
  prop_apply (intArray.full_Zlength coins_pre coinsSize_pre coins_l)
  Intros_p coins_length
  have PreH1 : ((Znth res dp_l_2 (0 : Int)) = (0 : Int)) := NewPreH1
  have PreH10 : (DpReachableTable coins_l dp_l_2 (amount_pre + 1)) := NewPreH5
  have PreH11 : (NoReachableAbove coins_l amount_pre res) := NewPreH6
  have hn : NoReachableAbove coins_l amount_pre (res - 1) := by
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    intro k hk hr
    by_cases he : k = res
    · subst k
      exact ((PreH10.2.2 res (by omega)).mpr hr) PreH1
    · exact PreH11.2 k (by omega) hr
  Exists dp_l_2
  split_pure_spatial
  · cancel
  · split_pures
    all_goals dump_pre_spatial
    all_goals first | assumption | omega | (solve | (simp only [Zlength_app, Zlength_cons, Zlength_nil] <;> omega)) | assumption | omega | rfl | trivial

theorem proof_of_coinChange_entail_wit_9_1 : coinChange_entail_wit_9_1 := by
  unfold coinChange_entail_wit_9_1
  left
  intro amount_pre coinsSize_pre coins_pre coins_l dp_l res NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5
  prop_apply (intArray.full_Zlength coins_pre coinsSize_pre coins_l)
  Intros_p coins_length
  have PreH10 : (NoReachableAbove coins_l amount_pre res) := NewPreH5
  have hr : res = 0 := by omega
  have hm : MaxReachableAmount coins_l amount_pre res :=
    MaxReachableAmount_intro_no_above _ _ _ (by rw [hr]; exact ReachableAmount_zero) (by omega) (by omega) PreH10
  sep_apply (scratch_cleanup ( &( "dp" ) ) (amount_pre + 1) 100001 dp_l (by omega))
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact hm


theorem proof_of_coinChange_entail_wit_9_2 : coinChange_entail_wit_9_2 := by
  unfold coinChange_entail_wit_9_2
  left
  intro amount_pre coinsSize_pre coins_pre coins_l dp_l res NewPreH1 NewPreH2 NewPreH3 NewPreH4 NewPreH5 NewPreH6
  prop_apply (intArray.full_Zlength coins_pre coinsSize_pre coins_l)
  Intros_p coins_length
  have PreH1 : ((Znth res dp_l (0 : Int)) ≠ (0 : Int)) := by first | assumption | omega
  have PreH10 : (DpReachableTable coins_l dp_l (amount_pre + 1)) := by first | assumption | omega
  have PreH11 : (NoReachableAbove coins_l amount_pre res) := NewPreH6
  have hm : MaxReachableAmount coins_l amount_pre res :=
    MaxReachableAmount_intro_no_above _ _ _ ((PreH10.2.2 res (by omega)).mp PreH1) (by omega) (by omega) PreH11
  sep_apply (scratch_cleanup ( &( "dp" ) ) (amount_pre + 1) 100001 dp_l (by omega))
  split_pure_spatial
  · cancel
  · dump_pre_spatial
    exact hm



end SimpleC.EE.LLM_bench.Algorithms.coin_change.coin_change_proof_manual
