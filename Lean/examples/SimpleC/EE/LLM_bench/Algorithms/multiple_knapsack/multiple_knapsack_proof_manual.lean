import SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_goal
import SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_proof_auto

set_option maxHeartbeats 4000000
set_option maxRecDepth 4000
set_option linter.unusedVariables false
namespace SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_proof_manual
open AUXLib SimpleC.SL.CNotation SimpleC.SL.CommonAssertion
open SimpleC.SL.CommonAssertion.DerivedPredSig SimpleC.SL.CommonAssertion.SeparationLogicSig
open SimpleC.SL.IntLib SimpleC.SL.SeparationLogic
open multiple_knapsack_goal multiple_knapsack_lib
open scoped SimpleC.SL.SAC
local instance : SacContext := ⟨naive_C_Rules⟩
private noncomputable abbrev intArray := naive_C_Rules.IntArray

private theorem queue_drop_pack (old qi qv : List Int) (head tail r w v cnt k cap : Int)
    (hs : MKQueueDropSafety old qi qv head tail r w k cap)
    (hm : MKQueueDropSemantics old qi qv head tail r w v cnt k) :
    MKQueueDropLoopState old qi qv head tail r w v cnt k cap := by
  obtain ⟨hr,hk,hh,ht,htl,hqi,hqv,ho⟩ := hs
  exact ⟨hr,hk,hh,ht,htl,hqi,hqv,ho,hm⟩
private theorem queue_pending_pack (old qi qv : List Int) (head tail r w v cnt k cap current : Int)
    (hs : MKQueueDropSafety old qi qv head tail r w k cap)
    (hm : MKQueuePendingSemantics old qi qv head tail r w v cnt k current) :
    MKQueuePendingState old qi qv head tail r w v cnt k cap current := by
  obtain ⟨hr,hk,hh,ht,htl,hqi,hqv,ho⟩ := hs
  exact ⟨hr,hk,hh,ht,htl,hqi,hqv,ho,hm⟩


private theorem nth_mem {A : Type} (l : List A) (d : A) (i : Int)
    (hi : 0 ≤ i ∧ i < Zlength l) : Znth i l d ∈ l := by
  unfold Znth
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp only [Zlength, Int.ofNat_eq_coe] at hi; omega)]
  simp only [Option.getD_some]
  exact List.getElem_mem _

private theorem nth_property (P : Int → Prop) (l : List Int) (i : Int)
    (h : Forall P l) (hi : 0 ≤ i ∧ i < Zlength l) : P (Znth i l 0) :=
  h.mem (nth_mem l 0 i hi)

theorem proof_of_multipleKnapsack_safety_wit_15 : multipleKnapsack_safety_wit_15 := by
  right
  intro capacity_pre n_pre counts_pre values_pre weights_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l qidx_l old_l dp_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  have hlo := nth_property _ old_l pos PreH37 (by omega)
  have hhi := nth_property _ old_l pos PreH38 (by omega)
  split_pures <;> dump_pre_spatial
  all_goals simp only [INT_MAX, INT_MIN]; nlinarith [mul_nonneg (show 0 ≤ k by omega) (show 0 ≤ v by omega), mul_le_mul_of_nonneg_left (show v ≤ 1000 by omega) (show 0 ≤ k by omega)]

theorem proof_of_multipleKnapsack_safety_wit_24 : multipleKnapsack_safety_wit_24 := by
  right
  intro capacity_pre n_pre counts_pre values_pre weights_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l qidx_l old_l dp_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54
  have he : head = tail := by omega
  subst head
  have heq := Znth_replace_Znth_Same 0 qval_l tail current (by omega)
  split_pures <;> dump_pre_spatial
  all_goals rw [heq]; simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_multipleKnapsack_safety_wit_26 : multipleKnapsack_safety_wit_26 := by
  right
  intro capacity_pre n_pre counts_pre values_pre weights_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l qidx_l old_l dp_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  have hb := PreH47.2.2.2.2.1 head (show head ≤ head ∧ head < tail by omega)
  have heq := Znth_replace_Znth_Diff 0 qval_l tail head current (by omega) (by omega) (by omega)
  split_pures <;> dump_pre_spatial
  all_goals rw [heq]; simp only [INT_MAX, INT_MIN]; omega

theorem proof_of_multipleKnapsack_entail_wit_1 : multipleKnapsack_entail_wit_1 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | rfl | exact Forall.nil

theorem proof_of_multipleKnapsack_entail_wit_2 : multipleKnapsack_entail_wit_2 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l qval0_2 qidx0_2 old0_2 j dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hz : Forall (Eq (0 : Int)) (dp_l_2 ++ [0]) := by
    apply Forall.iff_forall_mem.mpr
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact PreH15.mem hx
    · have he : x = 0 := by simpa using hx
      exact he.symm
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | exact hz | (simp only [Zlength_app, Zlength_cons, Zlength_nil]; omega)

theorem proof_of_multipleKnapsack_entail_wit_4 : multipleKnapsack_entail_wit_4 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have hc : MKCopyPrefixSemantics dp_l_2 old_l_2 0 := by intro c hc; omega
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    exact hc

theorem proof_of_multipleKnapsack_entail_wit_5 : multipleKnapsack_entail_wit_5 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have hc : MKCopyPrefix dp_l_2 old_l_2 j capacity_pre := ⟨⟨PreH15,PreH16⟩,PreH9,PreH10,PreH18⟩
  have hs := MKCopyPrefix_extend_by_replace_Znth dp_l_2 old_l_2 j capacity_pre hc (by omega)
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    · exact hs.2.2.2
    · simpa only [Zlength_replace_Znth] using PreH10

private theorem forall_of_nth (P : Int → Prop) (l : List Int)
    (h : ∀ i, (0 ≤ i ∧ i < Zlength l) → P (Znth i l 0)) : Forall P l := by
  apply Forall.iff_forall_mem.mpr
  intro x hx
  obtain ⟨i, hi, he⟩ := List.mem_iff_getElem.mp hx
  have hp := h (i : Int) ⟨by omega, by simp only [Zlength, Int.ofNat_eq_coe]; omega⟩
  simpa only [Znth, Int.toNat_natCast, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, he] using hp

attribute [local irreducible]
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.full
  SimpleC.SL.ArrayLibCore.ArrayLibCoreSig.ArrayLib.seg

theorem proof_of_multipleKnapsack_entail_wit_3 : multipleKnapsack_entail_wit_3 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l qval0 qidx0 old0 j dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have he : j = capacity_pre + 1 := by omega
  have hz : MKZeroPrefix dp_l_2 (capacity_pre+1) := ⟨by omega, by omega, fun c hc => (nth_property _ dp_l_2 c PreH15 (by omega)).symm⟩
  have ht := MKZeroPrefix_implies_MKDPTable_zero_items weights_l values_l counts_l capacity_pre dp_l_2 PreH4 hz
  have hm : MKDPTableSemantics weights_l values_l counts_l 0 capacity_pre dp_l_2 := ht.2.2.2
  Exists qval0 qidx0 old0 dp_l_2
  split_pure_spatial
  · rw [he]
    sep_apply (intArray.seg_to_full (&("dp")) 0 (capacity_pre+1) dp_l_2)
    sep_apply (intArray.seg_to_full (&("old")) 0 (capacity_pre+1) old0)
    sep_apply (intArray.seg_to_full (&("q_idx")) 0 (capacity_pre+1) qidx0)
    sep_apply (intArray.seg_to_full (&("q_val")) 0 (capacity_pre+1) qval0)
    simp only [Int.zero_mul, Int.add_zero, Int.sub_zero]
    cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_multipleKnapsack_entail_wit_6 : multipleKnapsack_entail_wit_6 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l j i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24
  have he : j = capacity_pre + 1 := by omega
  have hc : MKCopyPrefix dp_l_2 old_l_2 (capacity_pre+1) capacity_pre := ⟨⟨by omega,by omega⟩,PreH9,PreH10,by simpa only [he] using PreH18⟩
  have hd : MKDPTable weights_l values_l counts_l i capacity_pre dp_l_2 := ⟨⟨PreH13,by omega⟩,PreH4,PreH9,PreH17⟩
  have hb : ∀ idx, (0 ≤ idx ∧ idx < Zlength weights_l) → 1 ≤ Znth idx weights_l 0 ∧ 0 ≤ Znth idx values_l 0 ∧ Znth idx values_l 0 ≤ 1000 := by
    intro idx hi
    exact ⟨nth_property _ _ _ PreH19 hi, nth_property _ _ _ PreH21 (by omega), nth_property _ _ _ PreH22 (by omega)⟩
  have hw := nth_property _ weights_l i PreH19 (by omega)
  have hwmax := nth_property _ weights_l i PreH20 (by omega)
  have hv := nth_property _ values_l i PreH21 (by omega)
  have hvmax := nth_property _ values_l i PreH22 (by omega)
  have hcnt := nth_property _ counts_l i PreH23 (by omega)
  have hcntmax := nth_property _ counts_l i PreH24 (by omega)
  have hold := MKDPTable_copy_full weights_l values_l counts_l i capacity_pre dp_l_2 old_l_2 hd hc
  have hsem : MKDPTableSemantics weights_l values_l counts_l i capacity_pre old_l_2 := hold.2.2.2
  have hbound := MKDPTable_copy_implies_MKDPValueBound_under_global_item_bounds weights_l values_l counts_l i capacity_pre dp_l_2 old_l_2 ⟨PreH4,PreH5⟩ hb hd hc
  have hlo : Forall (fun x : Int => 0 ≤ x) old_l_2 := forall_of_nth _ _ (fun idx hi => (hbound.2 idx ⟨hi.1,by omega⟩).1)
  have hhi : Forall (fun x : Int => x ≤ 1000000) old_l_2 := forall_of_nth _ _ (fun idx hi => (hbound.2 idx ⟨hi.1,by omega⟩).2)
  have hprog : MKItemResidueProgressSemantics old_l_2 dp_l_2 0 (Znth i weights_l 0) (Znth i values_l 0) (Znth i counts_l 0) capacity_pre := by
    constructor
    · intro rem k pos he hr; omega
    · intro rem k pos he hr hk hp; exact (hc.2.2.2 pos ⟨hp.1,by omega⟩).symm
  have htb := MKDPTable_implies_MKTransitionValueBound_for_current_item weights_l values_l counts_l i capacity_pre dp_l_2 old_l_2 (Znth i weights_l 0) (Znth i values_l 0) (Znth i counts_l 0) ⟨PreH4,PreH5⟩ hw ⟨hv,hvmax⟩ hb hd hc
  have hguard : ∀ pos ans, ((0 ≤ pos ∧ pos ≤ capacity_pre) ∧ MKTransitionSemantics old_l_2 (Znth i weights_l 0) (Znth i values_l 0) (Znth i counts_l 0) capacity_pre pos ans) → 0 ≤ ans ∧ ans ≤ 1000000 := by
    intro pos ans hp
    exact htb pos ans hp.1 ⟨by omega,hcnt,hp.1,PreH10,hp.2⟩
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

private theorem queue_bounds (q : List Int) (head tail v k : Int)
    (hh : 0 ≤ head ∧ head ≤ tail) (ht : tail ≤ Zlength q)
    (hb : MKQueueResultValueBound q head tail v k) :
    Forall (fun x : Int => -(k*v) ≤ x) (sublist head tail q) ∧
    Forall (fun x : Int => x ≤ 1000000-k*v) (sublist head tail q) := by
  have hl : Zlength (sublist head tail q) = tail-head := by
    simp only [Zlength, sublist_length head tail q hh ht, Int.ofNat_eq_coe]
    omega
  constructor
  all_goals
    apply forall_of_nth
    intro i hi
    rw [Znth_sublist 0 head i tail q hh.1 (by omega)]
    have := hb (i+head) (by omega)
    omega

theorem proof_of_multipleKnapsack_entail_wit_7 : multipleKnapsack_entail_wit_7 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38
  have hp : MKItemResiduePrefixSemantics old_l_2 dp_l_2 r w v cnt 0 capacity_pre := by
    refine ⟨?_,?_⟩
    · intro t ht; omega
    · intro pos hp
      refine ⟨fun rem t he hr ht => PreH32.1 rem t pos he hr ht hp,?_⟩
      intro rem t he hr ht hlater
      exact PreH32.2 rem t pos he ⟨by omega,hr.2⟩ ht hp
  have hq : MKQueueResultSemantics old_l_2 qidx_l_2 qval_l_2 0 0 r w v cnt 0 capacity_pre := by
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    all_goals dsimp only [MKQueueEntriesValidForResult, MKQueueIndexIncreasing, MKQueueValueDecreasing, MKQueueCoversResultWindow, MKQueueResultValueBound]
    all_goals intros <;> omega
  have hb := queue_bounds qval_l_2 0 0 v (0-1) ⟨by omega,by omega⟩ (by omega) hq.2.2.2.2.1
  obtain ⟨hlo,hhi⟩ := hb
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_multipleKnapsack_entail_wit_8 : multipleKnapsack_entail_wit_8 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  have hd : MKQueueDropSemantics old_l qidx_l_2 qval_l_2 head tail r w v cnt k := by
    refine ⟨PreH41.1,PreH41.2.1,PreH41.2.2.1,?_,PreH41.2.2.2.2.1⟩
    intro cand hc hk hlo hp
    exact PreH41.2.2.2.1 cand hc hk (by omega) hp
  have hlo := nth_property _ old_l (r+k*w) PreH37 (by omega)
  have hhi := nth_property _ old_l (r+k*w) PreH38 (by omega)
  have hk : k ≤ capacity_pre := by nlinarith
  have hmul : 0 ≤ k*v ∧ k*v ≤ 1000000 := by
    constructor
    · exact mul_nonneg PreH28 PreH23
    · nlinarith [mul_le_mul_of_nonneg_left PreH24 PreH28]
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_multipleKnapsack_entail_wit_9 : multipleKnapsack_entail_wit_9 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  have hs : MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre := ⟨⟨PreH16,PreH17⟩,PreH29,⟨PreH38,PreH39⟩,PreH40,by omega,PreH12,PreH13,PreH11⟩
  have hx := MKQueueDropLoopState_pop_expired_preserves_predrop old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre PreH1 PreH2 (queue_drop_pack _ _ _ _ _ _ _ _ _ _ _ hs PreH47)
  have hd : MKQueueDropSemantics old_l_2 qidx_l_2 qval_l_2 (head+1) tail r w v cnt k := hx.2.2.2.2.2.2.2.2
  obtain ⟨hlo,hhi⟩ := queue_bounds qval_l_2 (head+1) tail v (k-1) (by omega) (by omega) hd.2.2.2.2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_multipleKnapsack_entail_wit_10_1 : multipleKnapsack_entail_wit_10_1 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54
  have hs : MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre := by
    refine ⟨⟨by omega,by omega⟩,by omega,⟨by omega,by omega⟩,by omega,by omega,by assumption,by assumption,by assumption⟩
  have hd := queue_drop_pack old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre hs PreH46
  have ha := MKQueueDropLoopState_empty_exit_to_MKQueueAfterDrop old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre PreH1 hd
  have hm : MKQueueAfterDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k := ha.2.2.2.2.2.2.2.2
  have hp : MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current := ⟨hm.1,hm.2.1,hm.2.2.1,(fun cand h0 hk hlo hl => Or.inl (hm.2.2.2.1 cand h0 hk hlo hl)),hm.2.2.2.2,by constructor <;> omega⟩
  obtain ⟨hlo,hhi⟩ := queue_bounds qval_l_2 head tail v k (by omega) (by omega) hm.2.2.2.2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

theorem proof_of_multipleKnapsack_entail_wit_10_2 : multipleKnapsack_entail_wit_10_2 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  have hs : MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre := by
    refine ⟨⟨by omega,by omega⟩,by omega,⟨by omega,by omega⟩,by omega,by omega,by assumption,by assumption,by assumption⟩
  have hd := queue_drop_pack old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre hs PreH47
  have ht : MKTransitionValueBound old_l_2 w v cnt capacity_pre := by
    intro pos ans hp ht
    exact PreH45 pos ans ⟨hp,ht.2.2.2.2⟩
  have ha := MKQueueDropLoopState_nonempty_exit_to_MKQueueAfterDrop old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos PreH1 PreH2 (by omega) (by omega) (by omega) (by omega) PreH28 ⟨PreH31,PreH32⟩ PreH33 PreH37 ht hd
  have hm : MKQueueAfterDropSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k := ha.2.2.2.2.2.2.2.2
  have hp : MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k current := ⟨hm.1,hm.2.1,hm.2.2.1,(fun cand h0 hk hlo hl => Or.inl (hm.2.2.2.1 cand h0 hk hlo hl)),hm.2.2.2.2,by constructor <;> omega⟩
  obtain ⟨hlo,hhi⟩ := queue_bounds qval_l_2 head tail v k (by omega) (by omega) hm.2.2.2.2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega

private theorem scratch_cleanup (a cap : Int) (l : List Int) (hc : 0 ≤ cap+1 ∧ cap+1 ≤ 1001) :
    intArray.full a (cap+1) l ** intArray.undef_seg a (cap+1) 1001 |-- intArray.undef_full a 1001 := by
  refine naive_C_Rules.toContext.derivable1_trans _ (intArray.undef_seg a 0 (cap+1) ** intArray.undef_seg a (cap+1) 1001) _ ?_ ?_
  · apply naive_C_Rules.toContext.derivable1_sepcon_mono
    · exact naive_C_Rules.toContext.derivable1_trans _ _ _ (intArray.full_to_seg a (cap+1) l) (intArray.seg_to_undef_seg a 0 (cap+1) l)
    · exact naive_C_Rules.toContext.derivable1_refl _
  · simpa only [Int.zero_mul,Int.add_zero,Int.sub_zero] using intArray.undef_seg_merge_to_undef_full a 0 (cap+1) 1001 hc

theorem proof_of_multipleKnapsack_entail_wit_11 : multipleKnapsack_entail_wit_11 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  have hs : MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre := ⟨⟨PreH16,PreH17⟩,PreH29,⟨PreH38,PreH39⟩,PreH40,by omega,PreH12,PreH13,PreH11⟩
  have hx := MKQueuePendingState_pop_dominated_tail_preserves old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current (queue_pending_pack _ _ _ _ _ _ _ _ _ _ _ _ hs PreH47) PreH2 PreH1
  have hm : MKQueuePendingSemantics old_l_2 qidx_l_2 qval_l_2 head (tail-1) r w v cnt k current := hx.2.2.2.2.2.2.2.2
  obtain ⟨hlo,hhi⟩ := queue_bounds qval_l_2 head (tail-1) v k (by omega) (by omega) hm.2.2.2.2.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; assumption) | ring

theorem proof_of_multipleKnapsack_entail_wit_12_1 : multipleKnapsack_entail_wit_12_1 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54
  have hs : MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre := by
    refine ⟨⟨by omega,by omega⟩,by omega,⟨by omega,by omega⟩,by omega,by omega,by assumption,by assumption,by assumption⟩
  have hx := MKQueuePending_push_complete_outcome__g06 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos PreH27 hs PreH46 PreH32 ⟨by omega,by omega⟩ (by omega) (by omega) (by intro hn; omega)
  have hq := hx.2.1
  have hp := MKItemResiduePrefixSemantics_after_dp_write__g09 old_l_2 dp_l_2 r w v cnt k capacity_pre pos (Znth head (replace_Znth tail current qval_l_2) 0+k*v) (by omega) (by omega) (by omega) PreH27 ⟨by omega,by omega⟩ PreH9 PreH45 hx.2.2.2.2
  rw [PreH27] at hp
  obtain ⟨hlo,hhi⟩ := queue_bounds (replace_Znth tail current qval_l_2) head (tail+1) v (k+1-1) (by omega) (by rw [Zlength_replace_Znth]; omega) hq.2.2.2.2.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; assumption) | ring

theorem proof_of_multipleKnapsack_entail_wit_12_2 : multipleKnapsack_entail_wit_12_2 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l tail head current k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49 PreH50 PreH51 PreH52 PreH53 PreH54 PreH55
  have hs : MKQueueDropSafety old_l_2 qidx_l_2 qval_l_2 head tail r w k capacity_pre := by
    refine ⟨⟨by omega,by omega⟩,by omega,⟨by omega,by omega⟩,by omega,by omega,by assumption,by assumption,by assumption⟩
  have hx := MKQueuePending_push_complete_outcome__g06 old_l_2 qidx_l_2 qval_l_2 head tail r w v cnt k capacity_pre current pos PreH28 hs PreH47 PreH33 ⟨by omega,by omega⟩ (by omega) (by omega) (by intro hn; omega)
  have hq := hx.2.1
  have hp := MKItemResiduePrefixSemantics_after_dp_write__g09 old_l_2 dp_l_2 r w v cnt k capacity_pre pos (Znth head (replace_Znth tail current qval_l_2) 0+k*v) (by omega) (by omega) (by omega) PreH28 ⟨by omega,by omega⟩ PreH10 PreH46 hx.2.2.2.2
  rw [PreH28] at hp
  obtain ⟨hlo,hhi⟩ := queue_bounds (replace_Znth tail current qval_l_2) head (tail+1) v (k+1-1) (by omega) (by rw [Zlength_replace_Znth]; omega) hq.2.2.2.2.1
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; assumption) | ring

theorem proof_of_multipleKnapsack_entail_wit_13 : multipleKnapsack_entail_wit_13 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l tail head k pos cnt v w r i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37 PreH38 PreH39 PreH40 PreH41 PreH42 PreH43 PreH44 PreH45 PreH46 PreH47 PreH48 PreH49
  have hp := MKItemResidueProgressSemantics_next_residue__g09 old_l_2 dp_l_2 r w v cnt k capacity_pre pos (by omega) PreH15 PreH27 PreH1 PreH40
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; assumption) | ring

theorem proof_of_multipleKnapsack_entail_wit_14 : multipleKnapsack_entail_wit_14 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l r cnt v w i qval_l_2 qidx_l_2 old_l_2 dp_l_2 PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21 PreH22 PreH23 PreH24 PreH25 PreH26 PreH27 PreH28 PreH29 PreH30 PreH31 PreH32 PreH33 PreH34 PreH35 PreH36 PreH37
  have hts : MKDPTableSafety weights_l i capacity_pre old_l_2 := ⟨⟨PreH13,by omega⟩,PreH4,PreH10⟩
  have hps : MKItemResidueProgressSafety old_l_2 dp_l_2 r w cnt capacity_pre := ⟨by omega,PreH22,PreH24,PreH25,PreH26,PreH10,PreH9⟩
  have hp := MKItemResidue_complete_table__g09 weights_l values_l counts_l i capacity_pre old_l_2 dp_l_2 r w v cnt ⟨PreH13,by omega⟩ (by omega) (by omega) PreH15 PreH16 PreH17 (fun idx hi => nth_property _ _ _ PreH32 hi) PreH1 hts PreH27 hps PreH31
  have hm := hp.2
  split_pure_spatial
  · cancel
  · split_pures <;> dump_pre_spatial
    all_goals first | assumption | omega | (simp only [Zlength_replace_Znth]; assumption) | ring

theorem proof_of_multipleKnapsack_entail_wit_15 : multipleKnapsack_entail_wit_15 := by
  right
  intro capacity_pre n_pre counts_l values_l weights_l i qval_l qidx_l old_l dp_l PreH1 PreH2 PreH3 PreH4 PreH5 PreH6 PreH7 PreH8 PreH9 PreH10 PreH11 PreH12 PreH13 PreH14 PreH15 PreH16 PreH17 PreH18 PreH19 PreH20 PreH21
  have he : i = n_pre := by omega
  have ht : MKDPTable weights_l values_l counts_l n_pre capacity_pre dp_l := ⟨⟨PreH2,by omega⟩,PreH4,PreH9,by simpa only [he] using PreH15⟩
  have ha := MKDPTable_final_capacity_implies_MultipleKnapsackAnswer weights_l values_l counts_l capacity_pre dp_l n_pre PreH6 PreH7 PreH8 PreH4 ht
  split_pure_spatial
  · sep_apply (scratch_cleanup (&("dp")) capacity_pre dp_l (by omega))
    sep_apply (scratch_cleanup (&("old")) capacity_pre old_l (by omega))
    sep_apply (scratch_cleanup (&("q_idx")) capacity_pre qidx_l (by omega))
    sep_apply (scratch_cleanup (&("q_val")) capacity_pre qval_l (by omega))
    cancel
  · dump_pre_spatial
    exact ha

end SimpleC.EE.LLM_bench.Algorithms.multiple_knapsack.multiple_knapsack_proof_manual
